//! ProofPlumber API for inline.
//!
//! Used for inlining a precondition at the callsite. See
//! `insert_failing_precondition.rs` for usage.
//!
//! Re-ported against the modern `inline_call` handler API: `CallInfo`,
//! `get_fn_params`, and `inline` are now `pub(crate)` in
//! `crate::handlers::inline_call` and take an extra `Crate` for the call
//! site (used by macro-expansion prettification).

use hir::{FileRange, Semantics};
use ide_db::RootDatabase;
use syntax::{
    AstNode,
    ast::{self, syntax_factory::SyntaxFactory, vst},
    syntax_editor::SyntaxEditor,
};

use crate::{
    AssistContext,
    handlers::inline_call::{CallInfo, get_fn_params, inline_simple},
};

impl<'a, 'db> AssistContext<'a, 'db> {
    /// Inline a function call.
    ///
    /// `name_ref` is the call-site identifier; `expr_to_inline` becomes the
    /// (synthetic) function body that gets substituted at every parameter
    /// usage.
    ///
    /// Limitations carried over from the original Verus implementation:
    /// - Single-file callers only.
    /// - Verus builtins (e.g. `int`) are not modelled; if the inliner needs
    ///   to query the type of such an expression it returns `None`.
    /// - The synthetic function we build does not properly register the
    ///   replaced expression's req/ens in the semantics database.
    pub fn vst_inline_call(
        &self,
        name_ref: vst::NameRef,
        expr_to_inline: vst::Expr,
    ) -> Option<vst::Expr> {
        let name_ref: ast::NameRef = name_ref.cst?;
        let call_site_krate = self.sema.scope(name_ref.syntax())?.krate();
        let call_info = CallInfo::from_name_ref(name_ref.clone(), call_site_krate.base())?;

        let function = match &call_info.node {
            ast::CallableExpr::Call(call) => {
                let path = match call.expr()? {
                    ast::Expr::PathExpr(path) => path.path(),
                    _ => None,
                }?;
                match self.sema.resolve_path(&path)? {
                    hir::PathResolution::Def(hir::ModuleDef::Function(f)) => f,
                    _ => return None,
                }
            }
            ast::CallableExpr::MethodCall(call) => self.sema.resolve_method_call(call)?,
        };

        let fn_source: hir::InFile<ast::Fn> = self.sema.source(function)?;

        // Use the to-be-inlined expression as the synthetic function body.
        let fn_body_expr = expr_to_inline.cst()?;
        let fn_body = ast::make::tail_only_block_expr(fn_body_expr);

        // Hand-build a function whose body is `fn_body` so the inliner sees a
        // fresh, well-formed source tree to work against.
        let (editor, temp_fn) = SyntaxEditor::with_ast_node(&fn_source.value);
        editor.replace(temp_fn.body()?.syntax(), fn_body.syntax());
        let temp_fn = ast::Fn::cast(editor.finish().new_root().clone())?;

        // Build a throw-away analysis db over the synthetic function so
        // `Semantics::to_def`, `resolve_path`, etc. can be queried against it.
        let mut temp_fn_str = temp_fn.to_string();
        temp_fn_str.insert_str(0, "$0");
        let (mut db, file_with_caret_id, range_or_offset) =
            <RootDatabase as test_fixture::WithFixture>::with_range_or_offset(&temp_fn_str);
        db.enable_proc_attr_macros();

        let frange = FileRange { file_id: file_with_caret_id, range: range_or_offset.into() };
        let sema: Semantics<'_, RootDatabase> = Semantics::new(&db);
        let cfg = self.config.clone();
        let tmp_ctx = AssistContext::new_with_verus_errors(sema, &cfg, frange, Vec::new());

        let tmp_fn = tmp_ctx.find_node_at_offset::<ast::Fn>()?;
        let tmp_body = tmp_fn.body()?;
        let tmp_param_list = tmp_fn.param_list()?;
        let tmp_function = tmp_ctx.sema.to_def(&tmp_fn)?;
        let make = SyntaxFactory::without_mappings();
        let tmp_params = get_fn_params(tmp_ctx.db(), tmp_function, &tmp_param_list, &make)?;

        let replacement = inline_simple(
            &tmp_ctx.sema,
            file_with_caret_id,
            tmp_function,
            &tmp_body,
            &tmp_params,
            &call_info,
        );
        vst::Expr::try_from(replacement).ok()
    }
}
