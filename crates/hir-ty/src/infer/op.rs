//! Inference of binary and unary operators.

use std::collections::hash_map;

use hir_def::{
    AdtId, FunctionId, GenericParamId, TraitId,
    expr_store::path::Path,
    hir::ExprId,
    signatures::{StructSignature, TypeAliasSignature},
};
use hir_expand::name::Name;
use rustc_ast_ir::Mutability;
use rustc_type_ir::{
    InferTy,
    inherent::{IntoKind, Ty as _},
};
use syntax::ast::{ArithOp, BinaryOp, CmpOp, UnaryOp};
use tracing::debug;

use crate::{
    Adjust, Adjustment, AutoBorrow,
    infer::{AllowTwoPhase, AutoBorrowMutability, Expectation, InferenceContext, expr::ExprIsRead},
    method_resolution::{MethodCallee, TreatNotYetDefinedOpaques},
    next_solver::{
        GenericArgs, TraitRef, Ty, TyKind,
        fulfill::NextSolverError,
        infer::traits::{Obligation, ObligationCause},
        obligation_ctxt::ObligationCtxt,
    },
};

impl<'db> InferenceContext<'db> {
    /// Checks a `a <op>= b`
    pub(crate) fn infer_assign_op_expr(
        &mut self,
        expr: ExprId,
        op: ArithOp,
        lhs: ExprId,
        rhs: ExprId,
    ) -> Ty<'db> {
        let (lhs_ty, rhs_ty, return_ty) =
            self.infer_overloaded_binop(expr, lhs, rhs, BinaryOp::Assignment { op: Some(op) });

        let category = BinOpCategory::from(op);
        let ty = if !lhs_ty.is_ty_var()
            && !rhs_ty.is_ty_var()
            && is_builtin_binop(lhs_ty, rhs_ty, category)
        {
            self.enforce_builtin_binop_types(expr, lhs_ty, rhs_ty, category);
            self.types.types.unit
        } else {
            return_ty
        };

        self.check_lhs_assignable(lhs);

        ty
    }

    /// Checks a potentially overloaded binary operator.
    pub(crate) fn infer_binop_expr(
        &mut self,
        expr: ExprId,
        op: BinaryOp,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
    ) -> Ty<'db> {
        debug!(
            "check_binop(expr.hir_id={:?}, expr={:?}, op={:?}, lhs_expr={:?}, rhs_expr={:?})",
            expr, expr, op, lhs_expr, rhs_expr
        );

        if self.in_verus_spec_mode()
            && Self::is_verus_spec_ord_op(op)
            && let Some(chain_lhs_expr) = self.chained_comparison_lhs(lhs_expr)
        {
            return self.infer_chained_comparison_expr(
                expr,
                op,
                lhs_expr,
                chain_lhs_expr,
                rhs_expr,
            );
        }

        match op {
            BinaryOp::LogicOp(_) => {
                // && and || are a simple case.
                self.infer_expr_coerce(
                    lhs_expr,
                    &Expectation::HasType(self.types.types.bool),
                    ExprIsRead::Yes,
                );
                let lhs_diverges = self.diverges;
                self.infer_expr_coerce(
                    rhs_expr,
                    &Expectation::HasType(self.types.types.bool),
                    ExprIsRead::Yes,
                );

                // Depending on the LHS' value, the RHS can never execute.
                self.diverges = lhs_diverges;

                self.types.types.bool
            }
            _ => {
                if self.in_verus_spec_mode()
                    && matches!(BinOpCategory::from(op), BinOpCategory::Math)
                {
                    return self.infer_verus_spec_arithmetic_expr(expr, op, lhs_expr, rhs_expr);
                }

                // Otherwise, we always treat operators as if they are
                // overloaded. This is the way to be most flexible w/r/t
                // types that get inferred.
                let (lhs_ty, rhs_ty, return_ty) =
                    self.infer_overloaded_binop(expr, lhs_expr, rhs_expr, op);

                // Supply type inference hints if relevant. Probably these
                // hints should be enforced during select as part of the
                // `consider_unification_despite_ambiguity` routine, but this
                // more convenient for now.
                //
                // The basic idea is to help type inference by taking
                // advantage of things we know about how the impls for
                // scalar types are arranged. This is important in a
                // scenario like `1_u32 << 2`, because it lets us quickly
                // deduce that the result type should be `u32`, even
                // though we don't know yet what type 2 has and hence
                // can't pin this down to a specific impl.
                let category = BinOpCategory::from(op);
                if matches!(category, BinOpCategory::Comparison)
                    && self.in_verus_spec_mode()
                    && Self::is_verus_spec_comparison_op(op)
                    && self.is_verus_spec_comparison(lhs_ty, rhs_ty)
                {
                    return self.types.types.bool;
                }

                if !lhs_ty.is_ty_var()
                    && !rhs_ty.is_ty_var()
                    && is_builtin_binop(lhs_ty, rhs_ty, category)
                {
                    let builtin_return_ty =
                        self.enforce_builtin_binop_types(expr, lhs_ty, rhs_ty, category);
                    _ = self.demand_eqtype(expr.into(), builtin_return_ty, return_ty);
                    builtin_return_ty
                } else {
                    return_ty
                }
            }
        }
    }

    fn infer_verus_spec_arithmetic_expr(
        &mut self,
        expr: ExprId,
        op: BinaryOp,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
    ) -> Ty<'db> {
        let lhs_ty = self.infer_expr_no_expect(lhs_expr, ExprIsRead::Yes);
        let lhs_ty = self.table.resolve_vars_with_obligations(lhs_ty);
        let rhs_ty = self.infer_expr_no_expect(rhs_expr, ExprIsRead::Yes);
        let rhs_ty = self.table.resolve_vars_with_obligations(rhs_ty);

        self.verus_spec_arithmetic_ty(expr, op, lhs_ty, rhs_ty)
            .unwrap_or_else(|| self.table.next_ty_var(expr.into()))
    }

    // Verus accepts chained comparisons in spec contexts. Exec contexts fall through to ordinary
    // binary operator inference, where `(a < b) <= c` is rejected as a Rust type mismatch.
    fn infer_chained_comparison_expr(
        &mut self,
        expr: ExprId,
        op: BinaryOp,
        lhs_expr: ExprId,
        chain_lhs_expr: ExprId,
        rhs_expr: ExprId,
    ) -> Ty<'db> {
        self.infer_expr_inner(lhs_expr, &Expectation::none(), ExprIsRead::Yes);
        self.infer_binop_expr(expr, op, chain_lhs_expr, rhs_expr);
        self.types.types.bool
    }

    fn chained_comparison_lhs(&self, expr: ExprId) -> Option<ExprId> {
        match self.store[expr] {
            hir_def::hir::Expr::BinaryOp { rhs, op: Some(BinaryOp::CmpOp(_)), .. } => Some(rhs),
            _ => None,
        }
    }

    fn enforce_builtin_binop_types(
        &mut self,
        expr: ExprId,
        lhs_ty: Ty<'db>,
        rhs_ty: Ty<'db>,
        category: BinOpCategory,
    ) -> Ty<'db> {
        debug_assert!(is_builtin_binop(lhs_ty, rhs_ty, category));

        // Special-case a single layer of referencing, so that things like `5.0 + &6.0f32` work.
        // (See https://github.com/rust-lang/rust/issues/57447.)
        let (lhs_ty, rhs_ty) = (deref_ty_if_possible(lhs_ty), deref_ty_if_possible(rhs_ty));

        match category {
            BinOpCategory::Shortcircuit => {
                _ = self.demand_suptype(expr.into(), self.types.types.bool, lhs_ty);
                _ = self.demand_suptype(expr.into(), self.types.types.bool, rhs_ty);
                self.types.types.bool
            }

            BinOpCategory::Shift => {
                // result type is same as LHS always
                lhs_ty
            }

            BinOpCategory::Math | BinOpCategory::Bitwise => {
                // both LHS and RHS and result will have the same type
                _ = self.demand_suptype(expr.into(), lhs_ty, rhs_ty);
                lhs_ty
            }

            BinOpCategory::Comparison => {
                // both LHS and RHS and result will have the same type
                _ = self.demand_suptype(expr.into(), lhs_ty, rhs_ty);
                self.types.types.bool
            }
        }
    }

    fn infer_overloaded_binop(
        &mut self,
        expr: ExprId,
        lhs_expr: ExprId,
        rhs_expr: ExprId,
        op: BinaryOp,
    ) -> (Ty<'db>, Ty<'db>, Ty<'db>) {
        debug!("infer_overloaded_binop(expr.hir_id={:?}, op={:?})", expr, op);

        let lhs_ty = match op {
            BinaryOp::Assignment { .. } => {
                // rust-lang/rust#52126: We have to use strict
                // equivalence on the LHS of an assign-op like `+=`;
                // overwritten or mutably-borrowed places cannot be
                // coerced to a supertype.
                self.infer_expr_no_expect(lhs_expr, ExprIsRead::Yes)
            }
            _ => {
                // Find a suitable supertype of the LHS expression's type, by coercing to
                // a type variable, to pass as the `Self` to the trait, avoiding invariant
                // trait matching creating lifetime constraints that are too strict.
                // e.g., adding `&'a T` and `&'b T`, given `&'x T: Add<&'x T>`, will result
                // in `&'a T <: &'x T` and `&'b T <: &'x T`, instead of `'a = 'b = 'x`.
                let lhs_ty = self.infer_expr_no_expect(lhs_expr, ExprIsRead::Yes);
                let fresh_var = self.table.next_ty_var(lhs_expr.into());
                self.demand_coerce(lhs_expr, lhs_ty, fresh_var, AllowTwoPhase::No, ExprIsRead::Yes)
            }
        };
        let lhs_ty = self.table.resolve_vars_with_obligations(lhs_ty);

        // N.B., as we have not yet type-checked the RHS, we don't have the
        // type at hand. Make a variable to represent it. The whole reason
        // for this indirection is so that, below, we can check the expr
        // using this variable as the expected type, which sometimes lets
        // us do better coercions than we would be able to do otherwise,
        // particularly for things like `String + &String`.
        let rhs_ty_var = self.table.next_ty_var(rhs_expr.into());
        let result = self.lookup_op_method(
            expr,
            lhs_ty,
            Some((rhs_expr, rhs_ty_var)),
            self.lang_item_for_bin_op(op),
        );

        // see `NB` above
        let rhs_ty = self.infer_binop_rhs_expr(lhs_ty, rhs_expr, rhs_ty_var, op);
        let rhs_ty = self.table.resolve_vars_with_obligations(rhs_ty);

        let return_ty = match result {
            Ok(method) => {
                let by_ref_binop = !is_op_by_value(op);
                if (matches!(op, BinaryOp::Assignment { .. }) || by_ref_binop)
                    && let TyKind::Ref(_, _, mutbl) =
                        method.sig.inputs_and_output.inputs()[0].kind()
                {
                    let mutbl = AutoBorrowMutability::new(mutbl, AllowTwoPhase::Yes);
                    let autoref = Adjustment {
                        kind: Adjust::Borrow(AutoBorrow::Ref(mutbl)),
                        target: method.sig.inputs_and_output.inputs()[0].store(),
                    };
                    self.write_expr_adj(lhs_expr, Box::new([autoref]));
                }
                if by_ref_binop
                    && let TyKind::Ref(_, _, mutbl) =
                        method.sig.inputs_and_output.inputs()[1].kind()
                {
                    // Allow two-phase borrows for binops in initial deployment
                    // since they desugar to methods
                    let mutbl = AutoBorrowMutability::new(mutbl, AllowTwoPhase::Yes);

                    let autoref = Adjustment {
                        kind: Adjust::Borrow(AutoBorrow::Ref(mutbl)),
                        target: method.sig.inputs_and_output.inputs()[1].store(),
                    };
                    // HACK(eddyb) Bypass checks due to reborrows being in
                    // some cases applied on the RHS, on top of which we need
                    // to autoref, which is not allowed by write_expr_adj.
                    // self.write_expr_adj(rhs_expr, Box::new([autoref]));
                    match self.result.expr_adjustments.entry(rhs_expr) {
                        hash_map::Entry::Occupied(mut entry) => {
                            let mut adjustments = Vec::from(std::mem::take(entry.get_mut()));
                            adjustments.reserve_exact(1);
                            adjustments.push(autoref);
                            entry.insert(adjustments.into_boxed_slice());
                        }
                        hash_map::Entry::Vacant(entry) => {
                            entry.insert(Box::new([autoref]));
                        }
                    };
                }
                self.write_method_resolution(expr, method.def_id, method.args);

                method.sig.output()
            }
            Err(_errors) => {
                // FIXME: Report diagnostic.
                self.types.types.error
            }
        };

        (lhs_ty, rhs_ty, return_ty)
    }

    fn infer_binop_rhs_expr(
        &mut self,
        lhs_ty: Ty<'db>,
        rhs_expr: ExprId,
        rhs_ty_var: Ty<'db>,
        op: BinaryOp,
    ) -> Ty<'db> {
        let expected = Expectation::HasType(rhs_ty_var);
        let rhs_ty = self.infer_expr_inner(rhs_expr, &expected, ExprIsRead::Yes);
        let resolved_rhs_ty = self.table.resolve_vars_with_obligations(rhs_ty);

        if let Some(target) = expected.only_has_type(&mut self.table) {
            match self.coerce(rhs_expr, rhs_ty, target, AllowTwoPhase::No, ExprIsRead::Yes) {
                Ok(res) => res,
                Err(_)
                    if self.in_verus_spec_mode()
                        && Self::is_verus_spec_comparison_op(op)
                        && self.is_verus_spec_comparison(lhs_ty, resolved_rhs_ty) =>
                {
                    let target = self.table.resolve_vars_with_obligations(target);
                    if self.is_verus_spec_comparison(lhs_ty, resolved_rhs_ty) {
                        resolved_rhs_ty
                    } else {
                        self.emit_type_mismatch(rhs_expr.into(), target, rhs_ty);
                        target
                    }
                }
                Err(_) => {
                    self.emit_type_mismatch(rhs_expr.into(), target, rhs_ty);
                    target
                }
            }
        } else {
            rhs_ty
        }
    }

    fn is_verus_spec_comparison(&self, lhs_ty: Ty<'db>, rhs_ty: Ty<'db>) -> bool {
        lhs_ty.is_ty_var() || rhs_ty.is_ty_var() || self.is_verus_integer_comparison(lhs_ty, rhs_ty)
    }

    fn is_verus_integer_comparison(&self, lhs_ty: Ty<'db>, rhs_ty: Ty<'db>) -> bool {
        let lhs_is_verus_integer = self.verus_integer_name_of_binop_ty(lhs_ty).is_some();
        let rhs_is_verus_integer = self.verus_integer_name_of_binop_ty(rhs_ty).is_some();
        let lhs_is_builtin_integer = is_builtin_integer(lhs_ty);
        let rhs_is_builtin_integer = is_builtin_integer(rhs_ty);
        let lhs_is_integer_var = is_integer_var(lhs_ty);
        let rhs_is_integer_var = is_integer_var(rhs_ty);

        lhs_is_verus_integer
            && (rhs_is_verus_integer || rhs_is_builtin_integer || rhs_is_integer_var)
            || rhs_is_verus_integer
                && (lhs_is_verus_integer || lhs_is_builtin_integer || lhs_is_integer_var)
            || lhs_is_builtin_integer && rhs_is_builtin_integer
    }

    fn is_verus_spec_comparison_op(op: BinaryOp) -> bool {
        Self::is_verus_spec_ord_op(op) || matches!(op, BinaryOp::CmpOp(CmpOp::Eq { .. }))
    }

    fn is_verus_spec_ord_op(op: BinaryOp) -> bool {
        matches!(op, BinaryOp::CmpOp(CmpOp::Ord { .. }))
    }

    fn verus_spec_arithmetic_ty(
        &mut self,
        expr: ExprId,
        op: BinaryOp,
        lhs_ty: Ty<'db>,
        rhs_ty: Ty<'db>,
    ) -> Option<Ty<'db>> {
        let op = match op {
            BinaryOp::ArithOp(
                op @ (ArithOp::Add | ArithOp::Sub | ArithOp::Mul | ArithOp::Div | ArithOp::Rem),
            ) => op,
            _ => return None,
        };

        let lhs_ty = deref_ty_if_possible(lhs_ty);
        let rhs_ty = deref_ty_if_possible(rhs_ty);
        let lhs_name = self.verus_numeric_name_of_binop_ty(lhs_ty);
        let rhs_name = self.verus_numeric_name_of_binop_ty(rhs_ty);

        if matches!(lhs_name, Some("real")) {
            return Some(lhs_ty);
        }
        if matches!(rhs_name, Some("real")) {
            return Some(rhs_ty);
        }

        let lhs = self.verus_spec_integer_ty(lhs_ty)?;
        let rhs = self.verus_spec_integer_ty(rhs_ty)?;

        match op {
            ArithOp::Add | ArithOp::Mul => {
                if let Some(nat_ty) = lhs.nat_pair_result(rhs) {
                    Some(nat_ty)
                } else {
                    Some(self.verus_named_numeric_ty(expr, "int"))
                }
            }
            ArithOp::Sub => Some(self.verus_named_numeric_ty(expr, "int")),
            ArithOp::Div => {
                if lhs.has_same_concrete_type(rhs) || lhs.has_integer_var_operand(rhs) {
                    if let Some(unsigned_ty) = lhs.unsigned_or_nat_pair_result(rhs) {
                        Some(unsigned_ty)
                    } else {
                        Some(self.verus_named_numeric_ty(expr, "int"))
                    }
                } else {
                    None
                }
            }
            ArithOp::Rem => {
                if lhs.has_same_concrete_type(rhs) || lhs.has_integer_var_operand(rhs) {
                    lhs.concrete_ty().or_else(|| rhs.concrete_ty())
                } else {
                    None
                }
            }
            ArithOp::Shl | ArithOp::Shr | ArithOp::BitXor | ArithOp::BitOr | ArithOp::BitAnd => {
                None
            }
        }
    }

    fn verus_named_numeric_ty(&mut self, expr: ExprId, name: &str) -> Ty<'db> {
        let path = Path::from(Name::new_root(name));
        let (ty, _) = self.resolve_variant(expr.into(), &path, false);
        if self.verus_numeric_name_of_binop_ty(ty) == Some(name) { ty } else { self.err_ty() }
    }

    fn verus_spec_integer_ty(&self, ty: Ty<'db>) -> Option<VerusSpecIntegerTy<'db>> {
        let ty = deref_ty_if_possible(ty);
        match ty.kind() {
            TyKind::Int(_) => Some(VerusSpecIntegerTy::Signed(ty)),
            TyKind::Uint(_) => Some(VerusSpecIntegerTy::Unsigned(ty)),
            TyKind::Infer(InferTy::IntVar(_)) => Some(VerusSpecIntegerTy::IntVar),
            _ => match self.verus_numeric_name_of_binop_ty(ty)? {
                "int" => Some(VerusSpecIntegerTy::Int(ty)),
                "nat" => Some(VerusSpecIntegerTy::Nat(ty)),
                _ => None,
            },
        }
    }

    fn verus_integer_name_of_binop_ty(&self, ty: Ty<'db>) -> Option<&'static str> {
        match self.verus_numeric_name_of_binop_ty(ty)? {
            name @ ("int" | "nat") => Some(name),
            _ => None,
        }
    }

    fn verus_numeric_name_of_binop_ty(&self, ty: Ty<'db>) -> Option<&'static str> {
        let ty = deref_ty_if_possible(ty);
        let name = if let Some((AdtId::StructId(id), _)) = ty.as_adt() {
            StructSignature::of(self.db, id).name.clone()
        } else if let TyKind::Foreign(alias) = ty.kind() {
            TypeAliasSignature::of(self.db, alias.0).name.clone()
        } else {
            return None;
        };

        match name.as_str() {
            "int" => Some("int"),
            "nat" => Some("nat"),
            "real" => Some("real"),
            _ => None,
        }
    }

    pub(crate) fn infer_user_unop(
        &mut self,
        ex: ExprId,
        operand_ty: Ty<'db>,
        op: UnaryOp,
    ) -> Ty<'db> {
        match self.lookup_op_method(ex, operand_ty, None, self.lang_item_for_unop(op)) {
            Ok(method) => {
                self.write_method_resolution(ex, method.def_id, method.args);
                method.sig.output()
            }
            Err(_errors) => {
                // FIXME: Report diagnostic.
                self.types.types.error
            }
        }
    }

    fn lookup_op_method(
        &mut self,
        expr: ExprId,
        lhs_ty: Ty<'db>,
        opt_rhs: Option<(ExprId, Ty<'db>)>,
        (op_method, trait_did): (Option<FunctionId>, Option<TraitId>),
    ) -> Result<MethodCallee<'db>, Vec<NextSolverError<'db>>> {
        let (Some(trait_did), Some(op_method)) = (trait_did, op_method) else {
            // Bail if the operator trait is not defined.
            return Err(vec![]);
        };

        debug!(
            "lookup_op_method(lhs_ty={:?}, opname={:?}, trait_did={:?})",
            lhs_ty, op_method, trait_did
        );

        let opt_rhs_ty = opt_rhs.map(|it| it.1);
        let cause = ObligationCause::new(expr);

        // We don't consider any other candidates if this lookup fails
        // so we can freely treat opaque types as inference variables here
        // to allow more code to compile.
        let treat_opaques = TreatNotYetDefinedOpaques::AsInfer;
        let method = self.table.lookup_method_for_operator(
            cause,
            trait_did,
            op_method,
            lhs_ty,
            opt_rhs_ty,
            treat_opaques,
        );
        match method {
            Some(ok) => {
                let method = self.table.register_infer_ok(ok);
                self.table.select_obligations_where_possible();
                Ok(method)
            }
            None => {
                // Guide inference for the RHS expression if it's provided --
                // this will allow us to better error reporting, at the expense
                // of making some error messages a bit more specific.
                if let Some((rhs_expr, rhs_ty)) = opt_rhs
                    && rhs_ty.is_ty_var()
                {
                    self.infer_expr_coerce(
                        rhs_expr,
                        &Expectation::HasType(rhs_ty),
                        ExprIsRead::Yes,
                    );
                }

                // Construct an obligation `self_ty : Trait<input_tys>`
                let args = GenericArgs::for_item(
                    self.interner(),
                    trait_did.into(),
                    |param_idx, param_id, _, _| match param_id {
                        GenericParamId::LifetimeParamId(_) | GenericParamId::ConstParamId(_) => {
                            unreachable!("did not expect operand trait to have lifetime/const args")
                        }
                        GenericParamId::TypeParamId(_) => {
                            if param_idx == 0 {
                                lhs_ty.into()
                            } else {
                                opt_rhs_ty.expect("expected RHS for binop").into()
                            }
                        }
                    },
                );
                let obligation = Obligation::new(
                    self.interner(),
                    cause,
                    self.table.param_env,
                    TraitRef::new_from_args(self.interner(), trait_did.into(), args),
                );
                let mut ocx = ObligationCtxt::new(self.infcx());
                ocx.register_obligation(obligation);
                Err(ocx.evaluate_obligations_error_on_ambiguity())
            }
        }
    }

    fn lang_item_for_bin_op(&self, op: BinaryOp) -> (Option<FunctionId>, Option<TraitId>) {
        let (method, trait_lang_item) =
            crate::lang_items::lang_items_for_bin_op(self.lang_items, op)
                .expect("invalid operator provided");
        (method, trait_lang_item)
    }

    fn lang_item_for_unop(&self, op: UnaryOp) -> (Option<FunctionId>, Option<TraitId>) {
        let (method, trait_lang_item) = match op {
            UnaryOp::Not => (self.lang_items.Not_not, self.lang_items.Not),
            UnaryOp::Neg => (self.lang_items.Neg_neg, self.lang_items.Neg),
            UnaryOp::Deref => panic!("Deref is not overloadable"),
        };
        (method, trait_lang_item)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VerusSpecIntegerTy<'db> {
    Int(Ty<'db>),
    Nat(Ty<'db>),
    Signed(Ty<'db>),
    Unsigned(Ty<'db>),
    IntVar,
}

impl<'db> VerusSpecIntegerTy<'db> {
    fn concrete_ty(self) -> Option<Ty<'db>> {
        match self {
            VerusSpecIntegerTy::Int(ty)
            | VerusSpecIntegerTy::Nat(ty)
            | VerusSpecIntegerTy::Signed(ty)
            | VerusSpecIntegerTy::Unsigned(ty) => Some(ty),
            VerusSpecIntegerTy::IntVar => None,
        }
    }

    fn is_int_var(self) -> bool {
        matches!(self, VerusSpecIntegerTy::IntVar)
    }

    fn nat_pair_result(self, other: Self) -> Option<Ty<'db>> {
        match (self, other) {
            (VerusSpecIntegerTy::Nat(ty), VerusSpecIntegerTy::Nat(_))
            | (VerusSpecIntegerTy::Nat(ty), VerusSpecIntegerTy::IntVar)
            | (VerusSpecIntegerTy::IntVar, VerusSpecIntegerTy::Nat(ty)) => Some(ty),
            _ => None,
        }
    }

    fn unsigned_or_nat_pair_result(self, other: Self) -> Option<Ty<'db>> {
        match (self, other) {
            (VerusSpecIntegerTy::Unsigned(ty), VerusSpecIntegerTy::Unsigned(_))
            | (VerusSpecIntegerTy::Unsigned(ty), VerusSpecIntegerTy::IntVar)
            | (VerusSpecIntegerTy::IntVar, VerusSpecIntegerTy::Unsigned(ty))
            | (VerusSpecIntegerTy::Nat(ty), VerusSpecIntegerTy::Nat(_))
            | (VerusSpecIntegerTy::Nat(ty), VerusSpecIntegerTy::IntVar)
            | (VerusSpecIntegerTy::IntVar, VerusSpecIntegerTy::Nat(ty)) => Some(ty),
            _ => None,
        }
    }

    fn has_same_concrete_type(self, other: Self) -> bool {
        matches!(
            (self, other),
            (VerusSpecIntegerTy::Int(_), VerusSpecIntegerTy::Int(_))
                | (VerusSpecIntegerTy::Nat(_), VerusSpecIntegerTy::Nat(_))
        ) || match (self.concrete_ty(), other.concrete_ty()) {
            (Some(lhs), Some(rhs)) => lhs == rhs,
            _ => false,
        }
    }

    fn has_integer_var_operand(self, other: Self) -> bool {
        self.is_int_var() ^ other.is_int_var()
    }
}

fn is_builtin_integer(ty: Ty<'_>) -> bool {
    matches!(deref_ty_if_possible(ty).kind(), TyKind::Int(_) | TyKind::Uint(_))
}

fn is_integer_var(ty: Ty<'_>) -> bool {
    matches!(deref_ty_if_possible(ty).kind(), TyKind::Infer(InferTy::IntVar(_)))
}

// Binary operator categories. These categories summarize the behavior
// with respect to the builtin operations supported.
#[derive(Clone, Copy)]
enum BinOpCategory {
    /// &&, || -- cannot be overridden
    Shortcircuit,

    /// <<, >> -- when shifting a single integer, rhs can be any
    /// integer type. For simd, types must match.
    Shift,

    /// +, -, etc -- takes equal types, produces same type as input,
    /// applicable to ints/floats/simd
    Math,

    /// &, |, ^ -- takes equal types, produces same type as input,
    /// applicable to ints/floats/simd/bool
    Bitwise,

    /// ==, !=, etc -- takes equal types, produces bools, except for simd,
    /// which produce the input type
    Comparison,
}

impl From<BinaryOp> for BinOpCategory {
    fn from(op: BinaryOp) -> BinOpCategory {
        match op {
            BinaryOp::LogicOp(_) => BinOpCategory::Shortcircuit,
            BinaryOp::ArithOp(op) | BinaryOp::Assignment { op: Some(op) } => op.into(),
            BinaryOp::CmpOp(_) => BinOpCategory::Comparison,
            BinaryOp::Assignment { op: None } => unreachable!(
                "assignment is lowered into `Expr::Assignment`, not into `Expr::BinaryOp`"
            ),
        }
    }
}

impl From<ArithOp> for BinOpCategory {
    fn from(op: ArithOp) -> BinOpCategory {
        use ArithOp::*;
        match op {
            Shl | Shr => BinOpCategory::Shift,
            Add | Sub | Mul | Div | Rem => BinOpCategory::Math,
            BitXor | BitAnd | BitOr => BinOpCategory::Bitwise,
        }
    }
}

/// Returns `true` if the binary operator takes its arguments by value.
fn is_op_by_value(op: BinaryOp) -> bool {
    !matches!(op, BinaryOp::CmpOp(_))
}

/// Dereferences a single level of immutable referencing.
fn deref_ty_if_possible(ty: Ty<'_>) -> Ty<'_> {
    match ty.kind() {
        TyKind::Ref(_, ty, Mutability::Not) => ty,
        _ => ty,
    }
}

/// Returns `true` if this is a built-in arithmetic operation (e.g.,
/// u32 + u32, i16x4 == i16x4) and false if these types would have to be
/// overloaded to be legal. There are two reasons that we distinguish
/// builtin operations from overloaded ones (vs trying to drive
/// everything uniformly through the trait system and intrinsics or
/// something like that):
///
/// 1. Builtin operations can trivially be evaluated in constants.
/// 2. For comparison operators applied to SIMD types the result is
///    not of type `bool`. For example, `i16x4 == i16x4` yields a
///    type like `i16x4`. This means that the overloaded trait
///    `PartialEq` is not applicable.
///
/// Reason #2 is the killer. I tried for a while to always use
/// overloaded logic and just check the types in constants/codegen after
/// the fact, and it worked fine, except for SIMD types. -nmatsakis
fn is_builtin_binop<'db>(lhs: Ty<'db>, rhs: Ty<'db>, category: BinOpCategory) -> bool {
    // Special-case a single layer of referencing, so that things like `5.0 + &6.0f32` work.
    // (See https://github.com/rust-lang/rust/issues/57447.)
    let (lhs, rhs) = (deref_ty_if_possible(lhs), deref_ty_if_possible(rhs));

    match category {
        BinOpCategory::Shortcircuit => true,
        BinOpCategory::Shift => lhs.is_integral() && rhs.is_integral(),
        BinOpCategory::Math => {
            lhs.is_integral() && rhs.is_integral()
                || lhs.is_floating_point() && rhs.is_floating_point()
        }
        BinOpCategory::Bitwise => {
            lhs.is_integral() && rhs.is_integral()
                || lhs.is_floating_point() && rhs.is_floating_point()
                || lhs.is_bool() && rhs.is_bool()
        }
        BinOpCategory::Comparison => lhs.is_scalar() && rhs.is_scalar(),
    }
}
