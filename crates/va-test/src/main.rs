//! `va-test` — a small CLI that loads a workspace through the rust-analyzer
//! infrastructure and exercises Verus-specific lifting (CST → VST) on every
//! function it can see, reporting parse errors and lifting failures.
//!
//! Originally ported from verus-lang/verus-analyzer. The original version
//! depended on the now-removed `SourceDatabaseExt` trait and a couple of
//! direct salsa queries; this re-port routes the same data through the
//! current `SourceDatabase` API and `hir::Semantics::parse`.

use std::collections::HashSet;
use std::path::PathBuf;

use base_db::SourceDatabase;
use clap::Parser as ClapParser;
use hir::{Crate, HasSource, Module, ModuleDef, Semantics, db::HirDatabase};
use load_cargo::{LoadCargoConfig, ProcMacroServerChoice, load_workspace_at};
use project_model::CargoConfig;
use syntax::AstNode;
use syntax::ast::vst;

#[derive(ClapParser)]
struct Args {
    /// Workspace folder to load
    workspace: PathBuf,
}

fn all_modules(db: &dyn HirDatabase) -> Vec<Module> {
    let mut worklist: Vec<_> =
        Crate::all(db).into_iter().map(|krate| krate.root_module(db)).collect();
    let mut modules = Vec::new();

    while let Some(module) = worklist.pop() {
        modules.push(module);
        worklist.extend(module.children(db));
    }

    modules
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let cargo_config = CargoConfig::default();
    let load_cargo_config = LoadCargoConfig {
        load_out_dirs_from_check: true,
        with_proc_macro_server: ProcMacroServerChoice::None,
        prefill_caches: false,
        num_worker_threads: 1,
        proc_macro_processes: 1,
    };

    let (db, vfs, _proc_macro) =
        load_workspace_at(&args.workspace, &cargo_config, &load_cargo_config, &|_| {})?;

    let all_modules = all_modules(&db);
    println!("Found {} total modules", all_modules.len());

    // Filter out modules whose backing file lives in a library source root —
    // those are dependencies, not project code we want to test-lift.
    let work: Vec<Module> = all_modules
        .into_iter()
        .filter(|module| {
            let editioned_file_id = module.definition_source_file_id(&db).original_file(&db);
            let raw_file_id = editioned_file_id.file_id(&db);
            let source_root_id = db.file_source_root(raw_file_id).source_root_id(&db);
            !db.source_root(source_root_id).source_root(&db).is_library
        })
        .collect();
    println!("After filtering, we have {} modules to process", work.len());

    let mut visited_files = HashSet::new();
    let sema = Semantics::new(&db);

    for module in work {
        let editioned_file_id = module.definition_source_file_id(&db).original_file(&db);
        let raw_file_id = editioned_file_id.file_id(&db);
        if !visited_files.insert(raw_file_id) {
            continue;
        }

        let crate_name = module
            .krate(&db)
            .display_name(&db)
            .map(|n| n.canonical_name().as_str().to_owned())
            .unwrap_or_else(|| "unknown".to_owned());
        println!("processing crate: {crate_name}, module: {}", vfs.file_path(raw_file_id));

        let source_file = sema.parse(editioned_file_id);
        println!("Parsed file: {} bytes", u32::from(source_file.syntax().text().len()));

        for def in module.declarations(&db) {
            if let ModuleDef::Function(func) = def {
                let fn_cst = match func.source(&db) {
                    Some(it) => it,
                    None => {
                        println!("Failed to get source for function {:?}", func.name(&db));
                        continue;
                    }
                };
                match vst::Fn::try_from(fn_cst.value) {
                    Ok(_fn_vst) => {
                        // TODO: drive a source-level proof rewrite here once
                        // those rewriters are exposed publicly from
                        // ide-assists::proof_plumber_api.
                    }
                    Err(err) => {
                        println!(
                            "Failed to lift function {:?}: got error: {:?}",
                            func.name(&db),
                            err
                        );
                    }
                }
            }
        }
    }

    Ok(())
}
