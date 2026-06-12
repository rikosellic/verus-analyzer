//! Verus-specific flycheck command construction.
//!
//! Ported from the verus-lang/verus-analyzer fork's `run_cargo_verus` /
//! `run_verus_direct` helpers in `crates/flycheck/src/lib.rs`.

use std::path::{Path, PathBuf};
use std::process::Command;

use paths::AbsPath;

use crate::flycheck::CargoOptions;

/// Resolve the `verus` binary. Returns the absolute path on success.
fn verus_binary() -> PathBuf {
    let raw = std::env::var("VERUS_BINARY_PATH").unwrap_or_else(|_| {
        tracing::warn!("VERUS_BINARY_PATH was not set, falling back to `verus` on $PATH");
        "verus".to_owned()
    });
    Path::new(&raw).canonicalize().unwrap_or_else(|_| PathBuf::from(raw))
}

/// Read `[package.metadata.verus.ide].extra_args = "..."` out of a
/// `Cargo.toml`, returning the parsed argv.
fn extra_args_from_cargo_toml(cargo_toml: &Path) -> Vec<String> {
    let Ok(toml) = std::fs::read_to_string(cargo_toml) else {
        return Vec::new();
    };
    let mut found_section = false;
    for line in toml.lines() {
        if found_section {
            if let Some(rest) = line.trim_start().strip_prefix("extra_args") {
                let mut s = rest.trim().to_owned();
                if let Some(stripped) = s.strip_prefix('=') {
                    s = stripped.trim().to_owned();
                }
                let s = s.trim().trim_matches('"').to_owned();
                return s.split_whitespace().map(str::to_owned).collect();
            }
            // Stop scanning once we leave the section.
            return Vec::new();
        }
        if line.contains("[package.metadata.verus.ide]") {
            found_section = true;
        }
    }
    Vec::new()
}

// Convert the file name into a module name, so we only receive errors for the file the developer is working on
fn module_args(workspace_root: &AbsPath, file: &Path) -> Vec<String> {
    let src_dir = workspace_root.join("src");
    let lib_rs = src_dir.join("lib.rs");
    let main_rs = src_dir.join("main.rs");
    let abs_file = std::path::absolute(file).unwrap_or_else(|_| file.to_path_buf());

    if abs_file == AsRef::<Path>::as_ref(&lib_rs) || abs_file == AsRef::<Path>::as_ref(&main_rs) {
        return vec!["--verify-root".to_owned()];
    }

    if let Ok(rel) = abs_file.strip_prefix(AsRef::<Path>::as_ref(&src_dir)) {
        let module = rel
            .to_string_lossy()
            .replace(std::path::MAIN_SEPARATOR_STR, "::")
            .replace(".rs", "")
            // Trimming `::mod` instead of trimming `mod` and conditionally
            // checking for a `::` before it. This works because a `mod.rs`
            // file at the source root can define a module called `mod`.
            .trim_end_matches("::mod")
            .to_owned();
        return vec!["--verify-module".to_owned(), module];
    }
    vec!["--verify-root".to_owned()]
}

/// `cargo verus verify` invocation.
pub(crate) fn run_cargo_verus(
    workspace_root: &AbsPath,
    saved_file: &AbsPath,
    verus_args: &[String],
    cargo_options: &CargoOptions,
    report_all_errors: bool,
) -> Command {
    let verus = verus_binary();
    let cargo_verus = verus
        .parent()
        .map(|p| p.join(if cfg!(windows) { "cargo-verus.exe" } else { "cargo-verus" }))
        .unwrap_or_else(|| PathBuf::from("cargo-verus"));

    let mut cmd = Command::new(cargo_verus);
    let extra_from_toml = extra_args_from_cargo_toml(workspace_root.join("Cargo.toml").as_ref());

    // Cargo command
    cmd.arg("verify");
    // Provide the cargo arguments
    cmd.arg("--message-format=json");
    cargo_options.apply_on_command(&mut cmd, None, None);
    cmd.args(&cargo_options.extra_args);
    // Provide the Verus arguments
    cmd.arg("--");
    cmd.args(verus_args);
    cmd.args(&extra_from_toml);
    if !report_all_errors {
        cmd.args(module_args(workspace_root, saved_file.as_ref()));
    }
    cmd.current_dir(workspace_root);
    cmd
}

/// Direct `verus <file>` invocation (no cargo).
pub(crate) fn run_verus_direct(
    workspace_root: &AbsPath,
    saved_file: &AbsPath,
    verus_args: &[String],
    report_all_errors: bool,
) -> Command {
    let verus = verus_binary();
    let mut cmd = Command::new(verus);

    let saved_path: &Path = saved_file.as_ref();
    let mut toml_dir: Option<PathBuf> = None;
    let mut extra_from_toml = Vec::new();
    for ans in saved_path.ancestors() {
        let manifest = ans.join("Cargo.toml");
        if manifest.exists() {
            extra_from_toml = extra_args_from_cargo_toml(&manifest);
            toml_dir = Some(ans.to_path_buf());
            break;
        }
    }

    // We may need to add additional configuration arguments
    let mut config_args: Vec<String> = Vec::new(); // File name and crate type
    let mut module_args: Vec<String> = Vec::new(); // Arguments to restrict verification to the file currently being edited
    match toml_dir {
        None => {
            // This file doesn't appear to be part of a larger project
            // Try to invoke Verus on it directly, but try to avoid
            // complaints about missing `fn main()`
            config_args.push("--crate-type".to_owned());
            config_args.push("lib".to_owned());
        }
        Some(toml_dir) => {
            // This file appears to be part of a Rust project.
            // If it's not the root file, then we need to
            // invoke Verus on the root file and then filter for results in the current file
            let main_rs = toml_dir.join("src").join("main.rs");
            let lib_rs = toml_dir.join("src").join("lib.rs");
            let root_file = if main_rs.exists() {
                Some(main_rs)
            } else if lib_rs.exists() {
                config_args.push("--crate-type".to_owned());
                config_args.push("lib".to_owned());
                Some(lib_rs)
            } else {
                None
            };

            match root_file {
                Some(root_file) => {
                    config_args.insert(0, root_file.to_string_lossy().into_owned());
                    if saved_path != root_file
                        && let Ok(rel) = saved_path.strip_prefix(toml_dir.join("src"))
                    {
                        let module = rel
                            .to_string_lossy()
                            .replace(std::path::MAIN_SEPARATOR_STR, "::")
                            .replace(".rs", "")
                            // Trimming `::mod` instead of trimming `mod` and conditionally
                            // checking for a `::` before it. This works because a `mod.rs`
                            // file at the source root can define a module called `mod`.
                            .trim_end_matches("::mod")
                            .to_owned();
                        module_args.push("--verify-module".to_owned());
                        module_args.push(module);
                    }
                }
                None => {
                    // Puzzling -- we found a Cargo.toml but no root file.
                    // Do our best by trying to run directly on the file supplied
                    config_args.insert(0, saved_path.to_string_lossy().into_owned());
                    config_args.push("--crate-type".to_owned());
                    config_args.push("lib".to_owned());
                }
            }
        }
    }

    // Apply all of the argument collections
    cmd.args(verus_args);
    cmd.args(&config_args);
    cmd.args(&extra_from_toml);
    if !report_all_errors {
        cmd.args(&module_args);
    }
    // Apply arguments that go to rustc instead of Verus
    cmd.arg("--");
    cmd.arg("--error-format=json");
    cmd.current_dir(workspace_root);
    cmd
}
