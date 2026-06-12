import * as vscode from "vscode";
import * as os from "os";
import type { Config } from "./config";
import { type Env, log, RUST_TOOLCHAIN_FILES, spawnAsync } from "./util";
import type { PersistentState } from "./persistent_state";
import { exec, execFile } from "child_process";
import { TextDecoder } from "node:util";
import { promisify } from "util";

const execFileAsync = promisify(execFile);

export async function bootstrap(
    context: vscode.ExtensionContext,
    config: Config,
    state: PersistentState,
): Promise<string> {
    const path = await getServer(context, config, state);
    if (!path) {
        throw new Error(
            "verus-analyzer Language Server is not available. " +
                "Please, ensure its [proper installation](https://github.com/verus-lang/verus-analyzer/).",
        );
    }

    log.info("Using server binary at", path);

    if (!isValidExecutable(path, config.serverExtraEnv)) {
        throw new Error(
            `Failed to execute ${path} --version.` +
                (config.serverPath
                    ? `\`config.server.path\` or \`config.serverPath\` has been set explicitly.\
            Consider removing this config or making a valid server binary available at that path.`
                    : ""),
        );
    }

    return path;
}

/// Run `<verusPath> --version` and return the version string from the
/// Verus banner, or "unknown" if the binary is missing/fails. Only used
/// to enrich the status-bar tooltip; not on any hot path.
export async function getVerusVersion(verusPath: string | undefined): Promise<string> {
    log.info("Getting Verus version using Verus binary: ", verusPath);
    if (verusPath === undefined || verusPath === "") {
        return "unknown";
    }
    try {
        const { stdout } = await execFileAsync(verusPath, ["--version"]);
        const versionRegex = /Version: (.*)/m;
        const matches = versionRegex.exec(stdout);
        if (matches !== null && matches.length > 1 && matches[1] !== undefined) {
            log.info("Found Verus version: ", matches[1]);
            return matches[1];
        }
        log.info("Failed to find Verus version in: ", stdout);
        return "unknown";
    } catch (err) {
        log.info("Failed to invoke Verus binary: ", err);
        return "unknown";
    }
}

async function getServer(
    context: vscode.ExtensionContext,
    config: Config,
    state: PersistentState,
): Promise<string | undefined> {
    const packageJson: {
        version: string;
        releaseTag: string | null;
        enableProposedApi: boolean | undefined;
    } = context.extension.packageJSON;

    // check if the server path is configured explicitly
    const explicitPath = process.env["__RA_LSP_SERVER_DEBUG"] ?? config.serverPath;
    if (explicitPath) {
        if (explicitPath.startsWith("~/")) {
            return os.homedir() + explicitPath.slice("~".length);
        }
        return explicitPath;
    }

    let toolchainServerPath = undefined;
    if (vscode.workspace.workspaceFolders) {
        for (const workspaceFolder of vscode.workspace.workspaceFolders) {
            // otherwise check if there is a toolchain override for the current vscode workspace
            // and if the toolchain of this override has a rust-analyzer component
            // if so, use the rust-analyzer component
            // Check both rust-toolchain.toml and rust-toolchain files
            for (const toolchainFile of RUST_TOOLCHAIN_FILES) {
                const toolchainUri = vscode.Uri.joinPath(workspaceFolder.uri, toolchainFile);
                if (!(await hasToolchainFileWithRaDeclared(toolchainUri))) {
                    continue;
                }
                const res = await spawnAsync("rustup", ["which", "rust-analyzer"], {
                    env: { ...process.env },
                    cwd: workspaceFolder.uri.fsPath,
                });
                if (!res.error && res.status === 0) {
                    toolchainServerPath = await earliestToolchainPath(
                        toolchainServerPath,
                        res.stdout.trim(),
                        raVersionResolver,
                    );
                    break;
                }
            }
        }
    }
    if (toolchainServerPath) {
        return toolchainServerPath;
    }

    if (packageJson.releaseTag === null) return "rust-analyzer";

    // finally, use the bundled one
    const ext = process.platform === "win32" ? ".exe" : "";
    const bundled = vscode.Uri.joinPath(context.extensionUri, "server", `verus-analyzer${ext}`);
    const bundledExists = await fileExists(bundled);
    if (bundledExists) {
        let server = bundled;
        if (await isNixOs()) {
            server = await getNixOsServer(
                context.globalStorageUri,
                packageJson.version,
                ext,
                state,
                bundled,
                server,
            );
            await state.updateServerVersion(packageJson.version);
        }
        return server.fsPath;
    }

    await vscode.window.showErrorMessage(
        "Unfortunately we don't ship binaries for your platform yet. " +
            "You need to manually clone the verus-analyzer repository and " +
            "run `cargo xtask install --server` to build the language server from sources. " +
            "If you feel that your platform should be supported, please create an issue " +
            "about that [here](https://github.com/verus-lang/verus-analyzer/issues) and we " +
            "will consider it.",
    );
    return undefined;
}

// Given a path to a rust-analyzer executable, resolve its version and return it.
async function raVersionResolver(path: string): Promise<string | undefined> {
    const res = await spawnAsync(path, ["--version"]);
    if (!res.error && res.status === 0) {
        return res.stdout;
    } else {
        return undefined;
    }
}

// Given a path to two rust-analyzer executables, return the earliest one by date.
async function earliestToolchainPath(
    path0: string | undefined,
    path1: string,
    raVersionResolver: (path: string) => Promise<string | undefined>,
): Promise<string> {
    if (path0) {
        if (
            (await orderFromPath(path0, raVersionResolver)) <
            (await orderFromPath(path1, raVersionResolver))
        ) {
            return path0;
        } else {
            return path1;
        }
    } else {
        return path1;
    }
}

// Further to extracting a date for comparison, determine the order of a toolchain as follows:
//  Highest - nightly
//  Medium  - versioned
//  Lowest  - stable
// Example paths:
//  nightly   - /Users/myuser/.rustup/toolchains/nightly-2022-11-22-aarch64-apple-darwin/bin/rust-analyzer
//  versioned - /Users/myuser/.rustup/toolchains/1.72.1-aarch64-apple-darwin/bin/rust-analyzer
//  stable    - /Users/myuser/.rustup/toolchains/stable-aarch64-apple-darwin/bin/rust-analyzer
async function orderFromPath(
    path: string,
    raVersionResolver: (path: string) => Promise<string | undefined>,
): Promise<string> {
    const raVersion = await raVersionResolver(path);
    const raDate = raVersion?.match(/^rust-analyzer .*\(.* (\d{4}-\d{2}-\d{2})\)$/);
    if (raDate?.length === 2) {
        const precedence = path.includes("nightly-") ? "0" : "1";
        return "0-" + raDate[1] + "/" + precedence;
    } else {
        return "2";
    }
}

async function fileExists(uri: vscode.Uri) {
    return await vscode.workspace.fs.stat(uri).then(
        () => true,
        () => false,
    );
}

async function hasToolchainFileWithRaDeclared(uri: vscode.Uri): Promise<boolean> {
    try {
        const toolchainFileContents = new TextDecoder().decode(
            await vscode.workspace.fs.readFile(uri),
        );
        return (
            toolchainFileContents.match(/components\s*=\s*\[.*"rust-analyzer".*\]/g)?.length === 1
        );
    } catch (_) {
        return false;
    }
}

/// Locate `rustup` on `PATH`, or fall back to the standard Cargo install
/// location (`$CARGO_HOME/bin/rustup` or `~/.cargo/bin/rustup`).
export async function findRustup(): Promise<{ path: string | undefined }> {
    const which = require("which") as (cmd: string) => Promise<string>;
    try {
        const resolvedPath = await which("rustup");
        log.info("Found rustup at: " + resolvedPath);
        return { path: resolvedPath };
    } catch (error: unknown) {
        log.warn("Caught an error while running `which(rustup)`: " + error);
        log.info("Attempting to find rustup in standard Cargo installation location...");

        const ext = process.platform === "win32" ? ".exe" : "";
        const cargoHome =
            process.env["CARGO_HOME"] ??
            (process.platform === "win32"
                ? `${process.env["USERPROFILE"]}\\.cargo`
                : `${os.homedir()}/.cargo`);
        const rustupPath = `${cargoHome}/bin/rustup${ext}`;

        try {
            const fs = await import("node:fs/promises");
            const stats = await fs.stat(rustupPath);
            if (stats.isFile()) {
                log.info("Found rustup at standard location: " + rustupPath);
                return { path: rustupPath };
            }
        } catch (statError: unknown) {
            log.warn(`Failed to find rustup at ${rustupPath}: ${statError}`);
        }

        return { path: undefined };
    }
}

/// Verify that the Rust toolchain version expected by Verus is installed
/// via rustup. Returns `true` when found, otherwise shows an error message
/// and returns `false`.
export async function validRustToolchain(): Promise<boolean> {
    // TODO: Add a config flag for the expected toolchain version
    const TOOLCHAIN_FULL = 1;
    const TOOLCHAIN_MAJOR = 97;
    const TOOLCHAIN_MINOR = 1;

    const { path: rustupExecutable } = await findRustup();
    if (!rustupExecutable) {
        await vscode.window.showErrorMessage("Failed to find rustup executable!");
        return false;
    }
    try {
        const fs = await import("node:fs/promises");
        const stats = await fs.stat(rustupExecutable);
        if (!stats.isFile()) {
            await vscode.window.showErrorMessage(rustupExecutable + " is not a valid file.");
            return false;
        }
        const { stdout } = await execFileAsync(rustupExecutable, ["toolchain", "list"]);
        const versionRegex = /(\d+)\.(\d+)\.(\d+)-/gi;
        const toolchainVersions = [...stdout.matchAll(versionRegex)].map((match) => {
            if (match[1] === undefined || match[2] === undefined || match[3] === undefined) {
                log.warn("Undefined rustup version match groups: ", match);
                return { full: 0, major: 0, minor: 0 };
            }
            const full = parseInt(match[1], 10);
            const major = parseInt(match[2], 10);
            const minor = parseInt(match[3], 10);
            log.info(`Found a Rust toolchain version: ${full}.${major}.${minor}`);
            return { full, major, minor };
        });
        const matched = toolchainVersions.find(
            ({ full, major, minor }) =>
                full === TOOLCHAIN_FULL && major === TOOLCHAIN_MAJOR && minor === TOOLCHAIN_MINOR,
        );
        if (matched === undefined) {
            const toolchainStr = `${TOOLCHAIN_FULL}.${TOOLCHAIN_MAJOR}.${TOOLCHAIN_MINOR}`;
            const cmd = `rustup toolchain install ${toolchainStr}`;
            await vscode.window.showErrorMessage(
                "Failed to find the Rust toolchain needed for Verus.  Try installing it by running: " +
                    cmd,
            );
            return false;
        }
        log.info("Found the expected rustup version");
        return true;
    } catch (error: unknown) {
        const errorMsg = `Error invoking ${rustupExecutable} toolchain list: ${error}`;
        log.warn(errorMsg);
        return false;
    }
}

/// Resolve the Verus binary to use, in priority order:
///   1. The user-configured `verus.verusBinary` path (if set), with `~/` expanded.
///   2. A previously-downloaded binary in `${extensionUri}/verus/`.
///   3. (Only when `verus.autoFetch` is enabled) the latest GitHub release
///      for the current platform/arch, downloaded into `${extensionUri}/verus/`.
/// Returns `undefined` when no binary could be located.
export async function getVerus(
    context: vscode.ExtensionContext,
    config: Config,
): Promise<string | undefined> {
    const explicitPath = config.verusBinary;
    log.info("Explicit path to Verus binary: ", explicitPath);
    if (explicitPath) {
        if (explicitPath.startsWith("~/")) {
            const absPath = os.homedir() + explicitPath.slice("~".length);
            log.info("Absolute path to Verus binary:", absPath);
            return absPath;
        }
        return explicitPath;
    }

    const targetDir = vscode.Uri.joinPath(context.extensionUri, "verus");
    const ext = process.platform === "win32" ? ".exe" : "";
    const targetBinary = vscode.Uri.joinPath(targetDir, `verus${ext}`);
    const targetDirExists = await vscode.workspace.fs.stat(targetDir).then(
        () => true,
        () => false,
    );
    if (targetDirExists) {
        log.info(
            "Verus is already installed at: ",
            targetBinary.fsPath,
            ".  No further work needed.",
        );
        return targetBinary.fsPath;
    }

    if (!config.verusAutoFetch) {
        log.info(
            "Verus binary is not configured and `verus.verusBinary`/`verus.autoFetch` are disabled; skipping download.",
        );
        return undefined;
    }

    void vscode.window.showInformationMessage(
        "Attempting to determine the version of Verus's latest release...",
    );
    const result = await fetch("https://api.github.com/repos/verus-lang/verus/releases/latest", {
        method: "get",
        headers: {
            Accept: "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
        },
    });

    if (result.status >= 400) {
        throw new Error(
            "Bad response from server when attempting to fetch the latest Verus release.",
        );
    }

    let platform = "";
    let releaseDir = "";
    if (process.platform === "win32") {
        platform = "win";
        releaseDir = "verus-x86-win";
    } else if (process.platform === "darwin" && process.arch === "x64") {
        platform = "x86-macos";
        releaseDir = "verus-x86-macos";
    } else if (process.platform === "darwin") {
        platform = "arm64-macos";
        releaseDir = "verus-arm64-macos";
    } else if (process.platform === "linux") {
        platform = "linux";
        releaseDir = "verus-x86-linux";
    } else {
        await vscode.window.showErrorMessage(
            "Unfortunately we don't ship Verus binaries for your platform yet. " +
                "You need to manually clone the verus repository and build it from sources. " +
                "If you feel that your platform should be supported, please create an issue " +
                "about that [here](https://github.com/verus-lang/verus/issues) and we " +
                "will consider it.",
        );
        return undefined;
    }
    log.info("Looking for a release for your platform, which we have identified as:", platform);
    log.info("We will save the downloaded Verus binaries in:", releaseDir);

    const releaseData = (await result.json()) as {
        assets: { name: string; browser_download_url: string }[];
    };
    for (const asset of releaseData.assets) {
        log.info("Found release asset: ", asset.name);
        log.info("Index of your platform in the asset's name: ", asset.name.indexOf(platform));
        if (asset.name.indexOf(platform) >= 0) {
            void vscode.window.showInformationMessage(
                `Attempting to download Verus's latest release (${asset.name})...`,
            );
            const url = asset.browser_download_url;
            log.info("Retrieving release from this URL:", url);
            const response = await fetch(url);
            const downloadedRelease = vscode.Uri.joinPath(context.extensionUri, asset.name);
            await vscode.workspace.fs.writeFile(
                downloadedRelease,
                new Uint8Array(await response.arrayBuffer()),
            );
            const decompress = require("decompress") as (
                input: string,
                output: string,
            ) => Promise<unknown>;
            const unzipDir = vscode.Uri.joinPath(context.extensionUri, "unzipped");
            await decompress(downloadedRelease.fsPath, unzipDir.fsPath);
            const srcDir = vscode.Uri.joinPath(unzipDir, releaseDir);
            await vscode.workspace.fs.rename(srcDir, targetDir);
            void vscode.window.showInformationMessage("Verus download completed successfully.");
            void vscode.window.showInformationMessage(
                "Verus will run each time you save your file.",
            );

            return targetBinary.fsPath;
        }
    }
    await vscode.window.showErrorMessage(
        "We failed to find a Verus release asset matching your platform! " +
            `Consider manually installing it from [here](https://github.com/verus-lang/verus/) into: ${targetDir.fsPath}`,
    );
    return undefined;
}

export async function isValidExecutable(path: string, extraEnv: Env): Promise<boolean> {
    log.debug("Checking availability of a binary at", path);

    const newEnv = { ...process.env };
    for (const [k, v] of Object.entries(extraEnv)) {
        if (v) {
            newEnv[k] = v;
        } else if (k in newEnv) {
            delete newEnv[k];
        }
    }
    const res = await spawnAsync(path, ["--version"], {
        env: newEnv,
    });

    if (res.error) {
        log.warn(path, "--version:", res);
    } else {
        log.info(path, "--version:", res);
    }
    return res.status === 0;
}

async function getNixOsServer(
    globalStorageUri: vscode.Uri,
    version: string,
    ext: string,
    state: PersistentState,
    bundled: vscode.Uri,
    server: vscode.Uri,
) {
    await vscode.workspace.fs.createDirectory(globalStorageUri).then();
    const dest = vscode.Uri.joinPath(globalStorageUri, `verus-analyzer${ext}`);
    let exists = await vscode.workspace.fs.stat(dest).then(
        () => true,
        () => false,
    );
    if (exists && version !== state.serverVersion) {
        await vscode.workspace.fs.delete(dest);
        exists = false;
    }
    if (!exists) {
        await vscode.workspace.fs.copy(bundled, dest);
        await patchelf(dest);
    }
    server = dest;
    return server;
}

async function isNixOs(): Promise<boolean> {
    try {
        const contents = (
            await vscode.workspace.fs.readFile(vscode.Uri.file("/etc/os-release"))
        ).toString();
        const idString = contents.split("\n").find((a) => a.startsWith("ID=")) || "ID=linux";
        return idString.indexOf("nixos") !== -1;
    } catch {
        return false;
    }
}

async function patchelf(dest: vscode.Uri): Promise<void> {
    await vscode.window.withProgress(
        {
            location: vscode.ProgressLocation.Notification,
            title: "Patching verus-analyzer for NixOS",
        },
        async (progress, _) => {
            const expression = `
            {srcStr, pkgs ? import <nixpkgs> {}}:
                pkgs.stdenv.mkDerivation {
                    name = "verus-analyzer";
                    src = /. + srcStr;
                    phases = [ "installPhase" "fixupPhase" ];
                    installPhase = "cp $src $out";
                    fixupPhase = ''
                    chmod 755 $out
                    patchelf --set-interpreter "$(cat $NIX_CC/nix-support/dynamic-linker)" $out
                    '';
                }
            `;
            const origFile = vscode.Uri.file(dest.fsPath + "-orig");
            await vscode.workspace.fs.rename(dest, origFile, { overwrite: true });
            try {
                progress.report({ message: "Patching executable", increment: 20 });
                await new Promise((resolve, reject) => {
                    const handle = exec(
                        `nix-build -E - --argstr srcStr '${origFile.fsPath}' -o '${dest.fsPath}'`,
                        (err, stdout, stderr) => {
                            if (err != null) {
                                reject(Error(stderr));
                            } else {
                                resolve(stdout);
                            }
                        },
                    );
                    handle.stdin?.write(expression);
                    handle.stdin?.end();
                });
            } finally {
                await vscode.workspace.fs.delete(origFile);
            }
        },
    );
}

export const _private = {
    earliestToolchainPath,
    orderFromPath,
};
