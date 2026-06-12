import * as vscode from "vscode";
import * as lc from "vscode-languageclient/node";

import * as commands from "./commands";
import { type CommandFactory, Ctx, fetchWorkspace } from "./ctx";
import * as diagnostics from "./diagnostics";
import { activateTaskProvider } from "./tasks";
import { setContextValue } from "./util";
import { initializeDebugSessionTrackingAndRebuild } from "./debug";

const RUST_PROJECT_CONTEXT_NAME = "inRustProject";

export interface RustAnalyzerExtensionApi {
    // FIXME: this should be non-optional
    readonly client?: lc.LanguageClient;

    // Allows adding a configuration override from another extension.
    // `extensionId` is used to only merge configuration override from present
    // extensions. `configuration` is map of rust-analyzer-specific setting
    // overrides, e.g., `{"cargo.cfgs": ["foo", "bar"]}`.
    addConfiguration(extensionId: string, configuration: Record<string, unknown>): Promise<void>;
}

export async function deactivate() {
    await setContextValue(RUST_PROJECT_CONTEXT_NAME, undefined);
}

export async function activate(
    context: vscode.ExtensionContext,
): Promise<RustAnalyzerExtensionApi> {
    checkConflictingExtensions();

    const ctx = new Ctx(context, createCommands(), fetchWorkspace());
    // VS Code doesn't show a notification when an extension fails to activate
    // so we do it ourselves.
    const api = await activateServer(ctx).catch((err) => {
        void vscode.window.showErrorMessage(
            `Cannot activate verus-analyzer extension: ${err.message}`,
        );
        throw err;
    });
    await setContextValue(RUST_PROJECT_CONTEXT_NAME, true);
    registerVerusCommands(context, ctx);
    return api;
}

function registerVerusCommands(context: vscode.ExtensionContext, ctx: Ctx) {
    const fold = vscode.commands.registerCommand("verus-analyzer.foldProofBlocks", async () => {
        await foldOrUnfoldProofBlocks(ctx, "fold");
    });
    const unfold = vscode.commands.registerCommand("verus-analyzer.unfoldProofBlocks", async () => {
        await foldOrUnfoldProofBlocks(ctx, "unfold");
    });
    context.subscriptions.push(fold, unfold);
}

async function foldOrUnfoldProofBlocks(ctx: Ctx, mode: "fold" | "unfold") {
    const editor = vscode.window.activeTextEditor;
    if (!editor) return;

    const client = ctx.client;
    if (!client) return;

    // VS Code's `executeFoldingRangeProvider` strips the `collapsedText`
    // field, so query the language client directly to preserve it.
    type ProofRange = {
        startLine: number;
        endLine: number;
        kind?: string;
        collapsedText?: string;
    };
    const ranges = (await client.sendRequest("textDocument/foldingRange", {
        textDocument: client.code2ProtocolConverter.asTextDocumentIdentifier(editor.document),
    })) as ProofRange[] | null;
    if (!ranges) return;

    const proofRanges = ranges.filter(
        (r) => r.kind === "region" && r.collapsedText?.trimEnd().endsWith("proof_block"),
    );
    if (proofRanges.length === 0) return;

    if (mode === "unfold") {
        const lines = [...new Set(proofRanges.map((r) => r.startLine))];
        await vscode.commands.executeCommand("editor.unfold", { selectionLines: lines });
        return;
    }

    // Fold inner blocks first, then outer blocks; keep only multiline
    // ranges and deduplicate by start line so repeated runs are idempotent.
    const sortedLines = [
        ...new Set(
            proofRanges
                .filter((r) => r.endLine > r.startLine)
                .sort((a, b) => a.endLine - a.startLine - (b.endLine - b.startLine))
                .map((r) => r.startLine),
        ),
    ];
    if (sortedLines.length === 0) return;

    await vscode.commands.executeCommand("editor.unfold", { selectionLines: sortedLines });
    for (const line of sortedLines) {
        await vscode.commands.executeCommand("editor.fold", { selectionLines: [line] });
    }
}

async function activateServer(ctx: Ctx): Promise<RustAnalyzerExtensionApi> {
    if (ctx.workspace.kind === "Workspace Folder") {
        ctx.pushExtCleanup(activateTaskProvider(ctx.config));
    }

    const diagnosticProvider = new diagnostics.TextDocumentProvider(ctx);
    ctx.pushExtCleanup(
        vscode.workspace.registerTextDocumentContentProvider(
            diagnostics.URI_SCHEME,
            diagnosticProvider,
        ),
    );

    const decorationProvider = new diagnostics.AnsiDecorationProvider(ctx);
    ctx.pushExtCleanup(decorationProvider);

    async function decorateVisibleEditors(document: vscode.TextDocument) {
        for (const editor of vscode.window.visibleTextEditors) {
            if (document === editor.document) {
                await decorationProvider.provideDecorations(editor);
            }
        }
    }

    vscode.workspace.onDidChangeTextDocument(
        async (event) => await decorateVisibleEditors(event.document),
        null,
        ctx.subscriptions,
    );
    vscode.workspace.onDidOpenTextDocument(decorateVisibleEditors, null, ctx.subscriptions);
    vscode.window.onDidChangeActiveTextEditor(
        async (editor) => {
            if (editor) {
                diagnosticProvider.triggerUpdate(editor.document.uri);
                await decorateVisibleEditors(editor.document);
            }
        },
        null,
        ctx.subscriptions,
    );
    vscode.window.onDidChangeVisibleTextEditors(
        async (visibleEditors) => {
            for (const editor of visibleEditors) {
                diagnosticProvider.triggerUpdate(editor.document.uri);
                await decorationProvider.provideDecorations(editor);
            }
        },
        null,
        ctx.subscriptions,
    );

    vscode.workspace.onDidChangeWorkspaceFolders(
        async (_) => ctx.onWorkspaceFolderChanges(),
        null,
        ctx.subscriptions,
    );
    vscode.workspace.onDidChangeConfiguration(
        async (_) => {
            await ctx.client?.sendNotification(lc.DidChangeConfigurationNotification.type, {
                settings: "",
            });
        },
        null,
        ctx.subscriptions,
    );

    if (ctx.config.debug.buildBeforeRestart) {
        initializeDebugSessionTrackingAndRebuild(ctx);
    }

    if (ctx.config.initializeStopped) {
        ctx.setServerStatus({
            health: "stopped",
        });
    } else {
        await ctx.start();
    }

    return ctx;
}

function createCommands(): Record<string, CommandFactory> {
    return {
        onEnter: {
            enabled: commands.onEnter,
            disabled: (_) => () => vscode.commands.executeCommand("default:type", { text: "\n" }),
        },
        restartServer: {
            enabled: (ctx) => async () => {
                await ctx.restart();
            },
            disabled: (ctx) => async () => {
                await ctx.start();
            },
        },
        startServer: {
            enabled: (ctx) => async () => {
                await ctx.start();
            },
            disabled: (ctx) => async () => {
                await ctx.start();
            },
        },
        stopServer: {
            enabled: (ctx) => async () => {
                // FIXME: We should re-use the client, that is ctx.deactivate() if none of the configs have changed
                await ctx.stopAndDispose();
                ctx.setServerStatus({
                    health: "stopped",
                });
            },
            disabled: (_) => async () => {},
        },

        analyzerStatus: { enabled: commands.analyzerStatus },
        memoryUsage: { enabled: commands.memoryUsage },
        reloadWorkspace: { enabled: commands.reloadWorkspace },
        rebuildProcMacros: { enabled: commands.rebuildProcMacros },
        newProject: {
            // Project creation is a pure VS Code-side workflow and should stay available even in
            // empty windows before rust-analyzer has started or a Rust workspace exists.
            enabled: commands.newProject,
            disabled: commands.newProject,
        },
        matchingBrace: { enabled: commands.matchingBrace },
        joinLines: { enabled: commands.joinLines },
        parentModule: { enabled: commands.parentModule },
        childModules: { enabled: commands.childModules },
        viewHir: { enabled: commands.viewHir },
        viewMir: { enabled: commands.viewMir },
        interpretFunction: { enabled: commands.interpretFunction },
        viewFileText: { enabled: commands.viewFileText },
        viewItemTree: { enabled: commands.viewItemTree },
        viewCrateGraph: { enabled: commands.viewCrateGraph },
        viewFullCrateGraph: { enabled: commands.viewFullCrateGraph },
        expandMacro: { enabled: commands.expandMacro },
        run: { enabled: (ctx) => (mode?: "cursor") => commands.run(ctx, mode)() },
        copyRunCommandLine: { enabled: commands.copyRunCommandLine },
        debug: { enabled: commands.debug },
        newDebugConfig: { enabled: commands.newDebugConfig },
        openDocs: { enabled: commands.openDocs },
        openExternalDocs: { enabled: commands.openExternalDocs },
        openCargoToml: { enabled: commands.openCargoToml },
        peekTests: { enabled: commands.peekTests },
        moveItemUp: { enabled: commands.moveItemUp },
        moveItemDown: { enabled: commands.moveItemDown },
        cancelFlycheck: { enabled: commands.cancelFlycheck },
        clearFlycheck: { enabled: commands.clearFlycheck },
        runFlycheck: { enabled: commands.runFlycheck },
        ssr: { enabled: commands.ssr },
        evaluatePredicate: { enabled: commands.evaluatePredicate },
        serverVersion: { enabled: commands.serverVersion },
        viewMemoryLayout: { enabled: commands.viewMemoryLayout },
        toggleCheckOnSave: { enabled: commands.toggleCheckOnSave },
        toggleLSPLogs: { enabled: commands.toggleLSPLogs },
        openWalkthrough: { enabled: commands.openWalkthrough },
        // Internal commands which are invoked by the server.
        applyActionGroup: { enabled: commands.applyActionGroup },
        applySnippetWorkspaceEdit: {
            enabled: commands.applySnippetWorkspaceEditCommand,
        },
        debugSingle: { enabled: commands.debugSingle },
        gotoLocation: { enabled: commands.gotoLocation },
        hoverRefCommandProxy: { enabled: commands.hoverRefCommandProxy },
        resolveCodeAction: { enabled: commands.resolveCodeAction },
        runSingle: { enabled: commands.runSingle },
        showReferences: { enabled: commands.showReferences },
        triggerParameterHints: { enabled: commands.triggerParameterHints },
        rename: { enabled: commands.rename },
        openLogs: { enabled: commands.openLogs },
        revealDependency: { enabled: commands.revealDependency },
        syntaxTreeReveal: { enabled: commands.syntaxTreeReveal },
        syntaxTreeCopy: { enabled: commands.syntaxTreeCopy },
        syntaxTreeHideWhitespace: {
            enabled: commands.syntaxTreeHideWhitespace,
        },
        syntaxTreeShowWhitespace: {
            enabled: commands.syntaxTreeShowWhitespace,
        },
        getFailedObligations: { enabled: commands.getFailedObligations },
    };
}

function checkConflictingExtensions() {
    if (vscode.extensions.getExtension("rust-lang.rust")) {
        vscode.window
            .showWarningMessage(
                `You have both the verus-analyzer (verus-lang.verus-analyzer) and Rust (rust-lang.rust) ` +
                    "plugins enabled. These are known to conflict and cause various functions of " +
                    "both plugins to not work correctly. You should disable one of them.",
                "Got it",
            )
            // eslint-disable-next-line no-console
            .then(() => {}, console.error);
    }
}
