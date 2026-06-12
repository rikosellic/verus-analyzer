# Differences from Upstream Verus Analyzer

This page summarizes the main user-visible and architectural differences between `verus-analyzer-rebased` and the upstream `verus-lang/verus-analyzer` project.

## New Features

### Go to Definition in More Verus Constructs

Go to Definition has been extended for several  previously unsupported constructs. This includes:

- names and function calls used inside `requires`, `ensures`, and `default_ensures` clauses;
- `broadcast group` declarations and `broadcast use` references.

### Stronger Type Inference：

Notable improvements include:

- Verus types such as `int`, `nat`, and `real`, including suffixed literals like `0int`, `0nat`, and `0real`;
- `value@` expressions;
- `Map<K, V>`.

### Hover Shows Function Mode

Function hover and display strings now include Verus function modes (`spec`, `proof`, `axiom`). Plain exec functions continue to display like normal Rust functions, so `exec` is not shown.

## Fixes

- **Empty Contract Clauses:** The parser allows empty `requires`, `ensures`, and `default_ensures` clauses.

- **Problem Source Name:** Diagnostics reported by the extension use `verus-analyzer` as the Problems
source/provider name.

## Implementation Changes

- **Verus Flycheck Uses the Standard Restart Path:** The Verus flycheck path now uses the standard `restart_workspace`
flow. The old separate `restart_verus` path has been removed to avoid racing.

- **Verus Syntax Is Carried Farther Through the Stack:** The rebase ports more Verus-specific syntax from parser output into syntax AST, HIR lowering, name resolution, IDE navigation, MIR lowering, and type inference.

## Known Limitations

- Type inference does not perform full Verus mode checking for `proof/tracked` and `ghost/spec`. It only tracks a rough spec-vs-exec distinction to allow/disallow chaining comparisons and broader integer-family comparisons.
- `#[verus_spec]` attribute syntax is not supported yet.
- Implementations of traits derived by `external_trait_extension` can be reported as errors incorrectly.
