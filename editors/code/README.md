# verus-analyzer-rebased

This extension provides support for the [Verus programming language](https://github.com/verus-lang/verus).
It is derived from [rust-analyzer](https://rust-analyzer.github.io/).

This extension is **experimental** and subject to change; some features are likely broken.
At present, it works best on small, self-contained Verus projects. Anything more complex
will likely fail.

**WARNING**: `verus-analyzer` expects you to "Open Folder..." on
a directory containing a standard Rust project layout and metadata (`Cargo.toml`) file.
`verus-analyzer` scans the project root (`src/lib.rs` or `src/main.rs`) and all files
that are reachable from the root. If the file you are working on is not
reachable from the project root, most of the IDE features like "Go to Definition" will not work.

## Verus-specific Features

- Support for Verus syntax
- Each time you save a file in your project, Verus runs and reports proof failures and warnings
- [Proof actions](https://www.andrew.cmu.edu/user/bparno/papers/proof-plumber.pdf) are an **experimental**
  feature to assist developers when debugging proof failures. They show up as
  light bulb icons in the IDE when you hover over a failed proof.

## Features Extended from Rust Analyzer

- [code completion] with [imports insertion]
- go to [definition], [implementation], [type definition]
- [find all references], [workspace symbol search], [symbol renaming]
- [types and documentation on hover]
- [inlay hints] for types and parameter names
- [semantic syntax highlighting]
- a lot of [assists (code actions)]
- apply suggestions from errors
- ... and many more, check out the [manual] to see them all

[code completion]: https://rust-analyzer.github.io/book/features.html#magic-completions
[imports insertion]: https://rust-analyzer.github.io/book/features.html#completion-with-autoimport
[definition]: https://rust-analyzer.github.io/book/features.html#go-to-definition
[implementation]: https://rust-analyzer.github.io/book/features.html#go-to-implementation
[type definition]: https://rust-analyzer.github.io/book/features.html#go-to-type-definition
[find all references]: https://rust-analyzer.github.io/book/features.html#find-all-references
[workspace symbol search]: https://rust-analyzer.github.io/book/features.html#workspace-symbol
[symbol renaming]: https://rust-analyzer.github.io/book/features.html#rename
[types and documentation on hover]: https://rust-analyzer.github.io/book/features.html#hover
[inlay hints]: https://rust-analyzer.github.io/book/features.html#inlay-hints
[semantic syntax highlighting]: https://rust-analyzer.github.io/book/features.html#semantic-syntax-highlighting
[assists (code actions)]: https://rust-analyzer.github.io/book/assists.html
[manual]: https://rust-analyzer.github.io/book/features.html

## Quick start

1. Ensure you have [rustup] installed.
2. Install the [verus-analyzer-rebased extension].

[rustup]: https://rustup.rs
[verus-analyzer-rebased extension]: https://marketplace.visualstudio.com/items?itemName=rikosellic.verus-analyzer-rebased

## Configuration

This extension provides configurations through VSCode's configuration settings. All configurations are under `verus-analyzer.*`.

See [the Rust analyzer manual](https://rust-analyzer.github.io/book/editor_features.html#vs-code) for more information on VSCode-specific configurations.

## Communication

For usage and troubleshooting requests, please use the [Verus Zulip](https://verus-lang.zulipchat.com/).

## Documentation

See [rust-analyzer.github.io](https://rust-analyzer.github.io/) for more information about the original Rust analyzer.
