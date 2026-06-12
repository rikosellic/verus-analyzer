//! Adapters that translate Verus's textual cargo-metadata diagnostics into
//! the structured [`VerusError`] form consumed by the proof_action assists.
//!
//! Ported verbatim from verus-lang/verus-analyzer; the only modernization is
//! the `flycheck::Diagnostic` re-export which now lives inside the
//! `rust-analyzer` crate (it used to be a standalone `flycheck` crate).

use ide::proof_plumber_api::verus_error::{AssertFailure, PostFailure, PreFailure, VerusError};
use syntax::{TextRange, TextSize};

use crate::flycheck::Diagnostic;

pub(crate) fn diagnostic_to_verus_err(diagnostic: &Diagnostic) -> Option<VerusError> {
    if diagnostic.message.contains("precondition not satisfied") {
        if diagnostic.spans.len() == 2 {
            let range0 = TextRange::new(
                TextSize::from(diagnostic.spans[0].byte_start),
                TextSize::from(diagnostic.spans[0].byte_end),
            );
            let range1 = TextRange::new(
                TextSize::from(diagnostic.spans[1].byte_start),
                TextSize::from(diagnostic.spans[1].byte_end),
            );
            let verr = if diagnostic.spans[0].is_primary {
                VerusError::Pre(PreFailure { failing_pre: range1, callsite: range0 })
            } else {
                VerusError::Pre(PreFailure { failing_pre: range0, callsite: range1 })
            };
            Some(verr)
        } else {
            None
        }
    } else if diagnostic.message.contains("postcondition not satisfied") {
        if diagnostic.spans.len() == 2 {
            let range0 = TextRange::new(
                TextSize::from(diagnostic.spans[0].byte_start),
                TextSize::from(diagnostic.spans[0].byte_end),
            );
            let range1 = TextRange::new(
                TextSize::from(diagnostic.spans[1].byte_start),
                TextSize::from(diagnostic.spans[1].byte_end),
            );
            let verr = if diagnostic.spans[0].is_primary {
                VerusError::Post(PostFailure { failing_post: range0, func_name: range1 })
            } else {
                VerusError::Post(PostFailure { failing_post: range1, func_name: range0 })
            };
            Some(verr)
        } else {
            None
        }
    } else if diagnostic.message.contains("assertion failed") {
        let span = diagnostic.spans.first()?;
        let range = TextRange::new(TextSize::from(span.byte_start), TextSize::from(span.byte_end));
        Some(VerusError::Assert(AssertFailure { range }))
    } else {
        None
    }
}
