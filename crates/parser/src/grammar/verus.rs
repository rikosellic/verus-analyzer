use types::type_no_bounds;

use super::{items::ITEM_RECOVERY_SET, *};

/// Returns `true` when `p` is at a Verus function-signature clause keyword
/// (`requires`, `recommends`, `ensures`, `default_ensures`, `returns`,
/// `decreases`, `opens_invariants`, `no_unwind`, `by`, `via`, `when`).
/// Used to keep the standard `fn` parser from misrecovering these keywords
/// as a missing `-> RetType`.
pub(crate) fn at_signature_clause_kw(p: &Parser<'_>) -> bool {
    p.at_contextual_kw(T![requires])
        || p.at_contextual_kw(T![recommends])
        || p.at_contextual_kw(T![ensures])
        || p.at_contextual_kw(T![default_ensures])
        || p.at_contextual_kw(T![returns])
        || p.at_contextual_kw(T![decreases])
        || p.at_contextual_kw(T![opens_invariants])
        || p.at_contextual_kw(T![no_unwind])
        || p.at_contextual_kw(T![by])
}

// referenced atom::closure_expr
pub(crate) fn verus_closure_expr(
    p: &mut Parser<'_>,
    m: Option<Marker>,
    forbid_structs: bool,
) -> CompletedMarker {
    let m = match m {
        Some(m) => m,
        None => p.start(),
    };
    p.eat_contextual_kw(T![forall]);
    p.eat_contextual_kw(T![exists]);
    p.eat_contextual_kw(T![choose]);

    if !p.at(T![|]) {
        p.error("expected `|`");
        return m.complete(p, CLOSURE_EXPR);
    }
    params::param_list_closure(p);
    attributes::inner_attrs(p);
    if forbid_structs {
        expressions::expr_no_struct(p);
    } else {
        expressions::expr(p);
    }
    m.complete(p, CLOSURE_EXPR)
}

pub(crate) fn verus_ret_type(p: &mut Parser<'_>) -> bool {
    if p.at(T![->]) {
        let m = p.start();
        p.bump(T![->]);
        if p.at_contextual_kw(T![tracked]) {
            p.expect_contextual_kw(T![tracked]);
        }
        // test tracked_tuple_ret_type
        // proof fn f() -> (tracked (x, y): (A, B)) {}
        // exec fn f() -> ((res, perm): (A, B)) {}
        let normal_named_param =
            p.at(T!['(']) && p.nth_at(1, IDENT) && p.nth_at(2, T![:]) && !p.nth_at(2, T![::]);
        let tuple_pattern_named_param =
            p.at(T!['(']) && p.nth_at(1, T!['(']) && p.nth_at(2, IDENT) && p.nth_at(3, T![,]);
        let tracked_named_param = p.at(T!['('])
            && p.nth_at_contextual_kw(1, T![tracked])
            && (p.nth_at(2, IDENT) && p.nth_at(3, T![:]) && !p.nth_at(3, T![::])
                || p.nth_at(2, T!['(']));
        if normal_named_param || tuple_pattern_named_param || tracked_named_param
        // tracked named param
        {
            // verus named param
            p.bump(T!['(']);
            if p.at_contextual_kw(T![tracked]) {
                p.expect_contextual_kw(T![tracked]);
            }
            patterns::pattern(p);
            p.expect(T![:]);
            types::type_no_bounds(p);
            p.expect(T![')']);
        } else {
            types::type_no_bounds(p);
        }
        m.complete(p, RET_TYPE);
        true
    } else {
        false
    }
}

pub(crate) fn proof_fn_type(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.eat_contextual_kw(T![proof_fn]);
    proof_fn_characteristics(p);
    generic_params::opt_generic_param_list(p);
    if p.at(T!['(']) {
        params::param_list_fn_ptr(p);
    } else {
        p.error("expected parameters");
    }
    verus_ret_type(p);
    m.complete(p, PROOF_FN_TYPE)
}

pub(crate) fn view_expr(p: &mut Parser<'_>, lhs: CompletedMarker) -> CompletedMarker {
    assert!(p.at(T![@]));
    let m = lhs.precede(p);
    p.bump(T![@]);
    m.complete(p, VIEW_EXPR)
}

pub(crate) fn is_expr(p: &mut Parser<'_>, lhs: CompletedMarker) -> CompletedMarker {
    assert!(p.at_contextual_kw(T![is]));
    let m = lhs.precede(p);
    p.bump_remap(T![is]);
    types::type_no_bounds(p);
    m.complete(p, IS_EXPR)
}

pub(crate) fn has_expr(p: &mut Parser<'_>, lhs: CompletedMarker) -> CompletedMarker {
    assert!(p.at_contextual_kw(T![has]));
    let m = lhs.precede(p);
    p.bump_remap(T![has]);
    expressions::expr(p);
    m.complete(p, HAS_EXPR)
}

pub(crate) fn matches_expr(p: &mut Parser<'_>, lhs: CompletedMarker) -> CompletedMarker {
    assert!(p.at_contextual_kw(T![matches]));
    let m = lhs.precede(p);
    p.bump_remap(T![matches]);
    patterns::pattern(p);
    m.complete(p, MATCHES_EXPR)
}

pub(crate) fn arrow_expr(p: &mut Parser<'_>, lhs: CompletedMarker) -> CompletedMarker {
    assert!(p.at(T![->]));
    let m = lhs.precede(p);
    p.bump(T![->]);
    if p.at(IDENT) {
        p.bump(IDENT);
    } else if p.at(NAME_REF) {
        p.bump(NAME_REF);
    } else {
        p.expect(INT_NUMBER);
    }
    m.complete(p, ARROW_EXPR)
}

pub(crate) fn publish(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    if p.at_contextual_kw(T![open]) {
        p.bump_remap(T![open]);
        if p.eat(T!['(']) {
            p.eat(T![in]);
            paths::use_path(p);
            p.expect(T![')']);
        }
        m.complete(p, PUBLISH)
    } else if p.at_contextual_kw(T![closed]) {
        p.bump_remap(T![closed]);
        m.complete(p, PUBLISH)
    } else if p.at_contextual_kw(T![uninterp]) {
        p.bump_remap(T![uninterp]);
        m.complete(p, PUBLISH)
    } else {
        p.error("TODO: expected open, closed, or uninterp.");
        m.complete(p, ERROR)
    }
}

pub(crate) fn proof_fn_characteristics(p: &mut Parser<'_>) -> Option<CompletedMarker> {
    if p.at(T!['[']) {
        let m = p.start();
        p.expect(T!['[']);
        while !p.at(EOF) && !p.at(T![']']) {
            paths::type_path(p);

            if p.at(T![']']) {
                break;
            }
            if p.at(T![,]) {
                p.bump(T![,]);
            }
        }
        p.expect(T![']']);
        Some(m.complete(p, PROOF_FN_CHARACTERISTICS))
    } else {
        None
    }
}

pub(crate) fn proof_fn(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![proof_fn]);
    proof_fn_characteristics(p);
    m.complete(p, PROOF_FN_WITH_CHARACTERISTICS)
}

pub(crate) fn fn_mode(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    if p.eat_contextual_kw(T![exec])
        || p.eat_contextual_kw(T![proof])
        || p.eat_contextual_kw(T![axiom])
    {
        m.complete(p, FN_MODE)
    } else if p.eat_contextual_kw(T![spec]) {
        if p.at(T!['(']) {
            p.expect(T!['(']);
            p.expect_contextual_kw(T![checked]);
            p.expect(T![')']);
        }
        m.complete(p, FN_MODE)
    } else {
        p.error("Expected spec/spec(checked)/proof/exec/axiom.");
        m.complete(p, ERROR)
    }
}

pub(crate) fn broadcast_group(p: &mut Parser<'_>, m: Marker) -> CompletedMarker {
    let group_name_m = p.start();
    p.expect(IDENT); // group name
    group_name_m.complete(p, BROADCAST_GROUP_IDENTIFIER);
    let group_list_m = p.start();
    p.expect(T!['{']);
    while !p.at(EOF) && !p.at(T!['}']) {
        attributes::inner_attrs(p);
        paths::use_path(p);

        if p.at(T!['}']) {
            break;
        }
        if p.at(T![,]) {
            p.bump(T![,]);
        }
    }
    p.expect(T!['}']);
    group_list_m.complete(p, BROADCAST_GROUP_LIST);
    m.complete(p, BROADCAST_GROUP)
}

pub(crate) fn broadcast_use_list(p: &mut Parser<'_>, m: Marker) -> CompletedMarker {
    p.expect(T![use]);
    let curly = p.eat(T!['{']); // Consume the (currently optional) curly brace
    while !p.at(EOF) && !p.at(T![;]) && !p.at(T!['}']) {
        paths::use_path(p);

        if p.at(T![;]) {
            break;
        }
        if p.at(T![,]) {
            p.bump(T![,]);
        }
    }
    if curly {
        p.expect(T!['}']); // Consume the (currently optional) curly brace
    }
    p.expect(T![;]);
    m.complete(p, BROADCAST_USE_LIST)
}

pub(crate) fn data_mode(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    if p.at_contextual_kw(T![ghost]) {
        p.bump_remap(T![ghost]);
        m.complete(p, DATA_MODE)
    } else if p.at_contextual_kw(T![tracked]) {
        p.bump_remap(T![tracked]);
        m.complete(p, DATA_MODE)
    } else {
        p.error("Err: expected ghost/tracked");
        m.complete(p, ERROR)
    }
}

pub(crate) fn assume(p: &mut Parser<'_>, m: Marker) -> CompletedMarker {
    p.expect_contextual_kw(T![assume]);
    p.expect(T!['(']);
    expressions::expr(p);
    p.expect(T![')']);
    m.complete(p, ASSUME_EXPR)
}

// FinalExpr = 'final' '(' Expr ')'
pub(crate) fn final_(p: &mut Parser<'_>, m: Marker) -> CompletedMarker {
    p.expect(T![final]);
    p.expect(T!['(']);
    expressions::expr(p);
    p.expect(T![')']);
    m.complete(p, FINAL_EXPR)
}

// AssertExpr =
//   'assert' '(' Expr ')' 'by'? ( '(' Name ')' )?  RequiresClause? BlockExpr?
pub(crate) fn assert(p: &mut Parser<'_>, m: Marker) -> CompletedMarker {
    if p.nth_at_contextual_kw(1, T![forall]) {
        return assert_forall(p, m);
    }

    p.expect_contextual_kw(T![assert]);
    if p.at(T!['(']) {
        // parse expression here
        p.expect(T!['(']);
        expressions::expr(p);
        p.expect(T![')']);
    } else {
        p.error("assert must be followed by left parenthesis or forall");
    }

    // parse optional `by`
    // bit_vector, nonlinear_artih ...
    if p.at_contextual_kw(T![by]) {
        p.expect_contextual_kw(T![by]);
        if p.at(T!['(']) {
            p.expect(T!['(']);
            // p.bump_any();
            name_r(p, ITEM_RECOVERY_SET);
            p.expect(T![')']);
        }
    }

    // parse optional 'requires`
    if p.at_contextual_kw(T![requires]) {
        requires(p);
    }

    if p.at(T![;]) || p.at(T![,]) {
        // end of assert_expr
    } else {
        // parse optional 'proof block'
        if p.at(T!['{']) {
            expressions::block_expr(p);
        }
    }

    m.complete(p, ASSERT_EXPR)
}

pub(crate) fn assert_forall(p: &mut Parser<'_>, m: Marker) -> CompletedMarker {
    p.expect_contextual_kw(T![assert]);

    if !p.at_contextual_kw(T![forall]) {
        p.error("assert forall must start with forall");
    }

    verus_closure_expr(p, None, true);
    if p.at_contextual_kw(T![implies]) {
        p.bump_remap(T![implies]);
        expressions::expr(p);
    }

    p.expect_contextual_kw(T![by]);
    expressions::block_expr(p);
    m.complete(p, ASSERT_FORALL_EXPR)
}

pub(crate) fn prover(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![by]);
    p.expect(T!['(']);
    name_r(p, ITEM_RECOVERY_SET);
    p.expect(T![')']);
    m.complete(p, PROVER)
}

pub(crate) fn requires(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![requires]);
    if !at_clause_expr_boundary(p) {
        expressions::expr_no_struct(p);
    }

    while !p.at(EOF)
        && !p.at_contextual_kw(T![recommends])
        && !p.at_contextual_kw(T![ensures])
        && !p.at_contextual_kw(T![default_ensures])
        && !p.at_contextual_kw(T![returns])
        && !p.at_contextual_kw(T![decreases])
        && !p.at_contextual_kw(T![opens_invariants])
        && !p.at_contextual_kw(T![no_unwind])
        && !p.at(T!['{'])
        && !p.at(T![;])
    {
        if p.at_contextual_kw(T![recommends])
            || p.at_contextual_kw(T![ensures])
            || p.at_contextual_kw(T![default_ensures])
            || p.at_contextual_kw(T![decreases])
            || p.at(T!['{'])
        {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at_contextual_kw(1, T![recommends])
                || p.nth_at_contextual_kw(1, T![ensures])
                || p.nth_at_contextual_kw(1, T![default_ensures])
                || p.nth_at_contextual_kw(1, T![returns])
                || p.nth_at_contextual_kw(1, T![decreases])
                || p.nth_at_contextual_kw(1, T![opens_invariants])
                || p.nth_at_contextual_kw(1, T![no_unwind])
                || p.nth_at(1, T!['{'])
                || p.nth_at(1, T![;])
            {
                break;
            } else {
                comma_expr(p);
            }
        } else {
            p.error("Expected a requires expression to be followed by a comma, a keyword, or an open brace.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, REQUIRES_CLAUSE)
}

pub(crate) fn recommends(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![recommends]);
    expressions::expr_no_struct(p);
    while !p.at(EOF)
        && !p.at(T![ensures])
        && !p.at(T![default_ensures])
        && !p.at(T![decreases])
        && !p.at(T!['{'])
        && !p.at(T![;])
    {
        if p.at_contextual_kw(T![recommends])
            || p.at_contextual_kw(T![ensures])
            || p.at_contextual_kw(T![default_ensures])
            || p.at_contextual_kw(T![decreases])
            || p.at(T!['{'])
            || p.at_contextual_kw(T![via])
        {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at_contextual_kw(1, T![recommends])
                || p.nth_at_contextual_kw(1, T![ensures])
                || p.nth_at_contextual_kw(1, T![default_ensures])
                || p.nth_at_contextual_kw(1, T![decreases])
                || p.nth_at_contextual_kw(1, T![via])
                || p.nth_at(1, T!['{'])
                || p.nth_at(1, T![;])
            {
                break;
            } else {
                comma_expr(p);
            }
        } else {
            p.error("Expected a recommends expression to be followed by a comma, a keyword, or an open brace.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    if p.at_contextual_kw(T![via]) {
        p.expect_contextual_kw(T![via]);
        expressions::expr_no_struct(p);
    }
    m.complete(p, RECOMMENDS_CLAUSE)
}

pub(crate) fn ensures(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![ensures]);
    if !at_clause_expr_boundary(p) {
        expressions::expr_no_struct(p);
    }

    while !p.at(EOF)
        && !p.at_contextual_kw(T![decreases])
        && !p.at_contextual_kw(T![default_ensures])
        && !p.at_contextual_kw(T![returns])
        && !p.at_contextual_kw(T![opens_invariants])
        && !p.at_contextual_kw(T![no_unwind])
        && !p.at(T!['{'])
        && !p.at(T![;])
    {
        if p.at_contextual_kw(T![recommends]) || p.at(T!['{']) {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at_contextual_kw(1, T![recommends])
                || p.nth_at_contextual_kw(1, T![default_ensures])
                || p.nth_at_contextual_kw(1, T![returns])
                || p.nth_at_contextual_kw(1, T![decreases])
                || p.nth_at_contextual_kw(1, T![opens_invariants])
                || p.nth_at_contextual_kw(1, T![no_unwind])
                || p.nth_at(1, T!['{'])
                || p.nth_at(1, T![;])
            {
                break;
            } else {
                comma_expr(p);
            }
        } else {
            p.error("Expected an ensures expression to be followed by a comma, a keyword, or an open brace.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, ENSURES_CLAUSE)
}

pub(crate) fn default_ensures(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![default_ensures]);
    if !at_clause_expr_boundary(p) {
        expressions::expr_no_struct(p);
    }

    while !p.at(EOF)
        && !p.at_contextual_kw(T![decreases])
        && !p.at_contextual_kw(T![returns])
        && !p.at_contextual_kw(T![opens_invariants])
        && !p.at_contextual_kw(T![no_unwind])
        && !p.at(T!['{'])
        && !p.at(T![;])
    {
        if p.at_contextual_kw(T![recommends]) || p.at(T!['{']) {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at_contextual_kw(1, T![recommends])
                || p.nth_at_contextual_kw(1, T![returns])
                || p.nth_at_contextual_kw(1, T![decreases])
                || p.nth_at_contextual_kw(1, T![opens_invariants])
                || p.nth_at_contextual_kw(1, T![no_unwind])
                || p.nth_at(1, T!['{'])
                || p.nth_at(1, T![;])
            {
                break;
            } else {
                comma_expr(p);
            }
        } else {
            p.error("Expected a default_ensures expression to be followed by a comma, a keyword, or an open brace.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, DEFAULT_ENSURES_CLAUSE)
}

pub(crate) fn returns(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![returns]);
    expressions::expr_no_struct(p);
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, RETURNS_CLAUSE)
}

pub(crate) fn opens_invariants(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![opens_invariants]);
    if p.at_contextual_kw(T![any]) {
        p.bump_remap(T![any]);
    } else if p.at_contextual_kw(T![none]) {
        p.bump_remap(T![none]);
    } else if p.at(T!['[']) {
        p.bump(T!['[']);
        // Consume the list of opened invariants
        while !p.at(EOF) && !p.at(T![']']) {
            expressions::expr_no_struct(p);
            if p.at(T![,]) {
                p.bump(T![,]);
            }
        }
        if p.at(T![']']) {
            p.bump(T![']']);
        }
    } else {
        // Try to parse a single set expression
        expressions::expr_no_struct(p);
    }

    m.complete(p, OPENS_INVARIANTS_CLAUSE)
}

pub(crate) fn invariants_except_break(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![invariant_except_break]);
    expressions::expr_no_struct(p);

    while !p.at(EOF) && !p.at_contextual_kw(T![decreases]) && !p.at(T!['{']) && !p.at(T![;]) {
        if p.at_contextual_kw(T![invariant])
            || p.at_contextual_kw(T![recommends])
            || p.at_contextual_kw(T![ensures])
            || p.at_contextual_kw(T![decreases])
            || p.at(T!['{'])
        {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at_contextual_kw(1, T![recommends])
                || p.nth_at_contextual_kw(1, T![invariant])
                || p.nth_at_contextual_kw(1, T![ensures])
                || p.nth_at_contextual_kw(1, T![decreases])
                || p.nth_at(1, T!['{'])
            {
                break;
            } else {
                comma_expr(p);
            }
        } else {
            p.error("Expected an invariants_except_break expression to be followed by a comma, a keyword, or an open brace.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, INVARIANT_EXCEPT_BREAK_CLAUSE)
}

pub(crate) fn invariants(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![invariant]);
    expressions::expr_no_struct(p);

    while !p.at(EOF) && !p.at_contextual_kw(T![decreases]) && !p.at(T!['{']) && !p.at(T![;]) {
        if p.at_contextual_kw(T![recommends])
            || p.at_contextual_kw(T![ensures])
            || p.at_contextual_kw(T![decreases])
            || p.at(T!['{'])
        {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at_contextual_kw(1, T![recommends])
                || p.nth_at_contextual_kw(1, T![ensures])
                || p.nth_at_contextual_kw(1, T![decreases])
                || p.nth_at(1, T!['{'])
            {
                break;
            } else {
                comma_expr(p);
            }
        } else {
            p.error("Expected an invariant expression to be followed by a comma, a keyword, or an open brace.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, INVARIANT_CLAUSE)
}

pub(crate) fn decreases(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![decreases]);
    expressions::expr_no_struct(p);
    while !p.at(EOF) && !p.at(T!['{']) && !p.at(T![;]) {
        if p.at_contextual_kw(T![recommends])
            || p.at_contextual_kw(T![ensures])
            || p.at_contextual_kw(T![default_ensures])
            || p.at_contextual_kw(T![decreases])
            || p.at_contextual_kw(T![via])
            || p.at_contextual_kw(T![when])
            || p.at(T!['{'])
        {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at_contextual_kw(1, T![recommends])
                || p.nth_at_contextual_kw(1, T![ensures])
                || p.nth_at_contextual_kw(1, T![default_ensures])
                || p.nth_at_contextual_kw(1, T![decreases])
                || p.nth_at_contextual_kw(1, T![via])
                || p.nth_at_contextual_kw(1, T![when])
                || p.nth_at(1, T!['{'])
            {
                break;
            } else {
                comma_expr(p);
            }
        } else {
            p.error("Expected a decreases expression to be followed by a comma, a keyword, or an open brace.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, DECREASES_CLAUSE)
}

pub(crate) fn signature_decreases(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    decreases(p);
    if p.at_contextual_kw(T![when]) {
        p.expect_contextual_kw(T![when]);
        expressions::expr_no_struct(p);
    }
    if p.at_contextual_kw(T![via]) {
        p.expect_contextual_kw(T![via]);
        expressions::expr_no_struct(p);
    }
    m.complete(p, SIGNATURE_DECREASES)
}

fn comma_expr(p: &mut Parser<'_>) -> () {
    p.expect(T![,]);
    expressions::expr_no_struct(p);
}

fn at_clause_expr_boundary(p: &Parser<'_>) -> bool {
    p.at(EOF)
        || p.at_contextual_kw(T![recommends])
        || p.at_contextual_kw(T![ensures])
        || p.at_contextual_kw(T![default_ensures])
        || p.at_contextual_kw(T![returns])
        || p.at_contextual_kw(T![decreases])
        || p.at_contextual_kw(T![opens_invariants])
        || p.at_contextual_kw(T![no_unwind])
        || p.at(T!['{'])
        || p.at(T![;])
}

pub(crate) fn trigger_attribute(p: &mut Parser<'_>, inner: bool) -> CompletedMarker {
    let m = p.start();
    p.expect_contextual_kw(T![trigger]);
    if inner {
        expressions::expr_no_struct(p);
        while !p.at(EOF) && !p.at(T![']']) {
            if !p.at(T![,]) {
                break;
            }
            p.expect(T![,]);
            expressions::expr_no_struct(p);
        }

        if p.at(T![,]) {
            p.expect(T![,]);
        }
    }

    m.complete(p, TRIGGER_ATTRIBUTE)
}

pub(crate) fn global_clause(p: &mut Parser<'_>, m: Marker) {
    //global size_of usize == 8;
    p.eat_contextual_kw(T![global]);
    if p.at_contextual_kw(T![size_of]) {
        // global size_of usize == 8;
        p.eat_contextual_kw(T![size_of]);
        type_no_bounds(p);
        p.expect(T![==]);
        p.expect(INT_NUMBER);
    } else {
        // global layout S<u64> is size == 16, align == 8;
        p.expect_contextual_kw(T![layout]);
        type_no_bounds(p);
        p.expect_contextual_kw(T![is]);
        p.expect_contextual_kw(T![size]);
        p.expect(T![==]);
        p.expect(INT_NUMBER);
        p.expect(T![,]);
        p.expect_contextual_kw(T![align]);
        p.expect(T![==]);
        p.expect(INT_NUMBER);
    }
    p.expect(T![;]);
    m.complete(p, VERUS_GLOBAL);
}
