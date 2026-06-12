use crate::{
    Edition, SourceFile,
    ast::{HasModuleItem, generated::vst_nodes},
};

// Verus tests
// Do "cargo test --package syntax --lib -- tests"
// Ignored tests are upstream coverage for Verus syntax that this rebase has not restored yet.

#[allow(dead_code)]
fn verus_core(source_code: &str) {
    let parse = SourceFile::parse(source_code, Edition::Edition2024);
    let errors = parse.errors();
    assert!(errors.is_empty(), "parse errors: {errors:?}");
    let file: SourceFile = parse.tree();
    //dbg!(&file);
    for item in file.items() {
        //dbg!(&item);
        let _v_item: vst_nodes::Item = item.try_into().unwrap();
        //dbg!(v_item);
    }
}

#[test]
fn verus_walkthrough0() {
    let source_code = "verus!{
        proof fn my_proof_fun(x: int, y: int)
            {
                let z = 1;
            }

        spec fn identity(x: u32) -> u32 {
            x
        }

        proof fn sq(x: nat) -> (squared: nat) {
            x
        }
        #[cfg(verus_keep_ghost)]
        #[verifier::proof]
        pub fn assert_safety(b: bool) {
            requires(b);
            ensures(b);
        }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough1() {
    let source_code = "verus!{
        proof fn my_proof_fun(x: int, y: int)
            requires
                x < 100,
                y < 100,
            ensures
                x + y < 200,
            {
                assert(x + y < 200);
            }
        fn test(a: u8) {
            assert(a & 0 == 0) by (bit_vector)
        }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough1_1() {
    let source_code = "
verus! {
    spec fn identity(x: u32) -> u32 {
        x
    }
    proof fn proof_index(a: u32, offset: u32)
    requires
        offset < 1000,
    ensures
        offset < 1000,
    {
        let mut x:u32 = 10;
        x = identity(x);
        assert(offset < 100);
    }
}
";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough2() {
    let source_code = "verus!{
        proof fn my_proof_fun(x: int, y: int) -> (sum: int)
            requires
                x < 100,
                y < 100,
            ensures
                sum < 200,
        {
            x + y
        }
        spec fn my_spec_fun(x: int, y: int) -> int
            recommends
                x < 100,
                y < 100,
        {
            x + y
        }
        pub(crate) open spec fn my_pub_spec_fun3(x: int, y: int) -> int {
            // function and body visible to crate
            x / 2 + y / 2
        }
        pub closed spec fn my_pub_spec_fun4(x: int, y: int) -> int {
            // function visible to all, body visible to module
            x / 2 + y / 2
        }
        pub(crate) closed spec fn my_pub_spec_fun5(x: int, y: int) -> int {
            // function visible to crate, body visible to module
            x / 2 + y / 2
        }
        pub open (crate) spec fn test1() {}
        pub open (in foo) spec fn test2() {}
        pub open (in crate::m) spec fn test3() { }
        pub open (super) spec fn test4() {}
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough3() {
    let source_code = "verus!{
        proof fn test5_bound_checking(x: u32, y: u32, z: u32)
            requires
                x <= 0xffff,
                y <= 0xffff,
                z <= 0xffff,
        {
            assert(x * z == mul(x, z)) by(nonlinear_arith)
                requires
                    x <= 0xffff,
                    z <= 0xffff,
            {
                assert(0 <= x * z);
                assert(x * z <= 0xffff * 0xffff);
            }
            assert(0 <= y < 100 ==> my_spec_fun(x, y) >= x);
            assert(forall|x: int, y: int| 0 <= x < 100 && 0 <= y < 100 ==> my_spec_fun(x, y) >= x);
        }
        fn test_quantifier() {
            assert(forall|x: int, y: int| 0 <= x < 100 && 0 <= y < 100 ==> my_spec_fun(x, y) >= x);
            assert(my_spec_fun(10, 20) == 30);
            assert(exists|x: int, y: int| my_spec_fun(x, y) == 30);
        }
        fn test() {
            if exists|i: int| 0 <= i {
                let x = 1;
            }
            if exists|i: int| 0 <= start <= i < stop <= s.len() && s[i] == x {
                let index = choose|i: int| 0 <= start <= i < stop <= s.len() && s[i] == x;
                assert(s.subrange(start, stop)[index - start] == s[index]);
            }
        }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough4() {
    let source_code = "verus!{
        fn test_assert_forall_by() {
            assert forall|x: int, y: int| f1(x) + f1(y) == x + y + 2 by {
                reveal(f1);
            }
            assert(f1(1) + f1(2) == 5);
            assert(f1(3) + f1(4) == 9);
            // to prove forall|...| P ==> Q, write assert forall|...| P implies Q by {...}
            assert forall|x: int| x < 10 implies f1(x) < 11 by {
                assert(x < 10);
                reveal(f1);
                assert(f1(x) < 11);
            }
            assert(f1(3) < 11);
        }
        fn test_choose() {
            assume(exists|x: int| f1(x) == 10);
            proof {
                let x_witness = choose|x: int| f1(x) == 10;
                assert(f1(x_witness) == 10);
            }

            assume(exists|x: int, y: int| f1(x) + f1(y) == 30);
            proof {
                let (x_witness, y_witness): (int, int) = choose|x: int, y: int| f1(x) + f1(y) == 30;
                assert(f1(x_witness) + f1(y_witness) == 30);
            }
        }
        fn test(s: Set<int>) {
            let x = s.choose();
            choose|x: int| f1(x)
        }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough5() {
    let source_code =
    "verus!{
        fn test_single_trigger1() {
            assume(forall|x: int, y: int| f1(x) < 100 && f1(y) < 100 ==> #[trigger] my_spec_fun(x, y) >= x);
        }

        fn foo(x:int) -> int {
            if x>0 {1} else {-1}
        }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough6() {
    let source_code = "verus!{
        proof fn my_proof_fun(x: int, y: int) -> (sum: int)
            requires
                x < 100,
                y < 100,
            ensures
                sum < 200,
        {
            x + y
        }
        spec fn sum2(i: int, j: int) -> int
            recommends
                0 <= i < 10,
                0 <= j < 10,
        {
            i + j
        }

        spec fn spec_index()
            recommends
                0 <= i,
        ;
        fn closed_under_incl()
            requires
                Self::op(a, b).valid(),
            ensures
                a.valid(),
        ;
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough7() {
    let source_code =
    "verus!{
        fn test_single_trigger2() {
            // Use [f1(x), f1(y)] as the trigger
            assume(forall|x: int, y: int| #[trigger] f1(x) < 100 && #[trigger] f1(y) < 100 ==> my_spec_fun(x, y) >= x);
        }
        /// To manually specify multiple triggers, use #![trigger]:
        fn test_multiple_triggers() {
            // Use both [my_spec_fun(x, y)] and [f1(x), f1(y)] as triggers
            assume(forall|x: int, y: int|
                #![trigger my_spec_fun(x, y)]
                #![trigger f1(x), f1(y)]
                f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x
            );
        }

        #[verus::line_count::ignore]
        pub const A: u64 = 0;

        fn test() {
            assert(p % p == 0) by (nonlinear_arith)
                requires
                p != 0,
            ;
        }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough8() {
    let source_code = "verus!{
    fn test_my_funs2(
        a: u32, // exec variable
        b: u32, // exec variable
    )
        requires
            a < 100,
            b < 100,
    {
        let s = a + b; // s is an exec variable
        proof {
            let u = a + b; // u is a ghost variable
            my_proof_fun(u / 2, b as int); // my_proof_fun(x, y) takes ghost parameters x and y
        }
    }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough9_0() {
    let source_code = "verus!{
    fn test_is_variant_1(v: Vehicle2<u64>) {
        match v {
            Vehicle2::Car(_) => assert(v.is_Car()),
            Vehicle2::Train(_) => assert(v.is_Train()),
        };
    }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough9() {
    let source_code = "verus!{
    proof fn test_tracked(
        tracked w: int,
        tracked x: int,
        tracked y: int,
        z: int,
      ) -> tracked TrackedAndGhost<(int, int), int> {

    }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough10_0() {
    let source_code = "verus!{
    pub(crate) proof fn binary_ops<A>(a: A, x: int) {
        assert(2 + 2 !== 3);
        assert(a === a);

        assert(false <==> true && false);
    }

    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough10_1() {
    let source_code = "verus!{
    spec fn ccc(x: int, y: int) -> bool {
        &&& if false {
                true
            } else {
                &&& b ==> b
                &&& !b
            }
        &&& true
    }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough10_2() {
    let source_code = "verus!{
    spec fn complex_conjuncts(x: int, y: int) -> bool {
        let b = x < y;
        &&& b
        &&& if false {
                &&& b ==> b
                &&& !b ==> !b
            } else {
                ||| b ==> b
                ||| !b
            }
        &&& false ==> true
    }

    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough10() {
    let source_code = "verus!{
    fn test_views() {
        let mut v: Vec<u8> = Vec::new();
        v.push(10);
        v.push(20);
        proof {
            let s: Seq<u8> = v@; // v@ is equivalent to v.view()
            assert(s[0] == 10);
            assert(s[1] == 20);
        }
    }
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough11() {
    let source_code = "verus!{
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
        exists|i:int| 0 <= i < v.len() && k == v[i],
    ensures
        r < v.len(),
        k == v[r as int],
{
    let mut i1: usize = 0;
    let mut i2: usize = v.len() - 1;
    while i1 != i2
        invariant
            i2 < v.len(),
            exists|i:int| i1 <= i <= i2 && k == v[i],
            forall|i:int, j:int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
    {
        //let d: Ghost<int> = ghost(i2 - i1);
        let ix = i1 + (i2 - i1) / 2;
        if *v.index(ix) < k {
            i1 = ix + 1;
        } else {
            i2 = ix;
        }
        assert(i2 - i1 < d@);
    }
    i1
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough12() {
    let source_code = "verus!{
fn pop_test(t: Vec<u64>)
requires
    t.len() > 0,
    forall|i: int| #![auto] 0 <= i < t.len() ==> uninterp_fn(t[i]),
{
let mut t = t;
let x = t.pop();
assert(uninterp_fn(x));
assert(forall|i: int| #![auto] 0 <= i < t.len() ==> uninterp_fn(t[i]));
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough13() {
    let source_code = "verus!{
    proof fn arith_sum_int_nonneg(i: nat)
        ensures
            arith_sum_int(i as int) >= 0,
        decreases
            i,
    {
        if i > 0 {
            arith_sum_int_nonneg((i - 1) as nat);
        }
    }

    spec fn arith_sum_int(i: int) -> int
    decreases i
{
    if i <= 0 { 0 } else { i + arith_sum_int(i - 1) }
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough14() {
    let source_code = "verus!{
fn exec_with_decreases(n: u64) -> u64
    decreases 100 - n,
{
    if n < 100 {
        exec_with_decreases(n + 1)
    } else {
        n
    }
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough15() {
    let source_code =
    "verus!{
spec(checked) fn my_spec_fun2(x: int, y: int) -> int
    recommends
        x < 100,
        y < 100,
{
    // Because of spec(checked), Verus checks that my_spec_fun's recommends clauses are satisfied here:
    my_spec_fun(x, y)
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough16() {
    let source_code = "verus!{
proof fn test_even_f()
    ensures
        forall|i: int| is_even(i) ==> f(i),
{
    assert forall|i: int| is_even(i) implies f(i) by {
        // First, i is in scope here
        // Second, we assume is_even(i) here
        lemma_even_f(i);
        // Finally, we have to prove f(i) here
    }
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough17() {
    //from: https://github.com/verus-lang/verus/wiki/Doc%3A-Deprecated-and-recommended-syntax%2C-and-upcoming-changes
    let source_code = "verus!{
proof fn lemma1(i: int, tracked t: S) {
}
fn f(i: u32, Ghost(j): Ghost<int>, Tracked(t): Tracked<S>) -> (k: u32)
    // Note: Ghost(j) unwraps the Ghost<int> value so that j has type int
    // Note: Tracked(t) unwraps the Tracked<S> value so that t has type S
    requires
        i != j,
        i < 10,
    ensures
        k == i + 1,
{
    let ghost i_plus_j = i + j;
    let ghost t_ghost_copy = t;
    let tracked t_moved = t;
    proof {
        lemma1(i as int, t_moved);
    }
    assert(t_moved == t_ghost_copy);
    assert(i_plus_j == i + j);
    i + 1
}
fn g(Tracked(t): Tracked<S>) -> u32 {
    f(5, Ghost(6), Tracked(t))
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough18() {
    //from: https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/syntax.rs
    let source_code = "
verus!{
spec fn add0(a: nat, b: nat) -> nat
    recommends a > 0,
    via add0_recommends
{
    a + b
}

spec fn dec0(a: int) -> int
    decreases a
    when a > 0
    via dec0_decreases
{
    if a > 0 {
        dec0(a - 1)
    } else {
        0
    }
}

#[via_fn]
proof fn add0_recommends(a: nat, b: nat) {
    // proof
}

#[via_fn]
proof fn dec0_decreases(a: int) {
    // proof
}
} // verus!";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough19() {
    //from: https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/syntax.rs
    let source_code = "
verus!{
tracked struct TrackedAndGhost<T, G>(
    tracked T,
    ghost G,
);
} // verus!";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough20() {
    //from: https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/syntax.rs
    let source_code = "
verus!{
proof fn lemma_mul_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
    by (nonlinear_arith)
    requires x <= x_bound, y <= y_bound, 0 <= x, 0 <= y,
    ensures x * y <= x_bound * y_bound,
{
}
} // verus!";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough21() {
    //from: https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/syntax.rs
    let source_code = "
verus!{
    spec fn add0(a: nat, b: nat) -> nat
    recommends a > 0,
    via add0_recommends
{
    a + b
}

#[via_fn]
proof fn add0_recommends(a: nat, b: nat) {
    // proof
}

} // verus!";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough22() {
    //from: https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/syntax.rs
    let source_code = "
verus!{
    spec fn add0(a: nat, b: nat) -> nat
    recommends a > 0,
    via add0_recommends
{
    a + b
}

spec fn dec0(a: int) -> int
    decreases a,
    when a > 0
    via dec0_decreases
{
    if a > 0 {
        dec0(a - 1)
    } else {
        0
    }
}

#[via_fn]
proof fn add0_recommends(a: nat, b: nat) {
    // proof
}

#[via_fn]
proof fn dec0_decreases(a: int) {
    // proof
}
} // verus!";
    verus_core(source_code);
}

// verus trigger attribute is custom syntax
// Need to extend Rust attribute
// or make a syntax kind for it (e.g. TriggerAttribute)
// Reference https://github.com/verus-lang/verus/blob/4ef61030aadc4fd66b62f3614f36e3b64e89b855/source/builtin_macros/src/syntax.rs#L1808
// Note that verus! macro compares the attributes name with "trigger", and process it
// However, the rust-analyzer parser does not have access to string's content.
// Therefore, to make a new syntax kind (e.g. TriggerAttribute),
// we need to register `trigger` as a reserved keyword.
// however, by registering `trigger` as a reserved keyword,
// single trigger attribute, which is `#[trigger]` becomes invalid syntax.
// therefore, we just special-case `#[trigger]`
#[test]
fn verus_walkthrough23() {
    //from: https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/syntax.rs
    let source_code = "
verus!{
    fn test_multiple_triggers() {
        assume(forall|x: int, y: int|
            #![trigger my_spec_fun(x, y)]
            #![trigger f1(x), f1(y)]
            f1(x) < 100 && f1(y) < 100 ==> my_spec_fun(x, y) >= x
        );
    }
} // verus!";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough24() {
    //from: https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/syntax.rs
    let source_code = "
verus!{
spec fn test_rec2(x: int, y: int) -> int
    decreases x, y
{
    if y > 0 {
        1 + test_rec2(x, y - 1)
    } else if x > 0 {
        2 + test_rec2(x - 1, 100)
    } else {
        3
    }
}
} // verus!";
    verus_core(source_code);
}

#[test]
fn verus_walkthrough25() {
    // https://github.com/verus-lang/verus/blob/ed95a417a236707fbb50efd96c91cb217ed2b22a/source/rust_verify/example/vectors.rs
    let source_code = "
verus!{
    fn pusher() -> Vec<u64> {
        let mut v = Vec::new();
        v.push(0);
        v.push(1);
        v.push(2);
        v.push(3);
        v.push(4);
        let ghost goal = Seq::new(5, |i: int| i as u64);
        assert(v@ =~= goal);
        assert(v[2] == 2);

        v.pop();
        v.push(4);
        assert(v@ =~= goal);

        v
    }
} // verus!";
    verus_core(source_code);
}

#[test]
fn verus_anonymous_return_types() {
    let source_code = "verus!{
fn foo() -> (u32, u32)
{
    (1, 2)
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_struct_syntax() {
    let source_code = "verus!{
proof fn sufficiently_creamy() -> bool
    requires
        bev is Coffee,
        bev !is Tea,
{
   bev->creamers
}

spec fn is_insect(l: Life) -> bool {
    l !is Primate && l is Arthropod && l->Arthropod_legs == 6
}

spec fn rect_height(s: Shape) -> int
    recommends s is Rect && s !is Circle
{
    s->1
}

spec fn cuddly(l: Life) -> bool
{
    ||| l matches Mammal{legs, ..} && legs == 4
    ||| l matches Arthropod{legs, wings} && legs == 8 && wings == 0
}

spec fn is_kangaroo(l: Life) -> bool
{
    &&& l matches Life::Mammal{legs, has_pocket}
    &&& legs == 2
    &&& has_pocket
}

spec fn walks_upright(l: Life) -> bool
{
    l matches Life::Mammal{legs, ..} ==> legs==2
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_has() {
    let source_code = "verus!{
fn uses_spec_has()
    requires
        s has 3,
        ms has 4,
        s !has 5,
        ms !has 6,
{
    assert(s has 3);
    assert(s has 3 == true);
    assert(s has 3 == s has 3);
    assert(ms has 4);
    assert(ms has 4 == ms has 4);
    assert(s !has 3);
    assert(s !has 3 == true);
    assert(s !has 3 == s !has 3);
    assert(ms !has 4);
    assert(ms !has 4 == ms !has 4);
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_while_loops() {
    let source_code = "verus!{
pub fn clone_vec_u8() {
    let i = 0;
    while i < v.len()
        invariant_except_break
            i <= v.len(),
        invariant
            i <= v.len(),
            i == out.len(),
            forall |j| #![auto] 0 <= j < i  ==> out@[j] == v@[j],
        ensures
            i > 0,
        decreases
            72,
    {
        i = i + 1;
    }
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_loops() {
    let source_code = "verus!{
fn test() {
    loop
        invariant
            x > 0,
    {
        x += 1;
    }
}

fn test() {
    loop
        invariant
            false,
        ensures
            next_idx + count <= 512,
    {
        x
    }
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_for_loops() {
    let source_code = "verus!{
fn reverse(v: &mut Vec<u64>)
    ensures
        v.len() == old(v).len(),
        forall|i: int| 0 <= i < old(v).len() ==> v[i] == old(v)[old(v).len() - i - 1],
{
    let length = v.len();
    let ghost v1 = v@;
    for n in 0..(length / 2)
        invariant
            length == v.len(),
            forall|i: int| 0 <= i < n ==> v[i] == v1[length - i - 1],
            forall|i: int| 0 <= i < n ==> v1[i] == v[length - i - 1],
            forall|i: int| n <= i && i + n < length ==> #[trigger] v[i] == v1[i],
    {
        let x = v[n];
        let y = v[length - 1 - n];
        v.set(n, y);
        v.set(length - 1 - n, x);
    }
}

fn test() {
    for x in iter: 0..end
        invariant
            end == 10,
    {
        n += 3;
    }
    let x = 2;
    for x in iter: vec_iter_copy(v)
        invariant
            b <==> (forall|i: int| 0 <= i < iter.cur ==> v[i] > 0),
    {
        b = b && x > 0;
    }
    let y = 3;
    for x in iter: 0..({
        let z = end;
        non_spec();
        z
    })
        invariant
            n == iter.cur * 3,
            end == 10,
    {
        n += 3;
        end = end + 0;  // causes end to be non-constant
    }
}
    }";
    verus_core(source_code);
}

#[test]
fn verus_broadcast() {
    let source_code = "verus!{
mod ring {
    use builtin::*;

    pub struct Ring {
        pub i: u64,
    }

    impl Ring {
        pub closed spec fn inv(&self) -> bool {
            self.i < 10
        }

        pub closed spec fn spec_succ(&self) -> Ring {
            Ring { i: if self.i == 9 { 0 } else { (self.i + 1) as u64 } }
        }

        pub closed spec fn spec_prev(&self) -> Ring {
            Ring { i: if self.i == 0 { 9 } else { (self.i - 1) as u64 } }
        }

        pub broadcast proof fn spec_succ_ensures(p: Ring)
            requires p.inv()
            ensures p.inv() && (#[trigger] p.spec_succ()).spec_prev() == p
        { }

        pub broadcast proof fn spec_prev_ensures(p: Ring)
            requires p.inv()
            ensures p.inv() && (#[trigger] p.spec_prev()).spec_succ() == p
        { }

        pub    broadcast    group    properties {
        Ring::spec_succ_ensures,
                Ring::spec_prev_ensures,
        }
    }

    #[verifier::prune_unless_this_module_is_used]
    pub    broadcast    group    properties {
    Ring::spec_succ_ensures,
            Ring::spec_prev_ensures,
    }
}

mod m2 {
    use builtin::*;
    use crate::ring::*;

    fn t2(p: Ring) requires p.inv() {
           broadcast    use     Ring::properties;
        assert(p.spec_succ().spec_prev() == p);
        assert(p.spec_prev().spec_succ() == p);
    }
}

mod m3 {
    use builtin::*;
    use crate::ring::*;

        broadcast   use    Ring::properties;

        fn a() { }
}

mod m4 {
    use builtin::*;
    use crate::ring::*;

        broadcast   use
                    Ring::spec_succ_ensures,
            Ring::spec_prev_ensures;
}

mod m5 {
broadcast use
    super::raw_ptr::group_raw_ptr_axioms,
    super::set_lib::group_set_lib_axioms,
    super::set::group_set_axioms,
;
broadcast use
    super::raw_ptr::group_raw_ptr_axioms,
    super::set_lib::group_set_lib_axioms,
    super::set::group_set_axioms;
broadcast use super::raw_ptr::group_raw_ptr_axioms;
broadcast use super::set_lib::group_set_lib_axioms;
broadcast use super::set::group_set_axioms;
broadcast use {
    super::raw_ptr::group_raw_ptr_axioms,
    super::set_lib::group_set_lib_axioms,
    super::set::group_set_axioms};
broadcast use {
    super::raw_ptr::group_raw_ptr_axioms,
    super::set_lib::group_set_lib_axioms,
    super::set::group_set_axioms,};
broadcast use {super::set::group_set_axioms};
broadcast use {super::set::group_set_axioms,};

}

}";

    verus_core(source_code);
}

#[test]
fn verus_broadcast_regression() {
    let source_code = "verus!{
fn f() { let group = Group::new(Delimiter::Bracket, bracketed.build()); let mut group = crate::Group::_new_fallback(group); group.set_span(span); trees.push_token_from_parser(TokenTree::Group(group)); }
}";
    verus_core(source_code);
}

#[test]
fn verus_where_clauses() {
    let source_code = "verus!{
pub fn spawn<F, Ret>(f: F) -> (handle: JoinHandle<Ret>) where
    F: FnOnce() -> Ret,
    requires
        f.requires(()),
    ensures
        forall|ret: Ret| #[trigger] handle.predicate(ret) ==> f.ensures((), ret),
{
}
pub fn write(in_v: V) where V: Copy
    requires
        old(perm).pptr() == self,
    ensures
        perm.pptr() === old(perm).pptr(),
        perm.mem_contents() === MemContents::Init(in_v),
    opens_invariants none
    no_unwind
{
}
}";

    verus_core(source_code);
}

#[test]
fn verus_default_ensures() {
    let source_code = "verus!{
trait T1 {
    proof fn my_function_decl(&self, i: int, j: int) -> (r: int)
        requires
            0 <= i < 10,
            0 <= j < 10,
        ensures
            i <= r,
            j <= r,
    ;

    /// A trait function may have a default (provided) implementation,
    /// and this defaults may have additional ensures specified with default_ensures
    fn my_function_with_a_default(&self, i: u32, j: u32) -> (r: u32)
        requires
            0 <= i < 10,
            0 <= j < 10,
        ensures
            i <= r,
            j <= r,
        default_ensures
            i == r || j == r,
        {
            if i >= j { i } else { j }
        }
}

trait T2 {
    fn f(i: u32) -> (r: u32)
        requires
            (builtin::default_ensures)(true),
        default_ensures
            r <= i,
    {
        i / 2
    }
}

trait T3 {
    fn f(i: u32) -> (r: u32)
        default_ensures
            r <= i,
    {
        i / 2
    }
}
}";
    verus_core(source_code);
}

#[test]
fn verus_opens_invariants() {
    let source_code = "verus!{
fn inv1()
    opens_invariants none
{
}

fn inv2()
    opens_invariants any
{
}

fn inv3()
    opens_invariants [a, b, c]
{
}

fn inv4()
    ensures true,
    opens_invariants any
{
}

fn inv5()
    requires true,
    opens_invariants any
{
}

fn put()
    requires
        self.id() === old(perm)@.pptr,
        old(perm)@.value === None,
    ensures
        perm@.pptr === old(perm)@.pptr,
        perm@.value === Some(v),
    opens_invariants none
    no_unwind
{
}

fn kw_test() {
    let any = 5;
}

proof fn foo1() opens_invariants bar();
proof fn foo2() opens_invariants baz;
proof fn foo3() opens_invariants bar() {}
proof fn foo4() opens_invariants baz {}
proof fn foo5() opens_invariants Set::<int>::empty() {}
proof fn foo6() opens_invariants { let a = Set::<int>::empty(); let b = a.insert(c); b } {}

}";
    verus_core(source_code);
}

#[test]
fn verus_no_wind() {
    let source_code = "verus!{
fn put1()
    requires
        self.id() === old(perm)@.pptr,
    ensures
        perm@.pptr === old(perm)@.pptr,
    no_unwind when true
{
}

fn put2()
    requires
        self.id() === old(perm)@.pptr,
    ensures
        perm@.pptr === old(perm)@.pptr,
    opens_invariants none
    no_unwind when true
{
}

fn put3()
    requires
        self.id() === old(perm)@.pptr,
    no_unwind when true
{
}

fn put4()
    no_unwind when true
{
}

fn put5()
    no_unwind when x + y > z
{
}
}";
    verus_core(source_code);
}

#[test]
fn verus_tracked() {
    let source_code = "verus!{
fn is_nonnull(tracked &self)
{
}

fn into_raw() -> (tracked points_to_raw: PointsToRaw)
{
}
}";
    verus_core(source_code);
}

#[test]
fn verus_higher_order_functions() {
    let source_code = "verus!{
pub fn spawn(f: F)
    requires
        f.requires(true),
    ensures
        f.ensures(ret),
{
}
}";

    verus_core(source_code);
}

#[test]
fn verus_triggers() {
    let source_code = "verus!{
fn lemma()
    ensures
        #[trigger]
        true,
{
}

fn lemma_mul_by_zero_is_zero()
    ensures
        #![trigger x]
        true,
{
    assert forall|x: int| #![trigger x * 0] #![trigger 0 * x] x * 0 == 0 && 0 * x == 0 by {
        lemma_mul_basics(x);
    }
}
}";

    verus_core(source_code);
}

#[test]
fn verus_triple_ops() {
    let source_code = "verus!{
spec fn test(a: bool, b:bool) -> bool {
    ||| {
        a
    }
    ||| b
}
proof fn tester(a: bool, b:bool)
    requires
        ({
            let x = a;
            ||| a == true
        }),
{
}
proof fn testp(a: bool, b:bool)
    requires
        ({
            ||| { a }
            ||| b
        }),
    ensures true,
{
}
}";

    verus_core(source_code);
}

#[test]
fn verus_assume_specification() {
    let source_code = "verus!{
pub assume_specification<T> [core::mem::swap::<T>] (a: &mut T, b: &mut T)
    ensures
        *a == *old(b),
        *b == *old(a),
    opens_invariants none
    no_unwind;

pub assume_specification<T>[Vec::<T>::new]() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty();

pub assume_specification<T, A: Allocator>[Vec::<T, A>::clear](vec: &mut Vec<T, A>)
    ensures
        vec@ == Seq::<T>::empty();

pub assume_specification [<bool as Clone>::clone](b: &bool) -> (res: bool)
    ensures res == b;

assume_specification[char::REPLACEMENT_CHARACTER] -> (c: char)
    ensures
        c != '7',
;
assume_specification[C] -> u8
    returns
        7u8,
;
}";

    verus_core(source_code);
}

#[test]
fn verus_returns() {
    let source_code = "verus!{
fn test() -> u8
    returns 20u8,
{
    20u8
}

proof fn proof_test() -> u8
    returns 20u8,
{
    20u8
}


fn test2() {
    let j = test();
    assert(j == 20);
}

fn test3() -> u8
    returns 20u8,
{
    19u8
}

fn test4() -> u8
    returns 20u8,
{
    return 19u8;
}

fn test5(a: u8, b: u8) -> (k: u8)
    requires a + b < 256,
    ensures a + b < 257,
    returns (a + b) as u8,
{
    return a;
}

fn test6(a: u8, b: u8) -> (k: u8)
    requires a + b < 256,
    ensures a + b < 250,
    returns (a + b) as u8,
{
    return a + b;
}

proof fn proof_test5(a: u8, b: u8) -> (k: u8)
    requires a + b < 256,
    ensures a + b < 257,
    returns (a + b) as u8,
{
    return a;
}

proof fn proof_test6(a: u8, b: u8) -> (k: u8)
    requires a + b < 256,
    ensures a + b < 250,
    returns (a + b) as u8,
{
    return (a + b) as u8;
}

pub assume_specification<T, I>[ <[T]>::get::<I> ](slice: &[T], i: I) -> (b: bool)
    where I: core::slice::SliceIndex<[T]>,
    returns
        spec_slice_get(slice, i),
;

pub assume_specification<T, I>[ <[T]>::get::<I> ](slice: &[T], i: I) -> (b: Option<
    &<I as core::slice::SliceIndex<[T]>>::Output,
>) where I: core::slice::SliceIndex<[T]>
    returns
        spec_slice_get(slice, i),
;

}";

    verus_core(source_code);
}

#[test]
fn verus_final_expr() {
    let source_code = "verus!{

pub fn vec_index_mut<T, A: Allocator>(vec: &mut Vec<T, A>, i: usize) -> (element: &mut T)
    requires i < vec.view().len(),
    ensures
        *element == old(vec)@.index(i as int),
        final(vec)@ == old(vec)@.update(i as int, *final(element)),
        *final(element) == final(vec).view().index(i as int),
    no_unwind
;

}";

    verus_core(source_code);
}

#[test]
fn verus_final_expr_simple() {
    let source_code = "verus!{

fn test(x: &mut u64)
    ensures *x == 5, *final(x) == 10,
{
    *x = 10;
}

}";

    verus_core(source_code);
}

#[test]
fn verus_globals() {
    let source_code = "verus!{
global size_of usize == 4;

global size_of S == 8;

global size_of S<u64> == 8;

global size_of S<U> == 8;

global layout S is size == 8, align == 8;

global layout S<u64> is size == 16, align == 8;

global layout S<u32> is size == 8, align == 4;
}";

    verus_core(source_code);
}

#[test]
fn verus_normal_rust() {
    let source_code = "
fn check(attrs: Vec<u64>) {
    assert!(1 > 0);
    for attr in attrs {
        ()
    }
}
";

    verus_core(source_code);
}

#[test]
fn verus_axioms() {
    let source_code = "verus!{
pub axiom fn foo(x: u8) requires x == 5;
}";

    verus_core(source_code);
}

#[test]
fn verus_proof_fn() {
    let source_code = "verus!{
    proof fn testfn() {
        let tracked f = proof_fn |y: u64| -> (z: u64)
            requires
                y == 2,
            ensures
                z == 2,
            { y };
        assert(f.requires((2,)));
        assert(!f.ensures((2,), 3));
        let t = f(2);
        assert(t == 2);
    }
    proof fn helper(tracked f: proof_fn(y: u64) -> u64)
        requires
            f.requires((2,)),
            forall|z: u64| f.ensures((2,), z) ==> z == 2,
    {
        let t = f(2);
        assert(t == 2);
    }
    proof fn testfn() {
        let tracked f = proof_fn |y: u64| -> (z: u64)
            requires
                y == 2,
            ensures
                z == 2,
            { y };
        helper(f);
    }
    proof fn test() {
        let tracked f = proof_fn[Mut, Copy, Send, ReqEns<foo>, Sync] |y: u64| -> (z: u64) { y };
    }
    proof fn foo(x: proof_fn(a: u32) -> u64, y: proof_fn[Send](a: u32) -> u64) {
    }
}";

    verus_core(source_code);
}

#[test]
fn verus_uninterp() {
    let source_code = "verus!{
pub uninterp spec fn bar() -> bool;
}";

    verus_core(source_code);
}

#[test]
fn verus_constants() {
    let source_code = "verus!{
pub exec const BDF_DEVICE_MASK: u16
    ensures BDF_DEVICE_MASK == 31
{
    31
}

const fn e() -> (u: u64) ensures u == 1 { 1 }
exec const E: u64 ensures E == 2 { 1 + e() }

exec const F: u64 ensures true { 1 }

spec const SPEC_E: u64 = 7;
#[verifier::when_used_as_spec(SPEC_E)]
exec const E: u64 ensures E == SPEC_E { 7 }


exec static E: u64 ensures false {
    proof { let x = F; }
    0
}
exec static F: u64 ensures false {
    proof { let x = E; }
    0
}

}";

    verus_core(source_code);
}

#[test]
fn verus_fn_signatures() {
    let source_code = "verus!{
trait T { }

spec fn v<K>()
        where
            K: T,
        recommends
            true,
{
    ()
}
}";

    verus_core(source_code);
}

#[test]
fn verus_empty_signature_clauses() {
    let source_code = "verus!{
proof fn empty_clauses()
    requires
    ensures
{
    assert(true) by {
    }
}

trait T {
    fn f()
        requires
        ensures
        default_ensures
    {
    }
}
}";

    verus_core(source_code);
}

#[test]
fn cst_to_vst1() {
    let source_code = "
verus!{
spec fn sum(x: int, y: int) -> int
{
    x + y
}
} // verus!";
    verus_core(source_code);
}

#[test]
fn cst_to_vst2() {
    let source_code = "
verus!{
spec fn test_rec2(x: int, y: int) -> int
    decreases x, y
{
    if y > 0 {
        1 + test_rec2(x, y - 1)
    } else {
        3
    }
}
} // verus!";
    verus_core(source_code);
}

#[test]
fn verus_real_literals() {
    let source_code = "verus!{
fn test_real_literals() {
    // Integer-style with real suffix
    assert(0real <= 1real);
    assert(0xFFreal >= 0real);
    assert(0b1010real == 10real);
    assert(0o77real == 63real);
    // Decimal-style with real suffix
    assert(0.5real < 1.0real);
    assert(0.0real <= 1.5real);
    // Exponential-style with real suffix
    assert(1e2real == 100real);
    assert(2e-1real == 0.2real);
}
}";
    verus_core(source_code);
}
