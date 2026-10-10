# CLRS §4.3–4.4: reusable recurrence proofs

The project provides checked **discrete** substitution and recursion-tree
libraries. They use Lean 4.26 and `Std`, with natural-number input sizes and
nonnegative integer costs. No compiler extension or Mathlib dependency is needed.
These frameworks formalize the reasoning principles of §4.3–4.4; they do not
claim to cover every textbook example or exercise.

## Substitution (§4.3)

[`Substitution.lean`](../proofs/chapter4/Substitution.lean), namespace
`Chapter4Substitution`, represents subproblems by `children : Nat → List Nat`.
Their number and sizes may vary with the parent size. Repeated children count
repeatedly. Odd-size floor/ceiling splits and unequal branches are supported.

For a cutoff `b`, sizes `n < b` are base cases. Above that range, every listed
child must be strictly smaller than its parent. An upper recurrence has the form

```text
T(n) ≤ toll(n) + sum(T(m) for m in children(n)).
```

To establish `T(n) ≤ B(n)` for every natural `n`, `upper_comparison` requires:

1. `T(n) ≤ B(n)` for every base size `n < b`;
2. the upper recurrence inequality for `T`;
3. `toll(n) + sum(B(m) for m in children(n)) ≤ B(n)` above the cutoff;
4. strict decrease of child sizes.

The proof performs strong induction on size. `lower_comparison` reverses the
relevant inequalities. Exact recurrences have convenience theorems for upper
and lower bounds, simultaneous bounds, and uniqueness of solutions agreeing on
all base cases. `depth_upper` and `depth_lower` specialize the same framework to
`T(k+1) ≤ a*T(k)+g(k)` and its lower-bound counterpart.

The natural-valued `IsBigO`, `IsBigOmega`, and `IsTheta` definitions include
positive multiplicative constants and eventual thresholds. For example,
`IsBigO T G` means there are natural `C > 0` and `N` such that
`T(n) ≤ C*G(n)` for every `n ≥ N`. Comparison and transitivity lemmas retain
those thresholds. These definitions do not supply real powers or logarithms.

## Recursion trees (§4.4)

[`RecursionTree.lean`](../proofs/chapter4/RecursionTree.lean), namespace
`Chapter4RecursionTree`, models a call as a node containing its size, its own
charged work, and an ordered list of child calls. Trees may have arbitrary
finite branching and unequal leaf depths.

Checked results include:

- `Tree.total_eq_levels`: total work equals the sum of level costs through the
  tree's height. Levels after that height have zero work.
- `Tree.levelCost_frontier`: a level's work is the sum of work on its frontier.
- `Tree.upper_bound` / `Tree.lower_bound`: per-level bounds add to bounds on
  total work.
- `Tree.internal_add_leaf`: internal-node and leaf contributions partition all
  work, including trees with leaves at different depths.
- `consistent_exists`: strictly decreasing natural child sizes produce a finite
  tree for every size.
- `recurrence_tree_accounting`: a tree consistent with a numerical recurrence
  computes exactly that recurrence's cost, both as node work and as level sums.

For balanced recurrences, `balanced_unroll` proves the general identity

```text
T(k) = a^k*T(0) + sum(a^(k-1-j)*g(j), j=0,...,k-1)
```

from `T(k+1) = a*T(k)+g(k)`. The arity, base cost, and toll sequence are arbitrary
natural values, including zero. Upper and lower recurrence inequalities have
matching unrolling bounds. `balancedTree_total` connects the formula to an
actual finite tree, rather than only to an algebraically defined sequence.

## Worked applications

[`SubstitutionExamples.lean`](../proofs/chapter4/SubstitutionExamples.lean)
defines a total, well-founded recurrence on **every natural size**:

```text
T(0)=0, T(1)=1
T(n)=T(floor(n/2))+T(ceil(n/2))+n       for n≥2.
```

`balancedCost_bounds` proves `n ≤ T(n) ≤ n²`, including odd sizes and both base
cases, by applying the general comparison theorems. That deliberately simple
quadratic bound is followed by a tight analysis: monotonicity and the exact
power-of-two formula bracket every size between adjacent powers of two.

The checked all-size bounds are

```text
n*(Nat.log2(n)+1) ≤ 2*T(n)
T(n) ≤ 4*n*(Nat.log2(n)+1).
```

`balancedCost_isTheta_nlogn` proves the canonical **Θ(n·log₂ n)** statement,
with threshold `n ≥ 2`, upper constant 8 and lower comparison constant 2.
`balanced_isTheta_nlogn` extends it to any exact solution with the specified
base cases. Zero and one remain explicitly covered by the all-size bounds.

[`RecurrenceApplications.lean`](../proofs/chapter4/RecurrenceApplications.lean)
contains two further applications:

1. `balanced_linear_exact` proves that every solution of
   `T(0)=1`, `T(k+1)=2*T(k)+2^(k+1)` satisfies `T(k)=(k+1)*2^k`.
   `balanced_linear_tree` proves the same cost for its explicit recursion tree.
   With `n=2^k`, this is the usual `n*(log₂(n)+1)` formula. This is a numerical
   example, not an additional claim about merge sort's compiled source.
2. The **actual compiled Strassen program** has total charged work
   `W(0)=2`, `W(k+1)=7*W(k)+30*4^k+1`, including leaf products, recursive calls,
   copying, and linear combinations. The library proves its exact tree sum
   and proves the upper bound `13*7^k`, sharpening the bundled editor
   analysis's `33*7^k` bound.

The Strassen substitution proof demonstrates why an induction hypothesis may
need strengthening. Substituting `C*7^k` directly leaves no room for the positive
toll. Instead define `U(k)=W(k)+10*4^k+1`; then `U(0)=13` and
`U(k+1)≤7*U(k)`. Generic substitution gives

```text
7^k ≤ W(k) ≤ 13*7^k.
```

`runtime_via_substitution` and `runtime_via_tree` state these conclusions using
`strassen.ReturnsWithCost` for every completed execution.
`terminates_with_bounds` also supplies a completed execution, so the bounds are
not conditional on an unproved termination assumption. `strassen_theta`
packages the natural-depth asymptotic result. The constant 13 is not claimed
optimal, and recursive matrix dimensions remain restricted to `n=2^k`.

## Checking and reuse

From the repository root, with the pinned Lean toolchain available:

```sh
python3 scripts/check_chapter4_proofs.py
python3 -m unittest tests.test_chapter4
```

The checker compiles the real Strassen `.algo` file, its named-point interface,
and every proof module independently in dependency order. It then audits the
principal framework and application theorems for unexpected axioms. Temporary
compiled files are removed after checking. The ordinary editor bundle is also
checked separately by `tests.test_analysis`.

The general libraries and applications are maintained as separate Lean modules.
The editor loads the matrix analyses; the recurrence modules are checked through
the modular checker. Their import dependencies and applications are part of the
normal regression suite. When extending the library, update its module list
and audited public theorems in `scripts/check_chapter4_proofs.py`.

These results concern numerical recurrences. A new algorithm still needs a
proof connecting its actual counters to the recurrence or inequality, and a
termination argument. The current size-recurrence interface fixes the children
as a function of size; data-dependent branching needs an appropriate bound or
additional program-specific argument. Together with the matrix algorithms, the
current Chapter 4 scope is §4.1–4.4. The master theorem (§4.5), real-valued
asymptotics, the continuous master theorem (§4.6), and a general Akra–Bazzi
interface (§4.7) remain outside this Lean/Std library.
