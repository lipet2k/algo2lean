# CLRS fourth edition: Chapter 4, §4.1–4.4

These examples formalize the main matrix-multiplication algorithms from
§4.1 and §4.2 using the existing Algo2Lean language and generated execution
relations. The [recurrence framework](RECURRENCES.md) adds general discrete
substitution and recursion-tree reasoning for §4.3–4.4. These proofs use Lean/Std
alone and require no compiler changes. The master theorem is outside the current
scope.

| Algorithm | Source | Lean analysis | Size | Charged work |
| --- | --- | --- | --- | --- |
| Ordinary multiplication | [matrix_multiply.algo](../examples/matrix_multiply.algo) | [matrix_multiply.lean](../examples/analysis/matrix_multiply.lean) | Any natural `n`, including zero | Exactly `n³` scalar multiply-adds |
| Eight-way recursive multiplication | [matrix_recursive.algo](../examples/matrix_recursive.algo) | [matrix_recursive.lean](../examples/analysis/matrix_recursive.lean) | `n = 2^k`, `k ≥ 0` | Exactly `8^k = n³` multiplications; cubic call overhead |
| Seven-way Strassen multiplication | [matrix_strassen.algo](../examples/matrix_strassen.algo) | [matrix_strassen.lean](../examples/analysis/matrix_strassen.lean) | `n = 2^k`, `k ≥ 0` | Exactly `7^k` leaf products; total charged work between `7^k` and `13·7^k` |

The Lean theorems quantify over arbitrary integer entries and all permitted
sizes. Each establishes a terminating execution of the compiled source,
characterizes every completed output and its counters, and relates every
matrix entry to the ordinary finite row-column dot product. Pure recurrence
identities and the Strassen algebraic identity are intermediate lemmas;
the final results use the actual programs' scoped `ReturnsWithCost` relations,
including `strassen.ReturnsWithCost`.

## Representation and assumptions

A matrix has type `Seq[Seq[Int]]`: an outer array contains references to its
integer row arrays, and entry `(i,j)` is `a[i][j]`. The finite matrix occupies
`0 ≤ i < n` and `0 ≤ j < n`. Input values outside that square are unrestricted.
Results have fresh outer arrays and separately allocated finite rows; values
outside the result square are zero. The programs preserve their inputs,
including matrices that alias each other and rows shared within or between
inputs. Integers are unbounded mathematical integers.

The iterative example uses row, column, and dot-product loops. It supports the
empty matrix. The classic recursive example uses row and column offsets into
its original inputs and accumulates eight subproducts into a fresh zero matrix.
Strassen copies quadrants into arrays of rows, combines intermediate matrices,
recursively computes seven products, and joins four result blocks.

Rows are mutable references. `const(row)` repeats the same reference at every
outer index; it does not clone the row. Each finite result row is allocated
separately; helpers may fill it before installing it in the outer array. The
shared zero row used outside the finite matrix is never mutated.

The public nested-array relations accept an initial heap and matrix references,
and return a final heap and result reference. `MatrixHeap.Stored`, from the shared
`Algo2LeanLib.MatrixHeap` module, connects these references to mathematical
two-dimensional values and requires
well-formed row references. It permits repeated references rather than assuming
that input rows are disjoint. `Extends` records preservation of all previously
allocated rows, outer arrays, and objects. This explicit heap interface captures
sharing that a pure matrix value alone would omit.

For both recursive examples, the theorem precondition is `n = 2^k` for natural
`k`, so `n ≥ 1`. Arbitrary-size padding, rectangular matrices, and invalid
sizes are outside these contracts. The source does not perform dimension
validation: selecting another integer does not establish a correctness or
runtime guarantee.

## What the runtime guarantees mean

`tick` counters measure named operations in the same execution as the returned
matrix. These are unit-cost guarantees for mathematical scalar operations,
cell copies/combinations, and recursive calls. They do not measure wall-clock
seconds or the bit complexity of arithmetic on arbitrarily large integers.
For Strassen, `products` counts only scalar products at recursive leaves.
The linear helper also evaluates `sign * b[i]` with sign `+1` or `−1`; those
operations belong to `linear_cells`, not to the `products` clock. Thus `7^k`
is not a count of every source-level multiplication operator.
They also do not assert an exact count of every generated Lean transition.
Outer-array and row allocations are not separate clocks; the exact counts below
refer to the named scalar/cell operations and recursive calls. The new row loops
do not change those counts.

For the iterative program, `multiply_add = n³` and every other counter has
zero increment. For the eight-way recursive program:

- `multiplications = 8^k = (2^k)³`;
- `calls = C₈(k)`, where `C₈(0)=1` and `C₈(k+1)=1+8C₈(k)`;
- `8^k ≤ C₈(k) ≤ 2·8^k`, so their sum is cubic as well.

For Strassen, let `H(0)=0` and `H(k+1)=4^k+7H(k)`. Its exact increments are:

- `products = 7^k`;
- `calls = C₇(k)`, where `C₇(0)=1` and `C₇(k+1)=1+7C₇(k)`;
- `linear_cells = 18H(k)`;
- `copied_cells = 12H(k)` (eight quadrant copies and four output blocks);
- every other named counter remains unchanged.

Lean proves that the sum of these four counters lies between `7^k` and
`13·7^k`. The combined `correctness_and_running_time` contract includes this
bound in the editor analysis; the older `runtime_bounds` theorem retains its
valid upper bound of `33·7^k`. The general substitution proof is
`Chapter4RecurrenceApplications.runtime_via_substitution`. These are concrete
two-sided asymptotic bounds over all natural depths.
For `n=2^k`, it is the familiar **Θ(n^(log₂ 7))** bound. The checked Strassen
theorem is stated using natural powers and needs no real logarithm library.
The master theorem and its Mathlib dependency are not part of this library.

## Reusable call contracts

Each analysis exports a `call` theorem under `MatrixMultiplyAnalysis`,
`MatrixRecursiveAnalysis`, or `MatrixStrassenVerified`. The contract packages a
finite generated `Call`, the complete result matrix, preservation of previously
allocated storage, a fresh outer array, pairwise distinct fresh finite rows, and
exact increments of every named clock from the caller's supplied initial values.
The `correctness_and_running_time` theorem adds a uniform positive runtime bound
for that same call. The recursive algorithms still require a power-of-two size.

The contracts live in the ordinary analysis files and can be imported through
`Algo2LeanExamples.MatrixMultiply`, `Algo2LeanExamples.MatrixRecursive`, and
`Algo2LeanExamples.MatrixStrassen`. A source project can reuse the same proof
bodies with its generated module imports. `tests/test_matrix_contracts.py` checks
two actual imported calls in sequence for each algorithm, including intermediate
storage and accumulated costs, and builds a downloaded project using all three
analysis libraries without Mathlib or repository search paths.

The nested representation changes the matrix examples' public inputs and outputs:
callers supply the heap and outer references, and receive a final heap and result
reference. It replaces the former flat-sequence matrix API; the mathematical
product and named-operation bounds are preserved.

## Main theorem names

`MatrixMultiplyAnalysis` contains `output_with_cost`, `terminates`,
`every_output_correct`, `every_execution_preserves`, `product_entry`, and
`runtime_cubic`. `every_execution_fresh_rows` identifies every finite output
row and proves that distinct row indices have distinct fresh references.

`MatrixRecursiveAnalysis` contains `output_with_cost`, `output_with_cost_iff`,
`every_output_correct`, `innerProduct_eq_sum`, `runtime_bounds`, and
`callCount_exact`. Its `every_execution_fresh_rows` proves independent, fresh
finite output rows. Its `recursive_summary` and `block_summary` work under
arbitrary caller stacks. `result_heap_preserves` proves preservation of all
previously allocated rows, outer arrays, and objects.

`MatrixStrassenVerified` contains `output_with_cost`, `every_output_costs`,
`terminates`, `every_output_entry`, `every_output_outside`,
`every_execution_preserves`, `every_execution_fresh`,
`every_execution_fresh_rows`, and `runtime_bounds`.
`MatrixStrassenExecution.strassen_summary` also supplies a reusable
arbitrary-heap/caller contract with exact contents, preserved old sequences,
and additive counter effects. Its stronger `strassen_summary_fresh` also
exposes that the returned outer-array reference was not allocated in the initial
heap; `strassen_summary_rows` additionally proves fresh, pairwise distinct
finite output rows. All three APIs retain explicit well-formed input-row
hypotheses; callers can reuse the shared `MatrixHeap.Stored`, `Extends`, and
`FreshRows` lemmas.

## Use in the editor or CLI

Choose `matrix_multiply.algo`, `matrix_recursive.algo`, or
`matrix_strassen.algo` from **Examples**. The matching proof loads into the
**Lean analysis** pane; choose **Check analysis**.

From the repository root:

```sh
python3 -m algo2lean analyze examples/matrix_multiply.algo examples/analysis/matrix_multiply.lean
python3 -m algo2lean analyze examples/matrix_recursive.algo examples/analysis/matrix_recursive.lean
python3 -m algo2lean analyze examples/matrix_strassen.algo examples/analysis/matrix_strassen.lean
```

The Strassen analysis is bundled from small, maintained modules in
[proofs/chapter4](../proofs/chapter4/README.md), because the current editor
checks one analysis file at a time. After editing those modules, regenerate it:

```sh
python3 scripts/build_chapter4_analysis.py
python3 scripts/build_chapter4_analysis.py --check
```

The normal analysis test checks every example against freshly compiled source.
Additional behavioral tests compare the three implementations with an
independent multiplication oracle, check aliases and input preservation, and
verify exact counters. Those tests complement the universal Lean proofs.

The current scope covers the matrix algorithms of §4.1–4.2 and the general
discrete substitution and recursion-tree frameworks of §4.3–4.4. It does not
formalize every exercise or all recurrence examples. The master theorem (§4.5),
the continuous master theorem (§4.6), and a general Akra–Bazzi interface (§4.7)
remain outside this library. See the [framework guide](RECURRENCES.md) for exact
scope and checking instructions.

Chapter scope follows the publisher's [fourth-edition table of contents](https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/11599/4e_toc.pdf).
