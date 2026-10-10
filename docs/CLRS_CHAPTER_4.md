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

A matrix occupies indices `0` through `n*n-1` of a `Seq` in row-major order:
entry `(i,j)` is `a[i*n+j]`. Input values at other integer indices are
unrestricted. Results are fresh sequences and are zero outside that finite
prefix. The programs preserve their inputs, including when both input
references alias the same sequence in the heap interface. Integers are
unbounded mathematical integers.

The iterative example flattens the two output-coordinate loops into a single
cell loop and uses a dot-product helper. It supports the empty matrix.
The classic recursive example uses offsets into its original inputs and
accumulates eight subproducts into one fresh zero matrix. Strassen explicitly
copies quadrants, combines intermediate matrices, recursively computes seven
products, and joins four result blocks.

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
`13·7^k`, using the generic substitution framework. The bundled editor
analysis proves `33·7^k`; the sharper library theorem is
`Chapter4RecurrenceApplications.runtime_via_substitution`. These are concrete
two-sided asymptotic bounds over all natural depths.
For `n=2^k`, it is the familiar **Θ(n^(log₂ 7))** bound. The checked theorem is
stated using natural powers; the project does not introduce a real logarithm
library merely to restate that change of variable.

## Main theorem names

`MatrixMultiplyAnalysis` contains `output_with_cost_iff`, `terminates`,
`every_output_correct`, `every_execution_preserves`, `product_entry`, and
`runtime_cubic`.

`MatrixRecursiveAnalysis` contains `output_with_cost`, `output_with_cost_iff`,
`every_output_correct`, `innerProduct_eq_sum`, `runtime_bounds`, and
`callCount_exact`. Its `recursive_summary` and `block_summary` work under
arbitrary caller stacks; `blockEffect_read_other` proves preservation outside
the accumulator reference.

`MatrixStrassenVerified` contains `output_with_cost`, `output_with_cost_iff`,
`terminates`, `every_output_entry`, `every_output_outside`,
`every_execution_preserves`, `every_execution_fresh`, and `runtime_bounds`.
`MatrixStrassenExecution.strassen_summary` also supplies a reusable
arbitrary-heap/caller contract with exact contents, preserved old sequences,
and additive counter effects. Its stronger `strassen_summary_fresh` also
exposes that the returned reference was not allocated in the initial heap.

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
