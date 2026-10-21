# Parallel matrix multiplication with arrays of rows

`parallel_matrix.algo` multiplies two square integer matrices represented as
`Seq[Seq]`: `a[i][j]` is row `i`, column `j`. It uses balanced fork–join trees
across output rows, output columns, and the terms of each dot product. There is
no flattened row-major indexing or power-of-two dimension requirement.

In the website's Examples menu, choose **Parallel matrix multiplication** to load
the source and complete Lean analysis. **Save analysis** downloads a checkable
Lean project with the shared libraries.

## Algorithms and storage contracts

- `parallel_matrix_dot` computes a row/column dot product over an arbitrary
  integer-indexed interval, combining independent halves in parallel.
- `parallel_matrix_columns` writes a specified column interval of one output row.
- `parallel_matrix_rows` writes a specified interval of output rows.
- `parallel_matrix_multiply_into` fills the first `n × n` entries of an existing
  output matrix, with all output rows already allocated.
- `matrix_new_rows` sequentially installs distinct zero-filled output rows.
- `parallel_matrix_multiply` allocates the outer sequence, its zero default row,
  and `n` distinct output rows before invoking the parallel computation.

The main contracts require a nonnegative dimension and allocated input rows.
Input entries are arbitrary mathematical integers. Inputs may be the same
matrix, and read-only input rows may share identities. The preallocated output
must have distinct rows, all disjoint from every input row that is read.

The product specification is the usual finite dot product:

```text
out[i][j] = sum(a[i][k] * b[k][j] for k = 0, ..., n-1)
```

The source-connected proofs also cover termination, compatible fork accesses,
input preservation, caller counters, and unrelated heap storage. The preallocated
operation preserves outer row pointers and writes only columns `0 .. n-1` of
its selected output row identities. All other physical cells are preserved;
other aliases of a selected row observe the same updates, including aliases at
outer indices outside `0 .. n-1`. The allocating operation returns a fresh outer sequence and fresh distinct result
rows, with zero outside the result rectangle. It allocates `n + 1` ordinary
sequences (including the default row) and one outer typed sequence.

`const(row)` shares the same row at every index. It does not produce independent
rows. The allocator explicitly replaces each of the `n` output row pointers with
a fresh sequence before any parallel writes begin.

## Work and span

The checked proofs establish:

| Entry point | Work | Span |
| --- | --- | --- |
| Preallocated `parallel_matrix_multiply_into` | O(n³) | O(log(n + 1)) |
| Allocating `parallel_matrix_multiply` | O(n³) | O(n + log(n + 1)) |

The precise inequalities include additive constants for dimension zero.
The allocating span includes the sequential creation of distinct output rows.
The current fork model excludes allocation inside children, so this setup cannot
be silently omitted from the complete algorithm's runtime bound.

These are bounds on the same generated execution as correctness. Main runtime
statements quantify a uniform positive constant; explicit bounds remain available
for reuse. The compiler counts lowered instructions, calls, returns, and forks
under its mathematical unit-cost model. Integer arithmetic and constant-sequence
allocation have unit cost; no bit-complexity, processor scheduler, or elapsed-time
guarantee is asserted. See [the fork–join guide](../../docs/PARALLEL_ALGORITHMS.md).

This is a conventional cubic matrix product parallelized at all three levels,
including reduction within each cell. It is not Strassen multiplication. The
balanced recursive helpers express parallel loops and reduction using the
compiler's binary `fork_join` operation.

## Proofs, checking, and export

Proof modules separate dot products, columns, rows, allocation, and the complete
allocating entry point. The preallocated public results are in
`ParallelMatrixIntoAnalysis`; the allocating results are in
`ParallelMatrixPublic`. Both provide `call_contract`, `correctness`,
`correctness_of_parallel_call`, `running_time_explicit`, and `running_time`.
The full theorem selector uses qualified names, so both entry points can be
selected even though the editor overview shows only one result per category.

```sh
python3 scripts/check_parallel_matrix_examples.py
python3 scripts/check_parallel_matrix_examples.py --write-analysis /tmp/ParallelMatrixAnalysis.lean --export /tmp/parallel-matrix-analysis.zip
python3 -m unittest tests.test_parallel_nested tests.test_parallel_matrix -v
```

The checker compiles the current `.algo` source, combines the exact separate proof
bodies into one editor analysis, checks it, and audits the principal theorem
axioms. The exported ZIP includes the generated definitions, proof, and shared
libraries; `lake --no-cache build` checks it in an isolated directory.

Executable regressions compare all 6,561 pairs of ternary 2 × 2 matrices against
ordinary matrix multiplication. Additional tests cover dimensions zero through
nine, 80-digit integer entries, equal inputs and shared input rows, fresh output
rows, prepopulated output sentinels, and shifted dot-product/column intervals.
Compiler tests check row-pointer reads as well as inner cell accesses, aliases,
outer-slot mutation conflicts, and the continued prohibition on child allocation.
These finite checks complement the general Lean proofs.
