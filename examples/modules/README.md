# Reuse an algorithm and its analysis

This example has three separately compiled modules:

| Source | Imported operation | Proved result | Clock increments |
| --- | --- | --- | --- |
| `increment.algo` | — | `value + 1` | `increments += 1` |
| `twice.algo` | `increment`, twice | `value + 2` | `increments += 2` |
| `pipeline.algo` | `twice`, twice, through an alias | `value + 4` | `increments += 4`, `batches += 1` |

Each file has a companion proof under `analysis/`. `TwiceAnalysis.summary`
applies `IncrementAnalysis.summary` twice. `PipelineAnalysis.summary` then
applies the already-proved `TwiceAnalysis.summary` twice. Neither imported proof
needs to change when a new caller is added.

The summary theorems work with an arbitrary initial heap and arbitrary initial
clock values. Each specifies the exact final heap, so correctness, preserved
data, and clock increments describe the same execution. The final
`PipelineAnalysis.output_cost` theorem gives the ordinary integer result and
both operation counts together. `PipelineAnalysis.correct` establishes the
result and exact increments for every completed execution from an arbitrary
initial heap, using the generated `eq_of_summary` helper.

Run these commands from the repository root:

```sh
# Check and export the three compiled modules.
python3 -m algo2lean compile examples/modules/pipeline.algo \
  --project examples/modules --check --output-dir /tmp/algo2lean-modules

# Check the final proof, including its imported component proofs.
python3 -m algo2lean analyze examples/modules/pipeline.algo \
  examples/modules/analysis/pipeline.lean --project examples/modules

# Check the reusable middle component on its own.
python3 -m algo2lean analyze examples/modules/twice.algo \
  examples/modules/analysis/twice.lean --project examples/modules
```

`import Algo.twice.Generated` imports the stable definitions and public
relations. `import Algo.twice.Analysis` resolves the existing companion proof
`analysis/twice.lean`. `Algo.twice.Facts` supplies optional checked determinism
facts; `Algo.twice.Points` contains the separate named-location interface.
Algorithm modules depend on generated definitions. The analysis imports choose
which proofs to check.

Project checks cache each module using its source, transitive dependencies, and
Lean version. Editing a proof or a named label keeps unaffected definitions
reusable. A changed algorithm invalidates the proofs and callers that depend on
it.
