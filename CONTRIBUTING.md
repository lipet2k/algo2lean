# Contributing

Algo2Lean aims to make algorithms and their Lean analyses readable and reusable.
Bug reports are most useful with a small `.algo` input, the compiler version,
the observed result, and the expected behavior. Include a minimal Lean proof
when reporting a problem with the generated interface.

## Development

Use Python 3.9 or newer. No Python packages are required. Install the version of
Lean recorded in `lean-toolchain` to check proofs, and Node.js 22 or newer to run
the editor tests. From the repository root:

```sh
python3 -m unittest discover -v
node --test tests/test_*.js
python3 -m algo2lean.publication --check-citation
python3 scripts/build_chapter4_analysis.py --check
```

Lean tests explain their skips when Lean is unavailable. A release must run
with Lean and the [optional Mathlib package](probability/README.md) available,
so probability and real-valued proofs are checked too. Install those dependencies
once before the full run. Ordinary compilation and Std-only proofs do not need
them. CI checks the compiler/editor, the actual pinned browser runtime and proof
downloads, and the full proof suite with Lean and Mathlib.

Make changes with focused regression tests. Language changes need an explicit
account of evaluation order, mutation, undefined operations, and termination.
Keep the ordinary generated definitions independent of source line labels.
Theorem and helper-lemma statements should use the public, source-facing Lean
interface; proof bodies may inspect generated transitions.

Edit Strassen proof modules in `proofs/chapter4`, then regenerate their editor
bundle with `python3 scripts/build_chapter4_analysis.py`. Other examples keep
their analyses beside the sources as described in the examples guides.

## Releases

Record changes and validation in `CHANGELOG.md`. Keep publication information in
`publication.json` and regenerate `CITATION.cff` when that information changes.
Follow [the hosting guide](docs/HOSTING.md) to build and archive numbered compiler
versions. Published versions and tags must remain fixed.

Contributions are provided under the project's [Apache License 2.0](LICENSE). Preserve
third-party notices and credit the authors of contributed algorithms and proofs.
