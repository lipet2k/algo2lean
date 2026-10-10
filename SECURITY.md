# Execution and trust boundaries

The compiler parses `.algo` source and generates Lean definitions. It does not
execute that source as Python. The hosted compiler runs inside a browser worker;
source and proof text remain in the visitor's browser. Static hosting does not
provide a Lean proof-checking service.

The local editor binds to localhost and checks request origins. Keep it local.
Lean analysis is executable Lean code: checking a file is not a sandbox for
untrusted proof code or imports. Review unfamiliar Lean files before checking
them, or use an appropriately isolated environment.

An exact generation match means the supplied files match a particular compiler
version's output for the supplied sources. It does not establish that a proof
has been checked, that a theorem captures the intended specification, or that
the compiler is formally verified. The compiler currently has tests and checked
examples, rather than a machine-checked compiler-correctness proof.

For a suspected security issue, use the repository's private vulnerability
reporting channel when available. Avoid placing credentials or private source
in public issues. Include the compiler version and a minimal reproduction.
