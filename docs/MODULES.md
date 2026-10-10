# Algorithm projects

A project is a folder of `.algo` files and optional Lean companion analyses.
Algorithm modules without circular dependencies are compiled separately.
Mutually dependent source files are compiled as one recursive group. Adding a
caller preserves the imported definitions and existing proofs in both cases.

## Files and imports

The project root determines module names: `sorting.algo` is `sorting`, and
`collections/queue.algo` is `collections.queue`. Paths use ASCII identifiers,
including their original letter case. Python keywords cannot be path components.
There are no implicit packages or `__init__.algo` files.
The root name `_a2l_groups`, including case variants, is reserved for the
compiler's generated recursive implementations and cannot name a source module.
Source identifiers beginning `_a2l_group_` are also reserved for generated
declarations, preventing accidental references to compiler-internal names.

All four import forms are supported at the top level:

```python
import sorting
import collections.queue as queues
from sorting import sort
from collections.queue import Queue as WorkQueue
```

Imported functions, classes, constructors, methods, and type annotations retain
the identity of their defining module. Both `queues.Queue` and `WorkQueue`
therefore name the same class. Explicit reexports are supported: a module can
export a name it imported, and two import paths to the same declaration share
one identity. Dotted imports such as `import collections.queue` permit qualified
references such as `collections.queue.Queue`.

Imports are resolved statically without executing Python. Relative imports,
wildcard imports, conditional or function-local imports, and dynamic imports
are rejected. A missing or invalid imported
declaration is reported with its file and source location. Files reached through
symlinks must stay inside the project root; ambiguous paths and case collisions
are rejected. Recursion is supported both within a module and across imports.

## Mutually recursive files

Two source files can call each other using ordinary imports:

```python
# even.algo
from odd import is_odd

def is_even(n: Int) -> Bool:
    if n <= 0:
        return True
    return is_odd(n - 1)
```

```python
# odd.algo
from even import is_even

def is_odd(n: Int) -> Bool:
    if n <= 0:
        return False
    return is_even(n - 1)
```

The compiler groups mutually dependent modules, collects their declarations,
and emits one shared implementation for each group. The group contains one
transition relation and the frames needed by its functions. Its generated Lean
imports have no cycle. Dependencies outside the group remain separately
compiled and are called through their existing execution interfaces.

Source-facing names stay unchanged: a proof imports `Algo.even.Generated` and
uses `Algo.even.is_even.Call`, while another imports `Algo.odd.Generated` and
uses `Algo.odd.is_odd.Call`. These generated files expose the shared
implementation under each source module's own namespace. An unrelated caller
can import just the function it needs without copying or reproving the group's
implementation. Internal names of the generated group are compiler details.

Group membership and generated definitions are independent of the entry module
and the order in which imports are visited. Editing a member's algorithm
invalidates the group; editing its line labels changes only the named-location
interface. A function-call cycle does not require a termination argument just
to compile: terminating calls, finite prefixes, and diverging computations use
the existing transcript semantics.

Mutual recursion in source code does not justify circular proofs. Establish
the functions' contracts together, usually with a simultaneous induction, then
export the individual call theorems for clients. Lean companion analyses must
still form an acyclic import graph. The weighted parity example in
[`examples/mutual_recursion`](../examples/mutual_recursion/README.md) shows the
source organization and a separate client.

## Compile and check

Run these commands from the repository root:

```sh
python3 -m algo2lean compile examples/modules/pipeline.algo \
  --project examples/modules --check --output-dir /tmp/algo2lean-modules

python3 -m algo2lean analyze examples/modules/pipeline.algo \
  examples/modules/analysis/pipeline.lean --project examples/modules
```

An explicit `--project` gives every file a stable name relative to that folder.
A source containing top-level imports automatically enables project mode, using
its containing folder as the root when `--project` is omitted. Use the explicit
root for entry files in subfolders. `--output-dir` also enables project mode for
an import-free source. Existing single-file commands retain their previous
behavior when neither imports nor project options are present.

For a source module `pkg.example`, project compilation exports:

| Lean module | Exported file | Purpose |
| --- | --- | --- |
| `Algo.pkg.example.Generated` | `Algo/pkg/example/Generated.lean` | Stable algorithm definitions and public relations |
| `Algo.pkg.example.Points` | `Algo/pkg/example/Points.lean` | Named source locations |
| `Algo.pkg.example.Facts` | `Algo/pkg/example/Facts.lean` | Optional checked execution facts and determinism helpers |

The public declarations live in namespace `Algo.pkg.example`. An independently
compiled module defines its transitions in that namespace's `Algo2LeanGenerated`
namespace. A member of a recursive group instead exposes aliases to the group's
shared transition definitions; its public function names stay in the source
namespace. A caller of several group members uses one shared execution wrapper
for the group. Changing a named label changes Points without changing Generated.
`--check` checks Generated and Points throughout the source dependency graph.
Facts are checked when an analysis imports them.

Without `--output-dir`, compile prints the entry module's Generated text. Use
`--output-dir` to obtain the other files and imported dependencies. Project mode
does not support `-o`, `--points-output`, or `--standalone`. Export preserves
unchanged files and rejects destinations that would overwrite source files,
companion proofs, shared libraries, or unrelated handwritten Lean files. The CLI
export is the generated module tree; the editor's project download also includes
the shared libraries and a Lake configuration.

## Reuse a companion analysis

For `pkg/example.algo`, put its proof in either `analysis/pkg/example.lean` or
`pkg/example.lean`, with only one of those paths present. Import it from another
analysis using `import Algo.pkg.example.Analysis`. Proof-only companion modules
are also supported. A proof may import an algorithm outside the entry source's
call graph; the checker compiles that algorithm from the same project root and
source snapshot on demand.

A typical analysis begins with:

```lean
import Algo.pipeline.Generated
import Algo.pipeline.Facts
import Algo.twice.Analysis

open Algo2LeanCore _root_.Algo2LeanGenerated
open Algo.pipeline
```

Import Points only when using named source locations, and Facts when using its
execution helpers. A source import depends on code; its analysis chooses which
proof modules to import. Unused analyses are not required by an ordinary compile
or check.

The public relations for a function `f` include:

| Relation | Meaning |
| --- | --- |
| `f.Returns input output` | A completed execution produces the output |
| `f.ReturnsWithCost input output costs` | One completed execution produces both the output and clock increments |
| `f.Run before input after output` | Execution from the supplied heap to the final heap |
| `f.Call before input after output` | The execution can finish under any caller stack |

The names are grouped under the source function, inside its module namespace:
`Algo.sorting.merge_sort.Call`, or `merge_sort.Call` after `open Algo.sorting`.
Methods use names such as `Counter.add.Call`, and constructors use
`Counter.Call`. Older analyses must replace flat names with the corresponding
scoped names described in the [interface guide](LEAN_INTERFACE.md).

`f.Call.run call` obtains an ordinary completed run from a reusable call.
Importing Facts also enables `f.Run.eq_of_call execution call`, which equates
an arbitrary completed run's final heap and result with the proved call's.
Neither helper requires a transcript argument. Named observations remain in
Points, under `f.At.label`, `f.Local.x`, and `f.Element.a`.

Reusable summaries start from an arbitrary heap, so the same theorem applies
with existing objects, aliases, and nonzero counters. Imported calls use the
callee's own transitions and the current shared heap. `ModuleCall.summary`
lifts an imported summary into a caller; the complete checked example in
[`examples/modules`](../examples/modules/README.md) proves increment, reuses it
twice, and then reuses that caller twice. The final theorem proves the output and
both named clock increments for the same execution. Its proofs currently still
refer to generated local steps and call-linking lemmas; a fully source-facing
proof automation layer is not yet provided.

Clock increments count explicit `tick` operations, rather than machine runtime.
Checking definitions alone does not establish termination or a specification.
Analysis checking rejects unfinished `sorry` proofs and otherwise uses the
analysis's declared assumptions and Lean options.

## Generic algorithms with small interfaces

```python
from algo2lean import Interface

class Counter(Interface):
    def get(self) -> Int: ...
    def put(self, value: Int) -> None: ...
```

An imported interface can be used as a function parameter. Ordinary calls such
as `counter.get()` use the selected implementation's actual transitions. A caller
passes an imported concrete object; the compiler checks its method signatures
and builds the binding. Two calls may use different implementations of the same
generic module without duplicating its compiled body.

Bindings are shared within a compilation unit: an independent module or a
recursive group. Every export of a generic unit shares its
dependencies, including a helper that does not call an interface itself; place
such a helper in a separate module to make it independently callable. A wrapper
can bind some dependencies and forward the others to its own callers.
When selecting a concrete interface implementation inside a recursive group,
import the backend from outside that group. A class defined in the same group
cannot currently serve as that binding's concrete backend. Ordinary calls to
local classes and methods remain supported.

A generic generated module exposes `Dependencies`, with one `Code` field per
used interface. Its relations take that value first:
`increment.Call dependencies before counter after value`.
A concrete wrapper stores the selected code in its generated binding, so its
ordinary output relation needs no extra dependency argument.

The companion specification is a normal Lean record of the laws the client
needs. It can describe outputs, mutation, termination, and costs from the same
calls. Signature compatibility alone does not assert these laws. Each generated
concrete binding provides per-method summary-transfer lemmas, which apply the
implementation's independently proved theorems. Optional `DependencyFacts`
provide determinism, separate from behavioral laws and core definitions.

The [worked counter example](../examples/interfaces/README.md) documents the
current limits, including one implementation per interface type within a module
instance. Interface values in fields/containers, stored concrete-to-interface
conversions, and escaping interface returns are deliberately diagnosed until
their implementation identity can be preserved. A
[typed callable proof example](../examples/modules/CALLABLES.md) exercises the
same execution/contract foundation without objects; source-level callable
annotations are not yet supported.

## Editor workflow

Start `python3 -m algo2lean serve`, then choose **Open project** and select the
folder containing the algorithms and all their imported files. **Open source**
opens a standalone document; use **Open project** for imports. The browser reads
that folder through its folder picker; the server does not receive a filesystem
root. Use **Module** to switch sources and their companion analyses. The generated definitions and
named-location interface remain in the two existing output panes.
For a module in a recursive group, the **Public interface** / **Shared execution**
selector switches those panes between the source module's interfaces and the
group's underlying implementation. Browsing the shared execution does not
change the source-facing names or the analysis's imports. Exported projects
include both the public interfaces and the shared implementation.

To try imports immediately, choose a **Dijkstra … (imports)** entry from
**Examples**. It opens an editable project containing the selected algorithm,
its dependencies, and their existing correctness and runtime analyses. Choose
**Check analysis** to check the complete proof through its imports. These
bundles use the repository files unchanged and include only their required proofs.

After updating the compiler, restart an already running editor server. Reloading
the page updates the editor assets but cannot reload the server's Python modules.
The editor detects a server without project support and displays restart
instructions instead of submitting imports to its old single-file compiler.

Each module keeps its unsaved source and analysis draft when switching. Project
recovery records are separate from standalone drafts; **Close project** restores
the previous standalone document. Same-named folders and independently edited
tabs retain separate browser recovery records. Browser storage can be disabled
or full; the editor reports a failed save and protects unsaved changes.

**Check project** checks the selected module and its source dependencies.
**Check analysis** checks the selected companion and its imports. Source
diagnostics from another algorithm can switch to that module. **Download
project** exports the current source drafts, companion analyses, generated Lean
modules, shared libraries, and a Lake configuration in one ZIP. Open the ZIP's
`source` folder to continue editing, or use its included README to build Lean.
Downloading preserves all source and analysis drafts even if a source has a
syntax error or an import is missing. In that case the ZIP contains a draft
backup and export diagnostics; its README explains why generated build files
are unavailable. Downloading does not itself check the Lean proofs.
Individual source or analysis saves download that file; place it back at the
displayed project-relative path to update the original folder.

The current editor accepts up to 256 source modules and 256 analysis modules
(including a companion for each source). Each source is limited to 256 KiB, each
analysis to 1 MiB, folder text to 6 MiB, and a serialized request to 8 MiB. Paths
are at most 255 characters. Folder traversal is bounded and skips hidden
folders, `node_modules`, `build`, and `dist`. Browser recovery is best effort;
download the project to keep a durable copy.

Project checks cache generated and proof modules using their content, imported
dependencies, shared libraries, and Lean version. Changes invalidate affected
callers and proofs, while unrelated checked modules remain reusable.

## Existing standalone examples

Standalone examples use the single-file namespace and are checked without
`--project`. Project examples use canonical module names and class tags. To reuse
a standalone analysis in a project, adapt its imports and namespaces once; new
callers can then reuse that project analysis unchanged.

For a self-contained editor project, use the **Dijkstra … (imports)** menu entries,
or open `examples/interfaces` or `examples/modules`. When opening from disk,
the modular Dijkstra examples use `examples` as their root so they can import
the existing graph and heap sources. Select a
`dijkstra` module to check its project companion analysis. That root
also contains standalone proofs: they are not all project companions, and
downloading the whole mixed folder may produce a draft backup with import
diagnostics. The selected modular Dijkstra CLI checks do not require those
unrelated standalone proofs.
