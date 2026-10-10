"""Curated editor projects, with their real imported sources and analyses.

The catalog stays cheap to load. Selecting an example resolves its dependency
closure using the same module rules as project checking, so the browser receives
an ordinary editable project rather than a separate example-only compiler path.
"""

from pathlib import Path

from .modular import compile_project
from .project import load_project
from .project_checker import project_lean_sources


EXAMPLES = Path(__file__).resolve().parents[1] / "examples"
# Start with control flow and values, then mutation and familiar algorithms,
# before proof observations, objects, costs, and the Dijkstra building blocks.
_SINGLE_FILE_ORDER = (
    "sum_loop", "range_sum", "factorial", "gcd",
    "mutual_recursion", "divergence", "sequences", "mutable_sequences",
    "lower_bound", "merge_sort", "transcripts", "classes", "object_sequences",
    "clocks", "weighted_ticks", "heap_height", "select_min", "relax_edge",
    "graph", "indexed_heap", "fibonacci_heap", "dijkstra", "dijkstra_fibonacci",
)
_PROJECTS = {
    "dijkstra-generic": (
        "Dijkstra — generic priority queue (imports)",
        "composable_dijkstra/dijkstra.algo",
        "The shared algorithm imports a graph and a priority-queue interface; its proof works with either heap.",
    ),
    "dijkstra-binary": (
        "Dijkstra — binary heap (imports)",
        "composable_dijkstra/dijkstra_binary.algo",
        "Imports the shared Dijkstra algorithm and the indexed binary heap, with reusable correctness and runtime proofs.",
    ),
    "dijkstra-fibonacci": (
        "Dijkstra — Fibonacci heap (imports)",
        "composable_dijkstra/dijkstra_fibonacci.algo",
        "Imports the same Dijkstra algorithm with a Fibonacci heap and its amortized runtime analysis.",
    ),
}


def example_files(root=None):
    """Order known examples pedagogically; keep newly discovered files at the end."""
    directory = Path(root) if root is not None else EXAMPLES
    order = {name: index for index, name in enumerate(_SINGLE_FILE_ORDER)}
    return sorted(directory.glob("*.algo"), key=lambda path: (order.get(path.stem, len(order)), path.name))


def project_examples():
    """Return previews without compiling or loading the example's proof files."""
    return [
        {"project_id": identifier, "name": name, "filename": entry,
         "description": description, "source": (EXAMPLES / entry).read_text(encoding="utf-8")}
        for identifier, (name, entry, description) in _PROJECTS.items()
    ]


def load_example_project(identifier):
    """Return a browser project for a fixed catalog id; unknown ids raise KeyError.

    Sources use root-relative .algo paths. Analyses use canonical Lean module
    names, matching the editor's project request format. The files are copied
    unchanged from the examples directory; no generated Lean is bundled.
    """
    name, entry, _ = _PROJECTS[identifier]
    compiled = compile_project(EXAMPLES / entry, root=EXAMPLES)
    lean_sources = project_lean_sources(compiled,
        analysis_modules=("Algo." + compiled.project.entry + ".Analysis",))
    analyses = {module: source for module, source in lean_sources.items()
                if module.endswith(".Analysis")}
    source_modules = dict(compiled.project.modules)

    # Proofs may import an algorithm outside the entry's source dependency DAG.
    # An optional source re-export alongside a proof also makes that component
    # directly selectable in the editor's module list.
    for module in lean_sources:
        if not module.startswith("Algo."):
            continue
        source_name = ".".join(module.split(".")[1:-1])
        source_path = EXAMPLES.joinpath(*source_name.split(".")).with_suffix(".algo")
        if source_name not in source_modules and source_path.is_file():
            source_modules.update(load_project(source_path, root=EXAMPLES).modules)
    sources = {
        Path(*module.split(".")).with_suffix(".algo").as_posix(): snapshot.source
        for module, snapshot in sorted(source_modules.items())
    }
    return {"name": name, "entry": entry, "sources": sources, "analyses": analyses}
