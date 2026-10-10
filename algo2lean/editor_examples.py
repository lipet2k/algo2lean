"""Curated editor projects, with their real imported sources and analyses.

The catalog stays cheap to load. Folder projects include all source modules and
companion proofs. Dijkstra also gathers its shared graph and heap dependencies,
so every selection opens a self-contained editable project.
"""

from pathlib import Path

from .modular import compile_project
from .project import load_project
from .project_checker import project_lean_sources


EXAMPLES = Path(__file__).resolve().parents[1] / "examples"
# Start with control flow and values, then mutation and familiar algorithms,
# before proof observations, objects, costs, and the graph-algorithm projects.
_SINGLE_FILE_ORDER = (
    "sum_loop", "range_sum", "factorial", "gcd",
    "mutual_recursion", "divergence", "sequences", "mutable_sequences",
    "lower_bound", "merge_sort", "transcripts", "classes", "object_sequences",
    "clocks", "weighted_ticks", "heap_height", "select_min", "relax_edge",
    "graph", "indexed_heap", "fibonacci_heap",
)
_HIDDEN_SINGLE_FILES = {"dijkstra.algo", "dijkstra_fibonacci.algo"}
_PROJECTS = {
    "modules": (
        "Reusable algorithms",
        "pipeline.algo",
        "Import proved algorithms and compose their correctness and running-time analyses, from simple calls to sort then search.",
    ),
    "interfaces": (
        "Abstract interfaces",
        "use_direct.algo",
        "Prove an algorithm once, choose its data representation, and reuse the linked proof in another caller.",
    ),
    "mutual-recursion-imports": (
        "Mutual recursion across files",
        "client.algo",
        "Even and odd call each other across files; a client reuses their correctness and runtime proof.",
    ),
    "kruskal": (
        "Kruskal",
        "kruskal.algo",
        "Build a minimum spanning forest with reusable union-find, path compression, union by rank, and heap-based edge sorting.",
    ),
    "dijkstra": (
        "Dijkstra",
        "composable_dijkstra/dijkstra_binary.algo",
        "One shared algorithm, binary and Fibonacci heaps, and reusable correctness and running-time proofs.",
    ),
}
_PROJECT_ROOTS = {
    "modules": "modules",
    "interfaces": "interfaces",
    "mutual-recursion-imports": "mutual_recursion",
    "kruskal": "kruskal",
}
_PROJECT_EXTRA_ENTRIES = {
    "dijkstra": ("composable_dijkstra/dijkstra_fibonacci.algo",),
}


def _project_root(identifier):
    """Keep each example's original import paths and companion proof names."""
    return EXAMPLES / _PROJECT_ROOTS.get(identifier, "")


def example_files(root=None):
    """Order known examples pedagogically; keep newly discovered files at the end."""
    directory = Path(root) if root is not None else EXAMPLES
    order = {name: index for index, name in enumerate(_SINGLE_FILE_ORDER)}
    files = (path for path in directory.glob("*.algo")
             if path.stem.isascii() and path.stem.isidentifier()
             and path.name not in _HIDDEN_SINGLE_FILES)
    return sorted(files, key=lambda path: (order.get(path.stem, len(order)), path.name))


def _folder_files(root, suffix):
    """Read source modules with valid path names, excluding editor backup files."""
    return {
        path.relative_to(root): path.read_text(encoding="utf-8")
        for path in sorted(root.rglob("*" + suffix))
        if all(part.isascii() and part.isidentifier()
               for part in path.relative_to(root).with_suffix("").parts)
    }


def project_examples():
    """Return previews without compiling or loading the example's proof files."""
    return [
        {"project_id": identifier, "name": name, "filename": entry,
         "folder": _PROJECT_ROOTS.get(identifier, "composable_dijkstra"),
         "description": description, "source": (_project_root(identifier) / entry).read_text(encoding="utf-8")}
        for identifier, (name, entry, description) in _PROJECTS.items()
    ]


def load_example_project(identifier):
    """Return a browser project for a fixed catalog id; unknown ids raise KeyError.

    Sources use root-relative .algo paths. Analyses use canonical Lean module
    names, matching the editor's project request format. The files are copied
    unchanged from the examples directory; no generated Lean is bundled.
    """
    name, entry, _ = _PROJECTS[identifier]
    root = _project_root(identifier)
    if identifier in _PROJECT_ROOTS:
        sources = {path.as_posix(): text for path, text in _folder_files(root, ".algo").items()}
        analyses = {
            "Algo." + ".".join(path.with_suffix("").parts) + ".Analysis": text
            for path, text in _folder_files(root / "analysis", ".lean").items()
        }
        return {"name": name, "entry": entry, "sources": sources, "analyses": analyses}
    source_modules, lean_sources = {}, {}
    for source_entry in (entry,) + _PROJECT_EXTRA_ENTRIES.get(identifier, ()):
        compiled = compile_project(root / source_entry, root=root)
        source_modules.update(compiled.project.modules)
        lean_sources.update(project_lean_sources(compiled,
            analysis_modules=("Algo." + compiled.project.entry + ".Analysis",)))
    analyses = {module: source for module, source in lean_sources.items()
                if module.endswith(".Analysis")}
    # Proofs may import an algorithm outside the entry's source dependency DAG.
    # Include its source closure so that the exported project is self-contained.
    for module in lean_sources:
        if not module.startswith("Algo."):
            continue
        source_name = ".".join(module.split(".")[1:-1])
        source_path = root.joinpath(*source_name.split(".")).with_suffix(".algo")
        if source_name not in source_modules and source_path.is_file():
            source_modules.update(load_project(source_path, root=root).modules)
    sources = {
        Path(*module.split(".")).with_suffix(".algo").as_posix(): snapshot.source
        for module, snapshot in sorted(source_modules.items())
    }
    return {"name": name, "entry": entry, "sources": sources, "analyses": analyses}
