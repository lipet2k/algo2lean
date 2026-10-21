"""Curated editor projects, with their real imported sources and analyses.

The catalog stays cheap to load. Folder projects include all source modules and
companion proofs. Graph algorithms also gather their shared graph and heap
dependencies, so every selection opens a self-contained editable project.
"""

from pathlib import Path

from .modular import compile_project
from .modules import generated_module_name
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
    "additional_types": (
        "Values and collections",
        "main.algo",
        "Count frequencies with a dictionary, track visited values with a set, and average tuple coordinates using exact real arithmetic. Real examples use optional Mathlib support.",
    ),
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
    "randomized": (
        "Randomized algorithms",
        "sampling.algo",
        "Uniform integer draws, a six-sided die, imported random calls, and repeated coin flips. Probability analyses use optional Mathlib support.",
    ),
    "randomized_clrs": (
        "CLRS randomized algorithms",
        "shuffle.algo",
        "Shuffle, hiring, selection, quicksort, and coupon collection. Explore joint output laws, expected costs, and runtime tails with the developing probability analyses.",
    ),
    "kruskal": (
        "Kruskal",
        "kruskal.algo",
        "Build a minimum spanning forest with union by rank and path compression; compare total running time with the faster entry for already-sorted edges.",
    ),
    "prim": (
        "Prim with a Fibonacci Heap",
        "prim/prim_fibonacci.algo",
        "Grow a minimum spanning tree using the shared Fibonacci heap and its reusable correctness and amortized running-time analysis.",
    ),
    "dijkstra": (
        "Dijkstra",
        "dijkstra/dijkstra_binary.algo",
        "One shared algorithm, binary and Fibonacci heaps, and reusable correctness and running-time proofs.",
    ),
}
_PROJECT_ROOTS = {
    "additional_types": "additional_types",
    "modules": "modules",
    "interfaces": "interfaces",
    "mutual-recursion-imports": "mutual_recursion",
    "randomized": "randomized",
    "randomized_clrs": "randomized_clrs",
    "kruskal": "kruskal",
}
_PROJECT_EXTRA_ENTRIES = {
    "dijkstra": ("dijkstra/dijkstra_fibonacci.algo",),
}

# These programs are single source files with proofs split across several files.
# Keep those proof bodies shared with the command-line checkers and exports.
_PARALLEL_EXAMPLES = {
    "parallel": (
        "Parallel sum and prefix sum",
        "Sum an interval and compute exclusive prefix sums with fork_join; prove linear work and logarithmic span.",
        ("parallel_sum", "upsweep", "prefix_sum", "prefix_contract"),
    ),
    "parallel_merge": (
        "Parallel merge and merge sort",
        "CLRS parallel merge and merge sort, with correctness, storage preservation, and work/span bounds.",
        ("binary_search", "merge", "merge_sort", "contracts"),
    ),
    "parallel_matrix": (
        "Parallel matrix multiplication",
        "Multiply nested matrices with parallel rows, columns, and dot products; include allocation in the work/span analysis.",
        ("dot", "columns", "rows", "allocation", "contracts"),
    ),
}


def parallel_example_analysis(identifier, root=None):
    """Combine the maintained proof bodies without changing their statements."""
    directory = Path(root) if root is not None else EXAMPLES
    modules = _PARALLEL_EXAMPLES[identifier][2]
    imports, bodies = [], []
    for name in modules:
        path = directory / identifier / "analysis" / (name + ".lean")
        body = []
        for line in path.read_text(encoding="utf-8").splitlines():
            if line.startswith("import "):
                module = line.removeprefix("import ").strip()
                if module not in modules and line not in imports:
                    imports.append(line)
            else:
                body.append(line)
        bodies.append(f"-- Source: examples/{identifier}/analysis/{path.name}\n" + "\n".join(body))
    return "\n".join(imports) + "\n\n" + "\n\n".join(bodies) + "\n"


def parallel_examples(root=None):
    """Offer the parallel programs and complete analyses as single-file examples."""
    directory = Path(root) if root is not None else EXAMPLES
    examples = []
    for identifier, (name, description, _) in _PARALLEL_EXAMPLES.items():
        filename = identifier + ".algo"
        module = generated_module_name(filename)
        examples.append({"name": name, "filename": filename, "description": description,
                         "source": (directory / identifier / filename).read_text(encoding="utf-8"),
                         "analysis": parallel_example_analysis(identifier, directory),
                         "module": module, "points_module": module + "Points"})
    return examples


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
         "folder": _PROJECT_ROOTS.get(identifier, identifier),
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
