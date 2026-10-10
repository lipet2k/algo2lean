"""A caller reuses Dijkstra contracts without inspecting their transitions."""

from pathlib import Path
import shutil
import unittest

from algo2lean.analysis import check_analysis
from algo2lean.compiler import compile_source


ROOT = Path(__file__).resolve().parents[1]


CLIENT = r'''
namespace DijkstraContractReuse
open Algo2LeanGenerated Algo2Lean.Dijkstra ANALYSIS_NAMESPACE

-- Both calls reuse the same graph representation. The first distance array
-- remains readable after the second call; clock increments compose without
-- resetting counters or inspecting either algorithm's transition rules.
theorem twice (heap : Heap) (graph : Ref_Graph) (size source : Int)
    (heads : CollectionRef) (adjacency : Adjacency)
    (represented : GraphRep heap graph size heads adjacency)
    (lower : 0 ≤ source) (upper : source < size) :
    ∃ middle after,
      dijkstra.Call heap (graph, source) middle heap.nextRef ∧
      dijkstra.Call middle (graph, source) after middle.nextRef ∧
      after.read heap.nextRef = middle.read heap.nextRef ∧
      heap.Increments after (Clocks.add (Heap.cost heap middle) (Heap.cost middle after)) := by
  have reusable (before : Heap) (rep : GraphRep before graph size heads adjacency) :
      ∃ after, dijkstra.Call before (graph, source) after before.nextRef ∧
        GraphRep after graph size heads adjacency ∧ before.nextRef < after.nextRef ∧
        before.Footprint after [] [] [] ∧ before.Increments after (Heap.cost before after) := by
    CONTRACT_PROJECTION
  obtain ⟨middle, first, graphAfter, allocated, _, firstCost⟩ := reusable heap represented
  obtain ⟨after, second, _, _, frame, secondCost⟩ := reusable middle graphAfter
  exact ⟨middle, after, first, second, frame.read heap.nextRef allocated (by simp),
    firstCost.trans secondCost⟩

end DijkstraContractReuse
'''


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class DijkstraCallContractsTests(unittest.TestCase):
    def check_client(self, filename, namespace, projection):
        source = ROOT / "examples" / (filename + ".algo")
        compiled = compile_source(source.read_text(), filename=source.name)
        client = CLIENT.replace("ANALYSIS_NAMESPACE", namespace).replace(
            "CONTRACT_PROJECTION", projection)
        analysis = (ROOT / "examples/analysis" / (filename + ".lean")).read_text()
        checked = check_analysis(compiled.lean, analysis + "\n" + client, compiled.module,
                                 points_lean=compiled.points_lean, timeout=300)
        self.assertTrue(checked.ok, checked.output)
        self.assertNotIn("declaration uses `sorry`", checked.output)

    def test_binary_heap_dijkstra_reused_twice(self):
        self.check_client("dijkstra", "DijkstraAnalysis", r'''
    obtain ⟨after, execution, graphAfter, _, _, _, frame, allocated, increments⟩ :=
      dijkstra_call_contract before graph size source heads adjacency rep lower upper
    exact ⟨after, execution, graphAfter, allocated, frame, increments⟩''')

    def test_fibonacci_heap_dijkstra_reused_twice(self):
        self.check_client("dijkstra_fibonacci", "DijkstraFibonacciAnalysis", r'''
    obtain ⟨after, execution, graphAfter, _, allocated, frame, increments, _⟩ :=
      dijkstra_call_contract before graph size source heads adjacency rep lower upper
    exact ⟨after, execution, graphAfter, allocated, frame, increments⟩''')


if __name__ == "__main__":
    unittest.main()
