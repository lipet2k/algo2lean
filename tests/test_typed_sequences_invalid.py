"""Lean checks reject malformed heaps and undefined typed-sequence reads."""

import shutil
import unittest

from algo2lean.analysis import check_analysis
from algo2lean.compiler import compile_source


SOURCE = """\
class Cell:
    value: Int

def read_cell(values: Seq[Cell]) -> Int:
    return values[0].value

def read_flag(values: Seq[Bool]) -> Bool:
    return values[0]

def read_nullable(values: Seq[Cell | None]) -> Int:
    return values[0].value

def read_nested(values: Seq[Seq[Cell]]) -> Int:
    return values[0][0].value
"""


PROOF = """\
import TypedSequencesInvalid
open Algo2LeanGenerated

-- Input validity checks the collection identity and its element-type tag.
theorem invalid_sequence_has_no_execution
    (heap finalHeap : Heap) (values : CollectionRef) (output : Int)
    (invalid : ¬ seq_Cell.valid heap values) :
    ¬ read_cell.Run heap values finalHeap output := by
  rintro ⟨valid, _⟩
  exact invalid valid

example (finalHeap : Heap) (output : Int) :
    ¬ read_cell.Run {} 0 finalHeap output := by
  exact invalid_sequence_has_no_execution _ _ _ _ (by decide)

-- A number below nextCollection still needs an actual collection payload.
example (finalHeap : Heap) (output : Int) :
    ¬ read_cell.Run { nextCollection := 1 } 0 finalHeap output := by
  exact invalid_sequence_has_no_execution _ _ _ _ (by decide)

example (finalHeap : Heap) (output : Int) :
    ¬ read_cell.Run
      (({} : Heap).allocateSequence "Bool" (fun _ => .boolValue true))
      0 finalHeap output := by
  exact invalid_sequence_has_no_execution _ _ _ _ (by decide)

-- Shallow input validity never fabricates a value from a wrong cell decoder.
theorem undefined_object_element_has_no_output
    (heap : Heap) (values : CollectionRef) (output : Int)
    (undefined : seq_Cell.get heap values 0 = none) :
    ¬ read_cell.Returns (heap, values) output := by
  have terminal : Algo2LeanCore.Terminal Step (read_cell.initial heap values) := by
    intro next transition
    unfold read_cell.initial Algo2LeanCore.start at transition
    cases transition <;> simp_all
  rintro ⟨finalHeap, _, trace, run⟩
  cases run with
  | cons transition _ => exact terminal _ transition

-- Cell zero really exists: the decoder's fallback zero must not be observed.
example (output : Int) :
    let cell := create_Cell {} 99
    let heap := cell.1.allocateSequence "Cell" (fun _ => .boolValue true)
    ¬ read_cell.Returns (heap, 0) output := by
  apply undefined_object_element_has_no_output
  decide

theorem undefined_boolean_element_has_no_output
    (heap : Heap) (values : CollectionRef) (output : Bool)
    (undefined : seq_Bool.get heap values 0 = none) :
    ¬ read_flag.Returns (heap, values) output := by
  have terminal : Algo2LeanCore.Terminal Step (read_flag.initial heap values) := by
    intro next transition
    unfold read_flag.initial Algo2LeanCore.start at transition
    cases transition <;> simp_all
  rintro ⟨finalHeap, _, trace, run⟩
  cases run with
  | cons transition _ => exact terminal _ transition

example (output : Bool) :
    ¬ read_flag.Returns
      ((({} : Heap).allocateSequence "Bool" (fun _ => .objectValue 0)), 0)
      output := by
  apply undefined_boolean_element_has_no_output
  decide

-- Null is a valid nullable element but is not a reference to object zero.
theorem null_element_has_no_output
    (heap : Heap) (values : CollectionRef) (output : Int)
    (isNull : seq_Cell_optional.get heap values 0 = some none) :
    ¬ read_nullable.Returns (heap, values) output := by
  have terminal : Algo2LeanCore.Terminal Step (read_nullable.initial heap values) := by
    intro next transition
    unfold read_nullable.initial Algo2LeanCore.start at transition
    cases transition <;> simp_all
  rintro ⟨finalHeap, _, trace, run⟩
  cases run with
  | cons transition _ => exact terminal _ transition

example (output : Int) :
    let cell := create_Cell {} 99
    let values := seq_Cell_optional.const cell.1 none
    ¬ read_nullable.Returns values output := by
  apply null_element_has_no_output
  decide

-- Nested collection references are checked when their contents are accessed.
theorem undefined_nested_element_has_no_output
    (heap : Heap) (values inner : CollectionRef) (output : Int)
    (outerValue : seq_Seq_Cell.get heap values 0 = some inner)
    (undefined : seq_Cell.get heap inner 0 = none) :
    ¬ read_nested.Returns (heap, values) output := by
  have terminal : Algo2LeanCore.Terminal Step (read_nested.initial heap values) := by
    intro next transition
    unfold read_nested.initial Algo2LeanCore.start at transition
    cases transition <;> simp_all
  rintro ⟨finalHeap, _, trace, run⟩
  cases run with
  | cons transition _ => exact terminal _ transition

example (output : Int) :
    let values := seq_Seq_Cell.const {} 33
    ¬ read_nested.Returns values output := by
  apply undefined_nested_element_has_no_output (inner := 33)
  · decide
  · decide

example (output : Int) :
    let flags := seq_Bool.const {} true
    let values := seq_Seq_Cell.const flags.1 flags.2
    ¬ read_nested.Returns values output := by
  apply undefined_nested_element_has_no_output (inner := 0)
  · decide
  · decide
"""


@unittest.skipUnless(shutil.which("lean"), "Lean 4 is not installed")
class TypedSequencesInvalidTests(unittest.TestCase):
    def test_invalid_inputs_decoders_null_and_nested_references(self):
        generated = compile_source(SOURCE, module="TypedSequencesInvalid")
        checked = check_analysis(generated.lean, PROOF, generated.module)
        self.assertTrue(checked.ok, checked.output)


if __name__ == "__main__":
    unittest.main()
