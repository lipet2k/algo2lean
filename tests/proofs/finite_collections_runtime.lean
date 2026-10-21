import Algo2LeanLib.FiniteCollections
import Algo2LeanLib.Footprint
open Algo2LeanGenerated

namespace FiniteCollectionsRuntime

def ints : SetType Int where
  name := "Int"
  toValueCodec := .int
  keyEq := inferInstance

def mapping : DictType Int Int where
  keyName := "Int"
  valueName := "Int"
  key := .int
  value := .int
  keyEq := inferInstance

def nullable : DictType Int (Option ObjectRef) where
  keyName := "Int"
  valueName := "Node | None"
  key := .int
  value := .nullableObject
  keyEq := inferInstance

def refs : DictType Int SeqRef where
  keyName := "Int"
  valueName := "Seq"
  key := .int
  value := .seq
  keyEq := inferInstance

def raw (collection : Collection) : Heap := ({} : Heap).allocateCollection collection

-- A matching header alone does not certify a finite container's payload.
example : ¬ints.valid (raw (.set "Int" [.intValue 1, .intValue 1])) 0 := by decide
example : ¬ints.valid (raw (.set "Int" [.intValue 1, .boolValue true])) 0 := by decide
example : ¬mapping.valid (raw (.dictionary "Int" "Int"
    [(.intValue 1, .intValue 2), (.intValue 1, .intValue 3)])) 0 := by decide
example : ¬mapping.valid (raw (.dictionary "Int" "Int" [(.boolValue true, .intValue 2)])) 0 := by decide
example : ¬mapping.valid (raw (.dictionary "Int" "Int" [(.intValue 1, .boolValue true)])) 0 := by decide
example : ¬mapping.valid (raw (.dictionary "Int" "Bool" [(.intValue 1, .boolValue true)])) 0 := by decide
example : ¬ints.valid (raw (.sequence "Int" (fun _ => .intValue 1))) 0 := by decide
example : ¬ints.valid ({ collections := fun _ => some (.set "Int" []) } : Heap) 0 := by decide
example : ¬nullable.valid (raw (.dictionary "Int" "Node | None" [(.intValue 1, .intValue 7)])) 0 := by decide

-- Present null and missing keys are distinct observations.
example : nullable.get (nullable.create {} [(3, none)]).1 0 3 = some none := by decide
example : nullable.get (nullable.create {} [(3, none)]).1 0 9 = none := by decide
example : nullable.contains (nullable.create {} [(3, none)]).1 0 3 = true := by decide

-- Initial construction canonicalizes repeated entries without moving the first position.
example : ints.keys (ints.create {} [3, 1, 3, 2]).1 0 = [3, 1, 2] := by decide
example : mapping.entries (mapping.create {} [(3, 7), (1, 8), (3, 9)]).1 0 =
    some [(3, 9), (1, 8)] := by decide
example : mapping.keys (mapping.set (mapping.create {} [(3, 7), (1, 8)]).1 0 3 9) 0 = [3, 1] := by decide
example : mapping.keys (mapping.set
    (mapping.erase (mapping.create {} [(3, 7), (1, 8)]).1 0 3) 0 3 9) 0 = [1, 3] := by decide
example : ints.keys (ints.insert (ints.erase (ints.create {} [3, 1]).1 0 3) 0 3) 0 = [1, 3] := by decide

-- A forged descriptor cannot mutate a cell with a different collection header.
example (heap : Heap) (ref : CollectionRef) (payload : List ObjectValue)
    (wrong : heap.collectionType ref ≠ some (.set "Int")) :
    heap.replaceCollection ref (.set "Int" payload) = heap := by
  cases heap
  simp_all [Heap.replaceCollection, Collection.header]
example (heap : Heap) (ref : CollectionRef) (index : Int) (value : ObjectValue) :
    (heap.writeElement ref index value).collectionType ref = heap.collectionType ref := by simp

-- Storing and copying references retains identity; updates through either alias see shared storage.
example (heap : Heap) (ref : SeqRef) :
    refs.get (refs.create heap [(7, ref)]).1 heap.nextCollection 7 = some ref := by
  change refs.get (refs.create heap [(7, ref)]).1 (refs.create heap [(7, ref)]).2 7 = some ref
  simp only [DictType.get, DictType.entries_create]
  rfl
example (heap : Heap) (container : CollectionRef) (key : Int) :
    refs.get (refs.copy heap container).1 (refs.copy heap container).2 key =
      refs.get heap container key := refs.get_copy heap container key
example (heap : Heap) (container : CollectionRef) (present : refs.valid heap container) :
    (refs.copy heap container).2 ≠ container := refs.copy_fresh heap container present
example (heap : Heap) (alias original : SeqRef) (same : alias = original) (index value : Int) :
    (heap.write alias index value).read original index = value := by subst alias; simp

-- The local frame proof needs only the changed cell; no transcript is constructed.
example (heap : Heap) (ref : CollectionRef) (key value : Int) :
    heap.Footprint (mapping.set heap ref key value) [] [] [ref] := by
  cases observed : mapping.entries heap ref with
  | none => simpa [DictType.set, observed] using Heap.Footprint.refl heap [] [] [ref]
  | some entries =>
    simpa [DictType.set, observed] using
      (Heap.Footprint.refl heap [] [] [ref]).replaceCollection ref
        (.dictionary mapping.keyName mapping.valueName
          ((@OrderedEntries.set Int Int mapping.keyEq entries key value).map fun entry =>
            (mapping.key.encode entry.1, mapping.value.encode entry.2))) (Or.inl (by simp))
example (heap : Heap) (ref : CollectionRef) :
    heap.Footprint (mapping.copy heap ref).1 [] [] [] :=
  (Heap.Footprint.refl heap [] [] []).allocateCollection _
example (heap : Heap) (ref : CollectionRef) (key value : Int) (clock : String) :
    (mapping.set heap ref key value).clocks clock = heap.clocks clock := by simp

end FiniteCollectionsRuntime
