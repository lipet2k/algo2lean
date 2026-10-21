import Algo2LeanLib.Tuple

/-!
Finite mutable containers share the collection identity arena with sequences.
Typed views decode every finite entry and reject duplicate keys. References in
entries remain shared; validity does not traverse referenced objects or sequences.
Key comparison is supplied for the source key type, never for all raw values.
-/

namespace Algo2LeanGenerated

namespace OrderedEntries

variable {Key : Type u} {Value : Type v} [DecidableEq Key]

/-- Lookup uses the first matching entry. Well-formed maps have unique keys. -/
def get : List (Key × Value) → Key → Option Value
  | [], _ => none
  | (key, value) :: rest, wanted => if key = wanted then some value else get rest wanted

/-- Replacement keeps its position; a new key is appended after all old keys. -/
def set : List (Key × Value) → Key → Value → List (Key × Value)
  | [], key, value => [(key, value)]
  | (old, stored) :: rest, key, value =>
      if old = key then (key, value) :: rest else (old, stored) :: set rest key value

def erase (entries : List (Key × Value)) (key : Key) : List (Key × Value) :=
  entries.filter (fun entry => decide (entry.1 ≠ key))

def normalize (entries : List (Key × Value)) : List (Key × Value) :=
  entries.foldl (fun result entry => set result entry.1 entry.2) []

@[simp] theorem get_set_same (entries : List (Key × Value)) (key : Key) (value : Value) :
    get (set entries key value) key = some value := by
  induction entries with
  | nil => simp [set, get]
  | cons entry rest ih =>
    rcases entry with ⟨old, stored⟩
    by_cases equal : old = key <;> simp [set, get, equal, ih]

@[simp] theorem get_set_other (entries : List (Key × Value)) (key other : Key) (value : Value)
    (different : other ≠ key) : get (set entries key value) other = get entries other := by
  induction entries with
  | nil => simp [set, get, Ne.symm different]
  | cons entry rest ih =>
    rcases entry with ⟨old, stored⟩
    by_cases equal : old = key
    · subst old
      simp [set, get, Ne.symm different]
    · simp [set, get, equal, ih]

@[simp] theorem mem_keys_set (entries : List (Key × Value)) (key other : Key) (value : Value) :
    other ∈ (set entries key value).map Prod.fst ↔ other = key ∨ other ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [set]
  | cons entry rest ih =>
    rcases entry with ⟨old, stored⟩
    by_cases equal : old = key
    · subst old
      simp [set]
    · simp [set, equal, ih, or_left_comm]

theorem nodup_set (entries : List (Key × Value)) (key : Key) (value : Value)
    (unique : (entries.map Prod.fst).Nodup) : ((set entries key value).map Prod.fst).Nodup := by
  induction entries with
  | nil => simp [set]
  | cons entry rest ih =>
    rcases entry with ⟨old, stored⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    by_cases equal : old = key
    · subst old
      simpa [set] using unique
    · simp [set, equal, mem_keys_set, unique.1, ih unique.2]

theorem nodup_normalize (entries : List (Key × Value)) :
    ((normalize entries).map Prod.fst).Nodup := by
  have loop : ∀ (remaining result : List (Key × Value)), (result.map Prod.fst).Nodup →
      ((remaining.foldl (fun acc entry => set acc entry.1 entry.2) result).map Prod.fst).Nodup := by
    intro remaining
    induction remaining with
    | nil => intro result unique; exact unique
    | cons entry rest ih =>
      intro result unique
      exact ih _ (nodup_set result entry.1 entry.2 unique)
  exact loop entries [] (by simp)

@[simp] theorem get_erase_same (entries : List (Key × Value)) (key : Key) :
    get (erase entries key) key = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨old, stored⟩
    by_cases equal : old = key <;> simp [erase, get, equal, erase] at ih ⊢ <;> exact ih

@[simp] theorem get_erase_other (entries : List (Key × Value)) (key other : Key)
    (different : other ≠ key) : get (erase entries key) other = get entries other := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨old, stored⟩
    by_cases equal : old = key
    · subst old
      simpa [erase, get, Ne.symm different] using ih
    · simp [erase, get, equal, erase] at ih ⊢
      rw [ih]

theorem nodup_erase (entries : List (Key × Value)) (key : Key)
    (unique : (entries.map Prod.fst).Nodup) : ((erase entries key).map Prod.fst).Nodup := by
  exact List.Nodup.sublist ((List.Sublist.map _ (List.filter_sublist))) unique

@[simp] theorem get_isSome (entries : List (Key × Value)) (key : Key) :
    (get entries key).isSome = decide (key ∈ entries.map Prod.fst) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨old, stored⟩
    by_cases equal : old = key
    · subst old; simp [get]
    · simp [get, equal, ih, Ne.symm equal]


/-- Updating an existing key preserves the key snapshot; new keys append. -/
theorem keys_set (entries : List (Key × Value)) (key : Key) (value : Value) :
    (set entries key value).map Prod.fst =
      if key ∈ entries.map Prod.fst then entries.map Prod.fst
      else entries.map Prod.fst ++ [key] := by
  induction entries with
  | nil => simp [set]
  | cons entry rest ih =>
    rcases entry with ⟨old, stored⟩
    by_cases equal : old = key
    · subst old; simp [set]
    · by_cases present : key ∈ rest.map Prod.fst <;>
        simp [set, equal, ih, Ne.symm equal, present]

end OrderedEntries

namespace OrderedElements

variable {α : Type u} [DecidableEq α]

def insert (values : List α) (value : α) : List α :=
  if value ∈ values then values else values ++ [value]

def erase (values : List α) (value : α) : List α :=
  values.filter (fun other => decide (other ≠ value))

def normalize (values : List α) : List α := values.foldl insert []

@[simp] theorem mem_insert (values : List α) (value other : α) :
    other ∈ insert values value ↔ other = value ∨ other ∈ values := by
  by_cases present : value ∈ values
  · simp [insert, present]
    intro same
    exact same ▸ present
  · simp [insert, present, or_comm]

theorem nodup_insert (values : List α) (value : α) (unique : values.Nodup) :
    (insert values value).Nodup := by
  by_cases present : value ∈ values
  · simp [insert, present, unique]
  · simp [insert, present, unique, List.nodup_append]
    intro other member same
    exact present (same ▸ member)

theorem nodup_normalize (values : List α) : (normalize values).Nodup := by
  have loop : ∀ (remaining result : List α), result.Nodup →
      (remaining.foldl insert result).Nodup := by
    intro remaining
    induction remaining with
    | nil => intro result unique; exact unique
    | cons value rest ih =>
      intro result unique
      exact ih _ (nodup_insert result value unique)
  exact loop values [] (by simp)

@[simp] theorem mem_erase (values : List α) (value other : α) :
    other ∈ erase values value ↔ other ∈ values ∧ other ≠ value := by
  simp [erase]

theorem nodup_erase (values : List α) (value : α) (unique : values.Nodup) :
    (erase values value).Nodup := unique.filter _

@[simp] theorem length_insert (values : List α) (value : α) :
    (insert values value).length = values.length + if value ∈ values then 0 else 1 := by
  by_cases present : value ∈ values <;> simp [insert, present]

end OrderedElements

namespace ValueCodec

/-- Decode all finite entries without following any stored reference. -/
def decodeList (codec : ValueCodec α) : List ObjectValue → Option (List α)
  | [] => some []
  | value :: rest => do
      let first ← codec.decode value
      let remaining ← codec.decodeList rest
      return first :: remaining

def decodeEntries (key : ValueCodec α) (value : ValueCodec β) :
    List (ObjectValue × ObjectValue) → Option (List (α × β))
  | [] => some []
  | entry :: rest => do
      let first ← key.decode entry.1
      let second ← value.decode entry.2
      let remaining ← key.decodeEntries value rest
      return (first, second) :: remaining

@[simp] theorem decodeList_encode (codec : ValueCodec α) (values : List α) :
    codec.decodeList (values.map codec.encode) = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [decodeList, codec.decode_encode, ih]

@[simp] theorem decodeEntries_encode (key : ValueCodec α) (value : ValueCodec β)
    (entries : List (α × β)) :
    key.decodeEntries value (entries.map fun entry => (key.encode entry.1, value.encode entry.2)) =
      some entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp [decodeEntries, key.decode_encode, value.decode_encode, ih]

end ValueCodec

/-- A finite set's element codec, canonical source type tag, and typed equality. -/
structure SetType (α : Type) extends ValueCodec α where
  name : String
  keyEq : DecidableEq α

/-- A finite dictionary compares keys only; value types need no equality instance. -/
structure DictType (Key Value : Type) where
  keyName : String
  valueName : String
  key : ValueCodec Key
  value : ValueCodec Value
  keyEq : DecidableEq Key

namespace SetType

variable {α : Type} (type : SetType α)

/-- Successful observation certifies the finite payload's decodability and uniqueness. -/
def entries (h : Heap) (ref : CollectionRef) : Option (List α) := do
  letI := type.keyEq
  if ref < h.nextCollection then
    match h.collections ref with
    | some (.set name values) =>
        if name = type.name then do
          let decoded ← type.toValueCodec.decodeList values
          if decoded.Nodup then some decoded else none
        else none
    | _ => none
  else none

def valid (h : Heap) (ref : CollectionRef) : Prop := (type.entries h ref).isSome = true

instance (h : Heap) (ref : CollectionRef) : Decidable (type.valid h ref) :=
  inferInstanceAs (Decidable ((type.entries h ref).isSome = true))

/-- A finite insertion-ordered snapshot. Invalid containers have no observations. -/
def keys (h : Heap) (ref : CollectionRef) : List α := (type.entries h ref).getD []

def size (h : Heap) (ref : CollectionRef) : Nat := (type.keys h ref).length

def contains (h : Heap) (ref : CollectionRef) (value : α) : Bool :=
  letI := type.keyEq
  decide (value ∈ type.keys h ref)

def create (h : Heap) (values : List α) : Heap × CollectionRef :=
  letI := type.keyEq
  let values := OrderedElements.normalize values
  (h.allocateCollection (.set type.name (values.map type.encode)), h.nextCollection)

/-- Invalid containers are unchanged; source instructions separately require validity. -/
def insert (h : Heap) (ref : CollectionRef) (value : α) : Heap :=
  letI := type.keyEq
  match type.entries h ref with
  | none => h
  | some values => h.replaceCollection ref
      (.set type.name ((OrderedElements.insert values value).map type.encode))

def erase (h : Heap) (ref : CollectionRef) (value : α) : Heap :=
  letI := type.keyEq
  match type.entries h ref with
  | none => h
  | some values => h.replaceCollection ref
      (.set type.name ((OrderedElements.erase values value).map type.encode))

/-- Allocate a fresh outer container; stored object and collection identities remain shared. -/
def copy (h : Heap) (ref : CollectionRef) : Heap × CollectionRef :=
  (h.allocateCollection (.set type.name ((type.keys h ref).map type.encode)), h.nextCollection)


theorem entries_facts (h : Heap) (ref : CollectionRef) (values : List α)
    (observed : type.entries h ref = some values) :
    ref < h.nextCollection ∧ h.collectionType ref = some (.set type.name) ∧ values.Nodup := by
  letI := type.keyEq
  unfold entries at observed
  split at observed
  · rename_i allocated
    cases found : h.collections ref with
    | none => simp [found] at observed
    | some collection =>
      cases collection with
      | sequence name payload => simp [found] at observed
      | dictionary keyName valueName payload => simp [found] at observed
      | set name payload =>
        simp only [found] at observed
        split at observed
        · rename_i header
          cases decoded : type.toValueCodec.decodeList payload with
          | none => simp [decoded] at observed
          | some xs =>
            rw [decoded] at observed
            change (if xs.Nodup then some xs else none) = some values at observed
            split at observed
            · simp_all [Heap.collectionType, Collection.header]
            · simp_all
        · simp_all
  · simp_all

theorem entries_of_payload (h : Heap) (ref : CollectionRef) (values : List α)
    (allocated : ref < h.nextCollection) (unique : values.Nodup)
    (payload : h.collections ref = some (.set type.name (values.map type.encode))) :
    type.entries h ref = some values := by
  simp [entries, allocated, payload, unique]

@[simp] theorem entries_create (h : Heap) (values : List α) :
    type.entries (type.create h values).1 (type.create h values).2 =
      some (@OrderedElements.normalize α type.keyEq values) := by
  apply type.entries_of_payload
  · exact Nat.lt_succ_self _
  · exact @OrderedElements.nodup_normalize α type.keyEq values
  · simp [create]

@[simp] theorem valid_create (h : Heap) (values : List α) :
    type.valid (type.create h values).1 (type.create h values).2 := by
  simp [valid]

theorem entries_insert (h : Heap) (ref : CollectionRef) (values : List α) (value : α)
    (observed : type.entries h ref = some values) :
    type.entries (type.insert h ref value) ref =
      some (@OrderedElements.insert α type.keyEq values value) := by
  have facts := type.entries_facts h ref values observed
  simp only [insert, observed]
  apply type.entries_of_payload
  · exact facts.1
  · exact @OrderedElements.nodup_insert α type.keyEq values value facts.2.2
  · exact Heap.collections_replaceCollection_same _ _ _ facts.2.1

theorem entries_erase (h : Heap) (ref : CollectionRef) (values : List α) (value : α)
    (observed : type.entries h ref = some values) :
    type.entries (type.erase h ref value) ref =
      some (@OrderedElements.erase α type.keyEq values value) := by
  have facts := type.entries_facts h ref values observed
  simp only [erase, observed]
  apply type.entries_of_payload
  · exact facts.1
  · exact @OrderedElements.nodup_erase α type.keyEq values value facts.2.2
  · exact Heap.collections_replaceCollection_same _ _ _ facts.2.1


theorem valid_insert (h : Heap) (ref : CollectionRef) (value : α)
    (present : type.valid h ref) : type.valid (type.insert h ref value) ref := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values => simp [valid, type.entries_insert h ref values value observed]

theorem valid_erase (h : Heap) (ref : CollectionRef) (value : α)
    (present : type.valid h ref) : type.valid (type.erase h ref value) ref := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values => simp [valid, type.entries_erase h ref values value observed]

theorem keys_insert (h : Heap) (ref : CollectionRef) (value : α)
    (present : type.valid h ref) : type.keys (type.insert h ref value) ref =
      @OrderedElements.insert α type.keyEq (type.keys h ref) value := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values => simp [keys, type.entries_insert h ref values value observed, observed]

theorem keys_erase (h : Heap) (ref : CollectionRef) (value : α)
    (present : type.valid h ref) : type.keys (type.erase h ref value) ref =
      @OrderedElements.erase α type.keyEq (type.keys h ref) value := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values => simp [keys, type.entries_erase h ref values value observed, observed]

@[simp] theorem contains_insert_same (h : Heap) (ref : CollectionRef) (value : α)
    (present : type.valid h ref) : type.contains (type.insert h ref value) ref value = true := by
  simp [contains, type.keys_insert h ref value present]

theorem contains_insert_other (h : Heap) (ref : CollectionRef) (value other : α)
    (different : other ≠ value) (present : type.valid h ref) :
    type.contains (type.insert h ref value) ref other = type.contains h ref other := by
  simp [contains, type.keys_insert h ref value present, different]

@[simp] theorem contains_erase_same (h : Heap) (ref : CollectionRef) (value : α)
    (present : type.valid h ref) : type.contains (type.erase h ref value) ref value = false := by
  simp [contains, type.keys_erase h ref value present]

theorem contains_erase_other (h : Heap) (ref : CollectionRef) (value other : α)
    (different : other ≠ value) (present : type.valid h ref) :
    type.contains (type.erase h ref value) ref other = type.contains h ref other := by
  simp [contains, type.keys_erase h ref value present, different]

theorem size_insert (h : Heap) (ref : CollectionRef) (value : α)
    (present : type.valid h ref) : type.size (type.insert h ref value) ref =
      type.size h ref + if type.contains h ref value then 0 else 1 := by
  by_cases member : value ∈ type.keys h ref <;>
    simp [size, type.keys_insert h ref value present, contains, member]

@[simp] theorem keys_nodup (h : Heap) (ref : CollectionRef) : (type.keys h ref).Nodup := by
  cases observed : type.entries h ref with
  | none => simp [keys, observed]
  | some values => simpa [keys, observed] using (type.entries_facts h ref values observed).2.2

@[simp] theorem entries_copy (h : Heap) (ref : CollectionRef) :
    type.entries (type.copy h ref).1 (type.copy h ref).2 = some (type.keys h ref) := by
  apply type.entries_of_payload
  · exact Nat.lt_succ_self _
  · exact type.keys_nodup h ref
  · simp [copy]

@[simp] theorem valid_copy (h : Heap) (ref : CollectionRef) :
    type.valid (type.copy h ref).1 (type.copy h ref).2 := by simp [valid]

@[simp] theorem keys_copy (h : Heap) (ref : CollectionRef) :
    type.keys (type.copy h ref).1 (type.copy h ref).2 = type.keys h ref := by simp [keys]

theorem copy_fresh (h : Heap) (ref : CollectionRef) (present : type.valid h ref) :
    (type.copy h ref).2 ≠ ref := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values =>
    exact (Nat.ne_of_lt (type.entries_facts h ref values observed).1).symm

@[simp] theorem create_clocks (h : Heap) (values : List α) :
    (type.create h values).1.clocks = h.clocks := rfl

@[simp] theorem copy_clocks (h : Heap) (ref : CollectionRef) :
    (type.copy h ref).1.clocks = h.clocks := rfl

@[simp] theorem insert_clocks (h : Heap) (ref : CollectionRef) (value : α) :
    (type.insert h ref value).clocks = h.clocks := by
  cases observed : type.entries h ref <;> simp [insert, observed, Heap.replaceCollection]

@[simp] theorem erase_clocks (h : Heap) (ref : CollectionRef) (value : α) :
    (type.erase h ref value).clocks = h.clocks := by
  cases observed : type.entries h ref <;> simp [erase, observed, Heap.replaceCollection]

end SetType

namespace DictType

variable {Key Value : Type} (type : DictType Key Value)

def entries (h : Heap) (ref : CollectionRef) : Option (List (Key × Value)) := do
  letI := type.keyEq
  if ref < h.nextCollection then
    match h.collections ref with
    | some (.dictionary keyName valueName values) =>
        if keyName = type.keyName ∧ valueName = type.valueName then do
          let decoded ← type.key.decodeEntries type.value values
          if (decoded.map Prod.fst).Nodup then some decoded else none
        else none
    | _ => none
  else none

def valid (h : Heap) (ref : CollectionRef) : Prop := (type.entries h ref).isSome = true

instance (h : Heap) (ref : CollectionRef) : Decidable (type.valid h ref) :=
  inferInstanceAs (Decidable ((type.entries h ref).isSome = true))

def keys (h : Heap) (ref : CollectionRef) : List Key :=
  ((type.entries h ref).getD []).map Prod.fst

def size (h : Heap) (ref : CollectionRef) : Nat := (type.keys h ref).length

/-- `none` means missing or invalid; a present nullable value is `some none`. -/
def get (h : Heap) (ref : CollectionRef) (key : Key) : Option Value :=
  letI := type.keyEq
  (type.entries h ref).bind (fun values => OrderedEntries.get values key)

def contains (h : Heap) (ref : CollectionRef) (key : Key) : Bool :=
  (type.get h ref key).isSome

def create (h : Heap) (values : List (Key × Value)) : Heap × CollectionRef :=
  letI := type.keyEq
  let values := OrderedEntries.normalize values
  (h.allocateCollection (.dictionary type.keyName type.valueName
    (values.map fun entry => (type.key.encode entry.1, type.value.encode entry.2))), h.nextCollection)

def set (h : Heap) (ref : CollectionRef) (key : Key) (value : Value) : Heap :=
  letI := type.keyEq
  match type.entries h ref with
  | none => h
  | some values => h.replaceCollection ref
      (.dictionary type.keyName type.valueName
        ((OrderedEntries.set values key value).map fun entry =>
          (type.key.encode entry.1, type.value.encode entry.2)))

def erase (h : Heap) (ref : CollectionRef) (key : Key) : Heap :=
  letI := type.keyEq
  match type.entries h ref with
  | none => h
  | some values => h.replaceCollection ref
      (.dictionary type.keyName type.valueName
        ((OrderedEntries.erase values key).map fun entry =>
          (type.key.encode entry.1, type.value.encode entry.2)))

def copy (h : Heap) (ref : CollectionRef) : Heap × CollectionRef :=
  (h.allocateCollection (.dictionary type.keyName type.valueName
    (((type.entries h ref).getD []).map fun entry =>
      (type.key.encode entry.1, type.value.encode entry.2))), h.nextCollection)

theorem entries_facts (h : Heap) (ref : CollectionRef) (values : List (Key × Value))
    (observed : type.entries h ref = some values) :
    ref < h.nextCollection ∧ h.collectionType ref = some (.dictionary type.keyName type.valueName) ∧ (values.map Prod.fst).Nodup := by
  letI := type.keyEq
  unfold entries at observed
  split at observed
  · rename_i allocated
    cases found : h.collections ref with
    | none => simp [found] at observed
    | some collection =>
      cases collection with
      | sequence name payload => simp [found] at observed
      | set name payload => simp [found] at observed
      | dictionary keyName valueName payload =>
        simp only [found] at observed
        split at observed
        · rename_i header
          cases decoded : type.key.decodeEntries type.value payload with
          | none => simp [decoded] at observed
          | some xs =>
            rw [decoded] at observed
            change (if (xs.map Prod.fst).Nodup then some xs else none) = some values at observed
            split at observed
            · simp_all [Heap.collectionType, Collection.header]
            · simp_all
        · simp_all
  · simp_all

theorem entries_of_payload (h : Heap) (ref : CollectionRef) (values : List (Key × Value))
    (allocated : ref < h.nextCollection) (unique : (values.map Prod.fst).Nodup)
    (payload : h.collections ref = some (.dictionary type.keyName type.valueName (values.map fun entry => (type.key.encode entry.1, type.value.encode entry.2)))) :
    type.entries h ref = some values := by
  simp [entries, allocated, payload, unique]

@[simp] theorem entries_create (h : Heap) (values : List (Key × Value)) :
    type.entries (type.create h values).1 (type.create h values).2 =
      some (@OrderedEntries.normalize Key Value type.keyEq values) := by
  apply type.entries_of_payload
  · exact Nat.lt_succ_self _
  · exact @OrderedEntries.nodup_normalize Key Value type.keyEq values
  · simp [create]

@[simp] theorem valid_create (h : Heap) (values : List (Key × Value)) :
    type.valid (type.create h values).1 (type.create h values).2 := by
  simp [valid]

theorem entries_set (h : Heap) (ref : CollectionRef) (values : List (Key × Value)) (key : Key) (value : Value)
    (observed : type.entries h ref = some values) :
    type.entries (type.set h ref key value) ref =
      some (@OrderedEntries.set Key Value type.keyEq values key value) := by
  have facts := type.entries_facts h ref values observed
  simp only [set, observed]
  apply type.entries_of_payload
  · exact facts.1
  · exact @OrderedEntries.nodup_set Key Value type.keyEq values key value facts.2.2
  · exact Heap.collections_replaceCollection_same _ _ _ facts.2.1

theorem entries_erase (h : Heap) (ref : CollectionRef) (values : List (Key × Value)) (key : Key)
    (observed : type.entries h ref = some values) :
    type.entries (type.erase h ref key) ref =
      some (@OrderedEntries.erase Key Value type.keyEq values key) := by
  have facts := type.entries_facts h ref values observed
  simp only [erase, observed]
  apply type.entries_of_payload
  · exact facts.1
  · exact @OrderedEntries.nodup_erase Key Value type.keyEq values key facts.2.2
  · exact Heap.collections_replaceCollection_same _ _ _ facts.2.1

theorem valid_set (h : Heap) (ref : CollectionRef) (key : Key) (value : Value)
    (present : type.valid h ref) : type.valid (type.set h ref key value) ref := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values => simp [valid, type.entries_set h ref values key value observed]

theorem valid_erase (h : Heap) (ref : CollectionRef) (key : Key)
    (present : type.valid h ref) : type.valid (type.erase h ref key) ref := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values => simp [valid, type.entries_erase h ref values key observed]

@[simp] theorem get_set_same (h : Heap) (ref : CollectionRef) (key : Key) (value : Value)
    (present : type.valid h ref) : type.get (type.set h ref key value) ref key = some value := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values => simp [get, type.entries_set h ref values key value observed]

theorem get_set_other (h : Heap) (ref : CollectionRef) (key other : Key) (value : Value)
    (different : other ≠ key) (present : type.valid h ref) :
    type.get (type.set h ref key value) ref other = type.get h ref other := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values => simp [get, type.entries_set h ref values key value observed, observed, different]

@[simp] theorem get_erase_same (h : Heap) (ref : CollectionRef) (key : Key)
    (present : type.valid h ref) : type.get (type.erase h ref key) ref key = none := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values => simp [get, type.entries_erase h ref values key observed]

theorem get_erase_other (h : Heap) (ref : CollectionRef) (key other : Key)
    (different : other ≠ key) (present : type.valid h ref) :
    type.get (type.erase h ref key) ref other = type.get h ref other := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values => simp [get, type.entries_erase h ref values key observed, observed, different]

@[simp] theorem contains_set_same (h : Heap) (ref : CollectionRef) (key : Key) (value : Value)
    (present : type.valid h ref) : type.contains (type.set h ref key value) ref key = true := by
  simp [contains, type.get_set_same h ref key value present]

@[simp] theorem contains_erase_same (h : Heap) (ref : CollectionRef) (key : Key)
    (present : type.valid h ref) : type.contains (type.erase h ref key) ref key = false := by
  simp [contains, type.get_erase_same h ref key present]

/-- Membership refers to the captured key sequence, including for nullable values. -/
theorem contains_eq_true_iff (h : Heap) (ref : CollectionRef) (key : Key) :
    type.contains h ref key = true ↔ key ∈ type.keys h ref := by
  cases observed : type.entries h ref <;> simp [contains, get, keys, observed]



@[simp] theorem keys_nodup (h : Heap) (ref : CollectionRef) : (type.keys h ref).Nodup := by
  cases observed : type.entries h ref with
  | none => simp [keys, observed]
  | some values => simpa [keys, observed] using (type.entries_facts h ref values observed).2.2

@[simp] theorem entries_copy (h : Heap) (ref : CollectionRef) :
    type.entries (type.copy h ref).1 (type.copy h ref).2 = some ((type.entries h ref).getD []) := by
  apply type.entries_of_payload
  · exact Nat.lt_succ_self _
  · exact type.keys_nodup h ref
  · simp [copy]

@[simp] theorem valid_copy (h : Heap) (ref : CollectionRef) :
    type.valid (type.copy h ref).1 (type.copy h ref).2 := by simp [valid]

@[simp] theorem get_copy (h : Heap) (ref : CollectionRef) (key : Key) :
    type.get (type.copy h ref).1 (type.copy h ref).2 key = type.get h ref key := by
  cases observed : type.entries h ref <;> simp [get, observed, OrderedEntries.get]

@[simp] theorem keys_copy (h : Heap) (ref : CollectionRef) :
    type.keys (type.copy h ref).1 (type.copy h ref).2 = type.keys h ref := by simp [keys]

theorem copy_fresh (h : Heap) (ref : CollectionRef) (present : type.valid h ref) :
    (type.copy h ref).2 ≠ ref := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values =>
    exact (Nat.ne_of_lt (type.entries_facts h ref values observed).1).symm

@[simp] theorem create_clocks (h : Heap) (values : List (Key × Value)) :
    (type.create h values).1.clocks = h.clocks := rfl

@[simp] theorem copy_clocks (h : Heap) (ref : CollectionRef) :
    (type.copy h ref).1.clocks = h.clocks := rfl

@[simp] theorem set_clocks (h : Heap) (ref : CollectionRef) (key : Key) (value : Value) :
    (type.set h ref key value).clocks = h.clocks := by
  cases observed : type.entries h ref <;> simp [set, observed, Heap.replaceCollection]

@[simp] theorem erase_clocks (h : Heap) (ref : CollectionRef) (key : Key) :
    (type.erase h ref key).clocks = h.clocks := by
  cases observed : type.entries h ref <;> simp [erase, observed, Heap.replaceCollection]


/-- A present key keeps its position when its value changes. -/
theorem keys_set (h : Heap) (ref : CollectionRef) (key : Key) (value : Value)
    (present : type.valid h ref) : type.keys (type.set h ref key value) ref =
      if type.contains h ref key then type.keys h ref else type.keys h ref ++ [key] := by
  cases observed : type.entries h ref with
  | none => simp [valid, observed] at present
  | some values =>
    by_cases member : key ∈ values.map Prod.fst <;>
      simp [keys, type.entries_set h ref values key value observed, observed, contains, get,
        OrderedEntries.keys_set, member]

theorem size_set (h : Heap) (ref : CollectionRef) (key : Key) (value : Value)
    (present : type.valid h ref) : type.size (type.set h ref key value) ref =
      type.size h ref + if type.contains h ref key then 0 else 1 := by
  simp only [size, type.keys_set h ref key value present]
  split <;> simp

end DictType
end Algo2LeanGenerated
