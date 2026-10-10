/-
  Destination lookup for a normal TAINT group after subsumption.

  Each row has one shared must-tail exclusion. Exact leaves do not read it.
  Removing the last must leaf normalizes the row's exclusion to empty. The
  destination lookup must use this normalized remainder, not the input key.

  This model checks that local lookup and merge step. It does not model T2's
  equal-content exclusion intersection, trie sharing, or the full store delta.
-/
import ApSpec.AnyTaintExDefs

namespace ApSpec.CurrentTaintGroupKeys
open ApSpec

structure Cell where
  path : List Acc
  mark : Mark
  must : Bool
  deriving DecidableEq, Repr

structure Row where
  exclusion : Excl
  cells : List Cell
  deriving DecidableEq, Repr

/-- The normal TAINT factory drops E when the row has no must leaf. -/
def normalize (r : Row) : Row :=
  if r.cells.any (·.must) then r else ⟨.empty, r.cells⟩

/-- A nonempty exclusion belongs only to a row that still has a must leaf. -/
def RowCanonical (r : Row) : Prop :=
  r.exclusion = .empty ∨ r.cells.any (·.must) = true

def Canonical (rows : List Row) : Prop := ∀ row ∈ rows, RowCanonical row

theorem normalize_canonical (r : Row) : RowCanonical (normalize r) := by
  cases hasAny : r.cells.any (·.must) <;> simp [normalize, hasAny, RowCanonical]

theorem canonical_normalize (r : Row) (canonical : RowCanonical r) : normalize r = r := by
  rcases canonical with empty | hasAny
  · cases r with
    | mk exclusion cells =>
      dsimp only at empty
      subst exclusion
      cases h : cells.any (·.must) <;> simp [normalize, h]
  · simp [normalize, hasAny]

/-- Same-key merge keeps the destination key under the actual factory's normalization. -/
theorem merge_canonical (row remainder : Row) (canonical : RowCanonical row) :
    RowCanonical ⟨row.exclusion, row.cells ++ remainder.cells⟩ := by
  rcases canonical with empty | hasAny
  · exact Or.inl empty
  · exact Or.inr (by simp [List.any_append, hasAny])

theorem merge_normalize (row remainder : Row) (canonical : RowCanonical row) :
    normalize ⟨row.exclusion, row.cells ++ remainder.cells⟩ =
      ⟨row.exclusion, row.cells ++ remainder.cells⟩ :=
  canonical_normalize _ (merge_canonical row remainder canonical)

/-- Local normal-layer subsumption: a must leaf never removes an exact leaf. -/
def cellSubsumes (stored : Row) (s : Cell) (incoming : Row) (c : Cell) : Bool :=
  if s.mark != c.mark then false
  else if c.must then
    if !s.must then false
    else match relate s.path c.path with
      | .below [] => stored.exclusion.subB incoming.exclusion
      | .below suffix => stored.exclusion.admits suffix
      | _ => false
  else !s.must && s.path == c.path

/-- Subtraction computes the remainder, then applies the TAINT factory's key rule. -/
def subtract (rows : List Row) (incoming : Row) : Row :=
  normalize ⟨incoming.exclusion, incoming.cells.filter fun c =>
    !rows.any (fun stored => stored.cells.any fun s => cellSubsumes stored s incoming c)⟩

/-- Merge into the remainder's actual key, or append if that key is absent. -/
def place (remainder : Row) : List Row → List Row
  | [] => [remainder]
  | row :: rows =>
    if remainder.exclusion = row.exclusion then
      ⟨row.exclusion, row.cells ++ remainder.cells⟩ :: rows
    else row :: place remainder rows

/-- The repaired insertion after the unchanged subtraction operation. -/
def insert (rows : List Row) (incoming : Row) : List Row :=
  place (subtract rows incoming) rows

/-- The faulty absent-original-key branch appends the normalized remainder. -/
def staleInsert (rows : List Row) (incoming : Row) : List Row :=
  if rows.any (fun row => row.exclusion == incoming.exclusion) then
    place (subtract rows incoming) rows
  else rows ++ [subtract rows incoming]

/-- A group has at most one row for each exclusion key. -/
def UniqueKeys (rows : List Row) : Prop := (rows.map (·.exclusion)).Nodup

instance (rows : List Row) : Decidable (UniqueKeys rows) :=
  inferInstanceAs (Decidable (rows.map (·.exclusion)).Nodup)

/-- No key is introduced except the remainder's own normalized key. -/
theorem place_key_mem (remainder : Row) (rows : List Row) (key : Excl) :
    key ∈ (place remainder rows).map (·.exclusion) ↔
    key = remainder.exclusion ∨ key ∈ rows.map (·.exclusion) := by
  induction rows with
  | nil => simp [place]
  | cons row rows ih =>
    by_cases same : remainder.exclusion = row.exclusion
    · simp only [place, same, if_true, List.map_cons, List.mem_cons]
      simp only [or_self_left]
    · simp only [place, same, if_false, List.map_cons, List.mem_cons, ih]
      constructor
      · intro h
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · intro h
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- Destination lookup preserves the one-row-per-exclusion invariant. -/
theorem place_unique (remainder : Row) (rows : List Row)
    (unique : UniqueKeys rows) : UniqueKeys (place remainder rows) := by
  induction rows with
  | nil => simp [UniqueKeys, place]
  | cons row rows ih =>
    have old := List.nodup_cons.mp unique
    by_cases same : remainder.exclusion = row.exclusion
    · simpa [UniqueKeys, place, same] using unique
    · simp only [UniqueKeys, place, same, if_false, List.map_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_, ih old.2⟩
      intro present
      rcases (place_key_mem remainder rows row.exclusion).mp present with h | h
      · exact same h.symm
      · exact old.1 h

/-- The local group stays canonical; merging does not cause another key change. -/
theorem place_canonical (remainder : Row) (rows : List Row)
    (newCanonical : RowCanonical remainder) (oldCanonical : Canonical rows) :
    Canonical (place remainder rows) := by
  induction rows with
  | nil =>
    intro row member
    have same : row = remainder := by simpa [place] using member
    exact same ▸ newCanonical
  | cons row rows ih =>
    have headCanonical := oldCanonical row List.mem_cons_self
    have tailCanonical : Canonical rows := fun r hr => oldCanonical r (List.mem_cons_of_mem _ hr)
    intro r hr
    by_cases same : remainder.exclusion = row.exclusion
    · simp only [place, same, if_true, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact merge_canonical _ _ headCanonical
      · exact tailCanonical _ hr
    · simp only [place, same, if_false, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact headCanonical
      · exact ih tailCanonical _ hr

theorem insert_canonical (rows : List Row) (incoming : Row)
    (canonical : Canonical rows) : Canonical (insert rows incoming) :=
  place_canonical _ _ (normalize_canonical _) canonical

/-- The repaired local insertion works for every subtraction result. -/
theorem insert_unique (rows : List Row) (incoming : Row)
    (unique : UniqueKeys rows) : UniqueKeys (insert rows incoming) :=
  place_unique _ _ unique

/-- Read one annotated cell of the local group. -/
def values (rows : List Row) : List (Excl × Cell) :=
  rows.flatMap fun row => row.cells.map fun cell => (row.exclusion, cell)

def Reads (rows : List Row) (key : Excl) (cell : Cell) : Prop :=
  (key, cell) ∈ values rows

instance (rows : List Row) (key : Excl) (cell : Cell) : Decidable (Reads rows key cell) :=
  inferInstanceAs (Decidable ((key, cell) ∈ values rows))

theorem reads_cons (row : Row) (rows : List Row) (key : Excl) (cell : Cell) :
    Reads (row :: rows) key cell ↔
    (row.exclusion = key ∧ cell ∈ row.cells) ∨ Reads rows key cell := by
  have mapped : (key, cell) ∈ row.cells.map (fun c => (row.exclusion, c)) ↔
      row.exclusion = key ∧ cell ∈ row.cells := by
    constructor
    · intro h
      obtain ⟨c, hc, he⟩ := List.mem_map.mp h
      have sameCell : c = cell := congrArg Prod.snd he
      exact ⟨congrArg Prod.fst he, sameCell ▸ hc⟩
    · rintro ⟨hk, hc⟩
      exact List.mem_map.mpr ⟨cell, hc, by simp [hk]⟩
  change (key, cell) ∈ (row.cells.map (fun c => (row.exclusion, c))) ++ values rows ↔ _
  rw [List.mem_append, mapped]
  rfl

/-- Merging the remainder loses no annotated cell and adds no other one. -/
theorem place_reads (remainder : Row) (rows : List Row) (key : Excl) (cell : Cell) :
    Reads (place remainder rows) key cell ↔
    Reads rows key cell ∨ (remainder.exclusion = key ∧ cell ∈ remainder.cells) := by
  induction rows with
  | nil =>
    rw [place, reads_cons]
    simp [Reads, values]
  | cons row rows ih =>
    by_cases same : remainder.exclusion = row.exclusion
    · simp only [place, same, if_true, reads_cons]
      rw [List.mem_append]
      constructor
      · rintro (⟨hk, hc | hc⟩ | old)
        · exact Or.inl (Or.inl ⟨hk, hc⟩)
        · exact Or.inr ⟨hk, hc⟩
        · exact Or.inl (Or.inr old)
      · rintro ((⟨hk, hc⟩ | old) | ⟨hk, hc⟩)
        · exact Or.inl ⟨hk, Or.inl hc⟩
        · exact Or.inr old
        · exact Or.inl ⟨hk, Or.inr hc⟩
    · simp only [place, same, if_false, reads_cons, ih]
      exact or_assoc.symm

namespace Certificate

def mustRoot : Cell := ⟨[], 1, true⟩
def exactG : Cell := ⟨[2], 2, false⟩
def stored : Row := ⟨.empty, [mustRoot]⟩
def incoming : Row := ⟨.set [3], [mustRoot, exactG]⟩
def remainder : Row := subtract [stored] incoming

theorem key_changes : remainder = ⟨.empty, [exactG]⟩ := by decide

theorem old_duplicates_key :
    UniqueKeys [stored] ∧ ¬UniqueKeys (staleInsert [stored] incoming) := by decide

theorem repaired_value : insert [stored] incoming =
    [⟨.empty, [mustRoot, exactG]⟩] := by decide

/-- Actual computed failure and repaired group, with no chosen proposition witness. -/
def witness : { result : List Row × List Row //
    result = (staleInsert [stored] incoming, insert [stored] incoming) ∧
    ¬UniqueKeys result.1 ∧ UniqueKeys result.2 ∧
    Reads result.2 .empty mustRoot ∧ Reads result.2 .empty exactG } :=
  ⟨(staleInsert [stored] incoming, insert [stored] incoming), rfl,
    old_duplicates_key.2, insert_unique _ _ old_duplicates_key.1,
    by decide, by decide⟩

end Certificate

#eval Certificate.witness.val
#print axioms merge_normalize
#print axioms place_canonical
#print axioms place_unique
#print axioms place_reads
#print axioms Certificate.witness

end ApSpec.CurrentTaintGroupKeys
