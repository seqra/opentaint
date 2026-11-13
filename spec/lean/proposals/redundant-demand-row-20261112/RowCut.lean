import RetainedServiceBasis

namespace RetainedDemandRowCut
open RetainedServiceBasis
open AncestorMayPointQuery (Template Request NativeQuery iterate)

-- Rows are the native post-handoff memberships. Origins play no role here.
-- In particular, a second origin for a removed row is not a retained witness.
def checkRow (counted : Nat → Bool) (x : Row) (kept : List Row) : Bool :=
  kept.any (c2Check x) && kept.any (c5Check counted x)

def checkCut (counted : Nat → Bool) (before kept : List Row) : Bool :=
  kept.all (fun r => before.contains r) && before.all (fun r => checkRow counted r kept)

def singletonKept (before : List Row) (x : Row) : List Row :=
  before.filter (fun r => r != x)

theorem singleton_removes_all_producers (before : List Row) (x : Row) :
    x ∉ singletonKept before x := by
  simp [singletonKept]

def oracle {Query Answer : Type} (respond : Row → Query → List Answer)
    (rows : List Row) (common : Query → Answer → Prop) (q : Query) (answer : Answer) : Prop :=
  common q answer ∨ ∃ r ∈ rows, answer ∈ respond r q

theorem checked_row_witnesses (counted : Nat → Bool) (x : Row) (kept : List Row)
    (h : checkRow counted x kept = true) :
    ∃ z ∈ kept, ∃ y ∈ kept, c2Check x z = true ∧ c5Check counted x y = true := by
  simp only [checkRow, Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨z,hz,zc⟩ := h.1
  obtain ⟨y,hy,yc⟩ := h.2
  exact ⟨z,hz,y,hy,zc,yc⟩

theorem checked_cut_subset (counted : Nat → Bool) (before kept : List Row)
    (h : checkCut counted before kept = true) :
    ∀ r ∈ kept, r ∈ before := by
  simp only [checkCut, Bool.and_eq_true, List.all_eq_true] at h
  intro r hr
  exact List.contains_iff_mem.mp (h.1 r hr)

theorem checked_cut_row (counted : Nat → Bool) (before kept : List Row)
    (h : checkCut counted before kept = true) (r : Row) (hr : r ∈ before) :
    checkRow counted r kept = true := by
  simp only [checkCut, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 r hr

theorem checked_row_reply {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (x : Row) (kept : List Row) (checked : checkRow counted x kept = true)
    (q : NativeQuery Offer Raw) (answer : Atom Answer)
    (member : answer ∈ reply counted limit run emit other program x q) :
    ∃ r ∈ kept, answer ∈ reply counted limit run emit other program r q := by
  obtain ⟨z,hz,y,hy,zc,yc⟩ := checked_row_witnesses counted x kept checked
  rcases split_row_cover counted limit run late emit other program x z y zc yc q answer member with h | h
  · exact ⟨z,hz,h⟩
  · exact ⟨y,hy,h⟩

theorem checked_cut_oracle_equal {Offer Raw Answer : Type}
    (counted : Nat → Bool) (limit run : Nat) (late : 3 ≤ run)
    (emit : EntryKey → Offer → List Answer) (other : Input → List Template → Bool)
    (program : Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (before kept : List Row) (checked : checkCut counted before kept = true)
    (common : NativeQuery Offer Raw → Atom Answer → Prop) :
    oracle (reply counted limit run emit other program) before common =
      oracle (reply counted limit run emit other program) kept common := by
  funext q answer
  apply propext
  constructor
  · intro h
    rcases h with h | ⟨r,hr,ha⟩
    · exact Or.inl h
    · exact Or.inr (checked_row_reply counted limit run late emit other program r kept
        (checked_cut_row counted before kept checked r hr) q answer ha)
  · intro h
    rcases h with h | ⟨r,hr,ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨r,checked_cut_subset counted before kept checked r hr,ha⟩

def family {Offer Raw Answer : Type}
    (counted : Nat → Bool)
    (emit : Nat → Nat → EntryKey → Offer → List Answer)
    (other : Nat → Nat → Input → List Template → Bool)
    (program : Nat → Nat → Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (rows : List Row)
    (common : Nat → Nat → NativeQuery Offer Raw → Atom Answer → Prop) :
    (run : Nat) → 3 ≤ run → Nat → NativeQuery Offer Raw → Atom Answer → Prop :=
  fun run _ limit => oracle (reply counted limit run (emit run limit)
      (other run limit) (program run limit)) rows (common run limit)

theorem checked_all_runs_and_limits {Offer Raw Answer : Type}
    (counted : Nat → Bool)
    (emit : Nat → Nat → EntryKey → Offer → List Answer)
    (other : Nat → Nat → Input → List Template → Bool)
    (program : Nat → Nat → Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (before kept : List Row) (checked : checkCut counted before kept = true)
    (common : Nat → Nat → NativeQuery Offer Raw → Atom Answer → Prop) :
    family counted emit other program before common = family counted emit other program kept common := by
  funext run late limit
  exact checked_cut_oracle_equal counted limit run late (emit run limit) (other run limit)
    (program run limit) before kept checked (common run limit)

theorem checked_unbounded_continuation {Offer Raw Answer State : Type}
    (counted : Nat → Bool)
    (emit : Nat → Nat → EntryKey → Offer → List Answer)
    (other : Nat → Nat → Input → List Template → Bool)
    (program : Nat → Nat → Nat → Nat → ExitKind → Nat → List Template → Raw → List Answer)
    (before kept : List Row) (checked : checkCut counted before kept = true)
    (common : Nat → Nat → NativeQuery Offer Raw → Atom Answer → Prop)
    (step : ((run : Nat) → 3 ≤ run → Nat → NativeQuery Offer Raw → Atom Answer → Prop) → State → State)
    (n : Nat) (initial : State) :
    iterate step (family counted emit other program before common) n initial =
      iterate step (family counted emit other program kept common) n initial := by
  rw [checked_all_runs_and_limits counted emit other program before kept checked common]

theorem removed_row_is_not_a_witness (counted : Nat → Bool) (before kept : List Row)
    (checked : checkCut counted before kept = true) (x : Row)
    (original : x ∈ before) (removed : x ∉ kept) :
    ∃ z ∈ kept, ∃ y ∈ kept, z ≠ x ∧ y ≠ x ∧
      c2Check x z = true ∧ c5Check counted x y = true := by
  obtain ⟨z,hz,y,hy,zc,yc⟩ := checked_row_witnesses counted x kept
    (checked_cut_row counted before kept checked x original)
  refine ⟨z,hz,y,hy,?_,?_,zc,yc⟩
  · intro h; subst z; exact removed hz
  · intro h; subst y; exact removed hy

#print axioms checked_row_witnesses
#print axioms singleton_removes_all_producers
#print axioms checked_cut_subset
#print axioms checked_cut_row
#print axioms checked_row_reply
#print axioms checked_cut_oracle_equal
#print axioms checked_all_runs_and_limits
#print axioms checked_unbounded_continuation
#print axioms removed_row_is_not_a_witness
end RetainedDemandRowCut
