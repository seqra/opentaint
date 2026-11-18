import Std

/-! The executable batching and deletion kernel. Completeness of the
native use list is a separate obligation of each certificate extractor. -/
namespace TerminationRollback

structure Pair where
  entry : Nat
  selector : Nat
  cap : Nat
  deriving DecidableEq

def scalarC5 (rows : List Pair) (entry : Nat → Bool)
    (select : Nat → Nat → List Nat) : List Nat :=
  rows.flatMap fun r => if entry r.entry then select r.selector r.cap else []

def groupedC5 (rows : List Pair) (entry : Nat → Bool)
    (select : Nat → Nat → List Nat) : List Nat :=
  (rows.map Pair.entry).eraseDups.flatMap fun key =>
    if entry key then
      ((rows.filter fun r => r.entry == key).map fun r => (r.selector, r.cap)).eraseDups.flatMap
        fun (s, k) => select s k
    else []

theorem groupedC5_eq (rows : List Pair) (entry : Nat → Bool)
    (select : Nat → Nat → List Nat) (x : Nat) :
    x ∈ groupedC5 rows entry select ↔ x ∈ scalarC5 rows entry select := by
  unfold groupedC5 scalarC5
  constructor
  · intro h
    obtain ⟨key, _, found⟩ := List.mem_flatMap.mp h
    cases hk : entry key with
    | false =>
      have impossible (h : entry key = true) : False := Bool.false_eq_true.mp (hk.symm.trans h)
      rw [if_neg impossible] at found
      exact False.elim (List.not_mem_nil found)
    | true =>
      rw [if_pos hk] at found
      obtain ⟨sel, hsel, selected⟩ := List.mem_flatMap.mp found
      obtain ⟨r, filtered, eql⟩ := List.mem_map.mp (List.mem_eraseDups.mp hsel)
      have hr := List.mem_filter.mp filtered
      have he : r.entry = key := beq_iff_eq.mp hr.2
      apply List.mem_flatMap.mpr
      refine ⟨r, hr.1, ?_⟩
      rw [he, if_pos hk]
      rw [← eql] at selected
      exact selected
  · intro h
    obtain ⟨r, hr, found⟩ := List.mem_flatMap.mp h
    cases hk : entry r.entry with
    | false =>
      have impossible (h : entry r.entry = true) : False := Bool.false_eq_true.mp (hk.symm.trans h)
      rw [if_neg impossible] at found
      exact False.elim (List.not_mem_nil found)
    | true =>
      rw [if_pos hk] at found
      apply List.mem_flatMap.mpr
      refine ⟨r.entry, List.mem_eraseDups.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩), ?_⟩
      rw [if_pos hk]
      apply List.mem_flatMap.mpr
      refine ⟨(r.selector, r.cap), ?_, found⟩
      exact List.mem_eraseDups.mpr (List.mem_map.mpr
        ⟨r, List.mem_filter.mpr ⟨hr, beq_iff_eq.mpr rfl⟩, rfl⟩)

def effects (postings : List Nat) (apply : Nat → List Nat) :=
  postings.flatMap apply

theorem shareEffectiveApplication (postings : List Nat) (apply : Nat → List Nat) (x : Nat) :
    x ∈ effects postings.eraseDups apply ↔ x ∈ effects postings apply := by
  simp [effects, List.mem_flatMap]

structure Origin where
  action : Nat
  mark : Nat
  binding : Nat
  observer : Nat
  deriving DecidableEq

def mayRetire (complete : Bool) (quota : Nat)
    (uses normal impossible : List Origin) : Bool :=
  complete && decide (uses.length ≤ quota) &&
    uses.all fun o => decide (o ∈ normal ∨ o ∈ impossible)

/-- The extractor supplies all uses and a constructive impossibility proof
for each rejected origin. A successful check returns an actual saved origin. -/
theorem retired_live_has_provider
    (accepted : mayRetire complete quota uses normal impossible = true)
    (represented : o ∈ uses) (possible : o ∉ impossible) : o ∈ normal := by
  have checks := (Bool.and_eq_true_iff.mp accepted).2
  have witnessed := of_decide_eq_true (List.all_eq_true.mp checks o represented)
  exact witnessed.resolve_right possible

theorem exhausted_keeps_guidance (h : quota < uses.length) :
    mayRetire complete quota uses normal impossible = false := by
  simp [mayRetire, Nat.not_le_of_lt h]

def first : Origin := ⟨1, 2, 3, 4⟩
def sameReportOtherBinding : Origin := ⟨5, 2, 6, 4⟩
def differentReport : Origin := ⟨1, 2, 3, 7⟩

theorem report_identity_does_not_discharge_other_binding :
    mayRetire true 2 [first,sameReportOtherBinding] [first] [] = false := by decide

theorem covered_other_report_needed :
    mayRetire true 2 [first,differentReport] [first] [] = false := by decide

theorem all_observers_covered :
    mayRetire true 2 [first,differentReport] [first,differentReport] [] = true := by decide

#print axioms groupedC5_eq
#print axioms shareEffectiveApplication
#print axioms retired_live_has_provider
#print axioms exhausted_keeps_guidance
#print axioms report_identity_does_not_discharge_other_binding
#print axioms covered_other_report_needed
#print axioms all_observers_covered

end TerminationRollback
