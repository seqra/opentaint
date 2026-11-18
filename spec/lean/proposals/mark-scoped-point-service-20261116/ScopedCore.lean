import UnadmittedReturn
import CompleteClosure
namespace ScopedCore
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
abbrev Edge := Ap × Value

def eligible (q : Seed) : Bool := q.ap.tail == .exact && !q.demand &&
  q.ap.mark.isSome && q.ap.e.isEmpty && q.ap.mx.isEmpty

def normal (c : Value) : Bool := !c.demand && !c.h

def covered (current : List Edge) (q : Seed) (c : Value) : Bool :=
  current.any (fun e => decide (e.1=q.ap ∧ e.2=c))

def whole (current : List Edge) (q : Seed) (raw : List Value) : Bool :=
  eligible q && raw.all (fun c => normal c && covered current q c)

def focus (raw : List Value) (mark : Nat) : List Value :=
  raw.filter (fun c => c.ap.mark == some mark)

/-- The NORMAL closure is shared across all marks. Only TERMINAL service
    coverage is projected. The nonempty guard avoids new negative cells. -/
def completeFor (current : List Edge) (q : Seed) (raw : List Value) (mark : Nat) : Bool :=
  eligible q && raw.all normal && !(focus raw mark).isEmpty &&
    (focus raw mark).all (covered current q)

/-- Sparse output classes already present in admitted NORMAL service. -/
def existingMarks (current : List Edge) (q : Seed) : List Nat :=
  (current.filterMap fun e => if e.1 == q.ap && normal e.2 then e.2.ap.mark else none).eraseDups

def extra (current : List Edge) (q : Seed) (raw : List Value) : List Nat :=
  if whole current q raw then [] else
    (existingMarks current q).filter (completeFor current q raw)

theorem whole_is_the_previous_complete_check (current : List Edge) (q : Seed) :
    whole current q (UnadmittedReturn.colors.flatMap fun m => UnadmittedReturn.gen m q)=
      UnadmittedReturn.completePoint current q := rfl

theorem completeFor_has_full_same_mark_coverage (current : List Edge) (q : Seed)
    (raw : List Value) (mark : Nat) (ok : completeFor current q raw mark=true)
    (c : Value) (member : c ∈ raw) (same : c.ap.mark=some mark) :
    normal c=true ∧ covered current q c=true := by
  have h := ok
  simp only [completeFor,Bool.and_eq_true] at h
  have inFocus : c ∈ focus raw mark := List.mem_filter.mpr ⟨member,by simp [same]⟩
  exact ⟨List.all_eq_true.mp h.1.1.2 c member,List.all_eq_true.mp h.2 c inFocus⟩

theorem output_cell_has_an_existing_NORMAL_group (current : List Edge) (q : Seed)
    (raw : List Value) (m : Nat) (inside : m ∈ extra current q raw) :
    m ∈ existingMarks current q := by
  unfold extra at inside
  split at inside
  · cases inside
  · exact (List.mem_filter.mp inside).1

theorem no_more_cells_than_existing_groups (current : List Edge) (q : Seed) (raw : List Value) :
    (extra current q raw).length≤(existingMarks current q).length := by
  unfold extra
  split
  · simp
  · exact List.length_filter_le _ _

/-- Homogeneous old bodies get no extension: projection either proves the
    old whole certificate or still fails. This is independent of arrival order. -/
theorem homogeneous_projection_implies_whole (current : List Edge) (q : Seed)
    (raw : List Value) (mark : Nat) (same : ∀ c ∈ raw,c.ap.mark=some mark)
    (ok : completeFor current q raw mark=true) : whole current q raw=true := by
  have h := ok
  simp only [completeFor,Bool.and_eq_true] at h
  unfold whole
  simp only [Bool.and_eq_true]
  refine ⟨h.1.1.1,List.all_eq_true.mpr ?_⟩
  intro c hc
  have covered := completeFor_has_full_same_mark_coverage current q raw mark ok c hc (same c hc)
  simpa only [Bool.and_eq_true] using covered

-- R is NOT projected. Every internal state remains in the closed NORMAL set.
def focusedReturn {α : Type} (returned selected : α → Bool) (s : α) := returned s && selected s

theorem every_relevant_reachable_return_has_NORMAL_service
    {α : Type} [DecidableEq α] (next : α → List α) (seeds owned service : List α)
    (returned selected : α → Bool) (covers : α → α → Bool)
    (ok : CompleteClosure.check next seeds owned (focusedReturn returned selected)
      (CompleteClosure.hasWitness service covers)=true)
    (s : α) (reached : CompleteClosure.Reach next seeds s)
    (exit : returned s=true) (relevant : selected s=true) :
    ∃ n ∈ service,covers n s=true := by
  apply CompleteClosure.a_concrete_normal_service_witness next seeds owned service
    (focusedReturn returned selected) covers ok s reached
  simp [focusedReturn,exit,relevant]

theorem arbitrary_continuation_observation_is_preserved_for_the_selected_return
    {α : Type} [DecidableEq α] (next : α → List α) (seeds owned service : List α)
    (returned selected : α → Bool) (covers : α → α → Bool) (observe : α → Prop)
    (ok : CompleteClosure.check next seeds owned (focusedReturn returned selected)
      (CompleteClosure.hasWitness service covers)=true)
    (native : ∀ n ∈ service,∀ s,covers n s=true → observe s → observe n)
    (s : α) (reached : CompleteClosure.Reach next seeds s)
    (exit : returned s=true) (relevant : selected s=true) (seen : observe s) :
    ∃ n ∈ service,observe n := by
  apply CompleteClosure.caller_observation_is_preserved next seeds owned service
    (focusedReturn returned selected) covers observe ok native s reached _ seen
  simp [focusedReturn,exit,relevant]

-- An internal V state can lead to U. It cannot be erased from NORMAL closure.
def internal (n : Nat) : List Nat := if n==0 then [1] else if n==1 then [2] else []
theorem internal_other_mark_must_still_be_analyzed :
    CompleteClosure.check internal [0] [0,2] (fun n => n==2) (fun _ => true)=false := by decide

theorem missing_U_after_internal_V_is_rejected :
    CompleteClosure.check internal [0] [0,1,2] (fun n => n==2) (fun _ => false)=false := by decide

theorem complete_U_after_internal_V_is_accepted :
    CompleteClosure.check internal [0] [0,1,2] (fun n => n==2) (fun _ => true)=true := by decide

theorem homogeneous_query_gets_no_extra_cells (current : List Edge) (q : Seed)
    (raw : List Value) (fixed : Nat) (same : ∀ c ∈ raw,c.ap.mark=some fixed) :
    extra current q raw=[] := by
  unfold extra
  split
  · rfl
  · rename_i notWhole
    have never (mark : Nat) : completeFor current q raw mark=false := by
      cases hit : completeFor current q raw mark
      · rfl
      · have all := hit
        simp only [completeFor,Bool.and_eq_true] at all
        have nonempty : focus raw mark ≠ [] := by simpa using all.1.2
        rcases List.exists_mem_of_ne_nil _ nonempty with ⟨c,inside⟩
        have hn := List.mem_filter.mp inside
        have mk : c.ap.mark=some mark := by simpa using hn.2
        have equal : mark=fixed := Option.some.inj (mk.symm.trans (same c hn.1))
        subst mark
        have yes := homogeneous_projection_implies_whole current q raw fixed same hit
        exact False.elim (notWhole yes)
    have filterEmpty (xs : List Nat) : xs.filter (completeFor current q raw)=[] := by
      induction xs with
      | nil => rfl
      | cons mark rest ih => simp only [List.filter_cons,never mark,Bool.false_eq_true,ite_false,ih]
    exact filterEmpty _

-- One shared sparse failure set replaces an all-return scan per output mark.
def badMarks (current : List Edge) (q : Seed) (raw : List Value) : List Nat :=
  raw.filterMap fun c => if covered current q c then none else c.ap.mark

theorem bad_membership (current : List Edge) (q : Seed) (raw : List Value) (mark : Nat) :
    mark ∈ badMarks current q raw ↔
      ∃ c ∈ raw,c.ap.mark=some mark ∧ covered current q c=false := by
  simp only [badMarks,List.mem_filterMap]
  constructor
  · rintro ⟨c,hc,found⟩
    cases ok : covered current q c
    · simp only [ok,Bool.false_eq_true,ite_false] at found
      exact ⟨c,hc,found,ok⟩
    · simp [ok] at found
  · rintro ⟨c,hc,same,notCovered⟩
    exact ⟨c,hc,by simp [notCovered,same]⟩

theorem grouped_failure_check_equals_projected_scan (current : List Edge) (q : Seed)
    (raw : List Value) (mark : Nat) :
    mark ∉ badMarks current q raw ↔ (focus raw mark).all (covered current q)=true := by
  constructor
  · intro absent
    apply List.all_eq_true.mpr
    intro c hc
    have h := List.mem_filter.mp hc
    have same : c.ap.mark=some mark := by simpa using h.2
    cases ok : covered current q c
    · exact False.elim (absent ((bad_membership current q raw mark).mpr ⟨c,h.1,same,ok⟩))
    · decide
  · intro all present
    rcases (bad_membership current q raw mark).mp present with ⟨c,hc,same,bad⟩
    have yes := List.all_eq_true.mp all c (List.mem_filter.mpr ⟨hc,by simp [same]⟩)
    rw [bad] at yes
    contradiction

def presentMarks (raw : List Value) : List Nat := raw.filterMap (fun c => c.ap.mark)

theorem present_membership_equals_nonempty_focus (raw : List Value) (mark : Nat) :
    (presentMarks raw).contains mark=!(focus raw mark).isEmpty := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true',List.contains_iff_mem,List.isEmpty_eq_false_iff]
  constructor
  · intro inside
    rcases List.mem_filterMap.mp inside with ⟨c,hc,same⟩
    have hit : c ∈ focus raw mark := List.mem_filter.mpr ⟨hc,by simp [same]⟩
    intro empty
    rw [empty] at hit
    cases hit
  · intro nonempty
    rcases List.exists_mem_of_ne_nil _ nonempty with ⟨c,hc⟩
    have h := List.mem_filter.mp hc
    exact List.mem_filterMap.mpr ⟨c,h.1,by simpa using h.2⟩

theorem failure_membership_equals_projected_coverage (current : List Edge) (q : Seed)
    (raw : List Value) (mark : Nat) :
    (!(badMarks current q raw).contains mark) = (focus raw mark).all (covered current q) := by
  apply Bool.eq_iff_iff.mpr
  simpa using grouped_failure_check_equals_projected_scan current q raw mark

def completeFast (current : List Edge) (q : Seed) (raw : List Value) (mark : Nat) : Bool :=
  eligible q && raw.all normal && (presentMarks raw).contains mark &&
    !(badMarks current q raw).contains mark

theorem grouped_complete_check_equals_the_reference (current : List Edge) (q : Seed)
    (raw : List Value) (mark : Nat) : completeFast current q raw mark=completeFor current q raw mark := by
  simp only [completeFast,completeFor,present_membership_equals_nonempty_focus,
    failure_membership_equals_projected_coverage]

end ScopedCore
