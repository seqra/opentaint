import ProtectedReturn
import CompleteClosure
namespace LayerCore
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

-- H is independent of the propagation layer. Never erase it from a value.
def normalLayer (c : Value) : Bool := !c.demand
-- Actual plain service still requires H=0. This equals the older stricter predicate.
def plainService (c : Value) : Bool := normalLayer c && !c.h

def completeFor (current : List Edge) (q : Seed) (raw : List Value) (region : Ap) : Bool :=
  ScopedCore.eligible q && raw.all normalLayer &&
    (ReplyCore.focus raw region).all (fun c => plainService c && ScopedCore.covered current q c)

abbrev received := ReplyCore.received

theorem plain_service_is_the_previous_plain_predicate (c : Value) :
    plainService c=ScopedCore.normal c := rfl

theorem protected_NORMAL_is_a_NORMAL_closure_member (c : Value)
    (layer : c.demand=false) : normalLayer c=true := by simp [normalLayer,layer]

theorem selected_returns_require_plain_service (current : List Edge) (q : Seed)
    (raw : List Value) (region : Ap) (ok : completeFor current q raw region=true)
    (c : Value) (inside : c∈raw) (relevant : ReplyCore.overlaps c.ap region=true) :
    c.demand=false ∧ c.h=false ∧ ScopedCore.covered current q c=true := by
  have h := ok
  simp only [completeFor,Bool.and_eq_true] at h
  have yes := List.all_eq_true.mp h.2 c (List.mem_filter.mpr ⟨inside,relevant⟩)
  simp only [plainService,normalLayer,Bool.and_eq_true,Bool.not_eq_true'] at yes
  exact ⟨yes.1.1,yes.1.2,yes.2⟩

theorem a_relevant_protected_return_still_blocks_selection (current : List Edge) (q : Seed)
    (raw : List Value) (region : Ap) (c : Value) (inside : c∈raw)
    (relevant : ReplyCore.overlaps c.ap region=true) (flag : c.h=true) :
    completeFor current q raw region=false := by
  cases ok : completeFor current q raw region
  · rfl
  · have no := (selected_returns_require_plain_service current q raw region ok c inside relevant).2.1
    rw [flag] at no
    cases no

theorem every_old_certificate_remains_valid (current : List Edge) (q : Seed)
    (raw : List Value) (region : Ap) (old : ReplyCore.completeFor current q raw region=true) :
    completeFor current q raw region=true := by
  have h := old
  simp only [ReplyCore.completeFor,Bool.and_eq_true] at h
  simp only [completeFor,Bool.and_eq_true]
  refine ⟨⟨h.1.1,List.all_eq_true.mpr ?_⟩,List.all_eq_true.mpr ?_⟩
  · intro c hc
    have p := List.all_eq_true.mp h.1.2 c hc
    simp only [ScopedCore.normal,Bool.and_eq_true] at p
    exact p.1
  · intro c hc
    have all := List.all_eq_true.mp h.1.2 c (List.mem_filter.mp hc).1
    simp only [Bool.and_eq_true]
    exact ⟨all,List.all_eq_true.mp h.2 c hc⟩

theorem no_protected_returns_means_no_semantic_change (current : List Edge) (q : Seed)
    (raw : List Value) (region : Ap) (plain : ∀ c∈raw,c.h=false) :
    completeFor current q raw region=ReplyCore.completeFor current q raw region := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro ok
    have h := ok
    simp only [completeFor,Bool.and_eq_true] at h
    simp only [ReplyCore.completeFor,Bool.and_eq_true]
    refine ⟨⟨h.1.1,List.all_eq_true.mpr ?_⟩,List.all_eq_true.mpr ?_⟩
    · intro c hc
      simp only [ScopedCore.normal,Bool.and_eq_true]
      exact ⟨List.all_eq_true.mp h.1.2 c hc,by simp [plain c hc]⟩
    · intro c hc
      exact (selected_returns_require_plain_service current q raw region ok c (List.mem_filter.mp hc).1 (List.mem_filter.mp hc).2).2.2
  · exact every_old_certificate_remains_valid current q raw region

-- Same unprojected internal closure theorem. Only the terminal service predicate is selected.
theorem arbitrary_relevant_observation_preserved {α : Type} [DecidableEq α]
    (next : α → List α) (seeds owned service : List α) (returned relevant : α → Bool)
    (covers : α → α → Bool) (observe : α → Prop)
    (ok : CompleteClosure.check next seeds owned (ReplyCore.selected returned relevant)
      (CompleteClosure.hasWitness service covers)=true)
    (native : ∀ n∈service,∀ s,covers n s=true → observe s → observe n)
    (s : α) (reach : CompleteClosure.Reach next seeds s)
    (exit : returned s=true) (needed : relevant s=true) (seen : observe s) :
    ∃ n∈service,observe n :=
  ReplyCore.arbitrary_relevant_continuation_observation_is_preserved next seeds owned service
    returned relevant covers observe ok native s reach exit needed seen

end LayerCore
