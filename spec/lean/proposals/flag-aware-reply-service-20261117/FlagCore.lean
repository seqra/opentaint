import RelevantReturn
import CompleteClosure
namespace FlagCore
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
abbrev Edge := Ap × Value

def focus (raw : List Value) (region : Ap) (flag : Bool) : List Value :=
  raw.filter (fun c => c.h==flag && ReplyCore.overlaps c.ap region)

def completeFor (service : List Edge) (q : Seed) (raw : List Value) (region : Ap)
    (flag : Bool) : Bool :=
  ScopedCore.eligible q && raw.all LayerCore.normalLayer &&
    (focus raw region flag).all (ScopedCore.covered service q)

def received (native raw : List Value) (region : Ap) (flag : Bool) : Bool :=
  (focus raw region flag).all fun c => native.any
    (fun n => decide (n={c with ap:={c.ap with base:=AlternatingCondition.p}}))
theorem selected_return_has_the_same_flag_and_whole_NORMAL_service
    (service : List Edge) (q : Seed) (raw : List Value) (region : Ap) (flag : Bool)
    (ok : completeFor service q raw region flag=true) (c : Value) (inside : c∈raw)
    (selected : c.h=flag) (overlap : ReplyCore.overlaps c.ap region=true) :
    LayerCore.normalLayer c=true ∧ ScopedCore.covered service q c=true := by
  have hs := ok
  simp only [completeFor,Bool.and_eq_true] at hs
  exact ⟨List.all_eq_true.mp hs.1.2 c inside,
    List.all_eq_true.mp hs.2 c (List.mem_filter.mpr ⟨inside,by simp [selected,overlap]⟩)⟩

theorem receipt_preserves_the_complete_same_flag_image
    (native raw : List Value) (region : Ap) (flag : Bool)
    (ok : received native raw region flag=true) (c : Value) (inside : c∈raw)
    (selected : c.h=flag) (overlap : ReplyCore.overlaps c.ap region=true) :
    ∃ n∈native,n={c with ap:={c.ap with base:=AlternatingCondition.p}} ∧ n.h=flag := by
  have member : c∈focus raw region flag := List.mem_filter.mpr ⟨inside,by simp [selected,overlap]⟩
  obtain ⟨n,hn,eq⟩ := List.any_eq_true.mp (List.all_eq_true.mp ok c member)
  have eq := of_decide_eq_true eq
  refine ⟨n,hn,eq,?_⟩
  rw [eq]
  exact selected

theorem wrong_flag_provider_cannot_cover_a_selected_return
    (service : List Edge) (q : Seed) (c : Value)
    (wrong : ∀ e∈service,e.2.h≠c.h) : ScopedCore.covered service q c=false := by
  cases yes : ScopedCore.covered service q c
  · rfl
  · obtain ⟨e,he,eq⟩ := List.any_eq_true.mp yes
    have eq := of_decide_eq_true eq
    exact False.elim (wrong e he (congrArg Value.h eq.2))

theorem other_flags_are_not_erased_from_the_full_closure
    (service : List Edge) (q : Seed) (raw : List Value) (region : Ap) (flag : Bool)
    (ok : completeFor service q raw region flag=true) (c : Value) (inside : c∈raw) :
    c.demand=false := by
  have hs := ok
  simp only [completeFor,Bool.and_eq_true] at hs
  have normal := List.all_eq_true.mp hs.1.2 c inside
  simpa only [LayerCore.normalLayer,Bool.not_eq_true'] using normal

theorem arbitrary_same_flag_continuation_observation_is_preserved
    {α : Type} [DecidableEq α] (next : α → List α) (seeds owned service : List α)
    (returned selected : α → Bool) (covers : α → α → Bool) (observe : α → Prop)
    (ok : CompleteClosure.check next seeds owned (ReplyCore.selected returned selected)
      (CompleteClosure.hasWitness service covers)=true)
    (native : ∀ n∈service,∀ s,covers n s=true → observe s → observe n)
    (s : α) (reach : CompleteClosure.Reach next seeds s)
    (exit : returned s=true) (needed : selected s=true) (seen : observe s) :
    ∃ n∈service,observe n :=
  ReplyCore.arbitrary_relevant_continuation_observation_is_preserved next seeds owned service
    returned selected covers observe ok native s reach exit needed seen

end FlagCore
