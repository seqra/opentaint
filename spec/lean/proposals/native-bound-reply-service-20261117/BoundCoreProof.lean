import BoundCore
namespace BoundCoreProof
open NonEmptyPolicy NonEmptyRestriction BoundCore
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

theorem binding_keeps_the_complete_field_mark_and_layer_geometry (ctx : Context) (c : Value) :
    (bind ctx c).ap.path=c.ap.path ∧ (bind ctx c).ap.tail=c.ap.tail ∧
    (bind ctx c).ap.mark=c.ap.mark ∧ (bind ctx c).ap.e=c.ap.e ∧
    (bind ctx c).ap.mx=c.ap.mx ∧ (bind ctx c).demand=c.demand := by simp [BoundCore.bind]

theorem incoming_protection_does_not_erase_local_protection (ctx : Context) (c : Value)
    (localH : c.h=true) : (bind ctx c).h=true := by simp [BoundCore.bind,BoundCore.flag,localH]

theorem a_protected_input_protects_its_committed_image (ctx : Context) (c : Value)
    (incoming : ctx.inputH=true) : (bind ctx c).h=true := by simp [BoundCore.bind,BoundCore.flag,incoming]

theorem cycle_restoration_is_per_output_mark (c : Value) (mark : Nat)
    (same : c.ap.mark=some mark) :
    (bind ⟨false,[mark]⟩ c).h=true := by simp [BoundCore.bind,BoundCore.flag,same]

theorem stored_literal_memberships_stay_distinct_before_binding (c : Value) :
    {c with h:=false}≠{c with h:=true} := by
  intro same
  have no := congrArg Value.h same
  cases no

theorem coverage_has_a_NORMAL_provider_with_the_same_bound_flag (n x : Value)
    (ok : covers n x=true) : n.demand=false ∧ n.h=x.h := by
  have hs := ok
  simp only [covers,Bool.and_eq_true] at hs
  exact ⟨by simpa using hs.1.1,by simpa using hs.1.2⟩

theorem a_wrong_bound_flag_is_never_coverage (n x : Value) (wrong : n.h≠x.h) :
    covers n x=false := by
  cases yes : covers n x
  · rfl
  · exact False.elim (wrong (coverage_has_a_NORMAL_provider_with_the_same_bound_flag n x yes).2)

theorem coverage_keeps_the_same_base_and_full_mark (n x : Value) (ok : covers n x=true) :
    n.ap.base=x.ap.base ∧ n.ap.mark=x.ap.mark := by
  constructor
  · by_cases same : n.ap.base=x.ap.base
    · exact same
    · have neq : n≠x := fun eq => same (congrArg (fun v : Value => v.ap.base) eq)
      simp [covers,neq,same] at ok
  · by_cases same : n.ap.mark=x.ap.mark
    · exact same
    · have neq : n≠x := fun eq => same (congrArg (fun v : Value => v.ap.mark) eq)
      simp [covers,neq,same] at ok

theorem coverage_preserves_every_selected_concrete_location (n x : Value)
    (ok : covers n x=true) (location : Path)
    (inside : UniformActual.locationIn x.ap location) : UniformActual.locationIn n.ap location := by
  have hs := ok
  simp only [BoundCore.covers,Bool.and_eq_true,Bool.or_eq_true] at hs
  rcases hs.2 with same | uniform
  · have eq : n=x := of_decide_eq_true same
    simpa [eq] using inside
  · have must : n.ap.tail=.must := by
      cases tail : n.ap.tail <;> simp_all
    have geom := uniform
    exact UniformActual.whole_region_geometry n.ap x.ap must geom.2 location inside

theorem completed_query_constructs_a_real_native_witness
    (native : List Value) (q : Seed) (raw : List Value) (region : Ap)
    (ctx : Context) (replyH : Bool) (ok : completeFor native q raw region ctx replyH=true)
    (c : Value) (inside : c∈raw) (flagOK : flag ctx c=replyH)
    (overlap : ReplyCore.overlaps c.ap region=true) :
    ∃ n∈native,covers n (bind ctx c)=true ∧ n.demand=false ∧ n.h=replyH := by
  have hs := ok
  simp only [completeFor,Bool.and_eq_true] at hs
  have selected : c∈focus raw region ctx replyH := List.mem_filter.mpr ⟨inside,by simp [flagOK,overlap]⟩
  obtain ⟨n,hn,cover⟩ := List.any_eq_true.mp (List.all_eq_true.mp hs.2 c selected)
  have yes := coverage_has_a_NORMAL_provider_with_the_same_bound_flag n (bind ctx c) cover
  exact ⟨n,hn,cover,yes.1,yes.2.trans flagOK⟩

theorem full_body_closure_is_not_projected_onto_native_flags
    (native : List Value) (q : Seed) (raw : List Value) (region : Ap)
    (ctx : Context) (replyH : Bool) (ok : completeFor native q raw region ctx replyH=true)
    (c : Value) (inside : c∈raw) : c.demand=false := by
  have hs := ok
  simp only [completeFor,Bool.and_eq_true] at hs
  have yes := List.all_eq_true.mp hs.1.2 c inside
  simpa only [LayerCore.normalLayer,Bool.not_eq_true'] using yes

-- Binding is part of the terminal observation, not a new transfer graph.
-- Full internal closure stays in the owner. The native witness is executable.
theorem arbitrary_continuation_observation_after_binding_is_preserved
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (next : α → List α) (seeds owned : List α) (native : List β)
    (returned selected : α → Bool) (bound : α → β) (cover : β → β → Bool)
    (observe : β → Prop)
    (closed : CompleteClosure.check next seeds owned
      (ReplyCore.selected returned selected)
      (fun s => native.any (fun n => cover n (bound s)))=true)
    (image : ∀ n∈native,∀ c,cover n c=true → observe c → observe n)
    (s : α) (reach : CompleteClosure.Reach next seeds s)
    (exit : returned s=true) (needed : selected s=true) (seen : observe (bound s)) :
    ∃ n∈native,observe n := by
  have selectedTrue : ReplyCore.selected returned selected s=true := by
    simp [ReplyCore.selected,exit,needed]
  have obligation := CompleteClosure.every_reachable_return_is_covered next seeds owned
    (ReplyCore.selected returned selected) (fun t => native.any (fun n => cover n (bound t)))
    closed s reach selectedTrue
  obtain ⟨n,hn,covered⟩ := List.any_eq_true.mp obligation
  exact ⟨n,hn,image n hn (bound s) covered seen⟩

end BoundCoreProof
