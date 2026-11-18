import AuditScopedService
namespace AuditReplySafety
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def supports (v : Value) (p : UniformSafety.Point) : Prop :=
  v.ap.base=p.base ∧ v.ap.mark=some p.mark ∧ UniformActual.locationIn v.ap p.path

theorem native_cover_preserves_each_concrete_point
    (n c : Value) (cover : BoundCore.covers n c=true)
    (p : UniformSafety.Point) (present : supports c p) : supports n p := by
  have coords := BoundCoreProof.coverage_keeps_the_same_base_and_full_mark n c cover
  exact ⟨coords.1.trans present.1,coords.2.trans present.2.1,
    BoundCoreProof.coverage_preserves_every_selected_concrete_location n c cover p.path present.2.2⟩

theorem native_cover_preserves_every_positive_ND_continuation
    (n c : Value) (cover : BoundCore.covers n c=true)
    (program : List (AuditKernel.Rule UniformSafety.Point))
    (observation : UniformSafety.Point)
    (old : AuditKernel.Derives program (supports c) observation) :
    AuditKernel.Derives program (supports n) observation := by
  apply AuditKernel.positive_ND_closure_preserves_every_derivation program (supports c) (supports n) _ observation old
  intro p hp
  exact AuditKernel.Derives.initial p (native_cover_preserves_each_concrete_point n c cover p hp)

-- This discharges the previous abstract image-monotonicity premise for
-- positive ground programs. It does not establish raw C2-service equality.
theorem complete_query_service_preserves_positive_continuations_without_an_external_monotonicity_axiom
    {α : Type} [DecidableEq α]
    (next : α → List α) (seeds owned : List α) (native : List Value)
    (returned selected : α → Bool) (bound : α → Value)
    (program : List (AuditKernel.Rule UniformSafety.Point)) (observation : UniformSafety.Point)
    (closed : CompleteClosure.check next seeds owned
      (ReplyCore.selected returned selected)
      (fun s => native.any (fun n => BoundCore.covers n (bound s)))=true)
    (s : α) (reached : CompleteClosure.Reach next seeds s)
    (exit : returned s=true) (needed : selected s=true)
    (old : AuditKernel.Derives program (supports (bound s)) observation) :
    ∃ n∈native,AuditKernel.Derives program (supports n) observation := by
  exact BoundCoreProof.arbitrary_continuation_observation_after_binding_is_preserved
    next seeds owned native returned selected bound BoundCore.covers
    (fun c => AuditKernel.Derives program (supports c) observation) closed
    (fun n _ c hc h => native_cover_preserves_every_positive_ND_continuation n c hc program observation h)
    s reached exit needed old

def oldPacket (other : UniformSafety.Point → Prop) (raw : List Value)
    (ctx : BoundCore.Context) (region : Ap) (h : Bool) (point : UniformSafety.Point) : Prop :=
  other point ∨ ∃ c∈BoundCore.focus raw region ctx h,supports (BoundCore.bind ctx c) point

def newPacket (other : UniformSafety.Point → Prop) (native : List Value)
    (point : UniformSafety.Point) : Prop := other point ∨ ∃ n∈native,supports n point

theorem whole_packet_and_joint_other_mark_observations_are_preserved
    (other : UniformSafety.Point → Prop) (native raw : List Value)
    (query : Seed) (ctx : BoundCore.Context) (region : Ap) (h : Bool)
    (closed : BoundCore.completeFor native query raw region ctx h=true)
    (program : List (AuditKernel.Rule UniformSafety.Point)) (observation : UniformSafety.Point)
    (old : AuditKernel.Derives program (oldPacket other raw ctx region h) observation) :
    AuditKernel.Derives program (newPacket other native) observation := by
  apply AuditKernel.positive_ND_closure_preserves_every_derivation program _ _ _ observation old
  intro p hp
  rcases hp with unchanged | ⟨c,hc,point⟩
  · exact AuditKernel.Derives.initial p (Or.inl unchanged)
  · have member := List.mem_filter.mp hc
    have selected := member.2
    simp only [Bool.and_eq_true] at selected
    have sameH : BoundCore.flag ctx c=h := by simpa using selected.1
    obtain ⟨n,hn,cover,_,_⟩ := BoundCoreProof.completed_query_constructs_a_real_native_witness
      native query raw region ctx h closed c member.1 sameH selected.2
    exact AuditKernel.Derives.initial p
      (Or.inr ⟨n,hn,native_cover_preserves_each_concrete_point n (BoundCore.bind ctx c) cover p point⟩)

end AuditReplySafety
