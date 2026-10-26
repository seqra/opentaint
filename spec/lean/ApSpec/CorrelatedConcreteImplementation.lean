/- Implementation laws for correlated concrete facts. No Kotlin mutation.
   This module makes the transport, packet and admission proofs constructive.
   Export and alias counterexamples keep the remaining decisions explicit. -/
import ApSpec.Run1CorrelatedConcreteInitials
import ApSpec.FlowBackedStore

namespace ApSpec.CorrelatedConcreteImplementation
open ApSpec ApSpec.Run1CorrelatedConcreteInitials

private def finish (c : AFact) (fr to : PFact) : Option (List Acc × Kind × Bool) → Res
  | none => Res.none
  | some (p,k,ap) => match markGate fr.mark c.fact.mark with
    | .no => Res.none
    | .req t => ⟨[],[t]⟩
    | .ok => match markComp to.mark c.fact.mark with
      | none => Res.none
      | some m => ⟨[⟨⟨to.base,p,k,m⟩,c.demand || ap⟩],[]⟩

private theorem raw_apply_eq (c : AFact) (fr to : PFact) :
    rawApply c fr to = if Nat.beq c.fact.base fr.base then
      finish c fr to (CoreAux.geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind)
    else Res.none := rfl

/-- Full geometry/mark coverage before the removed W2 erasure. The original
    concrete witness either has a computed result or produces a mark request. -/
theorem raw_apply_sound {ic fr to : PFact} {c : AFact} {l0 l1 l2 : Loc}
    (h1 : den ic c.fact l0 l1) (h2 : den fr to l1 l2) :
    (∃ r, r ∈ (rawApply c fr to).facts ∧ den ic r.fact l0 l2) ∨
    ((∀ t, c.fact.mark ≠ .conc t) ∧ l0.mark ∈ (rawApply c fr to).reqs) := by
  obtain ⟨hb0,hb1,hm0,hm1,hps,s,r,hp0,hp1,hti,htf⟩ := h1
  obtain ⟨hb1',hb2,hm1',hm2,hps2,s',r',hp1',hp2,hti',htf'⟩ := h2
  have hbase : Nat.beq c.fact.base fr.base = true := by
    rw [← hb1,hb1']; exact Nat.beq_refl _
  have hpath : c.fact.path ++ r = fr.path ++ s' := by rw [← hp1,hp1']
  obtain ⟨p,k,ap,hgeo,r'',hp2'',htf''⟩ :=
    CoreAux.geo_sound (toPath := to.path) hpath htf hti' htf'
  simp only [raw_apply_eq,hbase,if_true,hgeo,finish]
  have hadm : fr.mark.admits (c.fact.mark.out l0.mark) := by rw [← hm1]; exact hm1'
  have hps2' : to.mark.passes (c.fact.mark.out l0.mark) := by rw [← hm1]; exact hps2
  rcases CoreAux.gate_cases hadm hps with hg | ⟨hcs,hg⟩
  · rw [hg]
    cases hmc : markComp to.mark c.fact.mark with
    | none => exact absurd hps2' (CoreAux.markComp_none_no_pair hmc)
    | some m =>
      exact Or.inl ⟨⟨⟨to.base,p,k,m⟩,c.demand || ap⟩,List.mem_singleton.mpr rfl,
        CoreAux.den_result hb0 hm0 hm1 hps hb2 hm2 hps2 hmc hp0 hti
          (by rw [hp2,hp2'']) htf''⟩
  · rw [hg]
    exact Or.inr ⟨hcs,List.mem_singleton.mpr rfl⟩

/-- Arbitrary same-suffix marks are supported by the transfer proof. A seed
    with a concrete mark cannot raise a new mark request in the core gate. -/
theorem concrete_cannot_request (c : AFact) (fr to : PFact) (t : Mark)
    (concrete : c.fact.mark = .conc t) : (rawApply c fr to).reqs = [] := by
  rw [raw_apply_eq]
  split
  · cases hg : CoreAux.geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind with
    | none => rfl
    | some value =>
      obtain ⟨p,k,ap⟩ := value
      cases hm : fr.mark with
      | star => cases hc : markComp to.mark c.fact.mark <;> simp_all [finish,markGate,Res.none]
      | starEx xs => cases hc : markComp to.mark c.fact.mark <;> simp_all [finish,markGate,Res.none]
      | conc u =>
        by_cases hu : u = t <;>
          cases hc : markComp to.mark c.fact.mark <;> simp_all [finish,markGate,Res.none]
  · rfl

theorem abstract_premise_cannot_request (c : AFact) (fr to : PFact)
    (abstract : fr.mark = .star) : (rawApply c fr to).reqs = [] := by
  rw [raw_apply_eq]
  split
  · cases hg : CoreAux.geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind with
    | none => rfl
    | some value =>
      obtain ⟨p,k,ap⟩ := value
      cases hc : markComp to.mark c.fact.mark <;> simp [finish,abstract,markGate,hc,Res.none]
  · rfl

/-- If both arms execute the same alias micro-edge, pair coverage extends
    through it. This is the nonidentity/alias-enabled branch of the proof. -/
theorem covered_alias_step (ei eo fi fo fr to : PFact) (demand : Bool)
    (coverage : ∀ x y, den ei eo x y → den fi fo x y)
    (abstract : fr.mark = .star) (x y z : Loc)
    (marked : den ei eo x y) (aliasEdge : den fr to y z) :
    ∃ r, r ∈ (rawApply ⟨fo,demand⟩ fr to).facts ∧ den fi r.fact x z := by
  rcases raw_apply_sound (c := ⟨fo,demand⟩) (ic := fi) (coverage x y marked) aliasEdge with result | requested
  · exact result
  · rw [abstract_premise_cannot_request ⟨fo,demand⟩ fr to abstract] at requested
    cases requested.2

theorem raw_summary_sound {ic j : PFact} {c g : AFact} {x y z : Loc}
    (incoming : den ic c.fact x y) (summary : den j g.fact y z) :
    (∃ r, r ∈ (rawSummary c j g).facts ∧ den ic r.fact x z) ∨
    ((∀ t, c.fact.mark ≠ .conc t) ∧ x.mark ∈ (rawSummary c j g).reqs) := by
  rcases raw_apply_sound incoming summary with ⟨r,hr,hpair⟩ | requested
  · refine Or.inl ⟨⟨r.fact,r.demand || g.demand⟩,?_,hpair⟩
    exact List.mem_map.mpr ⟨r,hr,rfl⟩
  · exact Or.inr requested

private theorem finish_keeps_demand (c : AFact) (fr to : PFact)
    (geo : Option (List Acc × Kind × Bool)) (demand : c.demand = true)
    (r : AFact) (h : r ∈ (finish c fr to geo).facts) : r.demand = true := by
  cases geo with
  | none => simp [finish,Res.none] at h
  | some value =>
    obtain ⟨p,k,ap⟩ := value
    cases hg : markGate fr.mark c.fact.mark with
    | no => simp [finish,hg,Res.none] at h
    | req t => simp [finish,hg] at h
    | ok =>
      cases hm : markComp to.mark c.fact.mark with
      | none => simp [finish,hg,hm,Res.none] at h
      | some m =>
        simp only [finish,hg,hm,List.mem_singleton] at h
        subst r
        simp [demand]

theorem raw_keeps_demand (c : AFact) (fr to : PFact) (demand : c.demand = true)
    (r : AFact) (h : r ∈ (rawApply c fr to).facts) : r.demand = true := by
  rw [raw_apply_eq] at h
  split at h
  · exact finish_keeps_demand c fr to _ demand r h
  · simp [Res.none] at h

theorem summary_keeps_demand (c : AFact) (j : PFact) (g : AFact)
    (demand : c.demand = true) (r : AFact) (h : r ∈ (rawSummary c j g).facts) :
    r.demand = true := by
  obtain ⟨before,hb,hr⟩ := List.mem_map.mp h
  rw [← hr]
  simp [raw_keeps_demand c j g.fact demand before hb]

/-- No Cartesian product: each decoded mark retains its own same-mark premise. -/
structure Packet where
  geometry : FlowBackedStore.Geometry
  marks : List Mark
  protectedMarks : List Mark
deriving DecidableEq, Repr

def decodePacket (p : Packet) : List ((PFact × AFact) × Bool) :=
  p.marks.map fun t => (FlowBackedStore.scalar p.geometry t,memB t p.protectedMarks)

theorem packet_decode_exact (p : Packet) (row : (PFact × AFact) × Bool) :
    row ∈ decodePacket p ↔ ∃ t, t ∈ p.marks ∧
      row = (FlowBackedStore.scalar p.geometry t,memB t p.protectedMarks) := by
  simp [decodePacket,eq_comm]

theorem packet_decode_diagonal (p : Packet) (row : (PFact × AFact) × Bool)
    (h : row ∈ decodePacket p) : row.1.1.mark = row.1.2.fact.mark := by
  obtain ⟨t,_,rfl⟩ := (packet_decode_exact p row).mp h
  rfl

theorem packet_preserves_tail (p : Packet) (row : (PFact × AFact) × Bool)
    (h : row ∈ decodePacket p) : row.1.2.fact.kind = p.geometry.outputKind := by
  obtain ⟨t,_,rfl⟩ := (packet_decode_exact p row).mp h
  rfl

theorem packet_preserves_input_geometry (p : Packet) (row : (PFact × AFact) × Bool)
    (h : row ∈ decodePacket p) : row.1.1.base = p.geometry.inputBase ∧
      row.1.1.path = p.geometry.inputPath ∧ row.1.1.kind = p.geometry.inputKind := by
  obtain ⟨t,_,rfl⟩ := (packet_decode_exact p row).mp h
  exact ⟨rfl,rfl,rfl⟩

/-- Projection may merge full atoms into a group, but cannot lose a protected
    membership. Duplicate images are canonicalized by the production mark set. -/
theorem projected_protection_subset (projectAtom : Mark → Mark) (ordinary flags : List Mark)
    (inside : ∀ t, t ∈ flags → t ∈ ordinary) (u : Mark)
    (h : u ∈ flags.map projectAtom) : u ∈ ordinary.map projectAtom := by
  obtain ⟨t,ht,hu⟩ := List.mem_map.mp h
  exact List.mem_map.mpr ⟨t,inside t ht,hu⟩

/-- Runtime stores only the current FLOW coverage and explicit marked residual.
    The earlier Cell is a specification history, not a requested runtime store. -/
structure Residual where
  flow : Bool
  marked : Bool
  blocked : Bool
deriving DecidableEq, Repr

def project (s : FlowBackedStore.Cell) : Residual :=
  ⟨s.flow,FlowBackedStore.residual s,s.blocked⟩

def update (s : Residual) : FlowBackedStore.Event → Residual
  | .flow => ⟨true,s.marked && s.blocked,s.blocked⟩
  | .marked p => ⟨s.flow,!s.flow || s.blocked || p,s.blocked || p⟩

theorem residual_simulation (s : FlowBackedStore.Cell) (e : FlowBackedStore.Event) :
    update (project s) e = project (FlowBackedStore.admit s e) := by
  cases s with | mk f m p =>
    cases e with
    | flow => cases f <;> cases m <;> cases p <;> rfl
    | marked q => cases f <;> cases m <;> cases p <;> cases q <;> rfl

theorem residual_idempotent (s : Residual) (e : FlowBackedStore.Event) :
    update (update s e) e = update s e := by
  cases s with | mk f m p =>
    cases e with
    | flow => cases f <;> cases m <;> cases p <;> rfl
    | marked q => cases f <;> cases m <;> cases p <;> cases q <;> rfl

theorem residual_commutes (s : Residual) (e d : FlowBackedStore.Event) :
    update (update s e) d = update (update s d) e := by
  cases s with | mk f m p =>
    cases e <;> cases d <;> cases f <;> cases m <;> cases p <;>
      simp [update,Bool.or_comm]

def changed (s : Residual) (e : FlowBackedStore.Event) : Bool := decide (update s e ≠ s)

theorem repeated_event_has_no_delta (s : Residual) (e : FlowBackedStore.Event) :
    changed (update s e) e = false := by simp [changed,residual_idempotent]

theorem late_flag_is_retained (s : Residual) :
    (update s (.marked true)).marked = true ∧
    (update s (.marked true)).blocked = true := by simp [update]

theorem late_flag_is_work (s : Residual) (plain : s.blocked = false) :
    changed s (.marked true) = true := by
  cases s with | mk f m p => cases f <;> cases m <;> cases p <;> simp_all [changed,update]

theorem covered_plain_needs_no_archive :
    update ⟨true,false,false⟩ (.marked false) = ⟨true,false,false⟩ := rfl

theorem projected_transport (s : FlowBackedStore.Cell) (f t : Prop) (covers : t → f) :
    FlowBackedStore.oldTransport s f t ↔
      ((project s).flow = true ∧ f) ∨ ((project s).marked = true ∧ t) :=
  FlowBackedStore.normalized_transport_exact s f t covers

/-- A layer-only run-1 E-free residual keeps every represented pair. Calling
    this cover is authorized only by the existing exclusion-needing row. -/
def emptyExclusionCover (c : AFact) : AFact :=
  match c.fact.kind with
  | .star _ => ⟨{c.fact with kind := .star Excl.empty},true⟩
  | _ => c

theorem empty_exclusion_cover_sound (i : PFact) (c : AFact) (x y : Loc)
    (h : den i c.fact x y) : den i (emptyExclusionCover c).fact x y := by
  cases hk : c.fact.kind with
  | any => simpa [emptyExclusionCover,hk] using h
  | exact => simpa [emptyExclusionCover,hk] using h
  | star e =>
    simp only [emptyExclusionCover,hk]
    obtain ⟨b0,b1,m0,m1,pass,s,r,p0,p1,hi,hf⟩ := h
    refine ⟨b0,b1,m0,m1,pass,s,r,p0,p1,hi,?_,empty_admits s⟩
    have hs : r = s ∧ e.admits s = true := by simpa [hk,tailF] using hf
    exact hs.1

/-- A below-only cleaner at q leaves the root. An EXACT residual covers it
    without requiring the old coarse ANY seed. -/
theorem cleaner_root_survivor (i : PFact) (b : Base) (q : List Acc) (e : Excl)
    (t : Mark) (x y : Loc)
    (h : den i (shaped b q (.star e) (.conc t)) x y) (root : y.path = q) :
    den i (shaped b q .exact (.conc t)) x y := by
  obtain ⟨b0,b1,m0,m1,pass,s,r,p0,_,hi,_⟩ := h
  exact ⟨b0,b1,m0,m1,pass,s,[],p0,by simpa [shaped] using root,hi,rfl⟩

/-- Faithful local model of the current native FLOW initial gate. It is not
    an export policy decision. Nonempty E is rejected by that current gate. -/
def currentNativeFlowInitial (i : PFact) : Bool :=
  match i.mark,i.kind with
  | .star,.star e => decide (e = Excl.empty)
  | _,_ => false

theorem nonempty_flow_export_gap :
    currentNativeFlowInitial (shaped 1 [] (.star (.set [10])) .star) = false := by decide

def exportGapInput : PFact := shaped 1 [] (.star (.set [10])) .star
def exportGapOutput : PFact := shaped 2 [] (.star (.set [10])) .star

theorem export_gap_has_a_pair :
    den exportGapInput exportGapOutput ⟨1,[],7⟩ ⟨2,[],7⟩ := by
  exact ⟨rfl,rfl,trivial,rfl,trivial,[],[],rfl,rfl,rfl,rfl,rfl⟩

/-- A legal normal FLOW pair is not a current native record and is not an
    ordinary D-layer export. This is a policy gap, not an empty denotation. -/
theorem covered_pair_can_lack_export :
    den exportGapInput exportGapOutput ⟨1,[],7⟩ ⟨2,[],7⟩ ∧
    (false || currentNativeFlowInitial exportGapInput) = false :=
  ⟨export_gap_has_a_pair,by decide⟩

/-- Selected correction: normal abstract STAR records retain any legal E.
    Initial grammar/positive bounds are checked by the unchanged caller. -/
def selectedNativeFlowInitial (i : PFact) : Bool :=
  match i.mark,i.kind with
  | .star,.star _ => true
  | _,_ => false

theorem nonempty_flow_is_persistable (b p e) :
    selectedNativeFlowInitial (shaped b p (.star e) .star) = true := rfl

/-- The current generic view puts shared STAR exclusions on its result.
    The stored native record still retains its two original exclusions. -/
theorem native_star_view_exact (a b : Base) (p q : List Acc) (ei eo : Excl)
    (xs : List Mark) (x y : Loc) :
    den (shaped a p (.star ei) .star) (shaped b q (.star eo) (.starEx xs)) x y ↔
      den (shaped b q (.star Excl.empty) .star)
        (shaped a p (.star (ei.union eo)) (.starEx xs)) y x := by
  constructor
  · rintro ⟨b0,b1,_,hm,pass,s,r,p0,p1,hi,eq,hf⟩
    subst r
    refine ⟨b1,b0,trivial,hm.symm,?_,s,s,p1,p0,empty_admits s,rfl,?_⟩
    · change memB y.mark xs = false
      rw [hm]
      exact pass
    · change (ei.union eo).admits s = true
      rw [CoreAux.Excl.admits_union,hi,hf]
      rfl
  · rintro ⟨b1,b0,_,hm,pass,s,r,p1,p0,_,eq,hs⟩
    subst r
    have both : ei.admits s = true ∧ eo.admits s = true := by
      rw [CoreAux.Excl.admits_union,Bool.and_eq_true] at hs
      exact hs
    refine ⟨b0,b1,trivial,hm.symm,?_,s,s,p0,p1,both.1,rfl,both.2⟩
    change memB x.mark xs = false
    rw [hm]
    exact pass

/-- All C0-preserving ordinary operations use this layer rule. There is no
    NORMAL abstract ANY initial trace produced by the selected start policy. -/
inductive LayerTrace (start : Bool) : Bool → Prop where
  | initial : LayerTrace start start
  | step {old} : LayerTrace start old → (approx : Bool) → LayerTrace start (old || approx)

theorem demand_trace_stays_demand {last : Bool} (h : LayerTrace true last) : last = true := by
  induction h with
  | initial => rfl
  | step _ _ ih => simp [ih]

/-- A selected FLOW counterpart has STAR or ANY input. Under C0, a NORMAL
    trace must have STAR input and is eligible for the selected record store. -/
theorem normal_covered_flow_has_record (b p k) (starOrAny : (∃ e, k = Kind.star e) ∨ k = .any)
    (h : LayerTrace (selectedStart (shaped b p k .star)).demand false) :
    selectedNativeFlowInitial (shaped b p k .star) = true := by
  rcases starOrAny with ⟨e,rfl⟩ | rfl
  · rfl
  · have impossible := demand_trace_stays_demand h
    cases impossible

/-! Semantic input alias closure. These functions are a proof model of the
     existing definition/mark-producer contract, not new runtime stores.
     `covered` includes any admitted FLOW/TAINT cover of a required fact. -/
structure AliasState where
  address : Nat → Nat
  tainted : Nat → Bool
  covered : Nat → Bool

def inputCovered (s : AliasState) : Prop :=
  ∀ p, s.tainted (s.address p) = true → s.covered p = true

def emptyAliasState (address : Nat → Nat) : AliasState := ⟨address,fun _ => false,fun _ => false⟩

theorem empty_inputs_covered (address : Nat → Nat) : inputCovered (emptyAliasState address) := by
  intro p h
  cases h

/-- A genuine alias is a name for the same concrete mark location. False
    may-alias candidates do not create required concrete flow obligations. -/
theorem input_alias_closure (s : AliasState) (complete : inputCovered s) (p q : Nat)
    (alias : s.address p = s.address q) (real : s.tainted (s.address p) = true) :
    s.covered q = true := by
  apply complete q
  rw [← alias]
  exact real

/-- Existing alias-definition/copy transfer supplies the new name from its
    source, including when the concrete mark arrives before the definition. -/
def defineAlias (s : AliasState) (target source : Nat) : AliasState :=
  ⟨fun p => if p == target then s.address source else s.address p,s.tainted,
    fun p => if p == target then s.covered source else s.covered p⟩

theorem define_alias_preserves (s : AliasState) (h : inputCovered s) (target source : Nat) :
    inputCovered (defineAlias s target source) := by
  intro p marked
  by_cases hp : p = target
  · simpa [defineAlias,hp] using h source (by simpa [defineAlias,hp] using marked)
  · simpa [defineAlias,hp] using h p (by simpa [defineAlias,hp] using marked)

/-- Pointwise witness map for existing binding/field-copy transfer. Several
    output aliases may share a source; this does not form premise products. -/
def transportAliases (s : AliasState) (origin : Nat → Nat) : AliasState :=
  ⟨fun p => s.address (origin p),s.tainted,fun p => s.covered (origin p)⟩

theorem transport_aliases_preserves (s : AliasState) (h : inputCovered s) (origin : Nat → Nat) :
    inputCovered (transportAliases s origin) := fun p hp => h (origin p) hp

/-- A mark producer supplies existing genuine aliases. In the analyzer this
    is the producer/alias-transfer contract, not an extra identity-call stage. -/
def produceMark (s : AliasState) (cell : Nat) : AliasState :=
  ⟨s.address,fun c => s.tainted c || (c == cell),
    fun p => s.covered p || (s.address p == cell)⟩

theorem produce_mark_preserves (s : AliasState) (h : inputCovered s) (cell : Nat) :
    inputCovered (produceMark s cell) := by
  intro p marked
  change (s.tainted (s.address p) || (s.address p == cell)) = true at marked
  change (s.covered p || (s.address p == cell)) = true
  rw [Bool.or_eq_true] at marked
  rcases marked with old | fresh
  · simp [h p old]
  · simp [fresh]

def cleanCell (s : AliasState) (cell : Nat) : AliasState :=
  ⟨s.address,fun c => s.tainted c && !(c == cell),
    fun p => s.covered p && !(s.address p == cell)⟩

theorem clean_preserves_positive_coverage (s : AliasState) (h : inputCovered s) (cell : Nat) :
    inputCovered (cleanCell s cell) := by
  intro p marked
  change (s.tainted (s.address p) && (!(s.address p == cell))) = true at marked
  rw [Bool.and_eq_true] at marked
  change (s.covered p && (!(s.address p == cell))) = true
  rw [Bool.and_eq_true]
  exact ⟨h p marked.1,marked.2⟩

inductive AliasEvent where
  | define (target source : Nat)
  | transport (origin : Nat → Nat)
  | mark (cell : Nat)
  | clean (cell : Nat)
  | identity

def aliasStep (s : AliasState) : AliasEvent → AliasState
  | .define target source => defineAlias s target source
  | .transport origin => transportAliases s origin
  | .mark cell => produceMark s cell
  | .clean cell => cleanCell s cell
  | .identity => s

theorem alias_step_covered (s : AliasState) (h : inputCovered s) (e : AliasEvent) :
    inputCovered (aliasStep s e) := by
  cases e with
  | define p q => exact define_alias_preserves s h p q
  | transport origin => exact transport_aliases_preserves s h origin
  | mark c => exact produce_mark_preserves s h c
  | clean c => exact clean_preserves_positive_coverage s h c
  | identity => exact h

theorem alias_trace_covered (events : List AliasEvent) (s : AliasState) (h : inputCovered s) :
    inputCovered (events.foldl aliasStep s) := by
  induction events generalizing s with
  | nil => exact h
  | cons e es ih => exact ih (aliasStep s e) (alias_step_covered s h e)

/-- At an identity-only arm, every required genuine alias consequence is
    already represented by the input closure. The may-candidate set may differ. -/
theorem identity_alias_is_redundant (s : AliasState) (h : inputCovered s) (p q : Nat)
    (sameCell : s.address p = s.address q) (real : s.tainted (s.address p) = true) :
    (aliasStep s .identity).covered q = true := input_alias_closure s h p q sameCell real

/-- Direct binding and aliases are separate arms. Coverage need not imply
    equal metadata-dependent alias arms; the existing later D bypass supplies
    an explicit counterexample to that stronger claim. -/
def suffixOutputs (direct aliases : List Nat) (aliasEnabled : Bool) : List Nat :=
  direct ++ if aliasEnabled then aliases else []

theorem direct_arm_retained (direct aliases : List Nat) (flag : Bool) (v : Nat)
    (h : v ∈ direct) : v ∈ suffixOutputs direct aliases flag := by
  exact List.mem_append_left _ h

theorem alias_work_is_not_equal :
    suffixOutputs [1] [2] (laterAliasEnabled true false) = [1] ∧
    suffixOutputs [1] [2] (laterAliasEnabled true true) = [1,2] := by decide

def controls : List Bool := [
  decide (update ⟨true,false,false⟩ (.marked false) = ⟨true,false,false⟩),
  decide (update ⟨true,false,false⟩ (.marked true) = ⟨true,true,true⟩),
  decide (changed ⟨true,true,true⟩ (.marked true) = false),
  decide (changed ⟨false,true,true⟩ (.marked true) = false),
  decide (currentNativeFlowInitial (shaped 1 [] (.star Excl.empty) .star) = true),
  decide (currentNativeFlowInitial (shaped 1 [] (.star (.set [10])) .star) = false),
  decide (selectedNativeFlowInitial (shaped 1 [] (.star (.set [10])) .star) = true),
  decide (suffixOutputs [1] [2] (laterAliasEnabled true false) = [1]),
  decide (suffixOutputs [1] [2] (laterAliasEnabled true true) = [1,2]),
  decide (([AliasEvent.mark 0,.define 1 0,.identity].foldl aliasStep
    (emptyAliasState id)).covered 1 = true),
  decide (([AliasEvent.define 1 0,.mark 0,.identity].foldl aliasStep
    (emptyAliasState id)).covered 1 = true)
]

end ApSpec.CorrelatedConcreteImplementation
