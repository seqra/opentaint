import Lean

/-!
Producer grammar and one C2 premise for the current Thing2 investigation.
This file is NOT a demand-retirement theorem. In particular, structural
coverage of an exact initial by a STAR initial is not a theorem about source
hits, native filters, aliases, C5 or future observations.

The checked Kotlin correspondence is in the current case's
backward-grammar-action-audit.md. Every kernel here over-approximates only
tail outcomes. Geometry and marks can remove outcomes; they cannot add a
tail outside this grammar.
-/
namespace Thing2BackwardGrammar

inductive Tail where
  | exact | star | may | must
  deriving DecidableEq, Repr

inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr

def Regular (t : Tail) : Prop := t ≠ .must

instance (t : Tail) : Decidable (Regular t) := inferInstanceAs (Decidable (t ≠ .must))

/- Exact leaves do not acquire the packet's any-tail meaning. -/
structure Packet where
  exactCount : Nat
  anyCount : Nat
  anyTail : Tail
  deriving DecidableEq, Repr

def Packet.members (p : Packet) : List Tail :=
  List.replicate p.exactCount .exact ++ List.replicate p.anyCount p.anyTail

def Packet.noSemanticMust (p : Packet) : Prop := ∀ t ∈ p.members, Regular t

theorem exact_only_must_header_is_safe (n : Nat) :
    Packet.noSemanticMust ⟨n, 0, .must⟩ := by
  intro t ht
  simp [Packet.members, List.mem_replicate] at ht
  simp_all [Regular]

example : ¬ Packet.noSemanticMust ⟨0, 1, .must⟩ := by
  intro h
  have bad := h .must (by simp [Packet.members])
  exact bad rfl

/- The ordinary compiled edge kernel has a direct and an ancestor outcome.
   An EXACT/FLOW input also has an excluded identity-keep field-write
   exception which can produce MAY. Include it conservatively for EXACT
   inputs without assuming the concrete/FLOW distinction away. -/
def directTail (actual target : Tail) : Tail :=
  match target with
  | .star => actual
  | .exact => .exact
  | .may => .may
  | .must => .must

def ancestorTail (actual target : Tail) : Tail :=
  if actual = .must then
    match target with
    | .exact => .exact
    | .may => .may
    | .star | .must => .must
  else if target = .exact then .exact else .may

def kernel (actual target : Tail) : List Tail :=
  [directTail actual target] ++
    (if actual = .exact then [.may] else [ancestorTail actual target])

theorem kernel_preserves_regular (a t : Tail) (ha : Regular a) (ht : Regular t) :
    ∀ o ∈ kernel a t, Regular o := by
  cases a <;> cases t <;>
    simp_all [Regular, kernel, directTail, ancestorTail]

/- RevTails has no MUST output, even for a forward source with a MUST target.
   A forward MUST premise is not a micro-edge and is handled by native views. -/
def reversedTails (input output : Tail) : Option (Tail × Tail) :=
  match input, output with
  | .star, .star => some (.star, .star)
  | .star, .exact => some (.exact, .may)
  | .star, .may => some (.may, .may)
  | .may, .star => some (.star, .star)
  | .may, .exact => some (.exact, .may)
  | .may, .may => some (.may, .may)
  | .may, .must => some (.may, .may)
  | .exact, .star => some (.exact, .exact)
  | .exact, .exact => some (.exact, .exact)
  | .exact, .may => some (.may, .exact)
  | .exact, .must => some (.may, .exact)
  | _, _ => none

theorem reversed_tails_regular (i o p q : Tail)
    (h : reversedTails i o = some (p, q)) : Regular p ∧ Regular q := by
  cases i <;> cases o <;> simp [reversedTails] at h
  all_goals rcases h with ⟨rfl, rfl⟩; constructor <;> decide

/- Supported forward concrete native MUST views. The query is STAR for a
   MUST conclusion. A MUST premise becomes a MAY result, never a MUST result. -/
def oppositeConcreteView (input output : Tail) : Option (Tail × Tail) :=
  match input, output with
  | .must, .exact => some (.exact, .may)
  | .must, .must => some (.star, .may)
  | .exact, .must => some (.star, .exact)
  | _, _ => reversedTails input output

theorem opposite_view_regular (i o p q : Tail)
    (h : oppositeConcreteView i o = some (p, q)) : Regular p ∧ Regular q := by
  cases i <;> cases o <;> simp [oppositeConcreteView, reversedTails] at h
  all_goals rcases h with ⟨rfl, rfl⟩; constructor <;> decide

def oppositeFlowView (input output : Tail) : Option (Tail × Tail) :=
  match input, output with
  | .must, .star | .must, .must | .star, .must => some (.star, .may)
  | _, _ => reversedTails input output

theorem opposite_flow_view_regular (i o p q : Tail)
    (h : oppositeFlowView i o = some (p, q)) : Regular p ∧ Regular q := by
  cases i <;> cases o <;> simp [oppositeFlowView, reversedTails] at h
  all_goals rcases h with ⟨rfl, rfl⟩; constructor <;> decide

/- Cleaner/cut/filter/normalization outcomes are a tail over-approximation.
   A cleaner may preserve a tail, demote to MAY or retain an exact root.
   FLOW summary normalization can change EXACT to STAR. MUST survivors
   therefore require a pre-existing semantic MUST input. -/
def restrictedOutcomes (a : Tail) : List Tail := [a, .exact, .may, .star]

theorem restriction_preserves_regular (a : Tail) (ha : Regular a) :
    ∀ o ∈ restrictedOutcomes a, Regular o := by
  intro o ho
  simp [restrictedOutcomes] at ho
  rcases ho with rfl | rfl | rfl | rfl <;> simp_all [Regular]

/- An execution derivation, not an arbitrary pre-filled fact store.
   Native direct BACKWARD records have exact-only concrete conclusions.
   Reversed source and ND-source arms use the reversed micro-edge producer.
   Source targetTree on an unreversed forward action is not a backward rule.
   ZERO/Target values create no concrete DATA member in this grammar. -/
inductive Produced : Tail → Prop where
  | initialExact : Produced .exact
  | initialStar : Produced .star
  | sinkExact : Produced .exact
  | sinkMay : Produced .may
  | copy {a} : Produced a → Produced a
  | reversedMicro {a i o p q r} : Produced a →
      reversedTails i o = some (p, q) → r ∈ kernel a q → Produced r
  | directBackwardRecord {a r} : Produced a → r ∈ kernel a .exact → Produced r
  /- Current summaries, and retained backward FLOW summaries, use target
     memberships with their own finite backward derivation. -/
  | derivedBackwardSummary {a q r} : Produced a → Produced q → r ∈ kernel a q → Produced r
  | oppositeForwardRecord {a i o p q r} : Produced a →
      oppositeConcreteView i o = some (p, q) → r ∈ kernel a q → Produced r
  | oppositeForwardFlowRecord {a i o p q r} : Produced a →
      oppositeFlowView i o = some (p, q) → r ∈ kernel a q → Produced r
  | restrictOrClean {a r} : Produced a → r ∈ restrictedOutcomes a → Produced r

theorem produced_no_semantic_must {t : Tail} (h : Produced t) : Regular t := by
  induction h with
  | initialExact => decide
  | initialStar => decide
  | sinkExact => decide
  | sinkMay => decide
  | copy _ ih => exact ih
  | reversedMicro _ hv hm ih =>
      exact kernel_preserves_regular _ _ ih (reversed_tails_regular _ _ _ _ hv).2 _ hm
  | directBackwardRecord _ hm ih =>
      exact kernel_preserves_regular _ _ ih (by decide) _ hm
  | derivedBackwardSummary _ _ hm iha ihq =>
      exact kernel_preserves_regular _ _ iha ihq _ hm
  | oppositeForwardRecord _ hv hm ih =>
      exact kernel_preserves_regular _ _ ih (opposite_view_regular _ _ _ _ hv).2 _ hm
  | oppositeForwardFlowRecord _ hv hm ih =>
      exact kernel_preserves_regular _ _ ih (opposite_flow_view_regular _ _ _ _ hv).2 _ hm
  | restrictOrClean _ hm ih => exact restriction_preserves_regular _ ih _ hm

theorem backward_must_has_no_derivation : ¬ Produced .must := by
  intro h
  exact produced_no_semantic_must h rfl

inductive Mark where
  | concreteT | flow
  deriving DecidableEq, Repr

structure Initial where
  tail : Tail
  mark : Mark
  layer : Layer
  deriving DecidableEq, Repr

structure Offer where
  /- The demand is at the empty ret path. A positive depth is a child offer. -/
  depth : Nat
  tail : Tail
  layer : Layer
  deriving DecidableEq, Repr

def exactLayer (o : Offer) : Layer :=
  match o.tail with
  | .exact | .star | .must => o.layer
  | .may => .demand

/- W1/W6 apply to actual concrete memberships, not arbitrary low-level AP
   objects. The raw scalar API below still exposes STAR/NORMAL faithfully. -/
def CanonicalConcrete (o : Offer) : Prop :=
  (o.tail = .star ∨ o.tail = .may) → o.layer = .demand

def LegalOffer (o : Offer) : Prop := Regular o.tail ∧ CanonicalConcrete o

def propagatedLayer (incoming : Layer) (edgeDemand : Bool) (tail : Tail) : Layer :=
  if tail = .may then .demand else if edgeDemand then .demand else incoming

theorem kernel_star_origin (a t : Tail) (ha : Regular a) (ht : Regular t)
    (h : Tail.star ∈ kernel a t) : a = .star := by
  cases a <;> cases t <;> simp_all [Regular, kernel, directTail, ancestorTail]

theorem concrete_kernel_legal (a : Offer) (t r : Tail) (demand : Bool)
    (ha : LegalOffer a) (ht : Regular t) (hr : r ∈ kernel a.tail t) (depth : Nat) :
    LegalOffer ⟨depth, r, propagatedLayer a.layer demand r⟩ := by
  refine ⟨kernel_preserves_regular _ _ ha.1 ht _ hr, ?_⟩
  intro h
  rcases h with hs | hm
  · change r = .star at hs
    subst r
    have origin := kernel_star_origin _ _ ha.1 ht hr
    have layer := ha.2 (Or.inl origin)
    simp [propagatedLayer, layer]
  · change r = .may at hm
    subst r
    simp [propagatedLayer]

def concreteRestrictions (a : Tail) : List Tail := [a, .exact, .may]

theorem concrete_restriction_legal (a : Offer) (r : Tail) (demand : Bool)
    (ha : LegalOffer a) (hr : r ∈ concreteRestrictions a.tail) (depth : Nat) :
    LegalOffer ⟨depth, r, propagatedLayer a.layer demand r⟩ := by
  simp [concreteRestrictions] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨ha.1, ?_⟩
    intro h
    have layer := ha.2 h
    cases a.tail <;> simp_all [propagatedLayer]
  · simp [LegalOffer, Regular, CanonicalConcrete, propagatedLayer]
  · simp [LegalOffer, Regular, CanonicalConcrete, propagatedLayer]

/- Concrete layer producer induction. FLOW EXACT→STAR normalization remains
   in the earlier mark-agnostic grammar; it is not a concrete STAR generator.
   A FLOW relation applied to a concrete input uses the same layer-monotone
   kernel here. Current summaries and native records use that kernel too. -/
inductive CanonicalProduced : Offer → Prop where
  | initialExact (depth : Nat) (layer : Layer) : CanonicalProduced ⟨depth, .exact, layer⟩
  | initialStar (depth : Nat) : CanonicalProduced ⟨depth, .star, .demand⟩
  | sinkMay (depth : Nat) : CanonicalProduced ⟨depth, .may, .demand⟩
  | copy {a} (depth : Nat) : CanonicalProduced a → CanonicalProduced ⟨depth, a.tail, a.layer⟩
  | kernel {a t r} (depth : Nat) (demand : Bool) : CanonicalProduced a → Regular t →
      r ∈ Thing2BackwardGrammar.kernel a.tail t →
      CanonicalProduced ⟨depth, r, propagatedLayer a.layer demand r⟩
  | restrictOrClean {a r} (depth : Nat) (demand : Bool) : CanonicalProduced a →
      r ∈ concreteRestrictions a.tail → CanonicalProduced ⟨depth, r, propagatedLayer a.layer demand r⟩

theorem canonical_produced_legal {o : Offer} (h : CanonicalProduced o) : LegalOffer o := by
  induction h with
  | initialExact => simp [LegalOffer, Regular, CanonicalConcrete]
  | initialStar => simp [LegalOffer, Regular, CanonicalConcrete]
  | sinkMay => simp [LegalOffer, Regular, CanonicalConcrete]
  | copy _ _ ih => exact ih
  | kernel depth demand _ ht hr ih => exact concrete_kernel_legal _ _ _ _ ih ht hr depth
  | restrictOrClean depth demand _ hr ih => exact concrete_restriction_legal _ _ _ ih hr depth

theorem normal_concrete_star_has_no_derivation (depth : Nat) :
    ¬ CanonicalProduced ⟨depth, .star, .normal⟩ := by
  intro h
  have bad := (canonical_produced_legal h).2 (Or.inl rfl)
  cases bad

/- Matching full T, empty E, same return base. Mark mismatches and other bases
   emit nothing for X and are immaterial to this necessary-premise check. -/
def emitX (o : Offer) : List Initial :=
  if o.depth = 0 then [⟨.exact, .concreteT, exactLayer o⟩] else []

def emitYRoot (o : Offer) : List Initial :=
  match o.tail with
  | .exact => [⟨.exact, .concreteT, o.layer⟩]
  | .star | .may => [⟨.star, .concreteT, .demand⟩, ⟨.star, .flow, .normal⟩]
  | .must => [] /- legalInitial rejects the chosen backward MUST initial. -/

/- Leave every deeper Y cell arbitrary. X emits nothing there. -/
def emitY (children : Offer → List Initial) (o : Offer) : List Initial :=
  if o.depth = 0 then emitYRoot o else children o

def StructurallyCovers (y x : Initial) : Prop :=
  y.mark = x.mark ∧ y.layer = x.layer ∧
    (y.tail = x.tail ∨ (y.tail = .star ∧ x.tail = .exact))

/- Executable witness: the first Y root admission is the concrete admission.
   The actual MUST cell fails and is not silently assigned a witness. -/
def chooseY (o : Offer) : Option Initial := (emitYRoot o).head?

theorem legal_root_witness (o : Offer) (h : LegalOffer o) :
    ∃ y, chooseY o = some y ∧ y ∈ emitYRoot o ∧
      StructurallyCovers y ⟨.exact, .concreteT, exactLayer o⟩ := by
  cases ht : o.tail <;> cases hl : o.layer <;>
    simp_all [LegalOffer, Regular, CanonicalConcrete, chooseY, emitYRoot, exactLayer, StructurallyCovers]

theorem legal_c2_structural_cover (children : Offer → List Initial)
    (o : Offer) (h : LegalOffer o) :
    ∀ x ∈ emitX o, ∃ y ∈ emitY children o, StructurallyCovers y x := by
  intro x hx
  by_cases hd : o.depth = 0
  · simp [emitX, hd] at hx
    subst x
    obtain ⟨y, _, hy, hc⟩ := legal_root_witness o h
    exact ⟨y, by simpa [emitY, hd] using hy, hc⟩
  · simp [emitX, hd] at hx

theorem produced_offer_c2_cover (children : Offer → List Initial)
    (o : Offer) (h : Produced o.tail) (hc : CanonicalConcrete o) :
    ∀ x ∈ emitX o, ∃ y ∈ emitY children o, StructurallyCovers y x :=
  legal_c2_structural_cover children o ⟨produced_no_semantic_must h, hc⟩

theorem canonical_produced_offer_c2_cover (children : Offer → List Initial)
    (o : Offer) (h : CanonicalProduced o) :
    ∀ x ∈ emitX o, ∃ y ∈ emitY children o, StructurallyCovers y x :=
  legal_c2_structural_cover children o (canonical_produced_legal h)

example : emitX ⟨0, .must, .normal⟩ = [⟨.exact, .concreteT, .normal⟩] := by decide
example : emitYRoot ⟨0, .must, .normal⟩ = [] := by decide
example : chooseY ⟨0, .must, .normal⟩ = none := by decide
example : chooseY ⟨0, .may, .demand⟩ = some ⟨.star, .concreteT, .demand⟩ := by decide
example : emitX ⟨0, .star, .normal⟩ = [⟨.exact, .concreteT, .normal⟩] := by decide
example : ¬ ∃ y ∈ emitYRoot ⟨0, .star, .normal⟩,
    StructurallyCovers y ⟨.exact, .concreteT, .normal⟩ := by
  simp [emitYRoot, StructurallyCovers]
example : Tail.may ∈ kernel .exact .star := by decide
example : Tail.star ∈ restrictedOutcomes .exact := by decide

#print axioms exact_only_must_header_is_safe
#print axioms kernel_preserves_regular
#print axioms reversed_tails_regular
#print axioms opposite_view_regular
#print axioms opposite_flow_view_regular
#print axioms restriction_preserves_regular
#print axioms produced_no_semantic_must
#print axioms backward_must_has_no_derivation
#print axioms kernel_star_origin
#print axioms concrete_kernel_legal
#print axioms concrete_restriction_legal
#print axioms canonical_produced_legal
#print axioms normal_concrete_star_has_no_derivation
#print axioms legal_root_witness
#print axioms legal_c2_structural_cover
#print axioms produced_offer_c2_cover
#print axioms canonical_produced_offer_c2_cover

end Thing2BackwardGrammar
