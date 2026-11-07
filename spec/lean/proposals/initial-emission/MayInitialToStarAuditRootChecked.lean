/-
Investigation only: replace emitted ordinary MAY/ANY initials with STAR.
No implementation or semantic selection follows from this model.

Scope: FULL scalar marks, ordinary bases, ANY demands, Empty E, all accessors
counted fields, restricted runs >=2. Current budgeted scalar emission is reused.
A direction filter models backward MUST rejection. ANY-demand cells do not use
the imported run-2 STAR-demand override. Static/GROUP/ND/aliases/mx/H and nonempty
E require separate native adapters. ZERO is a separate typed token, not base 0.

The image proof has constructive current-emitter witnesses. C5 below models its
entry image+insideDemand gate and FLOW EXACT normalized preimage, not complete
exit restriction, matching, state transition, convergence or global soundness.
-/
import RestrictedInitialPolicy

namespace MayInitialToStarAudit
open ApSpec
abbrev Input := RestrictedInitialPolicy.Input
abbrev Mark := RestrictedInitialPolicy.Mark

inductive Direction where | forward | backward
deriving DecidableEq, Repr
inductive Layer where | normal | demand
deriving DecidableEq, Repr
structure Mode where
  direction : Direction
  fieldLimit : Nat
deriving DecidableEq, Repr
structure AnyDemand where
  base : Nat
  path : List Acc
  mark : Mark
deriving DecidableEq, Repr

def asDemand (d : AnyDemand) : RestrictedInitialPolicy.Demand :=
  ⟨d.base,d.path,.any,d.mark⟩
def directionLegal (direction : Direction) (initial : Input) : Bool :=
  match direction with | .forward => true | .backward => !initial.must

def currentEmit (mode : Mode) (d : AnyDemand) (actual : Input) : Option Input :=
  match RestrictedInitialPolicy.DemandStarPolicy.emitAtBudget mode.fieldLimit (asDemand d) actual with
  | none => none
  | some initial => if directionLegal mode.direction initial then some initial else none

def currentCanEmit (mode : Mode) (d : AnyDemand) (initial : Input) : Bool :=
  RestrictedInitialPolicy.DemandStarPolicy.canEmitAtBudget mode.fieldLimit (asDemand d) initial &&
    directionLegal mode.direction initial

theorem ANY_demand_never_uses_STAR_demand_override (d : AnyDemand) (actual : Input) :
    RestrictedInitialPolicy.DemandStarPolicy.overrideStar (asDemand d) actual = false := by
  simp [RestrictedInitialPolicy.DemandStarPolicy.overrideStar,asDemand,
    RestrictedInitialPolicy.shapeEq]

theorem current_image_has_constructive_actual_witness (mode : Mode) (d : AnyDemand)
    (initial : Input) :
    currentCanEmit mode d initial = true ↔ ∃ actual, currentEmit mode d actual = some initial := by
  constructor
  · intro allowed
    obtain ⟨image,legal⟩ := (Bool.and_eq_true _ _).mp allowed
    obtain ⟨actual,emitted⟩ :=
      (RestrictedInitialPolicy.DemandStarPolicy.bounded_image_has_executable_witness
        mode.fieldLimit (asDemand d) initial).mp image
    exact ⟨actual,by simp only [currentEmit,emitted,legal,if_true]⟩
  · rintro ⟨actual,emitted⟩
    cases raw : RestrictedInitialPolicy.DemandStarPolicy.emitAtBudget mode.fieldLimit (asDemand d) actual with
    | none => simp only [currentEmit,raw] at emitted; cases emitted
    | some candidate =>
      cases legal : directionLegal mode.direction candidate with
      | false => simp only [currentEmit,raw,legal,Bool.false_eq_true,if_false] at emitted; cases emitted
      | true =>
        have same : candidate = initial := by
          simpa only [currentEmit,raw,legal,if_true,Option.some.injEq] using emitted
        subst initial
        exact (Bool.and_eq_true _ _).mpr
          ⟨(RestrictedInitialPolicy.DemandStarPolicy.bounded_image_has_executable_witness
            mode.fieldLimit (asDemand d) candidate).mpr ⟨actual,raw⟩,legal⟩

/-- ANY with must=false is MAY. MUST is shape ANY with must=true and is unchanged. -/
def replaceMay (initial : Input) : Input :=
  match initial.shape, initial.must with
  | .any, false => { initial with shape := .star }
  | _, _ => initial

def isMay (initial : Input) : Bool :=
  RestrictedInitialPolicy.shapeEq initial.shape .any && !initial.must

/-- Exact finite inverse list of replacement. It is not self-projection. -/
def replacementPreimages (initial : Input) : List Input :=
  match initial.shape, initial.must with
  | .any, false => []
  | .star, false => [initial,{ initial with shape := .any }]
  | _, _ => [initial]

theorem replacement_has_explicit_preimage (initial : Input) :
    initial ∈ replacementPreimages (replaceMay initial) := by
  cases initial with
  | mk base path shape mark must =>
    cases shape <;> cases must <;> simp [replaceMay,replacementPreimages]

theorem every_listed_preimage_replaces_to_target (candidate initial : Input)
    (member : candidate ∈ replacementPreimages initial) : replaceMay candidate = initial := by
  cases initial with
  | mk base path shape mark must =>
    cases shape <;> cases must <;> simp [replacementPreimages] at member
    all_goals first
      | (subst candidate; rfl)
      | (rcases member with same | same <;> cases same <;> rfl)

def chooseCurrent (mode : Mode) (d : AnyDemand) : List Input → Bool
  | [] => false
  | initial :: rest => currentCanEmit mode d initial || chooseCurrent mode d rest

theorem choose_current_iff_explicit_candidate (mode : Mode) (d : AnyDemand) (values : List Input) :
    chooseCurrent mode d values = true ↔
      ∃ candidate, candidate ∈ values ∧ currentCanEmit mode d candidate = true := by
  induction values with
  | nil => simp [chooseCurrent]
  | cons head rest ih =>
    constructor
    · intro chosen
      change (currentCanEmit mode d head || chooseCurrent mode d rest) = true at chosen
      cases (Bool.or_eq_true _ _).mp chosen with
      | inl accepted => exact ⟨head,by simp,accepted⟩
      | inr accepted =>
        obtain ⟨candidate,member,image⟩ := ih.mp accepted
        exact ⟨candidate,List.mem_cons_of_mem head member,image⟩
    · rintro ⟨candidate,member,accepted⟩
      change (currentCanEmit mode d head || chooseCurrent mode d rest) = true
      cases List.mem_cons.mp member with
      | inl same =>
        subst candidate
        exact (Bool.or_eq_true _ _).mpr (Or.inl accepted)
      | inr member =>
        exact (Bool.or_eq_true _ _).mpr (Or.inr (ih.mpr ⟨candidate,member,accepted⟩))

def candidateEmit (mode : Mode) (d : AnyDemand) (actual : Input) : Option Input :=
  (currentEmit mode d actual).map replaceMay

def candidateCanEmit (mode : Mode) (d : AnyDemand) (initial : Input) : Bool :=
  chooseCurrent mode d (replacementPreimages initial)

/-- Complete output image of the candidate, with a current native-model actual
witness for each accepted initial. No hypothetical initial is interned. -/
theorem candidate_image_exactly_matches_emission (mode : Mode) (d : AnyDemand)
    (initial : Input) :
    candidateCanEmit mode d initial = true ↔ ∃ actual, candidateEmit mode d actual = some initial := by
  constructor
  · intro allowed
    obtain ⟨raw,member,oldImage⟩ := (choose_current_iff_explicit_candidate mode d _).mp allowed
    obtain ⟨actual,emitted⟩ := (current_image_has_constructive_actual_witness mode d raw).mp oldImage
    exact ⟨actual,by simp only [candidateEmit,emitted,Option.map_some,
      every_listed_preimage_replaces_to_target raw initial member]⟩
  · rintro ⟨actual,emitted⟩
    cases old : currentEmit mode d actual with
    | none => simp only [candidateEmit,old,Option.map_none] at emitted; cases emitted
    | some raw =>
      have same : replaceMay raw = initial := by
        simpa only [candidateEmit,old,Option.map_some,Option.some.injEq] using emitted
      apply (choose_current_iff_explicit_candidate mode d _).mpr
      refine ⟨raw,?_,(current_image_has_constructive_actual_witness mode d raw).mpr ⟨actual,old⟩⟩
      rw [← same]
      exact replacement_has_explicit_preimage raw

theorem replacement_removes_only_MAY_head (initial : Input) :
    isMay (replaceMay initial) = false := by
  cases initial with
  | mk base path shape mark must =>
    cases shape <;> cases must <;> rfl

theorem replacement_keeps_base_path_mark (initial : Input) :
    (replaceMay initial).base = initial.base ∧
    (replaceMay initial).path = initial.path ∧
    (replaceMay initial).mark = initial.mark := by
  cases initial with
  | mk base path shape mark must =>
    cases shape <;> cases must <;> exact ⟨rfl,rfl,rfl⟩

/-- Empty-E ANY-demand containment only. It is not arbitrary native matching. -/
def insideAny (d : AnyDemand) (initial : Input) : Bool :=
  Nat.beq d.base initial.base && RestrictedInitialPolicy.acceptsMark d.mark initial.mark &&
    (dropPrefix d.path initial.path).isSome

def flowStar (initial : Input) : Bool :=
  match initial.mark,initial.shape,initial.must with | .flow,.star,false => true | _,_,_ => false

def asExact (initial : Input) : Input := { initial with shape := .exact,must := false }

def canStoreUsing (image : Mode → AnyDemand → Input → Bool) (mode : Mode)
    (d : AnyDemand) (stored : Input) : Bool :=
  let fits := fun raw => image mode d raw && insideAny d raw
  fits stored || (flowStar stored && fits (asExact stored))

def normalizeFlowKey (initial : Input) : Input :=
  match initial.mark,initial.shape with
  | .flow,.exact => { initial with shape := .star }
  | _,_ => initial

structure StoredRow where
  initial : Input
  opaqueExit : Nat
  layer : Layer
deriving DecidableEq, Repr

def c5EntryTicket (image : Mode → AnyDemand → Input → Bool) (mode : Mode)
    (d : AnyDemand) (row : StoredRow) : Option StoredRow :=
  if canStoreUsing image mode d row.initial then some row else none

theorem accepted_entry_ticket_preserves_exit_and_layer
    (image : Mode → AnyDemand → Input → Bool) (mode : Mode) (d : AnyDemand)
    (row selected : StoredRow) (accepted : c5EntryTicket image mode d row = some selected) :
    selected = row := by
  cases gate : canStoreUsing image mode d row.initial with
  | false => simp only [c5EntryTicket,gate,Bool.false_eq_true,if_false] at accepted; cases accepted
  | true => simpa only [c5EntryTicket,gate,if_true,Option.some.injEq] using accepted.symm

def layerOr : Layer → Layer → Layer
  | .normal,.normal => .normal
  | _,_ => .demand

def intrinsic (initial : Input) : Layer :=
  match initial.shape,initial.mark with
  | .any,_ => if initial.must then .normal else .demand
  | .star,.full _ => .demand
  | _,_ => .normal

/-- The current concrete support/loss-bit rule. Recalculation is NOT a blanket
intrinsic-only reset; existing EXACT-on-MAY demotion remains present. -/
def admissionLayer (emitted actual : Input) (supplied : Layer) : Layer :=
  match emitted.mark with
  | .flow => intrinsic emitted
  | .full _ => layerOr (intrinsic emitted)
      (if decide (supplied = .demand) || (RestrictedInitialPolicy.shapeEq emitted.shape .exact && isMay actual)
       then .demand else .normal)

def startLayer (initial : Input) (admitted : Layer) : Layer :=
  layerOr (intrinsic initial) admitted

inductive LayerChoice where | preserveAdmission | recalculateConverted
deriving DecidableEq, Repr

def candidateStart (choice : LayerChoice) (old actual : Input) (supplied : Layer) : Layer :=
  let next := replaceMay old
  if isMay old then
    match choice with
    | .preserveAdmission => startLayer next (admissionLayer old actual supplied)
    | .recalculateConverted => startLayer next (admissionLayer next actual supplied)
  else startLayer old (admissionLayer old actual supplied)

/-- Necessary existing target guards after matching. This does not establish
that a relation matched, a concrete source arrived or a target was published. -/
def normalTargetGuard (direction : Direction) (flowOrigin : Bool)
    (matched offered : Layer) : Bool :=
  decide (direction = .forward) && !flowOrigin && decide (layerOr matched offered = .normal)

/-- Tail/layer part of the existing MAY-prefix certificate guard. A failed
certificate does not mean the native fallback or its result is absent. -/
def mayCertificate (expected : List Acc) (initial : Input) (layer : Layer) : Bool :=
  decide (initial.path = expected) && isMay initial && decide (layer = .demand)

/-- ZERO is a typed token outside the ordinary ANY-demand data grammar. -/
inductive TypedInput where | zero | ordinary (fact : Input)
deriving DecidableEq, Repr

def replaceTyped : TypedInput → TypedInput
  | .zero => .zero
  | .ordinary initial => .ordinary (replaceMay initial)
def emitTyped (mode : Mode) (d : AnyDemand) : TypedInput → Option TypedInput
  | .zero => none
  | .ordinary actual => (candidateEmit mode d actual).map TypedInput.ordinary

/-- Suffix relation of the copied start fact. It is a local relation abstraction
for ordinary return/copy, not a native driver or all-summary correctness proof. -/
def copiedStart (initial : Input) (resultBase : Nat) : Input := { initial with base := resultBase }
def premiseAllowsSuffix (_initial : Input) (_suffix : List Acc) : Bool := true
def copyRelationAllows (initial : Input) (inputSuffix outputSuffix : List Acc) : Bool :=
  if isMay initial then true else decide (inputSuffix = outputSuffix)

def starSuffixTransfer (entry : Input) (resultBase : Nat) (actual : Input) : Option Input :=
  if Nat.beq entry.base actual.base then
    (dropPrefix entry.path actual.path).map (fun suffix => {actual with base := resultBase,path := suffix})
  else none

theorem STAR_copy_transports_exact_T_suffix (base resultBase : Nat) (path suffix : List Acc) (t : Nat) :
    starSuffixTransfer ⟨base,path,.star,.flow,false⟩ resultBase
      ⟨base,path ++ suffix,.exact,.full t,false⟩ =
      some ⟨resultBase,suffix,.exact,.full t,false⟩ := by
  have removedPrefix : dropPrefix path (path ++ suffix) = some suffix := CoreAux.dropPrefix_some.mpr rfl
  simp only [starSuffixTransfer,Nat.beq_refl,if_true,removedPrefix,Option.map_some]

def forward2 : Mode := ⟨.forward,2⟩
def backward2 : Mode := ⟨.backward,2⟩
def forward1 : Mode := ⟨.forward,1⟩
def p : Nat := 1
def ret : Nat := 2
def f : Acc := 7
def g : Acc := 8
def T : Mark := .full 11
def d0 (mark : Mark) : AnyDemand := ⟨p,[],mark⟩
def d1 (mark : Mark) : AnyDemand := ⟨p,[f],mark⟩
def atF (mark : Mark) : Input := ⟨p,[f],.any,mark,false⟩
def starF (mark : Mark) : Input := ⟨p,[f],.star,mark,false⟩

theorem the_two_current_ANY_result_cells_and_replacements :
    currentEmit forward2 (d1 .flow) (atF T) = some (atF .flow) ∧
    currentEmit forward2 (d1 .flow) ⟨p,[],.any,T,false⟩ = some (atF .flow) ∧
    candidateEmit forward2 (d1 .flow) (atF T) = some (starF .flow) ∧
    candidateEmit forward2 (d1 .flow) ⟨p,[],.any,T,false⟩ = some (starF .flow) ∧
    candidateEmit backward2 (d1 T) (atF T) = some (starF T) := by decide

theorem same_head_STAR_needs_a_new_image_classifier :
    currentCanEmit forward1 (d1 .flow) (starF .flow) = false ∧
    candidateCanEmit forward1 (d1 .flow) (starF .flow) = true ∧
    currentCanEmit forward1 (d1 T) (starF T) = false ∧
    candidateCanEmit forward1 (d1 T) (starF T) = true ∧
    candidateCanEmit forward1 (d1 T) (atF T) = false := by decide

theorem supplied_STAR_still_rejects_and_self_projection_is_incomplete :
    candidateEmit forward1 (d1 .flow) (starF .flow) = none ∧
    candidateEmit forward1 (d1 T) (starF T) = none ∧
    candidateCanEmit forward1 (d1 .flow) (starF .flow) = true := by decide

theorem old_C5_FLOW_normalized_EXACT_fallback_is_not_concrete_STAR_admission :
    normalizeFlowKey ⟨p,[f],.exact,.flow,false⟩ = starF .flow ∧
    canStoreUsing currentCanEmit forward1 (d1 .flow) (starF .flow) = true ∧
    canStoreUsing currentCanEmit forward1 (d1 T) (starF T) = false ∧
    canStoreUsing candidateCanEmit forward1 (d1 T) (starF T) = true := by decide

theorem finer_field_and_terminal_exact_cells_are_unchanged :
    currentEmit forward2 (d0 T) ⟨p,[f],.exact,T,false⟩ =
      candidateEmit forward2 (d0 T) ⟨p,[f],.exact,T,false⟩ ∧
    candidateEmit forward2 (d0 T) ⟨p,[f],.exact,T,false⟩ = some ⟨p,[f],.exact,T,false⟩ ∧
    candidateEmit forward2 (d0 T) ⟨p,[f,g],.exact,T,false⟩ = some (starF T) ∧
    candidateEmit forward1 (d0 T) ⟨p,[f,g],.exact,T,false⟩ = none := by decide

theorem same_head_conversion_needs_no_new_field_budget :
    candidateEmit forward1 (d1 .flow) (atF T) = some (starF .flow) ∧
    candidateEmit forward1 (d1 T) (atF T) = some (starF T) ∧
    candidateEmit forward1 (d1 T) ⟨p,[f,g],.exact,T,false⟩ = none := by decide

theorem MUST_is_not_replaced_and_backward_still_forbids_it :
    candidateEmit forward1 (d1 T) ⟨p,[f],.any,T,true⟩ = some ⟨p,[f],.any,T,true⟩ ∧
    candidateEmit backward2 (d1 T) ⟨p,[f],.any,T,true⟩ = none ∧
    replaceMay ⟨p,[f],.any,.flow,true⟩ = ⟨p,[f],.any,.flow,true⟩ := by decide

theorem FLOW_recalculation_promotes_but_explicit_DEMAND_preservation_does_not :
    intrinsic (atF .flow) = .demand ∧ intrinsic (starF .flow) = .normal ∧
    candidateStart .preserveAdmission (atF .flow) (atF T) .demand = .demand ∧
    candidateStart .recalculateConverted (atF .flow) (atF T) .demand = .normal ∧
    candidateStart .preserveAdmission (atF T) (atF T) .demand = .demand ∧
    candidateStart .recalculateConverted (atF T) (atF T) .demand = .demand := by decide

theorem unrelated_EXACT_on_MAY_loss_bit_is_not_erased :
    admissionLayer ⟨p,[f],.exact,T,false⟩ (atF T) .normal = .demand ∧
    candidateStart .recalculateConverted ⟨p,[f],.exact,T,false⟩ (atF T) .normal = .demand := by decide

theorem FLOW_or_DEMAND_target_guards_prevent_an_immediate_spurious_NORMAL_claim :
    normalTargetGuard .forward true .normal .normal = false ∧
    normalTargetGuard .forward false .demand .normal = false ∧
    normalTargetGuard .forward false .normal .demand = false ∧
    normalTargetGuard .backward false .normal .normal = false ∧
    normalTargetGuard .forward false .normal .normal = true := by decide

theorem both_layer_choices_fail_the_existing_MAY_certificate_tail_guard :
    mayCertificate [f] (atF .flow) .demand = true ∧
    mayCertificate [f] (starF .flow) .demand = false ∧
    mayCertificate [f] (starF .flow) .normal = false := by decide

theorem ZERO_is_excluded_from_the_ordinary_ANY_candidate :
    replaceTyped .zero = .zero ∧ emitTyped forward2 (d0 .flow) .zero = none := by decide

theorem equal_premise_domains_do_not_imply_equal_copied_summary_relations :
    premiseAllowsSuffix (atF .flow) [f] = premiseAllowsSuffix (starF .flow) [f] ∧
    copiedStart (atF .flow) ret = ⟨ret,[f],.any,.flow,false⟩ ∧
    copiedStart (starF .flow) ret = ⟨ret,[f],.star,.flow,false⟩ ∧
    copyRelationAllows (atF .flow) [f] [g] = true ∧
    copyRelationAllows (starF .flow) [f] [g] = false ∧
    copyRelationAllows (starF .flow) [f] [f] = true := by decide

/-- Conditional header-cost abstraction only. It assumes an already protected
MAY or STAR root after the primer and models the supplied strong-write E step.
No AP/runtime/owner enabling, scheduling or cost measurement is inferred. -/
inductive ProtectedHead where | may | star
deriving DecidableEq, Repr

def strongWriteHeader (head : ProtectedHead) (e : List Acc) (field : Acc) : List Acc :=
  match head with | .may => [] | .star => e ++ [field]
def optionalHeader (head : ProtectedHead) (current : List (List Acc)) (field : Acc) : List (List Acc) :=
  (current ++ current.map (fun e => strongWriteHeader head e field)).eraseDups

def headerStages (head : ProtectedHead) : List (List (List Acc)) :=
  let h0 : List (List Acc) := [[]]
  let h1 := optionalHeader head h0 1
  let h2 := optionalHeader head h1 2
  let h3 := optionalHeader head h2 3
  let h4 := optionalHeader head h3 4
  let h5 := optionalHeader head h4 5
  [h0,h1,h2,h3,h4,h5]

theorem conditional_literal_H_header_family_is_one_versus_thirty_two :
    (headerStages .may).map List.length = [1,1,1,1,1,1] ∧
    (headerStages .star).map List.length = [1,2,4,8,16,32] ∧
    ((headerStages .star).getLast!).eraseDups.length = 32 := by decide

theorem concrete_STAR_header_family_does_not_require_a_NORMAL_promotion :
    intrinsic (starF T) = .demand ∧
    candidateStart .preserveAdmission (atF T) (atF T) .demand = .demand ∧
    candidateStart .recalculateConverted (atF T) (atF T) .demand = .demand := by decide

def check : Bool :=
  candidateCanEmit forward1 (d1 .flow) (starF .flow) &&
  !currentCanEmit forward1 (d1 .flow) (starF .flow) &&
  canStoreUsing currentCanEmit forward1 (d1 .flow) (starF .flow) &&
  !canStoreUsing currentCanEmit forward1 (d1 T) (starF T) &&
  decide (candidateStart .recalculateConverted (atF .flow) (atF T) .demand = .normal) &&
  !mayCertificate [f] (starF .flow) .demand

theorem executable_investigation_cells : check = true := by decide
#eval (if check then "MAY_INITIAL_TO_STAR_AUDIT=true" else "MAY_INITIAL_TO_STAR_AUDIT=false")

#print axioms ANY_demand_never_uses_STAR_demand_override
#print axioms current_image_has_constructive_actual_witness
#print axioms replacement_has_explicit_preimage
#print axioms every_listed_preimage_replaces_to_target
#print axioms choose_current_iff_explicit_candidate
#print axioms candidate_image_exactly_matches_emission
#print axioms replacement_removes_only_MAY_head
#print axioms replacement_keeps_base_path_mark
#print axioms accepted_entry_ticket_preserves_exit_and_layer
#print axioms STAR_copy_transports_exact_T_suffix
#print axioms the_two_current_ANY_result_cells_and_replacements
#print axioms same_head_STAR_needs_a_new_image_classifier
#print axioms supplied_STAR_still_rejects_and_self_projection_is_incomplete
#print axioms old_C5_FLOW_normalized_EXACT_fallback_is_not_concrete_STAR_admission
#print axioms finer_field_and_terminal_exact_cells_are_unchanged
#print axioms same_head_conversion_needs_no_new_field_budget
#print axioms MUST_is_not_replaced_and_backward_still_forbids_it
#print axioms FLOW_recalculation_promotes_but_explicit_DEMAND_preservation_does_not
#print axioms unrelated_EXACT_on_MAY_loss_bit_is_not_erased
#print axioms FLOW_or_DEMAND_target_guards_prevent_an_immediate_spurious_NORMAL_claim
#print axioms both_layer_choices_fail_the_existing_MAY_certificate_tail_guard
#print axioms ZERO_is_excluded_from_the_ordinary_ANY_candidate
#print axioms equal_premise_domains_do_not_imply_equal_copied_summary_relations
#print axioms conditional_literal_H_header_family_is_one_versus_thirty_two
#print axioms concrete_STAR_header_family_does_not_require_a_NORMAL_promotion
#print axioms executable_investigation_cells

end MayInitialToStarAudit
