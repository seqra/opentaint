/-
SELECTED FULL strategy: post-map every emitted MAY/ANY initial to STAR.
Joint image supplement. No new source, grounding, history or admission cell.

The exact executable image is finite: two ordinary bases, a two-field alphabet,
all paths of length <=2, FLOW/two full marks, all valid tails and supplied layers.
MAY actuals are DEMAND by W6. Other actuals keep supplied N/D support. The generic
joint-image theorem is parameterized by the CURRENT scalar emitter; instantiating
it does not add an emitter rule. The certificate theorem uses the checked ANY-
demand scalar adapter universally over counted-field paths and full scalar marks.
Static/GROUP/mx/nonemptyE/noncounted accessors and native owner loops are OPEN.
-/
import MayInitialToStarAuditRootChecked

namespace SelectedFullAdmission
open ApSpec MayInitialToStarAudit
abbrev Mark := MayInitialToStarAudit.Mark
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

structure Actual where
  fact : Input
  layer : Layer
deriving DecidableEq, Repr
structure Admission where
  initial : Input
  layer : Layer
deriving DecidableEq, Repr

/-- Re-run the current support rule on the converted shape. This changes FLOW
MAY/D to STAR/N; concrete STAR stays D. It is not an intrinsic-only reset. -/
def convertAdmission (old : Input) (actual : Actual) : Admission :=
  let initial := replaceMay old
  ⟨initial,admissionLayer initial actual.fact actual.layer⟩
def emitJoint (oldEmitter : Input → Option Input) (actual : Actual) : Option Admission :=
  (oldEmitter actual.fact).map (fun old => convertAdmission old actual)

def anyBy {α : Type} (accept : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => accept x || anyBy accept xs

theorem finite_search_has_explicit_witness {α : Type} (accept : α → Bool) (xs : List α) :
    anyBy accept xs = true ↔ ∃ x, x ∈ xs ∧ accept x = true := by
  induction xs with
  | nil => simp [anyBy]
  | cons x xs ih =>
    constructor
    · intro yes
      change (accept x || anyBy accept xs) = true at yes
      cases (Bool.or_eq_true _ _).mp yes with
      | inl h => exact ⟨x,by simp,h⟩
      | inr h =>
        obtain ⟨y,member,accepted⟩ := ih.mp h
        exact ⟨y,List.mem_cons_of_mem x member,accepted⟩
    · rintro ⟨y,member,accepted⟩
      change (accept x || anyBy accept xs) = true
      cases List.mem_cons.mp member with
      | inl same => subst y; exact (Bool.or_eq_true _ _).mpr (Or.inl accepted)
      | inr member => exact (Bool.or_eq_true _ _).mpr (Or.inr (ih.mpr ⟨y,member,accepted⟩))

inductive BaseTag where | first | second
deriving DecidableEq, Repr
inductive PathTag where | root | f | g | ff | fg | gf | gg
deriving DecidableEq, Repr
inductive TailTag where | exact | star | may | must
deriving DecidableEq, Repr
inductive MarkTag where | flow | t | u
deriving DecidableEq, Repr
structure ActualTag where
  base : BaseTag
  path : PathTag
  tail : TailTag
  mark : MarkTag
  support : Layer
deriving DecidableEq, Repr

def baseOf : BaseTag → Nat | .first => 1 | .second => 2
def pathOf : PathTag → List Acc
  | .root => [] | .f => [7] | .g => [8] | .ff => [7,7]
  | .fg => [7,8] | .gf => [8,7] | .gg => [8,8]
def markOf : MarkTag → Mark | .flow => .flow | .t => .full 11 | .u => .full 12

def actualOf (tag : ActualTag) : Actual :=
  let shape : RestrictedInitialPolicy.Shape :=
    match tag.tail with
    | .exact => .exact
    | .star => .star
    | .may => .any
    | .must => .any
  ⟨⟨baseOf tag.base,pathOf tag.path,shape,markOf tag.mark,
      match tag.tail with | .must => true | _ => false⟩,
    match tag.tail with | .may => .demand | _ => tag.support⟩

def allActualTags : List ActualTag :=
  [BaseTag.first,.second].flatMap fun b =>
  [PathTag.root,.f,.g,.ff,.fg,.gf,.gg].flatMap fun p =>
  [TailTag.exact,.star,.may,.must].flatMap fun t =>
  [MarkTag.flow,.t,.u].flatMap fun m =>
  [Layer.normal,.demand].map fun l => ⟨b,p,t,m,l⟩

theorem every_bounded_typed_actual_is_enumerated (tag : ActualTag) : tag ∈ allActualTags := by
  cases tag with
  | mk b p t m l =>
    unfold allActualTags
    apply List.mem_flatMap.mpr
    refine ⟨b,?_,?_⟩
    · cases b <;> simp
    · apply List.mem_flatMap.mpr
      refine ⟨p,?_,?_⟩
      · cases p <;> simp
      · apply List.mem_flatMap.mpr
        refine ⟨t,?_,?_⟩
        · cases t <;> simp
        · apply List.mem_flatMap.mpr
          refine ⟨m,?_,?_⟩
          · cases m <;> simp
          · apply List.mem_map.mpr
            exact ⟨l,by cases l <;> simp,rfl⟩

/-- The inverse has at most two PATTERN preimages. The remaining predicate
checks the actual supplied layer/loss support; it is not guessed from a key. -/
def inverseJointCell (oldEmitter : Input → Option Input) (wanted : Admission) (actual : Actual) : Bool :=
  anyBy (fun raw => decide (oldEmitter actual.fact = some raw) &&
    decide (admissionLayer wanted.initial actual.fact actual.layer = wanted.layer))
    (replacementPreimages wanted.initial)

theorem inverse_joint_cell_exactly_matches_emission
    (oldEmitter : Input → Option Input) (wanted : Admission) (actual : Actual) :
    inverseJointCell oldEmitter wanted actual = true ↔ emitJoint oldEmitter actual = some wanted := by
  rw [inverseJointCell,finite_search_has_explicit_witness]
  constructor
  · rintro ⟨raw,member,accepted⟩
    obtain ⟨emitted,layer⟩ := (Bool.and_eq_true _ _).mp accepted
    have rawEquation : oldEmitter actual.fact = some raw := of_decide_eq_true emitted
    have layerEquation : admissionLayer wanted.initial actual.fact actual.layer = wanted.layer :=
      of_decide_eq_true layer
    have initialEquation := every_listed_preimage_replaces_to_target raw wanted.initial member
    cases wanted with
    | mk initial selectedLayer =>
      simp only [emitJoint,rawEquation,Option.map_some,convertAdmission,initialEquation,layerEquation]
  · intro emitted
    cases rawEquation : oldEmitter actual.fact with
    | none => simp only [emitJoint,rawEquation,Option.map_none] at emitted; cases emitted
    | some raw =>
      have same : convertAdmission raw actual = wanted := by
        simpa only [emitJoint,rawEquation,Option.map_some,Option.some.injEq] using emitted
      rw [← same]
      exact ⟨raw,replacement_has_explicit_preimage raw,
        (Bool.and_eq_true _ _).mpr ⟨decide_eq_true rfl,decide_eq_true rfl⟩⟩

def canEmitJoint (oldEmitter : Input → Option Input) (wanted : Admission) : Bool :=
  anyBy (fun tag => inverseJointCell oldEmitter wanted (actualOf tag)) allActualTags

/-- Exact joint initial/layer image over the declared COMPLETE bounded actual
universe. The actual tag and its materialized support are executable witnesses. -/
theorem exact_joint_image_has_actual_and_layer_witness
    (oldEmitter : Input → Option Input) (wanted : Admission) :
    canEmitJoint oldEmitter wanted = true ↔
      ∃ tag : ActualTag, emitJoint oldEmitter (actualOf tag) = some wanted := by
  rw [canEmitJoint,finite_search_has_explicit_witness]
  constructor
  · rintro ⟨tag,_,accepted⟩
    exact ⟨tag,(inverse_joint_cell_exactly_matches_emission oldEmitter wanted _).mp accepted⟩
  · rintro ⟨tag,emitted⟩
    exact ⟨tag,every_bounded_typed_actual_is_enumerated tag,
      (inverse_joint_cell_exactly_matches_emission oldEmitter wanted _).mpr emitted⟩

theorem non_MAY_output_preserves_current_support
    (old : Input) (actual : Actual) (notMay : isMay old = false) :
    convertAdmission old actual = ⟨old,admissionLayer old actual.fact actual.layer⟩ := by
  cases old with
  | mk b p s m must =>
    cases s <;> cases must <;> simp [isMay,RestrictedInitialPolicy.shapeEq] at notMay
    all_goals rfl

theorem selected_layer_and_unrelated_EXACT_loss_cells :
    convertAdmission (atF .flow) ⟨atF T,.demand⟩ = ⟨starF .flow,.normal⟩ ∧
    convertAdmission (atF T) ⟨atF T,.demand⟩ = ⟨starF T,.demand⟩ ∧
    convertAdmission ⟨p,[f],.exact,T,false⟩ ⟨atF T,.normal⟩ =
      ⟨⟨p,[f],.exact,T,false⟩,.demand⟩ ∧
    convertAdmission ⟨p,[f],.any,T,true⟩ ⟨⟨p,[f],.any,T,true⟩,.demand⟩ =
      ⟨⟨p,[f],.any,T,true⟩,.demand⟩ := by decide

def mayAt (b : Nat) (path : List Acc) (m : Mark) : Input := ⟨b,path,.any,m,false⟩
def starAt (b : Nat) (path : List Acc) (m : Mark) : Input := ⟨b,path,.star,m,false⟩
def starLayer : Mark → Layer | .flow => .normal | .full _ => .demand

/-- Both native MAY-result cells, with the full witness path and unchanged mark
matching/budget. An earlier cut need not be exactly one field from the witness. -/
theorem current_MAY_prefixes_emit_the_same_witness
    (mode : Mode) (b : Nat) (prefixPath suffix : List Acc) (required supplied : Mark)
    (markMatches : RestrictedInitialPolicy.acceptsMark required supplied = true)
    (budget : (prefixPath ++ suffix).length ≤ mode.fieldLimit) :
    currentEmit mode ⟨b,prefixPath ++ suffix,required⟩ (mayAt b prefixPath supplied) =
      some (mayAt b (prefixPath ++ suffix) required) := by
  have prefixFits : prefixPath.length ≤ mode.fieldLimit := by
    simp only [List.length_append] at budget
    omega
  have ordinary : RestrictedInitialPolicy.emit (asDemand ⟨b,prefixPath ++ suffix,required⟩)
      (mayAt b prefixPath supplied) = some (mayAt b (prefixPath ++ suffix) required) := by
    cases suffix with
    | nil =>
      have same : dropPrefix prefixPath prefixPath = some [] := ApSpec.Handoff.RAux.dropPrefix_self' prefixPath
      simp [RestrictedInitialPolicy.emit,RestrictedInitialPolicy.selectTemplate,
        RestrictedInitialPolicy.rawTemplate,RestrictedInitialPolicy.validInput,
        RestrictedInitialPolicy.validTemplate,RestrictedInitialPolicy.render,
        RestrictedInitialPolicy.shapeEq,asDemand,mayAt,relate,same,markMatches]
    | cons field rest =>
      have below : dropPrefix prefixPath (prefixPath ++ field :: rest) = some (field :: rest) :=
        CoreAux.dropPrefix_some.mpr rfl
      have aboveNone : dropPrefix (prefixPath ++ field :: rest) prefixPath = none := by
        cases h : dropPrefix (prefixPath ++ field :: rest) prefixPath with
        | none => rfl
        | some tail =>
          have equation := CoreAux.dropPrefix_some.mp h
          have lengths := congrArg List.length equation
          simp only [List.length_append,List.length_cons] at lengths
          omega
      have relative := CoreAux.relate_above aboveNone below
      simp [RestrictedInitialPolicy.emit,RestrictedInitialPolicy.selectTemplate,
        RestrictedInitialPolicy.rawTemplate,RestrictedInitialPolicy.validInput,
        RestrictedInitialPolicy.validTemplate,RestrictedInitialPolicy.render,
        RestrictedInitialPolicy.shapeEq,asDemand,mayAt,relative,markMatches]
  have raw : RestrictedInitialPolicy.DemandStarPolicy.emit
      (asDemand ⟨b,prefixPath ++ suffix,required⟩) (mayAt b prefixPath supplied) =
      some (mayAt b (prefixPath ++ suffix) required) := by
    rw [RestrictedInitialPolicy.DemandStarPolicy.unchanged_outside_override _ _
      (ANY_demand_never_uses_STAR_demand_override _ _)]
    exact ordinary
  have bounded := RestrictedInitialPolicy.DemandStarPolicy.budget_emission_from_facts
    mode.fieldLimit (asDemand ⟨b,prefixPath ++ suffix,required⟩)
    (mayAt b prefixPath supplied) (mayAt b (prefixPath ++ suffix) required)
    budget prefixFits raw budget
  simp only [currentEmit,bounded]
  cases mode.direction <;> rfl

theorem selected_MAY_prefix_joint_result_is_constant
    (mode : Mode) (b : Nat) (prefixPath suffix : List Acc) (required supplied : Mark)
    (markMatches : RestrictedInitialPolicy.acceptsMark required supplied = true)
    (budget : (prefixPath ++ suffix).length ≤ mode.fieldLimit) :
    emitJoint (currentEmit mode ⟨b,prefixPath ++ suffix,required⟩)
      ⟨mayAt b prefixPath supplied,.demand⟩ =
      some ⟨starAt b (prefixPath ++ suffix) required,starLayer required⟩ := by
  rw [emitJoint,current_MAY_prefixes_emit_the_same_witness mode b prefixPath suffix required supplied markMatches budget]
  cases required <;> rfl

/-- Opaque complete label: it stands for the exact scope/family/original/exit
key, not an invitation to combine distinct labels or physical interfaces. -/
structure Label where
  scope : Nat
  family : Nat
  original : Nat
  exit : Nat
deriving DecidableEq, Repr

def labelledAnswer (label : Label) (answer : Option Admission) : Option (Label × Admission) :=
  answer.map (fun value => (label,value))

theorem certificate_comparison_keeps_label_and_answer_for_any_earlier_prefix
    (mode : Mode) (b : Nat) (path prefix1 suffix1 prefix2 suffix2 : List Acc)
    (required supplied : Mark) (label : Label)
    (same1 : path = prefix1 ++ suffix1) (same2 : path = prefix2 ++ suffix2)
    (markMatches : RestrictedInitialPolicy.acceptsMark required supplied = true)
    (budget : path.length ≤ mode.fieldLimit) :
    labelledAnswer label (emitJoint (currentEmit mode ⟨b,path,required⟩)
      ⟨mayAt b prefix1 supplied,.demand⟩) =
    labelledAnswer label (emitJoint (currentEmit mode ⟨b,path,required⟩)
      ⟨mayAt b prefix2 supplied,.demand⟩) := by
  have first := selected_MAY_prefix_joint_result_is_constant mode b prefix1 suffix1 required supplied markMatches
    (by simpa only [← same1] using budget)
  have second := selected_MAY_prefix_joint_result_is_constant mode b prefix2 suffix2 required supplied markMatches
    (by simpa only [← same2] using budget)
  rw [← same1] at first
  rw [← same2] at second
  rw [first,second]

def selectedCertificateGuard (witness : AnyDemand) (answer : Admission) : Bool :=
  decide (answer.initial.base = witness.base) && decide (answer.initial.path = witness.path) &&
    decide (answer.initial.mark = witness.mark) &&
    RestrictedInitialPolicy.shapeEq answer.initial.shape .star && !answer.initial.must &&
    decide (answer.layer = starLayer witness.mark)

theorem adapted_certificate_accepts_exact_selected_witness_only
    (b : Nat) (path : List Acc) (mark : Mark) :
    selectedCertificateGuard ⟨b,path,mark⟩ ⟨starAt b path mark,starLayer mark⟩ = true := by
  cases mark <;> simp [selectedCertificateGuard,starAt,starLayer,RestrictedInitialPolicy.shapeEq]

theorem certificate_negatives_and_old_STAR_actual_rejection :
    selectedCertificateGuard (d1 .flow) ⟨starF .flow,.demand⟩ = false ∧
    selectedCertificateGuard (d1 T) ⟨starF T,.normal⟩ = false ∧
    selectedCertificateGuard (d1 T) ⟨starAt p [g] T,.demand⟩ = false ∧
    candidateEmit forward1 (d1 .flow) (starF .flow) = none := by decide

def check : Bool :=
  canEmitJoint (currentEmit forward1 (d1 .flow)) ⟨starF .flow,.normal⟩ &&
  !canEmitJoint (currentEmit forward1 (d1 .flow)) ⟨starF .flow,.demand⟩ &&
  canEmitJoint (currentEmit forward1 (d1 T)) ⟨starF T,.demand⟩ &&
  !canEmitJoint (currentEmit forward1 (d1 T)) ⟨starF T,.normal⟩ &&
  canEmitJoint (currentEmit forward1 (d1 T)) ⟨⟨p,[f],.exact,T,false⟩,.normal⟩ &&
  canEmitJoint (currentEmit forward1 (d1 T)) ⟨⟨p,[f],.exact,T,false⟩,.demand⟩ &&
  selectedCertificateGuard (d1 .flow) ⟨starF .flow,.normal⟩

theorem executable_selected_full_joint_and_certificate_cells : check = true := by decide
#eval (if check then "SELECTED_FULL_JOINT=true" else "SELECTED_FULL_JOINT=false")

#print axioms finite_search_has_explicit_witness
#print axioms every_bounded_typed_actual_is_enumerated
#print axioms inverse_joint_cell_exactly_matches_emission
#print axioms exact_joint_image_has_actual_and_layer_witness
#print axioms non_MAY_output_preserves_current_support
#print axioms selected_layer_and_unrelated_EXACT_loss_cells
#print axioms current_MAY_prefixes_emit_the_same_witness
#print axioms selected_MAY_prefix_joint_result_is_constant
#print axioms certificate_comparison_keeps_label_and_answer_for_any_earlier_prefix
#print axioms adapted_certificate_accepts_exact_selected_witness_only
#print axioms certificate_negatives_and_old_STAR_actual_rejection
#print axioms executable_selected_full_joint_and_certificate_cells

end SelectedFullAdmission
