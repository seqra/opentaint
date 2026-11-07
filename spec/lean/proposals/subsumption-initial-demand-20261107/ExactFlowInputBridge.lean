/-
Prepared native-domain bridge. The checked 47-law C2 component is unchanged.
Native FLOW/EXACT actuals may carry field E after an ordinary strong write.
EXACT does not inspect that E to reach a descendant: it cannot reach one.
Only the pure C2 computation view resets that one E coordinate. The actual
kept by call binding is never replaced by the view.

This extends a formal input domain to existing native behavior. It does not
change field transfer, layers, marks, H, source/Target rules or normalization.
No ANY initial or new tail is added. FULL scalar scope; the JVM static-anchor,
catalog and packed representation adapters keep their separate obligations.
-/
import RelativeAdmission

namespace ExactFlowInputBridge
open PlainStarRelativeAdmission
open ApSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

def nativeLegalActual (mode : Mode) (a : Actual) : Prop :=
  a.pattern.path.length ≤ mode.limit ∧
    match a.pattern.tail,a.pattern.mark with
    | .exact,.flow => True
    | .exact,.full _ => a.pattern.exclusion = []
    | .any,_ => a.pattern.exclusion = [] ∧ a.layer = .demand
    | .star,.full _ => a.layer = .demand
    | _,_ => True
instance (mode : Mode) (a : Actual) : Decidable (nativeLegalActual mode a) := by
  unfold nativeLegalActual
  cases a.pattern.tail <;> cases a.pattern.mark <;> infer_instance

def queryView (a : Actual) : Actual :=
  match a.pattern.tail,a.pattern.mark with
  | .exact,.flow => {a with pattern := {a.pattern with exclusion := []}}
  | _,_ => a

@[simp] theorem queryView_base (a : Actual) : (queryView a).pattern.base = a.pattern.base := by
  cases a with | mk p l h => cases p with | mk b path t m e => cases t <;> cases m <;> rfl
@[simp] theorem queryView_path (a : Actual) : (queryView a).pattern.path = a.pattern.path := by
  cases a with | mk p l h => cases p with | mk b path t m e => cases t <;> cases m <;> rfl
@[simp] theorem queryView_tail (a : Actual) : (queryView a).pattern.tail = a.pattern.tail := by
  cases a with | mk p l h => cases p with | mk b path t m e => cases t <;> cases m <;> rfl
@[simp] theorem queryView_mark (a : Actual) : (queryView a).pattern.mark = a.pattern.mark := by
  cases a with | mk p l h => cases p with | mk b path t m e => cases t <;> cases m <;> rfl
@[simp] theorem queryView_layer (a : Actual) : (queryView a).layer = a.layer := by
  cases a with | mk p l h => cases p with | mk b path t m e => cases t <;> cases m <;> rfl
@[simp] theorem queryView_H (a : Actual) : (queryView a).hasProtection = a.hasProtection := by
  cases a with | mk p l h => cases p with | mk b path t m e => cases t <;> cases m <;> rfl
theorem queryView_is_idempotent (a : Actual) : queryView (queryView a) = queryView a := by
  cases a with | mk p l h => cases p with | mk b path t m e => cases t <;> cases m <;> rfl

theorem old_legal_view_iff_native_legal (mode : Mode) (a : Actual) :
    legalActual mode (queryView a) ↔ nativeLegalActual mode a := by
  cases a with
  | mk p l h =>
    cases p with
    | mk b path t m e => cases t <;> cases m <;> simp [queryView,legalActual,nativeLegalActual]

theorem queryView_is_identity_on_old_domain (mode : Mode) (a : Actual)
    (legal : legalActual mode a) : queryView a = a := by
  cases a with
  | mk p l h =>
    cases p with
    | mk b path t m e => cases t <;> cases m <;> simp_all [queryView,legalActual]

theorem old_legal_is_native_legal (mode : Mode) (a : Actual) (legal : legalActual mode a) :
    nativeLegalActual mode a := by
  apply (old_legal_view_iff_native_legal mode a).mp
  simpa only [queryView_is_identity_on_old_domain mode a legal] using legal

/-- This is exactly the old table body, with its actual-domain guard factored
out. It gives a direct geometry statement rather than using an assumed native
equivalence theorem. No actual H/layer is read by this geometric table. -/
def geometryTable (mode : Mode) (d : Demand) (a : Actual) : Option Template :=
  match d.shape,relate d.path a.pattern.path with
  | .any,.below [] =>
      match a.pattern.tail with
      | .exact => some .rootExact
      | .star | .any => some .rootStar
      | .must => some (.rootMust a.pattern.exclusion)
  | .any,.below (f::rest) =>
      if concrete d.mark && decide (a.pattern.tail = .exact) && rest.isEmpty
      then some (.childExact f) else some (.childStar f)
  | .star,.below (f::rest) =>
      if demandAdmits d (f::rest) && decide (mode.run = 2) then some .rootStar else none
  | .exact,.below (_::_) => none
  | .any,.above rest =>
      if tailAdmits a.pattern.tail a.pattern.exclusion rest then
        match a.pattern.tail with
        | .any => some .rootStar
        | .must => some (.rootMust (demandE d))
        | _ => none
      else none
  | _,.above rest =>
      if tailAdmits a.pattern.tail a.pattern.exclusion rest then some .rootExact else none
  | _,.below [] => some .rootExact
  | _,.apart => none

theorem old_table_is_guarded_geometry (mode : Mode) (d : Demand) (a : Actual) :
    table mode d a = if commonLegal mode d a then geometryTable mode d a else none := rfl

theorem native_geometry_ignores_only_FLOW_EXACT_actual_E (mode : Mode) (d : Demand) (a : Actual) :
    geometryTable mode d (queryView a) = geometryTable mode d a := by
  cases a with
  | mk p l h =>
    cases p with
    | mk b path t m e => cases t <;> cases m <;> rfl

theorem EXACT_ancestor_still_cannot_reach_a_deeper_demand
    (mode : Mode) (d : Demand) (base : Nat) (path e : List Nat) (layer : Layer)
    (h : Bool) (field : Nat) (rest : List Nat)
    (position : relate d.path path = .above (field::rest)) :
    geometryTable mode d ⟨⟨base,path,.exact,.flow,e⟩,layer,h⟩ = none := by
  cases shapeIs : d.shape <;> simp [geometryTable,shapeIs,position,tailAdmits]

def nativeCommonLegal (mode : Mode) (d : Demand) (a : Actual) : Prop :=
  mode.run ≥ 2 ∧ mode.limit ≥ 1 ∧ validDemand d ∧ d.path.length ≤ mode.limit ∧
    nativeLegalActual mode a ∧ d.base = a.pattern.base ∧
    RestrictedInitialPolicy.acceptsMark d.mark a.pattern.mark = true ∧
    ¬ (d.shape = .exact ∧ d.mark = .flow ∧ a.pattern.tail = .any)
instance (mode : Mode) (d : Demand) (a : Actual) : Decidable (nativeCommonLegal mode d a) := by
  unfold nativeCommonLegal
  infer_instance

theorem common_legal_query_iff_native (mode : Mode) (d : Demand) (a : Actual) :
    commonLegal mode d (queryView a) ↔ nativeCommonLegal mode d a := by
  simp only [commonLegal,nativeCommonLegal,queryView_base,queryView_mark,queryView_tail,
    old_legal_view_iff_native_legal]

def nativeTable (mode : Mode) (d : Demand) (a : Actual) : Option Template :=
  if nativeCommonLegal mode d a then geometryTable mode d a else none
theorem native_table_is_old_query_table (mode : Mode) (d : Demand) (a : Actual) :
    nativeTable mode d a = table mode d (queryView a) := by
  simp only [nativeTable,old_table_is_guarded_geometry,common_legal_query_iff_native,
    native_geometry_ignores_only_FLOW_EXACT_actual_E]

def nativeSelected (mode : Mode) (d : Demand) (a : Actual) : Option Template :=
  match nativeTable mode d a with
  | none => none
  | some t => if Allowed mode d t then some t else none
theorem selected_table_is_unchanged_geometry (mode : Mode) (d : Demand) (a : Actual) :
    nativeSelected mode d a = selected mode d (queryView a) := by
  simp only [nativeSelected,selected,native_table_is_old_query_table]
  rfl

theorem admission_layer_is_unchanged (initial : Pattern) (a : Actual) :
    admissionLayer initial (queryView a) = admissionLayer initial a := by
  simp only [admissionLayer,queryView_layer,queryView_tail]

def nativeEmitByTable (mode : Mode) (d : Demand) (a : Actual) : Option Seed :=
  (nativeSelected mode d a).map fun t => ⟨render d t,admissionLayer (render d t) a⟩
theorem native_table_emitter_is_old_query_emitter (mode : Mode) (d : Demand) (a : Actual) :
    nativeEmitByTable mode d a = emit mode d (queryView a) := by
  simp only [nativeEmitByTable,emit,selected_table_is_unchanged_geometry,admission_layer_is_unchanged]

theorem old_emitter_rejects_illegal_actual (mode : Mode) (d : Demand) (a : Actual)
    (illegal : ¬ legalActual mode a) : emit mode d a = none := by
  simp [emit,selected,table,commonLegal,illegal]
theorem old_emission_has_legal_actual (mode : Mode) (d : Demand) (a : Actual) (seed : Seed)
    (emitted : emit mode d a = some seed) : legalActual mode a := by
  by_cases legal : legalActual mode a
  · exact legal
  · rw [old_emitter_rejects_illegal_actual mode d a legal] at emitted
    cases emitted

def nativeEmit (mode : Mode) (d : Demand) (a : Actual) : Option Seed :=
  if nativeLegalActual mode a then emit mode d (queryView a) else none
theorem native_emit_is_old_query_emit (mode : Mode) (d : Demand) (a : Actual) :
    nativeEmit mode d a = emit mode d (queryView a) := by
  by_cases legal : nativeLegalActual mode a
  · simp only [nativeEmit,if_pos legal]
  · have illegalOld : ¬ legalActual mode (queryView a) :=
      fun old => legal ((old_legal_view_iff_native_legal mode a).mp old)
    simp only [nativeEmit,if_neg legal,old_emitter_rejects_illegal_actual mode d (queryView a) illegalOld]
theorem native_emit_is_geometry_table_emit (mode : Mode) (d : Demand) (a : Actual) :
    nativeEmit mode d a = nativeEmitByTable mode d a := by
  rw [native_emit_is_old_query_emit,native_table_emitter_is_old_query_emitter]
theorem native_emit_preserves_old_legal_behavior (mode : Mode) (d : Demand) (a : Actual)
    (legal : legalActual mode a) : nativeEmit mode d a = emit mode d a := by
  rw [native_emit_is_old_query_emit,queryView_is_identity_on_old_domain mode a legal]

theorem raw_image_has_same_native_actual_witnesses (mode : Mode) (d : Demand) (initial : Pattern) :
    rawImage mode d initial = true ↔
      ∃ a seed, nativeEmit mode d a = some seed ∧ seed.initial = initial := by
  constructor
  · intro present
    obtain ⟨actual,found,legal,emitted⟩ := raw_image_supplies_actual_witness mode d initial present
    exact ⟨actual,⟨initial,intrinsic initial⟩,
      by rw [native_emit_preserves_old_legal_behavior mode d actual legal]; exact emitted,rfl⟩
  · rintro ⟨actual,seed,emitted,same⟩
    rw [native_emit_is_old_query_emit] at emitted
    rw [← same]
    exact arbitrary_actual_emission_is_in_raw_image mode d (queryView actual) seed emitted

theorem joint_image_has_same_native_actual_witnesses (mode : Mode) (d : Demand) (seed : Seed) :
    jointImage mode d seed = true ↔ ∃ a, nativeEmit mode d a = some seed := by
  constructor
  · intro present
    obtain ⟨actual,found,legal,emitted⟩ := joint_image_has_executable_actual_witness mode d seed present
    exact ⟨actual,by rw [native_emit_preserves_old_legal_behavior mode d actual legal]; exact emitted⟩
  · rintro ⟨actual,emitted⟩
    apply (joint_image_exactly_characterizes_arbitrary_admission mode d seed).mpr
    exact ⟨queryView actual,by simpa only [native_emit_is_old_query_emit] using emitted⟩

theorem normalized_C5_image_has_same_native_witnesses (mode : Mode) (d : Demand) (stored : Pattern) :
    canStoreInitial mode d stored = true ↔
      ∃ actual seed, nativeEmit mode d actual = some seed ∧
        publicInitial seed.initial = stored ∧ insideDemand d seed.initial = true := by
  constructor
  · intro permitted
    obtain ⟨witness,found,legal,emitted,normal,inside⟩ :=
      C5_permission_has_executable_raw_actual_witness mode d stored permitted
    exact ⟨witness.actual,⟨witness.rawInitial,intrinsic witness.rawInitial⟩,
      by rw [native_emit_preserves_old_legal_behavior mode d witness.actual legal]; exact emitted,
      normal,inside⟩
  · rintro ⟨actual,seed,emitted,normal,inside⟩
    apply (C5_permission_iff_normalized_actual_emission mode d stored).mpr
    exact ⟨queryView actual,seed,
      by simpa only [native_emit_is_old_query_emit] using emitted,normal,inside⟩

theorem native_emission_has_the_same_base_mark_budget_and_no_ANY
    (mode : Mode) (d : Demand) (a : Actual) (seed : Seed)
    (emitted : nativeEmit mode d a = some seed) :
    seed.initial.base = d.base ∧ seed.initial.mark = d.mark ∧
    seed.initial.path.length ≤ mode.limit ∧ seed.initial.tail ≠ .any ∧
    (seed.initial.path = d.path ∨ ∃ field, seed.initial.path = d.path ++ [field]) := by
  rw [native_emit_is_old_query_emit] at emitted
  exact raw_image_preserves_base_mark_budget_and_has_no_ANY mode d seed.initial
    (arbitrary_actual_emission_is_in_raw_image mode d (queryView a) seed emitted)
theorem initial_identity_start_and_its_new_H_are_unchanged (seed : Seed) :
    (start seed).pattern = seed.initial ∧ (start seed).hasProtection = false := ⟨rfl,rfl⟩
theorem unchanged_C5_permission_keeps_output_layer_and_H
    (mode : Mode) (d : Demand) (stored : Pattern) (output : Output)
    (permitted : canStoreInitial mode d stored = true) :
    acceptOutput mode d stored output = some output :=
  C5_entry_permission_preserves_supplied_output_and_H mode d stored output permitted

/-- Execution carries the original actual alongside its query command; it
does not replace the supplied data by the E-erased computation view. -/
structure Command where
  seed : Seed
  submitted : Actual
  deriving DecidableEq, Repr
def nativeCommand (mode : Mode) (d : Demand) (a : Actual) : Option Command :=
  (nativeEmit mode d a).map fun seed => ⟨seed,a⟩
theorem bound_submitted_actual_is_literal_original
    (mode : Mode) (d : Demand) (a : Actual) (command : Command)
    (produced : nativeCommand mode d a = some command) : command.submitted = a := by
  unfold nativeCommand at produced
  cases chosen : nativeEmit mode d a with
  | none => simp [chosen] at produced
  | some seed =>
      have same : (⟨seed,a⟩ : Command) = command := by simpa [chosen] using produced
      exact congrArg Command.submitted same.symm
theorem original_E_layer_mark_H_are_not_rewritten
    (mode : Mode) (d : Demand) (a : Actual) (command : Command)
    (produced : nativeCommand mode d a = some command) :
    command.submitted.pattern.exclusion = a.pattern.exclusion ∧
    command.submitted.layer = a.layer ∧ command.submitted.pattern.mark = a.pattern.mark ∧
    command.submitted.hasProtection = a.hasProtection := by
  rw [bound_submitted_actual_is_literal_original mode d a command produced]
  exact ⟨rfl,rfl,rfl,rfl⟩
theorem concrete_EXACT_nonempty_E_is_still_rejected
    (mode : Mode) (d : Demand) (base : Nat) (path e : List Nat) (mark : Nat) (layer : Layer)
    (h : Bool) (notEmpty : e ≠ []) :
    nativeEmit mode d ⟨⟨base,path,.exact,.full mark,e⟩,layer,h⟩ = none := by
  simp [nativeEmit,nativeLegalActual,notEmpty]

/- Reachable native state, not a fabricated initial: ANY/FLOW plus exact T
emits p.$/FLOW,N; existing strong write p.f=null adds E={f} to that raw FLOW
EXACT conclusion. Ordinary bind-in preserves E. The new formal bridge admits
this existing native input and keeps it in the actual command unchanged. -/
def forwardMode : Mode := ⟨3,2,.forward⟩
def outerDemand : Demand := ⟨0,[],.any,.flow,[]⟩
def actualRootT : Actual := ⟨⟨0,[],.exact,.full 7,[]⟩,.normal,false⟩
def exactFlowSeed : Seed := ⟨⟨0,[],.exact,.flow,[]⟩,.normal⟩
def existingStrongWrite (input : Actual) : Actual :=
  {input with pattern := {input.pattern with exclusion := input.pattern.exclusion ++ [5]}}
def written : Actual := existingStrongWrite (start exactFlowSeed)
def boundInput : Actual := {written with pattern := {written.pattern with base := 1}}
def innerDemand : Demand := ⟨1,[],.any,.flow,[]⟩
def innerSeed : Seed := ⟨⟨1,[],.exact,.flow,[]⟩,.normal⟩

theorem scenario_initial_is_emitted_from_real_exact_T :
    nativeEmit forwardMode outerDemand actualRootT = some exactFlowSeed := by decide
theorem scenario_existing_strong_write_keeps_raw_EXACT_E :
    boundInput = ⟨⟨1,[],.exact,.flow,[5]⟩,.normal,false⟩ := by decide
theorem scenario_old_formal_domain_did_not_cover_the_input :
    emit forwardMode innerDemand boundInput = none := by decide
theorem scenario_native_query_admits_but_binding_retains_E :
    nativeCommand forwardMode innerDemand boundInput =
      some ⟨innerSeed,⟨⟨1,[],.exact,.flow,[5]⟩,.normal,false⟩⟩ := by decide

#print axioms queryView_is_idempotent
#print axioms old_legal_view_iff_native_legal
#print axioms queryView_is_identity_on_old_domain
#print axioms old_legal_is_native_legal
#print axioms old_table_is_guarded_geometry
#print axioms native_geometry_ignores_only_FLOW_EXACT_actual_E
#print axioms EXACT_ancestor_still_cannot_reach_a_deeper_demand
#print axioms common_legal_query_iff_native
#print axioms native_table_is_old_query_table
#print axioms selected_table_is_unchanged_geometry
#print axioms admission_layer_is_unchanged
#print axioms native_table_emitter_is_old_query_emitter
#print axioms old_emitter_rejects_illegal_actual
#print axioms old_emission_has_legal_actual
#print axioms native_emit_is_old_query_emit
#print axioms native_emit_is_geometry_table_emit
#print axioms native_emit_preserves_old_legal_behavior
#print axioms raw_image_has_same_native_actual_witnesses
#print axioms joint_image_has_same_native_actual_witnesses
#print axioms normalized_C5_image_has_same_native_witnesses
#print axioms native_emission_has_the_same_base_mark_budget_and_no_ANY
#print axioms initial_identity_start_and_its_new_H_are_unchanged
#print axioms unchanged_C5_permission_keeps_output_layer_and_H
#print axioms bound_submitted_actual_is_literal_original
#print axioms original_E_layer_mark_H_are_not_rewritten
#print axioms concrete_EXACT_nonempty_E_is_still_rejected
#print axioms scenario_initial_is_emitted_from_real_exact_T
#print axioms scenario_existing_strong_write_keeps_raw_EXACT_E
#print axioms scenario_old_formal_domain_did_not_cover_the_input
#print axioms scenario_native_query_admits_but_binding_retains_E

end ExactFlowInputBridge
