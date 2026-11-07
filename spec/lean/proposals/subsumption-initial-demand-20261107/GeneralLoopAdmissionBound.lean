/-
Prepared reusable C2 key-bound component, not a new loop/runtime policy.
The entire labelled DATA query is bounded, not one chosen row. Any emitted
key is at most max(demand-head depth, actual depth). A real next field below
a longest ANY/FLOW head emits a depth h+1 STAR key; no coarse actual of depth
at most h can reproduce that key from ANY other query family with heads <=h.

The checked native EXACT/FLOW/E bridge preserves actual path depth. Class
anchors and named-static grammar need the existing counted-path adapter.
Key distinguishability alone does not prove delivery, source permission or
termination; complete scope/port and normal-record continuation remain.

The final E07 subdomain is a genuine root/child uniform packet. It drops the
ordinary redundant child BEFORE C2, derives a NORMAL MUST identity by return,
and preserves an arbitrary full mark at a return field. No child history or
invented NORMAL STAR relation is used. It is not a general context theorem.
-/
import ExactFlowInputBridge

namespace GeneralLoopAdmissionBound
open PlainStarRelativeAdmission
open ExactFlowInputBridge
open ApSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

theorem geometric_key_depth_bound (mode : Mode) (d : Demand) (a : Actual) (t : Template)
    (chosen : geometryTable mode d a = some t) :
    (render d t).path.length ≤ max d.path.length a.pattern.path.length := by
  cases position : relate d.path a.pattern.path with
  | below suffix =>
    cases suffix with
    | nil =>
      cases shapeIs : d.shape <;> cases tailIs : a.pattern.tail <;>
        simp only [geometryTable,shapeIs,position,tailIs] at chosen
      all_goals
        cases chosen
        simpa only [render] using Nat.le_max_left d.path.length a.pattern.path.length
    | cons field rest =>
      have actualPath := CoreAux.relate_below_inv position
      have enough : d.path.length + 1 ≤ a.pattern.path.length := by
        rw [actualPath]
        simp only [List.length_append,List.length_cons]
        omega
      cases t <;> simp only [render,List.length_append,List.length_singleton]
      all_goals omega
  | above suffix =>
    cases shapeIs : d.shape <;> cases tailIs : a.pattern.tail <;>
      simp only [geometryTable,shapeIs,position,tailIs] at chosen
    all_goals
      first
      | (split at chosen <;> cases chosen)
      | cases chosen
    all_goals
      simpa only [render] using Nat.le_max_left d.path.length a.pattern.path.length
  | apart =>
    cases shapeIs : d.shape <;> simp [geometryTable,shapeIs,position] at chosen

theorem selected_has_same_table_result (mode : Mode) (d : Demand) (a : Actual) (t : Template)
    (chosen : selected mode d a = some t) : table mode d a = some t := by
  unfold selected at chosen
  cases produced : table mode d a with
  | none => simp [produced] at chosen
  | some candidate =>
    rw [produced] at chosen
    by_cases allowed : Allowed mode d candidate
    · simp only [if_pos allowed,Option.some.injEq] at chosen
      exact chosen ▸ rfl
    · simp [allowed] at chosen

theorem raw_C2_key_depth_bound (mode : Mode) (d : Demand) (a : Actual) (seed : Seed)
    (emitted : emit mode d a = some seed) :
    seed.initial.path.length ≤ max d.path.length a.pattern.path.length := by
  cases selectedIs : selected mode d a with
  | none => simp [emit,selectedIs] at emitted
  | some t =>
    have same : (⟨render d t,admissionLayer (render d t) a⟩ : Seed) = seed := by
      simpa only [emit,selectedIs,Option.map_some,Option.some.injEq] using emitted
    have fromTable := selected_has_same_table_result mode d a t selectedIs
    rw [old_table_is_guarded_geometry] at fromTable
    split at fromTable
    next =>
      rw [← same]
      exact geometric_key_depth_bound mode d a t fromTable
    next => cases fromTable

theorem native_C2_key_depth_bound (mode : Mode) (d : Demand) (a : Actual) (seed : Seed)
    (emitted : nativeEmit mode d a = some seed) :
    seed.initial.path.length ≤ max d.path.length a.pattern.path.length := by
  rw [native_emit_is_old_query_emit] at emitted
  have bound := raw_C2_key_depth_bound mode d (queryView a) seed emitted
  simpa only [queryView_path] using bound

theorem public_normalization_keeps_key_depth (raw : Pattern) :
    (publicInitial raw).path.length = raw.path.length := by
  cases raw with | mk b path t m e => cases t <;> cases m <;> rfl
theorem native_public_key_depth_bound (mode : Mode) (d : Demand) (a : Actual) (seed : Seed)
    (emitted : nativeEmit mode d a = some seed) :
    (publicInitial seed.initial).path.length ≤ max d.path.length a.pattern.path.length := by
  rw [public_normalization_keeps_key_depth]
  exact native_C2_key_depth_bound mode d a seed emitted

universe u
structure Query (Label : Type u) where
  family : Label
  entry : Demand
structure Command (Label : Type u) where
  family : Label
  seed : Seed

/-- Label is the existing entire scope/family/port key. No runtime origin
bit or new fact equality coordinate is proposed by this parametric wrapper. -/
def commands {Label : Type u} (mode : Mode) (query : List (Query Label)) (a : Actual) :
    List (Command Label) :=
  query.filterMap fun row => (nativeEmit mode row.entry a).map fun seed => ⟨row.family,seed⟩

theorem each_command_keeps_a_real_query_family {Label : Type u}
    (mode : Mode) (query : List (Query Label)) (a : Actual) (command : Command Label)
    (member : command ∈ commands mode query a) :
    ∃ row, row ∈ query ∧ ∃ seed,
      nativeEmit mode row.entry a = some seed ∧ command.family = row.family ∧ command.seed = seed := by
  obtain ⟨row,present,produced⟩ := List.mem_filterMap.mp member
  cases emitted : nativeEmit mode row.entry a with
  | none => simp [emitted] at produced
  | some seed =>
    have same : (⟨row.family,seed⟩ : Command Label) = command := by simpa only [emitted,Option.map_some,Option.some.injEq] using produced
    exact ⟨row,present,seed,emitted,(congrArg Command.family same).symm,(congrArg Command.seed same).symm⟩

theorem ALL_cut_commands_are_bounded_by_the_entire_query {Label : Type u}
    (mode : Mode) (query : List (Query Label)) (a : Actual) (h : Nat)
    (allHeads : ∀ row ∈ query, row.entry.path.length ≤ h)
    (coarse : a.pattern.path.length ≤ h) (command : Command Label)
    (member : command ∈ commands mode query a) : command.seed.initial.path.length ≤ h := by
  obtain ⟨row,present,seed,emitted,labelSame,seedSame⟩ :=
    each_command_keeps_a_real_query_family mode query a command member
  rw [seedSame]
  exact Nat.le_trans (native_C2_key_depth_bound mode row.entry a seed emitted)
    (Nat.max_le.mpr ⟨allHeads row present,coarse⟩)

def fineDemand (base : Nat) (head : List Nat) : Demand := ⟨base,head,.any,.flow,[]⟩
def fineActual (base : Nat) (head : List Nat) (field mark : Nat) : Actual :=
  ⟨⟨base,head ++ [field],.exact,.full mark,[]⟩,.normal,false⟩
def fineSeed (base : Nat) (head : List Nat) (field : Nat) : Seed :=
  ⟨⟨base,head ++ [field],.star,.flow,[]⟩,.normal⟩

theorem fine_first_field_emits_a_real_deeper_STAR_key
    (mode : Mode) (base : Nat) (head : List Nat) (field mark : Nat)
    (restricted : 2 ≤ mode.run) (fits : head.length+1 ≤ mode.limit) :
    nativeEmit mode (fineDemand base head) (fineActual base head field mark) =
      some (fineSeed base head field) := by
  have positive : 1 ≤ mode.limit := by omega
  have headFits : head.length ≤ mode.limit := by omega
  rw [native_emit_is_old_query_emit]
  simp [emit,selected,table,commonLegal,validDemand,legalActual,Allowed,queryView,
    fineDemand,fineActual,fineSeed,one_child_relation,render,admissionLayer,intrinsic,
    RestrictedInitialPolicy.acceptsMark,concrete,restricted,fits,positive,headFits]

theorem fine_key_depth_is_h_plus_one (base : Nat) (head : List Nat) (field : Nat) :
    (fineSeed base head field).initial.path.length = head.length+1 := by
  simp [fineSeed]

theorem fine_command_is_present_with_its_own_label {Label : Type u}
    (mode : Mode) (query : List (Query Label)) (label : Label)
    (base : Nat) (head : List Nat) (field mark : Nat)
    (restricted : 2 ≤ mode.run) (fits : head.length+1 ≤ mode.limit)
    (present : (⟨label,fineDemand base head⟩ : Query Label) ∈ query) :
    (⟨label,fineSeed base head field⟩ : Command Label) ∈
      commands mode query (fineActual base head field mark) := by
  apply List.mem_filterMap.mpr
  refine ⟨⟨label,fineDemand base head⟩,present,?_⟩
  simp only [fine_first_field_emits_a_real_deeper_STAR_key mode base head field mark restricted fits,Option.map_some]

theorem NO_cut_from_ANY_other_family_reproduces_the_fine_key {Label : Type u}
    (mode : Mode) (query : List (Query Label)) (a : Actual)
    (base : Nat) (head : List Nat) (field : Nat)
    (allHeads : ∀ row ∈ query, row.entry.path.length ≤ head.length)
    (coarse : a.pattern.path.length ≤ head.length) (command : Command Label)
    (member : command ∈ commands mode query a) :
    command.seed.initial ≠ (fineSeed base head field).initial := by
  intro same
  have bound := ALL_cut_commands_are_bounded_by_the_entire_query mode query a head.length
    allHeads coarse command member
  rw [same,fine_key_depth_is_h_plus_one] at bound
  omega

/- E07 identity subdomain. Ordinary compatible MUST atoms only, fixed complete
origin, Empty E and no H. This reference is the selected native prefix law in
that cell; it is not a replacement for all packed/flagged canonicalization. -/
def rootActual (mark : Nat) : Actual := ⟨⟨0,[],.must,.full mark,[]⟩,.normal,false⟩
def childActual (mark field : Nat) : Actual := ⟨⟨0,[field],.must,.full mark,[]⟩,.normal,false⟩
def mustCovers (left right : Actual) : Bool :=
  decide (left.pattern.base = right.pattern.base ∧ left.pattern.mark = right.pattern.mark ∧
    left.layer = right.layer ∧ left.pattern.tail = .must ∧ right.pattern.tail = .must ∧
    left.pattern.exclusion = [] ∧ right.pattern.exclusion = [] ∧
    left.hasProtection = false ∧ right.hasProtection = false ∧
    left.pattern.path.IsPrefix right.pattern.path)
def admitUniform (state : List Actual) (offered : Actual) : List Actual :=
  if state.any (fun old => mustCovers old offered) then state
  else offered :: state.filter (fun old => !mustCovers offered old)
def canonicalPacket (packet : List Actual) : List Actual := packet.foldl admitUniform []

theorem E07_root_then_child_is_root (mark field : Nat) :
    canonicalPacket [rootActual mark,childActual mark field] = [rootActual mark] := by
  simp [canonicalPacket,admitUniform,mustCovers,rootActual,childActual]
theorem E07_child_then_root_is_root (mark field : Nat) :
    canonicalPacket [childActual mark field,rootActual mark] = [rootActual mark] := by
  simp [canonicalPacket,admitUniform,mustCovers,rootActual,childActual]

def rootDemand : Demand := ⟨0,[],.any,.flow,[]⟩
def uniformSeed : Seed := ⟨⟨0,[],.must,.flow,[]⟩,.normal⟩
def forwardMode : Mode := ⟨3,1,.forward⟩
def emitCanonical (packet : List Actual) : List Seed :=
  (canonicalPacket packet).filterMap (nativeEmit forwardMode rootDemand)
theorem E07_only_root_MUST_initial_is_emitted (mark field : Nat) :
    emitCanonical [rootActual mark,childActual mark field] = [uniformSeed] := by
  unfold emitCanonical
  rw [E07_root_then_child_is_root]
  simp [native_emit_is_old_query_emit,queryView,emit,selected,table,commonLegal,validDemand,
    legalActual,Allowed,rootActual,rootDemand,forwardMode,uniformSeed,
    render,admissionLayer,intrinsic,RestrictedInitialPolicy.acceptsMark,relate,dropPrefix]
theorem E07_child_first_emits_the_same_initial (mark field : Nat) :
    emitCanonical [childActual mark field,rootActual mark] = [uniformSeed] := by
  have same : emitCanonical [childActual mark field,rootActual mark] =
      emitCanonical [rootActual mark,childActual mark field] := by
    unfold emitCanonical
    rw [E07_child_then_root_is_root,E07_root_then_child_is_root]
  exact same.trans (E07_only_root_MUST_initial_is_emitted mark field)

structure UniformRelation where
  initial : Pattern
  output : Actual
  deriving DecidableEq, Repr
def inferIdentity (seed : Seed) : UniformRelation :=
  ⟨seed.initial,{start seed with pattern := {(start seed).pattern with base := 1}}⟩
def inferredUniformIdentity : UniformRelation := inferIdentity uniformSeed
def applyUniformIdentity (row : UniformRelation) (actual : Actual) : Option Actual :=
  if row.initial.base = actual.pattern.base ∧ row.initial.tail = .must ∧
      actual.pattern.tail = .must ∧ actual.pattern.path = [] ∧
      actual.pattern.exclusion = [] ∧
      RestrictedInitialPolicy.acceptsMark row.initial.mark actual.pattern.mark = true then
    some ⟨{row.output.pattern with mark := actual.pattern.mark},
      joinLayer row.output.layer actual.layer,actual.hasProtection || row.output.hasProtection⟩
  else none
def normalFieldWitness (field mark : Nat) (actual : Actual) : Bool :=
  decide (actual.pattern.base = 1 ∧ actual.pattern.mark = .full mark ∧
    actual.pattern.tail = .must ∧ actual.layer = .normal) &&
    tailAdmits actual.pattern.tail actual.pattern.exclusion [field]

theorem E07_identity_is_inferred_from_MUST_not_STAR :
    inferredUniformIdentity.initial.tail = .must ∧
    inferredUniformIdentity.output.pattern.tail = .must ∧
    inferredUniformIdentity.output.layer = .normal := by decide
theorem E07_arbitrary_full_mark_field_finding_survives (mark field : Nat) :
    ((applyUniformIdentity inferredUniformIdentity (rootActual mark)).map
      (normalFieldWitness field mark)).getD false = true := by
  simp [applyUniformIdentity,inferredUniformIdentity,inferIdentity,uniformSeed,start,
    rootActual,normalFieldWitness,tailAdmits,Excl.admits,memB,joinLayer,intrinsic,
    RestrictedInitialPolicy.acceptsMark]
theorem E07_requires_definite_MUST_not_ordinary_STAR (mark : Nat) :
    applyUniformIdentity inferredUniformIdentity {rootActual mark with
      pattern := {(rootActual mark).pattern with tail := .star},layer := .demand} = none := by
  simp [applyUniformIdentity,inferredUniformIdentity,inferIdentity,uniformSeed,start,rootActual]

#print axioms geometric_key_depth_bound
#print axioms selected_has_same_table_result
#print axioms raw_C2_key_depth_bound
#print axioms native_C2_key_depth_bound
#print axioms public_normalization_keeps_key_depth
#print axioms native_public_key_depth_bound
#print axioms each_command_keeps_a_real_query_family
#print axioms ALL_cut_commands_are_bounded_by_the_entire_query
#print axioms fine_first_field_emits_a_real_deeper_STAR_key
#print axioms fine_key_depth_is_h_plus_one
#print axioms fine_command_is_present_with_its_own_label
#print axioms NO_cut_from_ANY_other_family_reproduces_the_fine_key
#print axioms E07_root_then_child_is_root
#print axioms E07_child_then_root_is_root
#print axioms E07_only_root_MUST_initial_is_emitted
#print axioms E07_child_first_emits_the_same_initial
#print axioms E07_identity_is_inferred_from_MUST_not_STAR
#print axioms E07_arbitrary_full_mark_field_finding_survives
#print axioms E07_requires_definite_MUST_not_ordinary_STAR

end GeneralLoopAdmissionBound
