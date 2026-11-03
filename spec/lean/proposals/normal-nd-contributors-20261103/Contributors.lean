import Std

/-!
Selected conditional evidence lifetime, not a new rule evaluator. This finite
scalar model uses supplied accepted-Holds certificates, exact operation keys
and executable complete-binding enumeration. It does not prove Kotlin/AP
packing, the certificate checker, source evaluation, or current action callbacks.
-/
namespace NormalNdContributors
set_option autoImplicit false

inductive Direction where
  | forward | backward
  deriving DecidableEq, Repr
inductive MarkMode where
  | full | group
  deriving DecidableEq, Repr
inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr

structure Site where
  owner : Nat
  configuration : Nat
  methodContext : Nat
  block : Nat
  entryPort : Nat
  mode : MarkMode
  direction : Direction
  operation : Nat
  stage : Nat -- semantic observation stage; actual resume address is separate
  phase : Nat
  rule : Nat
  deriving DecidableEq, Repr

/-- The IDs are immutable scalar geometry/mark/annotation values. The payload
is retained intact, rather than replacing its accepted image by the leaf query. -/
structure Facts where
  base : Nat
  paths : List (List Nat)
  tail : Nat
  marks : List Nat
  fieldExclusions : List (List Nat)
  markExclusions : List Nat
  protection : List (List Nat)
  layer : Layer
  deriving DecidableEq, Repr
structure Input where
  site : Site
  leaf : Nat
  premise : List Nat
  facts : Facts
  holds : Bool
  deriving DecidableEq, Repr

/-- FULL mode only. Backward has independent condition branches and does not
publish or restore the forward contributor cache. -/
def supported (site : Site) : Bool :=
  site.mode == .full && site.direction == .forward

def retainable (input : Input) : Bool :=
  supported input.site && input.holds && input.facts.layer == .normal

def keep (input : Input) : Option Input := if retainable input then some input else none

def savedRows (completedForwardRun : Bool) (inputs : List Input) : List Input :=
  if completedForwardRun then inputs.filter retainable else []

def sameSite (site : Site) (input : Input) : Bool := input.site == site

def restore (site : Site) (saved : List Input) : List Input :=
  if supported site then saved.filter (fun input => sameSite site input && retainable input) else []

theorem DEMAND_is_never_retained (input : Input) (demand : input.facts.layer = .demand) :
    keep input = none := by simp [keep, retainable, demand]

theorem GROUP_is_not_reinterpreted_as_FULL (input : Input) (group : input.site.mode = .group) :
    keep input = none := by simp [keep, retainable, supported, group]

theorem backward_is_not_retained (input : Input) (backward : input.site.direction = .backward) :
    keep input = none := by simp [keep, retainable, supported, backward]

theorem an_unaccepted_fact_is_not_retained (input : Input) (notAccepted : input.holds = false) :
    keep input = none := by simp [keep, retainable, notAccepted]

theorem every_kept_input_is_the_same_conditional_edge
    (input result : Input) (kept : keep input = some result) : result = input := by
  unfold keep at kept
  split at kept
  · exact (Option.some.inj kept).symm
  · contradiction

theorem kept_geometry_marks_exclusions_and_protection_are_identical
    (input result : Input) (kept : keep input = some result) :
    result.site = input.site ∧ result.leaf = input.leaf ∧
    result.premise = input.premise ∧ result.facts = input.facts := by
  cases every_kept_input_is_the_same_conditional_edge input result kept
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem failed_or_cancelled_run_publishes_no_new_evidence (inputs : List Input) :
    savedRows false inputs = [] := rfl

theorem backward_restore_is_empty (site : Site) (rows : List Input)
    (backward : site.direction = .backward) : restore site rows = [] := by
  simp [restore, supported, backward]

theorem GROUP_restore_is_empty (site : Site) (rows : List Input)
    (group : site.mode = .group) : restore site rows = [] := by
  simp [restore, supported, group]

theorem restored_input_has_the_exact_owner_context_operation_stage_rule_key
    (site : Site) (rows : List Input) (input : Input) (found : input ∈ restore site rows) :
    input.site = site := by
  unfold restore at found
  split at found
  · have accepted := (List.mem_filter.mp found).2
    simp only [Bool.and_eq_true, sameSite, beq_iff_eq] at accepted
    exact accepted.1
  · contradiction

structure Plan where
  site : Site
  alternatives : List (List Nat)
  deriving DecidableEq, Repr

def knownLeaf (plan : Plan) (input : Input) : Bool :=
  plan.alternatives.flatten.contains input.leaf

def currentHolds (plan : Plan) (input : Input) : Bool :=
  supported plan.site && sameSite plan.site input && input.holds && knownLeaf plan input

abbrev Pool := Input → Bool

def emptyPool : Pool := fun _ => false

def rowsPool (rows : List Input) : Pool := fun input => rows.contains input

def addInput (pool : Pool) (input : Input) : Pool :=
  fun candidate => pool candidate || candidate == input

def addRows (pool : Pool) (rows : List Input) : Pool :=
  fun input => pool input || rows.contains input

/-- Executable finite ordinary join reference. The catalog is a finite scalar
accepted-input universe; vectors enumerates candidate bindings, not an oracle. -/
def vectors (width : Nat) (catalog : List Input) : List (List Input) :=
  match width with
  | 0 => [[]]
  | n + 1 => catalog.flatMap (fun input => (vectors n catalog).map (input :: ·))

def validBinding (plan : Plan) (required : List Nat) (pool : Pool) (inputs : List Input) : Bool :=
  (inputs.map Input.leaf == required) && inputs.all (fun input =>
    sameSite plan.site input && input.holds && pool input)

def ordinaryJoin (plan : Plan) (catalog : List Input) (pool : Pool) : List (List Input) :=
  plan.alternatives.flatMap (fun required =>
    (vectors required.length catalog).filter (validBinding plan required pool))

def premiseUnion (inputs : List Input) : List Nat :=
  (inputs.flatMap Input.premise).eraseDups

def resultLayer (inputs : List Input) : Layer :=
  if inputs.all (fun input => input.facts.layer == .normal) then .normal else .demand

structure Outcome where
  premise : List Nat
  layer : Layer
  acceptedFacts : List Facts
  deriving DecidableEq, Repr

def outcome (inputs : List Input) : Outcome :=
  ⟨premiseUnion inputs, resultLayer inputs, inputs.map Input.facts⟩

theorem every_contributing_premise_member_remains
    (inputs : List Input) (input : Input) (member : Nat)
    (selected : input ∈ inputs) (original : member ∈ input.premise) :
    member ∈ (outcome inputs).premise := by
  simp only [outcome, premiseUnion, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨input, selected, original⟩

theorem a_ZERO_result_premise_requires_every_contributor_to_be_ZERO
    (inputs : List Input) (zero : (outcome inputs).premise = []) :
    ∀ input ∈ inputs, input.premise = [] := by
  intro input selected
  cases shape : input.premise with
  | nil => rfl
  | cons head tail =>
    have original : head ∈ input.premise := shape ▸ List.mem_cons_self
    have kept := every_contributing_premise_member_remains inputs input head selected original
    rw [zero] at kept
    exact False.elim (List.not_mem_nil kept)

theorem NORMAL_requires_all_selected_contributors_NORMAL (inputs : List Input)
    (normal : (outcome inputs).layer = .normal) :
    inputs.all (fun input => input.facts.layer == .normal) = true := by
  unfold outcome resultLayer at normal
  split at normal
  · assumption
  · contradiction

theorem accepted_fact_metadata_is_not_recomputed (inputs : List Input) :
    (outcome inputs).acceptedFacts = inputs.map Input.facts := rfl

structure RunState where
  pool : Pool
  active : Bool
  completed : List (List Input)
  normalRows : List Input

/-- Seeding does not run callbacks and does not carry the last run's completed set. -/
def begin (plan : Plan) (saved : List Input) : RunState :=
  ⟨rowsPool (restore plan.site saved), false, [], []⟩

def ready (plan : Plan) (catalog : List Input) (state : RunState) : List (List Input) :=
  if state.active then ordinaryJoin plan catalog state.pool else []

def freshBindings (all previous : List (List Input)) : List (List Input) :=
  all.filter (fun inputs => !previous.contains inputs)

structure Step where
  state : RunState
  callbacks : List Outcome

/-- Only a current same-site Holds activates. Cached-only ready bindings retain
only their own premises; the activating input need not participate in them. -/
def accept (plan : Plan) (catalog : List Input) (allowed : Outcome → Bool)
    (state : RunState) (input : Input) : Step :=
  if currentHolds plan input then
    let pool := addInput state.pool input
    let all := ordinaryJoin plan catalog pool
    let rows := if retainable input then (state.normalRows ++ [input]).eraseDups else state.normalRows
    ⟨⟨pool, true, all, rows⟩,
      ((freshBindings all state.completed).map outcome).filter allowed⟩
  else ⟨state, []⟩

theorem loading_history_alone_is_not_execution (plan : Plan) (catalog saved : List Input) :
    ready plan catalog (begin plan saved) = [] ∧ (begin plan saved).completed = [] := ⟨rfl, rfl⟩

theorem a_nonmatching_current_check_does_not_activate_or_emit
    (plan : Plan) (catalog : List Input) (allowed : Outcome → Bool)
    (state : RunState) (input : Input) (none : currentHolds plan input = false) :
    (accept plan catalog allowed state input).state = state ∧
    (accept plan catalog allowed state input).callbacks = [] := by
  simp [accept, none]

theorem replay_and_current_Holds_use_the_ordinary_same_input_join
    (plan : Plan) (catalog saved : List Input) (allowed : Outcome → Bool)
    (input : Input) (holds : currentHolds plan input = true) :
    (accept plan catalog allowed (begin plan saved) input).state.completed =
      ordinaryJoin plan catalog (addInput (rowsPool (restore plan.site saved)) input) := by
  simp [accept, holds, begin]

/-- Structural filtering needs no proposition-level complement or choice. -/
theorem filter_of_false_on_members_is_empty {α : Type} (items : List α) (predicate : α → Bool) :
    (∀ item ∈ items, predicate item = false) → items.filter predicate = [] := by
  induction items with
  | nil => intro _; rfl
  | cons head tail induction =>
    intro rejected
    have headFalse := rejected head List.mem_cons_self
    rw [List.filter_cons, headFalse]
    exact induction (fun item member => rejected item (List.mem_cons_of_mem head member))

theorem a_missing_source_permission_produces_no_action_callback
    (plan : Plan) (catalog : List Input) (state : RunState) (input : Input) :
    (accept plan catalog (fun _ => false) state input).callbacks = [] := by
  unfold accept
  split
  · apply filter_of_false_on_members_is_empty
    intro _ _
    rfl
  · rfl

theorem initial_and_completed_dedup_are_reset_per_run (plan : Plan) (saved : List Input) :
    (begin plan saved).completed = [] ∧ (begin plan saved).normalRows = [] := ⟨rfl, rfl⟩


/-- CALL_SINK observes the semantic BOUND point. Physical outgoing ordinals
remain available for continuation, but are not a different condition site. -/
inductive StageAddress where
  | callSink (outgoingOrdinal : Nat)
  | exactSource (stage : Nat) (phase : Nat)
  | exactConjunction (stage : Nat) (phase : Nat)
  deriving DecidableEq, Repr

inductive ObservationStage where
  | bound
  | source (stage : Nat) (phase : Nat)
  | conjunction (stage : Nat) (phase : Nat)
  deriving DecidableEq, Repr

def semanticStage : StageAddress → ObservationStage
  | .callSink _ => .bound
  | .exactSource stage phase => .source stage phase
  | .exactConjunction stage phase => .conjunction stage phase

theorem BOUND_outgoing_addresses_have_one_condition_key (first second : Nat) :
    semanticStage (.callSink first) = semanticStage (.callSink second) := rfl

theorem source_phases_are_not_normalized_away (stage first second : Nat)
    (same : semanticStage (.exactSource stage first) =
      semanticStage (.exactSource stage second)) : first = second := by
  exact ObservationStage.source.inj same |>.2

theorem source_and_conjunction_phases_cannot_join (first second phase : Nat) :
    semanticStage (.exactSource first phase) ≠
      semanticStage (.exactConjunction second phase) := by
  intro impossible
  contradiction

/-- Set admission is order independent; callback chronological order is not a
semantic identity. Fixed catalog order makes final ordinary bindings equal. -/
theorem add_current_inputs_commutes (pool : Pool) (first second : Input) :
    addInput (addInput pool first) second = addInput (addInput pool second) first := by
  funext candidate
  simp only [addInput]
  cases pool candidate <;> cases candidate == first <;> cases candidate == second <;> rfl

theorem add_current_input_is_idempotent (pool : Pool) (input : Input) :
    addInput (addInput pool input) input = addInput pool input := by
  funext candidate
  simp only [addInput]
  cases pool candidate <;> cases candidate == input <;> rfl

theorem no_new_binding_is_fresh_again (bindings : List (List Input)) :
    freshBindings bindings bindings = [] := by
  unfold freshBindings
  apply filter_of_false_on_members_is_empty
  intro binding member
  rw [List.contains_iff_mem.mpr member]
  rfl

theorem current_arrival_order_has_the_same_complete_bindings
    (plan : Plan) (catalog : List Input) (allowed : Outcome → Bool)
    (state : RunState) (first second : Input)
    (firstAccepted : currentHolds plan first = true)
    (secondAccepted : currentHolds plan second = true) :
    (accept plan catalog allowed
      (accept plan catalog allowed state first).state second).state.completed =
    (accept plan catalog allowed
      (accept plan catalog allowed state second).state first).state.completed := by
  simp only [accept, firstAccepted, secondAccepted, if_true]
  rw [add_current_inputs_commutes]

theorem replaying_the_same_current_certificate_emits_no_duplicate
    (plan : Plan) (catalog : List Input) (allowed : Outcome → Bool)
    (state : RunState) (input : Input)
    (accepted : currentHolds plan input = true) :
    (accept plan catalog allowed
      (accept plan catalog allowed state input).state input).callbacks = [] := by
  simp only [accept, accepted, if_true]
  rw [add_current_input_is_idempotent, no_new_binding_is_fresh_again]
  rfl

theorem every_restored_input_is_NORMAL (site : Site) (rows : List Input) (input : Input)
    (found : input ∈ restore site rows) : input.facts.layer = .normal := by
  unfold restore at found
  split at found
  · have accepted := (List.mem_filter.mp found).2
    simp only [Bool.and_eq_true, retainable, beq_iff_eq] at accepted
    exact accepted.2.2
  · contradiction

theorem every_output_of_ordinary_join_keeps_the_selected_leaf_order
    (plan : Plan) (catalog : List Input) (pool : Pool) (inputs : List Input)
    (found : inputs ∈ ordinaryJoin plan catalog pool) :
    ∃ required ∈ plan.alternatives, inputs.map Input.leaf = required := by
  obtain ⟨required, member, selected⟩ := List.mem_flatMap.mp found
  refine ⟨required, member, ?_⟩
  have valid := (List.mem_filter.mp selected).2
  simp only [validBinding, Bool.and_eq_true, beq_iff_eq] at valid
  exact valid.1

/-- A successful barrier extends the earlier snapshot. A failed/cancelled run
cannot replace valid old evidence by a partially collected snapshot. -/
def publish (successful : Bool) (previous current : List Input) : List Input :=
  if successful then (previous ++ savedRows true current).eraseDups else previous

theorem unsuccessful_barrier_keeps_the_previous_snapshot (previous current : List Input) :
    publish false previous current = previous := rfl

theorem publishing_new_evidence_never_loses_an_old_certificate
    (previous current : List Input) (input : Input) (old : input ∈ previous) :
    input ∈ publish true previous current := by
  simp [publish, old]


theorem finite_vectors_are_constructively_complete (inputs catalog : List Input)
    (available : ∀ input ∈ inputs, input ∈ catalog) :
    inputs ∈ vectors inputs.length catalog := by
  induction inputs with
  | nil => simp [vectors]
  | cons head tail induction =>
    apply List.mem_flatMap.mpr
    refine ⟨head, available head (by simp), ?_⟩
    apply List.mem_map.mpr
    refine ⟨tail, induction (fun input member => available input (by simp [member])), rfl⟩

theorem finite_vector_width_is_exact (width : Nat) (catalog inputs : List Input)
    (found : inputs ∈ vectors width catalog) : inputs.length = width := by
  induction width generalizing inputs with
  | zero => simpa [vectors] using found
  | succ width induction =>
    obtain ⟨head, _, selected⟩ := List.mem_flatMap.mp found
    obtain ⟨tail, member, same⟩ := List.mem_map.mp selected
    subst inputs
    simp only [List.length_cons]
    exact congrArg Nat.succ (induction tail member)

theorem finite_vectors_contain_only_catalog_inputs (width : Nat) (catalog inputs : List Input)
    (found : inputs ∈ vectors width catalog) : ∀ input ∈ inputs, input ∈ catalog := by
  induction width generalizing inputs with
  | zero =>
    simp only [vectors, List.mem_singleton] at found
    subst inputs
    simp
  | succ width induction =>
    obtain ⟨head, headMember, selected⟩ := List.mem_flatMap.mp found
    obtain ⟨tail, member, same⟩ := List.mem_map.mp selected
    subst inputs
    intro input inputMember
    rcases List.mem_cons.mp inputMember with same | tailMember
    · exact same ▸ headMember
    · exact induction tail member input tailMember

/-- The executable join is complete for every accepted binding whose scalar
certificates occur in the explicit finite catalog. It needs no output oracle. -/
theorem ordinary_join_is_complete_in_the_finite_certificate_universe
    (plan : Plan) (catalog : List Input) (pool : Pool) (required : List Nat)
    (inputs : List Input) (alternative : required ∈ plan.alternatives)
    (leaves : inputs.map Input.leaf = required)
    (available : ∀ input ∈ inputs, input ∈ catalog)
    (accepted : inputs.all (fun input => sameSite plan.site input && input.holds && pool input) = true) :
    inputs ∈ ordinaryJoin plan catalog pool := by
  apply List.mem_flatMap.mpr
  refine ⟨required, alternative, List.mem_filter.mpr ⟨?_, ?_⟩⟩
  · have lengths : inputs.length = required.length := by
      simpa only [List.length_map] using congrArg List.length leaves
    rw [← lengths]
    exact finite_vectors_are_constructively_complete inputs catalog available
  · unfold validBinding
    have reflexive : (required == required) = true := beq_iff_eq.mpr rfl
    rw [leaves, accepted, reflexive]
    rfl

theorem ordinary_join_only_uses_same_site_accepted_available_certificates
    (plan : Plan) (catalog : List Input) (pool : Pool) (inputs : List Input)
    (found : inputs ∈ ordinaryJoin plan catalog pool) :
    ∀ input ∈ inputs, input ∈ catalog ∧ input.site = plan.site ∧
      input.holds = true ∧ pool input = true := by
  obtain ⟨required, _, selected⟩ := List.mem_flatMap.mp found
  obtain ⟨enumerated, accepted⟩ := List.mem_filter.mp selected
  simp only [validBinding, Bool.and_eq_true, beq_iff_eq] at accepted
  have fields : ∀ input ∈ inputs, (sameSite plan.site input && input.holds && pool input) = true := by
    exact List.all_eq_true.mp accepted.2
  intro input member
  have valid := fields input member
  simp only [Bool.and_eq_true, sameSite, beq_iff_eq] at valid
  exact ⟨finite_vectors_contain_only_catalog_inputs required.length catalog inputs enumerated input member,
    valid.1.1, valid.1.2, valid.2⟩

/-- Current observation parts do not include restored certificates. Only the
ordinary complete binding can consume their saved conditional premises. -/
def currentParts (input : Input) : List Facts := if input.holds then [input.facts] else []

theorem restored_evidence_does_not_become_an_extra_current_packet
    (input : Input) (currentAccepted : input.holds = true) :
    currentParts input = [input.facts] := by simp [currentParts, currentAccepted]

/-- Scalar session/data and conditional P/Q examples. -/
def site : Site := ⟨1, 2, 3, 4, 5, .full, .forward, 6, 7, 8, 9⟩
def normalFacts : Facts := ⟨10, [[11]], 12, [13], [[14]], [15], [[11]], .normal⟩
def session : Input := ⟨site, 0, [], normalFacts, true⟩
def data : Input := ⟨site, 1, [20], { normalFacts with marks := [21] }, true⟩
def oldP : Input := { session with premise := [10] }
def currentDemand : Input := { data with facts := { data.facts with layer := .demand } }
def andPlan : Plan := ⟨site, [[0, 1]]⟩
def catalog : List Input := [session, data, oldP, currentDemand]

theorem an_incomplete_NORMAL_leaf_is_retained :
    savedRows true [session] = [session] ∧
    ordinaryJoin andPlan catalog (rowsPool [session]) = [] := by decide

theorem session_cache_plus_current_DATA_restores_the_complete_binding :
    (accept andPlan catalog (fun _ => true) (begin andPlan [session]) data).callbacks =
      [⟨[20], .normal, [session.facts, data.facts]⟩] := by decide

theorem old_conditional_P_and_current_Q_keep_both_premises :
    (accept andPlan catalog (fun _ => true) (begin andPlan [oldP]) data).callbacks =
      [⟨[10, 20], .normal, [oldP.facts, data.facts]⟩] := by decide

theorem NORMAL_cache_plus_DEMAND_current_is_DEMAND :
    (accept andPlan catalog (fun _ => true) (begin andPlan [session]) currentDemand).callbacks =
      [⟨[20], .demand, [session.facts, currentDemand.facts]⟩] := by decide

theorem a_caller_with_only_Q_cannot_satisfy_the_old_P_binding :
    ([10, 20].all (fun premise => [20].contains premise)) = false := by decide

theorem mixed_ZERO_and_nonzero_support_has_no_independent_ZERO_arm :
    (outcome [session, data]).premise = [20] ∧
    (outcome [oldP, data]).premise = [10, 20] := by decide

theorem an_unrelated_stage_cannot_restore_the_same_facts :
    restore { site with stage := 99 } [session] = [] := by decide

theorem an_unrelated_owner_cannot_restore_the_same_facts :
    restore { site with owner := 99 } [session] = [] := by decide


def anotherCurrentLeaf : Input := { data with leaf := 2, premise := [99] }
def twoAlternatives : Plan := ⟨site, [[0, 1], [2, 3]]⟩
def activationCatalog : List Input := [oldP, data, anotherCurrentLeaf]

theorem cached_complete_bindings_are_not_emitted_when_loaded :
    ready twoAlternatives activationCatalog (begin twoAlternatives [oldP, data]) = [] := rfl

theorem current_accepted_leaf_activates_a_cached_complete_binding :
    (accept twoAlternatives activationCatalog (fun _ => true)
      (begin twoAlternatives [oldP, data]) anotherCurrentLeaf).callbacks =
      [⟨[10, 20], .normal, [oldP.facts, data.facts]⟩] := by decide

theorem unrelated_activating_premise_is_not_added_to_the_saved_binding :
    ((accept twoAlternatives activationCatalog (fun _ => true)
      (begin twoAlternatives [oldP, data]) anotherCurrentLeaf).callbacks.map Outcome.premise) =
      [[10, 20]] ∧ 99 ∉ [10, 20] := by decide

theorem nonmatching_leaf_cannot_activate_cached_complete_bindings :
    (accept twoAlternatives activationCatalog (fun _ => true)
      (begin twoAlternatives [oldP, data])
      { anotherCurrentLeaf with holds := false }).callbacks = [] := by decide

theorem an_unrelated_DEMAND_trigger_does_not_demote_a_saved_complete_NORMAL_binding :
    (accept twoAlternatives
      [oldP, data, { anotherCurrentLeaf with facts := { normalFacts with layer := .demand } }]
      (fun _ => true) (begin twoAlternatives [oldP, data])
      { anotherCurrentLeaf with facts := { normalFacts with layer := .demand } }).callbacks =
      [⟨[10, 20], .normal, [oldP.facts, data.facts]⟩] := by decide

theorem same_facts_at_another_block_or_entry_do_not_share_cache :
    restore { site with block := 100 } [session] = [] ∧
    restore { site with entryPort := 100 } [session] = [] := by decide

theorem same_facts_at_another_rule_or_phase_do_not_share_cache :
    restore { site with rule := 100 } [session] = [] ∧
    restore { site with phase := 100 } [session] = [] := by decide

theorem protection_and_exclusions_are_not_replaced_by_a_query_pattern :
    (outcome [oldP, data]).acceptedFacts.map Facts.protection = [[[11]], [[11]]] ∧
    (outcome [oldP, data]).acceptedFacts.map Facts.fieldExclusions = [[[14]], [[14]]] ∧
    (outcome [oldP, data]).acceptedFacts.map Facts.markExclusions = [[15], [15]] := by decide

theorem a_completed_binding_can_be_used_again_in_a_new_run :
    (accept andPlan catalog (fun _ => true) (begin andPlan [session, data]) data).callbacks =
      [⟨[20], .normal, [session.facts, data.facts]⟩] := by decide


end NormalNdContributors
