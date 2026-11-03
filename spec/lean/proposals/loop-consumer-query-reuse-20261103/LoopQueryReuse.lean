import Std

namespace LoopQueryReuse

/- Fixed-entry factoring keeps the unchanged native output/protection/normalization
   function opaque. Candidate rows retain full row/member/exit identity. -/
structure Row where
  id : Nat
  member : Nat
  entry : Nat
  exit : Nat
  port : Nat
  exitDepth : Nat
  deriving DecidableEq, Repr

structure Ticket (allowed : Row → Bool) where
  row : Row
  accepted : allowed row = true

def checked (allowed : Row → Bool) (row : Row) : Option (Ticket allowed) :=
  if h : allowed row = true then some ⟨row,h⟩ else none

def oldLeaf (allowed : Row → Bool) (nativeRest : Row → A → List B) (r : Row) (a : A) : List B :=
  if allowed r then nativeRest r a else []

def ticketLeaf (nativeRest : Row → A → List B) (t : Ticket allowed) (a : A) : List B :=
  nativeRest t.row a

theorem ticket_uses_same_entry_predicate (allowed : Row → Bool) (r : Row) (t : Ticket allowed)
    (h : checked allowed r = some t) : t.row = r ∧ allowed r = true := by
  unfold checked at h
  split at h
  next yes => cases Option.some.inj h; exact ⟨rfl,yes⟩
  next no => simp at h

theorem ticket_preserves_native_leaf (nativeRest : Row → A → List B)
    (t : Ticket allowed) (a : A) : ticketLeaf nativeRest t a = oldLeaf allowed nativeRest t.row a := by
  simp [ticketLeaf, oldLeaf, t.accepted]

def oldParts (allowed : Row → Bool) (rest : Row → A → List B) (r : Row) (parts : List A) : List B :=
  parts.flatMap (fun a => oldLeaf allowed rest r a)

def preparedParts (allowed : Row → Bool) (rest : Row → A → List B) (r : Row) (parts : List A) : List B :=
  match checked allowed r with
  | none => []
  | some ticket => parts.flatMap (fun a => ticketLeaf rest ticket a)

theorem empty_flatMap {A B : Type} (xs : List A) : xs.flatMap (fun _ => ([] : List B)) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.flatMap_cons, List.nil_append] using ih

theorem factor_entry_before_all_protection_parts (allowed : Row → Bool) (rest : Row → A → List B)
    (r : Row) (parts : List A) : preparedParts allowed rest r parts = oldParts allowed rest r parts := by
  cases h : allowed r <;> simp [preparedParts, checked, oldParts, oldLeaf, ticketLeaf, h]

theorem identical_post_normalization_and_annotation_transport
    (allowed : Row → Bool) (rest : Row → A → List B) (r : Row) (parts : List A)
    (packNormalizeProtect : List B → C) :
    packNormalizeProtect (preparedParts allowed rest r parts) =
      packNormalizeProtect (oldParts allowed rest r parts) := by
  rw [factor_entry_before_all_protection_parts]

def prepareRows (allowed : Row → Bool) (rows : List Row) : List Row := rows.filter allowed

def oldRows (allowed : Row → Bool) (outputMatch : Row → A → Bool)
    (rest : Row → A → List B) (rows : List Row) (actual : A) : List B :=
  rows.flatMap fun r => if outputMatch r actual then oldLeaf allowed rest r actual else []

def preparedRows (outputMatch : Row → A → Bool) (rest : Row → A → List B)
    (rows : List Row) (actual : A) : List B :=
  rows.flatMap fun r => if outputMatch r actual then rest r actual else []

theorem prepared_rows_equal_for_every_raw_output (allowed : Row → Bool)
    (outputMatch : Row → A → Bool) (rest : Row → A → List B) (rows : List Row) (actual : A) :
    preparedRows outputMatch rest (prepareRows allowed rows) actual =
      oldRows allowed outputMatch rest rows actual := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    cases ha : allowed r <;> cases ho : outputMatch r actual <;>
      simp [prepareRows, preparedRows, oldRows, oldLeaf, ha, ho] at ih ⊢ <;> exact ih

theorem prepared_row_is_one_original_pair (allowed : Row → Bool) (rows : List Row) (r : Row)
    (h : r ∈ prepareRows allowed rows) : r ∈ rows ∧ allowed r = true := by
  exact List.mem_filter.mp h

def budget (global depth : Nat) : Nat := if depth ≥ global then global else depth + 1

theorem row_budget_is_native_FL_plus_one (global depth : Nat) : budget global depth = min global (depth+1) := by
  unfold budget
  split <;> omega

theorem budget_never_exceeds_global (global depth : Nat) : budget global depth ≤ global := by
  rw [row_budget_is_native_FL_plus_one]
  exact Nat.min_le_left _ _

theorem each_row_keeps_its_exit_depth (allowed : Row → Bool) (rows : List Row) (r : Row)
    (h : r ∈ prepareRows allowed rows) (global : Nat) :
    ∃ old ∈ rows, old = r ∧ budget global old.exitDepth = budget global r.exitDepth := by
  exact ⟨r,(prepared_row_is_one_original_pair allowed rows r h).1,rfl,rfl⟩

structure PlannedRow where
  row : Row
  entryAccepted : Bool
  deriving DecidableEq, Repr

def compileRows (allowed : Row → Bool) (rows : List Row) : List PlannedRow :=
  rows.map (fun r => ⟨r,allowed r⟩)

def applyCompiled (outputMatch : Row → A → Bool) (rest : Row → A → List B)
    (plan : List PlannedRow) (actual : A) : List B :=
  plan.flatMap fun p => if outputMatch p.row actual then
    if p.entryAccepted then rest p.row actual else [] else []

theorem compiled_entry_decisions_preserve_ordered_outputs (allowed : Row → Bool)
    (outputMatch : Row → A → Bool) (rest : Row → A → List B) (rows : List Row) (actual : A) :
    applyCompiled outputMatch rest (compileRows allowed rows) actual = oldRows allowed outputMatch rest rows actual := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    cases ha : allowed r <;> cases ho : outputMatch r actual <;>
      simp [applyCompiled, compileRows, oldRows, oldLeaf, ha, ho] at ih ⊢ <;> exact ih

def attemptedRows (outputMatch : Row → A → Bool) (rows : List Row) (actual : A) : List Row :=
  rows.filter (fun r => outputMatch r actual)

theorem compiled_plan_keeps_all_diagnostic_row_references (allowed : Row → Bool) (rows : List Row) :
    (compileRows allowed rows).map PlannedRow.row = rows := by simp [compileRows, Function.comp_def]

theorem output_matched_diagnostic_attempt_order_preserved (allowed : Row → Bool)
    (outputMatch : Row → A → Bool) (rows : List Row) (actual : A) :
    attemptedRows outputMatch ((compileRows allowed rows).map PlannedRow.row) actual =
      attemptedRows outputMatch rows actual := by rw [compiled_plan_keeps_all_diagnostic_row_references]

theorem all_rejected_entries_give_empty_C5_for_every_output (allowed : Row → Bool)
    (outputMatch : Row → A → Bool) (rest : Row → A → List B) (rows : List Row)
    (reject : ∀ r ∈ rows, allowed r = false) (actual : A) :
    oldRows allowed outputMatch rest rows actual = [] := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    have first := reject r (List.mem_cons_self)
    have later := ih (fun x hx => reject x (List.mem_cons_of_mem _ hx))
    cases h : outputMatch r actual <;> simp [oldRows, oldLeaf, first, h] at later ⊢ <;> exact later

/- A skip certificate is narrower than a DATA result filter: a capable Target
   event must keep native replay. Requests are ignored only by this observer. -/
inductive ReplayEvent where
  | data (exit value : Nat)
  | target (value : Nat)
  | request (mark : Nat)
  deriving DecidableEq, Repr

def observeReplay (c5 : Nat → Nat → List Nat) : List ReplayEvent → List Nat
  | [] => []
  | .data exit value :: rest => c5 exit value ++ observeReplay c5 rest
  | .target value :: rest => value :: observeReplay c5 rest
  | .request _ :: rest => observeReplay c5 rest

def DataReplayOnly (events : List ReplayEvent) : Prop :=
  ∀ event ∈ events, ∀ value, event ≠ ReplayEvent.target value

def EmptyDataPorts (c5 : Nat → Nat → List Nat) (events : List ReplayEvent) : Prop :=
  ∀ exit value, ReplayEvent.data exit value ∈ events → c5 exit value = []

theorem skip_only_proven_empty_DATA_replay (c5 : Nat → Nat → List Nat)
    (events : List ReplayEvent) (noTarget : DataReplayOnly events)
    (emptyPorts : EmptyDataPorts c5 events) : observeReplay c5 events = [] := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    have tailNo : DataReplayOnly events := fun e he v => noTarget e (List.mem_cons_of_mem _ he) v
    have tailEmpty : EmptyDataPorts c5 events := fun e v hv => emptyPorts e v (List.mem_cons_of_mem _ hv)
    have tail := ih tailNo tailEmpty
    cases event with
    | data exit value =>
      simp only [observeReplay, emptyPorts exit value List.mem_cons_self, List.nil_append, tail]
    | target value => exact False.elim (noTarget _ List.mem_cons_self value rfl)
    | request mark => exact tail

theorem empty_DATA_plan_does_not_authorize_Target_skip :
    observeReplay (fun _ _ => []) [.target 7] = [7] := by decide

def nativeSinkRoute (backward zeroPremise isReach : Bool) (exit value : Nat) : ReplayEvent :=
  if backward && !zeroPremise && isReach then .target value else .data exit value

theorem nonReach_native_sink_is_DATA (backward zeroPremise : Bool) (exit value : Nat) :
    nativeSinkRoute backward zeroPremise false exit value = .data exit value := by
  cases backward <;> cases zeroPremise <;> rfl

theorem backward_Reach_native_sink_can_emit_Target :
    nativeSinkRoute true false true 3 7 = .target 7 := by decide

def canSkipReplay (localView sameDirection nonMust nonRoot dataInput dataOutput knownBase
    completePortCertificates : Bool) : Bool :=
  localView && sameDirection && nonMust && nonRoot && dataInput && dataOutput && knownBase && completePortCertificates

theorem reverse_MUST_root_unknown_keep_native_replay :
    canSkipReplay true false true true true true true true = false ∧
    canSkipReplay true true false true true true true true = false ∧
    canSkipReplay true true true false true true true true = false ∧
    canSkipReplay true true true true true true false true = false := by decide

theorem every_port_needs_an_empty_certificate :
    canSkipReplay true true true true true true true false = false := by decide

theorem empty_replay_contribution_preserves_ordered_observation (before after : List Nat)
    (c5 : Nat → Nat → List Nat) (events : List ReplayEvent)
    (noTarget : DataReplayOnly events) (emptyPorts : EmptyDataPorts c5 events) :
    before ++ observeReplay c5 events ++ after = before ++ after := by
  rw [skip_only_proven_empty_DATA_replay c5 events noTarget emptyPorts, List.append_nil]

/- C2: one scope/family query result supplies both projections. Native sets and
   their first-occurrence freezing are unchanged and may contain many admissions. -/
inductive Family where
  | adjacent | repeatFamily
  deriving DecidableEq, Repr

structure Admission where
  initial : Nat
  layer : Bool
  deriving DecidableEq, Repr

structure Label where
  scope : Nat
  family : Family
  admitted : Admission
  deriving DecidableEq, Repr

def labelOne (scope : Nat) (family : Family) (values : List Admission) : List Label :=
  values.map (fun value => ⟨scope,family,value⟩)

def project (family : Family) (labels : List Label) : List Admission :=
  labels.filterMap (fun x => if x.family = family then some x.admitted else none)

theorem project_own_family (scope : Nat) (family : Family) (values : List Admission) :
    project family (labelOne scope family values) = values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [project, labelOne] at ih ⊢; exact ih

theorem project_other_family (scope : Nat) (a b : Family) (different : a ≠ b)
    (values : List Admission) : project a (labelOne scope b values) = [] := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [project, labelOne, Ne.symm different] at ih ⊢ <;> exact ih

def labelled (query : Nat → List Admission) (family : Family) (scopes : List Nat) : List Label :=
  scopes.flatMap (fun scope => labelOne scope family (query scope))

def plain (query : Nat → List Admission) (scopes : List Nat) : List Admission := scopes.flatMap query

theorem project_append (family : Family) (a b : List Label) :
    project family (a ++ b) = project family a ++ project family b := by
  exact List.filterMap_append

theorem labelled_plain_projection_exact (query : Nat → List Admission) (family : Family) (scopes : List Nat) :
    project family (labelled query family scopes) = plain query scopes := by
  induction scopes with
  | nil => rfl
  | cons scope scopes ih =>
    change project family (labelOne scope family (query scope) ++ labelled query family scopes) =
      query scope ++ plain query scopes
    rw [project_append, project_own_family, ih]

def twoFamilies (query : Nat → List Admission) (adj repeatFamily : List Nat) : List Label :=
  labelled query .adjacent adj ++ labelled query .repeatFamily repeatFamily

def bundleAdjacent (query : Nat → List Admission) (adj repeatFamily : List Nat) : List Admission :=
  project .adjacent (twoFamilies query adj repeatFamily)

def bundleRepeat (query : Nat → List Admission) (adj repeatFamily : List Nat) : List Admission :=
  project .repeatFamily (twoFamilies query adj repeatFamily)

theorem other_scopes_project_empty (query : Nat → List Admission) (a b : Family) (h : a ≠ b) (scopes : List Nat) :
    project a (labelled query b scopes) = [] := by
  induction scopes with
  | nil => rfl
  | cons scope scopes ih =>
    change project a (labelOne scope b (query scope) ++ labelled query b scopes) = []
    rw [project_append, project_other_family scope a b h, ih]
    rfl

theorem adjacent_projection_preserved (query : Nat → List Admission) (adj repeatFamily : List Nat) :
    bundleAdjacent query adj repeatFamily = plain query adj := by
  simp only [bundleAdjacent, twoFamilies, project_append]
  change project .adjacent (labelled query .adjacent adj) ++
    project .adjacent (labelled query .repeatFamily repeatFamily) = plain query adj
  rw [labelled_plain_projection_exact, other_scopes_project_empty query .adjacent .repeatFamily (by decide)]
  exact List.append_nil _

theorem repeat_projection_preserved (query : Nat → List Admission) (adj repeatFamily : List Nat) :
    bundleRepeat query adj repeatFamily = plain query repeatFamily := by
  simp only [bundleRepeat, twoFamilies, project_append]
  change project .repeatFamily (labelled query .adjacent adj) ++
    project .repeatFamily (labelled query .repeatFamily repeatFamily) = plain query repeatFamily
  rw [other_scopes_project_empty query .repeatFamily .adjacent (by decide), labelled_plain_projection_exact]
  rfl

theorem frozen_projection_stays_equal (freeze : List Admission → A) (query : Nat → List Admission)
    (adj repeatFamily : List Nat) : freeze (bundleAdjacent query adj repeatFamily) = freeze (plain query adj) := by
  rw [adjacent_projection_preserved]

structure Observation (R : Type) where
  adjacent : List Admission
  enclosing : List R
  repeatAdmissions : List Admission
  labels : List Label

def referenceObservation (query : Nat → List Admission) (adj repeats : List Nat) (enclosing : List R) : Observation R :=
  ⟨plain query adj,enclosing,plain query repeats,twoFamilies query adj repeats⟩

def bundledObservation (query : Nat → List Admission) (adj repeats : List Nat) (enclosing : List R) : Observation R :=
  ⟨bundleAdjacent query adj repeats,enclosing,bundleRepeat query adj repeats,twoFamilies query adj repeats⟩

theorem complete_three_family_signature_preserved (query : Nat → List Admission)
    (adj repeats : List Nat) (enclosing : List R) :
    bundledObservation query adj repeats enclosing = referenceObservation query adj repeats enclosing := by
  simp [bundledObservation, referenceObservation, adjacent_projection_preserved, repeat_projection_preserved]

theorem positive_adjacent_does_not_remove_repeat_or_enclosing :
    (bundledObservation (fun n => [⟨n,false⟩]) [1] [2] [9]).repeatAdmissions = [⟨2,false⟩] ∧
    (bundledObservation (fun n => [⟨n,false⟩]) [1] [2] [9]).enclosing = [9] := by decide

/- Synchronous, bounded owner-quantum memo. On capacity exhaustion it clears on
   the same thread, then inserts the current answer. No deferred operation exists. -/
def lookup [DecidableEq K] (key : K) : List (K × V) → Option V
  | [] => none
  | (k,v)::rest => if key = k then some v else lookup key rest

def CacheValid (f : K → V) (cache : List (K × V)) : Prop :=
  ∀ pair ∈ cache, pair.2 = f pair.1

def remember (capacity : Nat) (key : K) (value : V) (cache : List (K × V)) : List (K × V) :=
  if capacity = 0 then [] else if cache.length < capacity then (key,value)::cache else [(key,value)]

def memo [DecidableEq K] (f : K → V) (capacity : Nat) (cache : List (K × V)) (key : K) : V × List (K × V) :=
  match lookup key cache with
  | some value => (value,cache)
  | none => let value := f key; (value,remember capacity key value cache)

theorem lookup_valid [DecidableEq K] (f : K → V) (cache : List (K × V)) (h : CacheValid f cache)
    (key : K) (value : V) (hit : lookup key cache = some value) : value = f key := by
  induction cache with
  | nil => simp [lookup] at hit
  | cons pair rest ih =>
    rcases pair with ⟨k,v⟩
    simp only [lookup] at hit
    split at hit
    next same => cases Option.some.inj hit; subst k; exact h (key,value) (List.mem_cons_self)
    next different => exact ih (fun pair hp => h pair (List.mem_cons_of_mem _ hp)) hit

theorem remember_valid (f : K → V) (capacity : Nat) (cache : List (K × V)) (h : CacheValid f cache) (key : K) :
    CacheValid f (remember capacity key (f key) cache) := by
  unfold remember
  split
  next empty => intro pair hp; simp at hp
  next nonempty =>
    split
    next room =>
      intro pair hp
      rcases List.mem_cons.mp hp with same | old
      · cases same; rfl
      · exact h pair old
    next full => intro pair hp; simp only [List.mem_singleton] at hp; cases hp; rfl

theorem remember_bounded (capacity : Nat) (key : K) (value : V) (cache : List (K × V)) :
    (remember capacity key value cache).length ≤ capacity := by
  unfold remember
  split
  next empty => simp_all
  next nonempty => split <;> simp_all <;> omega

theorem memo_answer_exact [DecidableEq K] (f : K → V) (capacity : Nat) (cache : List (K × V))
    (h : CacheValid f cache) (key : K) : (memo f capacity cache key).1 = f key := by
  unfold memo
  split
  next value hit => exact lookup_valid f cache h key value hit
  next miss => rfl

theorem memo_valid [DecidableEq K] (f : K → V) (capacity : Nat) (cache : List (K × V))
    (h : CacheValid f cache) (key : K) : CacheValid f (memo f capacity cache key).2 := by
  unfold memo
  split
  · exact h
  · exact remember_valid f capacity cache h key

theorem memo_bounded [DecidableEq K] (f : K → V) (capacity : Nat) (cache : List (K × V))
    (bounded : cache.length ≤ capacity) (key : K) : (memo f capacity cache key).2.length ≤ capacity := by
  unfold memo
  split
  · exact bounded
  · exact remember_bounded capacity key (f key) cache

def memoAdmitted [DecidableEq K] (f : K → V) (capacity : Nat) (cacheable : K → V → Bool)
    (cache : List (K × V)) (key : K) : V × List (K × V) :=
  match lookup key cache with
  | some value => (value,cache)
  | none => let value := f key
            (value,if cacheable key value then remember capacity key value cache else cache)

theorem result_weight_gate_cannot_change_query_answer [DecidableEq K] (f : K → V) (capacity : Nat)
    (cacheable : K → V → Bool) (cache : List (K × V)) (h : CacheValid f cache) (key : K) :
    (memoAdmitted f capacity cacheable cache key).1 = f key := by
  unfold memoAdmitted
  split
  next value hit => exact lookup_valid f cache h key value hit
  next miss => rfl

theorem admitted_memo_valid [DecidableEq K] (f : K → V) (capacity : Nat)
    (cacheable : K → V → Bool) (cache : List (K × V)) (h : CacheValid f cache) (key : K) :
    CacheValid f (memoAdmitted f capacity cacheable cache key).2 := by
  unfold memoAdmitted
  split
  · exact h
  · change CacheValid f (if cacheable key (f key) then remember capacity key (f key) cache else cache)
    split
    · exact remember_valid f capacity cache h key
    · exact h

theorem admitted_memo_bounded [DecidableEq K] (f : K → V) (capacity : Nat)
    (cacheable : K → V → Bool) (cache : List (K × V)) (h : cache.length ≤ capacity) (key : K) :
    (memoAdmitted f capacity cacheable cache key).2.length ≤ capacity := by
  unfold memoAdmitted
  split
  · exact h
  · change (if cacheable key (f key) then remember capacity key (f key) cache else cache).length ≤ capacity
    split
    · exact remember_bounded capacity key (f key) cache
    · exact h

def belowWeight {K V : Type} (weight : K → V → Nat) (limit : Nat) (cache : List (K × V)) : Prop :=
  ∀ pair ∈ cache, weight pair.1 pair.2 ≤ limit

theorem remember_entry_weight_bounded (weight : K → V → Nat) (limit capacity : Nat)
    (cache : List (K × V)) (h : belowWeight weight limit cache) (key : K) (value : V)
    (fits : weight key value ≤ limit) : belowWeight weight limit (remember capacity key value cache) := by
  unfold remember
  split
  next empty => intro pair hp; simp at hp
  next nonempty =>
    split
    next room =>
      intro pair hp
      rcases List.mem_cons.mp hp with same | old
      · cases same; exact fits
      · exact h pair old
    next full => intro pair hp; simp only [List.mem_singleton] at hp; cases hp; exact fits

def totalWeight (weight : K → V → Nat) : List (K × V) → Nat
  | [] => 0
  | pair :: rest => weight pair.1 pair.2 + totalWeight weight rest

theorem entry_and_capacity_bounds_bound_total_references (weight : K → V → Nat)
    (limit capacity : Nat) (cache : List (K × V)) (fits : belowWeight weight limit cache)
    (bounded : cache.length ≤ capacity) : totalWeight weight cache ≤ capacity * limit := by
  have rows : totalWeight weight cache ≤ cache.length * limit := by
    induction cache with
    | nil => simp [totalWeight]
    | cons pair rest ih =>
      have first := fits pair List.mem_cons_self
      have later := ih (fun p hp => fits p (List.mem_cons_of_mem _ hp))
        (by simp only [List.length_cons] at bounded; omega)
      change weight pair.1 pair.2 + totalWeight weight rest ≤ (rest.length + 1) * limit
      calc
        _ ≤ limit + rest.length * limit := Nat.add_le_add first later
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
  exact Nat.le_trans rows (Nat.mul_le_mul_right limit bounded)

theorem C2_selected_reference_bound (weight : K → V → Nat) (cache : List (K × V))
    (fits : belowWeight weight 128 cache) (bounded : cache.length ≤ 32) :
    totalWeight weight cache ≤ 4096 := entry_and_capacity_bounds_bound_total_references weight 128 32 cache fits bounded

theorem C5_selected_reference_bound (weight : K → V → Nat) (cache : List (K × V))
    (fits : belowWeight weight 2048 cache) (bounded : cache.length ≤ 32) :
    totalWeight weight cache ≤ 65536 := entry_and_capacity_bounds_bound_total_references weight 2048 32 cache fits bounded

inductive Program (K V O : Type) where
  | done (output : O)
  | query (key : K) (next : V → Program K V O)

def evaluate (f : K → V) : Program K V O → O
  | .done out => out
  | .query key next => evaluate f (next (f key))

def evaluateMemo [DecidableEq K] (f : K → V) (capacity : Nat) (cache : List (K × V)) : Program K V O → O × List (K × V)
  | .done out => (out,cache)
  | .query key next =>
      let answered := memo f capacity cache key
      evaluateMemo f capacity answered.2 (next answered.1)

theorem every_finite_adaptive_query_program_same [DecidableEq K] (f : K → V) (capacity : Nat)
    (program : Program K V O) (cache : List (K × V)) (valid : CacheValid f cache) :
    (evaluateMemo f capacity cache program).1 = evaluate f program ∧
      CacheValid f (evaluateMemo f capacity cache program).2 := by
  induction program generalizing cache with
  | done out => exact ⟨rfl,valid⟩
  | query key next ih =>
    have same := memo_answer_exact f capacity cache valid key
    have kept := memo_valid f capacity cache valid key
    have later := ih (memo f capacity cache key).1 (memo f capacity cache key).2 kept
    simpa only [evaluateMemo, evaluate, same] using later

theorem restriction_selection_and_complete_observation_same [DecidableEq K] (f : K → V)
    (capacity : Nat) (program : Program K V O) :
    (evaluateMemo f capacity [] program).1 = evaluate f program :=
  (every_finite_adaptive_query_program_same f capacity program [] (by intro pair hp; simp at hp)).1

def ownerQuantum (f : K → V) (capacity : Nat) (program : Program K V O) [DecidableEq K] : O :=
  (evaluateMemo f capacity [] program).1

theorem cache_dies_with_quantum [DecidableEq K] (f : K → V) (capacity : Nat) (program : Program K V O) :
    ownerQuantum f capacity program = evaluate f program := restriction_selection_and_complete_observation_same f capacity program

def queryWithWork [DecidableEq K] (f : K → V) (capacity : Nat) (cache : List (K × V)) (key : K) (work : W) :
    (V × List (K × V)) × W := (memo f capacity cache key,work)

theorem no_new_work_queue_or_completion_effect [DecidableEq K] (f : K → V) (capacity : Nat)
    (cache : List (K × V)) (key : K) (work : W) :
    (queryWithWork f capacity cache key work).2 = work := rfl

/- Finite CEGAR witnesses: invalid coarser keys and changed predicates. -/
inductive Tail where
  | exact | star | any | must
  deriving DecidableEq, Repr

def flowMemberTemplate (tail : Tail) : Tail := if tail = .exact then .star else tail

def preparedMemberTemplates (originalFlow : Bool) (members : List Tail) : List Tail :=
  if originalFlow then members.map flowMemberTemplate else members

def nativeNormalizedMembers (originalFlow resultFlow : Bool) (members : List Tail) : List Tail :=
  if originalFlow && resultFlow then members.map flowMemberTemplate else members

theorem pattern_only_templates_equal_native_after_guarded_kind
    (originalFlow resultFlow : Bool) (members : List Tail) (sameKind : resultFlow = originalFlow) :
    preparedMemberTemplates originalFlow members = nativeNormalizedMembers originalFlow resultFlow members := by
  subst resultFlow
  cases originalFlow <;> rfl

theorem FLOW_EXACT_template_changes_tail_only : flowMemberTemplate .exact = .star := by decide

theorem nonFLOW_ND_templates_keep_complete_members :
    preparedMemberTemplates false [.exact,.any] = [.exact,.any] := by decide

theorem unknown_result_kind_requires_fallback :
    preparedMemberTemplates true [.exact] ≠ nativeNormalizedMembers true false [.exact] := by decide

structure Packet where
  payload : Nat
  layer : Bool
  mark : Nat
  fields : List Nat
  tail : Tail
  fieldExclusions : List Nat
  flowExclusions : List Nat
  protection : List Nat
  deriving DecidableEq, Repr

structure FullKey where
  owner : Nat
  scope : Nat
  exit : Nat
  wholeOriginal : List Nat
  policy : Nat
  demandSnapshot : Nat
  recordsSnapshot : Nat
  targetsSnapshot : Nat
  packet : Packet
  deriving DecidableEq, Repr

def normalFlow : Packet := ⟨8,false,0,[7],.exact,[],[4],[]⟩
def protectedCopy : Packet := { normalFlow with protection := [3] }

theorem Facts_equals_is_not_a_full_query_key : normalFlow.payload = protectedCopy.payload ∧ normalFlow ≠ protectedCopy := by decide

def sampleKey : FullKey := ⟨1,2,3,[4,5],6,7,8,9,normalFlow⟩
theorem complete_original_cannot_be_one_metadata_arm :
    sampleKey ≠ { sampleKey with wholeOriginal := [4] } := by decide

theorem exact_exit_cannot_be_dropped : sampleKey ≠ { sampleKey with exit := 4 } := by decide

theorem frozen_snapshot_cannot_be_dropped : sampleKey ≠ { sampleKey with demandSnapshot := 10 } := by decide

theorem annotation_cannot_be_dropped : sampleKey ≠ { sampleKey with packet := protectedCopy } := by decide

/- This one fixed-slot run>=3 cell has an ANY demand, an abstract mark, empty E,
   and a stored EXACT or STAR tail. It is not a replacement native predicate. -/
def canEmitCell (demand stored : Tail) : Bool := demand = .any && stored = .exact

def canStoreCell (demand stored : Tail) : Bool :=
  canEmitCell demand stored || (stored = .star && canEmitCell demand .exact)

theorem NORMAL_FLOW_EXACT_STAR_preimage_required :
    canEmitCell .any .star = false ∧ canStoreCell .any .star = true := by decide

def metadataArm (arms : List Nat) (selected : Nat) : Bool := decide (selected ∈ arms)
def completeExecution (required supplied : List Nat) : Bool := required.all (fun x => decide (x ∈ supplied))

theorem ND_metadata_is_not_execution_OR :
    metadataArm [1,2] 1 = true ∧ completeExecution [1,2] [1] = false := by decide

def rowA : Row := ⟨1,1,1,1,4,0⟩
def rowB : Row := ⟨2,2,2,2,4,1⟩
def entryCell (original : Nat) (r : Row) : Bool := original == r.entry
def outputCell (r : Row) (raw : Nat) : Bool := raw == r.exit

theorem entry_exit_permissions_cannot_cross_pairs :
    (oldRows (entryCell 1) outputCell (fun r _ => [r.id]) [rowA,rowB] 2) = [] ∧
    (([rowA,rowB].any (entryCell 1)) && ([rowA,rowB].any (fun r => outputCell r 2))) = true := by decide

theorem different_positive_masks_cannot_share_key :
    { normalFlow with protection := [3] } ≠ { normalFlow with protection := [4] } := by decide

def localPreparationEnabled (run : Nat) (hasCompletion hasCarry zeroOriginal reachOutput : Bool) : Bool :=
  decide (run ≥ 3) && !hasCompletion && !hasCarry && !zeroOriginal && !reachOutput

theorem run2_uses_exact_native_fallback : localPreparationEnabled 2 false false false false = false := by decide

theorem static_completion_uses_exact_native_fallback : localPreparationEnabled 4 true false false false = false := by decide

theorem Zero_Reach_uses_exact_native_fallback :
    localPreparationEnabled 4 false false true false = false ∧
    localPreparationEnabled 4 false false false true = false := by decide

def savedTargetObserved (zeroOrigin normalTarget forward normalLayer alreadySaved : Bool) : Bool :=
  if zeroOrigin && normalTarget then false
  else if normalTarget then forward && normalLayer && !alreadySaved else true

theorem saved_ZERO_NormalTarget_has_no_new_effect : savedTargetObserved true true true true false = false := by decide

theorem backward_NormalTarget_never_observed : savedTargetObserved false true false true false = false := by decide

theorem DEMAND_NormalTarget_never_observed : savedTargetObserved false true true false false = false := by decide

def cycleProtection (wholeOriginal : List Nat) (recordMark : Nat) : Bool := decide (recordMark ∈ wholeOriginal)
theorem native_application_requires_complete_cycle_original :
    cycleProtection [1,2] 2 = true ∧ cycleProtection [1] 2 = false := by decide

def oldEntryChecks (rows parts outputs : Nat) : Nat := rows * parts * outputs
def preparedEntryChecks (rows : Nat) : Nat := rows

theorem fixed_entry_checks_do_not_depend_on_unique_full_keys :
    oldEntryChecks 2 2 3 = 12 ∧ preparedEntryChecks 2 = 2 := by decide

theorem preparation_can_cost_more_when_no_output_matches :
    oldEntryChecks 2 2 0 = 0 ∧ preparedEntryChecks 2 = 2 := by decide

theorem repeated_C2_projection_checks_removed (scopes : Nat) : scopes + scopes = 2 * scopes := by omega

end LoopQueryReuse
