/-
  Work removal for run-2 demand lookup. No production change.

  Part 1 models finite walks of labelled static-predecessor composition.
  A mapped right output and right geometry are immutable under prepend.
  FLOW is unresolved and must not be rejected as a fixed mapped output.
  Compatibility is a parameter: the implementation must use the current
  full/group-aware mark relation, not plain numeric equality.

  Part 2 models query-local owner-family memoization. The cache belongs to
  one immutable graph/method/view. It does not cross queries or snapshots.
  Exact result and incremental scratch state are observable in this model.

  These are scoped algorithm models, not a whole-driver or full AP proof.
  In particular, general entry-emission predicates are not assumed invariant
  under composition. The measured C5 opportunity concerns fixed right marks.
-/
import Std

namespace DemandWorkPruning

/-! ## 1. Removing downward-closed dead branches -/

inductive Walk {S : Type} (step : S → S → Prop) : S → S → Prop where
  | nil (s : S) : Walk step s s
  | cons {s t u : S} : step s t → Walk step t u → Walk step s u

def keptStep {S : Type} (step : S → S → Prop) (bad : S → Bool) (s t : S) : Prop :=
  step s t ∧ bad s = false ∧ bad t = false

theorem bad_persists_on_walk {S : Type} (step : S → S → Prop) (bad : S → Bool)
    (closed : ∀ s t, step s t → bad s = true → bad t = true)
    {s t : S} (path : Walk step s t) (hb : bad s = true) : bad t = true := by
  induction path with
  | nil => exact hb
  | cons edge _ ih => exact ih (closed _ _ edge hb)

theorem good_endpoint_has_good_start {S : Type} (step : S → S → Prop) (bad : S → Bool)
    (closed : ∀ s t, step s t → bad s = true → bad t = true)
    {s t : S} (path : Walk step s t) (ht : bad t = false) : bad s = false := by
  cases hs : bad s with
  | false => rfl
  | true =>
    have impossible := bad_persists_on_walk step bad closed path hs
    rw [ht] at impossible
    cases impossible

theorem good_walk_survives {S : Type} (step : S → S → Prop) (bad : S → Bool)
    (closed : ∀ s t, step s t → bad s = true → bad t = true)
    {s t : S} (path : Walk step s t) (ht : bad t = false) :
    Walk (keptStep step bad) s t := by
  induction path with
  | nil => exact .nil _
  | @cons s u t edge tail ih =>
    have hu := good_endpoint_has_good_start step bad closed tail ht
    have hs := good_endpoint_has_good_start step bad closed (.cons edge tail) ht
    exact .cons ⟨edge, hs, hu⟩ (ih ht)

theorem kept_walk_is_original {S : Type} (step : S → S → Prop) (bad : S → Bool)
    {s t : S} (path : Walk (keptStep step bad) s t) : Walk step s t := by
  induction path with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons edge.1 ih

def HasOutput {S O : Type} (step : S → S → Prop) (accept : S → O → Prop)
    (root : S) (out : O) : Prop :=
  ∃ target, Walk step root target ∧ accept target out

/-- All accepted outputs of all finite walks are preserved. On a finite
    graph this applies to an exhaustive worklist, including cyclic graphs.
    No DFS/BFS order or equality of diagnostic work counts is required. -/
theorem pruning_preserves_accepted_outputs {S O : Type} (step : S → S → Prop)
    (bad : S → Bool) (accept : S → O → Prop)
    (closed : ∀ s t, step s t → bad s = true → bad t = true)
    (acceptedGood : ∀ s out, accept s out → bad s = false)
    (root : S) (out : O) :
    HasOutput step accept root out ↔
      bad root = false ∧ HasOutput (keptStep step bad) accept root out := by
  constructor
  · rintro ⟨target, path, observed⟩
    have hg := acceptedGood target out observed
    exact ⟨good_endpoint_has_good_start step bad closed path hg,
      target, good_walk_survives step bad closed path hg, observed⟩
  · rintro ⟨_, target, path, observed⟩
    exact ⟨target, kept_walk_is_original step bad path, observed⟩

inductive Marks where
  | flow
  | mapped (input output : Nat)
deriving DecidableEq, Repr

structure State where
  left : Nat
  rightGeometry : Nat
  marks : Marks
deriving DecidableEq, Repr

structure Edge where
  src : Nat
  dst : Nat
  marks : Marks
deriving DecidableEq, Repr

def composeMarks (compatible : Nat → Nat → Bool) (left right : Marks) : Option Marks :=
  match left, right with
  | .flow, r => some r
  | l, .flow => some l
  | .mapped li lo, .mapped ri ro =>
    if compatible lo ri then some (.mapped li ro) else none

def prepend (compatible : Nat → Nat → Bool) (edge : Edge) (state : State) : Option State :=
  if edge.dst = state.left then
    (composeMarks compatible edge.marks state.marks).map
      (fun marks => ⟨edge.src, state.rightGeometry, marks⟩)
  else none

def PrependStep (compatible : Nat → Nat → Bool) (edges : List Edge) (s t : State) : Prop :=
  ∃ edge, edge ∈ edges ∧ prepend compatible edge s = some t

theorem mapped_output_does_not_change (compatible : Nat → Nat → Bool)
    (left result : Marks) (ri ro : Nat)
    (h : composeMarks compatible left (.mapped ri ro) = some result) :
    ∃ input, result = .mapped input ro := by
  cases left with
  | flow =>
    have he : Marks.mapped ri ro = result := Option.some.inj h
    exact ⟨ri, he.symm⟩
  | mapped li lo =>
    change (if compatible lo ri then some (Marks.mapped li ro) else none) = some result at h
    cases hc : compatible lo ri with
    | false => simp [hc] at h
    | true =>
      simp only [hc, if_true] at h
      exact ⟨li, (Option.some.inj h).symm⟩

theorem prepend_preserves_fixed_right (compatible : Nat → Nat → Bool)
    (edge : Edge) (s t : State) (ri ro : Nat)
    (hm : s.marks = .mapped ri ro) (h : prepend compatible edge s = some t) :
    t.rightGeometry = s.rightGeometry ∧ ∃ input, t.marks = .mapped input ro := by
  unfold prepend at h
  split at h
  · cases hc : composeMarks compatible edge.marks s.marks with
    | none => simp [hc] at h
    | some result =>
      simp only [hc, Option.map_some] at h
      have he := Option.some.inj h
      subst t
      obtain ⟨input, hi⟩ := mapped_output_does_not_change compatible edge.marks result ri ro
        (by rw [hm] at hc; exact hc)
      exact ⟨rfl, input, hi⟩
  · cases h

/-- Only already-fixed mapped outputs can be bad. `rightCompatible` may use
    the provided initial, immutable right geometry and full/group mark rules. -/
def badFixedRight (rightCompatible : Nat → Nat → Bool) (s : State) : Bool :=
  match s.marks with
  | .flow => false
  | .mapped _ output => !rightCompatible s.rightGeometry output

theorem fixed_right_rejection_is_downward_closed (compatible rightCompatible : Nat → Nat → Bool)
    (edges : List Edge) (s t : State) (step : PrependStep compatible edges s t)
    (hb : badFixedRight rightCompatible s = true) : badFixedRight rightCompatible t = true := by
  obtain ⟨edge, _, he⟩ := step
  cases hm : s.marks with
  | flow => simp [badFixedRight, hm] at hb
  | mapped input output =>
    obtain ⟨hg, nextInput, hn⟩ := prepend_preserves_fixed_right compatible edge s t input output hm he
    simpa [badFixedRight, hm, hn, hg] using hb

theorem c5_fixed_right_pruning_keeps_outputs {O : Type}
    (compatible rightCompatible : Nat → Nat → Bool) (edges : List Edge)
    (accept : State → O → Prop)
    (acceptedGood : ∀ s out, accept s out → badFixedRight rightCompatible s = false)
    (root : State) (out : O) :
    HasOutput (PrependStep compatible edges) accept root out ↔
      badFixedRight rightCompatible root = false ∧
      HasOutput (keptStep (PrependStep compatible edges) (badFixedRight rightCompatible))
        accept root out :=
  pruning_preserves_accepted_outputs _ _ _
    (fixed_right_rejection_is_downward_closed compatible rightCompatible edges) acceptedGood root out

def equalMarks (a b : Nat) : Bool := a == b
def wantsOne (_geometry output : Nat) : Bool := output == 1

theorem fixed_bad_output_stays_bad :
    prepend equalMarks ⟨3, 2, .mapped 7 4⟩ ⟨2, 10, .mapped 4 9⟩ =
      some ⟨3, 10, .mapped 7 9⟩ ∧
    badFixedRight wantsOne ⟨2, 10, .mapped 4 9⟩ = true ∧
    badFixedRight wantsOne ⟨3, 10, .mapped 7 9⟩ = true := by decide

/-- A failed left endpoint can be repaired. Pruning on it would lose this
    accepted descendant, although the fixed right endpoint is compatible. -/
theorem left_mismatch_is_not_downward_closed :
    prepend equalMarks ⟨3, 2, .flow⟩ ⟨2, 10, .mapped 4 1⟩ =
      some ⟨3, 10, .mapped 4 1⟩ ∧
    (2 : Nat) ≠ 3 ∧ (3 : Nat) = 3 ∧
    badFixedRight wantsOne ⟨2, 10, .mapped 4 1⟩ = false ∧
    badFixedRight wantsOne ⟨3, 10, .mapped 4 1⟩ = false := by decide

theorem unresolved_flow_can_become_compatible_mapped :
    badFixedRight wantsOne ⟨2, 10, .flow⟩ = false ∧
    prepend equalMarks ⟨3, 2, .mapped 7 1⟩ ⟨2, 10, .flow⟩ =
      some ⟨3, 10, .mapped 7 1⟩ ∧
    badFixedRight wantsOne ⟨3, 10, .mapped 7 1⟩ = false := by decide

#print axioms pruning_preserves_accepted_outputs
#print axioms prepend_preserves_fixed_right
#print axioms c5_fixed_right_pruning_keeps_outputs

/-! ## 2. Query-local eligibility memo, with exact scratch preservation

`hit` is outsideGraph membership OR an owner in the monotone seen set.
`exhausted` means the pending stack is empty. The laws below expose the
production bridge: true returns have a persistent hit; false returns exhaust
the scratch with no hit. Processing another family cannot remove a seen hit.
Idempotence alone, without persistence across other families, is insufficient.
-/

structure IncrementalQuery (Family Scratch : Type) where
  run : Family → Scratch → Bool × Scratch
  hit : Family → Scratch → Bool
  exhausted : Scratch → Bool
  hitIdentity : ∀ family s, hit family s = true → run family s = (true, s)
  exhaustedIdentity : ∀ family s, exhausted s = true → run family s = (hit family s, s)
  truePost : ∀ family s next, run family s = (true, next) → hit family next = true
  falsePost : ∀ family s next, run family s = (false, next) →
    exhausted next = true ∧ hit family next = false
  hitMonotone : ∀ family other s, hit family s = true → hit family (run other s).2 = true

theorem repeated_family_is_state_identity {F S : Type} (q : IncrementalQuery F S)
    (family : F) (s : S) :
    q.run family (q.run family s).2 = ((q.run family s).1, (q.run family s).2) := by
  cases hr : q.run family s with
  | mk answer next =>
    cases answer with
    | true => exact q.hitIdentity family next (q.truePost family s next hr)
    | false =>
      obtain ⟨done, nohit⟩ := q.falsePost family s next hr
      have he := q.exhaustedIdentity family next done
      rw [nohit] at he
      exact he

theorem identity_survives_other_family {F S : Type} (q : IncrementalQuery F S)
    (family other : F) (answer : Bool) (s : S)
    (identity : q.run family s = (answer, s)) :
    q.run family (q.run other s).2 = (answer, (q.run other s).2) := by
  cases answer with
  | true =>
    exact q.hitIdentity family _
      (q.hitMonotone family other s (q.truePost family s s identity))
  | false =>
    have done := (q.falsePost family s s identity).1
    have nextSame : (q.run other s).2 = s :=
      congrArg Prod.snd (q.exhaustedIdentity other s done)
    rw [nextSame]
    exact identity

structure MemoState (Family Scratch : Type) where
  scratch : Scratch
  answers : Family → Option Bool

def emptyMemo {F S : Type} (s : S) : MemoState F S := ⟨s, fun _ => none⟩

def MemoValid {F S : Type} (q : IncrementalQuery F S) (state : MemoState F S) : Prop :=
  ∀ family answer, state.answers family = some answer →
    q.run family state.scratch = (answer, state.scratch)

def memoStep {F S : Type} [DecidableEq F] (q : IncrementalQuery F S)
    (family : F) (state : MemoState F S) : Bool × MemoState F S :=
  match state.answers family with
  | some answer => (answer, state)
  | none =>
    let result := q.run family state.scratch
    (result.1, ⟨result.2, fun other =>
      if other = family then some result.1 else state.answers other⟩)

theorem empty_memo_valid {F S : Type} (q : IncrementalQuery F S) (s : S) :
    MemoValid q (emptyMemo s) := by
  intro family answer h
  cases h

theorem memo_hit_changes_no_state {F S : Type} [DecidableEq F]
    (q : IncrementalQuery F S) (family : F) (state : MemoState F S) (answer : Bool)
    (hit : state.answers family = some answer) :
    memoStep q family state = (answer, state) := by
  simp only [memoStep, hit]

theorem memo_step_preserves_result_and_scratch {F S : Type} [DecidableEq F]
    (q : IncrementalQuery F S) (family : F) (state : MemoState F S)
    (valid : MemoValid q state) :
    ((memoStep q family state).1, (memoStep q family state).2.scratch) =
        q.run family state.scratch ∧
      MemoValid q (memoStep q family state).2 := by
  cases hc : state.answers family with
  | some answer =>
    rw [memo_hit_changes_no_state q family state answer hc]
    exact ⟨(valid family answer hc).symm, valid⟩
  | none =>
    cases hr : q.run family state.scratch with
    | mk answer next =>
      simp only [memoStep, hc, hr]
      constructor
      · trivial
      · intro other previous h
        change (if other = family then some answer else state.answers other) = some previous at h
        by_cases same : other = family
        · subst other
          simp only [if_true, Option.some.injEq] at h
          subst previous
          simpa only [hr] using repeated_family_is_state_identity q family state.scratch
        · rw [if_neg same] at h
          have persisted := identity_survives_other_family q other family previous
            state.scratch (valid other previous h)
          simpa only [hr] using persisted

def plainExec {F S : Type} (q : IncrementalQuery F S) : List F → S → List Bool × S
  | [], s => ([], s)
  | family :: rest, s =>
    let first := q.run family s
    let tail := plainExec q rest first.2
    (first.1 :: tail.1, tail.2)

def memoExec {F S : Type} [DecidableEq F] (q : IncrementalQuery F S) :
    List F → MemoState F S → List Bool × MemoState F S
  | [], state => ([], state)
  | family :: rest, state =>
    let first := memoStep q family state
    let tail := memoExec q rest first.2
    (first.1 :: tail.1, tail.2)

/-- For any interleaving of families, memoization gives the same Boolean
    answers and exactly the same incremental scratch as the uncached stream.
    This theorem concerns P2's given stream, not P1's changed query stream. -/
theorem memo_execution_preserves_results_and_scratch {F S : Type} [DecidableEq F]
    (q : IncrementalQuery F S) (families : List F) (state : MemoState F S)
    (valid : MemoValid q state) :
    (memoExec q families state).1 = (plainExec q families state.scratch).1 ∧
    (memoExec q families state).2.scratch = (plainExec q families state.scratch).2 ∧
    MemoValid q (memoExec q families state).2 := by
  induction families generalizing state with
  | nil => exact ⟨rfl, rfl, valid⟩
  | cons family rest ih =>
    obtain ⟨same, nextValid⟩ := memo_step_preserves_result_and_scratch q family state valid
    cases hs : memoStep q family state with
    | mk answer next =>
      simp only [hs] at same nextValid
      obtain ⟨answersSame, scratchSame, finalValid⟩ := ih next nextValid
      simp only [memoExec, hs, plainExec, ← same]
      exact ⟨congrArg (List.cons answer) answersSame, scratchSame, finalValid⟩

theorem empty_memo_execution_is_equivalent {F S : Type} [DecidableEq F]
    (q : IncrementalQuery F S) (families : List F) (s : S) :
    (memoExec q families (emptyMemo s)).1 = (plainExec q families s).1 ∧
    (memoExec q families (emptyMemo s)).2.scratch = (plainExec q families s).2 := by
  have h := memo_execution_preserves_results_and_scratch q families (emptyMemo s)
    (empty_memo_valid q s)
  exact ⟨h.1, h.2.1⟩

theorem memo_step_defined_support {F S : Type} [DecidableEq F]
    (q : IncrementalQuery F S) (family other : F) (state : MemoState F S)
    (h : ((memoStep q family state).2.answers other).isSome = true) :
    other = family ∨ (state.answers other).isSome = true := by
  cases hc : state.answers family with
  | some answer =>
    rw [memo_hit_changes_no_state q family state answer hc] at h
    exact .inr h
  | none =>
    simp only [memoStep, hc] at h
    change (if other = family then some (q.run family state.scratch).1
      else state.answers other).isSome = true at h
    by_cases same : other = family
    · exact .inl same
    · rw [if_neg same] at h
      exact .inr h

theorem memo_execution_defined_support {F S : Type} [DecidableEq F]
    (q : IncrementalQuery F S) (families : List F) (state : MemoState F S)
    (other : F) (h : ((memoExec q families state).2.answers other).isSome = true) :
    other ∈ families ∨ (state.answers other).isSome = true := by
  induction families generalizing state with
  | nil => exact .inr h
  | cons family rest ih =>
    change ((memoExec q rest (memoStep q family state).2).2.answers other).isSome = true at h
    cases ih (memoStep q family state).2 h with
    | inl member => exact .inl (List.mem_cons_of_mem family member)
    | inr defined =>
      cases memo_step_defined_support q family other state defined with
      | inl same => exact .inl (same ▸ List.mem_cons_self)
      | inr old => exact .inr old

theorem empty_memo_defines_only_queried_families {F S : Type} [DecidableEq F]
    (q : IncrementalQuery F S) (families : List F) (s : S) (other : F)
    (h : ((memoExec q families (emptyMemo s)).2.answers other).isSome = true) :
    other ∈ families := by
  cases memo_execution_defined_support q families (emptyMemo s) other h with
  | inl member => exact member
  | inr impossible => cases impossible

def removeFirst {A : Type} [DecidableEq A] (a : A) : List A → List A
  | [] => []
  | b :: rest => if a = b then rest else b :: removeFirst a rest

theorem unequal_member_survives_remove {A : Type} [DecidableEq A]
    (a x : A) (ys : List A) (different : x ≠ a) (member : x ∈ ys) :
    x ∈ removeFirst a ys := by
  induction ys with
  | nil => cases member
  | cons b rest ih =>
    cases List.mem_cons.mp member with
    | inl same =>
      by_cases ab : a = b
      · exact False.elim (different (same.trans ab.symm))
      · simp only [removeFirst, if_neg ab]
        exact List.mem_cons.mpr (.inl same)
    | inr tail =>
      by_cases ab : a = b
      · simpa only [removeFirst, if_pos ab] using tail
      · simp only [removeFirst, if_neg ab]
        exact List.mem_cons_of_mem b (ih tail)

theorem remove_first_length {A : Type} [DecidableEq A] (a : A) (ys : List A)
    (member : a ∈ ys) : (removeFirst a ys).length + 1 = ys.length := by
  induction ys with
  | nil => cases member
  | cons b rest ih =>
    by_cases same : a = b
    · simp only [removeFirst, if_pos same, List.length_cons]
    · have tail : a ∈ rest := by
        cases List.mem_cons.mp member with
        | inl impossible => exact False.elim (same impossible)
        | inr found => exact found
      simpa only [removeFirst, if_neg same, List.length_cons] using
        congrArg Nat.succ (ih tail)

/-- Constructive subset/cardinality proof with explicit DecidableEq.
    The standard generic List.erase lemmas use classical instances, so the
    small executable removeFirst above supplies the required witnesses. -/
theorem nodup_length_le_subset {A : Type} [DecidableEq A] {xs ys : List A}
    (unique : xs.Nodup) (sub : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a tail ih =>
    obtain ⟨fresh, uniqueTail⟩ := List.nodup_cons.mp unique
    have member : a ∈ ys := sub List.mem_cons_self
    have subTail : tail ⊆ removeFirst a ys := by
      intro x hx
      have unequal : x ≠ a := by
        intro same
        exact fresh (same ▸ hx)
      exact unequal_member_survives_remove a x ys unequal (sub (List.mem_cons_of_mem a hx))
    have bound := ih uniqueTail subTail
    calc
      (a :: tail).length = tail.length + 1 := rfl
      _ ≤ (removeFirst a ys).length + 1 := Nat.succ_le_succ bound
      _ = ys.length := remove_first_length a ys member

def definedFamilyIds {n : Nat} {S : Type} (state : MemoState (Fin n) S) : List (Fin n) :=
  (List.finRange n).filter fun family => (state.answers family).isSome

/-- A dense UNKNOWN/FALSE/TRUE array allocates n cells when first needed.
    At most n cells can become defined; the array is released with the view. -/
theorem dense_memo_domain_bound {n : Nat} {S : Type} (state : MemoState (Fin n) S) :
    (definedFamilyIds state).length ≤ n := by
  simpa only [definedFamilyIds, List.length_finRange] using
    List.length_filter_le (fun family => (state.answers family).isSome) (List.finRange n)

/-- Defined cells after a query are bounded by distinct family IDs actually
    queried. This is separate from the dense array's n-byte allocation bound. -/
theorem memo_defined_cells_bound_by_distinct_families {n : Nat} {S : Type}
    (q : IncrementalQuery (Fin n) S) (families : List (Fin n)) (s : S) :
    (definedFamilyIds (memoExec q families (emptyMemo s)).2).length ≤
      families.eraseDups.length := by
  apply nodup_length_le_subset
  · exact List.Pairwise.filter _ (List.nodup_finRange n)
  · intro family member
    have defined := (List.mem_filter.mp member).2
    exact List.mem_eraseDups.mpr (empty_memo_defines_only_queried_families q families s family defined)

/-! ## 3. Finite source-model control

Graph: 0 -> 1; vertex 2 is unreachable from root 0. Scratch IDs encode:
  0 = seen {0}, pending {0};
  1 = seen {0,1}, pending {1};
  2 = seen {0,1}, pending empty.
Each owner-family is a singleton vertex. This is a closed finite instance
of the incremental query laws, not a proof of every JVM graph operation.
-/

def smallHit (family state : Fin 3) : Bool :=
  family.val == 0 || (family.val == 1 && state.val != 0)

def smallRun (family state : Fin 3) : Bool × Fin 3 :=
  if smallHit family state then (true, state)
  else if family.val == 1 then (true, 1) else (false, 2)

def smallQuery : IncrementalQuery (Fin 3) (Fin 3) where
  run := smallRun
  hit := smallHit
  exhausted := fun state => state.val == 2
  hitIdentity := by decide
  exhaustedIdentity := by decide
  truePost := by decide
  falsePost := by decide
  hitMonotone := by decide

def smallFamilies : List (Fin 3) := [1, 1, 0, 2, 2, 1]

theorem finite_interleaved_control :
    (plainExec smallQuery smallFamilies 0) = ([true, true, true, false, false, true], 2) ∧
    (memoExec smallQuery smallFamilies (emptyMemo 0)).1 =
      [true, true, true, false, false, true] ∧
    (memoExec smallQuery smallFamilies (emptyMemo 0)).2.scratch = 2 ∧
    (definedFamilyIds (memoExec smallQuery smallFamilies (emptyMemo 0)).2).length = 3 := by decide

def check : Bool :=
  prepend equalMarks ⟨3, 2, .flow⟩ ⟨2, 10, .mapped 4 9⟩ ==
    some ⟨3, 10, .mapped 4 9⟩ &&
  badFixedRight wantsOne ⟨3, 10, .mapped 4 9⟩ &&
  (memoExec smallQuery smallFamilies (emptyMemo 0)).1 ==
    (plainExec smallQuery smallFamilies 0).1 &&
  (memoExec smallQuery smallFamilies (emptyMemo 0)).2.scratch ==
    (plainExec smallQuery smallFamilies 0).2

theorem checked : check = true := by decide

#eval check

#print axioms repeated_family_is_state_identity
#print axioms identity_survives_other_family
#print axioms memo_execution_preserves_results_and_scratch
#print axioms memo_defined_cells_bound_by_distinct_families
#print axioms nodup_length_le_subset
#print axioms dense_memo_domain_bound
#print axioms finite_interleaved_control

end DemandWorkPruning
