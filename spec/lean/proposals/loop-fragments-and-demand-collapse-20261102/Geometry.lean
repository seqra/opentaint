import Init

/-!
Executable prefix-guided DATA projection for loop-fragment boundaries.

Scope: finite nonstatic bases, counted field symbols and concrete FULL marks;
scalar EXACT/MAY facts, empty field exclusions, and a carried protection bit.
`demands` is already scoped to the correct fragment, direction, status,
base and mark by the caller. Its paths supply precision, not publication
permission. This module does not replace paired C2/C5 admission.

The demand paths denote a prefix trie. While the raw path follows that
trie, retain its requested prefix. At the first missing branch, retain
the distinguishing field and cut the remaining suffix. An unmatched
path therefore retains its first field. A real cut is MAY/DEMAND and
preserves base, mark and protection. No blanket keep-on-refinement rule
is used.

Static anchors, uncounted accessors, STAR/MUST, E/mx, packed forests,
complete ND originals, FLOW suffix correlation, branch admission and
cross-run refinement require separate adapters/proofs. The coverage
theorem concerns possible marked locations; it is not NORMAL evidence
or a whole-program completeness theorem.
-/
namespace LoopFragments.Geometry
set_option autoImplicit false

abbrev Field (count : Nat) := Fin count
abbrev Path (count : Nat) := List (Field count)

inductive Tail where | exact | may deriving DecidableEq, Repr
inductive Layer where | normal | demand deriving DecidableEq, Repr

structure Fact (bases marks fields : Nat) where
  base : Fin bases
  mark : Fin marks
  path : Path fields
  tail : Tail
  layer : Layer
  protection : Bool := false
  deriving DecidableEq, Repr

variable {bases marks fields : Nat}

/-- The children below one trie edge. Empty demand paths denote terminal nodes. -/
def children (field : Field fields) : List (Path fields) → List (Path fields)
  | [] => []
  | [] :: rest => children field rest
  | (head :: suffix) :: rest =>
      if field = head then suffix :: children field rest else children field rest

def maxDepth : List (Path fields) → Nat
  | [] => 0
  | path :: rest => max path.length (maxDepth rest)

/-- Retain the first unmatched field, never its unrequested descendants. -/
def triePrefix (demands : List (Path fields)) : Path fields → Path fields
  | [] => []
  | field :: rest =>
      field :: if children field demands = [] then []
               else triePrefix (children field demands) rest

/-- The positive global limit can also cut inside a requested prefix. -/
def keptPath (global : Nat) (demands : List (Path fields)) (raw : Path fields) : Path fields :=
  (triePrefix demands raw).take global

def project (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) : Fact bases marks fields :=
  if keptPath global demands raw.path = raw.path then raw
  else { raw with path := keptPath global demands raw.path, tail := .may, layer := .demand }

def possiblePath (tail : Tail) (anchor location : Path fields) : Prop :=
  match tail with
  | .exact => location = anchor
  | .may => anchor.IsPrefix location

def possible (value : Fact bases marks fields) (base : Fin bases)
    (mark : Fin marks) (location : Path fields) : Prop :=
  base = value.base ∧ mark = value.mark ∧ possiblePath value.tail value.path location

theorem children_member (field : Field fields) (demands : List (Path fields))
    (suffix : Path fields) : suffix ∈ children field demands → (field :: suffix) ∈ demands := by
  induction demands with
  | nil => simp [children]
  | cons path rest ih =>
      cases path with
      | nil =>
          intro member
          exact List.mem_cons_of_mem _ (ih member)
      | cons head tail =>
          by_cases same : field = head
          · subst head
            rw [children, if_pos rfl]
            intro member
            rcases List.mem_cons.mp member with sameTail | later
            · exact List.mem_cons.mpr (Or.inl (congrArg (List.cons field) sameTail))
            · exact List.mem_cons.mpr (Or.inr (ih later))
          · simp only [children, if_neg same]
            intro member
            exact List.mem_cons_of_mem _ (ih member)

theorem member_depth_bound (demands : List (Path fields)) (path : Path fields)
    (member : path ∈ demands) : path.length ≤ maxDepth demands := by
  induction demands with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with equal | later
      · subst path
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

/-- A maximum has an executable list-member witness whenever the directory is nonempty. -/
def deepest : List (Path fields) → Option (Path fields)
  | [] => none
  | path :: rest =>
      match deepest rest with
      | none => some path
      | some later => if path.length < later.length then some later else some path

theorem deepest_spec (demands : List (Path fields)) :
    match deepest demands with
    | none => demands = []
    | some path => path ∈ demands ∧ path.length = maxDepth demands := by
  induction demands with
  | nil => rfl
  | cons head rest ih =>
      simp only [deepest]
      cases found : deepest rest with
      | none =>
          simp only [found] at ih ⊢
          subst rest
          simp [maxDepth]
      | some later =>
          simp only [found] at ih ⊢
          by_cases larger : head.length < later.length
          · simp only [if_pos larger]
            exact ⟨List.mem_cons_of_mem _ ih.1, by simp [maxDepth, ← ih.2, Nat.max_eq_right (Nat.le_of_lt larger)]⟩
          · simp only [if_neg larger]
            exact ⟨List.mem_cons_self, by simp [maxDepth, ← ih.2, Nat.max_eq_left (Nat.le_of_not_gt larger)]⟩

theorem children_depth_step (field : Field fields) (demands : List (Path fields))
    (nonempty : children field demands ≠ []) :
    maxDepth (children field demands) + 1 ≤ maxDepth demands := by
  have witness := deepest_spec (children field demands)
  cases found : deepest (children field demands) with
  | none =>
      simp only [found] at witness
      exact False.elim (nonempty witness)
  | some suffix =>
      simp only [found] at witness
      have bound := member_depth_bound demands (field :: suffix) (children_member field demands suffix witness.1)
      simpa only [List.length_cons, witness.2] using bound

theorem prefix_transitive {a b c : Path fields} (ab : a.IsPrefix b) (bc : b.IsPrefix c) :
    a.IsPrefix c := by
  obtain ⟨left, hl⟩ := ab
  obtain ⟨right, hr⟩ := bc
  exact ⟨left ++ right, by rw [← List.append_assoc, hl, hr]⟩

theorem triePrefix_is_prefix (demands : List (Path fields)) (raw : Path fields) :
    (triePrefix demands raw).IsPrefix raw := by
  induction raw generalizing demands with
  | nil => exact ⟨[], rfl⟩
  | cons field rest ih =>
      simp only [triePrefix]
      split
      · exact ⟨rest, rfl⟩
      · obtain ⟨suffix, same⟩ := ih (children field demands)
        exact ⟨suffix, by simpa only [List.cons_append] using congrArg (List.cons field) same⟩

theorem triePrefix_depth_bound (demands : List (Path fields)) (raw : Path fields) :
    (triePrefix demands raw).length ≤ maxDepth demands + 1 := by
  induction raw generalizing demands with
  | nil => exact Nat.zero_le _
  | cons field rest ih =>
      simp only [triePrefix]
      split
      · simp
      next nonempty =>
        have below := ih (children field demands)
        have step := children_depth_step field demands nonempty
        simpa only [List.length_cons] using Nat.le_trans (Nat.add_le_add_right below 1) (Nat.add_le_add_right step 1)

theorem keptPath_is_prefix (global : Nat) (demands : List (Path fields)) (raw : Path fields) :
    (keptPath global demands raw).IsPrefix raw := by
  exact prefix_transitive (List.take_prefix global _) (triePrefix_is_prefix demands raw)

theorem keptPath_global_bound (global : Nat) (demands : List (Path fields)) (raw : Path fields) :
    (keptPath global demands raw).length ≤ global := by
  exact List.length_take_le _ _

theorem keptPath_demand_bound (global : Nat) (demands : List (Path fields)) (raw : Path fields) :
    (keptPath global demands raw).length ≤ maxDepth demands + 1 := by
  have shorter : (keptPath global demands raw).length ≤ (triePrefix demands raw).length := by
    simp only [keptPath, List.length_take]
    exact Nat.min_le_right _ _
  exact Nat.le_trans shorter (triePrefix_depth_bound demands raw)

theorem unmatched_retains_distinction (field : Field fields) (rest : Path fields)
    (demands : List (Path fields)) (missing : children field demands = []) :
    triePrefix demands (field :: rest) = [field] := by
  simp [triePrefix, missing]

theorem positive_limit_retains_first_field (global : Nat) (positive : 0 < global)
    (demands : List (Path fields)) (field : Field fields) (rest : Path fields) :
    (keptPath global demands (field :: rest)).head? = some field := by
  cases global with
  | zero => cases positive
  | succ remaining => simp [keptPath, triePrefix]

theorem project_base (global : Nat) (demands : List (Path fields)) (raw : Fact bases marks fields) :
    (project global demands raw).base = raw.base := by unfold project; split <;> rfl

theorem project_mark (global : Nat) (demands : List (Path fields)) (raw : Fact bases marks fields) :
    (project global demands raw).mark = raw.mark := by unfold project; split <;> rfl

theorem project_protection (global : Nat) (demands : List (Path fields)) (raw : Fact bases marks fields) :
    (project global demands raw).protection = raw.protection := by unfold project; split <;> rfl

theorem project_path (global : Nat) (demands : List (Path fields)) (raw : Fact bases marks fields) :
    (project global demands raw).path = keptPath global demands raw.path := by
  unfold project
  split
  next same => exact same.symm
  next => rfl

theorem project_loss_is_demand (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) (loss : keptPath global demands raw.path ≠ raw.path) :
    (project global demands raw).tail = .may ∧ (project global demands raw).layer = .demand := by
  simp only [project, loss, ↓reduceIte, and_self]

theorem project_demand_stays_demand (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) (demand : raw.layer = .demand) :
    (project global demands raw).layer = .demand := by
  unfold project
  split
  · exact demand
  · rfl

theorem project_normal_is_unchanged (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) (normal : (project global demands raw).layer = .normal) :
    project global demands raw = raw := by
  unfold project at normal ⊢
  split at normal
  next same => simp only [same, ↓reduceIte]
  next different => cases normal

theorem project_possible_coverage (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) (base : Fin bases) (mark : Fin marks) (location : Path fields)
    (actual : possible raw base mark location) : possible (project global demands raw) base mark location := by
  unfold project
  split
  · exact actual
  next different =>
    obtain ⟨sameBase, sameMark, path⟩ := actual
    refine ⟨sameBase, sameMark, ?_⟩
    change (keptPath global demands raw.path).IsPrefix location
    cases tail : raw.tail with
    | exact =>
        have same : location = raw.path := by simpa only [possiblePath, tail] using path
        rw [same]
        exact keptPath_is_prefix global demands raw.path
    | may =>
        exact prefix_transitive (keptPath_is_prefix global demands raw.path)
          (by simpa only [possiblePath, tail] using path)

theorem parent_member_children (field : Field fields) (demands : List (Path fields))
    (suffix : Path fields) (member : (field :: suffix) ∈ demands) :
    suffix ∈ children field demands := by
  induction demands with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with equal | later
      · subst head
        rw [children, if_pos rfl]
        exact List.mem_cons_self
      · cases head with
        | nil => exact ih later
        | cons first tail =>
            by_cases same : field = first
            · rw [children, if_pos same]
              exact List.mem_cons_of_mem _ (ih later)
            · simpa only [children, if_neg same] using ih later

theorem requested_path_retained (demands : List (Path fields)) (path : Path fields)
    (member : path ∈ demands) : triePrefix demands path = path := by
  induction path generalizing demands with
  | nil => rfl
  | cons field rest ih =>
      have child := parent_member_children field demands rest member
      have nonempty : children field demands ≠ [] := by
        intro empty
        rw [empty] at child
        cases child
      simp only [triePrefix, if_neg nonempty]
      exact congrArg (List.cons field) (ih _ child)

theorem triePrefix_commutes_take (demands : List (Path fields)) (raw : Path fields) (n : Nat) :
    triePrefix demands (raw.take n) = (triePrefix demands raw).take n := by
  induction n generalizing demands raw with
  | zero => rfl
  | succ n ih =>
      cases raw with
      | nil => rfl
      | cons field rest =>
          by_cases missing : children field demands = []
          · simp [triePrefix, missing]
          · simp [triePrefix, missing, ih]

theorem requested_prefix_retained (demands : List (Path fields)) (path : Path fields)
    (member : path ∈ demands) (n : Nat) :
    triePrefix demands (path.take n) = path.take n := by
  rw [triePrefix_commutes_take, requested_path_retained demands path member]

theorem triePrefix_idempotent (demands : List (Path fields)) (raw : Path fields) :
    triePrefix demands (triePrefix demands raw) = triePrefix demands raw := by
  induction raw generalizing demands with
  | nil => rfl
  | cons field rest ih =>
      by_cases missing : children field demands = []
      · simp [triePrefix, missing]
      · simp [triePrefix, missing, ih]

theorem keptPath_idempotent (global : Nat) (demands : List (Path fields)) (raw : Path fields) :
    keptPath global demands (keptPath global demands raw) = keptPath global demands raw := by
  simp only [keptPath, triePrefix_commutes_take, triePrefix_idempotent, List.take_take, Nat.min_self]

theorem project_idempotent (global : Nat) (demands : List (Path fields)) (raw : Fact bases marks fields) :
    project global demands (project global demands raw) = project global demands raw := by
  have same : keptPath global demands (project global demands raw).path = (project global demands raw).path := by
    rw [project_path, keptPath_idempotent]
  rw [project, if_pos same]

/-- Rejected fallback policy: forcing MAY can add a new C2 candidate.
    This function is retained only for the explicit counterexample in Admission. -/
def forceMayDemand (raw : Fact bases marks fields) : Fact bases marks fields :=
  { raw with tail := .may, layer := .demand }

def rejectedForcedProject (eligible : Bool) (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) : Fact bases marks fields :=
  if eligible then project global demands raw
  else forceMayDemand (project global demands raw)

theorem forceMayDemand_possible_coverage (raw : Fact bases marks fields)
    (base : Fin bases) (mark : Fin marks) (location : Path fields)
    (actual : possible raw base mark location) : possible (forceMayDemand raw) base mark location := by
  obtain ⟨sameBase, sameMark, path⟩ := actual
  refine ⟨sameBase, sameMark, ?_⟩
  change raw.path.IsPrefix location
  cases tail : raw.tail with
  | exact =>
      have same : location = raw.path := by simpa only [possiblePath, tail] using path
      exact ⟨[], by simp [same]⟩
  | may => simpa only [possiblePath, tail] using path

theorem rejected_ineligible_is_may_demand (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) :
    (rejectedForcedProject false global demands raw).tail = .may ∧
    (rejectedForcedProject false global demands raw).layer = .demand := ⟨rfl, rfl⟩

theorem rejected_eligible_projection_is_core (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) : rejectedForcedProject true global demands raw = project global demands raw := rfl

theorem rejectedForcedProject_path (eligible : Bool) (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) :
    (rejectedForcedProject eligible global demands raw).path = keptPath global demands raw.path := by
  cases eligible <;> simp only [rejectedForcedProject, Bool.false_eq_true, ↓reduceIte, forceMayDemand, project_path]

theorem rejectedForcedProject_base (eligible : Bool) (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) : (rejectedForcedProject eligible global demands raw).base = raw.base := by
  cases eligible <;> simp only [rejectedForcedProject, Bool.false_eq_true, ↓reduceIte, forceMayDemand, project_base]

theorem rejectedForcedProject_mark (eligible : Bool) (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) : (rejectedForcedProject eligible global demands raw).mark = raw.mark := by
  cases eligible <;> simp only [rejectedForcedProject, Bool.false_eq_true, ↓reduceIte, forceMayDemand, project_mark]

theorem rejectedForcedProject_protection (eligible : Bool) (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) : (rejectedForcedProject eligible global demands raw).protection = raw.protection := by
  cases eligible <;> simp only [rejectedForcedProject, Bool.false_eq_true, ↓reduceIte, forceMayDemand, project_protection]

theorem rejectedForcedProject_possible_coverage (eligible : Bool) (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) (base : Fin bases) (mark : Fin marks) (location : Path fields)
    (actual : possible raw base mark location) :
    possible (rejectedForcedProject eligible global demands raw) base mark location := by
  cases eligible with
  | false => exact forceMayDemand_possible_coverage _ base mark location (project_possible_coverage global demands raw base mark location actual)
  | true => exact project_possible_coverage global demands raw base mark location actual

theorem rejectedForcedProject_normal_requires_eligible_and_unchanged (eligible : Bool) (global : Nat)
    (demands : List (Path fields)) (raw : Fact bases marks fields)
    (normal : (rejectedForcedProject eligible global demands raw).layer = .normal) :
    eligible = true ∧ rejectedForcedProject eligible global demands raw = raw := by
  cases eligible with
  | false => cases normal
  | true => exact ⟨rfl, project_normal_is_unchanged global demands raw normal⟩

/-- Selected gate. Its caller supplies complete consumer eligibility; this module
    does not choose the policy for persisted NORMAL summaries. -/
def selectProject (eligible : Bool) (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) : Option (Fact bases marks fields) :=
  if eligible then some (project global demands raw) else none

theorem selectProject_ineligible_is_none (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) : selectProject false global demands raw = none := rfl

theorem selectProject_eligible_is_core (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) : selectProject true global demands raw = some (project global demands raw) := rfl

theorem selectProject_result_has_eligibility (eligible : Bool) (global : Nat)
    (demands : List (Path fields)) (raw result : Fact bases marks fields)
    (produced : selectProject eligible global demands raw = some result) :
    eligible = true ∧ result = project global demands raw := by
  cases eligible with
  | false => cases produced
  | true => exact ⟨rfl, Option.some.inj produced |>.symm⟩

/-- An executable finite directory of all paths with at most the chosen depth. -/
def pathsUpTo (fields : Nat) : Nat → List (Path fields)
  | 0 => [[]]
  | n + 1 => [] :: (List.finRange fields).flatMap fun field =>
      (pathsUpTo fields n).map (List.cons field)

theorem pathsUpTo_complete (bound : Nat) (path : Path fields) (within : path.length ≤ bound) :
    path ∈ pathsUpTo fields bound := by
  induction bound generalizing path with
  | zero =>
      have empty : path = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero within)
      subst path
      exact List.mem_cons_self
  | succ bound ih =>
      cases path with
      | nil => exact List.mem_cons_self
      | cons field rest =>
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨field, List.mem_finRange field, ?_⟩
          exact List.mem_map.mpr ⟨rest, ih rest (Nat.le_of_succ_le_succ within), rfl⟩

theorem flatMap_constant_length {α β : Type} (xs : List α) (f : α → List β)
    (count : Nat) (constant : ∀ x ∈ xs, (f x).length = count) :
    (xs.flatMap f).length = xs.length * count := by
  induction xs with
  | nil => simp
  | cons head rest ih =>
      rw [List.flatMap_cons, List.length_append, constant head List.mem_cons_self]
      rw [ih (fun x member => constant x (List.mem_cons_of_mem _ member))]
      simp [Nat.succ_mul, Nat.add_comm]

def pathCapacity (fields : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => 1 + fields * pathCapacity fields n

theorem pathsUpTo_capacity (fields bound : Nat) :
    (pathsUpTo fields bound).length = pathCapacity fields bound := by
  induction bound with
  | zero => rfl
  | succ n ih =>
      simp only [pathsUpTo, List.length_cons]
      rw [flatMap_constant_length _ _ (pathCapacity fields n)]
      · simp only [List.length_finRange, pathCapacity, Nat.add_comm]
      · intro field _
        simpa only [List.length_map] using ih

/-- A concrete finite image witness. No infinite set or choice is used. -/
def factDirectory (bases marks fields bound : Nat) : List (Fact bases marks fields) :=
  (List.finRange bases).flatMap fun base =>
  (List.finRange marks).flatMap fun mark =>
  (pathsUpTo fields bound).flatMap fun path =>
  [Tail.exact, Tail.may].flatMap fun tail =>
  [Layer.normal, Layer.demand].flatMap fun layer =>
  [false, true].map fun protection => ⟨base, mark, path, tail, layer, protection⟩

theorem factDirectory_complete (bound : Nat) (fact : Fact bases marks fields)
    (within : fact.path.length ≤ bound) : fact ∈ factDirectory bases marks fields bound := by
  apply List.mem_flatMap.mpr
  refine ⟨fact.base, List.mem_finRange fact.base, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨fact.mark, List.mem_finRange fact.mark, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨fact.path, pathsUpTo_complete bound fact.path within, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨fact.tail, ?_, ?_⟩
  · cases fact.tail <;> simp
  · apply List.mem_flatMap.mpr
    refine ⟨fact.layer, ?_, ?_⟩
    · cases fact.layer <;> simp
    · apply List.mem_map.mpr
      refine ⟨fact.protection, ?_, ?_⟩
      · cases fact.protection <;> simp
      · cases fact
        rfl

theorem project_finite_image_member (global : Nat) (demands : List (Path fields))
    (raw : Fact bases marks fields) :
    project global demands raw ∈ factDirectory bases marks fields (min global (maxDepth demands + 1)) := by
  apply factDirectory_complete
  rw [project_path]
  exact Nat.le_min.mpr ⟨keptPath_global_bound global demands raw.path,
    keptPath_demand_bound global demands raw.path⟩

theorem executable_finite_image (global : Nat) (demands : List (Path fields)) :
    ∃ directory : List (Fact bases marks fields),
      ∀ raw, project global demands raw ∈ directory :=
  ⟨factDirectory bases marks fields (min global (maxDepth demands + 1)),
    project_finite_image_member global demands⟩

theorem selected_results_have_finite_image (eligible : Bool) (global : Nat)
    (demands : List (Path fields)) (raw result : Fact bases marks fields)
    (produced : selectProject eligible global demands raw = some result) :
    result ∈ factDirectory bases marks fields (min global (maxDepth demands + 1)) := by
  obtain ⟨_, same⟩ := selectProject_result_has_eligibility eligible global demands raw result produced
  rw [same]
  exact project_finite_image_member global demands raw

/-- Raw word-language enumeration used by the binary-read workload witness. -/
def words (fields : Nat) : Nat → List (Path fields)
  | 0 => [[]]
  | n + 1 => (List.finRange fields).flatMap fun field =>
      (words fields n).map (List.cons field)

theorem words_work (fields length : Nat) : (words fields length).length = fields ^ length := by
  induction length with
  | zero => rfl
  | succ n ih =>
      unfold words
      rw [flatMap_constant_length _ _ (fields ^ n)]
      · simp [Nat.pow_succ, Nat.mul_comm]
      · intro field _
        simpa only [List.length_map] using ih

def binarySample (path : Path 2) : Fact 1 1 2 := ⟨0, 0, path, .exact, .normal, false⟩

/-- The rejected Boolean policy: any descendant refines the root MAY demand. -/
def booleanKeep (raw : Fact 1 1 2) : Fact 1 1 2 :=
  if ([] : Path 2).isPrefixOf raw.path then raw else project 1 [[]] raw

theorem boolean_keep_all_descendants (raw : Fact 1 1 2) : booleanKeep raw = raw := by
  simp [booleanKeep]

theorem boolean_refinement_has_no_depth_bound (n : Nat) :
    (booleanKeep (binarySample (List.replicate (n + 2) 0))).path.length = n + 2 := by
  simp [boolean_keep_all_descendants, binarySample]

theorem projected_binary_root_bound (global : Nat) (path : Path 2) :
    (project global [[]] (binarySample path)).path.length ≤ 1 := by
  rw [project_path]
  simpa only [binarySample, maxDepth, List.length_nil, Nat.max_self, Nat.zero_add] using
    keptPath_demand_bound global ([[]] : List (Path 2)) path

def rootImage (field : Field 2) : Fact 1 1 2 := ⟨0, 0, [field], .may, .demand, false⟩

theorem deep_root_image (global : Nat) (positive : 0 < global)
    (first second : Field 2) (rest : Path 2) :
    project global [[]] (binarySample (first :: second :: rest)) = rootImage first := by
  have kept : keptPath global [[]] (first :: second :: rest) = [first] := by
    cases global with
    | zero => cases positive
    | succ n => simp [keptPath, triePrefix, children]
  have changed : keptPath global [[]] (binarySample (first :: second :: rest)).path ≠
      (binarySample (first :: second :: rest)).path := by
    simp only [binarySample, kept]
    intro same
    have lengths := congrArg List.length same
    simp only [List.length_cons, List.length_nil] at lengths
    have impossible : 0 = rest.length + 1 := Nat.succ.inj lengths
    exact Nat.noConfusion impossible
  rw [project, if_neg changed]
  simp only [binarySample, kept, rootImage]

theorem binary_field_zero_or_one (field : Field 2) : field = 0 ∨ field = 1 := by
  refine Fin.cases (Or.inl rfl) (fun tail => ?_) field
  have zero : tail = 0 := Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ tail.isLt))
  subst tail
  exact Or.inr rfl

/-- For arbitrarily deep binary inputs, two concrete MAY/DEMAND results suffice. -/
theorem deep_binary_projection_two_image_witness (global : Nat) (positive : 0 < global)
    (path : Path 2) (deep : 2 ≤ path.length) :
    project global [[]] (binarySample path) ∈ [rootImage 0, rootImage 1] := by
  cases path with
  | nil => exact False.elim (Nat.not_succ_le_zero 1 deep)
  | cons first rest =>
      cases rest with
      | nil => exact False.elim (Nat.not_succ_le_zero 0 (Nat.le_of_succ_le_succ deep))
      | cons second later =>
          rw [deep_root_image global positive first second later]
          rcases binary_field_zero_or_one first with zero | one
          · subst first
            exact List.mem_cons_self
          · subst first
            exact List.mem_cons_of_mem _ List.mem_cons_self

theorem words_member_length (fields length : Nat) (path : Path fields)
    (member : path ∈ words fields length) : path.length = length := by
  induction length generalizing path with
  | zero =>
      have same : path = [] := by simpa only [words, List.mem_singleton] using member
      subst path
      rfl
  | succ length ih =>
      rcases List.mem_flatMap.mp member with ⟨field, _, produced⟩
      rcases List.mem_map.mp produced with ⟨rest, below, same⟩
      subst path
      simp only [List.length_cons, ih rest below]

theorem binary_exponential_offers_have_two_bounded_images (n : Nat) (global : Nat)
    (positive : 0 < global) :
    (words 2 (n + 2)).length = 2 ^ (n + 2) ∧
    ∀ path ∈ words 2 (n + 2), project global [[]] (binarySample path) ∈ [rootImage 0, rootImage 1] := by
  refine ⟨words_work 2 (n + 2), ?_⟩
  intro path member
  apply deep_binary_projection_two_image_witness global positive path
  rw [words_member_length 2 (n + 2) path member]
  exact Nat.le_add_left 2 n

theorem eight_boolean_outputs_stay_eight :
    ((words 2 3).map (fun path => booleanKeep (binarySample path))).eraseDups.length = 8 := by decide

theorem eight_projection_outputs_become_two :
    ((words 2 3).map (fun path => project 3 [[]] (binarySample path))).eraseDups.length = 2 := by decide

theorem first_unmatched_branch_is_not_erased :
    (project 4 [[0, 0]] (binarySample [0, 1, 0, 0])).path = [0, 1] ∧
    (project 4 [[0, 0]] (binarySample [0, 1, 0, 0])).layer = .demand := by decide

theorem matching_requested_prefix_keeps_only_one_new_field :
    (project 5 [[0, 0]] (binarySample [0, 0, 1, 0])).path = [0, 0, 1] ∧
    (project 5 [[0, 0]] (binarySample [0, 0, 1, 0])).layer = .demand := by decide

end LoopFragments.Geometry
