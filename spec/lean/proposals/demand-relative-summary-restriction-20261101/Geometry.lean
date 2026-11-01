import Init

/-!
Scalar data geometry for the demand-relative C5 proposal.

An Accessor list is finite. Class anchors cost zero; named fields and array
elements cost one. A base is an opaque DATA-base identifier, never ZERO or
Target. Marks are concrete FULL-mark identities. Fields E and FLOW mark
exclusions, correlated FLOW and packed payloads are outside this module.

`possible` describes candidate locations, not a universal MUST assertion or
NORMAL report evidence. Cutting preserves these locations and moves any lost
geometry to DEMAND. This is a local abstraction theorem only.
-/
namespace RelativeRestriction
set_option autoImplicit false

inductive Accessor where
  | classId (value : Nat)
  | field (value : Nat)
  | element
  deriving DecidableEq, Repr

abbrev Path := List Accessor

def depth : Path → Nat
  | [] => 0
  | .classId _ :: rest => depth rest
  | .field _ :: rest => depth rest + 1
  | .element :: rest => depth rest + 1

/-- Retain uncounted anchors until the first blocked counted accessor. -/
def clip : Nat → Path → Path
  | _, [] => []
  | budget, .classId value :: rest => .classId value :: clip budget rest
  | 0, .field _ :: _ => []
  | budget + 1, .field value :: rest => .field value :: clip budget rest
  | 0, .element :: _ => []
  | budget + 1, .element :: rest => .element :: clip budget rest

inductive Layer where | normal | demand deriving DecidableEq, Repr
inductive Tail where | exact | star | may | must deriving DecidableEq, Repr

structure Pattern where
  base : Nat
  path : Path
  tail : Tail
  mark : Nat
  deriving DecidableEq, Repr

structure Scalar extends Pattern where
  layer : Layer
  protection : Bool := false
  deriving DecidableEq, Repr

/-- Only overflow changes a result. Its mark and protection are carried as-is. -/
def limit (budget : Nat) (raw : Scalar) : Scalar :=
  if depth raw.path ≤ budget then raw
  else {raw with path := clip budget raw.path, tail := .may, layer := .demand}

def pairBudget (global : Nat) (dp : Pattern) : Nat :=
  min global (depth dp.path + 1)

def possiblePath (tail : Tail) (anchor location : Path) : Prop :=
  match tail with
  | .exact => location = anchor
  | .star | .may | .must => anchor.IsPrefix location

def possible (value : Scalar) (base mark : Nat) (location : Path) : Prop :=
  base = value.base ∧ mark = value.mark ∧ possiblePath value.tail value.path location

theorem depth_append (left right : Path) : depth (left ++ right) = depth left + depth right := by
  induction left with
  | nil => simp only [depth,List.nil_append,Nat.zero_add]
  | cons accessor rest ih =>
    cases accessor <;> simp [depth, ih, Nat.add_comm, Nat.add_left_comm]

theorem clip_depth_le (budget : Nat) (path : Path) : depth (clip budget path) ≤ budget := by
  induction path generalizing budget with
  | nil => exact Nat.zero_le _
  | cons accessor rest ih =>
    cases accessor with
    | classId value => exact ih budget
    | field value =>
      cases budget with
      | zero => exact Nat.le_refl _
      | succ n => exact Nat.add_le_add_right (ih n) 1
    | element =>
      cases budget with
      | zero => exact Nat.le_refl _
      | succ n => exact Nat.add_le_add_right (ih n) 1

theorem clip_is_prefix (budget : Nat) (path : Path) : (clip budget path).IsPrefix path := by
  induction path generalizing budget with
  | nil => exact ⟨[],rfl⟩
  | cons accessor rest ih =>
    cases accessor with
    | classId value =>
      obtain ⟨suffix,same⟩ := ih budget
      exact ⟨suffix,by simpa only [clip,List.cons_append] using congrArg (List.cons (.classId value)) same⟩
    | field value =>
      cases budget with
      | zero => exact ⟨.field value :: rest,rfl⟩
      | succ n =>
        obtain ⟨suffix,same⟩ := ih n
        exact ⟨suffix,by simpa only [clip,List.cons_append] using congrArg (List.cons (.field value)) same⟩
    | element =>
      cases budget with
      | zero => exact ⟨.element :: rest,rfl⟩
      | succ n =>
        obtain ⟨suffix,same⟩ := ih n
        exact ⟨suffix,by simpa only [clip,List.cons_append] using congrArg (List.cons Accessor.element) same⟩

theorem clip_identity (budget : Nat) (path : Path) (within : depth path ≤ budget) :
    clip budget path = path := by
  induction path generalizing budget with
  | nil => rfl
  | cons accessor rest ih =>
    cases accessor with
    | classId value => exact congrArg (List.cons (.classId value)) (ih budget within)
    | field value =>
      cases budget with
      | zero => exact False.elim (Nat.not_succ_le_zero _ within)
      | succ n =>
        exact congrArg (List.cons (.field value)) (ih n (Nat.le_of_succ_le_succ within))
    | element =>
      cases budget with
      | zero => exact False.elim (Nat.not_succ_le_zero _ within)
      | succ n =>
        exact congrArg (List.cons Accessor.element) (ih n (Nat.le_of_succ_le_succ within))

theorem prefix_transitive {a b c : Path} (ab : a.IsPrefix b) (bc : b.IsPrefix c) :
    a.IsPrefix c := by
  obtain ⟨left,hl⟩ := ab
  obtain ⟨right,hr⟩ := bc
  refine ⟨left ++ right,?_⟩
  rw [← List.append_assoc,hl,hr]

theorem prefix_depth_le {a b : Path} (ab : a.IsPrefix b) : depth a ≤ depth b := by
  obtain ⟨suffix,same⟩ := ab
  rw [← same,depth_append]
  exact Nat.le_add_right _ _

theorem limit_within_identity (budget : Nat) (raw : Scalar) (within : depth raw.path ≤ budget) :
    limit budget raw = raw := by simp only [limit,within,↓reduceIte]

theorem limit_depth_bound (budget : Nat) (raw : Scalar) : depth (limit budget raw).path ≤ budget := by
  unfold limit
  split
  next within => exact within
  next => exact clip_depth_le budget raw.path

theorem limit_base_retained (budget : Nat) (raw : Scalar) : (limit budget raw).base = raw.base := by
  unfold limit; split <;> rfl

theorem limit_mark_retained (budget : Nat) (raw : Scalar) : (limit budget raw).mark = raw.mark := by
  unfold limit; split <;> rfl

theorem limit_protection_retained (budget : Nat) (raw : Scalar) :
    (limit budget raw).protection = raw.protection := by
  unfold limit; split <;> rfl

theorem limit_demand_stays_demand (budget : Nat) (raw : Scalar) (demand : raw.layer = .demand) :
    (limit budget raw).layer = .demand := by
  unfold limit; split
  · exact demand
  · rfl

theorem limit_overflow_is_demand (budget : Nat) (raw : Scalar) (overflow : ¬ depth raw.path ≤ budget) :
    (limit budget raw).layer = .demand := by simp only [limit,overflow,↓reduceIte]

theorem limit_normal_is_unchanged (budget : Nat) (raw : Scalar)
    (normal : (limit budget raw).layer = .normal) : limit budget raw = raw := by
  by_cases within : depth raw.path ≤ budget
  · exact limit_within_identity budget raw within
  · have demand := limit_overflow_is_demand budget raw within
    have impossible : Layer.demand = Layer.normal := demand.symm.trans normal
    cases impossible

theorem limit_possible_coverage (budget : Nat) (raw : Scalar) (base mark : Nat) (location : Path)
    (actual : possible raw base mark location) : possible (limit budget raw) base mark location := by
  unfold limit
  split
  · exact actual
  next overflow =>
    obtain ⟨sameBase,sameMark,atPath⟩ := actual
    refine ⟨sameBase,sameMark,?_⟩
    change (clip budget raw.path).IsPrefix location
    cases tail : raw.tail with
    | exact =>
      have same : location = raw.path := by simpa only [possiblePath,tail] using atPath
      rw [same]
      exact clip_is_prefix budget raw.path
    | star => exact prefix_transitive (clip_is_prefix budget raw.path) (by simpa only [possiblePath,tail] using atPath)
    | may => exact prefix_transitive (clip_is_prefix budget raw.path) (by simpa only [possiblePath,tail] using atPath)
    | must => exact prefix_transitive (clip_is_prefix budget raw.path) (by simpa only [possiblePath,tail] using atPath)

theorem pair_budget_le_global (global : Nat) (dp : Pattern) : pairBudget global dp ≤ global :=
  Nat.min_le_left _ _

theorem pair_budget_le_exit_step (global : Nat) (dp : Pattern) : pairBudget global dp ≤ depth dp.path + 1 :=
  Nat.min_le_right _ _

theorem pair_budget_positive (global : Nat) (dp : Pattern) (positive : 0 < global) :
    0 < pairBudget global dp :=
  Nat.le_min.mpr ⟨positive,Nat.succ_le_succ (Nat.zero_le _)⟩

theorem class_anchor_is_not_counted (name : Nat) (rest : Path) :
    depth (.classId name :: rest) = depth rest := rfl

theorem field_and_element_are_counted (field : Nat) (rest : Path) :
    depth (.field field :: rest) = depth rest + 1 ∧ depth (.element :: rest) = depth rest + 1 := ⟨rfl,rfl⟩

theorem budget_one_preserves_named_static_anchor (owner field extra : Nat) :
    clip 1 [.classId owner,.field field,.field extra] = [.classId owner,.field field] := rfl

theorem clip_retains_noncounted_anchor_before_blocked_field (owner field : Nat) :
    clip 0 [.classId owner,.field field] = [.classId owner] := rfl

theorem exact_class_marker_is_not_abstracted (budget base owner mark : Nat)
    (layer : Layer) (protection : Bool) :
    limit budget ⟨⟨base,[.classId owner],.exact,mark⟩,layer,protection⟩ =
      ⟨⟨base,[.classId owner],.exact,mark⟩,layer,protection⟩ := by
  apply limit_within_identity
  exact Nat.zero_le _

/-- Forgetting an extra constraint, such as a discarded field exclusion,
    can only widen possible locations. Uncut E retention is an adapter law. -/
theorem limit_covers_a_narrowed_location_set (budget : Nat) (raw : Scalar)
    (allowed : Path → Prop) (base mark : Nat) (location : Path)
    (actual : possible raw base mark location ∧ allowed location) :
    possible (limit budget raw) base mark location :=
  limit_possible_coverage budget raw base mark location actual.1

end RelativeRestriction
