import Std

namespace FlowAntichains.Matching

inductive Direction where | forward | backward
  deriving DecidableEq, BEq, Repr
inductive Role where | current | savedDirect | opposite
  deriving DecidableEq, BEq, Repr
inductive Tail where | exact | star | may | must
  deriving DecidableEq, BEq, Repr
inductive Layer where | normal | demand
  deriving DecidableEq, BEq, Repr

/-- The full native leaf payload is retained. Its opaque IDs stand for immutable native
    mark/exclusion/protection values, not a first-path or first-mark abstraction. -/
structure Leaf where
  base : Nat
  path : List Nat
  tail : Tail
  layer : Layer
  fullMarks : List Nat
  excludedFields : List Nat
  excludedMarks : List Nat
  protection : List Nat
  payload : Nat
  deriving DecidableEq, BEq, Repr

structure Query where
  base : Nat
  path : List Nat
  tail : Tail
  completePremise : List Nat
  owner : Nat
  entryPort : Int
  exitPort : Int
  deriving DecidableEq, BEq, Repr

/-- Native FULL mark, E/mx, tail and domain checks are supplied in this finite envelope.
    This model proves the policy delta, not those unchanged native predicates. -/
structure Candidate where
  leaf : Leaf
  query : Query
  nativeEligible : Bool
  deriving DecidableEq, BEq, Repr

def pathPrefix : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a = b) && pathPrefix as bs

def strictAncestor (a b : List Nat) : Bool := pathPrefix a b && decide (a.length < b.length)

def sameBase (c : Candidate) : Bool := decide (c.leaf.base = c.query.base)

def selectedRole (producer reader : Direction) : Role :=
  if producer = reader then .savedDirect else .opposite

/-- ALL incoming STAR leaves are in scope, independent of layer, concrete/FLOW mark,
    run number and query tail. Only a strict ancestor contribution can be removed. -/
def blocked (role : Role) (c : Candidate) : Bool :=
  decide (role ≠ .opposite) && decide (c.leaf.tail = .star) &&
    sameBase c && strictAncestor c.leaf.path c.query.path

def nativeKeep (c : Candidate) : Bool := c.nativeEligible && sameBase c

def keep (role : Role) (c : Candidate) : Bool := nativeKeep c && !blocked role c

def nativeSelect (rows : List Candidate) : List Candidate := rows.filter nativeKeep

def select (role : Role) (rows : List Candidate) : List Candidate := rows.filter (keep role)

/-- Explicit role and exact envelope are invocation inputs, not persisted AP metadata. -/
def selectAtRun (_run : Nat) (role : Role) (rows : List Candidate) : List Candidate := select role rows

theorem pathPrefix_refl (a : List Nat) : pathPrefix a a = true := by
  induction a with
  | nil => rfl
  | cons a as ih => simp [pathPrefix, ih]

theorem strict_irrefl (a : List Nat) : strictAncestor a a = false := by
  simp [strictAncestor]

theorem empty_strict_nonempty (x : Nat) (xs : List Nat) :
    strictAncestor [] (x :: xs) = true := by simp [strictAncestor, pathPrefix]

theorem role_same (d : Direction) : selectedRole d d = .savedDirect := by
  cases d <;> rfl

theorem role_forward_backward : selectedRole .forward .backward = .opposite := rfl

theorem role_backward_forward : selectedRole .backward .forward = .opposite := rfl

theorem opposite_never_blocks (c : Candidate) : blocked .opposite c = false := by
  simp [blocked]

theorem opposite_keep_native (c : Candidate) : keep .opposite c = nativeKeep c := by
  simp [keep, opposite_never_blocks]

theorem opposite_exact_list (rows : List Candidate) : select .opposite rows = nativeSelect rows := by
  change rows.filter (keep .opposite) = rows.filter nativeKeep
  congr 1
  funext c
  exact opposite_keep_native c

theorem current_direct_same (rows : List Candidate) : select .current rows = select .savedDirect rows := by
  rfl

theorem run_independent (r s : Nat) (role : Role) (rows : List Candidate) :
    selectAtRun r role rows = selectAtRun s role rows := rfl

theorem preserve_nonstar (role : Role) (c : Candidate) (h : c.leaf.tail ≠ .star) :
    keep role c = nativeKeep c := by
  simp [keep, blocked, h]

theorem preserve_may (role : Role) (c : Candidate) (h : c.leaf.tail = .may) :
    keep role c = nativeKeep c := by simp [keep, blocked, h]

theorem preserve_must (role : Role) (c : Candidate) (h : c.leaf.tail = .must) :
    keep role c = nativeKeep c := by simp [keep, blocked, h]

theorem preserve_exact (role : Role) (c : Candidate) (h : c.leaf.tail = .exact) :
    keep role c = nativeKeep c := by simp [keep, blocked, h]

theorem preserve_at (role : Role) (c : Candidate) (h : c.leaf.path = c.query.path) :
    keep role c = nativeKeep c := by simp [keep, blocked, h, strict_irrefl]

theorem preserve_not_strict (role : Role) (c : Candidate)
    (h : strictAncestor c.leaf.path c.query.path = false) :
    keep role c = nativeKeep c := by simp [keep, blocked, h]

theorem only_native (role : Role) (c : Candidate) (h : keep role c = true) :
    nativeKeep c = true := by
  cases hn : nativeKeep c <;> simp_all [keep]

theorem exact_delta (role : Role) (c : Candidate) :
    keep role c = true ↔ nativeKeep c = true ∧ blocked role c = false := by
  simp [keep, Bool.and_eq_true]

theorem reject_blocked (role : Role) (c : Candidate) (h : blocked role c = true) :
    keep role c = false := by simp [keep, h]

theorem selected_member (role : Role) (rows : List Candidate) (c : Candidate) :
    c ∈ select role rows ↔ c ∈ rows ∧ keep role c = true := by
  simp [select]

theorem selected_is_native (role : Role) (rows : List Candidate) (c : Candidate)
    (h : c ∈ select role rows) : c ∈ nativeSelect rows := by
  obtain ⟨hr, hk⟩ := (selected_member role rows c).mp h
  exact List.mem_filter.mpr ⟨hr, only_native role c hk⟩

theorem selected_payload_exact (role : Role) (rows : List Candidate) (c : Candidate)
    (h : c ∈ select role rows) : c ∈ rows := (selected_member role rows c).mp h |>.1

theorem select_stable_sublist (role : Role) (rows : List Candidate) :
    (select role rows).Sublist rows := List.filter_sublist

theorem select_idempotent (role : Role) (rows : List Candidate) :
    select role (select role rows) = select role rows := by
  simp [select]

/-- The complete ND join is the executable ordered product of surviving arm choices.
    No unary observation is substituted for an executable complete binding. -/
def product : List (List Candidate) → List (List Candidate)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (product rest).map fun ys => x :: ys

def bindings (role : Role) (arms : List (List Candidate)) : List (List Candidate) :=
  product (arms.map (select role))

def nativeBindings (arms : List (List Candidate)) : List (List Candidate) :=
  product (arms.map nativeSelect)

theorem product_nil : product [] = [[]] := rfl

theorem empty_arm_no_binding (rest : List (List Candidate)) : product ([] :: rest) = [] := rfl

theorem product_length (arms : List (List Candidate)) (xs : List Candidate)
    (h : xs ∈ product arms) : xs.length = arms.length := by
  induction arms generalizing xs with
  | nil => simp_all [product]
  | cons arm rest ih =>
    simp only [product, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, _, ys, hy, rfl⟩ := h
    simp [ih ys hy]

theorem complete_binding_length (role : Role) (arms : List (List Candidate)) (xs : List Candidate)
    (h : xs ∈ bindings role arms) : xs.length = arms.length := by
  simpa [bindings] using product_length (arms.map (select role)) xs h

theorem opposite_bindings_exact (arms : List (List Candidate)) :
    bindings .opposite arms = nativeBindings arms := by
  unfold bindings nativeBindings
  congr 1
  induction arms with
  | nil => rfl
  | cons arm rest ih => simp only [List.map_cons, opposite_exact_list, ih]

theorem preserve_empty_query (role : Role) (c : Candidate) (h : c.query.path = []) :
    keep role c = nativeKeep c := by
  apply preserve_not_strict
  simp [strictAncestor, h]

theorem run1_ordinary_vacuous (role : Role) (c : Candidate) (h : c.query.path = []) :
    keep role c = nativeKeep c := preserve_empty_query role c h

theorem preserve_not_above_depth (role : Role) (c : Candidate)
    (h : c.query.path.length ≤ c.leaf.path.length) : keep role c = nativeKeep c := by
  apply preserve_not_strict
  simp [strictAncestor, Nat.not_lt_of_ge h]

/-- Witness-bearing ordered sublist avoids any finite-choice or set-order premise. -/
theorem product_native_inclusion (arms : List (List Candidate)) (role : Role)
    (xs : List Candidate) (h : xs ∈ bindings role arms) : xs ∈ nativeBindings arms := by
  induction arms generalizing xs with
  | nil => simpa [bindings, nativeBindings, product] using h
  | cons arm rest ih =>
    simp only [bindings, List.map_cons, product, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, hx, ys, hy, rfl⟩ := h
    have hxn : x ∈ nativeSelect arm := selected_is_native role arm x hx
    have hyn : ys ∈ product (rest.map nativeSelect) := ih ys hy
    simp only [nativeBindings, List.map_cons, product, List.mem_flatMap, List.mem_map]
    exact ⟨x, hxn, ys, hyn, rfl⟩

theorem binding_empty_first_arm (role : Role) (rest : List (List Candidate)) :
    bindings role ([] :: rest) = [] := rfl

theorem per_arm_uses_same_role (role : Role) (arm : List Candidate)
    (rest : List (List Candidate)) :
    bindings role (arm :: rest) = (select role arm).flatMap
      (fun x => (bindings role rest).map (fun ys => x :: ys)) := rfl

/-- A successful complete binding contains its entire ordered chosen input, with all
    fields and annotations; this policy does not construct replacement premises. -/
theorem no_replacement_candidate (role : Role) (rows : List Candidate) :
    ∀ c ∈ select role rows, c ∈ rows := by
  intro c hc
  exact selected_payload_exact role rows c hc

def starExample (inputLayer : Layer) : Candidate := {
  leaf := {
    base := 7
    path := []
    tail := .star
    layer := inputLayer
    fullMarks := [3, 11]
    excludedFields := []
    excludedMarks := [19]
    protection := [3]
    payload := 42
  }
  query := {
    base := 7
    path := [5, 9]
    tail := .exact
    completePremise := [17, 23]
    owner := 6
    entryPort := 80
    exitPort := -2
  }
  nativeEligible := true
}

theorem concrete_full_profile_star_current_drops :
    select .current [starExample .demand] = [] := by decide

theorem same_example_opposite_survives :
    select .opposite [starExample .demand] = [starExample .demand] := by decide

theorem run1_current_star_changes :
    selectAtRun 1 .current [starExample .normal] = [] ∧
      nativeSelect [starExample .normal] = [starExample .normal] := by decide

theorem no_layer_veto (layer : Layer) : keep .current (starExample layer) = false := by
  cases layer <;> rfl

end FlowAntichains.Matching
