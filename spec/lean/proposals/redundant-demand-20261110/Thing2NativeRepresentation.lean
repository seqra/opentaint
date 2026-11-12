import «proposals».«redundant-demand-20261110».Thing2RootDebtCandidate

/- Representation and C2 bridges. NOT a retirement theorem. Native records,
   scope/ports and full mark keys stay in the binding certificate. -/
namespace Thing2NativeRepresentation
open Thing2RootDebtCandidate

def flowStarts (xs : List Initial) : List Fact :=
  (xs.filter (fun i => i.mark == .flow)).map Initial.fact

theorem flow_append (xs ys : List Initial) :
    flowStarts (xs ++ ys) = flowStarts xs ++ flowStarts ys := by
  simp [flowStarts]

theorem exact_t_start_has_no_flow (a : Offer) : flowStarts (c2Exact a) = [] := by
  cases a with | mk f kept =>
    cases f with | mk path tail layer excluded flag =>
      cases kept <;> cases path <;> simp [flowStarts, c2Exact]

theorem c2_flow_family_unchanged (a : Offer) (common : List Initial) :
    flowStarts (c2Any a ++ common ++ c2Exact a) = flowStarts (c2Any a ++ common) := by
  simp [flow_append, exact_t_start_has_no_flow]

theorem coarse_root_flow_companion (a : Offer) (coarse : CoarseRoot a) :
    flowStarts (c2Any a) = [⟨[], .star, .normal, [], false⟩] := by
  cases a with | mk f kept =>
    cases f with | mk path tail layer excluded flag =>
      rcases coarse with ⟨rfl, rfl, tails, rfl⟩
      rcases tails with rfl | rfl <;> simp [c2Any, flowStarts]

/- K6 and the actual unary source scope make color preservation executable.
   No selected-T input can create a FLOW or another full mark. FLOW cannot
   satisfy a restricted CM. This table is a scope adapter, not the generic
   language's source semantics. It excludes unconditional GEN and cross-mark
   assignments, which this captured scope does not have. -/
inductive Color where
  | flow
  | taint (fullMark : Nat)
  | zero
  deriving DecidableEq, Repr
inductive ColorOp where
  | copy
  | filter (kept : Bool)
  | clean (survives : Bool)
  | sameMarkSource (required : Nat) (permitted : Bool)
  deriving DecidableEq, Repr

def colorStep : ColorOp → Color → List Color
  | .copy, c => [c]
  | .filter keep, c | .clean keep, c => if keep then [c] else []
  | .sameMarkSource required allowed, .taint m =>
      if m == required && allowed then [.taint m] else []
  | .sameMarkSource _ _, _ => []

def colorRun : List ColorOp → Color → List Color
  | [], c => [c]
  | op :: more, c => (colorStep op c).flatMap (colorRun more)

theorem color_step_preserves (op : ColorOp) (c o : Color) (h : o ∈ colorStep op c) : o = c := by
  cases op <;> cases c <;> simp_all [colorStep]
  all_goals split at h <;> simp_all

theorem color_run_preserves (ops : List ColorOp) (c o : Color) (h : o ∈ colorRun ops c) : o = c := by
  induction ops generalizing c o with
  | nil => simpa [colorRun] using h
  | cons op more ih =>
    simp only [colorRun, List.mem_flatMap] at h
    rcases h with ⟨mid, hm, ho⟩
    exact (ih mid o ho).trans (color_step_preserves op c mid hm)

theorem taint_path_cannot_create_flow (ops : List ColorOp) (t : Nat) :
    Color.flow ∉ colorRun ops (.taint t) := by
  intro h
  have impossible := color_run_preserves ops (.taint t) .flow h
  contradiction

theorem flow_does_not_satisfy_source (m : Nat) (allowed : Bool) :
    colorStep (.sameMarkSource m allowed) .flow = [] := rfl

/- Scalar coordinates are literal. The packet header's anyTail/E applies
   ONLY to any memberships. Exact memberships have EXACT/Empty E, even when
   an exact-only packet has a MUST header. Protection is per coordinate. -/
structure ScopeHeader where
  owner : Nat
  entryPort : Nat
  exitPort : Nat
  base : Nat
  layer : Layer
  deriving DecidableEq, Repr
structure PacketHeader extends ScopeHeader where
  anyTail : Tail
  excluded : List Nat
  deriving DecidableEq, Repr
structure Leaf where
  path : Path
  exact : List Nat
  any : List Nat
  protectedExact : List Nat
  protectedAny : List Nat
  deriving DecidableEq, Repr
structure Scalar where
  header : ScopeHeader
  path : Path
  tail : Tail
  excluded : List Nat
  fullMark : Nat
  flag : Bool
  deriving DecidableEq, Repr

def exactScalar (h : PacketHeader) (l : Leaf) (m : Nat) : Scalar :=
  ⟨h.toScopeHeader, l.path, .exact, [], m, l.protectedExact.contains m⟩
def anyScalar (h : PacketHeader) (l : Leaf) (m : Nat) : Scalar :=
  ⟨h.toScopeHeader, l.path, h.anyTail, h.excluded, m, l.protectedAny.contains m⟩
def unpackLeaf (h : PacketHeader) (l : Leaf) : List Scalar :=
  l.exact.map (exactScalar h l) ++ l.any.map (anyScalar h l)
def unpack (h : PacketHeader) (leaves : List Leaf) : List Scalar :=
  leaves.flatMap (unpackLeaf h)

def classRows (flag : Bool) (rows : List Scalar) : List Scalar :=
  rows.filter (fun row => row.flag == flag)
def splitClasses (rows : List Scalar) : List Scalar := classRows false rows ++ classRows true rows

def SetEq {α : Type} (xs ys : List α) : Prop := ∀ x, x ∈ xs ↔ x ∈ ys

theorem exact_membership_ignores_any_header (h : PacketHeader) (l : Leaf) (m : Nat) :
    (exactScalar h l m).tail = .exact ∧ (exactScalar h l m).excluded = [] := by
  exact ⟨rfl, rfl⟩

theorem exact_scalar_independent_of_packet_header (h : PacketHeader) (l : Leaf)
    (m : Nat) (tail : Tail) (e : List Nat) :
    exactScalar { h with anyTail := tail, excluded := e } l m = exactScalar h l m := rfl

theorem exact_only_packet_no_semantic_must (h : PacketHeader) (l : Leaf)
    (emptyAny : l.any = []) : ∀ row ∈ unpackLeaf h l, row.tail = .exact := by
  intro row member
  simp only [unpackLeaf, emptyAny, List.map_nil, List.append_nil, List.mem_map] at member
  rcases member with ⟨mark, _, rfl⟩
  rfl

theorem split_classes_preserves (rows : List Scalar) : SetEq (splitClasses rows) rows := by
  intro row
  cases flag : row.flag <;> simp [splitClasses, classRows, flag]

theorem class_cannot_change (rows : List Scalar) (flag : Bool) (row : Scalar)
    (member : row ∈ classRows flag rows) : row.flag = flag := by
  simpa [classRows] using (List.mem_filter.mp member).2

theorem split_never_invents (h : PacketHeader) (leaves : List Leaf) (row : Scalar)
    (member : row ∈ splitClasses (unpack h leaves)) : row ∈ unpack h leaves :=
  (split_classes_preserves _ row).mp member

theorem plain_and_protected_are_distinct (h : ScopeHeader) (p : Path)
    (tail : Tail) (e : List Nat) (mark : Nat) :
    (Scalar.mk h p tail e mark false) ≠ (Scalar.mk h p tail e mark true) := by
  intro equal
  have := congrArg Scalar.flag equal
  contradiction

/- A handoff expands final packet leaves, then normalizes each scalar. The
   function is left parametric here, so the exact native guidancePattern and
   physical port flip can be supplied by the paired-row proof without changing
   the packet theorem. It is NOT allowed to use allocation ids as coordinates. -/
def project {α : Type} (normalize : Scalar → α) (h : PacketHeader)
    (leaves : List Leaf) : List α := (unpack h leaves).map normalize

theorem projection_has_exact_scalar_witness {α : Type} (normalize : Scalar → α)
    (h : PacketHeader) (leaves : List Leaf) (row : α) :
    row ∈ project normalize h leaves ↔
      ∃ scalar ∈ unpack h leaves, normalize scalar = row := by
  simp [project]

theorem projection_ignores_split_order {α : Type} (normalize : Scalar → α)
    (rows : List Scalar) :
    SetEq ((splitClasses rows).map normalize) (rows.map normalize) := by
  intro row
  simp only [List.mem_map]
  constructor
  · rintro ⟨s, hs, hrow⟩
    exact ⟨s, (split_classes_preserves _ s).mp hs, hrow⟩
  · rintro ⟨s, hs, hrow⟩
    exact ⟨s, (split_classes_preserves _ s).mpr hs, hrow⟩

theorem projection_common_union {α : Type} (normalize : Scalar → α)
    (selected common : List Scalar) :
    (selected ++ common).map normalize = selected.map normalize ++ common.map normalize := by
  simp

/- Per-mark set algebra is pointwise. An added selected-T coordinate cannot
   change another mark through union, intersection, subtraction or a MUST-hole
   intersection. Concrete packet/header grouping can change; these exact
   scalar memberships remain the authority. -/
abbrev Marks := Nat → Bool
def unionMarks (a b : Marks) : Marks := fun m => a m || b m
def intersectMarks (a b : Marks) : Marks := fun m => a m && b m
def minusMarks (a b : Marks) : Marks := fun m => a m && !b m

theorem mark_algebra_local (a a' b b' : Marks) (m : Nat)
    (left : a m = a' m) (right : b m = b' m) :
    unionMarks a b m = unionMarks a' b' m ∧
    intersectMarks a b m = intersectMarks a' b' m ∧
    minusMarks a b m = minusMarks a' b' m := by
  simp [unionMarks, intersectMarks, minusMarks, left, right]

end Thing2NativeRepresentation

#print axioms Thing2NativeRepresentation.flow_append
#print axioms Thing2NativeRepresentation.exact_t_start_has_no_flow
#print axioms Thing2NativeRepresentation.c2_flow_family_unchanged
#print axioms Thing2NativeRepresentation.coarse_root_flow_companion
#print axioms Thing2NativeRepresentation.color_step_preserves
#print axioms Thing2NativeRepresentation.color_run_preserves
#print axioms Thing2NativeRepresentation.taint_path_cannot_create_flow
#print axioms Thing2NativeRepresentation.flow_does_not_satisfy_source
#print axioms Thing2NativeRepresentation.exact_membership_ignores_any_header
#print axioms Thing2NativeRepresentation.exact_only_packet_no_semantic_must
#print axioms Thing2NativeRepresentation.split_classes_preserves
#print axioms Thing2NativeRepresentation.class_cannot_change
#print axioms Thing2NativeRepresentation.split_never_invents
#print axioms Thing2NativeRepresentation.plain_and_protected_are_distinct
#print axioms Thing2NativeRepresentation.projection_has_exact_scalar_witness
#print axioms Thing2NativeRepresentation.projection_ignores_split_order
#print axioms Thing2NativeRepresentation.projection_common_union
#print axioms Thing2NativeRepresentation.mark_algebra_local

#print axioms Thing2NativeRepresentation.exact_scalar_independent_of_packet_header
