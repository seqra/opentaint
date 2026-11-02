import Geometry

/-!
Executable concrete-FULL, nonstatic, empty-E C2 adapter.

Only EXACT/MAY demand and actual tails are modeled. Canonical initials
can be EXACT, STAR or MAY. This copies the corresponding directed cells
of RestrictedInitialPolicy.emit/emitAdmission, including the first-new-
field rule and concrete MAY -> provisional exact DEMAND admission.

The finite certificate checks the core geometry projection, not the
forced ineligible fallback: all field paths of length <= global, binary
alphabet, global 1/2/3, both demand/actual tails and actual layers, with
the tested demand included plus zero or one additional scoped guide.
One base and one matching FULL mark suffice for this certificate; mark
rejection is stated separately. It is NOT a general arbitrary-trie C2
equivalence proof, and excludes STAR/MUST actuals, statics, E/mx and FLOW.

The explicit fallback counterexample proves that forcing MAY on an
ineligible exact ancestor can ADD a provisional DEMAND initial. Thus
the wrapper must not be advertised as admission-equivalent.
-/
namespace LoopFragments.Admission
open LoopFragments.Geometry
set_option autoImplicit false

inductive InitialTail where | exact | star | may deriving DecidableEq, Repr

structure Demand (bases marks fields : Nat) where
  base : Fin bases
  mark : Fin marks
  path : Path fields
  tail : Geometry.Tail
  deriving DecidableEq, Repr

structure Initial (bases marks fields : Nat) where
  base : Fin bases
  mark : Fin marks
  path : Path fields
  tail : InitialTail
  deriving DecidableEq, Repr

structure Emission (bases marks fields : Nat) where
  initial : Initial bases marks fields
  layer : Layer
  deriving DecidableEq, Repr

variable {bases marks fields : Nat}

/-- Geometry has only counted fields, so firstFieldEnd is prefix length + 1. -/
def emitKey (global : Nat) (d : Demand bases marks fields)
    (a : Fact bases marks fields) : Option (Initial bases marks fields) :=
  if d.base ≠ a.base ∨ d.mark ≠ a.mark ∨ global < d.path.length ∨ global < a.path.length then none
  else
    let result (path : Path fields) (tail : InitialTail) :=
      some (Initial.mk d.base d.mark path tail)
    if a.path = d.path then
      match d.tail, a.tail with
      | .may, .may => result d.path .may
      | _, _ => result d.path .exact
    else if d.path.IsPrefix a.path then
      match d.tail with
      | .exact => none
      | .may =>
          let fieldEnd := d.path.length + 1
          let tail := if a.tail = .exact ∧ fieldEnd = a.path.length then InitialTail.exact else .star
          result (a.path.take fieldEnd) tail
    else if a.path.IsPrefix d.path ∧ a.tail = .may then
      match d.tail with
      | .exact => result d.path .exact
      | .may => result d.path .may
    else none

def startingLayer (key : Initial bases marks fields) (actual : Fact bases marks fields) : Layer :=
  if actual.layer = .demand ∨ actual.tail = .may then .demand
  else match key.tail with
    | .exact => .normal
    | .star | .may => .demand

def emit (global : Nat) (d : Demand bases marks fields)
    (a : Fact bases marks fields) : Option (Emission bases marks fields) :=
  (emitKey global d a).map fun initial => ⟨initial, startingLayer initial a⟩

theorem wrong_mark_rejects (global : Nat) (d : Demand bases marks fields)
    (a : Fact bases marks fields) (wrong : d.mark ≠ a.mark) : emitKey global d a = none := by
  rw [emitKey, if_pos (Or.inr (Or.inl wrong))]

theorem demand_actual_never_starts_normal (key : Initial bases marks fields)
    (a : Fact bases marks fields) (demand : a.layer = .demand) : startingLayer key a = .demand := by
  simp only [startingLayer, demand, true_or, ↓reduceIte]

theorem may_actual_never_starts_normal (key : Initial bases marks fields)
    (a : Fact bases marks fields) (may : a.tail = .may) : startingLayer key a = .demand := by
  simp only [startingLayer, may, or_true, ↓reduceIte]

theorem normal_initial_requires_normal_exact_actual (key : Initial bases marks fields)
    (a : Fact bases marks fields) (normal : startingLayer key a = .normal) :
    a.layer = .normal ∧ a.tail = .exact ∧ key.tail = .exact := by
  cases layer : a.layer <;> cases tail : a.tail <;> cases kt : key.tail <;>
    simp [startingLayer, layer, tail, kt] at normal ⊢

/-- The optional extra guide is scoped by the same base, mark, status and direction. -/
def scopedGuides (d : Demand 1 1 2) (extra : Option (Path 2)) : List (Path 2) :=
  d.path :: extra.toList

def finiteExtras (global : Nat) : List (Option (Path 2)) :=
  none :: (pathsUpTo 2 global).map some

def sampleDemand (path : Path 2) (tail : Geometry.Tail) : Demand 1 1 2 := ⟨0, 0, path, tail⟩
def sampleActual (path : Path 2) (tail : Geometry.Tail) (layer : Layer) : Fact 1 1 2 :=
  ⟨0, 0, path, tail, layer, false⟩

def cell (global : Nat) (dp : Path 2) (dt : Geometry.Tail)
    (ap : Path 2) (actualTail : Geometry.Tail) (layer : Layer) (extra : Option (Path 2)) : Bool :=
  let d := sampleDemand dp dt
  let a := sampleActual ap actualTail layer
  decide (emit global d (project global (scopedGuides d extra) a) = emit global d a)

/-- Check one demanded path at a time. This keeps kernel reduction below
    the verifier's 768 MiB budget without deleting any finite case. -/
def pathCertificate (global : Nat) (dp : Path 2) : Bool :=
  [Geometry.Tail.exact, Geometry.Tail.may].all fun dt =>
  (pathsUpTo 2 global).all fun ap =>
  [Geometry.Tail.exact, Geometry.Tail.may].all fun actualTail =>
  [Layer.normal, Layer.demand].all fun layer =>
  (finiteExtras global).all fun extra => cell global dp dt ap actualTail layer extra

def certificate (global : Nat) : Bool :=
  (pathsUpTo 2 global).all (pathCertificate global)

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_1_path_0 : pathCertificate 1 [] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_1_path_1 : pathCertificate 1 [0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_1_path_2 : pathCertificate 1 [1] = true := by decide

theorem finite_certificate_global_one : certificate 1 = true := by
  change ([[], [0], [1]].all (pathCertificate 1)) = true
  simp only [List.all_cons, List.all_nil,
    certificate_1_path_0,
    certificate_1_path_1,
    certificate_1_path_2, Bool.true_and]

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_2_path_0 : pathCertificate 2 [] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_2_path_1 : pathCertificate 2 [0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_2_path_2 : pathCertificate 2 [0, 0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_2_path_3 : pathCertificate 2 [0, 1] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_2_path_4 : pathCertificate 2 [1] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_2_path_5 : pathCertificate 2 [1, 0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_2_path_6 : pathCertificate 2 [1, 1] = true := by decide

theorem finite_certificate_global_two : certificate 2 = true := by
  change ([[], [0], [0, 0], [0, 1], [1], [1, 0], [1, 1]].all (pathCertificate 2)) = true
  simp only [List.all_cons, List.all_nil,
    certificate_2_path_0,
    certificate_2_path_1,
    certificate_2_path_2,
    certificate_2_path_3,
    certificate_2_path_4,
    certificate_2_path_5,
    certificate_2_path_6, Bool.true_and]

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_0 : pathCertificate 3 [] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_1 : pathCertificate 3 [0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_2 : pathCertificate 3 [0, 0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_3 : pathCertificate 3 [0, 0, 0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_4 : pathCertificate 3 [0, 0, 1] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_5 : pathCertificate 3 [0, 1] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_6 : pathCertificate 3 [0, 1, 0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_7 : pathCertificate 3 [0, 1, 1] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_8 : pathCertificate 3 [1] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_9 : pathCertificate 3 [1, 0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_10 : pathCertificate 3 [1, 0, 0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_11 : pathCertificate 3 [1, 0, 1] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_12 : pathCertificate 3 [1, 1] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_13 : pathCertificate 3 [1, 1, 0] = true := by decide

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 0 in
theorem certificate_3_path_14 : pathCertificate 3 [1, 1, 1] = true := by decide

theorem finite_certificate_global_three : certificate 3 = true := by
  change ([[], [0], [0, 0], [0, 0, 0], [0, 0, 1], [0, 1], [0, 1, 0], [0, 1, 1], [1], [1, 0], [1, 0, 0], [1, 0, 1], [1, 1], [1, 1, 0], [1, 1, 1]].all (pathCertificate 3)) = true
  simp only [List.all_cons, List.all_nil,
    certificate_3_path_0,
    certificate_3_path_1,
    certificate_3_path_2,
    certificate_3_path_3,
    certificate_3_path_4,
    certificate_3_path_5,
    certificate_3_path_6,
    certificate_3_path_7,
    certificate_3_path_8,
    certificate_3_path_9,
    certificate_3_path_10,
    certificate_3_path_11,
    certificate_3_path_12,
    certificate_3_path_13,
    certificate_3_path_14, Bool.true_and]

theorem certificate_cell (global : Nat) (checked : certificate global = true)
    (dp ap : Path 2) (dt actualTail : Geometry.Tail) (layer : Layer) (extra : Option (Path 2))
    (dpMember : dp ∈ pathsUpTo 2 global) (apMember : ap ∈ pathsUpTo 2 global)
    (extraMember : extra ∈ finiteExtras global) : cell global dp dt ap actualTail layer extra = true := by
  have one := List.all_eq_true.mp checked dp dpMember
  have dtMember : dt ∈ [Geometry.Tail.exact, Geometry.Tail.may] := by cases dt <;> simp
  have two := List.all_eq_true.mp one dt dtMember
  have three := List.all_eq_true.mp two ap apMember
  have atMember : actualTail ∈ [Geometry.Tail.exact, Geometry.Tail.may] := by cases actualTail <;> simp
  have four := List.all_eq_true.mp three actualTail atMember
  have layerMember : layer ∈ [Layer.normal, Layer.demand] := by cases layer <;> simp
  have five := List.all_eq_true.mp four layer layerMember
  exact List.all_eq_true.mp five extra extraMember

theorem checked_core_emission_preservation (global : Nat) (checked : certificate global = true)
    (dp ap : Path 2) (dt actualTail : Geometry.Tail) (layer : Layer) (extra : Option (Path 2))
    (dpWithin : dp.length ≤ global) (apWithin : ap.length ≤ global)
    (extraMember : extra ∈ finiteExtras global) :
    emit global (sampleDemand dp dt)
      (project global (scopedGuides (sampleDemand dp dt) extra) (sampleActual ap actualTail layer)) =
    emit global (sampleDemand dp dt) (sampleActual ap actualTail layer) := by
  have checkedCell := certificate_cell global checked dp ap dt actualTail layer extra
    (pathsUpTo_complete global dp dpWithin) (pathsUpTo_complete global ap apWithin) extraMember
  exact of_decide_eq_true checkedCell

/-- Current C2 consumers only. This is not a decision about saved NORMAL replay. -/
def c2Eligible (global : Nat) : List (Demand bases marks fields) → Fact bases marks fields → Bool
  | [], _ => false
  | d :: rest, actual => (emit global d actual).isSome || c2Eligible global rest actual

theorem all_current_admissions_empty_is_ineligible (global : Nat)
    (consumers : List (Demand bases marks fields)) (actual : Fact bases marks fields)
    (empty : ∀ d ∈ consumers, emit global d actual = none) : c2Eligible global consumers actual = false := by
  induction consumers with
  | nil => rfl
  | cons d rest ih =>
      have head := empty d List.mem_cons_self
      have later := ih (fun other member => empty other (List.mem_cons_of_mem _ member))
      simp only [c2Eligible, head, Option.isSome_none, Bool.false_or, later]

theorem no_current_consumer_gate_drops (global : Nat)
    (consumers : List (Demand bases marks fields)) (guides : List (Path fields))
    (actual : Fact bases marks fields) (empty : ∀ d ∈ consumers, emit global d actual = none) :
    selectProject (c2Eligible global consumers actual) global guides actual = none := by
  rw [all_current_admissions_empty_is_ineligible global consumers actual empty]
  rfl

def ancestorDemand : Demand 1 1 2 := ⟨0, 0, [0, 1], .may⟩
def exactAncestor : Fact 1 1 2 := ⟨0, 0, [0], .exact, .normal, false⟩

theorem core_keeps_rejected_exact_ancestor :
    emit 3 ancestorDemand exactAncestor = none ∧
    project 3 [ancestorDemand.path] exactAncestor = exactAncestor := by decide

theorem forced_fallback_can_add_a_provisional_initial :
    emit 3 ancestorDemand (rejectedForcedProject false 3 [ancestorDemand.path] exactAncestor) =
      some ⟨⟨0, 0, [0, 1], .may⟩, .demand⟩ := by decide

theorem forced_fallback_is_not_c2_equivalent :
    emit 3 ancestorDemand (rejectedForcedProject false 3 [ancestorDemand.path] exactAncestor) ≠
      emit 3 ancestorDemand exactAncestor := by decide

theorem concrete_may_supplies_exact_on_demand_only :
    emit 3 ⟨(0 : Fin 1), (0 : Fin 1), [0, 1], .exact⟩
      (⟨0, 0, [0], .may, .demand, false⟩ : Fact 1 1 2) =
      some ⟨⟨0, 0, [0, 1], .exact⟩, .demand⟩ := by decide

end LoopFragments.Admission
