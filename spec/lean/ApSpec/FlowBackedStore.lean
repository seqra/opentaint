/- Per-complete-key executable store. Histories are specification ghosts.
   The runtime retains residuals and local progress, not a subsumed archive. -/
import ApSpec.FlowBackedProtection

namespace ApSpec.FlowBackedStore
open ApSpec

structure Cell where
  flow : Bool := false
  marked : Bool := false
  blocked : Bool := false
deriving DecidableEq, Repr

inductive Event where
  | flow
  | marked (blocked : Bool)
deriving DecidableEq, Repr

def admit (s : Cell) : Event → Cell
  | .flow => { s with flow := true }
  | .marked p => { s with marked := true, blocked := s.blocked || p }

/-- `flow` means an accepted coverage certificate for this particular key,
    not merely the existence of some FLOW with the same base. -/
def residual (s : Cell) : Bool := s.marked && (!s.flow || s.blocked)
def wellFormed (s : Cell) : Prop := s.blocked = true → s.marked = true
def novel (s : Cell) (e : Event) : Bool := decide (admit s e ≠ s)
def rank (s : Cell) : Nat := s.flow.toNat + s.marked.toNat + s.blocked.toNat

theorem admission_wellFormed (s : Cell) (h : wellFormed s) (e : Event) :
    wellFormed (admit s e) := by
  cases e <;> simp_all [wellFormed, admit]

theorem admission_idempotent (s : Cell) (e : Event) : admit (admit s e) e = admit s e := by
  cases s with | mk f m p =>
    cases e with
    | flow => rfl
    | marked q => cases p <;> cases q <;> rfl

theorem admission_commutes (s : Cell) (e d : Event) :
    admit (admit s e) d = admit (admit s d) e := by
  cases s with | mk f m p =>
    cases e <;> cases d <;> simp [admit, Bool.or_comm, Bool.or_left_comm]

theorem covered_plain_removed (s : Cell) (h : s.flow = true) (p : s.blocked = false) :
    residual s = false := by simp [residual, h, p]

theorem protected_retained (s : Cell) (m : s.marked = true) (p : s.blocked = true) :
    residual s = true := by simp [residual, m, p]

theorem late_protection_restores (s : Cell) : residual (admit s (.marked true)) = true := by
  simp [residual, admit]

theorem covered_protection_is_work (s : Cell) (p : s.blocked = false) :
    novel s (.marked true) = true := by
  cases s with | mk f m p => cases p <;> simp_all [novel, admit]

theorem coverage_keeps_local_membership (s : Cell) : (admit s .flow).marked = s.marked := rfl

/-- Semantic transport and protected dependency observations are separate. -/
def oldTransport (s : Cell) (flowPair markedPair : Prop) : Prop :=
  (s.flow = true ∧ flowPair) ∨ (s.marked = true ∧ markedPair)
def newTransport (s : Cell) (flowPair markedPair : Prop) : Prop :=
  (s.flow = true ∧ flowPair) ∨ (residual s = true ∧ markedPair)

theorem normalized_transport_exact (s : Cell) (f t : Prop) (covers : t → f) :
    oldTransport s f t ↔ newTransport s f t := by
  cases s with | mk flow marked blocked =>
    cases flow <;> cases marked <;> cases blocked <;>
      simp_all [oldTransport, newTransport, residual]

theorem protected_obligation_exact (s : Cell) (h : wellFormed s) :
    (s.marked = true ∧ s.blocked = true) ↔
      (residual s = true ∧ s.blocked = true) := by
  cases s with | mk f m p => cases f <;> cases m <;> cases p <;>
    simp_all [wellFormed, residual]

theorem rank_bounded (s : Cell) : rank s ≤ 3 := by
  cases s with | mk f m p => cases f <;> cases m <;> cases p <;> decide

theorem novel_strict_growth (s : Cell) (e : Event) (h : novel s e = true) :
    rank s < rank (admit s e) := by
  cases s with | mk f m p =>
    cases e with
    | flow => cases f <;> cases m <;> cases p <;> simp_all [novel, admit, rank]
    | marked q => cases f <;> cases m <;> cases p <;> cases q <;>
        simp_all [novel, admit, rank]

/-- Reference exact same-mark mask, with a distinct scalar premise per member. -/
structure Geometry where
  inputBase : Base
  inputPath : List Acc
  inputKind : Kind
  outputBase : Base
  outputPath : List Acc
  outputKind : Kind
  demand : Bool
deriving DecidableEq, Repr

def scalar (g : Geometry) (t : Mark) : PFact × AFact :=
  (⟨g.inputBase, g.inputPath, g.inputKind, .conc t⟩,
   ⟨⟨g.outputBase, g.outputPath, g.outputKind, .conc t⟩, g.demand⟩)
def decode (g : Geometry) (marks : List Mark) : List (PFact × AFact) := marks.map (scalar g)

theorem decode_exact (g : Geometry) (marks : List Mark) (edge : PFact × AFact) :
    edge ∈ decode g marks ↔ ∃ t, t ∈ marks ∧ edge = scalar g t := by
  simp [decode, eq_comm]

theorem decode_diagonal (g : Geometry) (marks : List Mark) (edge : PFact × AFact)
    (h : edge ∈ decode g marks) : edge.1.mark = edge.2.fact.mark := by
  obtain ⟨t, _, rfl⟩ := (decode_exact g marks edge).mp h
  rfl

theorem decode_injective (g : Geometry) (t u : Mark) (h : scalar g t = scalar g u) : t = u := by
  have hm := congrArg (fun edge : PFact × AFact => edge.1.mark) h
  exact MarkA.conc.inj hm

/-- Count geometry operations only; mark-set storage and observers remain costs. -/
def scalarGeometryCost (marks : List Mark) : Nat := marks.length
def sharedGeometryCost (marks : List Mark) : Nat := if marks.isEmpty then 0 else 1

theorem geometry_cost_not_greater (marks : List Mark) :
    sharedGeometryCost marks ≤ scalarGeometryCost marks := by
  cases marks <;> simp [sharedGeometryCost, scalarGeometryCost]

theorem nonempty_geometry_cost (t : Mark) (ts : List Mark) :
    sharedGeometryCost (t :: ts) = 1 ∧ scalarGeometryCost (t :: ts) = ts.length + 1 := by
  simp [sharedGeometryCost, scalarGeometryCost]

#print axioms admission_wellFormed
#print axioms admission_idempotent
#print axioms admission_commutes
#print axioms covered_plain_removed
#print axioms protected_retained
#print axioms late_protection_restores
#print axioms covered_protection_is_work
#print axioms coverage_keeps_local_membership
#print axioms normalized_transport_exact
#print axioms protected_obligation_exact
#print axioms rank_bounded
#print axioms novel_strict_growth
#print axioms decode_exact
#print axioms decode_diagonal
#print axioms decode_injective
#print axioms geometry_cost_not_greater
#print axioms nonempty_geometry_cost
end ApSpec.FlowBackedStore
