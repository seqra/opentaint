import Init

/- Layered initial admission. All APs are constant-free data APs in this
   kernel. JVM static anchor shape/counting remain adapter obligations. -/
namespace ExactDemand
set_option autoImplicit false

inductive Layer where | normal | demand deriving DecidableEq, Repr

def join : Layer → Layer → Layer
  | .normal, .normal => .normal | _, _ => .demand

theorem join_normal_iff (a b : Layer) : join a b = .normal ↔ a = .normal ∧ b = .normal := by
  cases a <;> cases b <;> simp [join]

theorem join_demand_left (layer : Layer) : join .demand layer = .demand := rfl

theorem join_demand_right (layer : Layer) : join layer .demand = .demand := by
  cases layer <;> rfl

inductive Tail where | exact | star | may | must deriving DecidableEq, Repr
inductive Mark where
  | flow (excluded : List Nat)
  | concrete (value : Nat)
  deriving DecidableEq, Repr

structure Pattern where
  base : Nat
  path : List Nat
  tail : Tail
  mark : Mark
  excludedFields : List Nat := []
  deriving DecidableEq, Repr

/-- Layer is outside InitialKey and does not affect its equality/hash. -/
inductive InitialKey where
  | zero
  | data (pattern : Pattern)
  deriving DecidableEq, Repr

structure Seed where
  initial : InitialKey
  layer : Layer
  deriving DecidableEq, Repr

structure Actual where
  pattern : Pattern
  layer : Layer
  deriving DecidableEq, Repr

structure Demand where
  pattern : Pattern
  layer : Layer
  deriving DecidableEq, Repr

/-- Directed required-mark compatibility. FLOW does not invent a concrete mark. -/
def markSub : Mark → Mark → Bool
  | .flow required, .flow actual => required.all fun t => t ∈ actual
  | .flow excluded, .concrete actual => !(actual ∈ excluded)
  | .concrete required, .concrete actual => decide (required = actual)
  | .concrete _, .flow _ => false

def isPrefix : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, q :: qs => decide (p = q) && isPrefix ps qs

def tailAdmits (tail : Tail) (excluded : List Nat) (suffix : List Nat) : Bool :=
  match tail, suffix with
  | .exact, [] => true
  | .exact, _ :: _ => false
  | .may, _ => true
  | _, [] => true
  | _, field :: _ => !(field ∈ excluded)

/-- Canonical copy used only after demand validation. Concrete EXACT/E
    is rejected before this helper; abstract FLOW normalization is separate. -/
def normalizeDemand (pattern : Pattern) : Pattern := {pattern with excludedFields := []}

/-- Existing base/mark/budget guards, independent of the changed tail cell. -/
def commonGuards (limit : Nat) (demand actual : Pattern) : Bool :=
  decide (demand.base = actual.base) && markSub demand.mark actual.mark &&
    decide (demand.path.length ≤ limit) && decide (actual.path.length ≤ limit)

/-- An EXACT requested location is equal to, or below an admitted actual prefix.
An EXACT actual cannot supply a strictly deeper location. -/
def exactGeometry (demand actual : Pattern) : Bool :=
  isPrefix actual.path demand.path &&
    tailAdmits actual.tail actual.excludedFields (demand.path.drop actual.path.length)

/-- This model does not broaden any base, field, mark, or budget guard. -/
def exactGuards (limit : Nat) (demand actual : Pattern) : Bool :=
  commonGuards limit (normalizeDemand demand) actual && exactGeometry demand actual

/-- The key requested by an EXACT demand; initial identity contains no layer. -/
def exactPattern (demand : Pattern) : Pattern :=
  {normalizeDemand demand with tail := .exact}

def exactKey (demand : Pattern) : InitialKey := .data (exactPattern demand)

theorem exact_key_is_exact (demand : Pattern) : (exactPattern demand).tail = .exact := rfl

theorem exact_key_has_empty_exclusion (demand : Pattern) :
    (exactPattern demand).excludedFields = [] := rfl

theorem concrete_demand_does_not_match_flow (t : Nat) (excluded : List Nat) :
    markSub (.concrete t) (.flow excluded) = false := rfl

theorem different_concrete_marks_reject (wanted actual : Nat) (different : wanted ≠ actual) :
    markSub (.concrete wanted) (.concrete actual) = false := by
  simp only [markSub, decide_eq_false different]

end ExactDemand
