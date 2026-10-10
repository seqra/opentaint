/-
  Method-key isolation for the proposed per-path conjunctive sink oracle.

  Inputs are already checked positive sink literals. A slot may retain many
  inputs. The full key includes the method key, sink alternative, and statement.
  This local model checks the join partition, not sink checking or confirmation.
-/
import Std

namespace ApSpec.CurrentSinkJoin

structure Input where
  method : Nat
  alternative : Nat
  statement : Nat
  right : Bool
  premise : Nat
deriving DecidableEq, Repr

/-- Complete list scan before any key filter. -/
def pairs (inputs : List Input) : List (Input × Input) :=
  inputs.flatMap fun a => inputs.map fun b => (a, b)

/-- The old oracle omits the method key from the sink-input key. -/
def unscopedJoin (inputs : List Input) : List (Input × Input) :=
  (pairs inputs).filter fun p =>
    !p.1.right && p.2.right && p.1.alternative == p.2.alternative &&
      p.1.statement == p.2.statement

/-- The current oracle includes the method key in the join key. -/
def scopedJoin (inputs : List Input) : List (Input × Input) :=
  (unscopedJoin inputs).filter fun p => p.1.method == p.2.method

theorem method_isolation (inputs : List Input) (p : Input × Input)
    (h : p ∈ scopedJoin inputs) : p.1.method = p.2.method := by
  exact beq_iff_eq.mp (List.mem_filter.mp h).2

/-- The method guard removes only combinations from different method keys. -/
theorem scoped_iff (inputs : List Input) (p : Input × Input) :
    p ∈ scopedJoin inputs ↔ p ∈ unscopedJoin inputs ∧ p.1.method = p.2.method := by
  simp [scopedJoin]

/-- A same-method combination admitted by the literal/site checks is retained. -/
theorem same_method_retained (inputs : List Input) (p : Input × Input)
    (h : p ∈ unscopedJoin inputs) (hm : p.1.method = p.2.method) :
    p ∈ scopedJoin inputs := (scoped_iff inputs p).mpr ⟨h, hm⟩

namespace Certificate

def leftA : Input := ⟨1, 7, 9, false, 11⟩
def rightB : Input := ⟨2, 7, 9, true, 22⟩
def rightA : Input := ⟨1, 7, 9, true, 33⟩

/-- Two contexts supply different slots; neither context satisfies the sink. -/
def differentContexts : List Input := [leftA, rightB]

theorem old_oracle_false_combination :
    unscopedJoin differentContexts = [(leftA, rightB)] := rfl

theorem corrected_oracle_no_combination : scopedJoin differentContexts = [] := rfl

/-- A valid combination in one context still has a computed witness. -/
def sameContext : List Input := [leftA, rightA]

theorem corrected_oracle_keeps_combination :
    scopedJoin sameContext = [(leftA, rightA)] := rfl

def check : Bool :=
  unscopedJoin differentContexts == [(leftA, rightB)] &&
  scopedJoin differentContexts == [] && scopedJoin sameContext == [(leftA, rightA)]

theorem checked : check = true := rfl

end Certificate
end ApSpec.CurrentSinkJoin
