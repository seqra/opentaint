/-
  F74 local vectors for a named field action on a normal must-taint fact.
  Apply the actual read / temporary cleaner / strong write operations, with L=3.
  This tests the unchanged X AP operations, not an F72 X iteration theorem.
-/
import ApSpec.CleanerLowering
import ApSpec.AnyTaintExDefs

namespace ApSpec.FieldCleanerX
open ApSpec ApSpec.CleanerLowering ApSpec.AnyTaintEx

def input : XFact := ⟨⟨⟨4, [], .any, .conc 1⟩, false⟩, Excl.empty⟩
def outside : XFact := ⟨input.af, .set [5, 5]⟩
def partialField : XFact := ⟨⟨⟨4, [5], .any, .conc 1⟩, true⟩, Excl.empty⟩
def fieldValue : XFact := ⟨⟨⟨4, [5], .exact, .conc 1⟩, false⟩, Excl.empty⟩

/-- The temporary is projected away only after the ordinary write. -/
def run (reach : CleanReach) : List XFact :=
  (transferX (fun _ => false) (fun _ => true) 3 (readStmt 4 6 5) input).facts.flatMap fun a =>
    (cleanResX (tempCleanerWith 6 reach (some 1)) a).facts.flatMap fun b =>
      ((transferX (fun _ => false) (fun _ => true) 3 (writeStmt 4 6 5) b).facts).filter
        (fun x => !Nat.beq x.af.fact.base 6)

theorem exact_vector : run .exact = [outside, partialField] := by decide
theorem below_vector : run .below = [outside, fieldValue] := by decide
theorem atAndBelow_vector : run .atAndBelow = [outside] := by decide

/-- A computed normal fact outside the cleaned field, for every reach. -/
def outsideWitness (reach : CleanReach) :
    {f : XFact // f ∈ run reach ∧ f.af.demand = false ∧
      f.af.fact.mark = .conc 1 ∧ f.ex.admits [4] = true} :=
  ⟨outside, by cases reach <;> decide, rfl, rfl, by decide⟩

#print axioms exact_vector
#print axioms below_vector
#print axioms atAndBelow_vector
#print axioms outsideWitness
end ApSpec.FieldCleanerX
