import AuditGeometry
import UniformCoverage
namespace AuditNormalization
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

structure Move where
  read : Path
  write : Path

def move (edge : Move) (input : Path) : Option Path :=
  (dropHead edge.read input).map (fun rest => edge.write++rest)

def run : List Move → Path → Option Path
  | [],input => some input
  | first::rest,input => (move first input).bind (run rest)

theorem one_known_prefix_move_transports_the_same_symbolic_suffix
    (edge : Move) (input output suffix : Path) (hit : move edge input=some output) :
    move edge (input++suffix)=some (output++suffix) := by
  unfold move at hit ⊢
  cases consumed : dropHead edge.read input with
  | none => simp [consumed] at hit
  | some rest =>
      simp only [consumed,Option.map_some,Option.some.injEq] at hit
      have more := NormalUniformNE.suffix_prefix_composition edge.read input rest consumed suffix
      simp [more,←hit,List.append_assoc]

theorem every_finite_NORMAL_prefix_path_preserves_correlation
    (edges : List Move) (input output suffix : Path) (hit : run edges input=some output) :
    run edges (input++suffix)=some (output++suffix) := by
  induction edges generalizing input output with
  | nil => cases hit; rfl
  | cons first rest ih =>
      cases firstStep : move first input with
      | none => simp [run,firstStep] at hit
      | some middle =>
          have tail : run rest middle=some output := by simpa [run,firstStep] using hit
          have firstMore := one_known_prefix_move_transports_the_same_symbolic_suffix
            first input middle suffix firstStep
          simp only [run,firstMore,Option.bind_some]
          exact ih middle output tail

-- A stored FLOW STAR relation additionally carries its genuine field
-- guard. A native adapter must prove its finite path has exactly these
-- suffix guards; an epsilon test alone cannot establish that fact.
def guarded (edges : List Move) (input suffix : Path) (excluded : List Nat) : Option Path :=
  if admits .star excluded suffix then run edges (input++suffix) else none

theorem complete_FLOW_normalization_is_valid_on_every_admitted_suffix
    (edges : List Move) (input output suffix : Path) (excluded : List Nat)
    (pointPath : run edges input=some output) (allowed : admits .star excluded suffix=true) :
    guarded edges input suffix excluded=some (output++suffix) := by
  simp only [guarded,allowed,ite_true]
  exact every_finite_NORMAL_prefix_path_preserves_correlation edges input output suffix pointPath

def rootOnly (suffix : Path) : Option Path := if suffix=[] then some [] else none

theorem an_arbitrary_exact_probe_does_not_prove_suffix_uniformity :
    rootOnly []=some [] ∧ rootOnly [1]=none := by decide

theorem the_field_write_exclusion_rejects_the_overwritten_suffix
    (field : Nat) (rest : Path) : admits .star [field] (field::rest)=false := by
  simp [admits]

theorem EXACT_before_normalization_cannot_execute_a_deeper_read
    (headPath : Path) (field : Nat) (more : Path) :
    dropHead (headPath++field::more) headPath=none := by
  induction headPath with
  | nil => rfl
  | cons head tail ih => simpa [dropHead] using ih

end AuditNormalization
