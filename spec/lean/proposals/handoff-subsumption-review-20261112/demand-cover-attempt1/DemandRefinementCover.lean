import Std

/- Semantic order on concrete-mark DEMAND requests, with all other headers
   fixed. STAR denotes its late exact-point request, not uniform taint.
   MAY allows descendants. This proves request-language inclusion only.
   It does not assume that current C2 emits every permitted point at once,
   or prove a whole-engine progress simulation for MAY coarsening. -/
namespace DemandRefinementCover
set_option autoImplicit false

inductive Tail where | exact | star | may
  deriving DecidableEq
structure Demand where
  path : List Nat
  tail : Tail

def allows (d : Demand) (point : List Nat) : Prop :=
  match d.tail with
  | .exact | .star => point = d.path
  | .may => ∃ suffix, point = d.path ++ suffix

def covers (broad precise : Demand) : Prop :=
  ∀ point, allows precise point → allows broad point

theorem reflexive (d : Demand) : covers d d := fun _ h => h
theorem transitive (a b c : Demand) (ab : covers a b) (bc : covers b c) :
    covers a c := fun point h => ab point (bc point h)

theorem star_exact_equal (path point : List Nat) :
    allows ⟨path,.star⟩ point ↔ allows ⟨path,.exact⟩ point := Iff.rfl
theorem star_covers_exact (path : List Nat) : covers ⟨path,.star⟩ ⟨path,.exact⟩ :=
  fun _ h => h
theorem exact_covers_star (path : List Nat) : covers ⟨path,.exact⟩ ⟨path,.star⟩ :=
  fun _ h => h

theorem may_covers_descendant_point (prefix suffix : List Nat) :
    covers ⟨prefix,.may⟩ ⟨prefix ++ suffix,.exact⟩ := by
  intro point h
  exact ⟨suffix,h⟩

theorem may_covers_descendant_may (prefix extension : List Nat) :
    covers ⟨prefix,.may⟩ ⟨prefix ++ extension,.may⟩ := by
  intro point h
  obtain ⟨suffix,same⟩ := h
  refine ⟨extension ++ suffix, ?_⟩
  simpa [List.append_assoc] using same

theorem root_star_does_not_cover_child_exact (field : Nat) :
    ¬ covers ⟨[],.star⟩ ⟨[field],.exact⟩ := by
  intro cover
  have impossible := cover [field] rfl
  simp [allows] at impossible

/- One known implementation cell: from root MAY and a nonempty precise
   submitted path, the first-field rule retains only the first new field.
   Hence semantic coverage is not literal emitted-initial equality. -/
def rootMayStart : List Nat → Demand
  | [] => ⟨[],.exact⟩
  | [field] => ⟨[field],.exact⟩
  | field :: _ :: _ => ⟨[field],.star⟩

theorem first_field_is_exact (f : Nat) :
    (rootMayStart [f]).path = [f] ∧ (rootMayStart [f]).tail = .exact := ⟨rfl,rfl⟩
theorem second_field_is_not_retained (f g : Nat) :
    (rootMayStart [f,g]).path = [f] ∧ (rootMayStart [f,g]).tail = .star := ⟨rfl,rfl⟩
theorem requested_point_is_allowed_before_emission (f g : Nat) :
    allows ⟨[],.may⟩ [f,g] := ⟨[f,g],rfl⟩
theorem emitted_start_is_not_the_requested_deep_point (f g : Nat) :
    ¬ allows (rootMayStart [f,g]) [f,g] := by
  simp [allows,rootMayStart]

#print axioms reflexive
#print axioms transitive
#print axioms star_exact_equal
#print axioms star_covers_exact
#print axioms exact_covers_star
#print axioms may_covers_descendant_point
#print axioms may_covers_descendant_may
#print axioms root_star_does_not_cover_child_exact
#print axioms first_field_is_exact
#print axioms second_field_is_not_retained
#print axioms requested_point_is_allowed_before_emission
#print axioms emitted_start_is_not_the_requested_deep_point
end DemandRefinementCover
