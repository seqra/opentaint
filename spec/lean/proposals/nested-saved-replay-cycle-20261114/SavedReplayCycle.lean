import UniformService

/- Scoped reference model: the selected saved-NORMAL replay policy
   is unchanged, before callee demand admission. There is no direct field
   read in wrapper. The leaf records below are ordinary code's two directions.
   No new transfer, tail, source permission, cleaner or pass rule is added. -/
namespace NestedSavedReplayCycle
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline BoundedLocalRouting NormalUniformNE
set_option linter.unusedSimpArgs false

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def point (base : Nat) (path : Path) (tail : Tail) (mark : Option Nat := none) : Ap :=
  ap base path tail mark

def inputSelector (path : Path) : Ap := point p path .may
def outputSelector (path : Path) : Ap := point ret path .star

def stableRows : List Row :=
  [⟨inputSelector [],outputSelector []⟩,
   ⟨inputSelector [],outputSelector [f]⟩,
   ⟨inputSelector [f],outputSelector []⟩,
   ⟨inputSelector [f],outputSelector [f]⟩]

def source (k : Nat := 0) : Offered :=
  ⟨point p (List.replicate (2*k+1) f ++ [g]) .must (some t),false⟩
def need : Offered := ⟨point p [] .may (some t),true⟩
def domainF : List Offered := [source 0,source 1,source 2,need]
def domainB : List Offered := [need]

/-- Full ordinary C2 plus the one-level field-f child family. Its routing
    mask cannot alter the policy "saved records first, unchanged". The mask
    is not attached to an AP key and no recursive child preparation occurs. -/
def prepared (run limit : Nat) (row : Row) (a : Offered) : List Seed :=
  ((emit run limit false row.entry a).flatMap fun q =>
    if q.ap.tail == .star && q.ap.path == row.entry.path &&
        decide (q.ap.path.length+1 ≤ limit) then
      [q,⟨{q.ap with path := q.ap.path ++ [f],tail := .exact},false⟩,
         ⟨{q.ap with path := q.ap.path ++ [f]},false⟩]
    else [q]).eraseDups

/-- In this qualified wrapper frame, the leaf's saved opposite record
    reads f.f; its saved same-direction record prepends f.f. Projecting
    both directions into a fresh entry/exit frame yields these same kernels. -/
def savedRead (q : Ap) : Option Value := moveE p ret [f,f] [] q
def savedWrite (q : Ap) : Option Value := moveE p ret [] [f,f] q

def leafReplay (q : Ap) : List Value := [savedRead q,savedWrite q].filterMap id

def normalPrecovered (q : Ap) (c : Value) : Bool :=
  !c.demand &&
    (decide (savedWrite q = some c) ||
     ((dropHead [f,f] q.path).isSome && decide (savedRead q = some c)))

def insertBy (key : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | a :: rest => if key x ≤ key a then x :: a :: rest else a :: insertBy key x rest

def sortBy (key : α → Nat) : List α → List α
  | [] => []
  | a :: rest => insertBy key a (sortBy key rest)

/-- Complete current wrapper candidates, not a chosen cycle edge.
    Every raw value first uses its own C2 family and its own paired C5. -/
def candidates (run limit : Nat) (domain : List Offered) : List Edge :=
  sortBy (fun e => e.1.path.length*2+e.2.ap.path.length)
  ((stableRows.flatMap fun row => domain.flatMap fun a =>
    let qs := prepared run limit row a
    qs.flatMap fun q => (leafReplay q.ap).filterMap fun raw =>
      if normalPrecovered q.ap raw then none
      else restricted limit qs q (cut limit raw) row).eraseDups)

def parentPubs : List Edge :=
  [(point p [] .star,val (point ret [] .may) true),
   (point p [] .star,val (point ret [f] .may) true),
   (point p [f] .star,val (point ret [] .may) true),
   (point p [f] .star,val (point ret [f] .may) true)]

/-- Callee executable MAY union hides child outputs but not their local
    qualified refinement rows. This is the existing two-view distinction. -/
def executablePubs : List Edge :=
  [(point p [] .star,val (point ret [] .may) true),
   (point p [f] .star,val (point ret [] .may) true)]

def swapped (e : Edge) : Row := ⟨{e.2.ap with base := p},{e.1 with base := ret}⟩
def nextRows (edges : List Edge) : List Row :=
  sortBy (fun a => a.entry.path.length*2+a.exit.path.length) ((edges.map swapped).eraseDups)

theorem full_forward_packet_at_run9 : candidates 9 8 domainF = parentPubs := by decide

theorem full_backward_packet_at_run10 : candidates 10 9 domainB = parentPubs := by decide

theorem no_new_uniform_law_can_remove_any_of_these_rows (normal edge : Edge)
    (inside : edge ∈ parentPubs) : SameLaneUniform.covers normal edge = false := by
  have may : edge.2.ap.tail = .may := by
    simp only [parentPubs,List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with h | h | h | h <;> rw [h] <;> rfl
  exact SameLaneUniform.no_may_output_is_retired normal edge may

theorem a_child_actual_cannot_make_the_unknown_saved_read_normal :
    savedRead (point p [f] .star) = some (val (point ret [] .may) true) ∧
    savedRead (point p [f,g] .must (some t)) = none := by decide

theorem child_preparation_and_exact_probes_have_not_been_omitted :
    (stableRows.flatMap fun row => domainB.flatMap fun a => prepared 10 9 row a).any
      (fun q => q.ap.path == [f,f] && q.ap.tail == .star) = true ∧
    (stableRows.flatMap fun row => domainB.flatMap fun a => prepared 10 9 row a).any
      (fun q => q.ap.path == [f,f] && q.ap.tail == .exact) = true := by decide

theorem the_complete_four_row_handoff_is_unchanged :
    nextRows parentPubs = stableRows := by decide

/-- A one-field plan covers the first split, but its STAR child still
    uses the saved opposite inside match. A second split is not authorized
    by the original root selector's one-field budget. -/
theorem one_level_cover_does_not_remove_the_nested_may_result :
    prepared 9 8 ⟨inputSelector [],outputSelector []⟩ need =
      [⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,
       ⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩] ∧
    savedRead (point p [f] .exact) = none ∧
    savedRead (point p [f] .star) = some (val (point ret [] .may) true) ∧
    ¬legalSeed 8 (inputSelector []) ⟨point p [f,f] .star,false⟩ := by decide

end NestedSavedReplayCycle

#print axioms NestedSavedReplayCycle.full_forward_packet_at_run9
#print axioms NestedSavedReplayCycle.full_backward_packet_at_run10
#print axioms NestedSavedReplayCycle.no_new_uniform_law_can_remove_any_of_these_rows
#print axioms NestedSavedReplayCycle.a_child_actual_cannot_make_the_unknown_saved_read_normal
#print axioms NestedSavedReplayCycle.child_preparation_and_exact_probes_have_not_been_omitted
#print axioms NestedSavedReplayCycle.the_complete_four_row_handoff_is_unchanged

#print axioms NestedSavedReplayCycle.one_level_cover_does_not_remove_the_nested_may_result
