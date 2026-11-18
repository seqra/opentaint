import NativeOutputFilter
import GuardedTermination
import PairedContext

namespace OperationalChecks
open NativeOutputFilter

def copyLocal : Destination := .statement true true false false false

theorem nested_calls_require_only_the_callers_first_destinations :
    skipOutput true [overwrite, overwrite] = true ∧
    skipOutput true [overwrite, .call] = false ∧
    skipOutput true [copyLocal] = false ∧
    skipOutput true [.boundary] = false := by decide

theorem the_three_alternating_outputs_have_live_destinations :
    ([Destination.call, Destination.call, Destination.boundary].map
      (fun dest => skipOutput true [dest])) = [false, false, false] := by decide

-- Observe the retained-reply controls at their real completed forward
-- runs. This checks the presence of a frontier, not an uncapped recurrence.
#eval do
  for run in [3, 5, 7, 9, 11] do
    let retained := GuardedTermination.retainedHistory run
    unless retained.observationActive do
      throw (IO.userError s!"expected retained root Target at run-{run}")
    IO.println s!"retained alternating run-{run}: DATA={retained.rows.length}, DT={retained.observationActive}, NORMAL={retained.report}"

theorem regular_controls_prove_disjointness_and_reject_a_shared_word :
    RegularCertificate.certifiesEmpty RegularCertificate.writer RegularCertificate.reader = true ∧
    RegularCertificate.certifiesEmpty RegularCertificate.writer RegularCertificate.overlapReader = false :=
  ⟨RegularCertificate.the_infinite_branching_languages_have_an_empty_product,
   RegularCertificate.a_real_shared_word_prevents_certification⟩

-- 2 is g and 3 is h. The branch h·R·h can consume the exact word h.g.h.
def hghWriter : RegularCertificate.Nfa :=
  ⟨0, [3], [(0,3,1), (1,2,2), (2,3,3)]⟩

theorem nested_controls_discharge_only_the_disjoint_word_language :
    PairedContext.check PairedContext.reader 1 PairedContext.writer = true ∧
    PairedContext.check PairedContext.reader 1 hghWriter = false :=
  ⟨PairedContext.the_nested_reader_has_no_shared_word, by decide⟩

theorem the_outer_position_is_appended_after_the_whole_nested_word :
    PairedContext.check PairedContext.suffixGrammar 1 PairedContext.suffixObserver [3] = false ∧
    PairedContext.check [.base 0 [3], .nested 0 [2] 0 [1]] 1 PairedContext.suffixObserver = true :=
  PairedContext.a_suffix_after_a_recursive_return_is_never_appended_at_the_base

theorem a_required_base_symbol_survives_every_regular_derivation
    (derives : RegularCertificate.Derives rules owner word)
    (inBase : ∀ c ∈ rules, c.callee = none → field ∈ c.chunk) :
    field ∈ word := by
  induction derives with
  | base present => exact inBase _ present rfl
  | call _ _ ih => exact List.mem_append.mpr (Or.inr ih)

def wordsOf : PairedContext.Rule → List Nat
  | .base _ word => word
  | .nested _ lead _ suffix => lead ++ suffix

theorem a_symbol_absent_from_every_nested_clause_is_absent_from_every_derivation
    (derives : PairedContext.Derives rules owner word)
    (absent : ∀ c ∈ rules, field ∉ wordsOf c) :
    field ∉ word := by
  induction derives with
  | base present => exact absent _ present
  | nested present _ ih =>
    have noOuter := absent _ present
    simp only [wordsOf, List.mem_append, not_or] at noOuter ⊢
    exact ⟨⟨noOuter.1, ih⟩, noOuter.2⟩

theorem a_symbol_absent_from_each_regular_clause_is_absent_from_the_word
    (derives : RegularCertificate.Derives rules owner word)
    (absent : ∀ c ∈ rules, field ∉ c.chunk) : field ∉ word := by
  induction derives with
  | base present => exact absent _ present
  | call present _ ih =>
    exact fun h => (List.mem_append.mp h).elim (absent _ present) ih

-- Both recorded negative fixtures can be discharged with this simpler
-- certificate. They do not establish necessity of the general products.
theorem the_regular_fixture_needs_no_general_product
    (left : RegularCertificate.Derives RegularCertificate.wg 0 word)
    (right : RegularCertificate.Derives RegularCertificate.rg 0 word) : False := by
  have hasF : 1 ∈ word := a_required_base_symbol_survives_every_regular_derivation left
    (by decide)
  exact a_symbol_absent_from_each_regular_clause_is_absent_from_the_word
    (field := 1) right (by decide) hasF

def plainWriter : List RegularCertificate.Clause :=
  [⟨0, [1], none⟩, ⟨0, [2], some 0⟩]

theorem the_nested_fixture_needs_no_general_cell_closure
    (left : RegularCertificate.Derives plainWriter 0 word)
    (right : PairedContext.Derives PairedContext.reader 0 word) : False :=
  a_symbol_absent_from_every_nested_clause_is_absent_from_every_derivation (field := 1) right
    (by decide) (a_required_base_symbol_survives_every_regular_derivation left (by decide))

end OperationalChecks
