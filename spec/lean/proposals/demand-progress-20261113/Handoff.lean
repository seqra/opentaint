import Progress

/- Executable retirement checker for finite neutral prefix evidence.
   Native evidence construction, control routing and scheduling are outside
   this checker. Unknown evidence always prevents retirement. -/
namespace RelationalLossHandoff
open NonEmptyPolicy DemandProgress

def composeMiddle (inputPrefix outputPrefix : Path) : Path → Path → Option PrefixRule
  | [], right => some ⟨inputPrefix ++ right, outputPrefix⟩
  | left, [] => some ⟨inputPrefix, outputPrefix ++ left⟩
  | left :: ls, right :: rs =>
      if left = right then composeMiddle inputPrefix outputPrefix ls rs else none

def compose (first second : PrefixRule) : Option PrefixRule :=
  composeMiddle first.read second.write first.write second.read

def covers (provider required : PrefixRule) : Bool :=
  match dropHead provider.read required.read with
  | none => false
  | some shift => decide (provider.write ++ shift = required.write)

def compile : Code → List PrefixRule
  | .transfer r => [r]
  | .choice left right => compile left ++ compile right
  | .sequence first second =>
      (compile first).flatMap fun a => (compile second).filterMap (compose a)

/-- None means an unrepresented origin, unclosed evidence cycle, or an
    unsupported native operation. An empty known list denotes no flow. -/
abbrev Evidence := Option (List PrefixRule)

def retire (normal : List PrefixRule) : Evidence → Bool
  | none => false
  | some origins => origins.all fun required => normal.any (covers · required)

def merge : Evidence → Evidence → Evidence
  | some a, some b => some (a ++ b)
  | _, _ => none

def uncovered (normal : List PrefixRule) (origins : List PrefixRule) : List PrefixRule :=
  origins.filter fun required => !(normal.any (covers · required))

theorem drop_prefix_append (a b input : Path) :
    dropHead (a ++ b) input = (dropHead a input).bind (dropHead b) := by
  induction a generalizing input with
  | nil => rfl
  | cons head tail ih =>
      cases input with
      | nil => rfl
      | cons actual rest =>
          by_cases same : head = actual
          · simp [dropHead, same, ih]
          · simp [dropHead, same]

theorem drop_prefix_recovers_input (head input rest : Path)
    (found : dropHead head input = some rest) : input = head ++ rest := by
  induction head generalizing input with
  | nil => simpa [dropHead] using found
  | cons field fields ih =>
      cases input with
      | nil => simp [dropHead] at found
      | cons actual tail =>
          by_cases same : field = actual
          · subst actual
            have next : dropHead fields tail = some rest := by simpa [dropHead] using found
            simp [ih tail next]
          · simp [dropHead, same] at found

theorem compose_middle_exact (a b c d input : Path) :
    ((composeMiddle a d b c).bind (fun r => applyRule r input)) =
      (dropHead a input).bind (fun suffix =>
        (dropHead c (b ++ suffix)).map (fun rest => d ++ rest)) := by
  induction b generalizing c with
  | nil =>
      simp only [composeMiddle, Option.bind_some, applyRule, drop_prefix_append, List.nil_append]
      cases dropHead a input <;> simp
  | cons field fields ih =>
      cases c with
      | nil =>
          cases found : dropHead a input <;>
            simp [composeMiddle, applyRule, found, dropHead, List.append_assoc]
      | cons actual rest =>
          by_cases same : field = actual
          · subst actual
            simpa [composeMiddle, dropHead] using ih rest
          · cases found : dropHead a input <;>
              simp [composeMiddle, dropHead, same, Ne.symm same]

theorem compose_exact (first second : PrefixRule) (input : Path) :
    (compose first second).bind (fun r => applyRule r input) =
      (applyRule first input).bind (applyRule second) := by
  rw [compose, compose_middle_exact]
  cases found : dropHead first.read input <;> simp [applyRule, found]

theorem cover_is_a_real_relation_inclusion (provider required : PrefixRule)
    (input output : Path) (checked : covers provider required = true)
    (found : applyRule required input = some output) :
    applyRule provider input = some output := by
  unfold covers at checked
  cases prefMatch : dropHead provider.read required.read with
  | none => simp [prefMatch] at checked
  | some shift =>
      have writes : provider.write ++ shift = required.write := by simpa [prefMatch] using checked
      have reads := drop_prefix_recovers_input _ _ _ prefMatch
      cases suffix : dropHead required.read input with
      | none => simp [applyRule, suffix] at found
      | some rest =>
          have result : required.write ++ rest = output := by simpa [applyRule, suffix] using found
          have original := drop_prefix_recovers_input _ _ _ suffix
          rw [original, reads, List.append_assoc, arbitrary_suffix_is_preserved]
          simp only [← List.append_assoc, writes, result]

def libraryReaches (normal : List PrefixRule) (input output : Path) : Prop :=
  ∃ rule ∈ normal, applyRule rule input = some output

theorem composition_has_an_executable_middle (first second : PrefixRule)
    (input output : Path) :
    (∃ result, compose first second = some result ∧ applyRule result input = some output) ↔
    (∃ middle, applyRule first input = some middle ∧ applyRule second middle = some output) := by
  constructor
  · rintro ⟨result, composed, found⟩
    have whole := compose_exact first second input
    rw [composed, Option.bind_some, found] at whole
    cases prior : applyRule first input with
    | none => simp [prior] at whole
    | some middle =>
        exact ⟨middle, rfl, by simpa [prior] using whole.symm⟩
  · rintro ⟨middle, firstFound, secondFound⟩
    have whole : (compose first second).bind (fun r => applyRule r input) = some output := by
      rw [compose_exact, firstFound]
      exact secondFound
    cases composed : compose first second with
    | none => simp [composed] at whole
    | some result =>
        exact ⟨result, rfl, by simpa [composed] using whole⟩

theorem compiled_evidence_is_sound (code : Code) (input output : Path)
    (found : libraryReaches (compile code) input output) : Reaches code input output := by
  induction code generalizing input output with
  | transfer r =>
      rcases found with ⟨rule, member, reached⟩
      have same : rule = r := by simpa [compile] using member
      subst rule
      exact Reaches.transfer reached
  | choice left right ihLeft ihRight =>
      rcases found with ⟨rule, member, reached⟩
      rcases List.mem_append.mp member with l | r
      · exact Reaches.left (ihLeft input output ⟨rule,l,reached⟩)
      · exact Reaches.right (ihRight input output ⟨rule,r,reached⟩)
  | sequence first second ihFirst ihSecond =>
      rcases found with ⟨rule, member, reached⟩
      rcases List.mem_flatMap.mp member with ⟨a, inFirst, viaSecond⟩
      rcases List.mem_filterMap.mp viaSecond with ⟨b, inSecond, composed⟩
      rcases (composition_has_an_executable_middle a b input output).mp
        ⟨rule,composed,reached⟩ with ⟨middle,firstFound,secondFound⟩
      exact Reaches.sequence (ihFirst input middle ⟨a,inFirst,firstFound⟩)
        (ihSecond middle output ⟨b,inSecond,secondFound⟩)

theorem compiled_evidence_is_complete {code : Code} {input output : Path}
    (found : Reaches code input output) : libraryReaches (compile code) input output := by
  induction found with
  | @transfer r input output found => exact ⟨r,by simp [compile],found⟩
  | @left a b input output prior ih =>
      rcases ih with ⟨rule,member,reached⟩
      exact ⟨rule,List.mem_append.mpr (Or.inl member),reached⟩
  | @right a b input output prior ih =>
      rcases ih with ⟨rule,member,reached⟩
      exact ⟨rule,List.mem_append.mpr (Or.inr member),reached⟩
  | @sequence a b input middle output first second ihFirst ihSecond =>
      rcases ihFirst with ⟨firstRule, inFirst, firstFound⟩
      rcases ihSecond with ⟨secondRule, inSecond, secondFound⟩
      rcases (composition_has_an_executable_middle firstRule secondRule input output).mpr
        ⟨middle,firstFound,secondFound⟩ with ⟨result,composed,reached⟩
      refine ⟨result, ?_, reached⟩
      exact List.mem_flatMap.mpr ⟨firstRule,inFirst,
        List.mem_filterMap.mpr ⟨secondRule,inSecond,composed⟩⟩

theorem retirement_covers_every_evidence_point (normal origins : List PrefixRule)
    (checked : retire normal (some origins) = true) (input output : Path)
    (found : libraryReaches origins input output) : libraryReaches normal input output := by
  rcases found with ⟨required, member, result⟩
  have witness := List.all_eq_true.mp checked required member
  rcases List.any_eq_true.mp witness with ⟨provider, present, covered⟩
  exact ⟨provider, present, cover_is_a_real_relation_inclusion _ _ _ _ covered result⟩

theorem retirement_preserves_all_precise_prefix_observations (code : Code)
    (normal : List PrefixRule) (checked : retire normal (some (compile code)) = true)
    (sourceSet sinkSet : Path → Prop)
    (found : ∃ input, sourceSet input ∧ ∃ output, Reaches code input output ∧ sinkSet output) :
    ∃ input, sourceSet input ∧ ∃ output, libraryReaches normal input output ∧ sinkSet output := by
  rcases found with ⟨input,sourceFound,output,reached,sinkFound⟩
  exact ⟨input,sourceFound,output,retirement_covers_every_evidence_point _ _ checked _ _
    (compiled_evidence_is_complete reached),sinkFound⟩

theorem unknown_origins_cannot_be_retired (normal : List PrefixRule) :
    retire normal none = false := rfl

theorem a_missing_origin_prevents_retirement (normal a b : List PrefixRule)
    (failed : retire normal (some b) = false) :
    retire normal (merge (some a) (some b)) = false := by
  change (a ++ b).all (fun r => normal.any (covers · r)) = false
  change b.all (fun r => normal.any (covers · r)) = false at failed
  rw [List.all_append, failed]
  simp

theorem both_origin_arrival_orders_have_the_same_decision (normal a b : List PrefixRule) :
    retire normal (merge (some a) (some b)) =
      retire normal (merge (some b) (some a)) := by
  simp [retire, merge, List.all_append, Bool.and_comm]

def f : Nat := AcyclicMayCycle.f
def g : Nat := AcyclicMayCycle.g
def h : Nat := 3
def normalBasis : List PrefixRule := [⟨[f,g],[]⟩, ⟨[],[f]⟩]

theorem the_read_evidence_is_computed_by_composition :
    compile (.sequence (.transfer ⟨[f],[]⟩) (.transfer ⟨[g],[]⟩)) =
      [⟨[f,g],[]⟩] := by decide

theorem reader_and_cut_specialization_are_both_retired :
    retire normalBasis (some [⟨[f,g],[]⟩]) = true ∧
    retire normalBasis (some [⟨[f],[f,f]⟩]) = true := by decide

theorem a_different_reader_is_not_covered_by_the_direct_writer :
    retire [⟨[],[f]⟩] (some [⟨[h],[f]⟩]) = false := by decide

theorem the_same_reader_becomes_covered_when_its_normal_arrives :
    retire [⟨[],[f]⟩, ⟨[h],[f]⟩] (some [⟨[h],[f]⟩]) = true := by decide

theorem uncovered_relations_are_an_executable_refinement_plan :
    uncovered [⟨[],[f]⟩] [⟨[f,g],[]⟩, ⟨[f],[f,f]⟩] =
      [⟨[f,g],[]⟩] := by decide

theorem reverse_writer_evidence_is_also_covered :
    retire [⟨[],[f,g]⟩, ⟨[f],[]⟩] (some [⟨[f],[]⟩]) = true := by decide

end RelationalLossHandoff

#print axioms RelationalLossHandoff.drop_prefix_append
#print axioms RelationalLossHandoff.drop_prefix_recovers_input
#print axioms RelationalLossHandoff.compose_middle_exact
#print axioms RelationalLossHandoff.compose_exact
#print axioms RelationalLossHandoff.cover_is_a_real_relation_inclusion
#print axioms RelationalLossHandoff.composition_has_an_executable_middle
#print axioms RelationalLossHandoff.compiled_evidence_is_sound
#print axioms RelationalLossHandoff.compiled_evidence_is_complete
#print axioms RelationalLossHandoff.retirement_covers_every_evidence_point
#print axioms RelationalLossHandoff.retirement_preserves_all_precise_prefix_observations
#print axioms RelationalLossHandoff.unknown_origins_cannot_be_retired
#print axioms RelationalLossHandoff.a_missing_origin_prevents_retirement
#print axioms RelationalLossHandoff.both_origin_arrival_orders_have_the_same_decision
#print axioms RelationalLossHandoff.the_read_evidence_is_computed_by_composition
#print axioms RelationalLossHandoff.reader_and_cut_specialization_are_both_retired
#print axioms RelationalLossHandoff.a_different_reader_is_not_covered_by_the_direct_writer
#print axioms RelationalLossHandoff.the_same_reader_becomes_covered_when_its_normal_arrives
#print axioms RelationalLossHandoff.uncovered_relations_are_an_executable_refinement_plan
#print axioms RelationalLossHandoff.reverse_writer_evidence_is_also_covered
