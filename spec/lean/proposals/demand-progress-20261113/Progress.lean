import BbTrace

/- A finite acyclic prefix-transfer reference. It is a constructive target
   for a progress strategy, not a proof about the current C2/C5 scheduler. -/
namespace DemandProgress
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle AcyclicMayBbTrace

structure PrefixRule where
  read : Path
  write : Path
  deriving DecidableEq, Repr

def applyRule (r : PrefixRule) (input : Path) : Option Path :=
  (dropHead r.read input).map (fun rest => r.write ++ rest)

inductive Code where
  | transfer (r : PrefixRule)
  | choice (left right : Code)
  | sequence (first second : Code)
  deriving Repr

def outputs : Code → Path → List Path
  | .transfer r, input => (applyRule r input).toList
  | .choice left right, input => outputs left input ++ outputs right input
  | .sequence first second, input =>
      (outputs first input).flatMap (outputs second)

inductive Reaches : Code → Path → Path → Prop where
  | transfer {r input output} (found : applyRule r input = some output) :
      Reaches (.transfer r) input output
  | left {a b input output} (found : Reaches a input output) :
      Reaches (.choice a b) input output
  | right {a b input output} (found : Reaches b input output) :
      Reaches (.choice a b) input output
  | sequence {a b input middle output}
      (first : Reaches a input middle) (second : Reaches b middle output) :
      Reaches (.sequence a b) input output

theorem outputs_sound (code : Code) (input output : Path)
    (found : output ∈ outputs code input) : Reaches code input output := by
  induction code generalizing input output with
  | transfer r =>
      cases result : applyRule r input with
      | none => simp [outputs, result] at found
      | some value =>
          have eq : output = value := by simpa [outputs, result] using found
          subst output
          exact Reaches.transfer result
  | choice left right ihLeft ihRight =>
      rcases List.mem_append.mp found with l | r
      · exact Reaches.left (ihLeft input output l)
      · exact Reaches.right (ihRight input output r)
  | sequence first second ihFirst ihSecond =>
      rcases List.mem_flatMap.mp found with ⟨middle, fromFirst, fromSecond⟩
      exact Reaches.sequence (ihFirst input middle fromFirst) (ihSecond middle output fromSecond)

theorem outputs_complete {code : Code} {input output : Path}
    (found : Reaches code input output) : output ∈ outputs code input := by
  induction found with
  | transfer found => simp [outputs, found]
  | left _ ih => exact List.mem_append.mpr (Or.inl ih)
  | right _ ih => exact List.mem_append.mpr (Or.inr ih)
  | sequence _ _ first second =>
      exact List.mem_flatMap.mpr ⟨_, first, second⟩

theorem exact_findings {code : Code} {input output : Path} :
    output ∈ outputs code input ↔ Reaches code input output :=
  ⟨outputs_sound code input output, outputs_complete⟩

def maxResults : Code → Nat
  | .transfer _ => 1
  | .choice left right => maxResults left + maxResults right
  | .sequence first second => maxResults first * maxResults second

theorem flat_map_bound (inputs : List Path) (f : Path → List Path) (bound : Nat)
    (bounded : ∀ input, (f input).length ≤ bound) :
    (inputs.flatMap f).length ≤ inputs.length * bound := by
  induction inputs with
  | nil => simp
  | cons input rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      exact Nat.le_trans (Nat.add_le_add (bounded input) ih)
        (by simp [Nat.add_mul, Nat.add_comm])

theorem outputs_have_a_finite_program_bound (code : Code) (input : Path) :
    (outputs code input).length ≤ maxResults code := by
  induction code generalizing input with
  | transfer r =>
      cases result : applyRule r input <;> simp [outputs, maxResults, result]
  | choice left right ihLeft ihRight =>
      simpa [outputs, maxResults] using Nat.add_le_add (ihLeft input) (ihRight input)
  | sequence first second ihFirst ihSecond =>
      exact Nat.le_trans (flat_map_bound (outputs first input) (outputs second)
          (maxResults second) ihSecond)
        (Nat.mul_le_mul_right _ (ihFirst input))

theorem arbitrary_suffix_is_preserved (inputPrefix outputPrefix suffix : Path) :
    applyRule ⟨inputPrefix,outputPrefix⟩ (inputPrefix ++ suffix) = some (outputPrefix ++ suffix) := by
  have same (head rest : Path) : dropHead head (head ++ rest) = some rest := by
    induction head with
    | nil => rfl
    | cons field fields ih => simpa [dropHead] using ih
  simp [applyRule, same]

theorem correlated_specialization_has_the_same_image (inputPrefix outputPrefix shift suffix : Path) :
    applyRule ⟨inputPrefix,outputPrefix⟩ (inputPrefix ++ shift ++ suffix) =
      applyRule ⟨inputPrefix ++ shift,outputPrefix ++ shift⟩ (inputPrefix ++ shift ++ suffix) := by
  simp only [List.append_assoc]
  rw [arbitrary_suffix_is_preserved]
  rw [← List.append_assoc inputPrefix shift suffix, arbitrary_suffix_is_preserved]
  simp only [List.append_assoc]

def readFG : PrefixRule := ⟨[f,g],[]⟩
def writeF : PrefixRule := ⟨[],[f]⟩
def choose : Code := .choice (.transfer readFG) (.transfer writeF)
def twoCalls : Code := .sequence choose choose

/-- [f,g] is a concrete point inside the example's f.MUST source. -/
theorem exact_example_has_both_real_outputs :
    outputs twoCalls [f,g] = [[f],[f,f,f,g]] := by decide

theorem an_exact_f_source_cannot_use_the_read_branch :
    outputs twoCalls [f] = [[f,f,f]] := by decide

theorem fixed_relation_reference_never_needs_an_iteration_limit :
    maxResults twoCalls = 4 ∧
    ∀ input, (outputs twoCalls input).length ≤ 4 := by
  constructor
  · rfl
  · exact outputs_have_a_finite_program_bound twoCalls

theorem normal_writer_already_covers_the_raw_specialization :
    applyRule writeF [f] = some [f,f] ∧
    applyRule ⟨[f],[f,f]⟩ [f] = some [f,f] := by decide

theorem a_relative_cut_forgets_that_correlation :
    cut 1 (val (ap ret [f,f] .exact)) = val (ap ret [f] .ne) true ∧
    admits .ne [] [g] = true ∧
    applyRule writeF [f] ≠ some [f,g] := by decide

/-- Already established in the selected C5 model: more global precision
    does not raise this particular pair's local output budget. -/
theorem existing_bb_cycle_repeats_the_same_cut_at_arbitrary_limits (run k : Nat) :
    restrictOne (run+5) (k+2) false [source] firstMethodQuery
      (val (ap ret [f,f] .must)) methodForward5 =
        some (firstMethodQuery,val (ap ret [f] .ne) true) :=
  method_cut_repeats_at_every_later_limit run k

def stableCoarse (n : Nat) : Bool :=
  forwardHandoffs n && laterHandoffs n

theorem changing_only_the_run_number_does_not_ensure_progress (n : Nat) :
    stableCoarse n = true := by
  simp [stableCoarse, all_forward_handoffs_keep_the_cycle,
    arbitrarily_many_later_forward_handoffs_have_demand]

/-- A complete exact NORMAL model can replace coarse refinement guidance
    for arbitrary source sets and sink observations in this unary scope. -/
theorem exact_replay_preserves_every_finding (code : Code)
    (sourceSet sinkSet : Path → Prop) :
    (∃ input, sourceSet input ∧ ∃ output, Reaches code input output ∧ sinkSet output) ↔
    (∃ input, sourceSet input ∧ ∃ output, output ∈ outputs code input ∧ sinkSet output) := by
  constructor
  · rintro ⟨input, sourceFound, output, reached, sinkFound⟩
    exact ⟨input, sourceFound, output, outputs_complete reached, sinkFound⟩
  · rintro ⟨input, sourceFound, output, reached, sinkFound⟩
    exact ⟨input, sourceFound, output, outputs_sound code input output reached, sinkFound⟩

/-- Replaying the two retained NORMAL branch relations on the ACTUAL
    uniform source, rather than on a lossy STAR query. No C5 is bypassed. -/
def firstNormalOffers : List Value := body false (ap p [f] .must (some t))
def secondNormalOffers : List Value := firstNormalOffers.flatMap fun first =>
  body false {first.ap with base := p}

theorem first_actual_call_replays_only_normal_uniform_results :
    firstNormalOffers =
      [val (ap ret [] .must (some t)), val (ap ret [f,f] .must (some t))] := by decide

theorem second_actual_call_replays_only_normal_uniform_results :
    secondNormalOffers =
      [val (ap ret [] .must (some t)), val (ap ret [f] .must (some t)),
       val (ap ret [f,f,f] .must (some t))] := by decide

theorem all_actual_replay_outputs_fit_run5_and_are_normal :
    secondNormalOffers.all (fun c => !c.demand && decide (c.ap.path.length ≤ 4)) = true := by decide

def terminalG (n : Nat) : Path := List.replicate n f ++ [g]
def terminalH (n : Nat) : Path := List.replicate n f ++ [3]

theorem these_two_unbounded_path_families_are_disjoint (n m : Nat) :
    terminalG n ≠ terminalH m := by
  intro same
  have last := congrArg (fun path : Path => path.reverse.head?) same
  simp [terminalG, terminalH, g] at last

theorem a_deeper_pair_has_equal_cuts_at_every_finite_depth (depth : Nat) :
    cut depth (val (ap p (terminalG (depth+1)) .exact (some t))) =
      val (ap p (List.replicate depth f) .ne (some t)) true ∧
    cut depth (val (ap p (terminalH (depth+1)) .exact (some t))) =
      val (ap p (List.replicate depth f) .ne (some t)) true := by
  simp [cut, val, ap, terminalG, terminalH, List.take_append,
    List.take_replicate, Nat.min_eq_left (Nat.le_succ depth)] <;> omega

theorem arbitrary_finite_depth_still_has_a_false_overlap (depth : Nat) :
    ∃ left right : Path, left ≠ right ∧
      cut depth (val (ap p left .exact (some t))) =
      cut depth (val (ap p right .exact (some t))) := by
  refine ⟨terminalG (depth+1), terminalH (depth+1),
    these_two_unbounded_path_families_are_disjoint _ _, ?_⟩
  exact (a_deeper_pair_has_equal_cuts_at_every_finite_depth depth).1.trans
    (a_deeper_pair_has_equal_cuts_at_every_finite_depth depth).2.symm

end DemandProgress

#print axioms DemandProgress.outputs_sound
#print axioms DemandProgress.outputs_complete
#print axioms DemandProgress.exact_findings
#print axioms DemandProgress.flat_map_bound
#print axioms DemandProgress.outputs_have_a_finite_program_bound
#print axioms DemandProgress.arbitrary_suffix_is_preserved
#print axioms DemandProgress.correlated_specialization_has_the_same_image
#print axioms DemandProgress.exact_example_has_both_real_outputs
#print axioms DemandProgress.an_exact_f_source_cannot_use_the_read_branch
#print axioms DemandProgress.fixed_relation_reference_never_needs_an_iteration_limit
#print axioms DemandProgress.normal_writer_already_covers_the_raw_specialization
#print axioms DemandProgress.a_relative_cut_forgets_that_correlation
#print axioms DemandProgress.existing_bb_cycle_repeats_the_same_cut_at_arbitrary_limits
#print axioms DemandProgress.changing_only_the_run_number_does_not_ensure_progress
#print axioms DemandProgress.exact_replay_preserves_every_finding
#print axioms DemandProgress.first_actual_call_replays_only_normal_uniform_results
#print axioms DemandProgress.second_actual_call_replays_only_normal_uniform_results
#print axioms DemandProgress.all_actual_replay_outputs_fit_run5_and_are_normal
#print axioms DemandProgress.these_two_unbounded_path_families_are_disjoint
#print axioms DemandProgress.a_deeper_pair_has_equal_cuts_at_every_finite_depth
#print axioms DemandProgress.arbitrary_finite_depth_still_has_a_false_overlap
