/-
  Initial emission policy audit. No policy is selected in this file.

  This file checks local AP obligations and counterexamples. It does not prove
  termination of the analyzer or implement a repair. All example exclusions
  are Empty. This is also the scope in which the legacy emitW match gate and
  the current Kotlin abstract-demand overlap gate agree.

  The library encodes MUST as concrete .any with a NORMAL layer, and MAY as
  .any with a DEMAND layer. Current concrete STAR starts with STAR/DEMAND.
  Basic.startFact has the older concrete STAR row; the examples below do not
  use that row. The separate cycle model supplies the current row.

  concreteMeet uses the older three-tail emitM. It proves a location/mark
  contract, not equality to every current Kotlin commonPart cell. In
  particular, Kotlin has a distinct ANY_TAINT/STAR meet cell. The actual
  forward input and demand below use ANY_TAINT/ANY; emitTX preserves MUST
  for that checked cell. No unproved MUST/STAR bridge is used here.
-/
import ApSpec.AbsDefs
import ApSpec.AnyTaintExDefs

namespace ApSpec.InitialEmissionPolicies
open ApSpec ApSpec.Abs ApSpec.Handoff ApSpec.AnyTaintEx
set_option autoImplicit false

/-! ## 1. Candidate families, with no default repair -/

/-- Keep the actual/demand intersection and its concrete mark. Under an
    abstract demand this is a semantic change from F72. -/
def concreteMeet (d a : PFact) : Option PFact := emitM d a

/-- Intersect first, then replace the mark. This candidate must also decide
    how to represent EXACT and MUST with an abstract mark. -/
def meetThenErase (d a : PFact) : Option PFact :=
  (emitM d a).map fun j =>
    if d.mark = .star then { j with mark := .star } else j

/-- A geometry-only variant restores the ordinary FLOW form after the
    intersection. In particular, it does not retain a MUST certificate. -/
def flowOfMeet (d a : PFact) : Option PFact :=
  (emitM d a).map fun j =>
    if d.mark = .star then flowForm j else j

/-- A blanket ANY rejection is a separate candidate, not an AP rule. -/
def dropAnyInput (d a : PFact) : Option PFact :=
  if a.kind.isAny then none else emitW d a

/-- The relevant current admission guard. An abstract EXACT initial is
    illegal. MUST needs a concrete mark and an ANY tail. -/
def initialLegal (j : PFact) (must : Bool) : Bool :=
  if must then
    j.kind.isAny && (match j.mark with | .conc _ => true | _ => false)
  else
    match j.kind, j.mark with
    | .exact, .star => false
    | .exact, .starEx _ => false
    | _, _ => true

/-- Keep all location, mark, satisfaction and inside-demand obligations.
    This local theorem is not a whole-run equivalence theorem. -/
theorem concreteMeet_obligations {d a : PFact} {l : Loc} {t : Mark}
    (ham : a.mark = .conc t) (hd : d.covers l) (ha : a.covers l) :
    ∃ j, concreteMeet d a = some j ∧ j.covers l ∧
      satW j a = true ∧ insideB j d = true ∧ j.mark = .conc t := by
  obtain ⟨j, he, hc, hs⟩ := RCore.emitM_contract_I d a l t ham hd ha
  refine ⟨j, he, hc, satW_of_satI hs, (emitM_insideB he ham).1, ?_⟩
  rw [RCore.emitM_mark he, ham]

/-! ## 2. One actual exact mark must not become an abstract EXACT initial -/

def rootFlowDemand : PFact := ⟨1, [], .any, .star⟩
def flowRoot : PFact := ⟨1, [], .star Excl.empty, .star⟩
def actualExact (t : Mark) : PFact := ⟨1, [], .exact, .conc t⟩
def actualAny (t : Mark) : PFact := ⟨1, [], .any, .conc t⟩
def abstractExact : PFact := ⟨1, [], .exact, .star⟩

theorem current_shares_marks (t u : Mark) :
    emitW rootFlowDemand (actualExact t) = some flowRoot ∧
    emitW rootFlowDemand (actualExact u) = some flowRoot := by
  constructor <;> rfl

theorem meet_then_erase_has_illegal_exact :
    meetThenErase rootFlowDemand (actualExact 7) = some abstractExact ∧
    initialLegal abstractExact false = false := by decide

theorem concrete_meet_keeps_required_mark (t : Mark) :
    concreteMeet rootFlowDemand (actualExact t) = some (actualExact t) ∧
    initialLegal (actualExact t) false = true := by
  constructor <;> rfl

theorem concrete_meet_is_not_current_shared_policy :
    concreteMeet rootFlowDemand (actualExact 7) ≠
      emitW rootFlowDemand (actualExact 7) := by decide

def actualNamedSubtree : PFact :=
  ⟨1, [3], .star Excl.empty, .conc 7⟩
def namedFlow : PFact := ⟨1, [3], .star Excl.empty, .star⟩

theorem using_actual_geometry_can_keep_a_known_prefix :
    emitW rootFlowDemand actualNamedSubtree = some flowRoot ∧
    flowOfMeet rootFlowDemand actualNamedSubtree = some namedFlow ∧
    insideB namedFlow rootFlowDemand = true ∧
    satW namedFlow actualNamedSubtree = true := by decide

theorem geometry_only_does_not_retain_whole_object_taint :
    flowOfMeet rootFlowDemand (actualAny 7) = some flowRoot := by decide

theorem concrete_requirements_still_check_the_actual_mark :
    emitW ⟨1, [], .any, .conc 7⟩ (actualAny 8) = none ∧
    concreteMeet ⟨1, [], .any, .conc 7⟩ (actualAny 8) = none ∧
    concreteMeet rootFlowDemand (actualAny 8) = some (actualAny 8) := by decide

/-! ## 3. Source ALL and MAY are different evidence -/

/-- A whole-object source marks every descendant. -/
def sourceMust (t : Mark) : XFact :=
  ⟨⟨actualAny t, false⟩, Excl.empty⟩

/-- The same path syntax with a DEMAND layer is MAY, not source ALL. -/
def mayInput (t : Mark) : XFact :=
  ⟨⟨actualAny t, true⟩, Excl.empty⟩

def move (b u : Base) (p q : List Acc) : MicroEdge :=
  (⟨b, p, .star Excl.empty, .star⟩,
   ⟨u, q, .star Excl.empty, .star⟩)

def readField : MicroEdge := move 1 2 [3] []
def mustRead (t : Mark) : XFact :=
  ⟨⟨⟨2, [], .any, .conc t⟩, false⟩, Excl.empty⟩
def mayRead (t : Mark) : XFact :=
  ⟨⟨⟨2, [], .any, .conc t⟩, true⟩, Excl.empty⟩
def flowMayRead : XFact :=
  ⟨⟨⟨2, [], .any, .star⟩, true⟩, Excl.empty⟩

theorem actual_must_read_is_normal :
    (bindX (sourceMust 7) readField).facts = [mustRead 7] := by decide

theorem actual_may_read_stays_demand :
    (bindX (mayInput 7) readField).facts = [mayRead 7] := by decide

theorem current_flow_seed_loses_source_all_evidence :
    emitW rootFlowDemand (sourceMust 7).af.fact = some flowRoot ∧
    (bindX (startX flowRoot false Excl.empty) readField).facts =
      [flowMayRead] := by decide

def erasedAny : PFact := ⟨1, [], .any, .star⟩

theorem preserving_any_without_must_still_starts_demand :
    meetThenErase rootFlowDemand (sourceMust 7).af.fact = some erasedAny ∧
    initialLegal erasedAny false = true ∧
    (startX erasedAny false Excl.empty).af.demand = true ∧
    (bindX (startX erasedAny false Excl.empty) readField).facts =
      [flowMayRead] := by decide

theorem preserving_must_with_abstract_mark_is_illegal :
    initialLegal erasedAny true = false := by decide

theorem concrete_source_fallback_retains_must_locally :
    emitTX emitX rootFlowDemand (sourceMust 7).af.fact true Excl.empty =
      some (actualAny 7, true, Excl.empty) ∧
    startX (actualAny 7) true Excl.empty = sourceMust 7 ∧
    (bindX (startX (actualAny 7) true Excl.empty) readField).facts =
      [mustRead 7] := by decide

/-! ## 3b. The complete helper under the concrete MUST candidate

The helper has two independent model routes in each of its first two
statements. The original test uses the same named storage field for both.
No deduplication is needed for these local statements. Repeated identical
results in this small list are harmless and are shown explicitly.

    bytes = p       OR bytes = p.H
    out = bytes     OR out.H = bytes
    ret = out

This is not a proposed replacement for the F72 contract. It checks what a
different selected initial would do under the existing transfer operation.
-/

def helperStep (es : List MicroEdge) (xs : List XFact) : List XFact :=
  xs.flatMap fun x => es.flatMap fun e =>
    (bindX x e).facts.map (limitFX (fun _ => true) 1)

def helperCandidateInitial : List XFact :=
  match emitTX emitX rootFlowDemand (sourceMust 7).af.fact true Excl.empty with
  | some (j, must, ex) => [startX j must ex]
  | none => []

def helperCandidate : List XFact :=
  let bytes := helperStep [move 1 2 [] [], move 1 2 [3] []]
    helperCandidateInitial
  let out := helperStep [move 2 3 [] [], move 2 3 [] [3]] bytes
  helperStep [move 3 4 [] []] out

def concreteReturn (p : List Acc) : XFact :=
  ⟨⟨⟨4, p, .any, .conc 7⟩, false⟩, Excl.empty⟩

def helperGuide : DemandEdge :=
  ⟨rootFlowDemand, some ⟨4, [], .star Excl.empty, .star⟩⟩

theorem candidate_helper_has_no_demand_result :
    helperCandidate = [concreteReturn [], concreteReturn [3],
      concreteReturn [], concreteReturn [3]] ∧
    ∀ x, x ∈ helperCandidate → x.af.demand = false := by
  constructor
  · decide
  · intro x hx
    have he : helperCandidate = [concreteReturn [], concreteReturn [3],
      concreteReturn [], concreteReturn [3]] := by decide
    rw [he] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h <;> subst x <;> rfl

theorem candidate_helper_still_satisfies_entry_and_exit_demand :
    insideB (actualAny 7) helperGuide.din = true ∧
    satW (actualAny 7) (sourceMust 7).af.fact = true ∧
    restrictI (actualAny 7) (concreteReturn []).af helperGuide =
      some (concreteReturn []).af ∧
    restrictI (actualAny 7) (concreteReturn [3]).af helperGuide =
      some (concreteReturn [3]).af := by decide

/-! ## 4. A MAY input does not justify a universal-taint assertion -/

/-- One concrete heap: only path [4] has the mark. -/
def onlyOtherField (l : Loc) : Prop :=
  l.base = 1 ∧ l.path = [4] ∧ l.mark = 7

def fieldDemand : PFact := ⟨1, [3], .exact, .conc 7⟩
def selectedLocation : Loc := ⟨1, [3], 7⟩
def otherLocation : Loc := ⟨1, [4], 7⟩

/-- A minimal heap interpretation of a MAY input: some location in the
    pattern has taint. This is weaker than the MUST statement below. -/
def MayValid (f : PFact) (heap : Loc → Prop) : Prop :=
  ∃ l, f.covers l ∧ heap l

/-- The meaning of an actual source ALL result: every covered location has
    taint. Only a concrete mark can establish this assertion. -/
def MustValid (f : PFact) (heap : Loc → Prop) : Prop :=
  ∀ l, coversFX f Excl.empty l → heap l

/-- An existential MAY assertion is true in this heap. -/
theorem may_has_one_witness :
    (actualAny 7).covers otherLocation ∧ onlyOtherField otherLocation := by
  constructor
  · exact ⟨rfl, ⟨[4], rfl, True.intro⟩, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- But the input does not establish taint at the selected field. -/
theorem may_does_not_establish_demanded_field :
    fieldDemand.covers selectedLocation ∧ ¬ onlyOtherField selectedLocation := by
  constructor
  · exact ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩
  · intro h
    have : ([3] : List Acc) = [4] := h.2.1
    contradiction

theorem same_pattern_can_validate_may_but_not_must :
    MayValid (actualAny 7) onlyOtherField ∧
    ¬ MustValid (actualAny 7) onlyOtherField := by
  refine ⟨⟨otherLocation, may_has_one_witness⟩, ?_⟩
  intro hm
  apply may_does_not_establish_demanded_field.2
  apply hm selectedLocation
  exact ⟨rfl, ⟨[3], rfl, True.intro, rfl⟩, 7, rfl, rfl⟩

theorem source_all_includes_the_named_field (heap : Loc → Prop)
    (hm : MustValid (sourceMust 7).af.fact heap) :
    heap selectedLocation := by
  apply hm selectedLocation
  exact ⟨rfl, ⟨[3], rfl, True.intro, rfl⟩, 7, rfl, rfl⟩

/-- The AP can select this conditional hypothesis. This is not a proof that
    the concrete heap supplies that field; application/layers still matter. -/
theorem possible_field_is_not_an_invalid_query :
    emitW fieldDemand (actualAny 7) = some fieldDemand ∧
    satW fieldDemand (actualAny 7) = true ∧
    insideB fieldDemand fieldDemand = true := by decide

theorem blanket_drop_breaks_local_emission_obligation :
    fieldDemand.covers selectedLocation ∧
    (actualAny 7).covers selectedLocation ∧
    dropAnyInput fieldDemand (actualAny 7) = none := by
  refine ⟨⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩,
    ⟨rfl, ⟨[3], rfl, True.intro⟩, rfl⟩, rfl⟩

/-- In a heap with taint at [3], deleting the same MAY input would delete
    the real required path as well. ANY alone cannot distinguish these heaps. -/
def onlySelectedField (l : Loc) : Prop :=
  l.base = 1 ∧ l.path = [3] ∧ l.mark = 7

theorem possible_field_can_be_real :
    (actualAny 7).covers selectedLocation ∧ onlySelectedField selectedLocation := by
  exact ⟨⟨rfl, ⟨[3], rfl, True.intro⟩, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-! ## 5. A cut ANY input can acquire a named field at a larger limit -/

def exactDeep : XFact :=
  ⟨⟨⟨1, [3, 4], .exact, .conc 7⟩, false⟩, Excl.empty⟩
def cutOne : XFact :=
  ⟨⟨⟨1, [3], .any, .conc 7⟩, true⟩, Excl.empty⟩
def deepDemand : PFact := ⟨1, [3, 4], .exact, .conc 7⟩

theorem field_limit_creates_any_without_a_program_loop :
    limitFX (fun _ => true) 1 exactDeep = cutOne ∧
    limitFX (fun _ => true) 2 exactDeep = exactDeep := by decide

theorem deeper_query_is_admitted_after_a_cut :
    emitW deepDemand cutOne.af.fact = some deepDemand ∧
    insideB deepDemand deepDemand = true ∧
    satW deepDemand cutOne.af.fact = true := by decide

theorem equal_frontier_counts_do_not_prove_equal_information :
    ([limitFX (fun _ => true) 1 exactDeep]).length =
      ([limitFX (fun _ => true) 2 exactDeep]).length ∧
    [limitFX (fun _ => true) 1 exactDeep] ≠
      [limitFX (fun _ => true) 2 exactDeep] := by decide

/-! ## 6. A location-set equality is not a summary-relation equality -/

def identityStar : PFact := flowRoot
def identityAny : PFact := ⟨1, [], .any, .star⟩

theorem star_any_have_same_locations (l : Loc) :
    identityStar.covers l ↔ identityAny.covers l := by
  obtain ⟨b, p, t⟩ := l
  simp [PFact.covers, identityStar, identityAny, flowRoot, tailI,
    AnyTaintEx.admits_empty, MarkA.admits]

/-- ANY output relates independent suffixes. STAR output relates one bound
    suffix. Replacing one with the other is not mere normalization. -/
theorem any_and_star_relations_differ :
    den identityStar identityAny ⟨1, [3], 7⟩ ⟨1, [4], 7⟩ ∧
    ¬ den identityStar identityStar ⟨1, [3], 7⟩ ⟨1, [4], 7⟩ := by
  constructor
  · exact ⟨rfl, rfl, True.intro, rfl, True.intro,
      [3], [4], rfl, rfl, rfl, True.intro⟩
  · intro h
    obtain ⟨_, _, _, _, _, σ, τ, hin, hout, _, htail⟩ := h
    have hs : σ = [3] := by simpa [identityStar, flowRoot] using hin.symm
    have ht : τ = [4] := by simpa [identityStar, flowRoot] using hout.symm
    have heq := htail.1
    rw [hs, ht] at heq
    contradiction

#print axioms concreteMeet_obligations
#print axioms current_shares_marks
#print axioms meet_then_erase_has_illegal_exact
#print axioms concrete_meet_keeps_required_mark
#print axioms concrete_meet_is_not_current_shared_policy
#print axioms using_actual_geometry_can_keep_a_known_prefix
#print axioms geometry_only_does_not_retain_whole_object_taint
#print axioms concrete_requirements_still_check_the_actual_mark
#print axioms actual_must_read_is_normal
#print axioms actual_may_read_stays_demand
#print axioms current_flow_seed_loses_source_all_evidence
#print axioms preserving_any_without_must_still_starts_demand
#print axioms preserving_must_with_abstract_mark_is_illegal
#print axioms concrete_source_fallback_retains_must_locally
#print axioms candidate_helper_has_no_demand_result
#print axioms candidate_helper_still_satisfies_entry_and_exit_demand
#print axioms may_has_one_witness
#print axioms may_does_not_establish_demanded_field
#print axioms same_pattern_can_validate_may_but_not_must
#print axioms source_all_includes_the_named_field
#print axioms possible_field_is_not_an_invalid_query
#print axioms blanket_drop_breaks_local_emission_obligation
#print axioms possible_field_can_be_real
#print axioms field_limit_creates_any_without_a_program_loop
#print axioms deeper_query_is_admitted_after_a_cut
#print axioms equal_frontier_counts_do_not_prove_equal_information
#print axioms star_any_have_same_locations
#print axioms any_and_star_relations_differ

end ApSpec.InitialEmissionPolicies
