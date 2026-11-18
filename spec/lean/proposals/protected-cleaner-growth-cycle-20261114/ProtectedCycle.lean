import ProtectedGrowth

namespace ProtectedCleanerCycle
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline BoundedLocalRouting BoundedOrdinaryCycle
open NormalUniformNE ProtectedCleanerGrowth
set_option linter.unusedSimpArgs false

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def publishGrowing (run limit : Nat) (backward : Bool) (row : Row)
    (actual : Offered) : List Edge :=
  (recurringCommands run limit backward row actual).filterMap (growingSummary limit backward row)

theorem both_forward_calls_publish_their_concrete_protected_cuts
    (run n : Nat) (may : Bool) :
    publishGrowing run (n+2) false (fRow n may) ProtectedCleanerGrowth.source = [fEdge n] ∧
    publishGrowing run (n+2) false (fRow n may) (fOffer2 n) = [fEdge2 n] := by
  rcases all_four_edges_are_generated_by_the_actual_growing_branch n may with ⟨a,b,_⟩
  constructor
  · simp [publishGrowing,source_c2_is_the_concrete_uniform_command,a]
  · simp [publishGrowing,second_forward_c2_keeps_the_concrete_star_command,b]

theorem both_backward_calls_publish_their_concrete_protected_cuts
    (run n : Nat) (may : Bool) :
    publishGrowing run (n+3) true (bRow n may) ProtectedCleanerGrowth.sink = [bEdge n] ∧
    publishGrowing run (n+3) true (bRow n may) (bOffer1 n) = [bEdge2 n] := by
  rcases all_four_edges_are_generated_by_the_actual_growing_branch n may with ⟨_,_,a,b⟩
  constructor
  · simp [publishGrowing,first_backward_c2_keeps_the_concrete_star_command,a]
  · simp [publishGrowing,second_backward_c2_keeps_the_concrete_star_command,b]

/-- Concrete diagonal relation, with the native independent-NE matching
    cases from the earlier counterexample. The full-mark gate is explicit. -/
def bindCut (edge : Edge) (actual : Offered) : Option Offered :=
  if edge.1.mark == some t && edge.2.ap.mark == some t && actual.ap.mark == some t
  then bindIndependentNE edge actual else none

theorem forward_actuals_really_link_call1_to_call2_and_the_sink (n : Nat) :
    (bindCut (fEdge n) ProtectedCleanerGrowth.source).map bindArgument = some (fOffer2 n) ∧
    bindCut (fEdge2 n) (fOffer2 n) = some ⟨full ret (n+2) .ne,true⟩ := by
  constructor
  · simp [bindCut,bindIndependentNE,fEdge,fQ,ProtectedCleanerGrowth.source,
      fOffer2,bindArgument,ProtectedCleanerGrowth.full,data,ap,fields_step,dropHead]
  · simp [bindCut,bindIndependentNE,fEdge2,fQ2,fOffer2,ProtectedCleanerGrowth.full,data,ap,drop_same_fields]

theorem backward_actuals_really_link_call2_to_call1_and_the_source (n : Nat) :
    (bindCut (bEdge n) ProtectedCleanerGrowth.sink).map bindReturn = some (bOffer1 n) ∧
    bindCut (bEdge2 n) (bOffer1 n) = some ⟨full p (n+3) .ne,true⟩ := by
  constructor
  · simp [bindCut,bindIndependentNE,bEdge,bQ,ProtectedCleanerGrowth.sink,
      bOffer1,bindReturn,ProtectedCleanerGrowth.full,data,ap,fields_step,dropHead]
  · simp [bindCut,bindIndependentNE,bEdge2,bQ2,bOffer1,ProtectedCleanerGrowth.full,data,ap,drop_same_fields]

theorem each_handoff_supplies_the_next_opposite_paired_row (n : Nat) :
    (⟨(fEdge2 n).2.ap,(fEdge2 n).1⟩ : Row) = bRow n ∧
    (⟨(bEdge2 n).2.ap,(bEdge2 n).1⟩ : Row) = fRow (n+2) := by
  constructor <;> rfl

def forwardCertificate (run n : Nat) (may : Bool := false) : Bool :=
  (publishGrowing run (n+2) false (fRow n may) ProtectedCleanerGrowth.source).any fun edge =>
    ((bindCut edge ProtectedCleanerGrowth.source).map bindArgument).any fun offered =>
      (publishGrowing run (n+2) false (fRow n may) offered).any fun second =>
        decide (second = fEdge2 n) && (bindCut second offered).any demandSink

def backwardCertificate (run n : Nat) (may : Bool := false) : Bool :=
  (publishGrowing run (n+3) true (bRow n may) ProtectedCleanerGrowth.sink).any fun edge =>
    ((bindCut edge ProtectedCleanerGrowth.sink).map bindReturn).any fun offered =>
      (publishGrowing run (n+3) true (bRow n may) offered).any fun first =>
        decide (first = bEdge2 n) && (bindCut first offered).any sourcePermission

theorem every_forward_pair_reaches_a_demand_sink (run n : Nat) (may : Bool) :
    forwardCertificate run n may = true := by
  unfold forwardCertificate
  rcases both_forward_calls_publish_their_concrete_protected_cuts run n may with ⟨a,b⟩
  rcases forward_actuals_really_link_call1_to_call2_and_the_sink n with ⟨c,d⟩
  rw [a]
  simp only [List.any_cons,List.any_nil,Bool.or_false,c,Option.any_some,b]
  simp only [List.any_cons,List.any_nil,Bool.or_false,decide_true,Bool.true_and,d,Option.any_some]
  rfl

theorem every_backward_pair_renews_the_real_source (run n : Nat) (may : Bool) :
    backwardCertificate run n may = true := by
  unfold backwardCertificate
  rcases both_backward_calls_publish_their_concrete_protected_cuts run n may with ⟨a,b⟩
  rcases backward_actuals_really_link_call2_to_call1_and_the_source n with ⟨c,d⟩
  rw [a]
  simp only [List.any_cons,List.any_nil,Bool.or_false,c,Option.any_some,b]
  simp only [List.any_cons,List.any_nil,Bool.or_false,decide_true,Bool.true_and,d,Option.any_some]
  rfl

def run1Seed : Value := val (full p 0 .star) true
def run1Writer : Option Value := (cleanEntry run1Seed).map (growTwice 1 ret)
def run1WriterEdge : Edge := (run1Seed.ap,⟨full ret 1 .ne,true,true⟩)
def run1MayEdge : Edge := (run1Seed.ap,⟨full ret 0 .may,true,true⟩)
def bootstrapRow : Row := ⟨full ret 1 .ne,full p 0 .star⟩
def bootstrapQuery : Seed := ⟨full ret 1 .star,true⟩
def bootstrapEdge : Edge := (bootstrapQuery.ap,⟨full p 1 .ne,true,true⟩)

theorem the_run1_request_answer_is_not_a_must_initial :
    run1Seed.ap.tail = .star ∧ run1Seed.ap.mark = some t ∧ run1Seed.demand = true ∧
    cleanEntry run1Seed = some ⟨full p 0 .may,true,true⟩ := by decide

theorem run1_really_generates_the_protected_field_cut :
    run1Writer = some run1WriterEdge.2 := by decide

/-- Two ordinary reads of the MAY survivor produce the caller-visible
    root MAY result. This is not a pass rule or a predefined summary. -/
def readOne (fromBase toBase : Nat) (c : Value) : Option Value :=
  (moveE fromBase toBase [f] [] c.ap).map fun result =>
    {result with demand := c.demand || result.demand,h := c.h}

def readingSummary (limit : Nat) (row : Row) (q : Seed) : Option Edge := do
  let start ← cleanEntry ⟨q.ap,q.demand,false⟩
  let middle ← readOne p 17 start
  let result ← readOne 17 ret middle
  restricted limit [q] q result row

def normalReader3 : Edge := ((fQ 0).ap,⟨full ret 1 .must,false,true⟩)

theorem run3_has_a_normal_concrete_reader_with_the_same_original :
    readingSummary 2 (fRow 0) (fQ 0) = some normalReader3 ∧
    normalReader3.1 = (fEdge 0).1 ∧ normalReader3.2.h = (fEdge 0).2.h := by decide

theorem the_normal_concrete_reader_does_not_qualify_as_uniform_flow_cover :
    uniformCovers normalReader3 (fEdge 0) = false := by decide

def applyConcreteUniform (edge : Edge) (actual : Offered) : Option Offered :=
  if !edge.2.demand && edge.1.tail == .must && actual.ap.tail == .must &&
      edge.1.mark == some t && edge.2.ap.mark == some t && actual.ap.mark == some t &&
      (dropHead actual.ap.path edge.1.path).isSome then
    some ⟨edge.2.ap,actual.demand⟩ else none

theorem the_sink_can_already_have_a_normal_witness_in_run3 :
    (((applyConcreteUniform normalReader3 ProtectedCleanerGrowth.source).map bindArgument).bind
      (applyConcreteUniform normalReader3)) = some ⟨full ret 1 .must,false⟩ := by decide
def run1Reader : Option Value := do
  let input ← cleanEntry run1Seed
  let middle ← readOne p 17 input
  readOne 17 ret middle

theorem run1_really_generates_its_caller_visible_may :
    run1Reader = some run1MayEdge.2 ∧
    (((applyLoss run1MayEdge ProtectedCleanerGrowth.source).map bindArgument).bind
      (applyLoss run1MayEdge)) = some ProtectedCleanerGrowth.sink := by decide

theorem run2_constructs_the_run3_paired_row :
    recurringCommands 2 1 true bootstrapRow ProtectedCleanerGrowth.sink = [bootstrapQuery] ∧
    growingSummary 1 true bootstrapRow bootstrapQuery = some bootstrapEdge ∧
    (⟨bootstrapEdge.2.ap,bootstrapEdge.1⟩ : Row) = fRow 0 := by decide

def bootstrapMayEdge : Edge := (bootstrapQuery.ap,⟨full p 0 .may,true,true⟩)
def run2OtherBranch : Option Edge := do
  let start : Value := ⟨bootstrapQuery.ap,bootstrapQuery.demand,false⟩
  let middle ← readOne ret 17 start
  let atEntry ← readOne 17 p middle
  let after ← cleanEntry atEntry
  restricted 1 [bootstrapQuery] bootstrapQuery after bootstrapRow

theorem run2_really_renews_source_permission_at_the_bootstrap :
    run2OtherBranch = some bootstrapMayEdge ∧
    ((((applyLoss bootstrapMayEdge ProtectedCleanerGrowth.sink).map bindReturn).bind
      (applyLoss bootstrapMayEdge)).any sourcePermission) = true := by decide

def bootstrap : Bool :=
  run1Writer == some run1WriterEdge.2 && run1Reader == some run1MayEdge.2 &&
    growingSummary 1 true bootstrapRow bootstrapQuery == some bootstrapEdge &&
    run2OtherBranch == some bootstrapMayEdge

theorem the_bootstrap_is_computed_from_rules_and_micro_operations : bootstrap = true := by decide

/-- Recurrence starts at run-3/limit 2 and advances two field levels per
    forward/backward pair. No test or production iteration ceiling occurs. -/
def forwardRounds (mayFlags : Nat → Bool) : Nat → Bool
  | 0 => bootstrap && forwardCertificate 3 0 (mayFlags 3)
  | k+1 => forwardRounds mayFlags k && backwardCertificate (2*k+4) (2*k) (mayFlags (2*k+4)) &&
      forwardCertificate (2*k+5) (2*k+2) (mayFlags (2*k+5))

theorem every_forward_round_has_fresh_demand (mayFlags : Nat → Bool) (k : Nat) :
    forwardRounds mayFlags k = true := by
  induction k with
  | zero => rw [forwardRounds,the_bootstrap_is_computed_from_rules_and_micro_operations,every_forward_pair_reaches_a_demand_sink];rfl
  | succ k ih => rw [forwardRounds,ih,every_backward_pair_renews_the_real_source,every_forward_pair_reaches_a_demand_sink];rfl

def rootHandoff (mayFlags : Nat → Bool) (k : Nat) : List RootEdge :=
  if forwardRounds mayFlags k then (rootC5 repeatedTarget).toList else []

theorem the_literal_same_zero_to_target_repeats_forever (mayFlags : Nat → Bool) (k : Nat) :
    rootHandoff mayFlags k = [repeatedTarget] := by
  rw [rootHandoff,every_forward_round_has_fresh_demand]
  rfl

theorem run3_and_every_later_forward_have_nonempty_demand (mayFlags : Nat → Bool) (k : Nat) :
    (rootHandoff mayFlags k).isEmpty = false := by
  rw [the_literal_same_zero_to_target_repeats_forever]
  rfl

theorem a_normal_finding_does_not_make_this_demand_target_normal :
    repeatedTarget.demand = true := rfl

end ProtectedCleanerCycle

#print axioms ProtectedCleanerCycle.both_forward_calls_publish_their_concrete_protected_cuts
#print axioms ProtectedCleanerCycle.both_backward_calls_publish_their_concrete_protected_cuts
#print axioms ProtectedCleanerCycle.forward_actuals_really_link_call1_to_call2_and_the_sink
#print axioms ProtectedCleanerCycle.backward_actuals_really_link_call2_to_call1_and_the_source
#print axioms ProtectedCleanerCycle.each_handoff_supplies_the_next_opposite_paired_row
#print axioms ProtectedCleanerCycle.every_forward_pair_reaches_a_demand_sink
#print axioms ProtectedCleanerCycle.every_backward_pair_renews_the_real_source
#print axioms ProtectedCleanerCycle.the_run1_request_answer_is_not_a_must_initial
#print axioms ProtectedCleanerCycle.run1_really_generates_the_protected_field_cut
#print axioms ProtectedCleanerCycle.run1_really_generates_its_caller_visible_may
#print axioms ProtectedCleanerCycle.run3_has_a_normal_concrete_reader_with_the_same_original
#print axioms ProtectedCleanerCycle.the_normal_concrete_reader_does_not_qualify_as_uniform_flow_cover
#print axioms ProtectedCleanerCycle.the_sink_can_already_have_a_normal_witness_in_run3
#print axioms ProtectedCleanerCycle.run2_constructs_the_run3_paired_row
#print axioms ProtectedCleanerCycle.run2_really_renews_source_permission_at_the_bootstrap
#print axioms ProtectedCleanerCycle.the_bootstrap_is_computed_from_rules_and_micro_operations
#print axioms ProtectedCleanerCycle.every_forward_round_has_fresh_demand
#print axioms ProtectedCleanerCycle.the_literal_same_zero_to_target_repeats_forever
#print axioms ProtectedCleanerCycle.run3_and_every_later_forward_have_nonempty_demand
#print axioms ProtectedCleanerCycle.a_normal_finding_does_not_make_this_demand_target_normal
