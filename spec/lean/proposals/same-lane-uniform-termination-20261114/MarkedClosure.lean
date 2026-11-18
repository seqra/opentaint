import UniformService

/- Complete C2 families, FLOW/mx and concrete/H lanes for the current
   acyclic cleaner helper. Every raw body output goes through its own C5.
   Candidate ordering is deliberate: stage ready NORMAL outputs before
   publishing the packet or testing its relative-cut duplicates. -/
namespace SameLaneMarkedClosure
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline BoundedLocalRouting BoundedOrdinaryCycle
open NormalUniformNE ProtectedCleanerGrowth ProtectedCleanerCycle
open SameLaneUniform
set_option linter.unusedSimpArgs false

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def clean (c : Value) : Option Value :=
  if c.ap.mark.isNone then
    some {c with ap := {c.ap with mx := if c.ap.mx.contains t then c.ap.mx else c.ap.mx ++ [t]}}
  else cleanEntry c

def supportedMove (command : Command) (input : Value) (fromBase toBase : Nat)
    (read write : Path) : Option Value :=
  (routedMove {command with seed := ⟨input.ap,input.demand⟩} fromBase toBase read write).map fun result =>
    {result with demand := input.demand || result.demand,h := input.h}

def body (limit : Nat) (backward : Bool) (command : Command) : List Value :=
  let input : Value := ⟨command.seed.ap,command.seed.demand,false⟩
  if backward then
    ([some (growTwice limit p input),
      supportedMove command input ret p [f,f] []].filterMap id).filterMap clean ++ [input]
  else match clean input with
    | none => []
    | some marked =>
        [supportedMove command marked p ret [f,f] [],
         some (growTwice limit ret marked),some marked].filterMap id

def flowStart : Command := ⟨⟨data p 0 .star,false⟩,[]⟩
def taintStart : Command := ⟨⟨ProtectedCleanerGrowth.full p 0 .star,true⟩,[]⟩
def run1All : List Edge :=
  [flowStart,taintStart].flatMap fun q =>
    (body 1 false q).map fun raw => normalize q.seed.ap raw

def guidance (a : Ap) : Ap :=
  {a with tail := if a.tail == .must then .may else a.tail,mx := []}

def incoming (all : List Edge) : List Row :=
  (all.filterMap fun e => if e.2.demand then
    some ⟨guidance e.2.ap,guidance e.1⟩ else none).eraseDups

def rows2 := incoming run1All
def sinkOffer : Offered := ⟨ProtectedCleanerGrowth.full ret 0 .may,true⟩

def candidates (run limit : Nat) (backward : Bool) (rows : List Row)
    (actuals : List Offered) : List Edge :=
  (actuals.flatMap fun actual => rows.flatMap fun row =>
    let commands := plan run limit backward row actual
    let keys := commands.map Command.seed
    commands.flatMap fun command =>
      (body limit backward command).filterMap fun raw =>
        restricted limit keys command.seed raw row).eraseDups

def packet2 := candidates 2 1 true rows2 [sinkOffer]
def rows3 := incoming packet2
def sourceOffer : Offered := ⟨ProtectedCleanerGrowth.full p 0 .must,false⟩

def reverseReturnedOffers : List Offered :=
  [sinkOffer,⟨ProtectedCleanerGrowth.full ret 1 .ne,true⟩]

theorem the_second_reverse_call_adds_no_missing_paired_row :
    candidates 2 1 true rows2 reverseReturnedOffers = packet2 := by decide

def packet3 (actuals : List Offered) := candidates 3 2 false rows3 actuals
def coldAll := packet3 [sourceOffer]
def coldNormal := coldAll.filter fun e => !e.2.demand
def coldDemand := coldAll.filter fun e => e.2.demand
def coldBasis := SameLaneUniform.compact true coldAll

theorem run1_has_both_taint_and_excluded_flow_field_heads :
    run1All.any (fun e => e.2.demand && e.2.ap.tail == .ne && e.2.ap.mark == some t && e.2.h) = true ∧
    run1All.any (fun e => e.2.demand && e.2.ap.tail == .ne && e.2.ap.mark.isNone && e.2.ap.mx.contains t) = true := by decide

theorem backward_bootstrap_has_concrete_and_flow_paired_rows :
    rows3.any (fun row => row.entry.mark == some t) = true ∧
    rows3.any (fun row => row.entry.mark.isNone) = true ∧
    rows3.all (fun row => row.entry.base == p && row.exit.base == ret) = true := by decide

theorem the_complete_cold_source_packet_has_only_uniform_raw_initials :
    (rows3.flatMap fun row => (plan 3 2 false row sourceOffer).map Command.seed).all
      (fun q => q.ap.tail == .must) = true := by decide

theorem the_cold_packet_contains_both_concrete_and_excluded_flow_demand :
    coldDemand.any (fun e => e.2.ap.mark == some t && e.2.h) = true ∧
    coldDemand.any (fun e => e.2.ap.mark.isNone && e.2.ap.mx.contains t) = true := by decide

theorem the_extended_law_removes_all_cold_demand_not_just_the_four_witnesses :
    coldBasis.any (fun e => e.2.demand) = false ∧ coldBasis.isEmpty = false := by decide

def normalApply (record : Edge) (input : Value) : Option Value := do
  if record.2.demand || !marksOK record.1 input.ap then none else
  if record.2.ap.mark.isNone && input.ap.mark == some t && record.2.ap.mx.contains t then none else
  if record.1.tail == .must then
    if input.ap.tail != .must || !(dropHead input.ap.path record.1.path).isSome then none else
    some {record.2 with
      ap := {record.2.ap with mark := input.ap.mark}
      demand := input.demand
      h := input.h || record.2.h}
  else if record.1.tail == .star && record.2.ap.tail == .star then
    let result ← moveE record.1.base record.2.ap.base record.1.path record.2.ap.path input.ap
    some {result with
      ap := {result.ap with mx := input.ap.mx ++ record.2.ap.mx}
      demand := input.demand || result.demand
      h := input.h || record.2.h}
  else none

def actualCovers (whole child : Value) : Bool :=
  whole.ap.base == child.ap.base && decide (whole.ap.mark = child.ap.mark) &&
    whole.ap.mx == child.ap.mx && whole.demand == child.demand && whole.h == child.h &&
    whole.ap.tail == .must && child.ap.tail == .must &&
    (dropHead whole.ap.path child.ap.path).isSome

def canonicalActuals (all : List Value) : List Value :=
  (all.filter fun child => !(all.any fun whole =>
    decide (whole.ap ≠ child.ap) && actualCovers whole child)).eraseDups

def replies (all : List Edge) (input : Value) : List Value :=
  canonicalActuals (all.filterMap fun e => normalApply e input)

def firstReplies := replies coldBasis ⟨sourceOffer.ap,false,false⟩
def secondOffers : List Offered := firstReplies.map fun c => ⟨{c.ap with base := p},c.demand⟩

theorem exact_normal_results_are_not_hidden_by_the_uniform_actual_filter :
    firstReplies.any (fun c => c.ap.tail == .exact && !c.demand) = true ∧
    firstReplies.any (fun c => c.ap.tail == .must && !c.demand) = true := by decide

theorem exact_replies_create_a_real_extra_c2_family :
    (secondOffers.flatMap fun offered => rows3.flatMap fun row =>
      (plan 3 2 false row offered).map Command.seed).any
      (fun q => q.ap.tail == .exact && q.ap.mark.isNone) = true := by decide

def expandedAll := packet3 (sourceOffer :: secondOffers)
def expandedBasis := SameLaneUniform.compact true expandedAll

-- This declaration is a diagnostic check, not the final algorithm's theorem.
def extraStarDemand := expandedBasis.filter fun e => e.2.demand && e.1.tail == .star

def bind (v : Value) : Value := {v with ap := {v.ap with base := p}}
def secondReplies := canonicalActuals (firstReplies.flatMap fun a => replies expandedBasis (bind a))
def closedOffers : List Offered :=
  sourceOffer :: (secondReplies.map fun c => ⟨{c.ap with base := p},c.demand⟩)
def closedPacket := SameLaneUniform.compact true (packet3 closedOffers)

theorem the_extra_exact_family_adds_a_normal_flow_record_but_no_demand :
    expandedAll.length = 16 ∧ expandedBasis.length = 11 ∧
    expandedBasis.any (fun e => e.2.demand) = false ∧
    expandedBasis.any (fun e => e.1.tail == .star && e.1.mark.isNone &&
      e.2.ap.path.length == 2 && e.2.ap.mx == [t]) = true := by decide

theorem both_call_sites_have_the_same_complete_actual_basis :
    secondReplies = firstReplies ∧
    firstReplies = [⟨ProtectedCleanerGrowth.full ret 0 .exact,false,true⟩,
      ⟨ProtectedCleanerGrowth.full ret 0 .must,false,true⟩] := by decide

theorem the_entire_new_frontier_is_empty_at_the_within_run_fixed_point :
    closedPacket = expandedBasis ∧ incoming closedPacket = [] ∧
    secondReplies.any Value.demand = false ∧
    secondReplies.any (fun c => c.ap.mark == some t && c.ap.tail == .must && !c.demand) = true := by decide

def nextCohort (basis : List Edge) : List Edge :=
  let returned := replies basis ⟨sourceOffer.ap,false,false⟩
  let offers : List Offered := sourceOffer :: returned.map fun c => ⟨{c.ap with base := p},c.demand⟩
  SameLaneUniform.compact true (packet3 offers)

theorem closing_the_cold_cohort_adds_only_the_one_ready_normal_row :
    coldAll.length = 15 ∧ coldBasis.length = 10 ∧
    nextCohort coldBasis = expandedBasis := by decide

theorem another_complete_c2_body_c5_delivery_round_changes_nothing :
    nextCohort expandedBasis = expandedBasis := by decide

def rounds : Nat → List Edge
  | 0 => coldBasis
  | n+1 => nextCohort (rounds n)

theorem no_later_closure_round_can_recreate_the_cycle (n : Nat) :
    rounds (n+1) = expandedBasis := by
  induction n with
  | zero => exact closing_the_cold_cohort_adds_only_the_one_ready_normal_row.2.2
  | succ n ih =>
    change nextCohort (rounds (n+1)) = expandedBasis
    rw [ih]
    exact another_complete_c2_body_c5_delivery_round_changes_nothing

theorem every_later_closure_round_has_no_handoff (n : Nat) :
    incoming (rounds (n+1)) = [] := by
  rw [no_later_closure_round_can_recreate_the_cycle]
  exact the_entire_new_frontier_is_empty_at_the_within_run_fixed_point.2.1

theorem no_provider_loses_its_literal_protection_or_mark_exclusion :
    (expandedBasis.filter fun e => e.2.ap.mark == some t).all (fun e => e.2.h) = true ∧
    (expandedBasis.filter fun e => e.2.ap.mark.isNone).all
      (fun e => e.2.ap.mx.contains t) = true := by decide

theorem excluded_flow_cannot_supply_a_spurious_t_to_either_caller :
    (expandedBasis.filter fun e => e.2.ap.mark.isNone).all
      (fun e => (normalApply e ⟨sourceOffer.ap,false,false⟩).isNone) = true := by decide

end SameLaneMarkedClosure

#print axioms SameLaneMarkedClosure.run1_has_both_taint_and_excluded_flow_field_heads
#print axioms SameLaneMarkedClosure.the_second_reverse_call_adds_no_missing_paired_row
#print axioms SameLaneMarkedClosure.backward_bootstrap_has_concrete_and_flow_paired_rows
#print axioms SameLaneMarkedClosure.the_complete_cold_source_packet_has_only_uniform_raw_initials
#print axioms SameLaneMarkedClosure.the_cold_packet_contains_both_concrete_and_excluded_flow_demand
#print axioms SameLaneMarkedClosure.the_extended_law_removes_all_cold_demand_not_just_the_four_witnesses
#print axioms SameLaneMarkedClosure.exact_normal_results_are_not_hidden_by_the_uniform_actual_filter
#print axioms SameLaneMarkedClosure.exact_replies_create_a_real_extra_c2_family
#print axioms SameLaneMarkedClosure.the_extra_exact_family_adds_a_normal_flow_record_but_no_demand
#print axioms SameLaneMarkedClosure.both_call_sites_have_the_same_complete_actual_basis
#print axioms SameLaneMarkedClosure.the_entire_new_frontier_is_empty_at_the_within_run_fixed_point
#print axioms SameLaneMarkedClosure.closing_the_cold_cohort_adds_only_the_one_ready_normal_row
#print axioms SameLaneMarkedClosure.another_complete_c2_body_c5_delivery_round_changes_nothing
#print axioms SameLaneMarkedClosure.no_later_closure_round_can_recreate_the_cycle
#print axioms SameLaneMarkedClosure.every_later_closure_round_has_no_handoff
#print axioms SameLaneMarkedClosure.no_provider_loses_its_literal_protection_or_mark_exclusion
#print axioms SameLaneMarkedClosure.excluded_flow_cannot_supply_a_spurious_t_to_either_caller
