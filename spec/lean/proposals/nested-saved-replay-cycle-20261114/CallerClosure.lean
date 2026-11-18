import ColdCertificates

/- Caller closure of the synthetic three-call program. The NORMAL records
   are those derived in ColdCertificates, not supplied method models. -/
namespace NestedCallerClosure
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open NormalUniformNE NestedSavedReplayCycle NestedColdMachine NestedColdCertificates
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def retainedRead : Edge := (point p [f,f] .star,val (point ret [] .star))
def retainedWrite : Edge := (point p [] .star,val (point ret [f,f] .star))
def unresolved : Edge := (point p [] .star,val (point ret [] .may) true)
def packet (a : Offered) : List Offered :=
  values ([retainedRead,retainedWrite,unresolved].filterMap fun e => applyEdge true e a)
def deliver (actuals : List Offered) : List Offered := values (actuals.flatMap packet)
def first : List Offered := deliver [NestedSavedReplayCycle.source 0]
def second : List Offered := deliver first
def third : List Offered := deliver second

theorem complete_forward_packets_retain_the_precise_and_unresolved_routes :
    first = values [NestedSavedReplayCycle.source 1,need] ∧
    second = values [NestedSavedReplayCycle.source 0,NestedSavedReplayCycle.source 2,need] ∧
    third = values [NestedSavedReplayCycle.source 1,NestedSavedReplayCycle.source 3,need] := by decide

theorem forward_caller_domains_are_exactly_those_in_the_packet_proof :
    unique valueKey ([NestedSavedReplayCycle.source 0] ++ first ++ second) =
      unique valueKey domainF := by decide

theorem reversed_three_calls_reach_the_real_mark_producer :
    packet need = [need] ∧ deliver (deliver (deliver [need])) = [need] ∧
    admits need.ap.tail need.ap.e [f,g] = true ∧ need.ap.mark = some t := by decide

theorem normal_and_demand_observations_coexist :
    third.any Offered.demand = true ∧
    third.any (fun a => !a.demand && a.ap.mark == some t && a.ap.tail == .must) = true := by decide

theorem no_packet_fact_exceeds_eight_fields :
    (domainF.flatMap packet).all (fun a => decide (a.ap.path.length ≤ 8)) = true := by decide

theorem every_later_global_limit_keeps_each_packet_fact (n : Nat)
    (a : Offered) (ha : a ∈ domainF.flatMap packet) : cutOffer (n+8) a = a := by
  have bound : a.ap.path.length ≤ 8 := by
    exact of_decide_eq_true (List.all_eq_true.mp no_packet_fact_exceeds_eight_fields a ha)
  have within : ¬n+8 < a.ap.path.length := by omega
  cases a
  simp [cutOffer,cut,within,val]

theorem finite_packet_is_the_actual_complete_forward_offer :
    domainF.all (fun a => decide (packet a =
      offer 9 8 (rows8[0]!) (saved8[0]!) parentPubs a)) = true := by decide

theorem finite_packet_is_the_actual_complete_backward_offer :
    packet need = offer 10 9 (rows9[0]!) (saved9[0]!) parentPubs need := by decide

theorem root_admission_remains_nonempty_at_every_later_limit (n : Nat) :
    domainF.all (fun a => !((prepared (n+9) (n+8)
      ⟨inputSelector [],outputSelector []⟩ a).isEmpty)) = true := by
  have row : (⟨inputSelector [],outputSelector []⟩ : Row) ∈ stableRows := by simp [stableRows]
  apply List.all_eq_true.mpr
  intro a ha
  rw [prepared_stable n _ a row ha]
  have h : domainF.all (fun a => !(prepared 9 8
      ⟨inputSelector [],outputSelector []⟩ a).isEmpty) = true := by decide
  exact List.all_eq_true.mp h a ha

theorem no_submitted_initial_requires_a_new_mark_or_tail :
    (state9.domains[1]!).all (fun a => a.ap.mark.isNone &&
      (a.ap.tail == .exact || a.ap.tail == .star)) = true := by decide

end NestedCallerClosure

#print axioms NestedCallerClosure.complete_forward_packets_retain_the_precise_and_unresolved_routes
#print axioms NestedCallerClosure.forward_caller_domains_are_exactly_those_in_the_packet_proof
#print axioms NestedCallerClosure.reversed_three_calls_reach_the_real_mark_producer
#print axioms NestedCallerClosure.normal_and_demand_observations_coexist
#print axioms NestedCallerClosure.no_packet_fact_exceeds_eight_fields
#print axioms NestedCallerClosure.every_later_global_limit_keeps_each_packet_fact
#print axioms NestedCallerClosure.finite_packet_is_the_actual_complete_forward_offer
#print axioms NestedCallerClosure.finite_packet_is_the_actual_complete_backward_offer
#print axioms NestedCallerClosure.root_admission_remains_nonempty_at_every_later_limit
#print axioms NestedCallerClosure.no_submitted_initial_requires_a_new_mark_or_tail
