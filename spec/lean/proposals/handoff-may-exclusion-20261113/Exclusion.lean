import Cycle

/- Counterexample to removing a whole field branch from a MAY demand merely
   because a same-premise NE child row exists. No production change.
   The candidate's new descendant exclusion guard is modeled only for the
   reached cell; this is not a complete new C2 implementation. -/
namespace HandoffMayExclusion
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle

def h : Nat := 3
def temp : Nat := 2
def broad : Ap := ap ret [] .may
def narrow : Ap := ap ret [f] .ne
def need : Offered := ⟨ap ret [f] .exact (some t),false⟩
def pair : Row := ⟨broad,ap p [] .star⟩

/-- First-accessor exclusion is anchored at the broad demand's head.
    It must not be copied to a refined child's different coordinate. -/
def excludedDescendant (excluded : List Nat) (d : Ap) (a : Offered) : Bool :=
  match dropHead d.path a.ap.path with
  | some (field :: _) => excluded.contains field
  | _ => false

def candidate (run limit : Nat) (d : Ap) (excluded : List Nat)
    (a : Offered) : List Seed :=
  if excludedDescendant excluded d a then []
  else emit run limit true d a

def branchAllowed (excluded : Nat) (path : Path) : Prop :=
  match path with
  | [] => True
  | field :: _ => field ≠ excluded

def childMay (field : Nat) (path : Path) : Prop :=
  ∃ suffix : Path, path = field :: suffix
def childNe (field : Nat) (path : Path) : Prop :=
  ∃ suffix : Path, path = field :: suffix ∧ suffix ≠ []

theorem full_child_partition_is_exact (field : Nat) (path : Path) :
    branchAllowed field path ∨ childMay field path := by
  cases path with
  | nil => exact Or.inl True.intro
  | cons head rest =>
    by_cases same : head = field
    · subst head; exact Or.inr ⟨rest,rfl⟩
    · exact Or.inl same

theorem ne_child_does_not_cover_the_removed_field_point (field : Nat) :
    ¬ branchAllowed field [field] ∧ ¬ childNe field [field] := by
  constructor
  · intro impossible; exact impossible rfl
  · rintro ⟨suffix,same,nonempty⟩
    have empty : suffix = [] := List.cons.inj same |>.2.symm
    exact nonempty empty

theorem exact_child_does_not_cover_a_removed_descendant :
    ¬ branchAllowed f [f,h] ∧ [f,h] ≠ [f] := by
  constructor
  · intro impossible; exact impossible rfl
  · decide

def correlatedChild (input output : Path) : Prop := output = f :: input
theorem child_star_is_not_an_independent_full_child_relation :
    childMay f [f] ∧ ¬ correlatedChild [g] [f] := by
  exact ⟨⟨[],rfl⟩,by intro impossible; cases impossible⟩

theorem ordinary_code_produces_the_broad_row :
    move p ret [g] [] (ap p [] .star) = some (val broad true) := by decide

def firstWrite : Option Value := move p temp [] [h] (ap p [] .star)
def secondWrite : Option Value := firstWrite.bind fun value =>
  move temp ret [] [f] value.ap

theorem ordinary_writes_produce_the_child_cut :
    firstWrite = some (val (ap temp [h] .star)) ∧
    secondWrite = some (val (ap ret [f,h] .star)) ∧
    (secondWrite.map (cut 1)) = some (val narrow true) := by decide

theorem complete_forward_return_family_has_no_normal_provider :
    [move p ret [g] [] (ap p [] .star), secondWrite.map (cut 1)].filterMap id =
      [val broad true,val narrow true] := by decide

theorem both_conclusions_have_the_same_original :
    let original := ap p [] .star
    (original,val broad true).1 = (original,val narrow true).1 := rfl

theorem baseline_admits_the_required_point_and_structural_probe :
    emit 2 1 true broad need =
      [⟨ap ret [f] .exact,false⟩,⟨ap ret [] .exact,false⟩] := by decide

theorem excluded_broad_demand_rejects_the_required_point :
    candidate 2 1 broad [f] need = [] := by decide

theorem kept_ne_child_also_rejects_the_required_point :
    emit 2 1 true narrow need = [] := by decide

theorem candidate_union_has_no_initial :
    candidate 2 1 broad [f] need ++ emit 2 1 true narrow need = [] := by decide

theorem previous_cycle_uniform_offer_uses_the_dedicated_child_query :
    emit 3 2 false (ap p [f] .ne) source = [⟨ap p [f] .must,false⟩] := by decide

theorem previous_cycle_uncertain_offer_still_starts_star :
    emit 3 2 false (ap p [f] .ne) ⟨ap p [f] .ne (some t),true⟩ =
      [⟨ap p [f] .star,false⟩] := by decide

theorem reversed_read_from_the_probe_is_precise :
    move ret p [] [g] (ap ret [] .exact) = some (val (ap p [g] .exact)) := by decide

theorem baseline_probe_publishes_the_normal_provider :
    restrictOne 2 1 true [need] (ap ret [] .exact)
      (val (ap p [g] .exact)) pair =
        some (ap ret [] .star,val (ap p [g] .star)) := by decide

def actualSource : Offered := ⟨ap p [g] .must (some t),false⟩
theorem retained_provider_reaches_the_real_marked_result :
    move p ret [g] [] actualSource.ap =
      some (val (ap ret [] .must (some t))) := by decide

theorem that_uniform_result_includes_the_sink_point :
    admits .must [] [f] = true := by decide

theorem retaining_point_permission_is_possible_in_the_existing_grammar :
    emit 2 1 true (ap ret [f] .may) need = [⟨ap ret [f] .exact,false⟩] ∧
    emit 2 1 true (ap ret [f] .star) need = [⟨ap ret [f] .exact,false⟩] := by decide

end HandoffMayExclusion

#print axioms HandoffMayExclusion.full_child_partition_is_exact
#print axioms HandoffMayExclusion.ne_child_does_not_cover_the_removed_field_point
#print axioms HandoffMayExclusion.exact_child_does_not_cover_a_removed_descendant
#print axioms HandoffMayExclusion.child_star_is_not_an_independent_full_child_relation
#print axioms HandoffMayExclusion.ordinary_code_produces_the_broad_row
#print axioms HandoffMayExclusion.ordinary_writes_produce_the_child_cut
#print axioms HandoffMayExclusion.complete_forward_return_family_has_no_normal_provider
#print axioms HandoffMayExclusion.both_conclusions_have_the_same_original
#print axioms HandoffMayExclusion.baseline_admits_the_required_point_and_structural_probe
#print axioms HandoffMayExclusion.excluded_broad_demand_rejects_the_required_point
#print axioms HandoffMayExclusion.kept_ne_child_also_rejects_the_required_point
#print axioms HandoffMayExclusion.candidate_union_has_no_initial
#print axioms HandoffMayExclusion.previous_cycle_uniform_offer_uses_the_dedicated_child_query
#print axioms HandoffMayExclusion.previous_cycle_uncertain_offer_still_starts_star
#print axioms HandoffMayExclusion.reversed_read_from_the_probe_is_precise
#print axioms HandoffMayExclusion.baseline_probe_publishes_the_normal_provider
#print axioms HandoffMayExclusion.retained_provider_reaches_the_real_marked_result
#print axioms HandoffMayExclusion.that_uniform_result_includes_the_sink_point
#print axioms HandoffMayExclusion.retaining_point_permission_is_possible_in_the_existing_grammar
