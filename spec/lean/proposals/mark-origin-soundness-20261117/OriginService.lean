namespace OriginService
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

abbrev Graph:=List (Nat × Nat)

-- The same direction is used for both graphs: generator -> observation.
inductive Reaches (edges : Graph) (goal : Nat) : Nat → Prop
  | here : Reaches edges goal goal
  | step : (a,b)∈edges → Reaches edges goal b → Reaches edges goal a

def predecessors (edges : Graph) (seen : List Nat) : List Nat:=
  edges.flatMap fun (a,b)=>if b∈seen then [a] else []
def step (edges : Graph) (seen : List Nat) : List Nat:=
  (seen ++ predecessors edges seen).eraseDups
def close (edges : Graph) : Nat → List Nat → List Nat
  | 0,seen=>seen
  | n+1,seen=>close edges n (step edges seen)
def scan (edges : Graph) (goal : Nat) : List Nat:=close edges (edges.length+1) [goal]

def closed (edges : Graph) (goal : Nat) (seen : List Nat) : Bool:=
  decide (goal∈seen) && edges.all (fun (a,b)=>decide (b∉seen ∨ a∈seen))

theorem every_step_member_has_a_path_if_the_input_members_do
    (paths : ∀v∈seen, Reaches edges goal v) (present : v∈step edges seen) :
    Reaches edges goal v := by
  have member : v∈seen ++ predecessors edges seen:=List.mem_eraseDups.mp present
  rcases List.mem_append.mp member with old | fresh
  · exact paths v old
  · obtain ⟨pair,hpair,hv⟩:=List.mem_flatMap.mp fresh
    obtain ⟨a,b⟩:=pair
    by_cases hb : b∈seen
    · simp only [predecessors] at fresh
      simp only [hb,ite_true,List.mem_singleton] at hv
      subst v
      exact Reaches.step hpair (paths b hb)
    · simp only [hb,ite_false,List.not_mem_nil] at hv

theorem every_closure_member_has_a_path (n : Nat)
    (paths : ∀v∈seen, Reaches edges goal v) (present : v∈close edges n seen) :
    Reaches edges goal v := by
  induction n generalizing seen with
  | zero=>exact paths v present
  | succ n ih=>
    exact ih (fun w hw=>every_step_member_has_a_path_if_the_input_members_do paths hw) present

theorem a_normal_scan_never_invents_a_generator_to_observer_path
    (present : v∈scan normal goal) : Reaches normal goal v := by
  apply every_closure_member_has_a_path _ ?_ present
  intro w hw
  have same:=List.mem_singleton.mp hw
  subst w
  exact Reaches.here

theorem a_validated_upper_scan_contains_every_reachable_generator
    (passed : closed upper goal seen=true) (path : Reaches upper goal v) : v∈seen := by
  have halves:=Bool.and_eq_true_iff.mp passed
  induction path with
  | here=>exact of_decide_eq_true halves.1
  | step edge earlier ih=>
    have checked:=of_decide_eq_true ((List.all_eq_true.mp halves.2) _ edge)
    exact checked.resolve_left (fun absent=>absent ih)

-- Source nodes are distinct even if their emitted facts or report IDs are
-- equal. Both scans are temporary. The committed result is one goal bit.
def served (sources : List Nat) (upper normal : Graph) (goal : Nat)
    (complete : Bool) : Bool:=
  complete && closed upper goal (scan upper goal) &&
    sources.all (fun source=>decide (source∉scan upper goal ∨ source∈scan normal goal))

theorem every_served_possible_marking_point_has_a_NORMAL_witness
    (passed : served sources upper normal goal complete=true)
    (source : v∈sources) (possible : Reaches upper goal v) : Reaches normal goal v := by
  have halves:=Bool.and_eq_true_iff.mp passed
  have gates:=Bool.and_eq_true_iff.mp halves.1
  have reachable:=a_validated_upper_scan_contains_every_reachable_generator gates.2 possible
  have covered:=of_decide_eq_true ((List.all_eq_true.mp halves.2) v source)
  exact a_normal_scan_never_invents_a_generator_to_observer_path
    (covered.resolve_left (fun missing=>missing reachable))

theorem unknown_accounting_never_retires_a_goal :
    served sources upper normal goal false=false := by simp [served]

-- Refinement can add a NORMAL path. It cannot invalidate an existing one.
theorem service_is_stable_under_more_NORMAL_paths
    (sources : List Nat) (upper normal next : Graph) (goal : Nat)
    (servedPaths : ∀v∈sources, Reaches upper goal v → Reaches normal goal v)
    (grow : ∀a b, (a,b)∈normal → (a,b)∈next) :
    ∀v∈sources, Reaches upper goal v → Reaches next goal v := by
  have lift : ∀v, Reaches normal goal v → Reaches next goal v := by
    intro v path
    induction path with
    | here=>exact Reaches.here
    | step edge _ ih=>exact Reaches.step (grow _ _ edge) ih
  intro v hv hp
  exact lift v (servedPaths v hv hp)

-- This is the explicit abstraction boundary, not an axiom. The executable
-- adapters must prove their upper map and their NORMAL witness map.
theorem retirement_preserves_every_required_source_specific_relation
    (required retainedWitness : Nat → Prop)
    (passed : served sources upper normal goal complete=true)
    (catalogue : required source → source∈sources)
    (upperMap : required source → Reaches upper goal source)
    (normalMap : Reaches normal goal source → retainedWitness source)
    (needed : required source) : retainedWitness source :=
  normalMap (every_served_possible_marking_point_has_a_NORMAL_witness
    passed (catalogue needed) (upperMap needed))

def upperTwo : Graph:=[(0,2),(1,2)]
def earlyNormal : Graph:=[(0,2)]
def lateNormal : Graph:=[(0,2),(1,2)]
theorem two_sources_with_one_NORMAL_report_are_not_served :
    served [0,1] upperTwo earlyNormal 2 true=false := by decide
theorem both_distinct_NORMAL_witnesses_close_the_goal :
    served [0,1] upperTwo lateNormal 2 true=true := by decide
theorem an_unrelated_marking_point_does_not_prevent_service :
    served [0,1,3] upperTwo lateNormal 2 true=true := by decide
theorem recursive_edges_need_no_source_vector_on_DATA :
    served [0,1] [(0,2),(1,2),(2,3),(3,2),(3,4)]
      [(0,2),(1,2),(2,3),(3,4)] 4 true=true := by decide
theorem a_delayed_source_in_a_recursive_cone_keeps_the_goal :
    served [0,1] [(0,2),(1,2),(2,3),(3,2),(3,4)]
      [(0,2),(2,3),(3,4)] 4 true=false := by decide
theorem a_saved_conditional_hypothesis_cannot_replace_a_root_NORMAL_route :
    served [0,1] upperTwo [(0,2),(4,2)] 2 true=false := by decide
end OriginService

namespace OriginService
-- An adjacency/BFS implementation need not keep the reference's repeated
-- list scans. These two invariants prove the same selected vertex set.
theorem any_sound_closed_scan_has_exact_reachability_membership
    (valid : closed edges goal seen=true)
    (sound : ∀v∈seen, Reaches edges goal v) :
    ∀v, v∈seen ↔ Reaches edges goal v := by
  intro v
  exact ⟨sound v, a_validated_upper_scan_contains_every_reachable_generator valid⟩
theorem queue_and_list_scans_agree_when_both_certificates_pass
    (validA : closed edges goal a=true) (validB : closed edges goal b=true)
    (soundA : ∀v∈a, Reaches edges goal v)
    (soundB : ∀v∈b, Reaches edges goal v) : ∀v, v∈a ↔ v∈b := by
  intro v
  exact (any_sound_closed_scan_has_exact_reachability_membership validA soundA v).trans
    (any_sound_closed_scan_has_exact_reachability_membership validB soundB v).symm
end OriginService
