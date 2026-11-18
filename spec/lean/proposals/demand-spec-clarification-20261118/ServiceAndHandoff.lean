import ServiceSimulation
import CompleteClosure
import LostMarkOrigin

namespace ServiceAndHandoff
open ServiceSimulation

-- "Complete" is a native extraction obligation. The executable check uses
-- only the supplied, fully qualified uses and recipes over retained inputs.
def continuation (complete : Bool) (enabled plan : List Action)
    (retained uses : List Need) : Bool :=
  complete && check enabled plan retained uses

theorem a_checked_continuation_supplies_every_affected_use
    (passed : continuation complete enabled plan retained uses = true)
    (affected : need ∈ uses) :
    AuditKernel.Derives (nativeRules enabled) (· ∈ retained) need :=
  checked_service_supplies_each_obligation (Bool.and_eq_true_iff.mp passed).2 affected

theorem no_complete_scope_means_no_continuation_certificate :
    continuation false enabled plan retained uses = false := by simp [continuation]

def readyU : Need := ⟨.data,3,1,0⟩
def observeU : Need := ⟨.track,3,1,1⟩
def otherSource : Need := ⟨.sourcePermission,5,1,2⟩
def observe : Action := ⟨[readyU],observeU⟩

theorem r17_the_bound_normal_serve_can_reproduce_the_observation :
    continuation true [observe] [observe] [readyU] [observeU] = true := by decide

theorem r17_a_distinct_source_permission_is_not_supplied_by_the_same_points :
    continuation true [observe] [observe] [readyU] [observeU,otherSource] = false := by decide

inductive State where
  | seed | localV | retH | retK
  deriving DecidableEq

def next : State → List State
  | .seed => [.localV]
  | .localV => [.retH,.retK]
  | _ => []

def selectedH : State → Bool | .retH => true | _ => false
def selectedK : State → Bool | .retK => true | _ => false
def owned : List State := [.seed,.localV,.retH,.retK]
def committed : List State := [.retH]
def covered : State → Bool := CompleteClosure.hasWitness committed (fun n s => decide (n = s))

theorem r19_a_disjoint_unpublished_return_can_be_in_the_closed_graph :
    CompleteClosure.check next [.seed] owned selectedH covered = true := by decide

theorem r19_removing_the_disjoint_return_or_its_predecessor_breaks_closure :
    CompleteClosure.check next [.seed] [.seed,.localV,.retH] selectedH covered = false ∧
    CompleteClosure.check next [.seed] [.seed,.retH,.retK] selectedH covered = false := by decide

theorem r19_the_same_owned_graph_cannot_certify_a_k_delivery :
    CompleteClosure.check next [.seed] owned selectedK covered = false := by decide

theorem r19_each_selected_reachable_exit_has_a_concrete_committed_witness
    {S : Type} [DecidableEq S] (next : S → List S) (seeds owned committed : List S)
    (selected : S → Bool) (cover : S → S → Bool)
    (s : S)
    (passed : CompleteClosure.check next seeds owned selected
      (CompleteClosure.hasWitness committed cover) = true)
    (reached : CompleteClosure.Reach next seeds s) (relevant : selected s = true) :
    ∃ n ∈ committed, cover n s = true :=
  CompleteClosure.a_concrete_normal_service_witness next seeds owned committed
    selected cover passed s reached relevant

-- The DATA cases stand for the full scalar entry and exit tests.
inductive Entry where
  | data (matched : Bool) | zero | target
inductive Exit where
  | data (matched : Bool) | zero
inductive Result where
  | data | zero | dt | nt
  deriving DecidableEq

structure Pair where
  entry : Entry
  exit : Exit

def entryAccepts (isZero : Bool) : Entry → Bool
  | .data matched => !isZero && matched
  | .zero | .target => isZero

def exitAccepts (result : Result) : Exit → Bool
  | .data matched => decide (result = .data) && matched
  | .zero => decide (result = .zero ∨ result = .dt)

def admits (isZero : Bool) (result : Result) (pairs : List Pair) : Bool :=
  pairs.any (fun pair => entryAccepts isZero pair.entry && exitAccepts result pair.exit)

theorem typed_c5_does_not_combine_two_different_pairs :
    admits true .dt [⟨.target,.data true⟩,⟨.data true,.zero⟩] = false ∧
    admits true .dt [⟨.target,.zero⟩] = true := by decide

theorem a_dt_uses_the_same_exit_as_zero_but_never_as_an_nt (entry : Entry) (isZero : Bool) :
    admits isZero .dt [⟨entry,.zero⟩] = admits isZero .zero [⟨entry,.zero⟩] ∧
    admits isZero .nt [⟨entry,.zero⟩] = false := by simp [admits,exitAccepts]

-- Two independent synthetic observers. Reuse the checked four-field
-- source and three-read transfer for id2. Entry/permission is modelled
-- by the sole admitted root control guide in this void-root slice.
def id1 : Nat := 1
def id2 : Nat := 2
def origins (run : Nat) : List Nat :=
  if LostMarkOrigin.demandB (max 1 (run-1)) then [id2] else []
def needs (frozen : List Nat) (goals : List Nat) : Bool :=
  goals.any (fun goal => !frozen.contains goal)
def keepRoot (run : Nat) (frozen : List Nat) (otherUsesServed : Bool) : Bool :=
  !(origins run).isEmpty && !RecursiveTargetSupport.retire true true true otherUsesServed
    (needs frozen (origins run))

theorem r37_a_first_observer_does_not_retire_the_second_observers_target :
    origins 3 = [id2] ∧ keepRoot 3 [id1] true = true ∧
    LostMarkOrigin.normalB 2 = false := by decide

theorem r37_the_retained_guide_can_reach_the_other_id_at_run5 :
    (keepRoot 3 [id1] true && LostMarkOrigin.normalB 4) = true ∧
    origins 5 = [] ∧ keepRoot 5 [id1] true = false := by decide

theorem r37_an_already_known_origin_does_not_hide_a_late_distinct_origin :
    RecursiveTargetSupport.events none [needs [id1] [id1],needs [id1] [id2]] =
      [false,true] := by decide

theorem r37_closed_goals_still_need_the_separate_control_certificate :
    keepRoot 3 [id1,id2] false = true ∧ keepRoot 3 [id1,id2] true = false := by decide

end ServiceAndHandoff
