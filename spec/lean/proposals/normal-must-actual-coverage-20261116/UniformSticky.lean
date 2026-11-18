import UniformCampaign
import UniformAlternating

/- Selected control model. DATA normalization may remove a late covered
   member, but an observation that already emitted Target remains emitted.
   The final-DATA-only helper is used for data witnesses, not Target state. -/
namespace UniformSticky
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def seenDemand (exitDemand : α → Bool) (advance : α → α) : Nat → α → Bool
  | 0, data => exitDemand data
  | n+1, data => exitDemand data || seenDemand exitDemand advance n (advance data)

theorem an_emitted_target_is_never_erased (test : α → Bool) (advance : α → α)
    (fuel : Nat) (data : α) (already : test data = true) :
    seenDemand test advance fuel data = true := by
  cases fuel <;> simp [seenDemand,already]

def forwardDemand (c : UniformCampaign.Case) (run : Nat) (old : UniformCampaign.State) : Bool :=
  seenDemand (fun data => data.offers.getLast!.any (·.demand))
    (UniformReplay.round run (UniformCampaign.limit run) c.calls c.methods old.rows old.saved) 8
    (OverwriteReplay.initial run (UniformCampaign.limit run) c.methods.length c.calls c.source)

def step (c : UniformCampaign.Case) (run : Nat) (old : UniformCampaign.State) : UniformCampaign.State :=
  let next := UniformCampaign.step c run old
  if run % 2 == 1 && old.forwardActive then
    {next with backwardActive := forwardDemand c run old}
  else next

def history (c : UniformCampaign.Case) : Nat → UniformCampaign.State
  | 0 => UniformCampaign.initial c
  | n+1 => step c (n+1) (history c n)

theorem from_checked_data_step (c : UniformCampaign.Case) (run : Nat)
    (old next : UniformCampaign.State) (data : UniformCampaign.step c run old = next)
    (observations : (run % 2 == 1 && old.forwardActive) = true → forwardDemand c run old = next.backwardActive) :
    step c run old = next := by
  unfold step
  rw [data]
  split
  · rename_i active
    rw [observations active]
  · rfl

theorem quiet_still_has_no_new_work (c : UniformCampaign.Case) (run : Nat)
    (report : Bool) (saved : List (List NestedColdMachine.Saved)) :
    step c run (UniformCampaign.quiet c report saved) = UniformCampaign.quiet c report saved := by
  unfold step
  rw [UniformCampaign.inactive_has_no_analysis_or_new_guidance]
  simp [UniformCampaign.quiet]

def newForwardDemand (run : Nat) (old : UniformAlternating.State) : Bool :=
  seenDemand (fun data => data.offers.getLast!.any (·.demand))
    (UniformAlternating.round true run (UniformAlternating.limit run) old.rows old.saved) 12
    (UniformAlternating.initialData false)

def newStep (run : Nat) (old : UniformAlternating.State) : UniformAlternating.State :=
  let next := UniformAlternating.step true run old
  if run % 2 == 1 && old.sourceAllowed then {next with observationActive := newForwardDemand run old} else next

def newHistory : Nat → UniformAlternating.State
  | 0 => UniformAlternating.initial
  | n+1 => newStep (n+1) (newHistory n)

theorem from_checked_new_data_step (run : Nat) (old next : UniformAlternating.State)
    (data : UniformAlternating.step true run old = next)
    (observations : (run % 2 == 1 && old.sourceAllowed) = true → newForwardDemand run old = next.observationActive) :
    newStep run old = next := by
  unfold newStep
  rw [data]
  split
  · rename_i active
    rw [observations active]
  · rfl

theorem new_quiet_still_has_no_work (run : Nat) (report : Bool) (saved : List UniformAlternating.Saved) :
    newStep run (UniformAlternating.quiet report saved) = UniformAlternating.quiet report saved := by
  unfold newStep
  rw [UniformAlternating.quiet_never_restarts]
  simp [UniformAlternating.quiet]

end UniformSticky
