import CarryNeutral
namespace CarryCampaign
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
def dataStep (c : UniformCampaign.Case) (run : Nat) (old : UniformCampaign.State) : UniformCampaign.State :=
  let back := run % 2 == 0
  let active := if back then old.backwardActive else old.forwardActive
  if !active then
    ⟨List.replicate c.methods.length [],old.saved,false,false,old.report,UniformCampaign.emptyData c⟩
  else
    let st := CarryNeutral.rounds 8 run (UniformCampaign.limit run) c.calls c.methods old.rows old.saved c.source
    let rows := OverwriteReplay.outputRows st
    let saved := OverwriteReplay.outputSaved run old.saved st
    if back then ⟨rows,saved,UniformCampaign.producerHit c st,false,old.report,st⟩
    else ⟨rows,saved,old.forwardActive,st.offers.getLast!.any (·.demand),
      old.report || st.offers.getLast!.any (fun a => !a.demand),st⟩


def forwardDemand (c : UniformCampaign.Case) (run : Nat) (old : UniformCampaign.State) : Bool :=
  UniformSticky.seenDemand (fun data => data.offers.getLast!.any (·.demand))
    (CarryNeutral.round run (UniformCampaign.limit run) c.calls c.methods old.rows old.saved) 8
    (OverwriteReplay.initial run (UniformCampaign.limit run) c.methods.length c.calls c.source)

def step (c : UniformCampaign.Case) (run : Nat) (old : UniformCampaign.State) : UniformCampaign.State :=
  let next := dataStep c run old
  if run % 2 == 1 && old.forwardActive then {next with backwardActive := forwardDemand c run old} else next

def history (c : UniformCampaign.Case) : Nat → UniformCampaign.State
  | 0 => UniformCampaign.initial c
  | n+1 => step c (n+1) (history c n)

theorem dataStep_eq_old (c : UniformCampaign.Case) (run : Nat) (old : UniformCampaign.State)
    (flow : CarryNeutral.FlowAll old.rows = true) :
    dataStep c run old = UniformCampaign.step c run old := by
  simp only [dataStep,UniformCampaign.step,
    CarryNeutral.rounds_eq_old 8 run (UniformCampaign.limit run) c.calls c.methods old.rows old.saved c.source flow]

theorem forwardDemand_eq_old (c : UniformCampaign.Case) (run : Nat) (old : UniformCampaign.State)
    (flow : CarryNeutral.FlowAll old.rows = true) :
    forwardDemand c run old = UniformSticky.forwardDemand c run old := by
  have func : CarryNeutral.round run (UniformCampaign.limit run) c.calls c.methods old.rows old.saved =
      UniformReplay.round run (UniformCampaign.limit run) c.calls c.methods old.rows old.saved := by
    funext data
    exact CarryNeutral.round_eq_old run (UniformCampaign.limit run) c.calls c.methods old.rows old.saved data flow
  simp only [forwardDemand,UniformSticky.forwardDemand,func]

theorem step_eq_old (c : UniformCampaign.Case) (run : Nat) (old : UniformCampaign.State)
    (flow : CarryNeutral.FlowAll old.rows = true) : step c run old = UniformSticky.step c run old := by
  simp only [step,UniformSticky.step,dataStep_eq_old c run old flow,forwardDemand_eq_old c run old flow]

theorem quiet_never_restarts (c : UniformCampaign.Case) (run : Nat)
    (report : Bool) (saved : List (List NestedColdMachine.Saved)) :
    step c run (UniformCampaign.quiet c report saved) = UniformCampaign.quiet c report saved := by
  simp [step,dataStep,UniformCampaign.quiet]
end CarryCampaign
