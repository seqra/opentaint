import UniformReplay

namespace UniformCampaign
open NonEmptyPolicy NonEmptyRestriction NestedColdMachine
set_option maxRecDepth 32768
set_option maxHeartbeats 80000000

structure Case where
  methods : List PointWriteReplay.Method
  source : Offered
  calls : Nat
  expected : Bool
  deriving Repr
instance : Inhabited Case := ⟨⟨[],⟨⟨0,[],.exact,none,[],[]⟩,false⟩,0,false⟩⟩

structure State where
  rows : List (List Row)
  saved : List (List Saved)
  forwardActive : Bool
  backwardActive : Bool
  report : Bool
  data : NestedColdMachine.State
  deriving DecidableEq, Repr

def emptyData (c : Case) : NestedColdMachine.State :=
  ⟨List.replicate c.methods.length [],List.replicate c.methods.length [],List.replicate (c.calls+1) []⟩
def initial (c : Case) : State :=
  ⟨List.replicate c.methods.length [],List.replicate c.methods.length [],true,false,false,emptyData c⟩
def limit (run : Nat) : Nat := max 1 (run-1)

def producerHit (c : Case) (st : NestedColdMachine.State) : Bool :=
  st.offers.getLast!.any fun a =>
    a.ap.mark == c.source.ap.mark &&
    ((match dropHead a.ap.path c.source.ap.path with
      | some rest => admits a.ap.tail a.ap.e rest
      | none => false) ||
      (c.source.ap.tail == .must && (dropHead c.source.ap.path a.ap.path).isSome))

def step (c : Case) (run : Nat) (old : State) : State :=
  let back := run % 2 == 0
  let active := if back then old.backwardActive else old.forwardActive
  if !active then
    ⟨List.replicate c.methods.length [],old.saved,false,false,old.report,emptyData c⟩
  else
    let st := UniformReplay.rounds 8 run (limit run) c.calls c.methods old.rows old.saved c.source
    let rows := OverwriteReplay.outputRows st
    let saved := OverwriteReplay.outputSaved run old.saved st
    if back then ⟨rows,saved,producerHit c st,false,old.report,st⟩
    else ⟨rows,saved,old.forwardActive,st.offers.getLast!.any (·.demand),
      old.report || st.offers.getLast!.any (fun a => !a.demand),st⟩

def history (c : Case) : Nat → State
  | 0 => initial c
  | n+1 => step c (n+1) (history c n)

def stopped (run : Nat) (s : State) : Bool :=
  run % 2 == 1 && s.rows.all List.isEmpty && !s.backwardActive

def cases : List (String × Case) := [
 ("Double",⟨PointDouble.methods,PointDouble.source,3,true⟩),
 ("Growth",⟨PointGrowth.methods,PointGrowth.source,2,true⟩),
 ("LongReader",⟨PointLongReader.methods,PointLongReader.source,2,true⟩),
 ("Nested",⟨PointNested.methods,PointNested.source,3,true⟩),
 ("NestedDeep",⟨PointNestedDeep.methods,PointNestedDeep.source,1,true⟩),
 ("NestedExact",⟨PointNestedExact.methods,PointNestedExact.source,1,true⟩),
 ("NestedLarger",⟨PointNestedLarger.methods,PointNestedLarger.source,3,true⟩),
 ("NestedNegative",⟨PointNestedNegative.methods,PointNestedNegative.source,1,false⟩),
 ("NestedPositive",⟨PointNestedPositive.methods,PointNestedPositive.source,1,true⟩),
 ("NestedSurvivor",⟨PointNestedSurvivor.methods,PointNestedSurvivor.source,1,true⟩),
 ("OldBB",⟨PointOldBB.methods,PointOldBB.source,2,true⟩),
 ("OldMethod",⟨PointOldMethod.methods,PointOldMethod.source,2,true⟩),
 ("OrdinaryTwo",⟨PointOrdinaryTwo.methods,PointOrdinaryTwo.source,2,true⟩),
 ("Overwrite",⟨PointOverwrite.methods,PointOverwrite.source,3,true⟩),
 ("Postfix",⟨PointPostfix.methods,PointPostfix.source,3,true⟩),
 ("Prefix",⟨PointPrefix.methods,PointPrefix.source,3,false⟩),
 ("PrefixPostfix",⟨PointPrefixPostfix.methods,PointPrefixPostfix.source,3,true⟩),
 ("RoundTrip",⟨PointRoundTrip.methods,PointRoundTrip.source,3,true⟩)]

def quiet (c : Case) (report : Bool) (saved : List (List Saved)) : State :=
  ⟨List.replicate c.methods.length [],saved,false,false,report,emptyData c⟩

theorem inactive_has_no_analysis_or_new_guidance (c : Case) (run : Nat) (report : Bool)
    (saved : List (List Saved)) : step c run (quiet c report saved) = quiet c report saved := by
  simp [step,quiet]

theorem quiet_never_revives (c : Case) (start count : Nat) (report : Bool)
    (saved : List (List Saved)) :
    (List.range count).foldl (fun s k => step c (start+k+1) s) (quiet c report saved) =
      quiet c report saved := by
  induction count with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ,List.foldl_append]
      simp only [List.foldl_cons,List.foldl_nil,ih]
      exact inactive_has_no_analysis_or_new_guidance c _ _ _

end UniformCampaign
