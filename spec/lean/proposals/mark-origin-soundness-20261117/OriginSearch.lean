import RecursiveSearch
import OriginRepair
namespace OriginSearch
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedColdMachine
open NestedSavedReplayCycle DirectPossibleReplay
set_option maxRecDepth 32768
set_option maxHeartbeats 600000000
local instance : Inhabited Offered:=⟨⟨point p [] .exact (some t),false⟩⟩

-- Distinct marking labels are proof/query inputs only, never runtime marks.
-- All marking points use the same full T and the same observer ID.
def applyMove (k : Nat) (r w : Path) (a : Offered) : Option Offered:=
  (OverwriteReplay.move r w a.ap).map fun b=>
    cutOffer k ⟨b.ap,b.demand || a.demand⟩
def transfer (k : Nat) (r w : Path) (source : Path) : Option Offered:=
  (some (cutOffer k ⟨point p source .exact (some t),false⟩)).bind (applyMove k r w)
def truth (r w source : Path) : Bool:=
  (OverwriteReplay.move r w (point p source .exact (some t))).isSome

def flat (r w source : Path) : Nat × Bool:=Id.run do
  let mut active:=true
  let mut known:=false
  for n in List.range 16 do
    let k:=max 1 (2*n)
    if !active then return (2*n+1,known)
    let result:=transfer k r w source
    let normal:=result.any (fun a=> !a.demand)
    let raw:=result.any (·.demand)
    let ready:=OriginRepair.closedGoal known
    known:=known || normal
    let target:=raw && !ready
    if !target then return (2*n+1,known)
    active:=target
  return (0,known)

-- A loop's ordinary body can repeatedly read or wrap. Zero iterations also
-- reach AL and its broad observation. The actual per-cap closure is finite.
def loopStep (k : Nat) (r w : Path) (xs : List Offered) : List Offered:=
  OverwriteReplay.values (xs ++ xs.filterMap (applyMove k r w))
def loopClose (k : Nat) (r w : Path) : Nat → List Offered → List Offered
 | 0,xs=>xs
 | n+1,xs=>loopClose k r w n (loopStep k r w xs)
def loopFacts (k : Nat) (r w source : Path) : List Offered:=
  loopClose k r w 48 [cutOffer k ⟨point p source .exact (some t),false⟩]

def loopRun (r w source : Path) : Nat × Bool × Bool:=Id.run do
  let mut permission:=true
  let mut known:=false
  let mut fixed:=true
  for n in List.range 12 do
    let k:=max 1 (2*n)
    if !permission then return (2*n+1,known,fixed)
    let facts:=loopFacts k r w source
    fixed:=fixed && decide (loopStep k r w facts=facts)
    let raw:=facts.any (·.demand)
    let ready:=OriginRepair.closedGoal known
    known:=known || facts.any (fun a=> !a.demand)
    let target:=raw && !ready
    -- Growing internal DATA demand can remain at the retirement handoff.
    -- It does not seed a root without its Target on the next forward run.
    if !raw then return (2*n+1,known,fixed)
    permission:=target
  return (0,known,fixed)

-- Native-shaped shared neutral recursive summaries. One finite state is
-- settled for both offers; the read-only lower query applies only already
-- proved NORMAL FLOW summaries to each original, bounded source offer.
def normalRoute (k : Nat) (rows : List NormalUniformNE.Edge) (source : Offered) : Bool:=
  rows.any fun e=>
    !e.2.demand && e.1.mark.isNone && e.2.ap.mark.isNone &&
    ((OverwriteReplay.apply false e source).map (cutOffer k)).any fun out=>
      !out.demand && RecursiveSearch.meetsRegion [] .may out

def recursive (isMutual : Bool) (word second firstSource secondSource : Path) : Nat × Bool × Bool:=Id.run do
  let c : RecursiveSearch.Config:=⟨word,second,isMutual,false,firstSource,[],.may⟩
  let ms:=RecursiveSearch.methods c
  let sources:=[firstSource,secondSource]
  let mut prev : ReplayCases.Frame:=⟨{},ms.map (fun _=>[]),ms.map (fun _=>[])⟩
  let mut permission:=true
  let mut known:=[false,false]
  let mut fixed:=true
  for index in List.range 21 do
    let run:=index+1
    let k:=max 1 (run-1)
    let offers:=sources.map fun path=>cutOffer k ⟨point p path .exact (some t),false⟩
    let initial:=OverwriteReplay.initial run k ms.length 1 (offers[0]!)
    let initial:=if !permission then {initial with offers:=[[],[]]} else if run%2==0 then
      {initial with offers:=[[⟨point p [] .may (some t),true⟩],[]]}
      else {initial with offers:=[OverwriteReplay.values offers,[]]}
    let (st,ready,_):=PrefixPointAudit.settle 200 run k 1 ms prev initial
    fixed:=fixed && ready
    let current : ReplayCases.Frame:=⟨st,ReplayCases.handoff st,OverwriteReplay.outputSaved run prev.saved st⟩
    if run%2==1 then
      let normalRows:=(st.current[0]!) ++ (OverwriteReplay.views false (current.saved[0]!)).map (·.1)
      let frozenClosed:=known.all id
      known:=(List.range 2).map fun i=>known[i]! || normalRoute k normalRows (offers[i]!)
      let raw:=(st.offers[1]!).any fun a=>a.demand && RecursiveSearch.meetsRegion [] .may a
      let target:=raw && !frozenClosed
      if current.rows.all List.isEmpty && !target then return (run,known.all id,fixed)
      permission:=target
    else
      permission:=permission && (st.offers[1]!).any fun a=>sources.any fun path=>RecursiveSearch.meetsRegion path .exact a
    prev:=current
  return (0,known.all id,fixed)

theorem flat_counterexample_is_repaired : flat [1,1,1] [] [1,1,1,1]=(5,true) := by decide
theorem same_full_mark_and_same_observer_do_not_imply_one_marking_origin :
    OriginService.served [0,1] OriginService.upperTwo OriginService.earlyNormal 2 true=false := by decide

def main : IO Unit:=do
  let mut flatTotal:=0
  let mut loopTotal:=0
  let mut recTotal:=0
  let mut failed:=0
  let mut latest:=0
  for src in RecursiveSearch.paths 5 do
   for r in RecursiveSearch.paths 3 do
    for w in RecursiveSearch.paths 2 do
      let a:=flat r w src
      flatTotal:=flatTotal+1
      latest:=max latest a.1
      if a.1==0 || a.2 != truth r w src then
        failed:=failed+1
        IO.println s!"GAP flat src={src} r={r} w={w} result={a}"
  for src in RecursiveSearch.paths 3 do
   for r in RecursiveSearch.paths 2 do
    for w in RecursiveSearch.paths 2 do
      let a:=loopRun r w src
      loopTotal:=loopTotal+1
      latest:=max latest a.1
      if a.1==0 || !a.2.1 || !a.2.2 then
        failed:=failed+1
        IO.println s!"GAP loop src={src} r={r} w={w} result={a}"
  for isMutual in [false,true] do
   for word in [[1],[2],[1,1],[1,2]] do
    for second in (if isMutual then [[1],[2],[1,2]] else [[]]) do
     for firstSource in RecursiveSearch.paths 1 do
      for secondSource in RecursiveSearch.paths 2 do
        let a:=recursive isMutual word second firstSource secondSource
        recTotal:=recTotal+1
        latest:=max latest a.1
        if a.1==0 || !a.2.1 || !a.2.2 then
          failed:=failed+1
          IO.println s!"GAP recursive mutual={isMutual} word={word} second={second} sources={firstSource}/{secondSource} result={a}"
  IO.println s!"ORIGINS flat={flatTotal} loops={loopTotal} recursive={recTotal} failed={failed} latestNaturalRun={latest}"
end OriginSearch
