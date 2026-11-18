import OriginSearch
namespace PairedReference
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedSavedReplayCycle NestedColdMachine DirectPossibleReplay
set_option maxRecDepth 65536
set_option maxHeartbeats 800000000
local instance : Inhabited Offered:=⟨⟨point p [] .exact (some t),false⟩⟩

-- Writer base: f=p. One recursive branch adds g before the returned path.
-- Reader base: return p.g. Its recursive branch reads g before recurring.
-- A second recursive branch can use h in both methods without changing the
-- disjoint last fields. The small cold run first keeps only the g branch.
def methods (secondBranch : Bool := false) (positive : Bool:=false)
    (writerBase : Path:=[1]) (readerBase : Path:=if positive then [1] else [2])
    (prefixes : List Path:=if secondBranch then [[2],[3]] else [[2]]) : List Method:=
  [ [.move [] writerBase] :: prefixes.map (fun w=>[.call 0,.move [] w]),
    [.move readerBase []] :: prefixes.map (fun r=>[.move r [],.call 1]) ]

def round (run k : Nat) (ms : List Method) (prev : ReplayCases.Frame) (st : State) : State:=Id.run do
  let mut next:=st
  for j in List.range 2 do
    let owner:=if run%2==1 then j else 1-j
    let mut out:=next.offers[j+1]!
    for a in next.offers[j]! do
      next:=register owner a next
      out:=out ++ DirectPossibleReplay.offer run k (prev.rows[owner]!)
        (prev.saved[owner]!) (next.current[owner]!) a
    next:={next with offers:=next.offers.set (j+1) (OverwriteReplay.values out)}
  for owner in List.range 2 do
    next:=DirectPossibleReplay.process run k owner ms prev.rows prev.saved next
  return next

def settle (fuel run k : Nat) (ms : List Method) (prev : ReplayCases.Frame) :
    State → State × Bool × Nat
  | st=>match fuel with
    | 0=>(st,false,0)
    | n+1=>let next:=round run k ms prev st
           if next==st then (st,true,1) else
             let (done,fixed,count):=settle n run k ms prev next
             (done,fixed,count+1)

def step (run : Nat) (prev : ReplayCases.Frame) (branch : Bool:=false) (positive : Bool:=false) (allowed : Bool:=true)
    (writerBase : Path:=[1]) (readerBase : Path:=if positive then [1] else [2])
    (prefixes : List Path:=if branch then [[2],[3]] else [[2]]) : ReplayCases.Frame × Bool × Nat:=
  let k:=max 1 (run-1)
  let source : Offered:=⟨point p [] .exact (some t),false⟩
  let initial:=OverwriteReplay.initial run k 2 2 source
  let initial:=if run%2==0 then {initial with offers:=[[⟨point p [] .exact (some t),true⟩],[],[]]} else initial
  let initial:=if allowed then initial else {initial with offers:=[[],[],[]]}
  let (st,fixed,count):=settle 200 run k (methods branch positive writerBase readerBase prefixes) prev initial
  (⟨st,ReplayCases.handoff st,OverwriteReplay.outputSaved run prev.saved st⟩,fixed,count)

def observed (a : Offered) : Bool:=a.ap.mark==some t &&
  (dropHead a.ap.path []).isSome && admits a.ap.tail a.ap.e []

def main : IO Unit:=do
  let mut prev : ReplayCases.Frame:=⟨{},[[],[]],[[],[]]⟩
  for index in List.range 7 do
    let run:=index+1
    let (next,fixed,count):=step run prev
    let offered:=next.data.offers[2]!
    IO.println s!"PAIRED run={run} fixed={fixed} rounds={count} rows={next.rows.map List.length} summaries={next.data.current.map List.length} normal={offered.any (fun a=> !a.demand && observed a)} target={offered.any (fun a=>a.demand && observed a)}"
    if run≤5 then
      IO.println s!"offers={reprStr next.data.offers}"
      IO.println s!"rows={reprStr next.rows}"
      IO.println s!"summaries={reprStr next.data.current}"
      IO.println s!"submittedDomains={reprStr next.data.domains}"
      for owner in List.range 2 do
        IO.println s!"domain owner={owner} {reprStr (next.data.domains[owner]!)}"
        let norms:=OverwriteReplay.views (run%2==0) (prev.saved[owner]!)
        let work:=DirectPossibleReplay.cells run (max 1 (run-1)) (run%2==0)
          (prev.rows[owner]!) norms (next.data.domains[owner]!)
        IO.println s!"initials owner={owner} {reprStr ((work.flatMap fun cell=>cell.2.map (fun q=>q.1)).eraseDups)}"
    prev:=next
end PairedReference
