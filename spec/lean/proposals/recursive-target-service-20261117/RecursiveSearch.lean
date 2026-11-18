import PostDirectReference
import RootTerminalRepair
namespace RecursiveSearch
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open NestedSavedReplayCycle NestedColdMachine DirectPossibleReplay
set_option maxRecDepth 32768
set_option maxHeartbeats 240000000

structure Config where
  first : Path
  second : Path:=[]
  isMutual : Bool:=false
  secondBase : Bool:=false
  source : Path:=[]
  observation : Path:=[]
  tail : Tail:=.may
  deriving Repr

def methods (c : Config) : List Method :=
  if c.isMutual then
    [[[],[.call 1,.move [] c.first]],
      (if c.secondBase then [[]] else []) ++ [[.call 0,.move [] c.second]]]
  else [[[],[.call 0,.move [] c.first]]]

def source (c : Config) : Offered:=⟨point p c.source .exact (some t),false⟩
def meetsRegion (path : Path) (tail : Tail) (a : Offered) : Bool:=
  if a.ap.mark != some t then false else
  if a.ap.path==path then
    if tail==.exact then a.ap.tail != .ne
    else if tail==.ne then a.ap.tail != .exact else true
  else match dropHead path a.ap.path with
  | some (_::_)=>tail != .exact
  | _=>match dropHead a.ap.path path with
    | some suffix=>admits a.ap.tail a.ap.e suffix
    | _=>false

def observed (c : Config) (a : Offered) : Bool:=meetsRegion c.observation c.tail a
def sourcePermission (c : Config) (a : Offered) : Bool:=meetsRegion c.source .exact a

def oracle (c : Config) : Bool:=
  let cycle:=if c.isMutual then c.first++c.second else c.first
  let bases:=if c.isMutual && c.secondBase then [[],c.first] else [[]]
  (List.range (c.observation.length+2)).any fun n=>bases.any fun b=>
    let path:=(List.replicate n cycle).flatten ++ b ++ c.source
    observed c ⟨point p path .exact (some t),false⟩

structure Result where
  stop : Nat:=0
  normal : Bool:=false
  truth : Bool:=false
  fixed : Bool:=true
  rawTarget : Bool:=false
  deriving Repr

def run (c : Config) : Result:=Id.run do
  let ms:=methods c
  let mut prev : ReplayCases.Frame:=⟨{},ms.map (fun _=>[]),ms.map (fun _=>[])⟩
  let mut rootPermission:=true
  let mut known:=false
  let mut liveRootTarget:=false
  let mut allFixed:=true
  for index in List.range 25 do
    let run:=index+1
    let k:=max 1 (run-1)
    let initial:=OverwriteReplay.initial run k ms.length 1 (source c)
    let initial:=if !rootPermission then
      {initial with offers:=[[],[]]}
      else if run%2==0 then
        {initial with offers:=[[cutOffer k ⟨point p c.observation c.tail (some t),true⟩],[]]}
      else initial
    let (st,fixed,_):=PrefixPointAudit.settle 160 run k 1 ms prev initial
    allFixed:=allFixed && fixed
    let current:ReplayCases.Frame:=⟨st,ReplayCases.handoff st,OverwriteReplay.outputSaved run prev.saved st⟩
    if run%2==1 then
      let normal:=(st.offers[1]!).any (fun a=> !a.demand && observed c a)
      let rawTarget:=(st.offers[1]!).any (fun a=> a.demand && observed c a)
      liveRootTarget:=rawTarget && !known
      known:=known || normal
      if current.rows.all List.isEmpty && !liveRootTarget then
        return ⟨run,known,oracle c,allFixed,rawTarget⟩
      rootPermission:=liveRootTarget
    else
      rootPermission:=rootPermission && (st.offers[1]!).any (sourcePermission c)
    prev:=current
  return ⟨0,known,oracle c,allFixed,liveRootTarget⟩

def paths : Nat → List Path
 | 0=>[[]]
 | n+1=>[]::(paths n).flatMap (fun p=>[1::p,2::p])

theorem the_negative_exact_observer_is_not_covered_by_the_positive_MAY_report :
    oracle ⟨[1],[],false,false,[1,2],[1,2,2],.exact⟩=false ∧
    oracle ⟨[1],[],false,false,[1,2],[],.may⟩=true := by decide

theorem a_same_head_NE_is_a_broad_observation_witness_but_not_an_exact_point :
    meetsRegion [1] .may ⟨point p [1] .ne (some t),true⟩=true ∧
    meetsRegion [1] .ne ⟨point p [1] .ne (some t),true⟩=true ∧
    meetsRegion [1] .exact ⟨point p [1] .ne (some t),true⟩=false := by decide

def main : IO Unit:=do
  let words:=[[1],[2],[1,1],[1,2]]
  let graphs:=(words.map fun w=>({first:=w} : Config)) ++
    words.flatMap fun u=>words.flatMap fun v=>[{first:=u,second:=v,isMutual:=true,secondBase:=false},{first:=u,second:=v,isMutual:=true,secondBase:=true}]
  let mut total:=0
  let mut failed:=0
  let mut nonfixed:=0
  let mut latest:=0
  for graph in graphs do
   for src in paths 2 do
    for obs in paths 3 do
     for tail in [Tail.exact,Tail.may,Tail.ne] do
      let c:={graph with source:=src,observation:=obs,tail:=tail}
      let r:=run c
      total:=total+1
      if !r.fixed then nonfixed:=nonfixed+1
      latest:=max latest r.stop
      if r.stop==0 || r.normal != r.truth || !r.fixed then
        failed:=failed+1
        IO.println s!"GAP {reprStr c} result={reprStr r}"
      if failed>=8 then
        IO.println s!"EARLY total={total} failed={failed} nonfixed={nonfixed} latestNaturalRun={latest}"
        return
  IO.println s!"RECURSION total={total} failed={failed} nonfixed={nonfixed} latestNaturalRun={latest}"
end RecursiveSearch
