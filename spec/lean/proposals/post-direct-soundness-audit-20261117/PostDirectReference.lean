import RepairCases
namespace PrefixPointAudit
open NonEmptyPolicy NonEmptyRestriction NestedSavedReplayCycle NestedColdMachine
open DirectPossibleReplay
set_option maxRecDepth 32768
set_option maxHeartbeats 240000000

structure Config where
  branches : List (Path × Path)
  read : Path
  write : Path
  sourcePath : Path
  sourceTail : Tail
  sourceE : List Nat := []
  calls : Nat := 1
  observePath : Path := []
  observeTail : Tail := .may
  deriving Repr

def methods (c : Config) : List Method :=
  [[[.move c.read [], .call 1, .move [] c.write]],
    c.branches.map fun (r,w)=>[.move r w]]
def source (c : Config) : Offered :=
  ⟨{point AcyclicMayCycle.p c.sourcePath c.sourceTail (some AcyclicMayCycle.t) with e:=c.sourceE},false⟩

def settle (fuel run k calls : Nat) (ms : List Method) (prev : ReplayCases.Frame) :
    State → State × Bool × Nat
  | st => match fuel with
    | 0 => (st,false,0)
    | n+1 =>
      let next:=DirectPossibleReplay.round run k calls ms prev.rows prev.saved st
      if next=st then (st,true,1) else
        let (done,fixed,count):=settle n run k calls ms prev next
        (done,fixed,count+1)

def step (c : Config) (run : Nat) (prev : ReplayCases.Frame) : ReplayCases.Frame × Bool :=
  let k:=max 1 (run-1)
  let initial:=OverwriteReplay.initial run k (methods c).length c.calls (source c)
  let question:=cutOffer k ⟨point AcyclicMayCycle.p c.observePath c.observeTail (some AcyclicMayCycle.t),true⟩
  let initial:=if run%2==0 then {initial with offers:=initial.offers.set 0 [question]} else initial
  let (data,fixed,_):=settle 60 run k c.calls (methods c) prev initial
  (⟨data,ReplayCases.handoff data,OverwriteReplay.outputSaved run prev.saved data⟩,fixed)

def transfer (r w : Path) (a : Offered) : List Offered :=
  ((OverwriteReplay.move r w a.ap).map fun v=>⟨v.ap,v.demand || a.demand⟩).toList

def ordinary (c : Config) (actuals : List Offered) : List Offered :=
  actuals.flatMap fun a => (transfer c.read [] a).flatMap fun x =>
    c.branches.flatMap fun (r,w) => (transfer r w x).flatMap (transfer [] c.write)

def expected (c : Config) : List Offered :=
  (List.range c.calls).foldl (fun values _=>ordinary c values) [source c]

def containsPoint (a : Offered) (path : Path) : Bool :=
  !a.demand && a.ap.mark==some AcyclicMayCycle.t &&
    match dropHead a.ap.path path with
    | some suffix=>admits a.ap.tail a.ap.e suffix
    | none=>false

def paths : Nat → List Path
  | 0=>[[]]
  | n+1=>[] :: (paths n).flatMap (fun path=>[1::path,2::path])

def pointProbes (values : List Offered) : List Path :=
  (values.flatMap fun a => (paths 3).filterMap fun suffix=>
    if admits a.ap.tail a.ap.e suffix then some (a.ap.path++suffix) else none).eraseDups

structure Result where
  stop : Nat
  fixed : Bool
  missing : List Path
  extra : List Path
  frame : ReplayCases.Frame
  deriving Repr

def observes (c : Config) (a : Offered) : Bool :=
  a.ap.mark==some AcyclicMayCycle.t &&
  match dropHead c.observePath a.ap.path with
  | some []=>admits a.ap.tail a.ap.e []
  | some (_::_)=>c.observeTail != .exact
  | none=>match dropHead a.ap.path c.observePath with
    | some suffix=>admits a.ap.tail a.ap.e suffix
    | none=>false

def scan (c : Config) : Result := Id.run do
  let mut prev : ReplayCases.Frame:=⟨{},[[],[]],[[],[]]⟩
  let mut allFixed:=true
  for n in List.range 25 do
    let run:=n+1
    let (st,fixed):=step c run prev
    allFixed:=allFixed && fixed
    let actual:=st.data.offers.getLast!
    let normal:=actual.any (fun a=> !a.demand && observes c a)
    let targetD:=actual.any (fun a=>a.demand && observes c a)
    if run%2==1 && st.rows.all List.isEmpty && !targetD then
      let truth:=(expected c).any (observes c)
      return ⟨run,allFixed,if truth && !normal then [c.observePath] else [],
        if normal && !truth then [c.observePath] else [],st⟩
    prev:=st
  return ⟨0,allFixed,[],[],prev⟩

end PrefixPointAudit
