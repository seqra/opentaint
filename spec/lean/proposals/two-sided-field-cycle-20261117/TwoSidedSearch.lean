import OperationalCycle
import PairedSearch
import PairedContext
namespace TwoSidedSearch
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedColdMachine NestedSavedReplayCycle DirectPossibleReplay
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000000
local instance : Inhabited Offered:=⟨⟨point p [] .exact (some t),false⟩⟩

def step (run : Nat) (prev : ReplayCases.Frame) (ms : List Method) (source obs : Path)
    (allowed : Bool) : ReplayCases.Frame × Bool × Nat:=
  let k:=max 1 (run-1)
  let src : Offered:=⟨point p source .exact (some t),false⟩
  let initial:=OverwriteReplay.initial run k 2 2 src
  let initial:=if run%2==0 then {initial with offers:=[[cutOffer k ⟨point p obs .exact (some t),true⟩],[],[]]} else initial
  let initial:=if allowed then initial else {initial with offers:=[[],[],[]]}
  let (st,fixed,count):=PairedReference.settle 200 run k ms prev initial
  (⟨st,ReplayCases.handoff st,OverwriteReplay.outputSaved run prev.saved st⟩,fixed,count)

def observesPoint (path : Path) (a : Offered) : Bool :=
  a.ap.mark==some t && match dropHead a.ap.path path with
  | some rest => admits a.ap.tail a.ap.e rest
  | none => false

def showAp (a : Ap) := s!"{a.path}{repr a.tail}{if a.mark.isNone then "F" else "T"}"
def showRow (r : Row) := s!"[{showAp r.entry}|{showAp r.exit}]"
def showEdge (e : NormalUniformNE.Edge) := s!"{showAp e.1}->{showAp e.2.ap}:{if e.2.demand then "D" else "N"}"

def scan (ms : List Method) (source obs : Path) (noRoute : Bool) (fuel : Nat) (trace := false) : IO (Nat × Bool × Bool × List Nat) :=do
  let mut prev : ReplayCases.Frame:=⟨{},[[],[]],[[],[]]⟩
  let mut allowed:=true
  let mut known:=false
  let mut normalSeen:=false
  let mut fixed:=true
  let mut emitted:=[]
  for index in List.range fuel do
    let run:=index+1
    let (next,ready,count):=step run prev ms source obs allowed
    fixed:=fixed && ready
    let values:=next.data.offers[2]!
    let related:=values.filter (observesPoint (if run%2==1 then obs else source))
    if trace then
      IO.println s!"run={run} fixed={ready}/{count} allowed={allowed} rows={next.rows.map List.length} saved={next.saved.map List.length} related={reprStr related}"
      for o in [0,1] do
        IO.println s!"o={o} demand = {(prev.rows[o]!).map showRow}"
        IO.println s!"o={o} out = {(next.rows[o]!).map showRow}"
        IO.println s!"o={o} published = {(next.data.current[o]!).map showEdge}"
        IO.println s!"o={o} supplied = {(next.data.domains[o]!).map fun a => (showAp a.ap,a.demand)}"
        let norm := OverwriteReplay.views (run%2==0) (prev.saved[o]!)
        let own := DirectPossibleReplay.cells run (max 1 (run-1)) (run%2==0) (prev.rows[o]!) norm (next.data.domains[o]!)
        IO.println s!"o={o} raw = {(own.flatMap (fun c=>c.2.map (fun x=>(showAp x.1.ap,x.1.demand)))).eraseDups}"
    if run%2==1 then
      let normal:=related.any (fun a=> !a.demand)
      let target:=(related.any (·.demand)) && !known
      if target then emitted:=emitted++[run]
      known:=known || noRoute || normal
      normalSeen:=normalSeen || normal
      if next.rows.all List.isEmpty && !target then return (run,normalSeen,fixed,emitted)
      allowed:=target
    else
      allowed:=allowed && !related.isEmpty
    prev:=next
  return (0,normalSeen,fixed,emitted)

def readerMethods (base : Path := [2]) (readerLead : Path := [3]) (readerAfter : Path := [3]) :
    List Method :=
  [ [[.move [] [1]], [.call 0, .move [] [2]]],
    [[.move base []], [.move [2] [], .call 1],
     [.move readerLead [], .call 1, .move readerAfter []]] ]

def emptyFrame : ReplayCases.Frame := ⟨{},[[],[]],[[],[]]⟩
def reached (path : Path) (frame : ReplayCases.Frame) :=
  (frame.data.offers[2]!).any (fun a => a.demand && observesPoint path a)

def coldOne := step 1 emptyFrame readerMethods [] [] true
def coldTwo := step 2 coldOne.1 readerMethods [] [] true
def coldThree := step 3 coldTwo.1 readerMethods [] [] true

theorem cold_runs_exhibit_the_root_candidate_and_reverse_source_permission :
    coldOne.2.1 = true ∧ reached [] coldOne.1 = true ∧
    coldTwo.2.1 = true ∧ reached [] coldTwo.1 = true ∧
    coldThree.2.1 = true ∧ reached [] coldThree.1 = true := by decide

def negativeProof (base lead after src obs : Path) : Bool :=
  let g : List PairedContext.Rule :=
    [.base 0 base, .nested 0 [2] 0 [], .nested 0 lead 0 after]
  match RegularSearch.compile 1 (RegularSearch.grammar ([1] ++ src) [[2]]) with
  | some automaton => PairedContext.check g 1 automaton obs
  | none => false

def certificateRound : IO Unit := do
  let mut total := 0
  let mut failed := 0
  for lead in RegularSearch.paths 2 do
    for after in RegularSearch.paths 2 do
      for base in [[],[1],[2]] do
        for outerSuffix in [[],[1]] do
          for otherBase in [[1],[2],[1,2]] do
            let rules : List PairedContext.Rule := [.base 0 base, .nested 0 lead 0 after]
            if let some automaton := RegularSearch.compile 1 (RegularSearch.grammar otherBase [[2]]) then
              let stateCount := (PairedContext.states automaton).length
              let words := (List.range (stateCount*stateCount+1)).map fun count =>
                (List.replicate count lead).flatten ++ base ++
                  (List.replicate count after).flatten ++ outerSuffix
              -- Independent repeat-count oracle for [2]* · otherBase.
              let shared := words.any fun word =>
                word.length >= otherBase.length &&
                word.take (word.length-otherBase.length) == List.replicate (word.length-otherBase.length) 2 &&
                word.drop (word.length-otherBase.length) == otherBase
              if PairedContext.check rules 1 automaton outerSuffix == shared then
                failed := failed+1
              total := total+1
  IO.println s!"TWO_SIDED_CERTIFICATES total={total} disagreements={failed}"

def main (args : List String) : IO UInt32 := do
  if args.contains "trace" then
    let result ← scan readerMethods [] [] (args.contains "repair") (if args.contains "repair" then 7 else 5) true
    IO.println s!"TWO_SIDED_TRACE {result}"
  else
    certificateRound
    let mut cases := 0
    let mut latest := 0
    let mut suspect := 0
    let mut missing := 0
    let mut unfinished := 0
    for base in [[1],[2],[3]] do
      for lead in [[2],[3]] do
        for after in [[1],[2],[3]] do
          for (src,obs) in [([],[]),([],[1]),([1],[]),([],[2])] do
            let noRoute := negativeProof base lead after src obs
            let first ← scan (readerMethods base lead after) src obs noRoute 7
            let result ← if first.1 == 0 && first.2.2.1 then
              scan (readerMethods base lead after) src obs noRoute 11
              else pure first
            cases := cases+1
            latest := max latest result.1
            if result.1 == 0 || !result.2.2.1 then
              unfinished := unfinished+1
              IO.println s!"UNFINISHED base={base} reads={lead}/{after} point={src}/{obs} certificate={noRoute} result={result}"
            if !noRoute && !result.2.1 then
              missing := missing+1
              IO.println s!"MISSING base={base} reads={lead}/{after} point={src}/{obs} result={result}"
            if noRoute && result.2.1 then suspect := suspect+1
    IO.println s!"TWO_SIDED_SEARCH total={cases} latestNatural={latest} unfinished={unfinished} noRouteWithNormal={suspect} possibleWithoutNormal={missing}"
  return 0
end TwoSidedSearch
def main := TwoSidedSearch.main
