import NestedCleanerProtocol
namespace CleanerSearch
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
set_option maxRecDepth 32768
set_option maxHeartbeats 240000000
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

inductive Reach where | exact | all | below
  deriving DecidableEq, BEq, Repr
structure Cleaner where
  path : Path
  reach : Reach
  deriving DecidableEq, BEq, Repr

-- One scalar mark on one local. No FLOW or other-mark branch is changed.
-- E always belongs to the incoming head, not a descendant head.
def clean (run k : Nat) (cl : Cleaner) (c : Value) : List Value :=
  let keep:={c with h:=true}
  let uncertain:={keep with demand:=true,ap:={c.ap with tail:=if c.ap.tail==.star then .may else c.ap.tail}}
  if cl.reach==.exact && c.ap.tail==.must then [keep] else
  match dropHead cl.path c.ap.path with
  | some []=>
    match cl.reach with
    | .all=>[]
    | .exact=>if c.ap.tail==.exact then [] else if c.ap.tail==.ne then [keep] else [uncertain]
    | .below=>if c.ap.tail==.ne then [] else [cut k {keep with ap:={c.ap with tail:=.exact,e:=[]}}]
  | some (_::_)=>if cl.reach==.exact then [keep] else []
  | none=>match dropHead c.ap.path cl.path with
    | some (first::_)=>
      if c.ap.tail==.exact || c.ap.e.contains first then [keep]
      else if c.ap.tail==.must && !c.demand && run != 1 && cl.reach != .exact then
        (UniformCleanerSpine.regions (if cl.reach==.all then .all else .below)
          (cl.path.drop c.ap.path.length) c.ap.e).map (fun r=>cut k (NestedCleanerProtocol.valueOf c r))
      else [uncertain]
    | _=>[keep]

-- A possible intersection of two AP regions; it never uses a JVM type.
def overlap (a b : Ap) : Bool :=
  if a.path==b.path then
    !((a.tail==.exact && b.tail==.ne) || (b.tail==.exact && a.tail==.ne))
  else match dropHead a.path b.path with
  | some (field::_)=>a.tail != .exact && !a.e.contains field
  | _=>match dropHead b.path a.path with
    | some (field::_)=>b.tail != .exact && !b.e.contains field
    | _=>false

def values (run k : Nat) (source : Value) (cs : List Cleaner) : List Value :=
  cs.foldl (fun packet cl=>packet.flatMap (clean run k cl)) [cut k source]
def backward (k : Nat) (observation : Ap) (cs : List Cleaner) : List Value :=
  cs.reverse.foldl (fun packet cl=>packet.flatMap (clean 2 k cl)) [cut k ⟨observation,true,false⟩]

structure Step where
  demand : Bool := false
  normal : Bool := false
  sourcePermission : Bool := false
  deriving DecidableEq, BEq, Repr

-- Main has only ZERO/Target control demands. DATA does not start an owned
-- query. Both witnesses count: NORMAL does not silently cancel DEMAND.
def forward (run k : Nat) (source : Value) (cs : List Cleaner) (obs : Ap) : Step :=
  let hits:=(values run k source cs).filter (fun c=>overlap c.ap obs)
  ⟨hits.any (·.demand),hits.any (fun c=> !c.demand),false⟩
def back (k : Nat) (source : Value) (cs : List Cleaner) (obs : Ap) : Step :=
  let yes:=(backward k obs cs).any (fun c=>overlap c.ap source.ap)
  ⟨yes,false,yes⟩

-- Independent membership oracle: the selected EXACT/MUST contract keeps
-- the uniform input, while whole/BELOW cleaners delete their true region.
def selectedOracle (source : Value) (cs : List Cleaner) (word : Path) : Bool :=
  let start:=match dropHead source.ap.path word with
    | none=>false
    | some rest=>if source.ap.tail==.exact then rest.isEmpty
      else ExclusionChildCover.permits source.ap.e rest
  let result:=cs.foldl (fun state cl=>
    let (alive,uniform):=state
    match dropHead cl.path word with
    | none=>state
    | some rest=>match cl.reach with
      | .exact=>if rest.isEmpty && !uniform then (false,uniform) else state
      | .all=>(false,uniform)
      | .below=>if rest.isEmpty then (alive,false) else (false,uniform)) (start,source.ap.tail==.must)
  result.1

-- Required observations use actual point deletion, not the accepted
-- MUST/EXACT coarsening. That coarsening can add a NORMAL observation;
-- its absence is not loss of a real retained marked point.
def requiredWord (source : Value) (cs : List Cleaner) (word : Path) : Bool :=
  let start:=match dropHead source.ap.path word with
    | none=>false
    | some rest=>if source.ap.tail==.exact then rest.isEmpty
      else ExclusionChildCover.permits source.ap.e rest
  cs.foldl (fun alive cl=>alive &&
    match dropHead cl.path word with
    | none=>true
    | some rest=>match cl.reach with
      | .exact=> !rest.isEmpty
      | .all=>false
      | .below=>rest.isEmpty) start

def words : Nat → List Path
  | 0=>[[]]
  | n+1=>[]::(words n).flatMap (fun tail=>[1::tail,2::tail])

theorem this_reference_never_uses_unbounded_initials (s : Value) (cs : List Cleaner) :
    values 1 1 s cs=cs.foldl (fun packet cl=>packet.flatMap (clean 1 1 cl)) [cut 1 s] := rfl

-- All normality and set-difference checks below run in the Lean evaluator.
-- They supplement the symbolic spine/protocol proofs; they are not a
-- universal proof or a native hard-limit argument.
def main : IO Unit := do
  let sources:=(words 2).flatMap fun path=>
    [⟨ap 20 path .exact (some 3),false,false⟩,
     ⟨ap 20 path .must (some 3),false,false⟩,
     ⟨{ap 20 path .must (some 3) with e:=[1]},false,false⟩,
     ⟨{ap 20 path .must (some 3) with e:=[2]},false,false⟩]
  let cleaners:=(words 3).flatMap fun path=>[Cleaner.mk path .exact,⟨path,.all⟩,⟨path,.below⟩]
  let observations:=(words 3).flatMap fun path=>[ap 20 path .exact (some 3),ap 20 path .may (some 3),ap 20 path .ne (some 3)]
  let mut pipelines:=0
  let mut cases:=0
  let mut failures:=0
  let mut latest:=0
  let mut maxRows:=0
  for source in sources do
   for first in cleaners do
    for second in cleaners do
     let cs:=[first,second]
     pipelines:=pipelines+1
     let precise:=values 5 4 source cs
     let requiredPoints:=(words 5).filter (requiredWord source cs)
     maxRows:=max maxRows precise.length
     -- Two cleaner paths of length <=3 cannot need more than seven pieces.
     if precise.any (·.demand) || precise.length>7 then
       IO.println s!"GAP NORMAL {reprStr source} {reprStr cs} {reprStr precise}"
       failures:=failures+1
     for word in words 5 do
       let actual:=precise.any fun c=>match dropHead c.ap.path word with
         | none=>false
         | some rest=>if c.ap.tail==.exact then rest.isEmpty else ExclusionChildCover.permits c.ap.e rest
       if actual != selectedOracle source cs word then
         IO.println s!"GAP MEMBERSHIP {reprStr source} {reprStr cs} {reprStr word} actual={actual}"
         failures:=failures+1
     for obs in observations do
       cases:=cases+1
       let mut step:=forward 1 1 source cs obs
       let mut stopped:=if step.demand then 0 else 1
       let mut normal:=step.normal
       for run in [2,3,4,5] do
        if stopped==0 then
         if run%2==0 then step:=back (max 1 (run-1)) source cs obs
         else step:=if step.sourcePermission then forward run (run-1) source cs obs else {}
         normal:=normal || step.normal
         if !step.demand then stopped:=run
       latest:=max latest stopped
       -- Check every actual retained point in the explicit witness bound,
       -- for EXACT and broad MAY/NE observations alike.
       let expected:=requiredPoints.any fun word=>match dropHead obs.path word with
         | none=>false
         | some suffix=>if obs.tail==.exact then suffix.isEmpty
           else if obs.tail==.ne then !suffix.isEmpty else true
       if stopped==0 || (expected && !normal) then
         IO.println s!"GAP TRACE {reprStr source} {reprStr cs} {reprStr obs} stopped={stopped} normal={normal}"
         failures:=failures+1
     if failures>8 then
       IO.println s!"EARLY pipelines={pipelines} cases={cases} failures={failures}"
       return
  IO.println s!"CLEANERS pipelines={pipelines} cases={cases} failures={failures} latestNaturalRun={latest} maxRows={maxRows}"
end CleanerSearch
