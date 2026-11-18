import UpdatedReplay
namespace ReplayCases
open NonEmptyPolicy NonEmptyRestriction
open NestedSavedReplayCycle NestedColdMachine
open ConcretePaths
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000

abbrev Op:=UpdatedReplay.Op
abbrev Method:=UpdatedReplay.Method

def read (path : Path) : List Op:=path.map fun f => .move [f] []
def write (path : Path) : List Op:=path.reverse.map fun f => .move [] [f]

def methods165 : List Method :=
  [[read [g,g] ++ [UpdatedReplay.Op.call 1] ++ write [g,g]],
   [read [f] ++ write [f] ++ [UpdatedReplay.Op.overwrite g],
    [UpdatedReplay.Op.overwrite g] ++ read [f,g,f] ++ write [f,f] ++ [UpdatedReplay.Op.overwrite f]]]

def methods884 : List Method :=
  [[[UpdatedReplay.Op.nestedWrite [f,f,g]] ++ read [f] ++ write [g,f] ++ [UpdatedReplay.Op.call 1],
    [UpdatedReplay.Op.nestedWrite [g,f,f]] ++ read [g,f] ++ write [g] ++ [UpdatedReplay.Op.call 1]],
   [read [g,f,g] ++ write [f,g],
    [UpdatedReplay.Op.nestedWrite [f,g,g]] ++ read [g,f,g] ++ write [f,g] ++ [UpdatedReplay.Op.nestedWrite [f,g,f]]]]

def methodsMinimal : List Method :=
  [[read [g,g] ++ [UpdatedReplay.Op.call 1] ++ write [g,g]],
   [read [f] ++ write [f]]]

def source165 : Offered:=⟨point AcyclicMayCycle.p [g] .must (some AcyclicMayCycle.t),false⟩
def source884 : Offered:=⟨point AcyclicMayCycle.p [f,g,g] .exact (some AcyclicMayCycle.t),false⟩

def endpoint (a : Ap) : Ap :=
  {a with e:=[],mx:=[],tail:=if a.tail==.must then .may else a.tail}

def handoff (st : State) : List (List Row) := st.current.map fun es =>
  (es.filterMap fun e => if e.2.demand then
    some ⟨{endpoint e.2.ap with base:=AcyclicMayCycle.p},
          {endpoint e.1 with base:=AcyclicMayCycle.ret}⟩ else none).eraseDups

structure Frame where
  data : State
  rows : List (List Row)
  saved : List (List Saved)
  deriving Repr

def history (methods : List Method) (source : Offered) (calls : Nat := 2) : Nat → Frame
  | 0 => ⟨{},[[],[]],[[],[]]⟩
  | n+1 =>
    let prev:=history methods source calls n
    let st:=UpdatedReplay.rounds 12 (n+1) (max 1 n) calls methods prev.rows prev.saved source
    ⟨st,handoff st,OverwriteReplay.outputSaved (n+1) prev.saved st⟩

def describe (methods : List Method) (source : Offered) (calls : Nat := 2) : IO Unit := do
  for n in List.range 7 do
    let run:=n+1
    let prev:=history methods source calls n
    let st:=history methods source calls run
    let fixed:=decide (UpdatedReplay.round run (max 1 n) calls methods prev.rows prev.saved st.data=st.data)
    IO.println s!"RUN {run} fixed={fixed}\n{reprStr st}"

end ReplayCases
