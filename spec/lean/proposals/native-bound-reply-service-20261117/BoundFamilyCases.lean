import BoundFamily
namespace BoundFamilyCases
open NonEmptyPolicy NonEmptyRestriction AlternatingCondition BoundFamily
set_option maxRecDepth 65536
set_option maxHeartbeats 640000000
def cases : List Config := Id.run do
  let mut out := []
  for sourcePath in [[f],[f,g],[f,g,g]] do
    for sourceTail in [Tail.exact,Tail.must] do
      for targetTail in [Tail.exact,Tail.must] do
        for changeMark in [false,true] do
          for depth in [2,3,4] do
            for calls in [1,2,3] do
              let guardPath := [f] ++ List.replicate (depth-1) g
              out := out ++ [⟨sourcePath,sourceTail,[],false,guardPath,[3],.must,
                                [3,f,g],targetTail,changeMark,calls⟩]
  -- Hole, inherited protection, sibling, and disjoint-result controls.
  for sourceE in [[],[g],[3]] do
    for sourceH in [false,true] do
      for target in [[3,f,g],[3,3],[4]] do
        for changeMark in [false,true] do
          out := out ++ [⟨[f],.must,sourceE,sourceH,[f,g,g],[3],.must,
                            target,.must,changeMark,3⟩]
  return out

def concreteOutcome (cfg : Config) : List Value :=
  (List.range cfg.calls).foldl (fun incoming _ =>
    (incoming.flatMap fun v => colors cfg |>.flatMap fun m =>
      (gen cfg m ⟨v.ap,false⟩).map fun c => {c with ap:={c.ap with base:=p},h:=c.h || v.h}).filterMap consumeH)
    [originalSource cfg]


def checked (cfg : Config) : Bool :=
  let result := history cfg true 9
  stopped 9 result && result.report == !(concreteOutcome cfg).isEmpty

def chunk (n : Nat) : List Config := (cases.drop (12*n)).take 12

theorem exact_finite_scope : cases.length=252 := by decide +kernel
end BoundFamilyCases
