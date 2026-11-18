import DirectPossibleReplay
namespace RepairCases
open NonEmptyPolicy NonEmptyRestriction NestedSavedReplayCycle NestedColdMachine
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000
abbrev Frame := ReplayCases.Frame

def step (methods : List DirectPossibleReplay.Method) (source : Offered) (calls n : Nat) (prev : Frame) : Frame :=
  let st:=DirectPossibleReplay.rounds 16 (n+1) (max 1 n) calls methods prev.rows prev.saved source
  ⟨st,ReplayCases.handoff st,OverwriteReplay.outputSaved (n+1) prev.saved st⟩

def convertOp : UpdatedReplay.Op → DirectPossibleReplay.Op
  | .call n => .call n
  | .move r w => .move r w
  | .overwrite f => .overwrite f
  | .nestedWrite path => .nestedWrite path

def convert (ms : List UpdatedReplay.Method) : List DirectPossibleReplay.Method := ms.map (fun m=>m.map (List.map convertOp))

def history (methods : List UpdatedReplay.Method) (source : Offered) (calls : Nat) : Nat → Frame
  | 0 => ⟨{},[[],[]],[[],[]]⟩
  | n+1 => step (convert methods) source calls n (history methods source calls n)

end RepairCases
