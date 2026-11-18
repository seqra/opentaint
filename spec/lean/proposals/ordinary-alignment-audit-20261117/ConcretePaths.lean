import MaskHandoff
namespace ConcretePaths
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def f : Nat := 1
def g : Nat := 2
def p : Nat := 0
def t : Nat := 7
def ap (path : Path) (tail : Tail) : Ap := ⟨p,path,tail,some t,[],[]⟩
def value (path : Path) (tail : Tail) : Value := ⟨ap path tail,false,false⟩

def move (read write : Path) (v : Value) : Option Value :=
  (OverwriteReplay.move read write v.ap).map fun w =>
    {w with demand:=w.demand || v.demand,h:=v.h}

def source165 : Value := value [g] .must

def choose165 (v : Value) : Option Value := do
  let r←move [f] [f] v
  -- First branch writes y.g after producing y.f. That write cannot touch f.
  PointWriteReplay.keep 3 [] g r

def wrap165 (v : Value) : Option Value := do
  let a←move [g,g] [] v
  let b←choose165 a
  move [] [g,g] b

-- Reduced witness: no branch and no strong keep is used at all.
def wrapMinimal (v : Value) : Option Value := do
  let a←move [g,g] [] v
  let b←move [f] [f] a
  move [] [g,g] b

theorem source165_first_concrete_route_is_NORMAL :
    wrap165 source165=some (value [g,g,f] .must) := by decide +kernel

theorem source165_second_concrete_route_is_NORMAL :
    (wrap165 source165 >>= wrap165)=some (value [g,g,f] .must) := by decide +kernel

def source884 : Value := value [f,g,g] .exact

def choose884 (v : Value) : Option Value := do
  let a←move [g,f,g] [] v
  move [] [f,g] a

def wrap884 (v : Value) : List Value :=
  -- Exact parallel strong-keep transfer for x.f.f.g = new Node().
  (PointWriteReplay.nestedWrite 3 100 [f,f,g] [] v).filterMap fun kept => do
    let a←move [f] [] kept
    let b←move [] [g,f] a
    choose884 b

theorem source884_first_concrete_route_is_NORMAL :
    wrap884 source884=[source884] := by decide +kernel

theorem source884_second_concrete_route_is_NORMAL :
    (wrap884 source884).flatMap wrap884=[source884] := by decide +kernel

theorem both_witnesses_have_a_definite_observed_point :
    admits .must [] []=true ∧ admits .exact [] []=true ∧
    (value [g,g,f] .must).demand=false ∧ source884.demand=false := by decide +kernel

end ConcretePaths
