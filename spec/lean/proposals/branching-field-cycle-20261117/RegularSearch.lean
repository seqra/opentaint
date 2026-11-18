import RegularRepair
namespace RegularSearch
open RegularCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000000

def compile (owners : Nat) (grammar : List Clause) : Option Nfa:=Id.run do
  if owners==0 || grammar.any (fun c=>c.owner≥owners || c.callee.any (·≥owners)) then return none
  let finish:=owners
  let mut fresh:=owners+1
  let mut finals:=[finish]
  let mut arcs:=[]
  for c in grammar do
    if c.chunk.isEmpty then
      if c.callee.isNone then finals:=c.owner::finals
      else if c.callee != some c.owner then return none
    else
      let mut origin:=c.owner
      for i in List.range c.chunk.length do
        let target:=if i+1==c.chunk.length then c.callee.getD finish else fresh
        if i+1!=c.chunk.length then fresh:=fresh+1
        arcs:=(origin,c.chunk[i]!,target)::arcs
        origin:=target
  let result : Nfa:=⟨0,finals.eraseDups,arcs.eraseDups⟩
  return if grammar.all (validatesClause result) then some result else none

def grammar (base : Word) (cycleWord : List Word) : List Clause:=
  ⟨0,base,none⟩::cycleWord.map fun word=>⟨0,word,some 0⟩
def paths : Nat → List Word
 | 0=>[[]]
 | n+1=>[]::(paths n).flatMap fun p=>[1::p,2::p]
def unaryWords (cycleWord base : Word) (bound : Nat) : List Word:=
  (List.range (bound+1)).map fun n=>(List.replicate n cycleWord).flatten++base

def unaryCase (wp rp wb rb : Word) : Bool × Nat:=
  match compile 1 (grammar wb [wp]),compile 1 (grammar rb [rp]) with
  | some w,some r=>
    let bound:=(w.arcs.length+2)*(r.arcs.length+2)
    let left:=unaryWords wp wb bound
    let right:=unaryWords rp rb bound
    let overlap:=left.any right.contains
    (certifiesEmpty w r == !overlap,(scan w r).length)
  | _,_=>(false,0)

-- General finite compiler validation plus independent unary word witnesses.
-- All words up to the product-state shortest-path bound are represented by
-- one repetition count each; no alphabet-power word enumeration is used.
def main : IO Unit:=do
  let mut unary:=0
  let mut branching:=0
  let mut failed:=0
  let mut largestProduct:=0
  for wp in (paths 3).filter (fun p=> !p.isEmpty) do
   for rp in (paths 3).filter (fun p=> !p.isEmpty) do
    for wb in paths 2 do
     for rb in paths 2 do
      unary:=unary+1
      let (ok,size):=unaryCase wp rp wb rb
      largestProduct:=max largestProduct size
      if !ok then
        failed:=failed+1
        IO.println s!"GAP unary write={wp}/{wb} read={rp}/{rb}"
  -- Branching generators in either language, mutual recursion and nullable
  -- base paths. The known terminal/parity schemas have exact expectations.
  let choices:=[[[1]],[[2]],[[1],[2]],[[1,1],[2,2]],[[1,2],[2,1]]]
  for wchoices in choices do
   for rchoices in choices do
    for lastW in [3,4] do
     for lastR in [3,4] do
      let wg:=grammar [lastW] wchoices
      let rg:=grammar [lastR] rchoices
      match compile 1 wg,compile 1 rg with
      | some w,some r=>
        branching:=branching+1
        let expected:=lastW != lastR
        if certifiesEmpty w r != expected then failed:=failed+1
      | _,_=>failed:=failed+1
  IO.println s!"REGULAR_SEARCH unary={unary} branching={branching} failed={failed} largestVisitedProduct={largestProduct}"
end RegularSearch
