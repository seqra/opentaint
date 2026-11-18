import RegularSearch
namespace PairedSearch
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle NestedColdMachine RegularCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000000

def scan (wb rb : Word) (prefixes : List Word) : Nat × Bool × Bool:=Id.run do
  let mut prev : ReplayCases.Frame:=⟨{},[[],[]],[[],[]]⟩
  let mut allowed:=true
  let mut known:=false
  let mut normalSeen:=false
  let mut fixed:=true
  let noRoute:=match RegularSearch.compile 1 (RegularSearch.grammar wb prefixes),
      RegularSearch.compile 1 (RegularSearch.grammar rb prefixes) with
    | some w,some r=>certifiesEmpty w r
    | _,_=>false
  for index in List.range 25 do
    let run:=index+1
    let (next,ready,_):=PairedReference.step run prev false false allowed wb rb prefixes
    fixed:=fixed && ready
    let values:=next.data.offers[2]!
    if run%2==1 then
      let normal:=values.any fun a=> !a.demand && PairedReference.observed a
      let raw:=values.any fun a=>a.demand && PairedReference.observed a
      let target:=raw && !known
      known:=known || noRoute || normal
      normalSeen:=normalSeen || normal
      if next.rows.all List.isEmpty && !target then return (run,normalSeen,fixed)
      allowed:=target
    else
      allowed:=allowed && values.any PairedReference.observed
    prev:=next
  return (0,normalSeen,fixed)

def main : IO Unit:=do
  let mut cases:=0
  let mut failed:=0
  let mut latest:=0
  for wb in [[1],[2],[1,3],[2,3]] do
   for rb in [[1],[2],[1,3],[2,3]] do
    for prefixes in [[[2]],[[2],[3]]] do
      let result:=scan wb rb prefixes
      cases:=cases+1
      latest:=max latest result.1
      -- Distinct terminal symbols/chunks here are disjoint, equal ones
      -- have the zero-recursion base witness. Prefixes use 2/3 only.
      let expected:=wb==rb
      if result.1==0 || result.2.1 != expected || !result.2.2 then
        failed:=failed+1
        IO.println s!"GAP wb={wb} rb={rb} prefixes={prefixes} result={result} expected={expected}"
  IO.println s!"PAIRED_SEARCH total={cases} failed={failed} latestNaturalRun={latest}"
  IO.println s!"LONG_SHARED result={scan [1] [2,2,2,2,2,2,1] [[2,2]]}"
end PairedSearch
