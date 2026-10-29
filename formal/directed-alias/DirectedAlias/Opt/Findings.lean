import DirectedAlias.Opt.QueryFam

/-!
# Optimization O, part 10: findings (executable checks of the limits of the design)

* The map part of the O state is linear on the state family (`fam_osize`), but the shared node
  table is not: a right-nested join chain of `m + 1` allocations makes `m` union nodes with the
  sizes `2 .. m + 1`. The table content grows as `m^2 / 2` (`chain_table`). The node count
  (the DAG view) grows as `2 m + 1`.
* The O fixpoint test is not always one id comparison for each key. If the body gives a strict
  subset of the loop state with a new id, the test union is a new pair: a memo miss
  (`test_miss`).
-/

namespace DirectedAlias.Opt.Findings

open DirectedAlias DirectedAlias.Opt

/-- For the chain of 17 allocations, the table has 33 nodes with 169 set elements in total. -/
theorem chain_table :
    (analyzeProgO 1 fr0 (fam 0 16) []).1.nodes.length = 33 ∧
      ((analyzeProgO 1 fr0 (fam 0 16) []).1.nodes.map (fun n => n.set.length)).sum = 169 := by
  decide +kernel

/-- The program before the loop: `a := new 0 | new 2; b := new 1`. -/
def pPre : Prog := .seq (.choice (.stmt (.new 0 0)) (.stmt (.new 0 2))) (.stmt (.new 1 1))

/-- The program: `pPre; loop { b := a }`. -/
def pMiss : Prog := .seq pPre (.loop (.stmt (.copy 1 0)))

/-- In `pMiss`, the loop adds two memo entries: one in the first iteration and one in the test
iteration, where the body gives `b = {a0, a2}`, a strict subset of the loop state
`b = {a0, a1, a2}`. -/
theorem test_miss :
    let ctx := progCtx 1 fr0 pMiss []
    let i := initO ctx fr0
    let a := analyzeO ctx pPre i.1 i.2
    a.1.memo.length = 1 ∧
      (analyzeO ctx (.loop (.stmt (.copy 1 0))) a.1 a.2).1.memo.length = 3 := by
  decide +kernel

end DirectedAlias.Opt.Findings
