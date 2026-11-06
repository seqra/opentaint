import DirectedAlias.Sound.ValueSem.Examples
import DirectedAlias.Sound.ValueSem.StaticsExamples
import DirectedAlias.Sound.ValueSem.BackwardEq
import DirectedAlias.Opt.ValueSem
import DirectedAlias.Opt.ValueSemCost
import DirectedAlias.Opt.ValueSemStatics
import DirectedAlias.Opt.Query
import DirectedAlias.Impl.CfgExamples
import DirectedAlias.Impl.CfgEngineExamples

/-!
# Test vectors of design VS for the Kotlin engine (IMPL §9.1 item 1)

The library does not import this file. It prints one line for each query of the design VS
examples (`hv=vs`), with the answer of the Lean function of the example theorem. `#eval` is data
export: it adds no theorem, and the axiom audit of `check.sh` does not read this file.

Run: `lake env lean Export/Vectors.lean > <file>`. The committed copy is the test resource
`lean-vectors.txt` of `LeanVectorTest` (module `opentaint-jvm-dataflow`).

Each `V` and `F` line of a structured program has the fields of design doc §10.1:

```
V <name> | K=<k> eu=<0|1> rec=1 hv=vs | statics=<roots> | frame=<var>:<root>,... | prog=<prog> | q=<path>~<path> | may=<true|false>
F <name> | K=<k> eu=<0|1> rec=1 hv=vs | statics=<roots> | frame=... | prog=<prog> | var=<x> | D=<d> | paths=<list> | plain=<list>
```

A CFG example has `cfg=<cfg>` and `at=<node>` in place of `prog=` (an extension of the format).
The answer is the may-alias in the state before node `at` of the CFG solver `solveMay`, with the
compact catch rule (`useT = false`, `chkT = false`: a catch variable is only `⟨s⟩`, as the engine
does, I2), unless the name says `useT`.

Syntax:
* `<prog>`: `skip`, `(seq P Q)`, `(choice P Q)`, `(loop P)`, or a statement: `(new x s)`,
  `(null x)`, `(copy x y)`, `(load x y f)`, `(store x f y)`, `(aload x y)`, `(astore x y)`,
  `(unknown x s)`, `(call r s a1 ... an)` (`r` is `_` for no result).
* `<cfg>`: `(cfg <entry> <node> ...)`, node `v` is the `v`-th node. `<node>`:
  `(node <instr> (<succ> ...) (<exc> ...) (<kill> ...))`. `<instr>`: a statement, `(nop)`,
  `(thr y)`, `(cat x s)` (catch at site `s`), `(cnst x s)` (a constant of the key of site `s`).
* `<path>`: a variable and its cells: `3.0.*` is `v3.f0[*]`.
* `paths`: the paths of Lean `findAlias` (`Opt/Query.lean`) of `var` with depth `D`, sorted, the
  reserved variables of the sets removed. `plain`: the subset of the paths that reach an origin
  of `var` with no deep summary on the way (the engine search never follows the self cells of a
  deep summary, spec §5.7, and it keeps only the depth-K origins of its tables as parents of a
  deep summary; so only these paths must be in the engine answer, and the engine answer must be
  in `paths`).
-/

namespace DirectedAlias.Export

open DirectedAlias DirectedAlias.Sound DirectedAlias.Sound.CellNamed DirectedAlias.Sound.BlockOnly
open DirectedAlias.Sound.ValueSem DirectedAlias.Opt DirectedAlias.Impl.Cfg

/-! ## Text -/

def cellS : ACell → String
  | .fld f => toString f
  | .elem => "*"

def pathS (x : Var) (p : List ACell) : String :=
  toString x ++ String.join (p.map (fun c => "." ++ cellS c))

def optS : Option Var → String
  | none => "_"
  | some x => toString x

def stmtS : Stmt → String
  | .new x s => s!"(new {x} {s})"
  | .null x => s!"(null {x})"
  | .copy x y => s!"(copy {x} {y})"
  | .load x y f => s!"(load {x} {y} {f})"
  | .store x f y => s!"(store {x} {f} {y})"
  | .aload x y => s!"(aload {x} {y})"
  | .astore x y => s!"(astore {x} {y})"
  | .unknown x s => s!"(unknown {x} {s})"
  | .call r s args => "(call " ++ optS r ++ " " ++ toString s ++
      String.join (args.map (fun a => " " ++ toString a)) ++ ")"

def progS : Prog → String
  | .skip => "skip"
  | .stmt st => stmtS st
  | .seq p q => "(seq " ++ progS p ++ " " ++ progS q ++ ")"
  | .choice p q => "(choice " ++ progS p ++ " " ++ progS q ++ ")"
  | .loop p => "(loop " ++ progS p ++ ")"

def natsS (l : List Nat) : String := " ".intercalate (l.map toString)

def instrS : Instr → String
  | .stmt st => stmtS st
  | .nop => "(nop)"
  | .thr y => s!"(thr {y})"
  | .cat x s => s!"(cat {x} {s})"
  | .cnst x s => s!"(cnst {x} {s})"

def nodeS (nd : Impl.Cfg.Node) : String :=
  "(node " ++ instrS nd.instr ++ " (" ++ natsS nd.succ ++ ") (" ++ natsS nd.exc ++ ") (" ++
    natsS nd.kills ++ "))"

def cfgS (g : Cfg) : String :=
  "(cfg " ++ toString g.entry ++ String.join (g.nodes.map (fun nd => " " ++ nodeS nd)) ++ ")"

def frameS (fr : Frame) : String := ",".intercalate (fr.binds.map (fun b => s!"{b.1}:{b.2}"))

def rootsS (l : List Root) : String := ",".intercalate (l.map toString)

def boolS (b : Bool) : String := if b then "1" else "0"

/-! ## Deep summaries and the plain paths -/

def isDeepO : Origin → Bool
  | .deep _ => true
  | .hdeep _ _ _ => true
  | _ => false

/-- Forward evaluation that drops the deep summaries at each step. -/
def plainFrom (X : AState) : List Origin → List ACell → List Origin
  | S, [] => S.filter (fun o => !isDeepO o)
  | S, c :: cs => plainFrom X ((aread X (S.filter (fun o => !isDeepO o)) c)) cs

/-- The answer of Lean `findAlias` without the reserved variables, and its plain subset. -/
def answerS (ctx : Ctx) (X : AState) (vars : List Var) (D : Nat) (x : Var) : String :=
  let all := (findAlias ctx X D x).filter (fun vp => vars.contains vp.1)
  let plain := all.filter (fun vp => meetB (plainFrom X (X.env vp.1) vp.2) (plainFrom X (X.env x) []))
  let txt := fun (l : List (Var × List ACell)) =>
    ",".intercalate ((l.map (fun vp => pathS vp.1 vp.2)).eraseDups.mergeSort (fun a b => decide (a ≤ b)))
  "paths=" ++ txt all ++ " | plain=" ++ txt plain

/-! ## Structured programs -/

/-- A query of a structured program. `prog` is the program that the engine runs (the stripped
program of design VSS); `may` is the answer of the Lean function of the theorem. -/
structure PV where
  name : String
  eu : Bool
  K : Nat
  statics : List Root
  fr : Frame
  prog : Prog
  x : Var
  px : List ACell
  y : Var
  py : List ACell
  may : Bool

def vs (name : String) (eu : Bool) (K : Nat) (st : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : PV :=
  ⟨name, eu, K, st, fr, p, x, px, y, py, mayProgVS eu K st fr p x px y py⟩

def vso (name : String) (eu : Bool) (K : Nat) (st : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : PV :=
  ⟨name, eu, K, st, fr, p, x, px, y, py, Opt.ValueSem.mayProgVSO eu K st fr p x px y py⟩

def vss (name : String) (eu : Bool) (K : Nat) (st : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : PV :=
  ⟨name, eu, K, st, fr, stripStatic (shB st fr) p, x, px, y, py, mayProgVSS eu K st fr p x px y py⟩

def vsso (name : String) (eu : Bool) (K : Nat) (st : List Root) (fr : Frame) (p : Prog)
    (x : Var) (px : List ACell) (y : Var) (py : List ACell) : PV :=
  ⟨name, eu, K, st, fr, stripStatic (shB st fr) p, x, px, y, py,
    Opt.ValueSem.mayProgVSSO eu K st fr p x px y py⟩

def vsg (name : String) (eu : Bool) (K : Nat) (st : List Root) (fr : Frame) (gv : Var → Field → Var)
    (gs : List Var) (p : Prog) (x : Var) (px : List ACell) (y : Var) (py : List ACell) : PV :=
  ⟨name, eu, K, st, fr, StaticsExamples.stripStaticG (shB st fr) gv gs p, x, px, y, py,
    StaticsExamples.mayProgVSG eu K st fr gv gs p x px y py⟩

def headS (v : PV) : String :=
  s!"K={v.K} eu={boolS v.eu} rec=1 hv=vs | statics={rootsS v.statics} | frame={frameS v.fr} | prog={progS v.prog}"

def lineV (v : PV) : String :=
  s!"V {v.name} | {headS v} | q={pathS v.x v.px}~{pathS v.y v.py} | may={v.may}"

/-- The `F` line of variable `x` of the program of `v`, depth `D`. -/
def lineF (v : PV) (x : Var) (D : Nat) : String :=
  let cb := ctxVS v.eu v.K v.statics v.fr v.prog []
  let X := analyzeProgVS v.eu v.K v.statics v.fr v.prog []
  let vars := BlockOnly.progVars v.fr v.prog
  s!"F {v.name}.find{x} | {headS v} | var={x} | D={D} | {answerS cb.cn.ctx X vars D x}"

section vsExamples

open DirectedAlias.Sound.ValueSem.Examples

section user
open U

def userV : List PV := [
  vs "user_answers.1" true 0 [] frE pUser va [] vx [.fld ff],
  vs "user_answers.2" true 1 [] frE pUser va [] vx [.fld ff],
  vs "user_answers.3" false 1 [] frE pUser va [] vx [.fld ff],
  vs "user_answers.4" true 1 [] frE pUserCall va [] vx [.fld ff]]

end user

section need
open DirectedAlias.HavocNeed

def needV : List PV := [
  vs "empty_answersVS.1" true 0 [] fr pEmpty va [] vb [],
  vs "empty_answersVS.2" true 1 [] fr pEmpty va [] vb [],
  vs "empty_answersVS.3" false 1 [] fr pEmpty va [] vb [],
  vs "strong_answersVS.1" true 0 [] fr pStrong vw [.fld fg] ve [],
  vs "strong_answersVS.2" true 1 [] fr pStrong vw [.fld fg] ve []]

end need

section unsound
open DirectedAlias.Sound.BlockOnly.Unsound

def unsoundV : List PV := [
  vs "bo0_cases_VS.1" true 0 [] frU pJoinBug vt [] vx [.fld ff],
  vs "bo0_cases_VS.2" true 1 [] frU pJoinBug vt [] vx [.fld ff],
  vs "bo0_cases_VS.3" false 0 [] frU pJoinBug vt [] vx [.fld ff],
  vs "bo0_cases_VS.4" true 0 [] frU pLoopBug vt [] vx [.fld ff],
  vs "bo0_cases_VS.5" true 1 [] frU pLoopBug vt [] vx [.fld ff],
  vs "bo0_cases_VS.6" false 0 [] frU pLoopBug vt [] vx [.fld ff],
  vs "bo0_cases_VS.7" true 1 [] frS pSymBug vt [] vx [.fld ff]]

end unsound

section nulls
open U

def nullsV : List PV := [
  vs "nullStore_answers.1" true 0 [] frX pNullStore va [] vb [],
  vs "nullStore_answers.2" true 1 [] frX pNullStore va [] vb [],
  vs "nullStore_answers.3" false 1 [] frX pNullStore va [] vb [],
  vs "nulls_answers.1" true 1 [] frE pTwoNull va [] vb [],
  vs "nulls_answers.2" true 1 [] frE pTwoNew va [] vb [],
  vs "nulls_answers.3" true 1 [] frE pOneNull va [] vb []]

end nulls

section spread
open DirectedAlias.Examples DirectedAlias.Sound.Havoc.Examples

def spreadV : List PV := [
  vs "spread_goneVS.1" true 0 [] fr pHv va [] vb [],
  vs "spread_goneVS.2" true 0 [] fr pHv va [] vz [.fld ff],
  vs "spread_goneVS.3" true 0 [] fr pHv va [] vw [.fld fg],
  vs "spread_goneVS.4" true 0 [] fr pHv va [] vx [.fld ff],
  vs "spread_goneVS.5" false 0 [] fr pHv va [] vb [],
  vs "spread_goneVS.6" true 1 [] fr pHv va [] vb [],
  vs "other_answersVS.1" true 2 [] fr pJoin va [] vx [],
  vs "other_answersVS.2" true 2 [] fr pJoin va [] vy [],
  vs "other_answersVS.3" true 2 [] fr pJoin vx [] vy [],
  vs "other_answersVS.4" true 1 [] fr pField vx [.fld ff] vz [],
  vs "other_answersVS.5" true 1 [] fr pField vy [.fld ff] vz [],
  vs "other_answersVS.6" true 1 [] fr pField vx [] vy [],
  vs "other_answersVS.7" true 1 [] fr pField va [] vx [],
  vs "other_answersVS.8" true 1 [] fr pField va [] vw [],
  vs "other_answersVS.9" true 1 [] fr pStrong vb [.fld ff] vx [],
  vs "other_answersVS.10" true 1 [] fr pStrong vb [.fld ff] vy [],
  vs "other_answersVS.11" true 1 [] fr pCall vw [] vx [.fld ff],
  vs "loop_bf_x_VS.1" true 1 [] fr pLoop vb [.fld ff] vx [],
  vs "loop_bf_x_VS.2" false 1 [] fr pLoop vb [.fld ff] vx [],
  vs "loop_bf_x_VS.3" true 1 [] fr pLoop vb [.fld ff] vy []]

end spread

section cn
open DirectedAlias.Sound.CellNamed.Examples DirectedAlias.Sound.BlockOnly.Examples

def cnV : List PV := [
  vs "dead_answerVS.1" true 0 [] frN pDead vb [] vd [],
  vs "dead_answerVS.2" true 1 [] frN pDead vb [] vd [],
  vs "gain_answersVS.1" true 1 [] frN (pGain []) vt [.fld fg] vu [],
  vs "gain_answersVS.2" true 1 [5] frN (pGain []) vt [.fld fg] vu [],
  vs "gain_answersVS.3" true 1 [] frN (pGain [vx]) vt [.fld fg] vu [],
  vs "gain_answersVS.4" true 1 [0] frN (pGain []) vt [.fld fg] vu [],
  vs "traceC_answerVS.1" true 0 [] frN pC va [] vb [],
  vs "traceC_answerVS.2" true 1 [] frN pC va [] vb [],
  vs "traceC_answerVS.3" true 2 [] frN pC va [] vb [],
  vs "eval_answerVS.1" true 0 [] frN pE vn [.fld fg] vy [],
  vs "eval_answerVS.2" true 1 [] frN pE vn [.fld fg] vy [],
  vs "eval_answerVS.3" false 1 [] frN pE vn [.fld fg] vy [],
  vs "losses_VS.1" true 1 [] frN pL1 vt [.fld fg] vu [],
  vs "losses_VS.2" true 0 [] frN pL2 vt [] vw [],
  vs "losses_VS.3" true 1 [] frN pL2 vt [] vw [],
  vs "losses_VS.4" true 0 [] frN pL3 va [] vc [],
  vs "losses_VS.5" true 1 [] frN pL3 va [] vc [],
  vs "losses_VS.6" true 0 [] frN pL4 vy [.fld fg] vu [],
  vs "losses_VS.7" true 1 [] frN pL4 vy [.fld fg] vu []]

end cn

section siteless
open U

def sitelessV : List PV := [
  vs "siteless_unsound.1" true 1 [] frE pSiteless va [] vb [],
  vs "siteless_unsound.4" true 1 [] frE pSited va [] vb []]

end siteless

end vsExamples

section statics
open DirectedAlias.Sound.ValueSem.StaticsExamples

def staticsV : List PV := [
  vss "answers68.1" true 1 sts fr p68 vt [] vu [],
  vss "answers68.2" true 1 sts fr p68 vt [] vv [],
  vss "answers68.3" false 1 sts fr p68 vt [] vu [],
  vss "answers68.4" false 1 sts fr p68 vt [] vv [],
  vss "answers68.5" true 2 sts fr p68 vt [] vv [],
  vs "answers68.6" true 1 sts fr p68 vt [] vv [],
  vss "strong68.2" true 1 sts fr p68e ve [] vt [.fld fg],
  vss "strong68.3" true 1 sts fr p68w ve [] vt [.fld fg],
  vss "weak68.1" true 1 sts fr p68 vu [.fld fg] vz [],
  vss "weak68.2" true 1 sts fr p68 vu [.fld fg] vw [],
  vss "weak68.3" true 1 sts fr p68r vt [.fld fg] vz [],
  vss "weak68.4" true 1 sts fr p68r vu [.fld fg] vw [],
  vss "gapA.1" true 1 sts fr pGapA vt [] vv [],
  vs "gapA.4" true 1 sts fr pGapA vt [] vv [],
  vss "gapB.1" true 1 sts fr pGapB ve [.fld fg] vd [],
  vss "gapB.2" true 2 sts fr pGapB ve [.fld fg] vd [],
  vs "gapB.5" true 1 sts fr pGapB ve [.fld fg] vd [],
  vsg "option_answers.1" true 1 sts fr (fun _ _ => 20) [20] pGapB ve [.fld fg] vd [],
  vsg "option_answers.2" true 1 sts fr (fun _ _ => 20) [20] p68 vt [] vu [],
  vsg "option_answers.3" true 1 sts fr (fun _ _ => 20) [20] p68 vt [] vv [],
  vsg "option_answers.4" true 1 sts fr (fun _ _ => 20) [20] pGapA vt [] vv [],
  vsso "o_answersVSS.1" true 1 sts fr p68 vt [] vu [],
  vsso "o_answersVSS.2" true 1 sts fr p68 vt [] vv [],
  vsso "o_answersVSS.3" true 1 sts fr pGapA vt [] vv [],
  vsso "o_answersVSS.4" true 1 sts fr pGapB ve [.fld fg] vd []]

end statics

section bw
open DirectedAlias.Sound.ValueSem.BWExamples

def bwV : List PV := [
  vs "bw_needs_distinct_sites.1" true 1 [] frR pRep vt [] vx [.fld fg]]

end bw

section opt
open DirectedAlias.Sound.ValueSem.Examples DirectedAlias.Opt.ValueSem

def optV : List PV := [
  vso "o_answersVS.1" true 1 [] U.frE pUser U.va [] U.vx [.fld U.ff],
  vso "o_answersVS.2" true 1 [] U.frX pNullStore U.va [] U.vb [],
  vso "o_answersVS.3" true 1 [] U.frE pTwoNull U.va [] U.vb [],
  vso "o_answersVS.4" true 1 [] U.frE pTwoNew U.va [] U.vb []]

/-- The queries of `added_answers`: each query of `readQueries` and of `nullQueries`. -/
def addedV : List PV :=
  (readQueries.zip (List.range readQueries.length)).map (fun (q, i) =>
    vs s!"added_answers.reads.{i + 1}" true 1 [] U.frE pReads q.1 q.2.1 q.2.2.1 q.2.2.2) ++
  (nullQueries.zip (List.range nullQueries.length)).map (fun (q, i) =>
    vs s!"added_answers.nulls.{i + 1}" true 1 [] U.frE pNulls q.1 q.2.1 q.2.2.1 q.2.2.2)

end opt

def allPV : List PV :=
  userV ++ needV ++ unsoundV ++ nullsV ++ spreadV ++ cnV ++ sitelessV ++ staticsV ++ bwV ++ optV ++
    addedV

/-- One `F` line for each variable of the queries of each program, with `D = 2`. The first query
of a program (by name prefix and parameters) gives its program. -/
def allF : List String :=
  let keys := allPV.foldl (fun (acc : List (PV × List Var)) v =>
    match acc.find? (fun e => e.1.eu == v.eu && e.1.K == v.K && e.1.statics == v.statics &&
        e.1.fr == v.fr && e.1.prog == v.prog) with
    | some _ => acc.map (fun e =>
        if e.1.eu == v.eu && e.1.K == v.K && e.1.statics == v.statics && e.1.fr == v.fr &&
            e.1.prog == v.prog then (e.1, uni [v.x, v.y] e.2) else e)
    | none => acc ++ [(v, [v.x, v.y].eraseDups)]) []
  keys.flatMap (fun e => (e.2.mergeSort (fun a b => decide (a ≤ b))).map (fun x => lineF e.1 x 2))

/-! ## CFG examples -/

/-- A query of a CFG example: the may-alias before node `at` of the solver `solveMay`. -/
structure CV where
  name : String
  K : Nat
  fr : Frame
  g : Cfg
  guard : Origin → Bool
  heads : List Nat
  fuel : Nat
  node : Nat
  x : Var
  px : List ACell
  y : Var
  py : List ACell
  useT : Bool

def CV.may (v : CV) : Bool :=
  solveMay true v.K [] v.fr v.g v.guard v.heads v.fuel v.node v.x v.px v.y v.py v.useT v.useT

def cheadS (v : CV) : String :=
  s!"K={v.K} eu=1 rec=1 hv=vs | statics= | frame={frameS v.fr} | cfg={cfgS v.g} | at={v.node}"

def lineCV (v : CV) : String :=
  s!"V {v.name} | {cheadS v} | q={pathS v.x v.px}~{pathS v.y v.py} | may={v.may}"

/-- The `F` line of variable `x` before node `at`, depth `D`. -/
def lineCF (v : CV) (x : Var) (D : Nat) : String :=
  let cb := cfgCtx true v.K [] v.fr v.g []
  let vars := BlockOnly.progVars v.fr v.g.prog
  match solveCfg cb v.guard v.g v.fr v.heads v.fuel v.useT v.useT with
  | some C => s!"F {v.name}.find{x} | {cheadS v} | var={x} | D={D} | {answerS cb.cn.ctx (C.sb v.node) vars D x}"
  | none => s!"F {v.name}.find{x} | {cheadS v} | var={x} | D={D} | paths=none | plain=none"

section cfgs
open DirectedAlias.Impl.Cfg.Examples

/-- The CFG queries. A constant node needs the guard of the engine: no strong update into an
origin of a constant site (the engine origin of a constant is never unique). -/
def cfgV : List CV := [
  ⟨"loopEntry_answers.1", 1, frXV, gLoop, gu, [0], 20, 1, 2, [], 1, [], false⟩,
  ⟨"loopEntry_answers.2", 1, frXV, gLoopSim, gu, [0], 20, 1, 2, [], 1, [], false⟩,
  ⟨"catch_gap.3", 1, frV, gCatch, gu, [], 20, 5, 3, [], 2, [], false⟩,
  ⟨"catchA6_answer.2.useT", 1, frV, gCatch.a6, gu, [], 20, 5, 3, [], 2, [], true⟩,
  ⟨"nested_answers.1", 1, frE, gNest, gu, [0, 1], 30, 4, 2, [], 1, [], false⟩,
  ⟨"nested_answers.2", 1, frE, gNest, gu, [0, 1], 30, 4, 2, [], 0, [], false⟩,
  ⟨"inlined_answer", 1, frXV, gInl, gu, [], 30, 6, 13, [], 1, [], false⟩,
  ⟨"const_answers.2", 1, frE, gConst, guardC, [], 20, 2, 0, [], 1, [], false⟩,
  ⟨"guard_answers.3", 1, frAB, gConstStore, guardC, [], 20, 4, 3, [], 1, [], false⟩,
  ⟨"box_guard.3", 1, frAB, gBox, guardBox, [], 20, 4, 3, [], 1, [], false⟩,
  ⟨"box_key.2", 1, frE, gBoxKey, guardBox, [], 20, 3, 0, [], 1, [], false⟩,
  ⟨"box_key.3", 1, frE, gBoxKey, guardBox, [], 20, 3, 0, [], 2, [], false⟩,
  ⟨"live_real.solver", 1, frE, gL, gu, [], 20, 3, 0, [], 1, [], false⟩]

end cfgs

def allCF : List String :=
  let keys := cfgV.foldl (fun (acc : List (CV × List Var)) v =>
    match acc.find? (fun e => e.1.name.takeWhile (· ≠ '.') == v.name.takeWhile (· ≠ '.') &&
        e.1.g == v.g && e.1.node == v.node) with
    | some _ => acc.map (fun e =>
        if e.1.name.takeWhile (· ≠ '.') == v.name.takeWhile (· ≠ '.') && e.1.g == v.g &&
            e.1.node == v.node then (e.1, uni [v.x, v.y] e.2) else e)
    | none => acc ++ [(v, [v.x, v.y].eraseDups)]) []
  keys.flatMap (fun e => (e.2.mergeSort (fun a b => decide (a ≤ b))).map (fun x => lineCF e.1 x 2))

end DirectedAlias.Export

open DirectedAlias.Export in
#eval do
  IO.println "# Lean vectors of design VS (formal/directed-alias/Export/Vectors.lean). Do not edit."
  IO.println "# Regenerate: cd formal/directed-alias && lake env lean Export/Vectors.lean > <this file>"
  IO.println "# Format: see the header of Export/Vectors.lean. V: may-alias at the end of `prog` or before"
  IO.println "# node `at` of `cfg`. F: Lean findAlias of `var` with depth D (`paths`) and its plain subset."
  for v in allPV do IO.println (lineV v)
  for l in allF do IO.println l
  for v in cfgV do IO.println (lineCV v)
  for l in allCF do IO.println l
