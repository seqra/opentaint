import DirectedAlias.Impl.CfgCheck
import DirectedAlias.Impl.CfgLive

/-!
# Examples of the CFG certificate

Each analysis answer comes from the solver `solveCfg`, which returns a certificate only if the
checker `postFixB` accepts it; so each true answer is sound by `solveMay_sound`. The checks use
`decide +kernel` with `K = 1`. Each real alias has a direct concrete execution (`Reach`).

* (a) `loopEntry`: a loop whose head is the ENTRY node (a back edge to the first instruction),
  with a strong store in the body. The solver finds the real alias. A simulator that ignores the
  back edge (as `CompactGraphSimulator` of main does) answers false, and its result is not a
  post-fixpoint of the CFG (the checker rejects it).
* (b) `catchCase` (item 7): `e = new; throw e`, handler `c = catch; c.f = v; t = e.f`. The real
  alias `t ~ v` is MISSED by the compact-spec catch rule (`T h = []`); the certificate passes every
  check but the throw condition. With `T h ⊇ pts(e)` the alias is found.
* (c) `nested`: nested loops with two heads.
* (d) `inlined`: a callee spliced into the caller; the callee writes `this.f = a` strongly and
  then throws; the caller handler reads `x.f`; the real alias `t ~ a` is found.
* (9) `constReuse`: two constant reads of one key share a site; the reuse alias is found.
* (8) `liveSpec`: the liveness rule of the brief admits a kill that loses a real alias of two
  live variables at a handler; the fixed rule rejects the kill.
-/

namespace DirectedAlias.Impl.Cfg.Examples

open DirectedAlias DirectedAlias.Impl.Cfg DirectedAlias.Sound.ValueSem

/-- The guard that accepts every origin. -/
def gu : Origin → Bool := fun _ => true

/-- The empty frame. -/
def frE : Frame := ⟨[]⟩

/-- The frame where variable 0 holds root 0 and variable 1 holds root 1. -/
def frXV : Frame := ⟨[(0, 0), (1, 1)]⟩

/-- The frame where variable 2 holds root 0. -/
def frV : Frame := ⟨[(2, 0)]⟩

/-! ## (a) A loop whose head is the entry node -/

/-- `0: t = x.f; 1: x.f = v` (strong), back edge `1 → 0`, exit `1 → 2`. Variables: `x = 0`,
`v = 1`, `t = 2`; field `f = 0`. -/
def gLoop : Cfg :=
  ⟨[⟨.stmt (.load 2 0 0), [1], [], []⟩, ⟨.stmt (.store 0 0 1), [0, 2], [], []⟩,
    ⟨.nop, [], [], []⟩], 0⟩

/-- The same CFG without the back edge to the entry (what a simulator that ignores it sees). -/
def gLoopSim : Cfg :=
  ⟨[⟨.stmt (.load 2 0 0), [1], [], []⟩, ⟨.stmt (.store 0 0 1), [2], [], []⟩,
    ⟨.nop, [], [], []⟩], 0⟩

/-- The real alias `t ~ v` before the store, in the second iteration. -/
theorem loopEntry_real (src : Nat → Obj × Cell) :
    ∃ vs e, Reach src [] gLoop frXV ⟨1, vs, e⟩ ∧ AliasInV vs 2 [] 1 [] :=
  ⟨_, _, .step (.step (.step .init
    (.norm (w := 1) rfl (by decide) (.stmt (.load (o := .sym (.root 0) []) rfl))))
    (.norm (w := 0) rfl (by decide) (.stmt (.store (o := .sym (.root 0) []) rfl rfl))))
    (.norm (w := 1) rfl (by decide) (.stmt (.load (o := .sym (.root 0) []) rfl))),
    .obj (.sym (.root 1) []), by decide, by decide⟩

/-- LOOP AT THE ENTRY: the solver (head: the entry node) finds `t ~ v` before the store; without
the back edge the answer is false; and the result without the back edge is not a post-fixpoint
of the CFG. -/
theorem loopEntry_answers :
    solveMay true 1 [] frXV gLoop gu [0] 20 1 2 [] 1 [] = true ∧
      solveMay true 1 [] frXV gLoopSim gu [0] 20 1 2 [] 1 [] = false ∧
      (solveCfg (cfgCtx true 1 [] frXV gLoopSim []) gu gLoopSim frXV [0] 20).map
        (fun C => postFixB (cfgCtx true 1 [] frXV gLoop []) gu gLoop frXV C.sb C.sa C.tt) =
        some false := by
  decide +kernel

/-! ## (b) The catch case (item 7) -/

/-- `0: e = new@1; 1: throw e` (handler 2); `2: c = catch@3; 3: c.f = v; 4: t = e.f; 5: nop`.
Variables: `e = 0`, `c = 1`, `v = 2`, `t = 3`; field `f = 0`. -/
def gCatch : Cfg :=
  ⟨[⟨.stmt (.new 0 1), [1], [], []⟩, ⟨.thr 0, [], [2], []⟩, ⟨.cat 1 3, [3], [], []⟩,
    ⟨.stmt (.store 1 0 2), [4], [], []⟩, ⟨.stmt (.load 3 0 0), [5], [], []⟩,
    ⟨.nop, [], [], []⟩], 0⟩

/-- THE REAL ALIAS `t ~ v`: the catch gets the thrown object `e`, so `c.f = v` writes `e.f`. -/
theorem catch_real (src : Nat → Obj × Cell) :
    ∃ vs e, Reach src [] gCatch frV ⟨5, vs, e⟩ ∧ AliasInV vs 3 [] 2 [] :=
  ⟨_, _, .step (.step (.step (.step (.step .init
    (.norm (w := 1) rfl (by decide) (.stmt .new)))
    (.exc (h := 2) rfl (by decide) (.thr (o := .alloc 1 0) rfl)))
    (.norm (w := 3) rfl (by decide) .catP))
    (.norm (w := 4) rfl (by decide) (.stmt (.store (o := .alloc 1 0) rfl rfl))))
    (.norm (w := 5) rfl (by decide) (.stmt (.load (o := .alloc 1 0) rfl))),
    .obj (.sym (.root 0) []), by decide, by decide⟩

/-- THE COMPACT-SPEC CATCH RULE MISSES THE REAL ALIAS: with `T h = []` (a catch variable is only
the result origin `⟨s⟩`), the solver gives a certificate that passes every condition of `PostFix`
except the throw condition, has no thrown values, and answers `t ~ v` false. -/
theorem catch_spec_misses :
    (solveCfg (cfgCtx true 1 [] frV gCatch []) gu gCatch frV [] 20 false false).map
        (fun C => (postFixB (cfgCtx true 1 [] frV gCatch []) gu gCatch frV C.sb C.sa C.tt false,
          postFixB (cfgCtx true 1 [] frV gCatch []) gu gCatch frV C.sb C.sa C.tt true,
          (List.range 6).all (fun h => decide (C.tt h = [])),
          may (C.sb 5) 3 [] 2 [])) =
      some (true, false, true, false) := by
  decide +kernel

/-- THE FIX FINDS THE ALIAS: with `T h ⊇ pts(e)` (the throw condition of `PostFix`), the solver
answers `t ~ v` true. -/
theorem catch_fixed_finds : solveMay true 1 [] frV gCatch gu [] 20 5 3 [] 2 [] = true := by
  decide +kernel

/-! ## (c) Nested loops -/

/-- `0: a = new@1` (outer head); `1: b = new@2` (inner head); `2: a.f = b` (back edge to 1);
`3: c = a.f` (back edge to 0); `4: nop`. Variables: `a = 0`, `b = 1`, `c = 2`. -/
def gNest : Cfg :=
  ⟨[⟨.stmt (.new 0 1), [1], [], []⟩, ⟨.stmt (.new 1 2), [2], [], []⟩,
    ⟨.stmt (.store 0 0 1), [1, 3], [], []⟩, ⟨.stmt (.load 2 0 0), [0, 4], [], []⟩,
    ⟨.nop, [], [], []⟩], 0⟩

/-- The real alias `c ~ b` at the exit. -/
theorem nested_real (src : Nat → Obj × Cell) :
    ∃ vs e, Reach src [] gNest frE ⟨4, vs, e⟩ ∧ AliasInV vs 2 [] 1 [] :=
  ⟨_, _, .step (.step (.step (.step .init
    (.norm (w := 1) rfl (by decide) (.stmt .new)))
    (.norm (w := 2) rfl (by decide) (.stmt .new)))
    (.norm (w := 3) rfl (by decide) (.stmt (.store (o := .alloc 1 0) rfl rfl))))
    (.norm (w := 4) rfl (by decide) (.stmt (.load (o := .alloc 1 0) rfl))),
    .obj (.alloc 2 0), by decide, by decide⟩

/-- NESTED LOOPS: the solver (heads 0 and 1) finds `c ~ b` and answers `c ~ a` false. -/
theorem nested_answers :
    solveMay true 1 [] frE gNest gu [0, 1] 30 4 2 [] 1 [] = true ∧
      solveMay true 1 [] frE gNest gu [0, 1] 30 4 2 [] 0 [] = false := by
  decide +kernel

/-! ## (d) An inlined callee -/

/-- The callee `this' = x; this'.f = a; ex = new@7; throw ex`, spliced into the caller; each
callee node has an exceptional edge to the caller handler `4: h = catch@8`; then `5: t = x.f`.
Variables: `x = 0`, `a = 1`, `this' = 10`, `ex = 11`, `h = 12`, `t = 13`. -/
def gInl : Cfg :=
  ⟨[⟨.stmt (.copy 10 0), [1], [4], []⟩, ⟨.stmt (.store 10 0 1), [2], [4], []⟩,
    ⟨.stmt (.new 11 7), [3], [4], []⟩, ⟨.thr 11, [], [4], []⟩, ⟨.cat 12 8, [5], [], []⟩,
    ⟨.stmt (.load 13 0 0), [6], [], []⟩, ⟨.nop, [], [], []⟩], 0⟩

/-- The real alias `t ~ a` after the handler. -/
theorem inlined_real (src : Nat → Obj × Cell) :
    ∃ vs e, Reach src [] gInl frXV ⟨6, vs, e⟩ ∧ AliasInV vs 13 [] 1 [] :=
  ⟨_, _, .step (.step (.step (.step (.step (.step .init
    (.norm (w := 1) rfl (by decide) (.stmt (.copy rfl))))
    (.norm (w := 2) rfl (by decide) (.stmt (.store (o := .sym (.root 0) []) rfl rfl))))
    (.norm (w := 3) rfl (by decide) (.stmt .new)))
    (.exc (h := 4) rfl (by decide) (.thr (o := .alloc 7 0) rfl)))
    (.norm (w := 5) rfl (by decide) .catP))
    (.norm (w := 6) rfl (by decide) (.stmt (.load (o := .sym (.root 0) []) rfl))),
    .obj (.sym (.root 1) []), by decide, by decide⟩

/-- INLINING: the solver finds `t ~ a` after the handler. -/
theorem inlined_answer : solveMay true 1 [] frXV gInl gu [] 30 6 13 [] 1 [] = true := by
  decide +kernel

/-! ## (9) Constants with reuse -/

/-- `0: x = const@7; 1: y = const@7; 2: nop` (one key, one shared site). Variables: `x = 0`,
`y = 1`. -/
def gConst : Cfg :=
  ⟨[⟨.cnst 0 7, [1], [], []⟩, ⟨.cnst 1 7, [2], [], []⟩, ⟨.nop, [], [], []⟩], 0⟩

/-- The real alias `x ~ y`: the second read reuses the object of the first read. -/
theorem const_real (src : Nat → Obj × Cell) :
    ∃ vs e, Reach src [] gConst frE ⟨2, vs, e⟩ ∧ AliasInV vs 0 [] 1 [] :=
  ⟨_, _, .step (.step .init
    (.norm (w := 1) rfl (by decide) (.cnstF .unknown)))
    (.norm (w := 2) rfl (by decide) (.cnstR (n := 0) (by decide))),
    .obj (.sym (.fresh 7 0) []), by decide, by decide⟩

/-- CONSTANTS: the shared site is not once, and the solver finds `x ~ y`. -/
theorem const_answers :
    gConst.onceB 7 = false ∧ solveMay true 1 [] frE gConst gu [] 20 2 0 [] 1 [] = true := by
  decide +kernel

/-- The constant guard: no strong store into an origin of the constant site 7 or below it. -/
def guardC : Origin → Bool
  | .sym (.fresh 7) _ => false
  | .deep (.fresh 7) => false
  | _ => true

/-- `0: x = const@7; 1: x.f = a; 2: x.f = b; 3: t = x.f; 4: nop` (one constant node, not on a
cycle, so its site is once). Variables: `x = 0`, `a = 1`, `b = 2`, `t = 3`. -/
def gConstStore : Cfg :=
  ⟨[⟨.cnst 0 7, [1], [], []⟩, ⟨.stmt (.store 0 0 1), [2], [], []⟩,
    ⟨.stmt (.store 0 0 2), [3], [], []⟩, ⟨.stmt (.load 3 0 0), [4], [], []⟩,
    ⟨.nop, [], [], []⟩], 0⟩

/-- The frame where variables 1 and 2 hold roots 1 and 2. -/
def frAB : Frame := ⟨[(1, 1), (2, 2)]⟩

/-- THE GUARD WORKS: without the guard the second store is strong and `t ~ a` is false; with the
constant guard both stores are weak and `t ~ a` is true. Both answers are sound for every guard
(`solveMay_sound`). -/
theorem guard_answers :
    gConstStore.onceB 7 = true ∧
      solveMay true 1 [] frAB gConstStore gu [] 20 4 3 [] 1 [] = false ∧
      solveMay true 1 [] frAB gConstStore guardC [] 20 4 3 [] 1 [] = true := by
  decide +kernel

/-! ## (8) The liveness rule of the brief is unsound -/

/-- `0: x = new@1; 1: y = x; 2: x = m()@2` (handler 3); `3: x.f = y; 4: nop`. Variables:
`x = 0`, `y = 1`. -/
def gL : Cfg :=
  ⟨[⟨.stmt (.new 0 1), [1], [], []⟩, ⟨.stmt (.copy 1 0), [2], [], []⟩,
    ⟨.stmt (.call (some 0) 2 []), [4], [3], []⟩, ⟨.stmt (.store 0 0 1), [4], [], []⟩,
    ⟨.nop, [], [], []⟩], 0⟩

/-- `gL` with the kill of `x` at the call node (the call writes `x`). -/
def gLk : Cfg :=
  ⟨[⟨.stmt (.new 0 1), [1], [], []⟩, ⟨.stmt (.copy 1 0), [2], [], []⟩,
    ⟨.stmt (.call (some 0) 2 []), [4], [3], [0]⟩, ⟨.stmt (.store 0 0 1), [4], [], []⟩,
    ⟨.nop, [], [], []⟩], 0⟩

/-- The live variables by the rule of the brief: at the call, `x` is written, so it is removed
also from the live variables of the handler. -/
def liveS : Nat → List Var
  | 1 => [0]
  | 2 => [1]
  | 3 => [0, 1]
  | _ => []

/-- The live variables by the fixed rule: the handler's live variables are all live at the call. -/
def liveF : Nat → List Var
  | 1 => [0]
  | 2 => [0, 1]
  | 3 => [0, 1]
  | _ => []

/-- `gLk` is `gL` with kills. -/
theorem gLk_ext : KillExt gL gLk :=
  ⟨rfl, by decide, noKill_of_all (by decide)⟩

/-- The real alias `x ~ y` at the handler: the call throws before it writes `x`. -/
theorem live_real (src : Nat → Obj × Cell) :
    ∃ vs e, Reach src [] gL frE ⟨3, vs, e⟩ ∧ AliasInV vs 0 [] 1 [] :=
  ⟨_, _, .step (.step (.step .init
    (.norm (w := 1) rfl (by decide) (.stmt .new)))
    (.norm (w := 2) rfl (by decide) (.stmt (.copy rfl))))
    (.exc (h := 3) rfl (by decide) .none),
    .obj (.alloc 1 0), by decide, by decide⟩

/-- The checks of the liveness example: the rule of the brief holds for `liveS` and admits the
kill; the fixed rule rejects `liveS`, holds for `liveF`, and rejects the kill; the solver on the
CFG with the kill succeeds and answers `x ~ y` false at the handler. -/
theorem live_checks :
    liveOKSpecB gL liveS = true ∧ killOKB gLk liveS = true ∧ liveOKB gL liveS = false ∧
      liveOKB gL liveF = true ∧ killOKB gLk liveF = false ∧
      (solveCfg (cfgCtx true 1 [] frE gLk (afields ([] : List ACell) ++ afields ([] : List ACell)))
        gu gLk frE [] 20 true true).isSome = true ∧
      solveMay true 1 [] frE gLk gu [] 20 3 0 [] 1 [] = false := by
  decide +kernel

/-- THE LIVENESS RULE OF THE BRIEF IS UNSOUND: it holds, it admits the kill of `x` at the call,
`x` and `y` are live at the handler and alias there in a real execution of `gL`, but no
execution of the CFG with the kill has this alias at the handler. -/
theorem live_spec_unsound (src : Nat → Obj × Cell) :
    LiveOKSpec gL liveS ∧ KillExt gL gLk ∧ KillOK gLk liveS ∧ 0 ∈ liveS 3 ∧ 1 ∈ liveS 3 ∧
      (∃ vs e, Reach src [] gL frE ⟨3, vs, e⟩ ∧ AliasInV vs 0 [] 1 []) ∧
      ¬ ∃ vs e, Reach src [] gLk frE ⟨3, vs, e⟩ ∧ AliasInV vs 0 [] 1 [] := by
  obtain ⟨h1, h2, _, _, _, h6, h7⟩ := live_checks
  refine ⟨liveOKSpecB_sound h1, gLk_ext, killOKB_sound h2, by decide, by decide, live_real src, ?_⟩
  rintro ⟨vs, e, hr, ha⟩
  have := solveMay_sound src [] true 1 frE gLk gu [] 20 3 0 [] 1 [] true h6 hr ha
  have h8 : solveMay true 1 [] frE gLk gu [] 20 3 0 (([] : List Cell).map Cell.abs) 1
      (([] : List Cell).map Cell.abs) true true = false := h7
  rw [h8] at this
  cases this

/-- The fixed liveness rule holds for `liveF` (so `csoundKill` applies to each CFG with kills that
`liveF` admits; the kill of `x` at the call is not admitted). -/
theorem live_fixed_sound : LiveOK gL liveF := liveOKB_sound (live_checks.2.2.2.1)

end DirectedAlias.Impl.Cfg.Examples
