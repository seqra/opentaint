import DirectedAlias.Impl.CfgEngine
import DirectedAlias.Impl.CfgExamples

/-!
# Examples of the A6 corollary and of the box rule

* A6 on `gCatch` (`e = new; throw e` → handler `c = catch; c.f = v; t = e.f`): the spec answer
  `t ~ v` false is EXACT for the A6 semantics (no A6 execution has the alias), and the alias is
  real in the original semantics (`catch_real`). So the gap of the spec catch rule is exactly
  the local throw (`catch_gap`).
* Boxes (user decision 3): a box of a constant argument is a constant of the key
  (type, argument): one shared site per key (`cnst`). A box of a non-constant argument has its
  own per-site origin (`cnst` with the site of the box statement) that is never unique (the
  guard `guardBox`). `box_guard`: on a once node the per-site box gets no strong update with the
  guard (it gets one without). `box_key`: two box sites of one constant key share the origin and
  the alias is found; a different key has a different origin.
-/

namespace DirectedAlias.Impl.Cfg.Examples

open DirectedAlias DirectedAlias.Impl.Cfg DirectedAlias.Sound.ValueSem

/-! ## A6 on the catch case -/

/-- The A6 answer for `gCatch`: the solver on the A6 CFG succeeds and answers `t ~ v` false at
node 5. -/
theorem catchA6_answer :
    (solveCfg (cfgCtx true 1 [] frV gCatch.a6 (afields ([] : List ACell) ++ afields ([] : List ACell)))
      gu gCatch.a6 frV [] 20 true true).isSome = true ∧
      solveMay true 1 [] frV gCatch.a6 gu [] 20 5 3 [] 2 [] = false := by
  decide +kernel

/-- THE SPEC ANSWER IS EXACT FOR A6: no A6 execution of `gCatch` has `t ~ v` at node 5. -/
theorem catchA6_exact (src : Nat → Obj × Cell) :
    ¬ ∃ vs e, Reach src [] gCatch.a6 frV ⟨5, vs, e⟩ ∧ AliasInV vs 3 [] 2 [] := by
  rintro ⟨vs, e, hr, ha⟩
  have := solveMay_sound src [] true 1 frV gCatch.a6 gu [] 20 5 3 [] 2 [] true
    catchA6_answer.1 hr ha
  have h8 : solveMay true 1 [] frV gCatch.a6 gu [] 20 5 3 (([] : List Cell).map Cell.abs) 2
      (([] : List Cell).map Cell.abs) true true = false := catchA6_answer.2
  rw [h8] at this
  cases this

/-- THE GAP IS EXACTLY THE LOCAL THROW: the original semantics of `gCatch` has `t ~ v` at node 5,
the A6 semantics does not, and the spec rule answers false. -/
theorem catch_gap (src : Nat → Obj × Cell) :
    (∃ vs e, Reach src [] gCatch frV ⟨5, vs, e⟩ ∧ AliasInV vs 3 [] 2 []) ∧
      (¬ ∃ vs e, Reach src [] gCatch.a6 frV ⟨5, vs, e⟩ ∧ AliasInV vs 3 [] 2 []) ∧
      solveMay true 1 [] frV gCatch gu [] 20 5 3 [] 2 [] false false = false :=
  ⟨catch_real src, catchA6_exact src, by decide +kernel⟩

/-! ## Boxes -/

/-- The engine guard: no strong update into a constant or box origin (sites 9, 20, 21) or below
it. -/
def guardBox : Origin → Bool
  | .sym (.fresh s) _ => !(s = 9 || s = 20 || s = 21)
  | .deep (.fresh s) => !(s = 9 || s = 20 || s = 21)
  | _ => true

/-- `0: b = box(n)@9` (non-constant argument, per-site origin); `1: b.f = a; 2: b.f = c;
3: t = b.f; 4: nop`. Variables: `b = 0`, `a = 1`, `c = 2`, `t = 3`. -/
def gBox : Cfg :=
  ⟨[⟨.cnst 0 9, [1], [], []⟩, ⟨.stmt (.store 0 0 1), [2], [], []⟩,
    ⟨.stmt (.store 0 0 2), [3], [], []⟩, ⟨.stmt (.load 3 0 0), [4], [], []⟩,
    ⟨.nop, [], [], []⟩], 0⟩

/-- THE PER-SITE BOX GETS NO STRONG UPDATE WITH THE GUARD: the box site is once, the second store
is strong without the guard (`t ~ a` false) and weak with it (`t ~ a` true). -/
theorem box_guard :
    gBox.onceB 9 = true ∧
      solveMay true 1 [] frAB gBox gu [] 20 4 3 [] 1 [] = false ∧
      solveMay true 1 [] frAB gBox guardBox [] 20 4 3 [] 1 [] = true := by
  decide +kernel

/-- `0: x = box(5)` and `1: y = box(5)` (key `(Integer, 5)`, shared site 20); `2: z = box(6)`
(key `(Integer, 6)`, site 21); `3: nop`. Variables: `x = 0`, `y = 1`, `z = 2`. -/
def gBoxKey : Cfg :=
  ⟨[⟨.cnst 0 20, [1], [], []⟩, ⟨.cnst 1 20, [2], [], []⟩, ⟨.cnst 2 21, [3], [], []⟩,
    ⟨.nop, [], [], []⟩], 0⟩

/-- The real alias `x ~ y`: the second box of the key reuses the object of the first one. -/
theorem boxKey_real (src : Nat → Obj × Cell) :
    ∃ vs e, Reach src [] gBoxKey frE ⟨3, vs, e⟩ ∧ AliasInV vs 0 [] 1 [] :=
  ⟨_, _, .step (.step (.step .init
    (.norm (w := 1) rfl (by decide) (.cnstF .unknown)))
    (.norm (w := 2) rfl (by decide) (.cnstR (n := 0) (by decide))))
    (.norm (w := 3) rfl (by decide) (.cnstF .unknown)),
    .obj (.sym (.fresh 20 0) []), by decide, by decide⟩

/-- TWO BOX SITES OF ONE KEY SHARE THE ORIGIN: `x` and `y` both have the origin of site 20, the
alias is found, and the box of another key has another origin (`x ~ z` false). -/
theorem box_key :
    (solveCfg (cfgCtx true 1 [] frE gBoxKey []) guardBox gBoxKey frE [] 20).map
        (fun C => (decide ((C.sb 3).env 0 = [.sym (.fresh 20) []]),
          decide ((C.sb 3).env 1 = [.sym (.fresh 20) []]))) = some (true, true) ∧
      solveMay true 1 [] frE gBoxKey guardBox [] 20 3 0 [] 1 [] = true ∧
      solveMay true 1 [] frE gBoxKey guardBox [] 20 3 0 [] 2 [] = false := by
  decide +kernel

end DirectedAlias.Impl.Cfg.Examples
