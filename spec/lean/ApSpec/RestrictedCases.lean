/-
  ApSpec.RestrictedCases — test vectors and two counterexample programs for the
  restricted runs of `Restricted.lean`.

  Part 1: the emission table, the satisfaction and the restriction as vectors
          (checked by `decide`).
  Part 2: program 1, the EMISSION counterexample. A `*` added fact above the demand
          chain of the callee. The S rules find the real vulnerability. The U rules
          find no vulnerability (an invariant over the closure).
  Part 3: program 2, the RESTRICTION counterexample. A correlated `*` summary
          conclusion above `D-p`. `restrictS` keeps the edge and the vulnerability is
          found. `restrictU` drops the only summary and the vulnerability is lost.
  Parts 1-3 use the version-3 rules and the demands with the mark `*` (a `*` demand mark
  admits every mark, so `d.din.covers` holds on the round-3 witnesses).
  Part 1 also has the version-4 vectors: the mark-aware emission `emitM`, the meet `meetK`
  and the satisfaction `satO`.
  Part 4: programs 1 and 2 under the spec rules (`emitM`, `satI` since version 5, the AGREED
          restriction `restrictU`) with the demands of the backward run (concrete mark `T`).
          Both runs find the vulnerability, with no request. Every fact of the runs has the
          concrete mark `T`, so the two rows where `U` and `S` differ do not occur.
  Part 5: program 3, RECORD REUSE (the rule `retRec` applies a record by `sat` OR `applicable`).
          The run-1 record `(arg0,.,*,{},*) → (ret,.,*,{},*)` (`p3_run1_record`) applies to the
          caller fact `(arg0,.f,$,T)`, which does not satisfy it by `satI`, and gives `(r,.f,$,T)`
          in the normal layer (`p3_reuse`); the sink triggers on it (`p3_found_reuse`). Its
          exactness is `RMain.p3_reuse_exact`.
  Round 5: the programs have no cleaner and no type filter (`p1_no_clean`, `p1_no_filt`,
  `p2_no_clean`, `p2_no_filt`). So the field `filtPrefix` of `Program.WF` holds with no case,
  and the rules `clean`, `reqClean`, `filt` of `DR` add no object to the closures.
-/
import ApSpec.Restricted

namespace ApSpec.RCases
open ApSpec

/-- The `*` tail with the empty exclusion. -/
def st : Kind := .star (.set [])
/-- Every accessor counts for the field limit. -/
def cnt : Acc → Bool := fun _ => true

/-- An `Option` value that is `none` is not `some`. -/
theorem ne_some_of_eq_none {α : Type} {o : Option α} (h : o = none) {a : α} : o ≠ some a := by
  intro h'
  rw [h] at h'
  cases h'

/-- The value of `some` is in the list of the option. -/
theorem mem_toList_of_eq_some {α : Type} {o : Option α} {a : α} (h : o = some a) : a ∈ o.toList := by
  rw [h]
  exact List.Mem.head _

/-- A restriction by a demand edge without an exit pattern gives nothing. -/
theorem restrictWith_none {rc : AFact → PFact → Option AFact} {j : PFact} {g : AFact} {din : PFact}
    {g' : AFact} : restrictWith rc j g ⟨din, none⟩ ≠ some g' := by
  intro h
  change (none : Option AFact) = some g' at h
  cases h

/-! ## Part 1. Vectors -/

namespace Vec

def f : Acc := 1
def g : Acc := 2
def h : Acc := 3
def x : Acc := 4
def arg : Base := 3
def ret : Base := 4
def T : Mark := 1

/-- The demand entry pattern `(arg,.f,[any])`. -/
def dc : PFact := ⟨arg, [f], .any, .star⟩

/-! ### The emission table -/

-- apart from the demand chain: nothing
example : emitU dc ⟨arg, [g, h], st, .star⟩ = none := by decide
example : emitS dc ⟨arg, [g, h], st, .star⟩ = none := by decide
-- other base: nothing
example : emitU dc ⟨ret, [f], st, .star⟩ = none := by decide
example : emitS dc ⟨ret, [f], st, .star⟩ = none := by decide
-- below the demand chain: the chain and one accessor more
example : emitU dc ⟨arg, [f, g, x], st, .star⟩ = some ⟨arg, [f, g], st, .star⟩ := by decide
example : emitS dc ⟨arg, [f, g, x], st, .star⟩ = some ⟨arg, [f, g], st, .star⟩ := by decide
example : emitU dc ⟨arg, [f, g], .any, .conc T⟩ = some ⟨arg, [f, g], st, .star⟩ := by decide
example : emitS dc ⟨arg, [f, g], .any, .conc T⟩ = some ⟨arg, [f, g], st, .star⟩ := by decide
-- at the demand chain: the tail of the added fact
example : emitU dc ⟨arg, [f], .exact, .conc T⟩ = some ⟨arg, [f], .exact, .star⟩ := by decide
example : emitS dc ⟨arg, [f], .exact, .conc T⟩ = some ⟨arg, [f], .exact, .star⟩ := by decide
example : emitU dc ⟨arg, [f], .any, .star⟩ = some ⟨arg, [f], .any, .star⟩ := by decide
example : emitS dc ⟨arg, [f], .any, .star⟩ = some ⟨arg, [f], .any, .star⟩ := by decide
example : emitU dc ⟨arg, [f], st, .star⟩ = some ⟨arg, [f], st, .star⟩ := by decide
example : emitS dc ⟨arg, [f], st, .star⟩ = some ⟨arg, [f], st, .star⟩ := by decide
-- above the demand chain, `[any]`: the demand chain
example : emitU dc ⟨arg, [], .any, .star⟩ = some ⟨arg, [f], st, .star⟩ := by decide
example : emitS dc ⟨arg, [], .any, .star⟩ = some ⟨arg, [f], st, .star⟩ := by decide
-- above the demand chain, `$`: nothing
example : emitU dc ⟨arg, [], .exact, .star⟩ = none := by decide
example : emitS dc ⟨arg, [], .exact, .star⟩ = none := by decide
example : emitU dc ⟨arg, [], .exact, .conc T⟩ = none := by decide
example : emitS dc ⟨arg, [], .exact, .conc T⟩ = none := by decide
-- above the demand chain, `*`: THE ROW WHERE U AND S DIFFER
example : emitU dc ⟨arg, [], st, .star⟩ = none := by decide
example : emitS dc ⟨arg, [], st, .star⟩ = some ⟨arg, [f], st, .star⟩ := by decide
-- above the demand chain, `*` with an exclusion of `f`: nothing in both
example : emitU dc ⟨arg, [], .star (.set [f]), .star⟩ = none := by decide
example : emitS dc ⟨arg, [], .star (.set [f]), .star⟩ = none := by decide

/-! ### Satisfaction of the premise `(arg,.f,*)` -/

def jp : PFact := ⟨arg, [f], st, .star⟩

-- an `[any]` fact above the premise: satisfied in both
example : satU jp ⟨arg, [], .any, .star⟩ = true := by decide
example : satS jp ⟨arg, [], .any, .star⟩ = true := by decide
-- a `*` fact above the premise: only S
example : satU jp ⟨arg, [], st, .star⟩ = false := by decide
example : satS jp ⟨arg, [], st, .star⟩ = true := by decide
-- a `*` fact above the premise with an exclusion of `f`: not satisfied
example : satU jp ⟨arg, [], .star (.set [f]), .star⟩ = false := by decide
example : satS jp ⟨arg, [], .star (.set [f]), .star⟩ = false := by decide
-- a covered fact: satisfied in both
example : satU jp ⟨arg, [f, g], st, .star⟩ = true := by decide
example : satS jp ⟨arg, [f, g], st, .star⟩ = true := by decide
-- the premise mark `T` against the fact mark `*`: not satisfied
def jpT : PFact := ⟨arg, [f], st, .conc T⟩
example : satU jpT ⟨arg, [f], st, .star⟩ = false := by decide
example : satS jpT ⟨arg, [f], st, .star⟩ = false := by decide
example : satU jpT ⟨arg, [], .any, .star⟩ = false := by decide
example : satS jpT ⟨arg, [], .any, .star⟩ = false := by decide
example : satS jpT ⟨arg, [], st, .star⟩ = false := by decide

/-! ### Restriction of a summary edge `j → g` by the demand edge `d`

  The demand edge of the user's example: the backward edge `(ret,.f,*) → (arg,.g,[any])`.
  In forward orientation `D-c = (arg,.g,[any])` and `D-p = (ret,.f,*)`. -/

def d : DemandEdge := ⟨⟨arg, [g], .any, .star⟩, some ⟨ret, [f], st, .star⟩⟩
def j : PFact := ⟨arg, [g], st, .star⟩

-- `(ret,.,[any]) ∩ (ret,.f,*)` gives `(ret,.f,[any])` in both
example : restrictU j ⟨⟨ret, [], .any, .star⟩, false⟩ d = some ⟨⟨ret, [f], .any, .star⟩, false⟩ := by decide
example : restrictS j ⟨⟨ret, [], .any, .star⟩, false⟩ d = some ⟨⟨ret, [f], .any, .star⟩, false⟩ := by decide
-- a correlated `(ret,.,*)` above `D-p`: U drops the edge, S keeps it
example : restrictU j ⟨⟨ret, [], st, .star⟩, false⟩ d = none := by decide
example : restrictS j ⟨⟨ret, [], st, .star⟩, false⟩ d = some ⟨⟨ret, [], st, .star⟩, false⟩ := by decide
-- a conclusion below `D-p`: kept in both
example : restrictU j ⟨⟨ret, [f, g], st, .star⟩, false⟩ d = some ⟨⟨ret, [f, g], st, .star⟩, false⟩ := by
  decide
example : restrictS j ⟨⟨ret, [f, g], st, .star⟩, false⟩ d = some ⟨⟨ret, [f, g], st, .star⟩, false⟩ := by
  decide
-- a conclusion apart from `D-p` (`(ret,.x,*)` against `(ret,.f,*)`): nothing
example : restrictU j ⟨⟨ret, [x], st, .star⟩, false⟩ d = none := by decide
example : restrictS j ⟨⟨ret, [x], st, .star⟩, false⟩ d = none := by decide
-- a premise apart from `D-c`: nothing
example : restrictU ⟨arg, [h], st, .star⟩ ⟨⟨ret, [f], st, .star⟩, false⟩ d = none := by decide
example : restrictS ⟨arg, [h], st, .star⟩ ⟨⟨ret, [f], st, .star⟩, false⟩ d = none := by decide
-- no exit pattern: nothing
def d0 : DemandEdge := ⟨⟨arg, [g], .any, .star⟩, none⟩
example : restrictU j ⟨⟨ret, [f], st, .star⟩, false⟩ d0 = none := by decide
example : restrictS j ⟨⟨ret, [f], st, .star⟩, false⟩ d0 = none := by decide
-- the user's example: `(arg,.g,*) → (ret,.f,*)` is kept
example : restrictU j ⟨⟨ret, [f], st, .star⟩, false⟩ d = some ⟨⟨ret, [f], st, .star⟩, false⟩ := by decide
example : restrictS j ⟨⟨ret, [f], st, .star⟩, false⟩ d = some ⟨⟨ret, [f], st, .star⟩, false⟩ := by decide
-- `(arg,.,*) → (ret,.x,*)` is filtered (the premise overlaps `D-c`, the conclusion is apart)
example : restrictU ⟨arg, [], st, .star⟩ ⟨⟨ret, [x], st, .star⟩, false⟩ d = none := by decide
example : restrictS ⟨arg, [], st, .star⟩ ⟨⟨ret, [x], st, .star⟩, false⟩ d = none := by decide
-- `(arg,.h,*) → (ret,.f,*)` is filtered (the premise is apart from `D-c`)
example : restrictU ⟨arg, [h], st, .star⟩ ⟨⟨ret, [f], st, .star⟩, false⟩ d = none := by decide
example : restrictS ⟨arg, [h], st, .star⟩ ⟨⟨ret, [f], st, .star⟩, false⟩ d = none := by decide

/-! ### Version 4: the mark-aware emission `emitM`

  The demand entry pattern of a restricted run has a concrete mark: the backward run starts at
  a sink with the mark `T`. So `dcT = (arg,.f,[any],T)`. The emission is `a ∩ D-c` with the mark
  of the added fact `a`. -/

def dcT : PFact := ⟨arg, [f], .any, .conc T⟩

-- below the demand chain: the WHOLE added fact (not the chain and one accessor more)
example : emitM dcT ⟨arg, [f, g, x], .exact, .conc T⟩ = some ⟨arg, [f, g, x], .exact, .conc T⟩ := by
  decide
example : emitM dcT ⟨arg, [f, g], .any, .conc T⟩ = some ⟨arg, [f, g], .any, .conc T⟩ := by decide
-- at the demand chain: the meet of the two tails (`[any]` of the demand keeps the fact tail)
example : emitM dcT ⟨arg, [f], .exact, .conc T⟩ = some ⟨arg, [f], .exact, .conc T⟩ := by decide
example : emitM dcT ⟨arg, [f], .any, .conc T⟩ = some ⟨arg, [f], .any, .conc T⟩ := by decide
-- above the demand chain, `[any]`: the demand chain with the demand tail and the fact mark
example : emitM dcT ⟨arg, [], .any, .conc T⟩ = some ⟨arg, [f], .any, .conc T⟩ := by decide
-- above the demand chain, `$`: nothing (the fact does not reach the chain)
example : emitM dcT ⟨arg, [], .exact, .conc T⟩ = none := by decide
-- apart from the demand chain, and another base: nothing
example : emitM dcT ⟨arg, [g, h], .any, .conc T⟩ = none := by decide
example : emitM dcT ⟨ret, [f], .any, .conc T⟩ = none := by decide
-- mark mismatch: the demand asks for `T`, the fact carries `7`: nothing
example : emitM dcT ⟨arg, [f], .exact, .conc 7⟩ = none := by decide
example : emitM dcT ⟨arg, [], .any, .conc 7⟩ = none := by decide
-- a `*` fact mark against the concrete demand mark: nothing. This row never occurs in a
-- restricted run: the run starts from the zero fact, and `emitM` copies the concrete mark of
-- the added fact, so every added fact of the run has a concrete mark (no request is necessary).
example : emitM dcT ⟨arg, [f], st, .star⟩ = none := by decide
example : emitM dcT ⟨arg, [], .any, .star⟩ = none := by decide

/-- A demand entry pattern with the `*` mark: it admits every mark. -/
def dcS : PFact := ⟨arg, [f], .any, .star⟩

-- a `*` demand mark keeps the mark of the added fact (concrete or `*`)
example : emitM dcS ⟨arg, [f], .exact, .conc 7⟩ = some ⟨arg, [f], .exact, .conc 7⟩ := by decide
example : emitM dcS ⟨arg, [f, g, x], .exact, .conc T⟩ = some ⟨arg, [f, g, x], .exact, .conc T⟩ := by
  decide
example : emitM dcS ⟨arg, [], .any, .conc 7⟩ = some ⟨arg, [f], .any, .conc 7⟩ := by decide
example : emitM dcS ⟨arg, [f], st, .star⟩ = some ⟨arg, [f], st, .star⟩ := by decide

/-! #### The meet at the same path (`meetK`)

  `(p,[any],T) ∩ (p,$) = (p,$,T)` and `(p,[any],T) ∩ (p,*/{g}) = (p,*/{g},T)`. The vectors give
  the meet in both directions (the added fact `[any]` against a demand tail, and the reverse). -/

example : meetK .any .exact = .exact := by decide
example : meetK .exact .any = .exact := by decide
example : meetK .any (.star (.set [g])) = .star (.set [g]) := by decide
example : meetK (.star (.set [g])) .any = .star (.set [g]) := by decide
example : meetK .any .any = .any := by decide
-- the added fact `(arg,.f,[any],T)` against the demand `(arg,.f,$,T)` and `(arg,.f,*/{g},T)`
example : emitM ⟨arg, [f], .exact, .conc T⟩ ⟨arg, [f], .any, .conc T⟩ =
    some ⟨arg, [f], .exact, .conc T⟩ := by decide
example : emitM ⟨arg, [f], .star (.set [g]), .conc T⟩ ⟨arg, [f], .any, .conc T⟩ =
    some ⟨arg, [f], .star (.set [g]), .conc T⟩ := by decide
-- the same with a `*` demand mark: the result has the mark `T` of the added fact
example : emitM ⟨arg, [f], .exact, .star⟩ ⟨arg, [f], .any, .conc T⟩ =
    some ⟨arg, [f], .exact, .conc T⟩ := by decide
example : emitM ⟨arg, [f], .star (.set [g]), .star⟩ ⟨arg, [f], .any, .conc T⟩ =
    some ⟨arg, [f], .star (.set [g]), .conc T⟩ := by decide
-- the reverse direction: the demand `(arg,.f,[any],T)` against `(arg,.f,$,T)` and `(arg,.f,*/{g},T)`
example : emitM dcT ⟨arg, [f], .exact, .conc T⟩ = some ⟨arg, [f], .exact, .conc T⟩ := by decide
example : emitM dcT ⟨arg, [f], .star (.set [g]), .conc T⟩ =
    some ⟨arg, [f], .star (.set [g]), .conc T⟩ := by decide

/-! ### Version 4: the satisfaction `satO` -/

-- the fact overlaps the premise and the marks match: satisfied
example : satO ⟨arg, [f], .any, .conc T⟩ ⟨arg, [f, g], .any, .conc T⟩ = true := by decide
example : satO ⟨arg, [f], .any, .conc T⟩ ⟨arg, [f], .any, .conc T⟩ = true := by decide
example : satO ⟨arg, [f, g], .any, .conc T⟩ ⟨arg, [f], .any, .conc T⟩ = true := by decide
example : satO ⟨arg, [f], .exact, .conc T⟩ ⟨arg, [f], .exact, .conc T⟩ = true := by decide
-- the premise mark `*` admits every fact mark
example : satO ⟨arg, [f], st, .star⟩ ⟨arg, [], .any, .conc T⟩ = true := by decide
-- mark mismatch: not satisfied
example : satO ⟨arg, [f], .any, .conc T⟩ ⟨arg, [f, g], .any, .conc 7⟩ = false := by decide
example : satO ⟨arg, [f], .any, .conc T⟩ ⟨arg, [f], .any, .star⟩ = false := by decide
-- apart: not satisfied
example : satO ⟨arg, [f], .any, .conc T⟩ ⟨arg, [g], .any, .conc T⟩ = false := by decide
example : satO ⟨arg, [f], .any, .conc T⟩ ⟨ret, [f], .any, .conc T⟩ = false := by decide
-- the fact is above the premise but cannot reach it (`$`): no overlap, not satisfied
example : satO ⟨arg, [f], .any, .conc T⟩ ⟨arg, [], .exact, .conc T⟩ = false := by decide
-- `satI` (the spec rule): the premise must lie INSIDE the fact.
example : satI ⟨arg, [f, g], .exact, .conc T⟩ ⟨arg, [f], .any, .conc T⟩ = true := by decide
example : satI ⟨arg, [f], .any, .conc T⟩ ⟨arg, [f], .any, .conc T⟩ = true := by decide
-- a coarser premise is not read by a precise fact (`satO` reads it)
example : satI ⟨arg, [f], .any, .conc T⟩ ⟨arg, [f, g], .exact, .conc T⟩ = false := by decide
example : satO ⟨arg, [f], .any, .conc T⟩ ⟨arg, [f, g], .exact, .conc T⟩ = true := by decide
example : satI ⟨arg, [f], .any, .conc T⟩ ⟨arg, [f], .any, .conc 7⟩ = false := by decide

end Vec

/-! ## Part 2. Program 1: the emission counterexample

```
root():  x.g.h.f.k.z = source();  c(x);         // method 0
c(x):    y = x.g.h;  m(y);                       // method 1
m(arg):  sink(arg.f.k.z);                        // method 2, sink at its entry node 0
```
  Accessors f=1, g=2, h=3, k=4, z=5. Bases zero=0, x=1, y=2, arg=3. Mark T=1. L = 3.
  The demands are what a backward run with the field limit 2 gives: `arg.f.k.z` is cut to
  `(arg,.f.k,[any])` and `x.g.h.f.k.z` is cut to `(x,.g.h,[any])`. -/

def src : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨1, [2, 3, 1, 4, 5], .exact, .conc 1⟩)]⟩
def callC : Call := ⟨1, [1], [(⟨1, [], st, .star⟩, ⟨1, [], st, .star⟩)], []⟩
def rd : Stmt := ⟨[1, 2], [(⟨1, [], st, .star⟩, ⟨1, [], st, .star⟩),
  (⟨1, [2, 3], st, .star⟩, ⟨2, [], st, .star⟩)]⟩
def callM : Call := ⟨2, [2], [(⟨2, [], st, .star⟩, ⟨3, [], st, .star⟩)], []⟩
def P1 : Program := ⟨fun _ => 0, fun m => if m = 2 then 0 else 2,
  [(0, 0, .stmt src, 1), (0, 1, .call callC, 2), (1, 0, .stmt rd, 1), (1, 1, .call callM, 2)]⟩
def sink1 : PFact := ⟨3, [1, 4, 5], .exact, .conc 1⟩
def sinks1 : List (MethodId × Node × PFact) := [(2, 0, sink1)]
def dem1 : MethodId → DemandEdge → Prop := fun m d =>
  (m = 1 ∧ d = ⟨⟨1, [2, 3], .any, .star⟩, none⟩) ∨ (m = 2 ∧ d = ⟨⟨3, [1, 4], .any, .star⟩, none⟩)
def noRecs : MethodId → PFact × AFact → Prop := fun _ _ => False

/-- Program 1 has no cleaner and no type filter: these edges are not in the program. -/
theorem p1_no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ P1.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h

theorem p1_no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ P1.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h

theorem p1_wf : P1.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ he => cases he with
        | head => rfl
        | tail _ he => cases he
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          cases he with
          | head => rfl
          | tail _ he => cases he with
            | head => rfl
            | tail _ he => cases he
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  · intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | head => cases he with
        | head => rfl
        | tail _ he => cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => cases he with
            | head => rfl
            | tail _ he => cases he
          | tail _ hE => cases hE
  · intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | head => cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head => cases he
          | tail _ hE => cases hE
  · intro M n b may n' hE
    exact (p1_no_filt hE).elim

#print axioms p1_wf

namespace Prog1

/-- The source location `x.g.h.f.k.z`, the argument of `c` and the argument of `m`. -/
def l0 : Loc := ⟨1, [2, 3, 1, 4, 5], 1⟩
def l1 : Loc := ⟨2, [1, 4, 5], 1⟩
def l2 : Loc := ⟨3, [1, 4, 5], 1⟩

theorem den_src : den zeroFact ⟨1, [2, 3, 1, 4, 5], .exact, .conc 1⟩ zeroLoc l0 :=
  ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
theorem den_cx : den ⟨1, [], st, .star⟩ ⟨1, [], st, .star⟩ l0 l0 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [2, 3, 1, 4, 5], [2, 3, 1, 4, 5], rfl, rfl, rfl, rfl, rfl⟩
theorem den_rd : den ⟨1, [2, 3], st, .star⟩ ⟨2, [], st, .star⟩ l0 l1 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [1, 4, 5], [1, 4, 5], rfl, rfl, rfl, rfl, rfl⟩
theorem den_my : den ⟨2, [], st, .star⟩ ⟨3, [], st, .star⟩ l1 l2 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [1, 4, 5], [1, 4, 5], rfl, rfl, rfl, rfl, rfl⟩

end Prog1

open Prog1 in
/-- The vulnerability is real, and every call step on it is demanded. -/
theorem p1_reachR : ReachR P1 dem1 [0] 2 0 ⟨3, [1, 4, 5], 1⟩ := by
  have f0 : FlowR P1 dem1 0 zeroLoc 1 l0 :=
    FlowR.step (FlowR.start 0 zeroLoc) (s := src) (List.Mem.head _)
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_src⟩)
  have r0 : ReachR P1 dem1 [0] 0 1 l0 := ReachR.root (List.Mem.head _) f0
  have fc : FlowR P1 dem1 1 l0 1 l1 :=
    FlowR.step (FlowR.start 1 l0) (s := rd) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_rd⟩)
  have r1 : ReachR P1 dem1 [0] 1 1 l1 :=
    ReachR.down r0 (c := callC) (n' := 2) (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) den_cx
      (d := ⟨⟨1, [2, 3], .any, .star⟩, none⟩) (Or.inl ⟨rfl, rfl⟩) ⟨rfl, ⟨[1, 4, 5], rfl, trivial⟩, trivial⟩ fc
  exact ReachR.down r1 (c := callM) (n' := 2)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) den_my
    (d := ⟨⟨3, [1, 4], .any, .star⟩, none⟩) (Or.inr ⟨rfl, rfl⟩) ⟨rfl, ⟨[5], rfl, trivial⟩, trivial⟩
    (FlowR.start 2 l2)

#print axioms p1_reachR

theorem p1_sink_covers : sink1.covers ⟨3, [1, 4, 5], 1⟩ := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

#print axioms p1_sink_covers

open Prog1 in
/-- The vulnerability is real (the plain concrete witness). -/
theorem p1_reach : Reach P1 [0] 2 0 ⟨3, [1, 4, 5], 1⟩ := by
  have f0 : Flow P1 0 zeroLoc 1 l0 :=
    Flow.step (Flow.start 0 zeroLoc) (s := src) (List.Mem.head _)
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_src⟩)
  have r0 : Reach P1 [0] 0 1 l0 := Reach.root (List.Mem.head _) f0
  have fc : Flow P1 1 l0 1 l1 :=
    Flow.step (Flow.start 1 l0) (s := rd) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_rd⟩)
  have r1 : Reach P1 [0] 1 1 l1 :=
    Reach.down r0 (c := callC) (n' := 2) (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) den_cx fc
  exact Reach.down r1 (c := callM) (n' := 2)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) den_my
    (Flow.start 2 l2)

#print axioms p1_reach

namespace Prog1

/-- The run with the sound rules, and the run with the rules as agreed. -/
abbrev R1S := DR P1 cnt 3 dem1 emitS satS restrictS noRecs sinks1 [0]
abbrev R1U := DR P1 cnt 3 dem1 emitU satU restrictU noRecs sinks1 [0]

def d1 : DemandEdge := ⟨⟨1, [2, 3], .any, .star⟩, none⟩
def d2 : DemandEdge := ⟨⟨3, [1, 4], .any, .star⟩, none⟩
/-- The binding edges of the calls. -/
def bx : MicroEdge := (⟨1, [], st, .star⟩, ⟨1, [], st, .star⟩)
def bym : MicroEdge := (⟨2, [], st, .star⟩, ⟨3, [], st, .star⟩)

def Z : AFact := ⟨zeroFact, false⟩
/-- The root edge `(x,.g.h.f,[any],T)`: the source cut to the field limit 3 (demand layer). -/
def X : AFact := ⟨⟨1, [2, 3, 1], .any, .conc 1⟩, true⟩
/-- The initial fact of `c`: `J = (x,.g.h.f,*)`. -/
def J : PFact := ⟨1, [2, 3, 1], st, .star⟩
def Jf : AFact := ⟨J, false⟩
/-- `(y,.f,*)` in `c`. -/
def Y : AFact := ⟨⟨2, [1], st, .star⟩, false⟩
/-- The added fact of `m`: `(arg,.f,*)`. It is `*` and ABOVE the demand chain `arg.f.k`. -/
def A2 : PFact := ⟨3, [1], st, .star⟩
/-- `emitS` gives the demand chain `J2 = (arg,.f.k,*)`. -/
def J2 : PFact := ⟨3, [1, 4], st, .star⟩
/-- The answer in `c`: `(x,.g.h.f,*,T)`. -/
def Jc : PFact := ⟨1, [2, 3, 1], st, .conc 1⟩
def Yc : AFact := ⟨⟨2, [1], .any, .conc 1⟩, true⟩
def A2c : PFact := ⟨3, [1], .any, .conc 1⟩
/-- The answer in `m`: `(arg,.f.k,*,T)`. -/
def J2c : PFact := ⟨3, [1, 4], st, .conc 1⟩
def F2c : AFact := ⟨⟨3, [1, 4], .any, .conc 1⟩, true⟩

theorem hE00 : (0, 0, Instr.stmt src, 1) ∈ P1.edges := List.Mem.head _
theorem hE01 : (0, 1, Instr.call callC, 2) ∈ P1.edges := List.Mem.tail _ (List.Mem.head _)
theorem hE10 : (1, 0, Instr.stmt rd, 1) ∈ P1.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem hE11 : (1, 1, Instr.call callM, 2) ∈ P1.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

end Prog1

open Prog1 in
/-- With the S rules the run finds the vulnerability (in the demand layer). -/
theorem p1_found_S : DR P1 cnt 3 dem1 emitS satS restrictS noRecs sinks1 [0] (.vuln 2 0 sink1 true) := by
  have r0 : R1S (.init 0 zeroFact) := DR.root (List.Mem.head _)
  have e0 : R1S (.edge 0 zeroFact 0 Z) := DR.start r0
  -- the root edge X = (x,.g.h.f,[any],T): the source is cut to the field limit 3
  have e1 : R1S (.edge 0 zeroFact 1 X) := DR.step e0 (s := src) hE00 (by decide)
  -- the added fact of c and its emission J = (x,.g.h.f,*)
  have ad1 : R1S (.added 1 X.fact) :=
    DR.added (c := callC) (e := bx) (a := X) e1 hE01 (List.Mem.head _) (by decide)
  have iJ : R1S (.init 1 J) := DR.initR (d := d1) ad1 (Or.inl ⟨rfl, rfl⟩) (by decide)
  have eJ0 : R1S (.edge 1 J 0 Jf) := DR.start iJ
  -- in c: (y,.f,*)
  have eJ1 : R1S (.edge 1 J 1 Y) := DR.step eJ0 (s := rd) hE10 (by decide)
  -- the added fact of m: (arg,.f,*), above the demand chain; emitS gives J2 = (arg,.f.k,*)
  have ad2 : R1S (.added 2 A2) :=
    DR.added (c := callM) (e := bym) (a := ⟨A2, false⟩) eJ1 hE11 (List.Mem.head _) (by decide)
  have iJ2 : R1S (.init 2 J2) := DR.initR (d := d2) ad2 (Or.inr ⟨rfl, rfl⟩) (by decide)
  have eJ2 : R1S (.edge 2 J2 0 ⟨J2, false⟩) := DR.start iJ2
  -- the sink check requests T on J2
  have rq2 : R1S (.req 2 J2 1) := DR.reqSink eJ2 (s := sink1) (List.Mem.head _) (by decide)
  -- the request goes up to J in c
  have rq1 : R1S (.req 1 J 1) :=
    DR.reqUp (m := 2) (c := callM) (e := bym) (a := ⟨A2, false⟩) rq2 eJ1 hE11 rfl (List.Mem.head _)
      (by decide) rfl (by decide)
  -- the answer in c with the concrete added fact: (x,.g.h.f,*,T)
  have iJc : R1S (.init 1 Jc) := DR.answer rq1 ad1 rfl (by decide)
  have eJc0 : R1S (.edge 1 Jc 0 X) := DR.start iJc
  have eJc1 : R1S (.edge 1 Jc 1 Yc) := DR.step eJc0 (s := rd) hE10 (by decide)
  have ad2c : R1S (.added 2 A2c) :=
    DR.added (c := callM) (e := bym) (a := ⟨A2c, true⟩) eJc1 hE11 (List.Mem.head _) (by decide)
  -- the answer in m: (arg,.f.k,*,T); its start is (arg,.f.k,[any],T)
  have iJ2c : R1S (.init 2 J2c) := DR.answer rq2 ad2c rfl (by decide)
  have eJ2c : R1S (.edge 2 J2c 0 F2c) := DR.start iJ2c
  exact DR.vuln eJ2c (s := sink1) (List.Mem.head _) (by decide)

#print axioms p1_found_S

namespace Prog1

/-! ### The closure of the U run

  With `emitU` the added fact `(arg,.f,*)` of `m` is `*` and above the demand chain
  `arg.f.k`, so it gives NO initial fact. Then `m` has no edge, no request and no
  vulnerability. The lists below contain every object of the U run (`inv1`). -/

-- the row that differs: the added fact of `m` against the demand chain of `m`
example : emitU d2.din A2 = none := by decide
example : emitS d2.din A2 = some J2 := by decide
-- the answer added fact `(arg,.f,[any],T)` gives an initial fact in both, but the U run never
-- makes it: it needs the request in `c`, and that request needs an edge in `m`
example : emitU d2.din A2c = some J2 := by decide

def inits1 : List (MethodId × PFact) := [(0, zeroFact), (1, J)]
def edges1 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, X), (0, zeroFact, 2, Z),
   (1, J, 0, Jf), (1, J, 1, Jf), (1, J, 1, Y), (1, J, 2, Jf)]
def addeds1 : List (MethodId × PFact) := [(1, X.fact), (2, A2)]

/-- The invariant: every object of the U run is in the finite closure. No request and
    no vulnerability. -/
def Inv1 : Obj → Prop
  | .init M i => (M, i) ∈ inits1
  | .edge M i n f => (M, i, n, f) ∈ edges1
  | .added M a => (M, a) ∈ addeds1
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred Inv1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

theorem inv1 {o : Obj} (hD : R1U o) : Inv1 o := by
  induction hD with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits1, Inv1 (.edge x.1 x.2 (P1.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 3 src x.2.2.2).facts, Inv1 (.edge 0 x.2.1 1 f')) (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 3 rd x.2.2.2).facts, Inv1 (.edge 1 x.2.1 1 f')) (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 3 src x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 3 rd x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callC.touched = false → Inv1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 1 →
              memB x.2.2.2.fact.base callM.touched = false → Inv1 (.edge 1 x.2.1 2 x.2.2.2))
              (1, i, 1, f) ih rfl rfl hm
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callC.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, Inv1 (.added callC.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 1 → ∀ e ∈ callM.toCallee,
              ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, Inv1 (.added callM.callee a.fact))
              (1, i, 1, f) ih rfl rfl e he a ha
          | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (by decide : ∀ x ∈ addeds1, x.1 = 1 →
        ∀ j ∈ (emitU (⟨⟨1, [2, 3], .any, .star⟩, none⟩ : DemandEdge).din x.2).toList, Inv1 (.init 1 j))
        (1, a) ih rfl j (mem_toList_of_eq_some he)
    · exact (by decide : ∀ x ∈ addeds1, x.1 = 2 →
        ∀ j ∈ (emitU (⟨⟨3, [1, 4], .any, .star⟩, none⟩ : DemandEdge).din x.2).toList, Inv1 (.init 2 j))
        (2, a) ih rfl j (mem_toList_of_eq_some he)
  | ret _ _ _ _ _ _ hd hr =>
    rcases hd with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact absurd hr restrictWith_none
    · exact absurd hr restrictWith_none
  | retRec _ _ _ _ hrec => exact hrec.elim
  | @reqSink M i n f s t _ hs _ ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 2 → False) (2, i, 0, f) ih rfl
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs _ ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 2 → False) (2, i, 0, f) ih rfl
    | tail _ hs => cases hs
  -- the program has no cleaner and no type filter
  | clean _ hE _ _ => exact (p1_no_clean hE).elim
  | reqClean _ hE _ _ => exact (p1_no_clean hE).elim
  | filt _ hE _ _ => exact (p1_no_filt hE).elim

end Prog1

open Prog1 in
/-- With the U rules the run does NOT find the vulnerability: `m` gets no initial fact. -/
theorem p1_lost_U : ∀ b, ¬ DR P1 cnt 3 dem1 emitU satU restrictU noRecs sinks1 [0] (.vuln 2 0 sink1 b) :=
  fun _ h => inv1 h

#print axioms p1_lost_U

/-! ## Part 3. Program 2: the restriction counterexample

```
root():  x.h.i.f.k.z = source();  r = c(x);  sink(r.f.k.z);   // method 0, sink at node 2
c(arg):  ret = arg.h.i;  return ret;                           // method 1
```
  Accessors f=1, h=2, i=3, k=4, z=5. Bases zero=0, x=1, r=2, arg=3, ret=4. Mark T=1. L = 3.
  The demand edge of `c`: `D-c = (arg,.h.i,[any])`, `D-p = (ret,.f.k,[any])`. -/

def src2 : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨1, [2, 3, 1, 4, 5], .exact, .conc 1⟩)]⟩
def callC2 : Call := ⟨1, [1, 2], [(⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)],
  [(⟨4, [], st, .star⟩, ⟨2, [], st, .star⟩)]⟩
def rd2 : Stmt := ⟨[3, 4], [(⟨3, [], st, .star⟩, ⟨3, [], st, .star⟩),
  (⟨3, [2, 3], st, .star⟩, ⟨4, [], st, .star⟩)]⟩
def P2 : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 2,
  [(0, 0, .stmt src2, 1), (0, 1, .call callC2, 2), (1, 0, .stmt rd2, 1)]⟩
def sink2 : PFact := ⟨2, [1, 4, 5], .exact, .conc 1⟩
def sinks2 : List (MethodId × Node × PFact) := [(0, 2, sink2)]
def dem2 : MethodId → DemandEdge → Prop := fun m d =>
  m = 1 ∧ d = ⟨⟨3, [2, 3], .any, .star⟩, some ⟨4, [1, 4], .any, .star⟩⟩

/-- Program 2 has no cleaner and no type filter: these edges are not in the program. -/
theorem p2_no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ P2.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

theorem p2_no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ P2.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

theorem p2_wf : P2.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ he => cases he with
        | head => rfl
        | tail _ he => cases he
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          cases he with
          | head => rfl
          | tail _ he => cases he with
            | head => rfl
            | tail _ he => cases he
        | tail _ hE => cases hE
  · intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | head => cases he with
        | head => rfl
        | tail _ he => cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  · intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | head => cases he with
        | head => rfl
        | tail _ he => cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  · intro M n b may n' hE
    exact (p2_no_filt hE).elim

#print axioms p2_wf

namespace Prog2

/-- The source location `x.h.i.f.k.z`, the argument, the return value, the result `r.f.k.z`. -/
def l0 : Loc := ⟨1, [2, 3, 1, 4, 5], 1⟩
def l1 : Loc := ⟨3, [2, 3, 1, 4, 5], 1⟩
def l2 : Loc := ⟨4, [1, 4, 5], 1⟩
def l3 : Loc := ⟨2, [1, 4, 5], 1⟩

theorem den_src : den zeroFact ⟨1, [2, 3, 1, 4, 5], .exact, .conc 1⟩ zeroLoc l0 :=
  ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩
theorem den_in : den ⟨1, [], st, .star⟩ ⟨3, [], st, .star⟩ l0 l1 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [2, 3, 1, 4, 5], [2, 3, 1, 4, 5], rfl, rfl, rfl, rfl, rfl⟩
theorem den_rd : den ⟨3, [2, 3], st, .star⟩ ⟨4, [], st, .star⟩ l1 l2 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [1, 4, 5], [1, 4, 5], rfl, rfl, rfl, rfl, rfl⟩
theorem den_out : den ⟨4, [], st, .star⟩ ⟨2, [], st, .star⟩ l2 l3 :=
  ⟨rfl, rfl, trivial, rfl, trivial, [1, 4, 5], [1, 4, 5], rfl, rfl, rfl, rfl, rfl⟩

def dd : DemandEdge := ⟨⟨3, [2, 3], .any, .star⟩, some ⟨4, [1, 4], .any, .star⟩⟩

theorem hE00 : (0, 0, Instr.stmt src2, 1) ∈ P2.edges := List.Mem.head _
theorem hE01 : (0, 1, Instr.call callC2, 2) ∈ P2.edges := List.Mem.tail _ (List.Mem.head _)
theorem hE10 : (1, 0, Instr.stmt rd2, 1) ∈ P2.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

end Prog2

open Prog2 in
/-- The vulnerability is real, and the call step on it is demanded (entry AND exit). -/
theorem p2_reachR : ReachR P2 dem2 [0] 0 2 ⟨2, [1, 4, 5], 1⟩ := by
  have f0 : FlowR P2 dem2 0 zeroLoc 1 l0 :=
    FlowR.step (FlowR.start 0 zeroLoc) (s := src2) hE00
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_src⟩)
  have fc : FlowR P2 dem2 1 l1 1 l2 :=
    FlowR.step (FlowR.start 1 l1) (s := rd2) hE10
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_rd⟩)
  have f2 : FlowR P2 dem2 0 zeroLoc 2 l3 :=
    FlowR.call f0 (c := callC2) hE01 (List.Mem.head _) den_in fc (d := dd) ⟨rfl, rfl⟩
      ⟨rfl, ⟨[1, 4, 5], rfl, trivial⟩, trivial⟩ rfl ⟨rfl, [5], rfl, trivial⟩ (List.Mem.head _) den_out
  exact ReachR.root (List.Mem.head _) f2

#print axioms p2_reachR

theorem p2_sink_covers : sink2.covers ⟨2, [1, 4, 5], 1⟩ := ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

#print axioms p2_sink_covers

open Prog2 in
/-- The vulnerability is real (the plain concrete witness). -/
theorem p2_reach : Reach P2 [0] 0 2 ⟨2, [1, 4, 5], 1⟩ := by
  have f0 : Flow P2 0 zeroLoc 1 l0 :=
    Flow.step (Flow.start 0 zeroLoc) (s := src2) hE00
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_src⟩)
  have fc : Flow P2 1 l1 1 l2 :=
    Flow.step (Flow.start 1 l1) (s := rd2) hE10
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_rd⟩)
  have f2 : Flow P2 0 zeroLoc 2 l3 :=
    Flow.call f0 (c := callC2) hE01 (List.Mem.head _) den_in fc (List.Mem.head _) den_out
  exact Reach.root (List.Mem.head _) f2

#print axioms p2_reach

namespace Prog2

abbrev R2S := DR P2 cnt 3 dem2 emitS satS restrictS noRecs sinks2 [0]
abbrev R2U := DR P2 cnt 3 dem2 emitS satS restrictU noRecs sinks2 [0]

def bx : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
def br : MicroEdge := (⟨4, [], st, .star⟩, ⟨2, [], st, .star⟩)

def Z : AFact := ⟨zeroFact, false⟩
/-- The root edge `(x,.h.i.f,[any],T)`: the source cut to the field limit 3. -/
def X : AFact := ⟨⟨1, [2, 3, 1], .any, .conc 1⟩, true⟩
/-- The added fact of `c`: `(arg,.h.i.f,[any],T)`. -/
def A : AFact := ⟨⟨3, [2, 3, 1], .any, .conc 1⟩, true⟩
/-- The initial fact of `c`: `J = (arg,.h.i.f,*)`. -/
def J : PFact := ⟨3, [2, 3, 1], st, .star⟩
def Jf : AFact := ⟨J, false⟩
/-- The exit edge `g = (ret,.f,*)`: correlated, ABOVE `D-p = (ret,.f.k,[any])`. -/
def G : AFact := ⟨⟨4, [1], st, .star⟩, false⟩
/-- The summary result on `ret`, and the result on `r`: `(r,.f,[any],T)`. -/
def Rr : AFact := ⟨⟨4, [1], .any, .conc 1⟩, true⟩
def Rr' : AFact := ⟨⟨2, [1], .any, .conc 1⟩, true⟩

end Prog2

open Prog2 in
/-- With `restrictS` the run finds the vulnerability (in the demand layer). -/
theorem p2_found_S : DR P2 cnt 3 dem2 emitS satS restrictS noRecs sinks2 [0] (.vuln 0 2 sink2 true) := by
  have r0 : R2S (.init 0 zeroFact) := DR.root (List.Mem.head _)
  have e0 : R2S (.edge 0 zeroFact 0 Z) := DR.start r0
  have e1 : R2S (.edge 0 zeroFact 1 X) := DR.step e0 (s := src2) hE00 (by decide)
  have ad : R2S (.added 1 A.fact) :=
    DR.added (c := callC2) (e := bx) (a := A) e1 hE01 (List.Mem.head _) (by decide)
  have iJ : R2S (.init 1 J) := DR.initR (d := dd) ad ⟨rfl, rfl⟩ (by decide)
  have eJ0 : R2S (.edge 1 J 0 Jf) := DR.start iJ
  have eJ1 : R2S (.edge 1 J 1 G) := DR.step eJ0 (s := rd2) hE10 (by decide)
  -- restrictS keeps g = (ret,.f,*); the caller fact satisfies J; the result is (r,.f,[any],T)
  have e2 : R2S (.edge 0 zeroFact 2 (limitF cnt 3 Rr')) :=
    DR.ret (c := callC2) (e1 := bx) (a := A) (j := J) (g := G) (d := dd) (g' := G) (r := Rr)
      (e2 := br) e1 hE01 (List.Mem.head _) (by decide) iJ eJ1 ⟨rfl, rfl⟩ (by decide) (by decide)
      (by decide) (List.Mem.head _) (by decide)
  have e2' : R2S (.edge 0 zeroFact 2 Rr') := e2
  exact DR.vuln e2' (s := sink2) (List.Mem.head _) (by decide)

#print axioms p2_found_S

namespace Prog2

/-! ### The closure of the run with `restrictU`

  `restrictU` drops the only exit edge `(ret,.f,*)` of `J` (it is `*` and above `D-p`), and
  the other exit edge `J` itself is on the base `arg`. So no summary reaches the caller,
  and no fact on the base `r` reaches node 2 of the root. The lists below contain every
  object of this run (`inv2`). -/

-- the row that differs: the exit edge `(ret,.f,*)` against `D-p = (ret,.f.k,[any])`
example : restrictU J G dd = none := by decide
example : restrictS J G dd = some G := by decide
-- the caller fact `(arg,.h.i.f,[any],T)` satisfies `J` in both versions
example : satU J A.fact = true := by decide
example : satS J A.fact = true := by decide

def inits2 : List (MethodId × PFact) := [(0, zeroFact), (1, J)]
def edges2 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, X), (0, zeroFact, 2, Z),
   (1, J, 0, Jf), (1, J, 1, Jf), (1, J, 1, G)]
def addeds2 : List (MethodId × PFact) := [(1, A.fact)]

def Inv2 : Obj → Prop
  | .init M i => (M, i) ∈ inits2
  | .edge M i n f => (M, i, n, f) ∈ edges2
  | .added M a => (M, a) ∈ addeds2
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred Inv2 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits2))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges2))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds2))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

theorem inv2 {o : Obj} (hD : R2U o) : Inv2 o := by
  induction hD with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits2, Inv2 (.edge x.1 x.2 (P2.entry x.1) (startFact x.2))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges2, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 3 src2 x.2.2.2).facts, Inv2 (.edge 0 x.2.1 1 f')) (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges2, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 3 rd2 x.2.2.2).facts, Inv2 (.edge 1 x.2.1 1 f')) (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges2, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 3 src2 x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges2, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 3 rd2 x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges2, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callC2.touched = false → Inv2 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges2, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callC2.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, Inv2 (.added callC2.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    obtain ⟨rfl, rfl⟩ := hd
    exact (by decide : ∀ x ∈ addeds2, x.1 = 1 → ∀ j ∈ (emitS dd.din x.2).toList, Inv2 (.init 1 j))
      (1, a) ih rfl j (mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ _ _ _ _ _ hd hr _ _ _ _ _ _ ihg =>
    obtain ⟨hc, rfl⟩ := hd
    rw [hc] at ihg
    have hnone : restrictU j g dd = none :=
      (by decide : ∀ x ∈ edges2, x.1 = 1 → x.2.2.1 = P2.exit 1 → restrictU x.2.1 x.2.2.2 dd = none)
        (1, j, P2.exit 1, g) ihg rfl rfl
    exact absurd hr (ne_some_of_eq_none hnone)
  | retRec _ _ _ _ hrec => exact hrec.elim
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      have hn : check i f sink2 = .none :=
        (by decide : ∀ x ∈ edges2, x.1 = 0 → x.2.2.1 = 2 → check x.2.1 x.2.2.2 sink2 = .none)
          (0, i, 2, f) ih rfl rfl
      rw [hn] at hc
      cases hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      have hn : check i f sink2 = .none :=
        (by decide : ∀ x ∈ edges2, x.1 = 0 → x.2.2.1 = 2 → check x.2.1 x.2.2.2 sink2 = .none)
          (0, i, 2, f) ih rfl rfl
      rw [hn] at hc
      cases hc
    | tail _ hs => cases hs
  -- the program has no cleaner and no type filter
  | clean _ hE _ _ => exact (p2_no_clean hE).elim
  | reqClean _ hE _ _ => exact (p2_no_clean hE).elim
  | filt _ hE _ _ => exact (p2_no_filt hE).elim

end Prog2

open Prog2 in
/-- With `restrictU` (and the S emission and satisfaction) the run does NOT find the
    vulnerability: the only summary edge of `c` is dropped. -/
theorem p2_lost_U :
    ∀ b, ¬ DR P2 cnt 3 dem2 emitS satS restrictU noRecs sinks2 [0] (.vuln 0 2 sink2 b) :=
  fun _ h => inv2 h

#print axioms p2_lost_U

/-! ## Part 4. Programs 1 and 2 under the version-4 rules

  The rules are `emitM`, `satI` and the AGREED restriction `restrictU`. The demands are what the
  backward run gives: the backward run starts at the sink, so every demand entry pattern has the
  concrete mark `T = 1`.

  The run starts from the zero fact. The source gives a concrete fact, and `emitM` copies the mark
  of the added fact, so every fact of the run has the concrete mark `T`. Then the two rows where
  the version-3 tables differ (a `*` added fact above the chain, a correlated `*` exit fact above
  `D-p`) do not occur, and no request is necessary. -/

/-- The demand of program 1 (version 4): the chains of the round-3 demand with the mark `T`. -/
def dem1M : MethodId → DemandEdge → Prop := fun m d =>
  (m = 1 ∧ d = ⟨⟨1, [2, 3], .any, .conc 1⟩, none⟩) ∨ (m = 2 ∧ d = ⟨⟨3, [1, 4], .any, .conc 1⟩, none⟩)

/-- The demand of program 2 (version 4): the edge of the round-3 demand with the mark `T`. -/
def dem2M : MethodId → DemandEdge → Prop := fun m d =>
  m = 1 ∧ d = ⟨⟨3, [2, 3], .any, .conc 1⟩, some ⟨4, [1, 4], .any, .conc 1⟩⟩

namespace Prog1

def d1M : DemandEdge := ⟨⟨1, [2, 3], .any, .conc 1⟩, none⟩
def d2M : DemandEdge := ⟨⟨3, [1, 4], .any, .conc 1⟩, none⟩

/-- The version-4 run of program 1. -/
abbrev R1M := DR P1 cnt 3 dem1M emitM satI restrictU noRecs sinks1 [0]

/-- The added fact of `m` in the version-4 run: `(arg,.f,[any],T)` (above the chain `arg.f.k`). -/
def A2M : AFact := ⟨⟨3, [1], .any, .conc 1⟩, true⟩
/-- The initial fact of `m`: `emitM` gives the chain `(arg,.f.k,[any],T)`. -/
def J2M : PFact := ⟨3, [1, 4], .any, .conc 1⟩

/-! ### The trace, step by step (each step is checked by `decide`) -/

-- the root edge: the source `x.g.h.f.k.z` is cut to `X = (x,.g.h.f,[any],T)` (demand layer)
example : X ∈ (transfer cnt 3 src Z).facts := by decide
-- the binding into `c` gives the added fact `X` itself
example : X ∈ (applyEdge X bx.1 bx.2).facts := by decide
-- the added fact is below the demand chain `x.g.h`: `emitM` gives the WHOLE added fact
example : emitM d1M.din X.fact = some X.fact := by decide
-- the start fact is `[any]`: the demand layer
example : startFact X.fact = X := by decide
-- `y = x.g.h` gives `(y,.f,[any],T)`
example : Yc ∈ (transfer cnt 3 rd X).facts := by decide
-- the binding into `m` gives the added fact `(arg,.f,[any],T)`
example : A2M ∈ (applyEdge Yc bym.1 bym.2).facts := by decide
-- the added fact is above the demand chain `arg.f.k` and `[any]`: `emitM` gives the chain
example : emitM d2M.din A2M.fact = some J2M := by decide
example : startFact J2M = ⟨J2M, true⟩ := by decide
-- the sink triggers (no request)
example : check J2M ⟨J2M, true⟩ sink1 = .triggered := by decide

end Prog1

open Prog1 in
/-- Version 4: the vulnerability of program 1 is real, and every call step on it is demanded by
    `dem1M` (the entry location, WITH its mark `T`). -/
theorem p1_reachR_M : ReachR P1 dem1M [0] 2 0 ⟨3, [1, 4, 5], 1⟩ := by
  have f0 : FlowR P1 dem1M 0 zeroLoc 1 l0 :=
    FlowR.step (FlowR.start 0 zeroLoc) (s := src) hE00
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_src⟩)
  have r0 : ReachR P1 dem1M [0] 0 1 l0 := ReachR.root (List.Mem.head _) f0
  have fc : FlowR P1 dem1M 1 l0 1 l1 :=
    FlowR.step (FlowR.start 1 l0) (s := rd) hE10
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_rd⟩)
  have r1 : ReachR P1 dem1M [0] 1 1 l1 :=
    ReachR.down r0 (c := callC) (n' := 2) hE01 (List.Mem.head _) den_cx
      (d := d1M) (Or.inl ⟨rfl, rfl⟩) ⟨rfl, ⟨[1, 4, 5], rfl, trivial⟩, rfl⟩ fc
  exact ReachR.down r1 (c := callM) (n' := 2) hE11 (List.Mem.head _) den_my
    (d := d2M) (Or.inr ⟨rfl, rfl⟩) ⟨rfl, ⟨[5], rfl, trivial⟩, rfl⟩ (FlowR.start 2 l2)

#print axioms p1_reachR_M

open Prog1 in
/-- Version 4: the run with `emitM`, `satI` and `restrictU` finds the vulnerability of program 1
    (in the demand layer). No request object is necessary. -/
theorem p1_found_M :
    DR P1 cnt 3 dem1M emitM satI restrictU noRecs sinks1 [0] (.vuln 2 0 sink1 true) := by
  have r0 : R1M (.init 0 zeroFact) := DR.root (List.Mem.head _)
  have e0 : R1M (.edge 0 zeroFact 0 Z) := DR.start r0
  -- the root edge X = (x,.g.h.f,[any],T): the source is cut to the field limit 3
  have e1 : R1M (.edge 0 zeroFact 1 X) := DR.step e0 (s := src) hE00 (by decide)
  -- the added fact of c is X; emitM gives the fact itself
  have ad1 : R1M (.added 1 X.fact) :=
    DR.added (c := callC) (e := bx) (a := X) e1 hE01 (List.Mem.head _) (by decide)
  have iX : R1M (.init 1 X.fact) := DR.initR (d := d1M) ad1 (Or.inl ⟨rfl, rfl⟩) (by decide)
  -- the start of the [any] initial fact is X (demand layer)
  have eX0 : R1M (.edge 1 X.fact 0 X) := DR.start iX
  -- in c: (y,.f,[any],T)
  have eX1 : R1M (.edge 1 X.fact 1 Yc) := DR.step eX0 (s := rd) hE10 (by decide)
  -- the added fact of m: (arg,.f,[any],T); emitM gives the chain (arg,.f.k,[any],T)
  have ad2 : R1M (.added 2 A2M.fact) :=
    DR.added (c := callM) (e := bym) (a := A2M) eX1 hE11 (List.Mem.head _) (by decide)
  have iJ2 : R1M (.init 2 J2M) := DR.initR (d := d2M) ad2 (Or.inr ⟨rfl, rfl⟩) (by decide)
  have eJ2 : R1M (.edge 2 J2M 0 ⟨J2M, true⟩) := DR.start iJ2
  -- the sink triggers
  exact DR.vuln eJ2 (s := sink1) (List.Mem.head _) (by decide)

#print axioms p1_found_M

namespace Prog2

def ddM : DemandEdge := ⟨⟨3, [2, 3], .any, .conc 1⟩, some ⟨4, [1, 4], .any, .conc 1⟩⟩

/-- The version-4 run of program 2. -/
abbrev R2M := DR P2 cnt 3 dem2M emitM satI restrictU noRecs sinks2 [0]

/-- The initial fact of `c` in the version-4 run: `emitM` gives the added fact itself,
    `JM = (arg,.h.i.f,[any],T)`. -/
def JM : PFact := A.fact
/-- The exit edge of `c`: `GM = (ret,.f,[any],T)`. It is NOT a correlated `*`. -/
def GM : AFact := ⟨⟨4, [1], .any, .conc 1⟩, true⟩
/-- `restrictU` keeps it as `(ret,.f.k,[any],T)` (the meet with `D-p`). -/
def GM' : AFact := ⟨⟨4, [1, 4], .any, .conc 1⟩, true⟩
/-- The summary result on `ret`, and the result on `r`: `(r,.f.k,[any],T)`. -/
def RrM : AFact := ⟨⟨4, [1, 4], .any, .conc 1⟩, true⟩
def RrM' : AFact := ⟨⟨2, [1, 4], .any, .conc 1⟩, true⟩

/-! ### The trace, step by step (each step is checked by `decide`) -/

-- the binding into `c` gives the added fact `(arg,.h.i.f,[any],T)`
example : A ∈ (applyEdge X bx.1 bx.2).facts := by decide
-- the added fact is below the demand chain `arg.h.i`: `emitM` gives the WHOLE added fact
example : emitM ddM.din A.fact = some JM := by decide
example : startFact JM = A := by decide
-- `ret = arg.h.i` gives the exit fact `(ret,.f,[any],T)`
example : GM ∈ (transfer cnt 3 rd2 A).facts := by decide
example : P2.exit 1 = 1 := by decide
-- `restrictU` keeps the exit edge as `(ret,.f.k,[any],T)`
example : restrictU JM GM ddM = some GM' := by decide
-- THE VECTOR: on this exit edge `restrictU` and `restrictS` give the same result
example : restrictS JM GM ddM = some GM' := by decide
example : restrictU JM GM ddM = restrictS JM GM ddM := by decide
-- the caller fact satisfies the premise (overlap, and the marks match)
example : satO JM A.fact = true := by decide
example : satI JM A.fact = true := by decide
-- the summary application and the binding back give `(r,.f.k,[any],T)`
example : RrM ∈ (applySummary A JM GM').facts := by decide
example : RrM' ∈ (applyEdge RrM br.1 br.2).facts := by decide
example : limitF cnt 3 RrM' = RrM' := by decide
-- the sink triggers (no request)
example : check zeroFact RrM' sink2 = .triggered := by decide

end Prog2

open Prog2 in
/-- Version 4: the vulnerability of program 2 is real, and the call step on it is demanded by
    `dem2M` (the entry location WITH its mark `T`, and the exit location). -/
theorem p2_reachR_M : ReachR P2 dem2M [0] 0 2 ⟨2, [1, 4, 5], 1⟩ := by
  have f0 : FlowR P2 dem2M 0 zeroLoc 1 l0 :=
    FlowR.step (FlowR.start 0 zeroLoc) (s := src2) hE00
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_src⟩)
  have fc : FlowR P2 dem2M 1 l1 1 l2 :=
    FlowR.step (FlowR.start 1 l1) (s := rd2) hE10
      (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_rd⟩)
  have f2 : FlowR P2 dem2M 0 zeroLoc 2 l3 :=
    FlowR.call f0 (c := callC2) hE01 (List.Mem.head _) den_in fc (d := ddM) ⟨rfl, rfl⟩
      ⟨rfl, ⟨[1, 4, 5], rfl, trivial⟩, rfl⟩ rfl ⟨rfl, [5], rfl, trivial⟩ (List.Mem.head _) den_out
  exact ReachR.root (List.Mem.head _) f2

#print axioms p2_reachR_M

open Prog2 in
/-- Version 4: the run with `emitM`, `satI` and the AGREED restriction `restrictU` finds the
    vulnerability of program 2 (in the demand layer). The exit fact of `c` is `(ret,.f,[any],T)`,
    not a correlated `*`, so `restrictU` keeps it. -/
theorem p2_found_M :
    DR P2 cnt 3 dem2M emitM satI restrictU noRecs sinks2 [0] (.vuln 0 2 sink2 true) := by
  have r0 : R2M (.init 0 zeroFact) := DR.root (List.Mem.head _)
  have e0 : R2M (.edge 0 zeroFact 0 Z) := DR.start r0
  have e1 : R2M (.edge 0 zeroFact 1 X) := DR.step e0 (s := src2) hE00 (by decide)
  -- the added fact of c is A = (arg,.h.i.f,[any],T); emitM gives the fact itself
  have ad : R2M (.added 1 A.fact) :=
    DR.added (c := callC2) (e := bx) (a := A) e1 hE01 (List.Mem.head _) (by decide)
  have iJ : R2M (.init 1 JM) := DR.initR (d := ddM) ad ⟨rfl, rfl⟩ (by decide)
  have eJ0 : R2M (.edge 1 JM 0 A) := DR.start iJ
  -- the exit fact of c: (ret,.f,[any],T)
  have eJ1 : R2M (.edge 1 JM 1 GM) := DR.step eJ0 (s := rd2) hE10 (by decide)
  -- restrictU keeps it as (ret,.f.k,[any],T); the caller fact satisfies JM;
  -- the result is (r,.f.k,[any],T)
  have e2 : R2M (.edge 0 zeroFact 2 (limitF cnt 3 RrM')) :=
    DR.ret (c := callC2) (e1 := bx) (a := A) (j := JM) (g := GM) (d := ddM) (g' := GM') (r := RrM)
      (e2 := br) e1 hE01 (List.Mem.head _) (by decide) iJ eJ1 ⟨rfl, rfl⟩ (by decide) (by decide)
      (by decide) (List.Mem.head _) (by decide)
  have e2' : R2M (.edge 0 zeroFact 2 RrM') := e2
  exact DR.vuln e2' (s := sink2) (List.Mem.head _) (by decide)

#print axioms p2_found_M

/-! ## Part 5. Program 3: a persisted record is reused by `applicable` (the user's decision)

```
root():   x.f = source();  r = id(x);  sink(r.f);    // method 0, the call at node 1, sink at 2
id(arg0): ret = arg0;                                // method 1, exit node 1
```
  Accessor f=1. Bases zero=0, x=1, r=2, arg0=3, ret=4. Mark T=1. L = 3.
  Run 1 (the closure `D` with `policy1`) serves the added fact `(arg0,.f,$,T)` of `id` with the
  most abstract fact `(arg0,.,*,{},*)`; its exit record is `(arg0,.,*,{},*) → (ret,.,*,{},*)`
  (`p3_run1_record`). A later restricted run reuses it. The caller fact (bound into `id`) is
  `(arg0,.f,$,T)`. The record premise does NOT lie inside it (`satI` is false: with the version-5
  rule alone the record never applies), but it COVERS it (`applicable` is true). The rule
  `retRec` applies the record and gives `(ret,.f,$,T)`; the binding back gives `(r,.f,$,T)`, in
  the NORMAL layer (`p3_reuse`), and the sink triggers on it (`p3_found_reuse`). The run has NO
  demand: `id` gets no initial fact, so the record is the only summary of `id`. -/

def src3 : Stmt := ⟨[0], [(zeroFact, zeroFact), (zeroFact, ⟨1, [1], .exact, .conc 1⟩)]⟩
def callId : Call := ⟨1, [1, 2], [(⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)],
  [(⟨4, [], st, .star⟩, ⟨2, [], st, .star⟩)]⟩
def cp3 : Stmt := ⟨[3, 4], [(⟨3, [], st, .star⟩, ⟨3, [], st, .star⟩),
  (⟨3, [], st, .star⟩, ⟨4, [], st, .star⟩)]⟩
def P3 : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 2,
  [(0, 0, .stmt src3, 1), (0, 1, .call callId, 2), (1, 0, .stmt cp3, 1)]⟩
def sink3 : PFact := ⟨2, [1], .exact, .conc 1⟩
def sinks3 : List (MethodId × Node × PFact) := [(0, 2, sink3)]
/-- No demand: the restricted run emits no initial fact for `id`. -/
def noDem : MethodId → DemandEdge → Prop := fun _ _ => False

namespace Prog3

def bx : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
def br : MicroEdge := (⟨4, [], st, .star⟩, ⟨2, [], st, .star⟩)

def Z : AFact := ⟨zeroFact, false⟩
/-- The source fact `(x,.f,$,T)`, in the normal layer. -/
def X : AFact := ⟨⟨1, [1], .exact, .conc 1⟩, false⟩
/-- The caller fact bound into `id`: `(arg0,.f,$,T)`. -/
def A : AFact := ⟨⟨3, [1], .exact, .conc 1⟩, false⟩
/-- The run-1 record of `id`: the premise `(arg0,.,*,{},*)` and the conclusion `(ret,.,*,{},*)`. -/
def J : PFact := ⟨3, [], st, .star⟩
def G : AFact := ⟨⟨4, [], st, .star⟩, false⟩
/-- The record application `(ret,.f,$,T)` and the binding back `(r,.f,$,T)`, both normal. -/
def Rr : AFact := ⟨⟨4, [1], .exact, .conc 1⟩, false⟩
def Rr' : AFact := ⟨⟨2, [1], .exact, .conc 1⟩, false⟩

theorem hE00 : (0, 0, Instr.stmt src3, 1) ∈ P3.edges := List.Mem.head _
theorem hE01 : (0, 1, Instr.call callId, 2) ∈ P3.edges := List.Mem.tail _ (List.Mem.head _)
theorem hE10 : (1, 0, Instr.stmt cp3, 1) ∈ P3.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

end Prog3

/-- The persisted records of the later run: the one exit record of `id` from run 1. -/
def recs3 : MethodId → PFact × AFact → Prop := fun m jg => m = 1 ∧ jg = (Prog3.J, Prog3.G)

namespace Prog3

/-! ### The trace, step by step (each step is checked by `decide`) -/

-- the source `(x,.f,$,T)` and the binding into `id`: the caller fact `(arg0,.f,$,T)`
example : X ∈ (transfer cnt 3 src3 Z).facts := by decide
example : A ∈ (applyEdge X bx.1 bx.2).facts := by decide
-- run 1: `policy1` serves it with the most abstract fact, the record premise `J`
example : policy1 1 A.fact = J := by decide
example : startFact J = ⟨J, false⟩ := by decide
example : G ∈ (transfer cnt 3 cp3 ⟨J, false⟩).facts := by decide
-- THE POINT: the record premise does not lie inside the caller fact (`satI` fails), but it
-- covers the caller fact (`applicable`, the run-1 direction)
example : satI J A.fact = false := by decide
example : applicable J A.fact = true := by decide
-- the application is EXACT and stays concrete and in the normal layer: `(ret,.f,$,T)`, then
-- `(r,.f,$,T)` (no `*` tail, no abstract mark)
example : (applySummary A J G).facts = [Rr] ∧ (applySummary A J G).reqs = [] := by decide
example : (applyEdge Rr br.1 br.2).facts = [Rr'] ∧ (applyEdge Rr br.1 br.2).reqs = [] := by decide
example : limitF cnt 3 Rr' = Rr' := by decide
example : check zeroFact Rr' sink3 = .triggered := by decide
-- an `[any]` caller fact in the demand layer: the record applies by `applicable` too, and the
-- result stays `[any]` in the demand layer (no `*` tail with a concrete mark)
example : satI J ⟨3, [1], .any, .conc 1⟩ = false := by decide
example : applicable J ⟨3, [1], .any, .conc 1⟩ = true := by decide
example : (applySummary ⟨⟨3, [1], .any, .conc 1⟩, true⟩ J G).facts =
    [⟨⟨4, [1], .any, .conc 1⟩, true⟩] := by decide

end Prog3

open Prog3 in
/-- Run 1 of program 3 has the record `(arg0,.,*,{},*) → (ret,.,*,{},*)` of `id` as an exit edge
    (in the normal layer), so it is a persisted record of run 1. -/
theorem p3_run1_record : D P3 cnt 3 policy1 sinks3 [0] (.edge 1 J (P3.exit 1) G) := by
  have r0 : D P3 cnt 3 policy1 sinks3 [0] (.init 0 zeroFact) := D.root (List.Mem.head _)
  have e0 : D P3 cnt 3 policy1 sinks3 [0] (.edge 0 zeroFact 0 Z) := D.start r0
  have e1 : D P3 cnt 3 policy1 sinks3 [0] (.edge 0 zeroFact 1 X) :=
    D.step e0 (s := src3) hE00 (by decide)
  have ad : D P3 cnt 3 policy1 sinks3 [0] (.added 1 A.fact) :=
    D.added (c := callId) (e := bx) (a := A) e1 hE01 (List.Mem.head _) (by decide)
  have i1 : D P3 cnt 3 policy1 sinks3 [0] (.init 1 J) := by
    have h := D.initA (α := policy1) ad
    have e : policy1 1 A.fact = J := by decide
    rw [e] at h
    exact h
  have s1 : D P3 cnt 3 policy1 sinks3 [0] (.edge 1 J 0 ⟨J, false⟩) := D.start i1
  exact D.step s1 (s := cp3) hE10 (by decide)

#print axioms p3_run1_record

/-- Every record of `recs3` is an exit edge of run 1 (the hypothesis of `RExact.recs_of_D` with
    `RExact.recs_mono`). -/
theorem recs3_run1 : ∀ m jg, recs3 m jg → D P3 cnt 3 policy1 sinks3 [0] (.edge m jg.1 (P3.exit m) jg.2) := by
  intro m jg h
  obtain ⟨rfl, rfl⟩ := h
  exact p3_run1_record

#print axioms recs3_run1

/-- The restricted run of program 3: the spec rules, no demand, and the run-1 record. -/
abbrev R3 := DR P3 cnt 3 noDem emitM satI restrictU recs3 sinks3 [0]

open Prog3 in
/-- THE POINT OF THE CHANGE. In a restricted run, the run-1 record `(arg0,.,*,{},*) →
    (ret,.,*,{},*)` applies to the caller fact `(arg0,.f,$,T)` (by `applicable`; `satI` is false)
    and gives `(r,.f,$,T)` in the NORMAL layer. -/
theorem p3_reuse : R3 (.edge 0 zeroFact 2 Rr') := by
  have r0 : R3 (.init 0 zeroFact) := DR.root (List.Mem.head _)
  have e0 : R3 (.edge 0 zeroFact 0 Z) := DR.start r0
  have e1 : R3 (.edge 0 zeroFact 1 X) := DR.step e0 (s := src3) hE00 (by decide)
  have h := DR.retRec (c := callId) (e1 := bx) (a := A) (j := J) (g := G) (r := Rr) (e2 := br)
    (r' := Rr') e1 hE01 (List.Mem.head _) (by decide) ⟨rfl, rfl⟩
    (Or.inr (by decide : applicable J A.fact = true)) (by decide) (List.Mem.head _) (by decide)
  exact h

#print axioms p3_reuse

open Prog3 in
/-- The reused record finds the vulnerability of program 3 in the normal layer (a complete sink
    edge), with no demand and no initial fact of `id`. -/
theorem p3_found_reuse : R3 (.vuln 0 2 sink3 false) :=
  DR.vuln p3_reuse (s := sink3) (List.Mem.head _) (by decide)

#print axioms p3_found_reuse

end ApSpec.RCases
