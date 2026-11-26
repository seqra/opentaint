import ApSpec.AnyTaintExDefs
import ApSpec.HandoffDefs
import ApSpec.AbsDefs
import ApSpec.CurrentMustReverse
import ApSpec.BackMustRun
import ApSpec.BackMustView
import ApSpec.BackNDRefine
import ApSpec.BackCondRules

/-!
# Principal examples of `spec/backward-condition-progress.md`

Each example of the spec is a closed computation of the executable model, checked by `decide`.
The names `ex_*` are the example ids of the spec.

Names: bases `x y z ret arg0 va vb`, accessors `f g h k`, marks `T U`.
-/

namespace ApSpec.BackCondEx

open ApSpec ApSpec.AnyTaintEx ApSpec.Handoff

abbrev x : Base := 1
abbrev y : Base := 2
abbrev z : Base := 3
abbrev ret : Base := 4
abbrev arg0 : Base := 5
abbrev va : Base := 6
abbrev vb : Base := 7
abbrev f : Acc := 1
abbrev g : Acc := 2
abbrev h : Acc := 3
abbrev k : Acc := 4
abbrev tT : Mark := 7
abbrev tU : Mark := 8
abbrev T : MarkA := .conc tT
abbrev U : MarkA := .conc tU

def pf (b : Base) (p : List Acc) (κ : Kind) (μ : MarkA) : PFact := ⟨b, p, κ, μ⟩
/-- A NORMAL annotated fact. -/
def nx (φ : PFact) (ex : Excl := Excl.empty) : XFact := ⟨⟨φ, false⟩, ex⟩
/-- A DEMAND annotated fact (no exclusion). -/
def dx (φ : PFact) : XFact := ⟨⟨φ, true⟩, Excl.empty⟩
abbrev s0 : Kind := .star Excl.empty

/-! ## §2.2 Rule conditions -/

/-- Unary `ContainsMarkOnAnyField(ret, T)`: one location below `ret` fires it. -/
theorem ex_c1 : BackCond.fires [[pf ret [] .any T]] [⟨ret, [f], tT⟩] = true := by decide
/-- ND `a.$(T) ∧ b.[any](U)`: `b.f(U)` alone does not fire it. -/
theorem ex_c2 : BackCond.fires [[pf va [] .exact T, pf vb [] .any U]] [⟨vb, [f], tU⟩] = false := by
  decide
/-- ND: with `a(T)` it fires. -/
theorem ex_c3 :
    BackCond.fires [[pf va [] .exact T, pf vb [] .any U]] [⟨va, [], tT⟩, ⟨vb, [f], tU⟩] = true := by
  decide

/-! ## §3.1 Initial fact emission: premise, must flag, exclusion, start -/

def emit (d a : PFact) (am : Bool) (aex : Excl) : Option ((PFact × Bool × Excl) × XFact) :=
  (emitTX emitX d a am aex).map (fun r => (r, startX r.1 r.2.1 r.2.2))

theorem ex_e1 : emit (pf x [] .any T) (pf x [f] .exact T) false Excl.empty =
    some ((pf x [f] .exact T, false, Excl.empty), nx (pf x [f] .exact T)) := by decide
theorem ex_e2 : emit (pf x [f] .any T) (pf x [] .any T) false Excl.empty =
    some ((pf x [f] .any T, false, Excl.empty), dx (pf x [f] .any T)) := by decide
theorem ex_e3 : emit (pf x [f] .any T) (pf x [] .any T) true (.set [g]) =
    some ((pf x [f] .any T, true, Excl.empty), nx (pf x [f] .any T)) := by decide
theorem ex_e4 : emit (pf x [f] .any T) (pf x [] .any T) true (.set [f]) = none := by decide
theorem ex_e5 : emit (pf x [] .any T) (pf x [] .any T) true (.set [g]) =
    some ((pf x [] .any T, true, .set [g]), nx (pf x [] .any T) (.set [g])) := by decide
theorem ex_e6 : emit (pf x [] .exact T) (pf x [] .any T) true (.set [g]) =
    some ((pf x [] .exact T, false, Excl.empty), nx (pf x [] .exact T)) := by decide
/-- Abstract `D-c`: the FLOW form, whatever the added fact. -/
theorem ex_e7 : Abs.emitW (pf x [] .any .star) (pf x [] .any T) = some (pf x [] s0 .star) := by
  decide
theorem ex_e8 : emit (pf x [] .any T) (pf x [f] .exact U) false Excl.empty = none := by decide

/-! ## §3.2 Summary edge ∩ demand edge -/

theorem ex_r1 : restrictI (pf arg0 [] .exact T) ⟨pf ret [f, g] .exact T, false⟩
    ⟨pf arg0 [] .any T, some (pf ret [] .any T)⟩ = some ⟨pf ret [f, g] .exact T, false⟩ := by decide
theorem ex_r2 : restrictI (pf arg0 [] .exact T) ⟨pf ret [] .any T, true⟩
    ⟨pf arg0 [] .any T, some (pf ret [f] .exact T)⟩ = some ⟨pf ret [f] .exact T, true⟩ := by decide
theorem ex_r3 : restrictI (pf arg0 [] .exact T) ⟨pf ret [f] .exact T, false⟩
    ⟨pf arg0 [] .any T, none⟩ = none := by decide
theorem ex_r4 : restrictI (pf arg0 [] .exact T) ⟨pf ret [] .exact U, false⟩
    ⟨pf arg0 [] .exact T, some (pf ret [] .exact T)⟩ = none := by decide
theorem ex_r5 : restrictI (pf arg0 [] .any T) ⟨pf ret [] .exact T, false⟩
    ⟨pf arg0 [f] .any T, some (pf ret [] .any T)⟩ = none := by decide
theorem ex_r6 : restrictConcX (nx (pf ret [f] .exact T)) (pf ret [] s0 T) =
    some (nx (pf ret [f] .exact T)) := by decide
theorem ex_r7 : restrictConcX (nx (pf ret [f] .exact T)) (pf ret [] .exact T) = none := by decide
theorem ex_r8 : restrictConcX (nx (pf ret [] .any T) (.set [h])) (pf ret [f] .any T) =
    some (nx (pf ret [f] .any T)) := by decide
theorem ex_r9 : restrictConcX (nx (pf ret [] .any T) (.set [h])) (pf ret [h] .any T) = none := by
  decide
theorem ex_r10 : restrictConcX (nx (pf ret [] .any T) (.set [h])) (pf ret [f] .exact T) =
    some (nx (pf ret [f] .exact T)) := by decide
/-- The model keeps `/{h}` at the same path under a `*/{k}` demand; ap.md §6.4 gives `/{h,k}`. -/
theorem ex_r11_model : restrictConcX (nx (pf ret [] .any T) (.set [h])) (pf ret [] (.star (.set [k])) T) =
    some (nx (pf ret [] .any T) (.set [h])) := by decide
/-- Backward edge `ret.[any-taint] → arg0.[any-taint]` under the demand `D-p = arg0.h.$`. -/
theorem ex_r12 : restrictI (pf ret [] .any T) ⟨pf arg0 [] .any T, false⟩
    ⟨pf ret [] .any T, some (pf arg0 [h] .exact T)⟩ = some ⟨pf arg0 [h] .exact T, false⟩ := by decide

/-! ## §3.3 Application in the own direction: `(inside, applicable, results with the MUST rule)` -/

def app (a : XFact) (j : PFact) (mj : Bool) (jex : Excl) (gc : XFact) : Bool × Bool × List XFact :=
  let ok := satX j jex a.af.fact a.ex
  (ok, applicable j a.af.fact, (applySummaryX a j jex gc).facts.map (recLayerX mj ok))

theorem ex_a1 : app (nx (pf arg0 [] .exact T)) (pf arg0 [] .exact T) false Excl.empty
    (nx (pf ret [f] .exact T)) = (true, true, [nx (pf ret [f] .exact T)]) := by decide
theorem ex_a2 : app (nx (pf arg0 [h] .exact T)) (pf arg0 [] s0 .star) false Excl.empty
    (nx (pf ret [f] s0 .star)) = (false, true, [nx (pf ret [f, h] .exact T)]) := by decide
theorem ex_a3 : app (dx (pf arg0 [] .exact T)) (pf arg0 [] .exact T) false Excl.empty
    (nx (pf ret [f] .exact T)) = (true, true, [dx (pf ret [f] .exact T)]) := by decide
theorem ex_a4 : app (nx (pf arg0 [] .any T)) (pf arg0 [] .any T) true Excl.empty
    (nx (pf ret [g] .any T)) = (true, true, [nx (pf ret [g] .any T)]) := by decide
theorem ex_a5 : app (nx (pf arg0 [h] .any T)) (pf arg0 [] .any T) true Excl.empty
    (nx (pf ret [g] .any T)) = (false, true, [dx (pf ret [g] .any T)]) := by decide
theorem ex_a6 : (app (nx (pf arg0 [h] .exact T)) (pf arg0 [] .any T) true Excl.empty
    (nx (pf ret [g] .any T))).1 = false ∧ (app (nx (pf arg0 [h] .exact T)) (pf arg0 [] .any T) true
    Excl.empty (nx (pf ret [g] .any T))).2.1 = false := by decide
/-- B2: backward must record `ret.[any-taint] → arg0.[any-taint]`, inside. -/
theorem ex_a7 : app (nx (pf ret [] .any T)) (pf ret [] .any T) true Excl.empty
    (nx (pf arg0 [] .any T)) = (true, true, [nx (pf arg0 [] .any T)]) := by decide
/-- B2: the same record, applicable but not inside: DEMAND. -/
theorem ex_a8 : app (nx (pf ret [f] .any T)) (pf ret [] .any T) true Excl.empty
    (nx (pf arg0 [] .any T)) = (false, true, [dx (pf arg0 [] .any T)]) := by decide

/-! ## §3.4 Read view in the opposite direction -/

open ApSpec.CurrentMustReverse in
def viewApp (j : PFact) (mj : Bool) (jex : Excl) (gc : XFact) (a : AFact) :
    Option (ReadView × List AFact) :=
  (readView ⟨j, mj, jex, gc⟩).map (fun v => (v, (applySummary a v.1 v.2).facts))

theorem ex_v1 : viewApp (pf arg0 [] .exact T) false Excl.empty (nx (pf ret [] .any T))
    ⟨pf ret [h] .exact T, false⟩ =
    some ((pf ret [] s0 T, ⟨pf arg0 [] .exact T, false⟩), [⟨pf arg0 [] .exact T, false⟩]) := by decide
theorem ex_v2 : viewApp (pf arg0 [] .any T) true Excl.empty (nx (pf ret [g] .any T))
    ⟨pf ret [g, h] .exact T, false⟩ =
    some ((pf ret [g] s0 T, ⟨pf arg0 [] .any T, true⟩), [⟨pf arg0 [] .any T, true⟩]) := by decide
theorem ex_v3 : viewApp (pf arg0 [] .any T) true Excl.empty (nx (pf ret [f] .exact T))
    ⟨pf ret [f] .exact T, false⟩ =
    some ((pf ret [f] .exact T, ⟨pf arg0 [] .any T, true⟩), [⟨pf arg0 [] .any T, true⟩]) := by decide
/-- B2: the forward view of the backward must record `ret.[any-taint] → arg0.[any-taint]`. -/
theorem ex_v4 : BackMustView.viewF ⟨1, pf ret [] .any T, Excl.empty, nx (pf arg0 [] .any T)⟩
    (pf arg0 [h] .exact T) Excl.empty = some (dx (pf ret [] .any T)) := by decide
theorem ex_v5 : BackMustView.viewF ⟨1, pf ret [] .any T, Excl.empty, nx (pf arg0 [] .any T)⟩
    (pf arg0 [h] .exact U) Excl.empty = none := by decide

/-! ## §5 ND refinement: literals `0 = va.$(T)`, `1 = vb.[any](U)` -/

def lits : List PFact := [pf va [] .exact T, pf vb [] .any U]

theorem ex_n1 : BackND.refine lits [(0, pf va [] .exact T, Excl.empty), (1, pf vb [f] .exact U, Excl.empty),
    (1, pf vb [g, h] .exact U, Excl.empty)] =
    [(0, pf va [] .exact T, Excl.empty), (1, pf vb [f] .exact U, Excl.empty),
     (1, pf vb [g, h] .exact U, Excl.empty)] := by decide
theorem ex_n2 : BackND.refine lits [(1, pf vb [g] .any U, .set [k])] =
    [(0, pf va [] .exact T, Excl.empty), (1, pf vb [g] .any U, .set [k])] := by decide
theorem ex_n3 : BackND.refine lits [] =
    [(0, pf va [] .exact T, Excl.empty), (1, pf vb [] .any U, Excl.empty)] := by decide
/-- A capture with the abstract mark: literal 1 gets no seed (the normal form prevents it). -/
theorem ex_n4 : BackND.refine lits [(1, pf vb [f] s0 .star, Excl.empty)] =
    [(0, pf va [] .exact T, Excl.empty)] := by decide

/-! ## §7 S-H1: backward transfer over `x.f = y` and `x.f = z` (reversed) -/

def sY : Stmt := ⟨[x], [(pf x [f] s0 .star, pf y [] s0 .star), (pf x [] (.star (.set [f])) .star,
  pf x [] (.star (.set [f])) .star)]⟩
def sZ : Stmt := ⟨[x], [(pf x [f] s0 .star, pf z [] s0 .star), (pf x [] (.star (.set [f])) .star,
  pf x [] (.star (.set [f])) .star)]⟩
def tr (s : Stmt) (c : XFact) : List XFact := (BackMust.transferXB (fun _ => false) (fun _ => true) 9 s c).facts

theorem ex_t1 : (tr sY (nx (pf x [] .any T))).flatMap (tr sZ) =
    [nx (pf y [] .any T), nx (pf x [] .any T) (.set [f, f, f, f])] := by decide
theorem ex_t2 : (tr sY (dx (pf x [] .any T))).flatMap (tr sZ) =
    [dx (pf y [] .any T), dx (pf z [] .any T), dx (pf x [] .any T)] := by decide

end ApSpec.BackCondEx

#print axioms ApSpec.BackCondEx.ex_c3
#print axioms ApSpec.BackCondEx.ex_e7
#print axioms ApSpec.BackCondEx.ex_r11_model
#print axioms ApSpec.BackCondEx.ex_a6
#print axioms ApSpec.BackCondEx.ex_v4
#print axioms ApSpec.BackCondEx.ex_n4
#print axioms ApSpec.BackCondEx.ex_t1
