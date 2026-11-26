/-
  ApSpec.BackMustView — the FORWARD read view of a backward MUST record (proposed rule B2), and the
  hand-off question: may such a record replace the forward demand edge of its method?

  ## What is modelled

  A backward MUST record (`BRec`) of a method `M` is a backward summary `jb → gb`: the premise `jb`
  is a requirement at the FORWARD EXIT of `M`, a must-premise (tail `[any-taint]`, concrete mark,
  exclusion `jex`); the conclusion `gb : XFact` is at the FORWARD ENTRY, normal. Its meaning is
  END-EXACT, read forward (`EndExactB`): every admitted location of `gb` flows forward in `P` to SOME
  admitted location of `jb`. The FORWARD READ VIEW `viewF r a aex`: a forward added fact `(a, aex)`
  at the entry that MEETS `gb` (`meetB`: `overlapX` of the admitted location sets and `markMeetB` of
  the marks) gives `viewOut r` = `jb` with the `.any` tail and the mark of `jb`, in the DEMAND layer,
  with no exclusion; otherwise `none`. The hand-off question is whether such a record may replace the
  forward demand edge `(D-c = gb, D-p = jb)` of `M` (spec ap.md §9.2, §8.5, §8.7 R1/R3).

  ## Results

  * `viewF_demand`: every view result is DEMAND, has no exclusion, and is `jb` with the `.any`
    tail. `viewF_stays_demand`: `applyEdge`, `applySummary` and `transfer` on a view result give
    only DEMAND results.
  * `viewF_sound` (hypothesis `BComplete`): if `(a, aex)` covers `l0` and `Flow P M l0 (P.exit M) l1`
    with `l1` an admitted `jb` location, the view gives a result that covers `l1`.
    `viewF_sound_pair` (also `jb.mark = .conc T`): the result relates the pair, `denX a aex x l0 l1`.
    So the view is SOUND but only DEMAND (uncorrelated).
  * `Cex.viewF_not_exact` (a real `Flow` on a tiny `Program`, inverted by `Cex.flow_inv`): a
    well-formed B2 record of a well-formed program, END-EXACT in `P` and `BComplete`, whose view on
    `arg0.x $ (T)` gives `ret.[any] (T)`; the view relates `arg0.x` to `ret`, which is not a flow
    (nothing flows to `ret`, `Cex.no_flow_to_ret`). Published NORMAL, the result would break the
    pair-exact motive `EdgeOKX` (non-must reading) and even its end-exact (must) reading.
  * `Cex.cex_drop_forward_demand` (`decide` on `transfer`, `applyEdge`/`applySummary`, `limitF`,
    `check`, `emitM`, `restrictU`, `startFact`): callee `ret.f.g = arg0`, caller added fact
    `arg0.x $ (T)` normal, sink `ret.[any] (T)`. (a) Run-1 field limit 1, every accessor counted:
    the result is cut to `ret.f.[any]`, DEMAND. (b) Field limit 3 with the forward demand edge
    `(gb, jb)`: `ret.f.g.x $ (T)`, NORMAL, and `check` gives `.triggered` from a normal edge
    (confirmable). (c) The backward MUST record's forward view: `ret.[any] (T)`, DEMAND; the sink
    triggers only in the DEMAND layer. CONCLUSION: if the hand-off drops the forward demand edge of
    a callee because a backward MUST record exists, the next forward run keeps only (c), and the
    confirmation that the status quo gets in (b) is lost. `Cex.back_derives_gb`: the backward
    step (reversed write on the normal must start `ret.[any-taint] (T)`) gives exactly `gb`.
  * `guard_keeps_normal` (the guard, PROVED for canonical FLOW records): a normal, non-must forward
    record `b.p.*/{} (*) → b'.q.*/{} (*)` of `M` that is PAIR-EXACT (`FPairExact`) and COMPLETE
    towards `jb` (`FComplete`), with a premise covering `gb` (`GuardCovers`), applied to a normal
    `$`/`[any]` added fact with a concrete mark inside `gb`: (1) every result is NORMAL; (2) every
    real pair from the added fact into `jb` is related by a result; (3) every pair of a result is a
    caller pair followed by a real flow of `M`. `Cex.guard_instance`: on the same callee the
    field-limit-3 record `arg0.* → ret.f.g.*` satisfies the guard and gives the NORMAL `ret.f.g.x $`;
    after run 1 the summary is DEMAND, so no such record exists and the guard keeps the demand edge.

  ## Hypotheses (not proved here)

  * `BComplete P r`: the soundness of the backward run for the record, read forward.
  * `FPairExact`, `FComplete`: S14 exactness and forward completeness of the forward record.
  * The shape guards: `jb.mark = .conc T` for `viewF_sound_pair`; the FLOW shapes, a concrete mark
    and a `$`/`[any]` tail of the added fact, and `c` inside `gb` for `guard_keeps_normal`.

  ## Counterexample data (`Cex`)

  Bases `arg0 = 1`, `ret = 2`; accessors `f = 1`, `g = 2`, `x = 3`; mark `T = 7`. The callee is
  method `1` (entry node `0`, exit node `1`) with one statement that touches `arg0` and `ret`: the
  write `arg0.* → ret.f.g.*` and the keep edge `arg0.* → arg0.*`. The record is
  `jb = ret.[any-taint] (T)`, `jex = {}`, `gb = arg0.[any] (T)` normal.

  ## Model vs production

  * One leaf: production reads views leaf by leaf on a conclusion tree (R3); the module has one
    singleton record and one leaf, no store lookup (R2), no statics (F78), no cleaner or type filter.
  * The backward closure that would produce a B2 record is not modelled (current spec W8 (d): the
    backward run has no `[any-taint]`); `back_derives_gb` is one base-operation step, with the must
    premise started NORMAL as `AnyTaintEx.startX` does (the base `startFact` would demote it).
  * The sink is checked on the callee exit fact (`ret` named the same in the caller: the return
    binding is the identity), with `zeroFact` as the caller's initial fact; the concrete mark of the
    fact decides `check`. The transfer results also carry the keep edge fact `arg0.x $`.
  * `guard_keeps_normal` states the summary application (`applySummary`), not the R4 selection
    `applicable || inside`; it covers only canonical FLOW records with empty exclusions and star
    marks. For a `*/E` conclusion with `E ≠ {}` the base model demotes an `[any]` input at the
    premise path, and for the other record shapes no normality claim is made.
  * `EndExactB` has a validity predicate `ok`; `BComplete`, `FComplete`, `FPairExact` have none (the
    counterexample uses `ok = True` and has no type filter).

  All proofs are constructive: only `propext` and `Quot.sound` (see the `#print axioms` lines).
-/
import ApSpec.AnyTaintExDefs
import ApSpec.AnyTaintExCov
import ApSpec.Core
import ApSpec.Exact
import ApSpec.Invariant

namespace ApSpec.BackMustView
open ApSpec ApSpec.AnyTaintEx

/-! ## 1. The backward MUST record and its forward read view -/

/-- A backward MUST record (rule B2) of the method `method`: the backward summary `jb → gb`.
    `jb` is the premise at the FORWARD EXIT (a must-premise: tail `[any-taint]`, concrete mark,
    exclusion `jex`); `gb` is the conclusion at the FORWARD ENTRY (normal). This carrier does not
    prove store provenance; `wfB` is the local shape. -/
structure BRec where
  method : MethodId
  jb : PFact
  jex : Excl
  gb : XFact
deriving DecidableEq, Repr

/-- The local B2 shape: `jb` is `[any-taint]` with a concrete mark, `gb` is normal. -/
def BRec.wfB (r : BRec) : Bool :=
  (r.jb.kind == .any) && concB r.jb.mark && !r.gb.af.demand

/-- Two marks admit a common concrete mark. (`*∖x` and `*∖y` always do: marks are unbounded.) -/
def markMeetB : MarkA → MarkA → Bool
  | .conc t,   .conc u   => Nat.beq t u
  | .conc t,   .starEx x => !memB t x
  | .starEx x, .conc t   => !memB t x
  | _,         _         => true

/-- The forward added fact `(a, aex)` MEETS the conclusion `gb`: the admitted location sets
    overlap (`overlapX`) and the marks meet. -/
def meetB (a : PFact) (aex : Excl) (g : XFact) : Bool :=
  overlapX a aex g.af.fact g.ex && markMeetB a.mark g.af.fact.mark

/-- The one result of the view: `jb` with the `.any` tail and the mark of `jb`, in the DEMAND
    layer, with no exclusion (the must exclusion `jex` is forgotten). -/
def viewOut (r : BRec) : XFact :=
  ⟨⟨⟨r.jb.base, r.jb.path, .any, r.jb.mark⟩, true⟩, Excl.empty⟩

/-- THE FORWARD READ VIEW of a backward MUST record: an added fact at the forward entry of the
    method that meets `gb` gives `viewOut r`; otherwise nothing. -/
def viewF (r : BRec) (a : PFact) (aex : Excl) : Option XFact :=
  if meetB a aex r.gb then some (viewOut r) else none

/-! ## 2. The view is DEMAND -/

/-- `viewF_demand`: every result of the view is in the DEMAND layer, has no exclusion, and is
    `jb` with the `.any` tail. -/
theorem viewF_demand {r : BRec} {a : PFact} {aex : Excl} {x : XFact}
    (h : viewF r a aex = some x) :
    x.af.demand = true ∧ x.ex = Excl.empty ∧
      x.af.fact = ⟨r.jb.base, r.jb.path, .any, r.jb.mark⟩ := by
  unfold viewF at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- Every later operation on a view result stays in the DEMAND layer: the micro edge, the summary
    edge and the statement transfer (`Invariant.*_demand_monotone`). -/
theorem viewF_stays_demand {r : BRec} {a : PFact} {aex : Excl} {x : XFact}
    (h : viewF r a aex = some x) :
    (∀ fr to y, y ∈ (applyEdge x.af fr to).facts → y.demand = true) ∧
    (∀ j g y, y ∈ (applySummary x.af j g).facts → y.demand = true) ∧
    (∀ counted L s y, y ∈ (transfer counted L s x.af).facts → y.demand = true) := by
  have hd := (viewF_demand h).1
  exact ⟨fun _ _ _ hy => Invariant.applyEdge_demand_monotone hd hy,
    fun _ _ _ hy => Invariant.applySummary_demand_monotone (Or.inl hd) hy,
    fun _ _ _ _ hy => Invariant.transfer_demand_monotone hd hy⟩

/-! ## 3. The view is sound -/

theorem markMeetB_of_common {a b : MarkA} {m : Mark} (ha : a.admits m) (hb : b.admits m) :
    markMeetB a b = true := by
  cases a with
  | star => cases b <;> rfl
  | conc t =>
    have h1 : m = t := ha
    cases b with
    | star => rfl
    | conc u =>
      have h2 : m = u := hb
      show Nat.beq t u = true
      rw [← h1, ← h2]; exact Nat.beq_refl m
    | starEx x =>
      have h2 : memB m x = false := hb
      show (!memB t x) = true
      rw [← h1, h2]; rfl
  | starEx x =>
    have h1 : memB m x = false := ha
    cases b with
    | star => rfl
    | conc t =>
      have h2 : m = t := hb
      show (!memB t x) = true
      rw [← h2, h1]; rfl
    | starEx _ => rfl

/-- A common admitted location passes the meet test. -/
theorem meetB_of_common {a : PFact} {aex : Excl} {g : XFact} {l : Loc}
    (ha : coversX a aex l) (hg : coversX g.af.fact g.ex l) : meetB a aex g = true := by
  unfold meetB
  rw [AnyTaintExCov.overlapX_of_common (AnyTaintExCov.covLoc_of_coversX ha)
      (AnyTaintExCov.covLoc_of_coversX hg),
    markMeetB_of_common ha.2.2 hg.2.2]
  rfl

/-- THE COMPLETENESS OF THE BACKWARD RUN for the record (its soundness, read forward): every real
    forward flow of the method from an entry location `l0` to an admitted `jb` location `l1` at the
    exit has `l0` in `gb`. -/
def BComplete (P : Program) (r : BRec) : Prop :=
  ∀ l0 l1, Flow P r.method l0 (P.exit r.method) l1 → coversX r.jb r.jex l1 →
    coversX r.gb.af.fact r.gb.ex l0

/-- `viewF_sound`: under `BComplete`, an added fact `(a, aex)` covering an entry location `l0`
    that flows to an admitted `jb` location `l1` gets a view result, and the result covers `l1`. -/
theorem viewF_sound {P : Program} {r : BRec} {a : PFact} {aex : Excl} {l0 l1 : Loc}
    (hc : BComplete P r) (ha : coversX a aex l0)
    (hfl : Flow P r.method l0 (P.exit r.method) l1) (hj : coversX r.jb r.jex l1) :
    ∃ x, viewF r a aex = some x ∧ coversX x.af.fact x.ex l1 := by
  have hm : meetB a aex r.gb = true := meetB_of_common ha (hc l0 l1 hfl hj)
  refine ⟨viewOut r, by simp [viewF, hm], hj.1, ?_, hj.2.2⟩
  obtain ⟨τ, hp, _, _⟩ := hj.2.1
  exact ⟨τ, hp, trivial, admits_empty τ⟩

/-- `viewF_sound_pair`: with the concrete mark of the must-premise `jb`, the view result also
    relates the real pair `(l0, l1)` as an edge `a → x` (`denX`, uncorrelated). -/
theorem viewF_sound_pair {P : Program} {r : BRec} {a : PFact} {aex : Excl} {l0 l1 : Loc}
    {T : Mark} (hT : r.jb.mark = .conc T)
    (hc : BComplete P r) (ha : coversX a aex l0)
    (hfl : Flow P r.method l0 (P.exit r.method) l1) (hj : coversX r.jb r.jex l1) :
    ∃ x, viewF r a aex = some x ∧ x.af.demand = true ∧ denX a aex x.af.fact x.ex l0 l1 := by
  have hm : meetB a aex r.gb = true := meetB_of_common ha (hc l0 l1 hfl hj)
  refine ⟨viewOut r, by simp [viewF, hm], rfl, ?_⟩
  obtain ⟨hb0, ⟨σ, hp0, ht0, he0⟩, hm0⟩ := ha
  obtain ⟨hb1, ⟨τ, hp1, _, _⟩, hm1⟩ := hj
  have hl1 : l1.mark = T := by rw [hT] at hm1; exact hm1
  refine ⟨hb0, hb1, hm0, ?_, ?_, σ, τ, hp0, hp1, ht0, trivial, he0, admits_empty τ⟩
  · show l1.mark = r.jb.mark.out l0.mark
    rw [hT]; exact hl1
  · show r.jb.mark.passes l0.mark
    rw [hT]; trivial

#print axioms viewF_demand
#print axioms viewF_stays_demand
#print axioms viewF_sound
#print axioms viewF_sound_pair

/-! ## 4. The forward reading of the record and the NORMAL readings of a view result -/

/-- The END-EXACT meaning of a backward MUST record, read forward in `P`: every valid admitted
    location of `gb` flows forward to SOME valid admitted location of `jb` at the exit. -/
def EndExactB (P : Program) (ok : Loc → Prop) (r : BRec) : Prop :=
  ∀ l0, coversFX r.gb.af.fact r.gb.ex l0 → ok l0 →
    ∃ l1, coversX r.jb r.jex l1 ∧ Flow P r.method l0 (P.exit r.method) l1 ∧ ok l1

/-- The same fact in the NORMAL layer: what the view would publish if it were normal. -/
def asNormal (x : XFact) : XFact := ⟨⟨x.af.fact, false⟩, x.ex⟩

/-! ## 5. The guard: a pair-exact forward record keeps the results NORMAL -/

/-- A forward NON-MUST record `j → g` of the method `method` (a native normal singleton summary,
    §8.7 R1). -/
structure FRec where
  method : MethodId
  j : PFact
  g : AFact
deriving DecidableEq, Repr

/-- PAIR-EXACT (S14 for a non-must premise): every pair of the record is a real flow. -/
def FPairExact (P : Program) (f : FRec) : Prop :=
  ∀ l0 l1, den f.j f.g.fact l0 l1 → Flow P f.method l0 (P.exit f.method) l1

/-- The record is COMPLETE towards `(jb, jex)`: every real flow from a premise location to an
    admitted `jb` location at the exit is a pair of the record (the forward soundness of the run
    that produced it, restricted to `jb`). -/
def FComplete (P : Program) (f : FRec) (jb : PFact) (jex : Excl) : Prop :=
  ∀ l0 l1, f.j.covers l0 → Flow P f.method l0 (P.exit f.method) l1 → coversX jb jex l1 →
    den f.j f.g.fact l0 l1

/-- THE GUARD: the forward record is of the same method and its premise covers `gb`. -/
def GuardCovers (f : FRec) (r : BRec) : Prop :=
  f.method = r.method ∧ ∀ l, coversX r.gb.af.fact r.gb.ex l → f.j.covers l

/-- The geometry of a canonical FLOW record `b.p.*/{} (*) → b'.q.*/{} (*)` on a concrete-tail
    fact (`$` or `[any]`): never an approximation, and the result tail is `$` or `[any]`. -/
theorem geo_flow {ck k : Kind} {fp q tp p : List Acc} {ap : Bool}
    (hck : ck = .exact ∨ ck = .any)
    (hg : CoreAux.geo ck (.star Excl.empty) fp q tp (.star Excl.empty) = some (p, k, ap)) :
    ap = false ∧ (k = .exact ∨ k = .any) := by
  unfold CoreAux.geo at hg
  cases hr : relate fp q with
  | below r =>
    rw [hr] at hg
    rcases hck with rfl | rfl <;> cases r <;>
      simp [belowCase, admitsTailB, tailExcl, Excl.union, Excl.empty, Excl.admits,
        Excl.isEmptyB, memB] at hg <;> obtain ⟨_, rfl, rfl⟩ := hg <;> simp
  | above r =>
    rw [hr] at hg
    have hne := (CoreAux.relate_above_inv hr).2
    rcases hck with rfl | rfl <;> cases r
    all_goals first
      | exact absurd rfl hne
      | simp [aboveCase, admitsTailB, tailExcl, Excl.union, Excl.empty,
          Excl.isEmptyB, Kind.isAny] at hg
    all_goals obtain ⟨_, rfl, rfl⟩ := hg
    all_goals simp
  | apart =>
    rw [hr] at hg
    cases hg

/-- A normal FLOW record applied to a normal `$` or `[any]` fact gives only NORMAL results. -/
theorem flowRec_normal {c x : AFact} {b b' : Base} {p q : List Acc}
    (hcd : c.demand = false) (hck : c.fact.kind = .exact ∨ c.fact.kind = .any)
    (hx : x ∈ (applySummary c ⟨b, p, .star Excl.empty, .star⟩
      ⟨⟨b', q, .star Excl.empty, .star⟩, false⟩).facts) :
    x.demand = false := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨p', k, ap, m, hg, _, rfl⟩ := Invariant.applyEdge_shape hy
  obtain ⟨hap, hk⟩ := geo_flow hck hg
  subst hap
  rw [hcd]
  rcases hk with rfl | rfl <;> rfl

/-- `guard_keeps_normal`: let a canonical FLOW forward record `j = b.p.*/{} (*) → g = b'.q.*/{} (*)`
    (normal, non-must) of the method be PAIR-EXACT and COMPLETE towards `jb`, and let its premise
    cover `gb` (the guard). Apply it (`applySummary`, rule `ret`) to a normal added fact `c` with a
    concrete mark and a `$` or `[any]` tail, inside `gb`. Then
    (1) every result is NORMAL;
    (2) every real pair from `c` into `jb` is related by a (normal) result: for every caller pair
        `den ic c l00 l0` and every real flow `l0 → l1` with `l1` an admitted `jb` location;
    (3) every pair of a result is a caller pair of `c` followed by a REAL flow of the method
        (`Exact.applyEdge_exact` and `FPairExact`): the results are NORMAL with their meaning.
    So with this guard, dropping the forward demand edge `(gb, jb)` loses no normal result for the
    added facts inside `gb`. -/
theorem guard_keeps_normal {P : Program} {f : FRec} {r : BRec} {b b' : Base} {p q : List Acc}
    {c : AFact} {t : Mark}
    (hj : f.j = ⟨b, p, .star Excl.empty, .star⟩)
    (hg : f.g = ⟨⟨b', q, .star Excl.empty, .star⟩, false⟩)
    (hguard : GuardCovers f r) (hcomp : FComplete P f r.jb r.jex) (hexact : FPairExact P f)
    (hcd : c.demand = false) (hcm : c.fact.mark = .conc t)
    (hck : c.fact.kind = .exact ∨ c.fact.kind = .any)
    (hin : ∀ l, c.fact.covers l → coversX r.gb.af.fact r.gb.ex l) :
    (∀ x, x ∈ (applySummary c f.j f.g).facts → x.demand = false) ∧
    (∀ ic l00 l0 l1, den ic c.fact l00 l0 → Flow P f.method l0 (P.exit f.method) l1 →
        coversX r.jb r.jex l1 →
        ∃ x, x ∈ (applySummary c f.j f.g).facts ∧ x.demand = false ∧ den ic x.fact l00 l1) ∧
    (∀ ic x l00 l1, x ∈ (applySummary c f.j f.g).facts → den ic x.fact l00 l1 →
        ∃ l0, den ic c.fact l00 l0 ∧ Flow P f.method l0 (P.exit f.method) l1) := by
  have hnorm : ∀ x, x ∈ (applySummary c f.j f.g).facts → x.demand = false := by
    intro x hx
    rw [hj, hg] at hx
    exact flowRec_normal hcd hck hx
  refine ⟨hnorm, ?_, ?_⟩
  · intro ic l00 l0 l1 hd hfl hjb
    have hl0 : f.j.covers l0 := hguard.2 l0 (hin l0 (den_covers_final hd))
    rcases applySummary_sound hd (hcomp l0 l1 hl0 hfl hjb) with ⟨x, hx, hdx⟩ | ⟨hs, _⟩
    · exact ⟨x, hx, hnorm x hx, hdx⟩
    · exact absurd hcm (hs t)
  · intro ic x l00 l1 hx hdx
    obtain ⟨y, hy, rfl⟩ := Exact.applySummary_mem hx (hnorm x hx)
    have hyd : y.demand = false := by
      have h := hnorm _ hx
      rw [hg] at h
      simpa using h
    have hpm : Exact.premOKB f.j.mark c.fact.mark = true := by rw [hj]; rfl
    have hcm' : Exact.concOKB f.g.fact.mark c.fact.mark = true := by rw [hg]; rfl
    obtain ⟨l0, h0, h1⟩ := Exact.applyEdge_exact hpm hcm' hcd hy hyd hdx
    exact ⟨l0, h0, hexact l0 l1 h1⟩

#print axioms geo_flow
#print axioms flowRec_normal
#print axioms guard_keeps_normal

/-! ## 6. The counterexample program: the callee `ret.f.g = arg0`

  Bases: `arg0 = 1`, `ret = 2`. Accessors: `f = 1`, `g = 2`, `x = 3`. Mark `T = 7`.
  The callee is method `1`, entry node `0`, exit node `1`, one statement. The statement touches
  `arg0` and `ret` (a fresh `ret`: strong update); its micro edges are the write
  `arg0.* → ret.f.g.*` and the keep edge `arg0.* → arg0.*`. -/
namespace Cex

def write : MicroEdge := (⟨1, [], .star Excl.empty, .star⟩, ⟨2, [1, 2], .star Excl.empty, .star⟩)
def keep : MicroEdge := (⟨1, [], .star Excl.empty, .star⟩, ⟨1, [], .star Excl.empty, .star⟩)
def body : Stmt := ⟨[1, 2], [write, keep]⟩
def P : Program := ⟨fun _ => 0, fun _ => 1, [(1, 0, .stmt body, 1)]⟩

/-- The backward MUST record of the callee: `jb = ret.[any-taint] (T)` with no exclusion,
    `gb = arg0.[any] (T)` normal. -/
def bRec : BRec :=
  ⟨1, ⟨2, [], .any, .conc 7⟩, Excl.empty, ⟨⟨⟨1, [], .any, .conc 7⟩, false⟩, Excl.empty⟩⟩

theorem mem_body : ((1 : MethodId), (0 : Node), Instr.stmt body, (1 : Node)) ∈ P.edges :=
  List.Mem.head _

theorem wf : P.WF where
  stmtTouched := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h =>
        cases h with
        | head => rfl
        | tail _ h => cases h
    | tail _ h => cases h
  toStar := by
    intro M n c n' hE
    cases hE with
    | tail _ h => cases h
  fromStar := by
    intro M n c n' hE
    cases hE with
    | tail _ h => cases h
  filtPrefix := by
    intro M n b may n' hE
    cases hE with
    | tail _ h => cases h

/-- The flows of `P`: at the entry the start location, at the exit one statement step. -/
theorem flow_inv : ∀ {M l0 n l}, Flow P M l0 n l →
    (n = 0 ∧ l = l0) ∨ (n = 1 ∧ body.step l0 l) := by
  intro M l0 n l h
  induction h with
  | start M l0 => exact Or.inl ⟨rfl, rfl⟩
  | step _ hE hs ih =>
    cases hE with
    | head =>
      rcases ih with ⟨_, rfl⟩ | ⟨hn, _⟩
      · exact Or.inr ⟨rfl, hs⟩
      · exact absurd hn (by decide)
    | tail _ h => cases h
  | pass _ hE _ _ =>
    cases hE with
    | tail _ h => cases h
  | call _ hE _ _ _ _ _ _ _ =>
    cases hE with
    | tail _ h => cases h
  | clean _ hE _ _ =>
    cases hE with
    | tail _ h => cases h
  | filt _ hE _ _ =>
    cases hE with
    | tail _ h => cases h

/-- The location `ret` itself (with the mark `T`) at the exit. -/
def lRet : Loc := ⟨2, [], 7⟩

/-- Nothing flows to `ret` itself: the write reaches only `ret.f.g…`. -/
theorem no_flow_to_ret (l : Loc) : ¬ Flow P 1 l (P.exit 1) lRet := by
  intro h
  rcases flow_inv h with ⟨hn, _⟩ | ⟨_, hs⟩
  · exact absurd hn (by decide)
  · rcases hs with ⟨hm, he⟩ | ⟨e, he, hde⟩
    · rw [← he] at hm
      exact absurd hm (by decide)
    · cases he with
      | head =>
        obtain ⟨_, _, _, _, _, σ, τ, _, hp, _⟩ := hde
        have h' : ([] : List Acc) = 1 :: 2 :: τ := hp
        cases h'
      | tail _ h =>
        cases h with
        | head =>
          obtain ⟨_, hb, _⟩ := hde
          have h' : (2 : Nat) = 1 := hb
          cases h'
        | tail _ h => cases h

/-- The record is a well-formed B2 record whose END-EXACT meaning holds in `P`. -/
theorem endExact : EndExactB P (fun _ => True) bRec := by
  intro l0 hg _
  obtain ⟨hb, ⟨τ, hp, _, _⟩, t, ht, hm⟩ := hg
  have ht7 : t = 7 := (MarkA.conc.inj ht).symm
  refine ⟨⟨2, [1, 2] ++ l0.path, l0.mark⟩, ⟨rfl, ⟨[1, 2] ++ l0.path, rfl, trivial,
    admits_empty _⟩, ?_⟩, ?_, trivial⟩
  · show l0.mark = 7
    rw [hm, ht7]
  · refine Flow.step (Flow.start 1 l0) mem_body (Or.inr ⟨write, List.Mem.head _, ?_⟩)
    exact ⟨hb, rfl, trivial, rfl, trivial, l0.path, l0.path, rfl, rfl, admits_empty _,
      rfl, admits_empty _⟩

/-- The record satisfies the completeness hypothesis of the backward run in `P`. -/
theorem complete : BComplete P bRec := by
  intro l0 l1 hfl hj
  obtain ⟨hb1, _, hm1⟩ := hj
  rcases flow_inv hfl with ⟨hn, _⟩ | ⟨_, hs⟩
  · exact absurd hn (by decide)
  · rcases hs with ⟨hm, he⟩ | ⟨e, he, hde⟩
    · rw [he] at hb1
      have h' : memB l0.base [1, 2] = false := hm
      rw [hb1] at h'
      exact absurd h' (by decide)
    · cases he with
      | head =>
        obtain ⟨hb0, _, _, hmo, _, σ, _, hp0, _, ht0, _⟩ := hde
        refine ⟨hb0, ⟨σ, hp0, trivial, admits_empty σ⟩, ?_⟩
        have hm7 : l1.mark = 7 := hm1
        have hmo' : l1.mark = l0.mark := hmo
        show l0.mark = 7
        rw [← hmo', hm7]
      | tail _ h =>
        cases h with
        | head =>
          obtain ⟨_, hb, _⟩ := hde
          have h1 : l1.base = 1 := hb
          have h2 : l1.base = 2 := hb1
          rw [h1] at h2
          cases h2
        | tail _ h => cases h

/-- The caller's added fact `arg0.x $ (T)`, normal. -/
def added : AFact := ⟨⟨1, [3], .exact, .conc 7⟩, false⟩
/-- The view result `ret.[any] (T)`, DEMAND. -/
def viewRes : XFact := ⟨⟨⟨2, [], .any, .conc 7⟩, true⟩, Excl.empty⟩
/-- `arg0.x` with the mark `T` at the entry. -/
def lArg : Loc := ⟨1, [3], 7⟩

theorem view_eq : viewF bRec added.fact Excl.empty = some viewRes := by decide

/-- `viewF_not_exact`: THE FORWARD VIEW IS UNCORRELATED. The record is a well-formed B2 record
    of a well-formed program, END-EXACT in `P`, and complete (`BComplete`). Its forward view on the
    added fact `arg0.x $ (T)` gives `ret.[any] (T)`, which relates `arg0.x` to `ret`
    (`denX`), but `arg0.x` does not flow to `ret` (nothing does). So the view result cannot be
    NORMAL: published normal, it breaks the pair-exact motive (`EdgeOKX`, non-must premise) and
    even the end-exact motive (`EdgeOKX`, must reading). -/
theorem viewF_not_exact :
    bRec.wfB = true ∧ P.WF ∧ EndExactB P (fun _ => True) bRec ∧ BComplete P bRec ∧
    viewF bRec added.fact Excl.empty = some viewRes ∧ viewRes.af.demand = true ∧
    denX added.fact Excl.empty viewRes.af.fact viewRes.ex lArg lRet ∧
    ¬ Flow P 1 lArg (P.exit 1) lRet ∧
    ¬ EdgeOKX P (fun _ => True) (.edge 1 added.fact false Excl.empty (P.exit 1) (asNormal viewRes)) ∧
    ¬ EdgeOKX P (fun _ => True) (.edge 1 added.fact true Excl.empty (P.exit 1) (asNormal viewRes)) := by
  have hd : denX added.fact Excl.empty viewRes.af.fact viewRes.ex lArg lRet :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, trivial, rfl, rfl⟩
  refine ⟨by decide, wf, endExact, complete, view_eq, rfl, hd, no_flow_to_ret lArg, ?_, ?_⟩
  · intro h
    exact no_flow_to_ret lArg ((h rfl).2 lArg lRet hd trivial).1
  · intro h
    have hc : coversFX (asNormal viewRes).af.fact (asNormal viewRes).ex lRet :=
      ⟨rfl, ⟨[], rfl, trivial, rfl⟩, 7, rfl, rfl⟩
    obtain ⟨l0, _, hfl, _⟩ := (h rfl).2 lRet hc trivial
    exact no_flow_to_ret l0 hfl

#print axioms flow_inv
#print axioms no_flow_to_ret
#print axioms endExact
#print axioms complete
#print axioms viewF_not_exact

/-! ### The hand-off counterexample -/

/-- Every accessor is counted. -/
def cnt : Acc → Bool := fun _ => true
/-- The sink pattern `ret.[any] (T)` (a `ContainsMarkOnAnyField` sink). -/
def sink : PFact := ⟨2, [], .any, .conc 7⟩
/-- The run-1 premise of the callee: the most abstract fact `arg0.*` (`policy1`). -/
def run1Premise : PFact := ⟨1, [], .star Excl.empty, .star⟩
/-- The run-1 summary conclusion `ret.f.[any] (*)`, cut by the field limit 1: DEMAND. -/
def run1Concl : AFact := ⟨⟨2, [1], .any, .star⟩, true⟩
/-- The field-limit-1 result on the added fact: `ret.f.[any] (T)`, DEMAND. -/
def cut1 : AFact := ⟨⟨2, [1], .any, .conc 7⟩, true⟩
/-- The field-limit-3 result on the added fact: `ret.f.g.x $ (T)`, NORMAL. -/
def deep : AFact := ⟨⟨2, [1, 2, 3], .exact, .conc 7⟩, false⟩
/-- The keep edge result `arg0.x $ (T)`. -/
def kept : AFact := ⟨⟨1, [3], .exact, .conc 7⟩, false⟩
/-- The forward demand edge of the status quo: `D-c = gb`, `D-p = jb`, as patterns (`[any-taint]`
    becomes `[any]`, no exclusion, §9.2). -/
def demandEdge : DemandEdge := ⟨⟨1, [], .any, .conc 7⟩, some ⟨2, [], .any, .conc 7⟩⟩

/-- The backward run derives the record: the reversed write applied to the must-premise
    `ret.[any-taint] (T)` (normal start, `startX`) gives `arg0.[any] (T)` in the NORMAL layer. -/
theorem back_derives_gb :
    (applyEdge ⟨bRec.jb, false⟩ (revEdge write.1 write.2).1 (revEdge write.1 write.2).2).facts =
      [bRec.gb.af] := by decide

/-- `cex_drop_forward_demand`: DROPPING THE FORWARD DEMAND EDGE LOSES A CONFIRMATION.
    Callee `ret.f.g = arg0` (micro edge `arg0.* → ret.f.g.*`), caller added fact `arg0.x $ (T)`
    (normal), sink `ret.[any] (T)`.
    (a) Run 1, field limit 1, every accessor counted: the callee summary of the run-1 premise
        `arg0.*` is cut to `ret.f.[any] (*)` in the DEMAND layer; the caller's application gives
        `ret.f.[any] (T)`, DEMAND, and so does the direct transfer of the added fact; the sink
        triggers on it only in the DEMAND layer.
    (b) Status quo, the next forward run with field limit 3 and the forward demand edge
        `(D-c = gb, D-p = jb)`: the emission gives the premise `arg0.x $ (T)` itself, the transfer
        gives the NORMAL fact `ret.f.g.x $ (T)`, the restriction by `D-p` keeps it, the caller's
        application keeps it NORMAL, and `check` gives `.triggered` from a NORMAL edge
        (confirmable).
    (c) The backward MUST record's forward view gives `ret.[any] (T)` in the DEMAND layer; the
        sink triggers on it only in the DEMAND layer (and every later step stays DEMAND,
        `viewF_stays_demand`).
    CONCLUSION: if the hand-off drops the forward demand edge of the callee because a backward
    MUST record exists, the next forward run does not analyse the callee for this fact and keeps
    only (c); the confirmation that the status quo gets in (b) is lost. -/
theorem cex_drop_forward_demand :
    -- (a) run 1, field limit 1
    (transfer cnt 1 body (startFact run1Premise)).facts = [run1Concl, ⟨run1Premise, false⟩] ∧
    (applySummary added run1Premise run1Concl).facts = [cut1] ∧
    (transfer cnt 1 body added).facts = [cut1, kept] ∧
    cut1.demand = true ∧ check zeroFact cut1 sink = .triggered ∧
    -- (b) the status quo: forward re-analysis with field limit 3
    emitM demandEdge.din added.fact = some added.fact ∧
    startFact added.fact = added ∧
    (transfer cnt 3 body added).facts = [deep, kept] ∧
    restrictU added.fact deep demandEdge = some deep ∧
    (applySummary added added.fact deep).facts = [deep] ∧
    deep.demand = false ∧ check zeroFact deep sink = .triggered ∧
    -- (c) the backward MUST record read forward
    viewF bRec added.fact Excl.empty = some viewRes ∧
    viewRes.af.demand = true ∧ check zeroFact viewRes.af sink = .triggered := by
  decide

#print axioms back_derives_gb
#print axioms cex_drop_forward_demand

/-! ### The guard on the same callee -/

/-- The forward FLOW record of the callee once the field limit is at least 2: `arg0.* → ret.f.g.*`,
    normal, non-must. Run 1 (field limit 1) does not have it: its summary of `arg0.*` is DEMAND
    (`cex_drop_forward_demand` (a)), so R1 does not persist it and the guard fails after run 1. -/
def fRec : FRec := ⟨1, ⟨1, [], .star Excl.empty, .star⟩, ⟨⟨2, [1, 2], .star Excl.empty, .star⟩, false⟩⟩

theorem fRec_pairExact : FPairExact P fRec := by
  intro l0 l1 hd
  exact Flow.step (Flow.start 1 l0) mem_body (Or.inr ⟨write, List.Mem.head _, hd⟩)

theorem fRec_complete : FComplete P fRec bRec.jb bRec.jex := by
  intro l0 l1 _ hfl hj
  have hb1 : l1.base = 2 := hj.1
  rcases flow_inv hfl with ⟨hn, _⟩ | ⟨_, hs⟩
  · exact absurd hn (by decide)
  · rcases hs with ⟨hm, he⟩ | ⟨e, he, hde⟩
    · rw [he] at hb1
      have h' : memB l0.base [1, 2] = false := hm
      rw [hb1] at h'
      exact absurd h' (by decide)
    · cases he with
      | head => exact hde
      | tail _ h =>
        cases h with
        | head =>
          obtain ⟨_, hb, _⟩ := hde
          have h1 : l1.base = 1 := hb
          rw [h1] at hb1
          cases hb1
        | tail _ h => cases h

theorem fRec_guard : GuardCovers fRec bRec := by
  refine ⟨rfl, fun l hl => ?_⟩
  obtain ⟨hb, ⟨σ, hp, _, _⟩, _⟩ := hl
  exact ⟨hb, ⟨σ, hp, admits_empty σ⟩, trivial⟩

theorem added_inside : ∀ l, added.fact.covers l → coversX bRec.gb.af.fact bRec.gb.ex l := by
  intro l hl
  obtain ⟨hb, ⟨σ, hp, _⟩, hm⟩ := hl
  exact ⟨hb, ⟨[3] ++ σ, hp, trivial, admits_empty _⟩, hm⟩

/-- `guard_instance`: on the same callee, the field-limit-3 run gives the normal FLOW record
    `fRec`; it satisfies the guard for `bRec`, and its application to `arg0.x $ (T)` is the NORMAL
    `ret.f.g.x $ (T)` of `cex_drop_forward_demand` (b). With this record the hand-off could drop the
    forward demand edge; after run 1 only the DEMAND summary `arg0.* → ret.f.[any]` exists, so it
    must keep it. -/
theorem guard_instance :
    (transfer cnt 3 body (startFact run1Premise)).facts = [fRec.g, ⟨run1Premise, false⟩] ∧
    (applySummary added fRec.j fRec.g).facts = [deep] ∧ run1Concl.demand = true ∧
    (∀ x, x ∈ (applySummary added fRec.j fRec.g).facts → x.demand = false) ∧
    (∀ ic l00 l0 l1, den ic added.fact l00 l0 → Flow P 1 l0 (P.exit 1) l1 →
        coversX bRec.jb bRec.jex l1 →
        ∃ x, x ∈ (applySummary added fRec.j fRec.g).facts ∧ x.demand = false ∧
          den ic x.fact l00 l1) ∧
    (∀ ic x l00 l1, x ∈ (applySummary added fRec.j fRec.g).facts → den ic x.fact l00 l1 →
        ∃ l0, den ic added.fact l00 l0 ∧ Flow P 1 l0 (P.exit 1) l1) := by
  have h := guard_keeps_normal (P := P) (f := fRec) (r := bRec) (c := added) (t := 7)
    rfl rfl fRec_guard fRec_complete fRec_pairExact rfl rfl (Or.inl rfl) added_inside
  exact ⟨by decide, by decide, rfl, h⟩

#print axioms fRec_pairExact
#print axioms fRec_complete
#print axioms guard_instance

end Cex

end ApSpec.BackMustView
