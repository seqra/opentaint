/-
  ApSpec.AnyTaintExCases2 — THE ROUND-1 WORKED PROGRAMS `G`, `C`, `I` and `PassRule` RE-DERIVED IN
  THE REFINED CLOSURES `AnyTaintEx.D6X` (run 1) and `AnyTaintEx.DRXs` (the restricted forward run,
  the spec instance `emitX`, `satX`, `restrictX`) (decision F69, DESIGN §6, amendment A2).

  The round-1 file `AnyTaintCases.lean` proves the results of these programs for the round-1
  closures `AnyTaint.D6T` / `AnyTaint.DRT`. The spec states them for the refined closures (the
  exclusion of the `[any-taint]` conclusion). This file proves them there. The programs are the
  round-1 terms (imported, not restated): `AnyTaintCases.G.prog`, `AnyTaintCases.C.prog`,
  `AnyTaintCases.I.prog`, `AnyTaintCases.PassRule.prog`, with their sinks, taint edges, demands and
  facts. A refined fact is the round-1 fact with the empty exclusion (`plain`): none of these
  programs has an exclusion edge (`Carry.EdgeFree` holds for every edge), a cleaner or a type
  filter, so the refined runs create no annotation.

  Numbers (as round 1). Marks: `zeroMark = 0`, `T = 1`. Accessor `f = 1`. The field limit of every
  run is 3 (`cnt`). Bases of `G`/`I`: zero = 0, dto = 1, x = 2, p = 3, ret = 4; of `C`: zero = 0,
  dto = 1, o = 2; of `PassRule`: zero = 0, P = 1, Q = 2.

  THE THEOREMS (namespace, name: statement).
  * `G` (the getter: `root(){ dto = srcAny(); x = get(dto); sinkAny(x); }`, `get(p){ return p.f; }`):
    - `inv1`: the complete run 1 (`D6X`, `policy1`) of `G`; the only vulnerability is DEMAND;
    - `run1_flow_above`: the run-1 FLOW summary of `get` is `(p, [], *, {}, *) → (ret, [], [any], *)`,
      demand (case `above`), with the empty exclusion;
    - `run1_vuln`: `D6X` reports the vulnerability, in the DEMAND layer;
    - `run1_no_normal`, `run1_not_confirmed`: no normal report, NOT `Confirmed6X`;
    - `run1_forgets`, `run1_forget_eq`: `forget6` of the refined run 1 IS the round-1 run 1 `D6T`
      (every object, both directions);
    - `revDemX_bound`, `revDemX_get`, `HX_exact`, `handoffX_get`: the backward run (`Backward.DB`)
      restricted by the reversed summaries of the REFINED run 1 read without exclusions (`forget6`,
      as the refined pipeline reads it) hands off EXACTLY `AnyTaintCases.G.demGM`: the demand
      `dGet = (D-c = (p, [f], [any], T), D-p = (ret, [], [any], T))` of `get` and the zero demand;
    - `run3_must`: run 3 (`DRXs`) with a demand that has `dGet` derives the MUST premise
      `(p, [f], [any-taint], {}, T)` of `get`; `run3_must_supported`: it is supported (`SupX`);
    - `run3_sink_normal`: the sink edge `zero → (x, [], [any-taint], {}, T)` in `root` is NORMAL;
    - `run3_vuln_normal`, `run3_confirmed`: the normal report and `ConfirmedX` (every record set);
    - `run3_confirmed_handoff`: with the derived hand-off `HX`, for every record set: `ConfirmedX`;
    - `run1_carry`, `run1_not_confirmed_carry`: the same run 1 by the generic carry-over.
  * `C` (the sink in the callee: `root(){ dto = srcAny(); use(dto); }`, `use(o){ sinkAny(o.f); }`):
    - `run3_must`: run 3 (`DRXs`) with a demand that has `dUse = ((o, [f], [any], T), none)`
      derives the MUST premise `(o, [f], [any-taint], {}, T)` of `use`;
    - `run3_sink_normal`: its start fact is the NORMAL sink edge in `use`; `run3_vuln_normal`;
    - `run3_supported`: the must-premise is supported through `SupLinkX` (a must-premise inside
      the normal `[any-taint]` added fact `(o, [], [any-taint], {}, T)`, the same mark, `satX`);
    - `run3_confirmed`: `ConfirmedX` through the must-premise link; `run3_confirmed_handoff`: with
      the hand-off of the backward run (`AnyTaintCases.C.handoff_use`), for every backward demand,
      backward record set and forward record set.
  * `I` (the identity callee: `G` with `return p`):
    - `inv1`: the complete run 1 (`D6X`) of `I`; the only vulnerability is NORMAL;
    - `run1_flow`: the run-1 FLOW summary `(p, [], *, {}, *) → (ret, [], *, {}, *)`, normal;
    - `app_normal`: its refined application is a `keep` row of `annX` with the EMPTY exclusion and
      keeps the normal layer;
    - `run1_sink_normal`, `run1_vuln_normal`, `run1_confirmed` (`Confirmed6X`), `run1_no_demand`;
    - `run1_carry`, `run1_confirmed_carry`: the same by the generic carry-over.
  * `PassRule` (the micro edge `P.$ (T) → Q.[any] (T)` as a source and as a pass rule):
    - `source_vs_pass`: the refined statement transfer: as a source `(Q, [], [any-taint], {}, T)`
      NORMAL, as a pass rule `(Q, [], [any], T)` DEMAND;
    - `source_normal`, `source_confirmed` (`Confirmed6X`); `pass_demand`; `invPass`,
      `pass_not_confirmed` (the complete pass run: demand only, not `Confirmed6X`);
    - `run1_carry`, `confirmed_carry`: the same by the generic carry-over.
  * THE CARRY-OVER (namespace `Carry`; the conditions are stated at the section head):
    - the operation lemmas for a plain input and a free edge: `annX_free` (every row gives the
      EMPTY exclusion), `keep_layer` (a `keep` row agrees with the base layer),
      `applyEdgeX_free_facts` / `_reqs`, `bindX_free_facts`, `transferX_free_facts` / `_reqs`,
      `applySummaryX_free_facts`, `overlapX_empty`, `checkX_plain`, `limitFX_plain`, `emitTX_free`,
      `satX_empty`, `restrictX_plain`, `startX_plain`, `recLayerX_plain`, `supLinkX_iff`;
    - `d6x_iff_d6t`: under `ExclFreeProg P`, `NoClean P`, `SumFree P D6T`:
      `D6X o ↔ ∃ o', D6T o' ∧ lift6 o' = o` (the same fact and layer, the empty exclusion);
      `forget6_d6x`: `forget6 D6X = D6T`; `sup6x_iff`, `confirmed6x_iff`: `Confirmed6X ↔ ConfirmedT6`;
    - `drx_iff_drt`: under `ExclFreeProg P`, `NoClean P`, `SumFreeR P DRT`, `RecsLift recsX recs`,
      `RecsFree recs`: `DRXs o ↔ ∃ o', DRT o' ∧ liftR o' = o` (spec instances on both sides; the
      same fact, layer and must flag, the empty exclusions); `supX_iff`, `confirmedX_iff`:
      `ConfirmedX ↔ ConfirmedT`.

  FINDINGS (CEGAR). Every program behaves as the spec states in the refined closures; no program was
  changed and no statement was weakened.
  * The refined runs of these programs ARE the round-1 runs with the empty exclusion (G:
    `run1_forgets`; G, I, PassRule: `run1_carry`). The `keep` rows of `annX` DO fire (the
    must-premise summary of `get` in run 3 of `G`, `ret = p.f` at `r = []`; the application of the
    `id` summary in `I`), but with the empty exclusion: no annotation, and the base layer.
  * The restricted run of `G` uses the round-1 hand-off unchanged: the backward run reads the
    refined run 1 without its exclusions (`forget6`), and that is the round-1 run 1, so
    `AnyTaintCases.G.handoff_exact` applies (`HX_exact`). No added hypothesis (`HX_exact` has
    none; the confirmations hold for every record set).
  * The precise "no exclusion edge" condition (`EdgeFree`) must count a `$` PREMISE with a `*`
    target as an exclusion edge: it imposes `tailExcl $ = univ`, and in the case `above` on an
    `[any-taint]` fact the refined rule gives the NORMAL `[any-taint]/univ` (the location set of the
    target base alone) where the base demotes to `[any]` (`aboveCase`: `!(ck.isAny && …)`). So such
    an edge creates an annotation (`Carry.dollar_premise_annotates`); it is excluded by `EdgeFree`,
    not by "no `*/E` with `E ≠ {}`". (The refined result is correct and more precise than the base:
    its only location `y` is real.)
  * The restricted-run carry-over (`drx_iff_drt`) needs `SumFreeR` of the BASE restricted run (a
    condition on the demand, since the premises come from the emission); round 1 has no complete
    `DRT` run of `G` or `C`, so run 3 is derived directly here.

  All proofs are constructive (`propext`, `Quot.sound` only; see the `#print axioms` lines).
-/
import ApSpec.AnyTaintCases
import ApSpec.AnyTaintExDefs
import ApSpec.AnyTaintExCov

namespace ApSpec.AnyTaintExCases2
open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx ApSpec.AnyTaintCases

/-- A record set of the refined restricted run: premise, must flag, premise exclusion, annotated
    conclusion. -/
abbrev XRecs := MethodId → PFact × Bool × Excl × XFact → Prop


/-! ## THE CARRY-OVER: a run with no exclusion edge creates no annotation

  The refined operations differ from the base ones only where an EXCLUSION meets an `.any` fact
  (the `keep` rows of `annX`, the `partX` rows of the cleaners) or where an input already carries an
  exclusion (`annX`, `checkX`, `overlapX`, `restrictX`, `emitX`, `satX` read it). So a run in which
  NO EXCLUSION EDGE IS EVER APPLIED creates no annotation, and then every refined object is the base
  object with the empty exclusion. The conditions, precisely (sufficient):
  * `EdgeFree fr to` for every applied edge: a `*` target has the EMPTY exclusion, and then the
    premise tail imposes none (`tailExcl fr.kind = {}`: a `*/{}` or `[any]` premise; a `$` premise
    with a `*` target imposes `univ`, a `*/E` premise imposes `E`). An `.any` or `$` target is
    always free (a micro edge has no target annotation). On such an edge `annX` of a plain input
    gives the empty exclusion in every row (`annX_free`) and its `keep` row agrees with the base
    layer (`keep_layer`); a `$` premise with a `*` target is NOT free and does annotate
    (`dollar_premise_annotates`);
  * `ExclFreeProg P`: every statement micro edge and every call binding is `EdgeFree`;
  * `NoClean P`: no cleaner (a cleaner one accessor below an `[any-taint]` fact creates `E ∪ {f}`,
    `partX`);
  * `SumFree P R`: every summary of a callee in the base run `R` (a premise `j` and an exit
    conclusion `g` of it) is `EdgeFree j g.fact` (a `*/E` record would annotate, `annX` row
    `below []`).
  Under these, `d6x_iff_d6t`: the objects of `D6X` are exactly the lifts `lift6` (the same fact,
  the same layer, the empty exclusion) of the objects of `D6T`; `forget6_d6x`: `forget6 D6X = D6T`.
  The restricted run: `drx_iff_drt` (the same, for `DRXs` and the spec instance of `DRT`, with the
  records related by `RecsLift` and free by `RecsFree`). -/

namespace Carry

/-- An edge `fr → to` WITHOUT EXCLUSION: a `*` target has the empty exclusion, and then the
    premise tail imposes none. -/
def EdgeFree (fr to : PFact) : Prop :=
  ∀ et, to.kind = .star et → et = Excl.empty ∧ tailExcl fr.kind = Excl.empty

/-- The program has no exclusion edge: every statement micro edge and every call binding is
    `EdgeFree`. -/
def ExclFreeProg (P : Program) : Prop :=
  (∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges → ∀ e, e ∈ s.edges → EdgeFree e.1 e.2) ∧
  (∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    (∀ e, e ∈ c.toCallee → EdgeFree e.1 e.2) ∧ (∀ e, e ∈ c.fromCallee → EdgeFree e.1 e.2))

/-- The program has no cleaner. -/
def NoClean (P : Program) : Prop := ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → False

/-- The base run `R` has no summary with an exclusion: every summary of a callee (a premise `j`
    and an exit conclusion `g` of it) is `EdgeFree`. -/
def SumFree (P : Program) (R : Obj → Prop) : Prop :=
  ∀ M n c n' j g, (M, n, Instr.call c, n') ∈ P.edges → R (.init c.callee j) →
    R (.edge c.callee j (P.exit c.callee) g) → EdgeFree j g.fact

/-! ### Boolean forms (for concrete programs) -/

def edgeFreeB (fr to : PFact) : Bool :=
  match to.kind with
  | .star et => et.isEmptyB && (tailExcl fr.kind).isEmptyB
  | _        => true

theorem isEmptyB_eq {e : Excl} (h : e.isEmptyB = true) : e = Excl.empty := by
  cases e with
  | univ => cases h
  | set xs =>
    cases xs with
    | nil => rfl
    | cons _ _ => cases h

theorem edgeFree_of_B {fr to : PFact} (h : edgeFreeB fr to = true) : EdgeFree fr to := by
  intro et het
  unfold edgeFreeB at h
  rw [het] at h
  exact ⟨isEmptyB_eq (RExact.bool_and_left h), isEmptyB_eq (RExact.bool_and_right h)⟩

def instrFreeB : Instr → Bool
  | .stmt s    => s.edges.all (fun e => edgeFreeB e.1 e.2)
  | .call c    => c.toCallee.all (fun e => edgeFreeB e.1 e.2) &&
                  c.fromCallee.all (fun e => edgeFreeB e.1 e.2)
  | .clean _   => false
  | .filt _ _  => true

/-- The Boolean test of `ExclFreeProg` and `NoClean`. -/
def progFreeB (P : Program) : Bool := P.edges.all (fun x => instrFreeB x.2.2.1)

theorem instrFree_of {P : Program} (h : progFreeB P = true) {M n i n'}
    (hE : (M, n, i, n') ∈ P.edges) : instrFreeB i = true :=
  List.all_eq_true.mp h _ hE

/-- The Boolean test gives `ExclFreeProg` and `NoClean`. -/
theorem progFree_of_B {P : Program} (h : progFreeB P = true) : ExclFreeProg P ∧ NoClean P := by
  refine ⟨⟨fun M n s n' hE e he => ?_, fun M n c n' hE => ⟨fun e he => ?_, fun e he => ?_⟩⟩,
    fun M n cl n' hE => ?_⟩
  · exact edgeFree_of_B (List.all_eq_true.mp (instrFree_of h hE) e he)
  · exact edgeFree_of_B (List.all_eq_true.mp (RExact.bool_and_left (instrFree_of h hE)) e he)
  · exact edgeFree_of_B (List.all_eq_true.mp (RExact.bool_and_right (instrFree_of h hE)) e he)
  · exact Bool.noConfusion (instrFree_of h hE)

#print axioms progFree_of_B

/-! ### The operations on plain inputs and free edges -/

theorem map_congr_mem {α β : Type} {f g : α → β} :
    ∀ (l : List α), (∀ x, x ∈ l → f x = g x) → l.map f = l.map g
  | [], _ => rfl
  | x :: xs, h => by
    show f x :: xs.map f = g x :: xs.map g
    rw [h x (List.mem_cons_self ..), map_congr_mem xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- THE ANNOTATION RULES ON A PLAIN INPUT AND A FREE EDGE: the exclusion of every row is EMPTY,
    and a `keep` row needs an `.any` input and a `*` target. -/
theorem annX_free (c : AFact) {fr to : PFact} (hf : EdgeFree fr to) :
    ∃ keep, annX (plain c) fr Excl.empty to Excl.empty = some (keep, Excl.empty) ∧
      (keep = true → c.fact.kind = .any ∧ ∃ et, to.kind = .star et) := by
  unfold annX
  cases hr : relate fr.path (plain c).af.fact.path with
  | below r =>
    cases r with
    | nil =>
      cases hk : to.kind with
      | star et =>
        obtain ⟨h1, h2⟩ := hf et hk
        subst h1
        refine ⟨keepB (plain c), ?_, fun hkp => ⟨keepB_any hkp, _, rfl⟩⟩
        show some (keepB (plain c),
          (((Excl.empty.union (tailExcl fr.kind)).union Excl.empty).union Excl.empty)) = _
        rw [h2]; rfl
      | any => exact ⟨false, rfl, fun h => Bool.noConfusion h⟩
      | exact => exact ⟨false, rfl, fun h => Bool.noConfusion h⟩
    | cons x r =>
      show ∃ keep, (if Excl.empty.admits (x :: r) = true then _ else none) = _ ∧ _
      rw [admits_empty, if_pos rfl]
      cases hk : to.kind with
      | star et => exact ⟨false, rfl, fun h => Bool.noConfusion h⟩
      | any => exact ⟨false, rfl, fun h => Bool.noConfusion h⟩
      | exact => exact ⟨false, rfl, fun h => Bool.noConfusion h⟩
  | above r =>
    show ∃ keep, (if Excl.empty.admits r = true then _ else none) = _ ∧ _
    rw [admits_empty, if_pos rfl]
    cases hk : to.kind with
    | star et =>
      obtain ⟨h1, h2⟩ := hf et hk
      subst h1
      refine ⟨keepB (plain c), ?_, fun hkp => ⟨keepB_any hkp, _, rfl⟩⟩
      show some (keepB (plain c), (((tailExcl fr.kind).union Excl.empty).union Excl.empty)) = _
      rw [h2]; rfl
    | any => exact ⟨false, rfl, fun h => Bool.noConfusion h⟩
    | exact => exact ⟨false, rfl, fun h => Bool.noConfusion h⟩
  | apart => exact ⟨false, rfl, fun h => Bool.noConfusion h⟩

#print axioms annX_free

/-- The base `above` geometry of an `.any` input against a `*/{}` target, with a premise tail that
    imposes no exclusion: the result is `.any` and the approximation bit is off. -/
theorem above_keep {fk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (hfk : tailExcl fk = Excl.empty)
    (h : aboveCase .any fk r tp (.star Excl.empty) = some (p, k, ap)) : ap = false ∧ k = .any := by
  unfold aboveCase at h
  rw [hfk] at h
  cases h
  exact ⟨rfl, rfl⟩

/-- The base `below` geometry of an `.any` input against a `*/{}` target, with a premise tail that
    imposes no exclusion: the result is `.any` and the approximation bit is off. -/
theorem below_keep {fk : Kind} {r tp p : List Acc} {k : Kind} {ap : Bool}
    (hfk : tailExcl fk = Excl.empty)
    (h : belowCase .any fk r tp (.star Excl.empty) = some (p, k, ap)) : ap = false ∧ k = .any := by
  unfold belowCase at h
  split at h
  · cases r with
    | cons x r' =>
      cases h
      exact ⟨rfl, rfl⟩
    | nil =>
      rw [hfk] at h
      cases h
      exact ⟨rfl, rfl⟩
  · cases h

/-- The base geometry of an `.any` input against a `*/{}` target, with a premise tail that imposes
    no exclusion: the result is `.any` and the approximation bit is off. -/
theorem geo_keep {fk : Kind} {P q tp p : List Acc} {k : Kind} {ap : Bool}
    (hfk : tailExcl fk = Excl.empty)
    (h : CoreAux.geo .any fk P q tp (.star Excl.empty) = some (p, k, ap)) :
    ap = false ∧ k = .any := by
  unfold CoreAux.geo at h
  cases hrel : relate P q with
  | apart => rw [hrel] at h; cases h
  | above r => rw [hrel] at h; exact above_keep hfk h
  | below r => rw [hrel] at h; exact below_keep hfk h

#print axioms geo_keep

/-- THE `keep` ROWS AGREE WITH THE BASE LAYER on a free edge: an `.any` input with a `*` target
    gives base results in the layer of the input (the base demotes only when an exclusion meets the
    `.any` fact). -/
theorem keep_layer {c y : AFact} {fr to : PFact} {et : Excl} (hk : c.fact.kind = .any)
    (hf : EdgeFree fr to) (ht : to.kind = .star et) (hy : y ∈ (applyEdge c fr to).facts) :
    y.demand = c.demand := by
  obtain ⟨h1, h2⟩ := hf et ht
  obtain ⟨p, k, ap, m, hg, _, hr⟩ := Invariant.applyEdge_shape hy
  rw [hk, ht, h1] at hg
  obtain ⟨rfl, rfl⟩ := geo_keep h2 hg
  rw [hr, Invariant.norm_id_of_nonstar rfl]
  exact Bool.or_false _

#print axioms keep_layer

/-- THE CORE OPERATION ON A PLAIN INPUT AND A FREE EDGE IS THE BASE OPERATION (facts). -/
theorem applyEdgeX_free_facts (c : AFact) {fr to : PFact} (hf : EdgeFree fr to) :
    (applyEdgeX (plain c) fr Excl.empty to Excl.empty).facts = (applyEdge c fr to).facts.map plain := by
  obtain ⟨keep, ha, hk⟩ := annX_free c hf
  unfold applyEdgeX
  rw [ha]
  apply map_congr_mem
  intro y hy
  show normX ⟨layerX keep c.demand y, Excl.empty⟩ = ⟨y, Excl.empty⟩
  rw [normX_empty]
  cases keep with
  | false => rfl
  | true =>
    obtain ⟨hk1, et, het⟩ := hk rfl
    have hl := keep_layer hk1 hf het hy
    unfold layerX
    cases hcd : c.demand with
    | true => rfl
    | false =>
      rw [hcd] at hl
      obtain ⟨yf, yd⟩ := y
      cases hl
      rfl

#print axioms applyEdgeX_free_facts

/-- The requests of the core operation on a plain input and a free edge are the base requests. -/
theorem applyEdgeX_free_reqs (c : AFact) {fr to : PFact} (hf : EdgeFree fr to) :
    (applyEdgeX (plain c) fr Excl.empty to Excl.empty).reqs = (applyEdge c fr to).reqs := by
  obtain ⟨keep, ha, _⟩ := annX_free c hf
  unfold applyEdgeX
  rw [ha]
  rfl

theorem bindX_free_facts (c : AFact) {e : MicroEdge} (hf : EdgeFree e.1 e.2) :
    (bindX (plain c) e).facts = (applyEdge c e.1 e.2).facts.map plain :=
  applyEdgeX_free_facts c hf

theorem bindX_free_reqs (c : AFact) {e : MicroEdge} (hf : EdgeFree e.1 e.2) :
    (bindX (plain c) e).reqs = (applyEdge c e.1 e.2).reqs :=
  applyEdgeX_free_reqs c hf

theorem w6tX_plain (taint : TaintEdges) (e : MicroEdge) (y : AFact) :
    w6tX taint e (plain y) = plain (w6t taint e y) := by
  unfold w6tX w6t plain
  cases e.2.kind.isAny && !taint e <;> rfl

theorem limitFX_plain (counted : Acc → Bool) (L : Nat) (y : AFact) :
    limitFX counted L (plain y) = plain (limitF counted L y) := by
  show (match cutPath counted L y.fact.path with
    | none => plain y
    | some _ => (⟨limitF counted L y, Excl.empty⟩ : XFact)) = plain (limitF counted L y)
  unfold limitF
  cases cutPath counted L y.fact.path <;> rfl

theorem applyEdgeXT_free_facts (taint : TaintEdges) (c : AFact) {e : MicroEdge}
    (hf : EdgeFree e.1 e.2) :
    (applyEdgeXT taint (plain c) e).facts = (applyEdgeT taint c e).facts.map plain := by
  show (bindX (plain c) e).facts.map (w6tX taint e) =
    ((applyEdge c e.1 e.2).facts.map (w6t taint e)).map plain
  rw [bindX_free_facts c hf, List.map_map, List.map_map]
  exact map_congr_mem _ (fun y _ => w6tX_plain taint e y)

theorem applyAllXT_free_facts (taint : TaintEdges) (c : AFact) :
    ∀ {es : List MicroEdge}, (∀ e, e ∈ es → EdgeFree e.1 e.2) →
    (applyAllXT taint (plain c) es).facts = (applyAllT taint c es).facts.map plain
  | [], _ => rfl
  | e :: es, h => by
    show (applyEdgeXT taint (plain c) e).facts ++ (applyAllXT taint (plain c) es).facts =
      ((applyEdgeT taint c e).facts ++ (applyAllT taint c es).facts).map plain
    rw [List.map_append, applyEdgeXT_free_facts taint c (h e (List.mem_cons_self ..)),
      applyAllXT_free_facts taint c (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]

theorem applyAllXT_free_reqs (taint : TaintEdges) (c : AFact) :
    ∀ {es : List MicroEdge}, (∀ e, e ∈ es → EdgeFree e.1 e.2) →
    (applyAllXT taint (plain c) es).reqs = (applyAllT taint c es).reqs
  | [], _ => rfl
  | e :: es, h => by
    show (bindX (plain c) e).reqs ++ (applyAllXT taint (plain c) es).reqs =
      (applyEdge c e.1 e.2).reqs ++ (applyAllT taint c es).reqs
    rw [bindX_free_reqs c (h e (List.mem_cons_self ..)),
      applyAllXT_free_reqs taint c (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]

/-- THE STATEMENT TRANSFER ON A PLAIN INPUT AND FREE MICRO EDGES IS THE BASE TRANSFER (facts). -/
theorem transferX_free_facts (taint : TaintEdges) (counted : Acc → Bool) (L : Nat) {s : Stmt}
    (hs : ∀ e, e ∈ s.edges → EdgeFree e.1 e.2) (c : AFact) :
    (transferX taint counted L s (plain c)).facts =
      (transferT taint counted L s c).facts.map plain := by
  unfold transferX transferT
  show (if memB c.fact.base s.touched = true then
      ResX.mk ((applyAllXT taint (plain c) s.edges).facts.map (limitFX counted L))
        (applyAllXT taint (plain c) s.edges).reqs
    else ResX.mk [plain c] []).facts =
    (if memB c.fact.base s.touched = true then
      Res.mk ((applyAllT taint c s.edges).facts.map (limitF counted L))
        (applyAllT taint c s.edges).reqs
    else Res.mk [c] []).facts.map plain
  cases memB c.fact.base s.touched with
  | false => rfl
  | true =>
    show (applyAllXT taint (plain c) s.edges).facts.map (limitFX counted L) =
      ((applyAllT taint c s.edges).facts.map (limitF counted L)).map plain
    rw [applyAllXT_free_facts taint c hs, List.map_map, List.map_map]
    exact map_congr_mem _ (fun y _ => limitFX_plain counted L y)

#print axioms transferX_free_facts

theorem transferX_free_reqs (taint : TaintEdges) (counted : Acc → Bool) (L : Nat) {s : Stmt}
    (hs : ∀ e, e ∈ s.edges → EdgeFree e.1 e.2) (c : AFact) :
    (transferX taint counted L s (plain c)).reqs = (transferT taint counted L s c).reqs := by
  unfold transferX transferT
  show (if memB c.fact.base s.touched = true then
      ResX.mk ((applyAllXT taint (plain c) s.edges).facts.map (limitFX counted L))
        (applyAllXT taint (plain c) s.edges).reqs
    else ResX.mk [plain c] []).reqs =
    (if memB c.fact.base s.touched = true then
      Res.mk ((applyAllT taint c s.edges).facts.map (limitF counted L))
        (applyAllT taint c s.edges).reqs
    else Res.mk [c] []).reqs
  cases memB c.fact.base s.touched with
  | false => rfl
  | true => exact applyAllXT_free_reqs taint c hs

/-- THE SUMMARY APPLICATION ON A PLAIN INPUT AND A FREE SUMMARY IS THE BASE APPLICATION (facts). -/
theorem applySummaryX_free_facts (a g : AFact) {j : PFact} (hf : EdgeFree j g.fact) :
    (applySummaryX (plain a) j Excl.empty (plain g)).facts =
      (applySummary a j g).facts.map plain := by
  show (applyEdgeX (plain a) j Excl.empty g.fact Excl.empty).facts.map
      (fun x => normX ⟨AFact.norm ⟨x.af.fact, x.af.demand || g.demand⟩, x.ex⟩) =
    ((applyEdge a j g.fact).facts.map (fun x => AFact.norm ⟨x.fact, x.demand || g.demand⟩)).map plain
  rw [applyEdgeX_free_facts a hf, List.map_map, List.map_map]
  exact map_congr_mem _ (fun y _ => normX_empty _)

#print axioms applySummaryX_free_facts

theorem applySummaryX_free_reqs (a g : AFact) {j : PFact} (hf : EdgeFree j g.fact) :
    (applySummaryX (plain a) j Excl.empty (plain g)).reqs = (applySummary a j g).reqs :=
  applyEdgeX_free_reqs a hf

/-- With no exclusion, the overlap is the base overlap. -/
theorem overlapX_empty (a b : PFact) : overlapX a Excl.empty b Excl.empty = overlapB a b := by
  unfold overlapX overlapB
  cases relate a.path b.path with
  | below r => dsimp only; rw [admits_empty, Bool.and_true]
  | above r => dsimp only; rw [admits_empty, Bool.and_true]
  | apart => cases Nat.beq a.base b.base <;> rfl

#print axioms overlapX_empty

theorem check_none_of {i : PFact} {f : AFact} {s : PFact} (h : overlapB f.fact s = false) :
    check i f s = .none := by
  unfold check
  rw [h]
  cases s.mark <;> rfl

/-- With no exclusion, the sink check is the base check. -/
theorem checkX_plain (i : PFact) (f : AFact) (s : PFact) : checkX i (plain f) s = check i f s := by
  unfold checkX
  show (if overlapX f.fact Excl.empty s Excl.empty = true then check i f s else .none) = check i f s
  rw [overlapX_empty]
  cases ho : overlapB f.fact s with
  | true => rfl
  | false => exact (check_none_of ho).symm

#print axioms checkX_plain

/-! ### Why `EdgeFree` counts a `$` premise with a `*` target

  The vector: the normal `[any-taint]` fact `(x, [], [any-taint], {}, T)` and the micro edge
  `x.f.$ → y.*` (a `$` premise, a `*` target; no `*/E` anywhere). Case `above [f]`: the refined rule
  gives the NORMAL `(y, [], [any-taint], univ, T)` (the location `y` alone, which is real: `x.f`
  carries `T`), the base gives `(y, [], [any], T)` in the DEMAND layer. So the edge creates an
  annotation; `EdgeFree` rejects it (`tailExcl $ = univ`). -/

theorem dollar_premise_annotates :
    bindX ⟨⟨⟨1, [], .any, .conc 1⟩, false⟩, Excl.empty⟩
        (⟨1, [1], .exact, .star⟩, ⟨2, [], .star Excl.empty, .star⟩) =
      ⟨[⟨⟨⟨2, [], .any, .conc 1⟩, false⟩, .univ⟩], []⟩ ∧
    (applyEdge ⟨⟨1, [], .any, .conc 1⟩, false⟩ ⟨1, [1], .exact, .star⟩
        ⟨2, [], .star Excl.empty, .star⟩).facts = [⟨⟨2, [], .any, .conc 1⟩, true⟩] ∧
    edgeFreeB ⟨1, [1], .exact, .star⟩ ⟨2, [], .star Excl.empty, .star⟩ = false := by decide

#print axioms dollar_premise_annotates

/-! ### The carry-over of run 1 -/

/-- The refined object of a base object: the same fact and layer, the empty exclusion. -/
def lift6 : Obj → XObj6
  | .init M i     => .init M i
  | .edge M i n f => .edge M i n (plain f)
  | .added M a    => .added M a
  | .req M i t    => .req M i t
  | .vuln M n s d => .vuln M n s d

theorem forget_lift6 (o : Obj) : (lift6 o).forget = o := by cases o <;> rfl

/-- The base object of a refined object, as a predicate: an edge is plain and its fact is a base
    edge; every other object is a base object. -/
def Base6 (R : Obj → Prop) : XObj6 → Prop
  | .init M i      => R (.init M i)
  | .edge M i n x  => x = plain x.af ∧ R (.edge M i n x.af)
  | .added M a     => R (.added M a)
  | .req M i t     => R (.req M i t)
  | .vuln M n s d  => R (.vuln M n s d)

section Sim6
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)}
  {roots : List MethodId}

/-- Every base object of run 1, lifted, is an object of the refined run 1. -/
theorem d6t_lift (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFree P (D6T P taint counted L α sinks roots)) {o : Obj}
    (h : D6T P taint counted L α sinks roots o) : D6X P taint counted L α sinks roots (lift6 o) := by
  induction h with
  | root hM => exact D6X.root hM
  | start _ ih => exact D6X.start ih
  | @step M i n f n' s f' _ hE hf ih =>
    have hf' : plain f' ∈ (transferX taint counted L s (plain f)).facts := by
      rw [transferX_free_facts taint counted L (hP.1 _ _ _ _ hE) f]
      exact List.mem_map_of_mem hf
    exact D6X.step ih hE hf'
  | @reqStmt M i n f n' s t _ hE ht ih =>
    have ht' : t ∈ (transferX taint counted L s (plain f)).reqs := by
      rw [transferX_free_reqs taint counted L (hP.1 _ _ _ _ hE) f]; exact ht
    exact D6X.reqStmt ih hE ht'
  | pass _ hE hm ih => exact D6X.pass ih hE hm
  | @added M i n f n' c e a _ hE he ha ih =>
    have ha' : plain a ∈ (bindX (plain f) e).facts := by
      rw [bindX_free_facts f ((hP.2 _ _ _ _ hE).1 e he)]; exact List.mem_map_of_mem ha
    exact D6X.added ih hE he ha'
  | initA _ ih => exact D6X.initA ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha hj hap hg hr he2 hr' ihf ihj ihg =>
    have ha' : plain a ∈ (bindX (plain f) e1).facts := by
      rw [bindX_free_facts f ((hP.2 _ _ _ _ hE).1 e1 he1)]; exact List.mem_map_of_mem ha
    have hr1 : plain r ∈ (applySummaryX (plain a) j Excl.empty (plain g)).facts := by
      rw [applySummaryX_free_facts a g (hs _ _ _ _ _ _ hE hj hg)]; exact List.mem_map_of_mem hr
    have hr2 : plain r' ∈ (bindX (plain r) e2).facts := by
      rw [bindX_free_facts r ((hP.2 _ _ _ _ hE).2 e2 he2)]; exact List.mem_map_of_mem hr'
    have h := D6X.ret ihf hE he1 ha' ihj hap ihg hr1 he2 hr2
    rw [limitFX_plain] at h
    exact h
  | reqSink _ hs' hc ih => exact D6X.reqSink ih hs' (by rw [checkX_plain]; exact hc)
  | answer _ _ ha ho ih1 ih2 => exact D6X.answer ih1 ih2 ha ho
  | @reqUp m j t M ic n f n' c e a _ _ hE hc he ha hcl' ho ih1 ih2 =>
    have ha' : plain a ∈ (bindX (plain f) e).facts := by
      rw [bindX_free_facts f ((hP.2 _ _ _ _ hE).1 e he)]; exact List.mem_map_of_mem ha
    exact D6X.reqUp ih1 ih2 hE hc he ha' hcl' ((overlapX_empty a.fact j).trans ho)
  | vuln _ hs' hc ih => exact D6X.vuln ih hs' (by rw [checkX_plain]; exact hc)
  | clean _ hE _ _ => exact (hcl _ _ _ _ hE).elim
  | reqClean _ hE _ _ => exact (hcl _ _ _ _ hE).elim
  | filt _ hE hf ih => exact D6X.filt ih hE hf

#print axioms d6t_lift

/-- Every object of the refined run 1 is the lift of a base object (`Base6`). -/
theorem d6x_base (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFree P (D6T P taint counted L α sinks roots)) {o : XObj6}
    (h : D6X P taint counted L α sinks roots o) : Base6 (D6T P taint counted L α sinks roots) o := by
  induction h with
  | root hM => exact D6T.root hM
  | start _ ih => exact ⟨rfl, D6T.start ih⟩
  | @step M i n f n' s f' _ hE hf ih =>
    obtain ⟨he, hD⟩ := ih
    rw [he, transferX_free_facts taint counted L (hP.1 _ _ _ _ hE) f.af] at hf
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hf
    exact ⟨rfl, D6T.step hD hE hy⟩
  | @reqStmt M i n f n' s t _ hE ht ih =>
    obtain ⟨he, hD⟩ := ih
    rw [he, transferX_free_reqs taint counted L (hP.1 _ _ _ _ hE) f.af] at ht
    exact D6T.reqStmt hD hE ht
  | pass _ hE hm ih => exact ⟨ih.1, D6T.pass ih.2 hE hm⟩
  | @added M i n f n' c e a _ hE he ha ih =>
    obtain ⟨hfe, hD⟩ := ih
    rw [hfe, bindX_free_facts f.af ((hP.2 _ _ _ _ hE).1 e he)] at ha
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
    exact D6T.added hD hE he ha0
  | initA _ ih => exact D6T.initA ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    obtain ⟨hfe, hfD⟩ := ihf
    obtain ⟨hge, hgD⟩ := ihg
    rw [hfe, bindX_free_facts f.af ((hP.2 _ _ _ _ hE).1 e1 he1)] at ha
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
    rw [hge, applySummaryX_free_facts a0 g.af (hs _ _ _ _ _ _ hE ihj hgD)] at hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    rw [bindX_free_facts r0 ((hP.2 _ _ _ _ hE).2 e2 he2)] at hr'
    obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hr'
    rw [limitFX_plain]
    exact ⟨rfl, D6T.ret hfD hE he1 ha0 ihj hap hgD hr0 he2 hr1⟩
  | @reqSink M i n f s t _ hs' hc ih =>
    obtain ⟨hfe, hD⟩ := ih
    rw [hfe, checkX_plain] at hc
    exact D6T.reqSink hD hs' hc
  | answer _ _ ha ho ih1 ih2 => exact D6T.answer ih1 ih2 ha ho
  | @reqUp m j t M ic n f n' c e a _ _ hE hc he ha hcl' ho ih1 ih2 =>
    obtain ⟨hfe, hD⟩ := ih2
    rw [hfe, bindX_free_facts f.af ((hP.2 _ _ _ _ hE).1 e he)] at ha
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
    exact D6T.reqUp ih1 hD hE hc he ha0 hcl' ((overlapX_empty a0.fact j).symm.trans ho)
  | @vuln M i n f s _ hs' hc ih =>
    obtain ⟨hfe, hD⟩ := ih
    rw [hfe, checkX_plain] at hc
    exact D6T.vuln hD hs' hc
  | clean _ hE _ _ => exact (hcl _ _ _ _ hE).elim
  | reqClean _ hE _ _ => exact (hcl _ _ _ _ hE).elim
  | filt _ hE hf ih => exact ⟨ih.1, D6T.filt ih.2 hE hf⟩

#print axioms d6x_base

/-- THE CARRY-OVER OF RUN 1 (the generic lemma). For a program with no exclusion edge
    (`ExclFreeProg`), no cleaner (`NoClean`), and a base run whose callee summaries are free
    (`SumFree`): the objects of `D6X` are EXACTLY the lifts of the objects of `D6T` (the same fact,
    the same layer, the empty exclusion; `lift6`). So every result of a round-1 run 1 is a result of
    the refined run 1 and conversely. -/
theorem d6x_iff_d6t (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFree P (D6T P taint counted L α sinks roots)) (o : XObj6) :
    D6X P taint counted L α sinks roots o ↔ ∃ o', D6T P taint counted L α sinks roots o' ∧ lift6 o' = o := by
  constructor
  · intro h
    have hb := d6x_base hP hcl hs h
    cases o with
    | init M i => exact ⟨.init M i, hb, rfl⟩
    | edge M i n x =>
      refine ⟨.edge M i n x.af, hb.2, ?_⟩
      show XObj6.edge M i n (plain x.af) = .edge M i n x
      rw [← hb.1]
    | added M a => exact ⟨.added M a, hb, rfl⟩
    | req M i t => exact ⟨.req M i t, hb, rfl⟩
    | vuln M n s d => exact ⟨.vuln M n s d, hb, rfl⟩
  · rintro ⟨o', h, rfl⟩
    exact d6t_lift hP hcl hs h

#print axioms d6x_iff_d6t

/-- The carry-over as the reading of the refined pipeline: run 1 read without exclusions
    (`forget6`) IS the base run 1. -/
theorem forget6_d6x (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFree P (D6T P taint counted L α sinks roots)) :
    AnyTaintExCov.forget6 (D6X P taint counted L α sinks roots) = D6T P taint counted L α sinks roots := by
  funext o
  apply propext
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨o', ho', rfl⟩ := (d6x_iff_d6t hP hcl hs x).mp hx
    rw [forget_lift6]
    exact ho'
  · intro h
    exact ⟨lift6 o, d6t_lift hP hcl hs h, forget_lift6 o⟩

#print axioms forget6_d6x

/-- A confirmed vulnerability carries over: under the conditions of the carry-over, `Confirmed6X`
    of the refined run 1 iff `ConfirmedT6` of the base run 1 (the support `Sup6X` is the lift of
    `Sup6T`). -/
theorem sup6x_iff (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFree P (D6T P taint counted L α sinks roots)) (M : MethodId) (i : PFact) :
    Sup6X P taint counted L α sinks roots M i ↔ Sup6T P taint counted L α sinks roots M i := by
  constructor
  · intro h
    induction h with
    | root hM => exact Sup6T.root hM
    | @call M i n f n' c e a j _ hD hfd hE he ha had hj hl ih =>
      obtain ⟨hfe, hD'⟩ := d6x_base hP hcl hs hD
      rw [hfe, bindX_free_facts f.af ((hP.2 _ _ _ _ hE).1 e he)] at ha
      obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
      refine Sup6T.call ih hD' hfd hE he ha0 had (d6x_base hP hcl hs hj) ?_
      rcases hl with hl | ⟨k, t, hk, hrest⟩
      · exact Or.inl hl
      · exact Or.inr ⟨k, t, d6x_base hP hcl hs hk, hrest⟩
  · intro h
    induction h with
    | root hM => exact Sup6X.root hM
    | @call M i n f n' c e a j _ hD hfd hE he ha had hj hl ih =>
      have ha' : plain a ∈ (bindX (plain f) e).facts := by
        rw [bindX_free_facts f ((hP.2 _ _ _ _ hE).1 e he)]; exact List.mem_map_of_mem ha
      refine Sup6X.call ih (d6t_lift hP hcl hs hD) hfd hE he ha' had (d6t_lift hP hcl hs hj) ?_
      rcases hl with hl | ⟨k, t, hk, hrest⟩
      · exact Or.inl hl
      · exact Or.inr ⟨k, t, d6t_lift hP hcl hs hk, hrest⟩

#print axioms sup6x_iff

/-- THE CONFIRMATION CARRIES OVER (run 1): `Confirmed6X ↔ ConfirmedT6` under the conditions of the
    carry-over. -/
theorem confirmed6x_iff (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFree P (D6T P taint counted L α sinks roots)) (M : MethodId) (n : Node) (s : PFact) :
    Confirmed6X P taint counted L α sinks roots M n s ↔
      ConfirmedT6 P taint counted L α sinks roots M n s := by
  constructor
  · rintro ⟨i, f, hD, hS, hfd, hsk, hc⟩
    obtain ⟨hfe, hD'⟩ := d6x_base hP hcl hs hD
    rw [hfe, checkX_plain] at hc
    exact ⟨i, f.af, hD', (sup6x_iff hP hcl hs M i).mp hS, hfd, hsk, hc⟩
  · rintro ⟨i, f, hD, hS, hfd, hsk, hc⟩
    exact ⟨i, plain f, d6t_lift hP hcl hs hD, (sup6x_iff hP hcl hs M i).mpr hS, hfd, hsk,
      by rw [checkX_plain]; exact hc⟩

#print axioms confirmed6x_iff

end Sim6

/-! ### The operations of the restricted run on plain inputs -/

theorem normJ_empty (j : PFact) : normJ j Excl.empty = Excl.empty := by
  unfold normJ; cases j.kind <;> rfl

/-- With no exclusion, the refined emission is the base emission with the empty exclusion. -/
theorem emitX_empty (d a : PFact) :
    emitX d a Excl.empty = (emitM d a).map (fun j => (j, Excl.empty)) := by
  unfold emitX
  cases emitM d a with
  | none => rfl
  | some j =>
    dsimp only
    cases relate d.path a.path with
    | above r => dsimp only; rw [admits_empty]; rfl
    | below r => rw [normJ_empty]; rfl
    | apart => rw [normJ_empty]; rfl

/-- With no exclusion, the emission with the must flag is the base `emitT`. -/
theorem emitTX_free (d a : PFact) (am : Bool) :
    emitTX emitX d a am Excl.empty = (emitT d a am).map (fun p => (p.1, p.2, Excl.empty)) := by
  unfold emitTX emitT
  rw [emitX_empty]
  cases emitM d a <;> rfl

theorem empty_subB (e : Excl) : Excl.empty.subB e = true := by cases e <;> rfl

/-- With no exclusion, the refined satisfaction is the base `satI` (a premise that `satI` accepts
    lies at or below the added fact, and the empty exclusion admits every step). -/
theorem satX_empty (j a : PFact) : satX j Excl.empty a Excl.empty = satI j a := by
  unfold satX
  cases hs : satI j a with
  | false => rfl
  | true =>
    show insideExB j Excl.empty a Excl.empty = true
    have hc : coversB ⟨a.base, a.path, a.kind, .star⟩ j = true := RExact.bool_and_left hs
    unfold coversB at hc
    dsimp only at hc
    cases hdp : dropPrefix a.path j.path with
    | none =>
      rw [hdp] at hc
      cases RExact.bool_and_right hc
    | some r =>
      have hrel : relate a.path j.path = .below r := by
        unfold relate; rw [hdp]
      unfold insideExB
      rw [hrel]
      cases r with
      | nil => exact empty_subB _
      | cons x r => exact admits_empty _

#print axioms satX_empty

/-- With no exclusion, the refined restricted conclusion is the base one. -/
theorem restrictConcX_plain (g : AFact) (p : PFact) :
    restrictConcX (plain g) p = (restrictConcU g p).map plain := by
  unfold restrictConcX plain
  dsimp only
  cases restrictConcU g p with
  | none => rfl
  | some g' =>
    dsimp only
    cases relate p.path g.fact.path with
    | above r => dsimp only; rw [admits_empty]; rfl
    | below r => rw [normX_empty]; rfl
    | apart => rw [normX_empty]; rfl

/-- With no exclusion, the refined restriction is the base `restrictU`. -/
theorem restrictX_plain (j : PFact) (g : AFact) (d : DemandEdge) :
    restrictX j Excl.empty (plain g) d = (restrictU j g d).map plain := by
  unfold restrictX
  show _ = (restrictWith restrictConcU j g d).map plain
  unfold restrictWith
  cases d.dout with
  | none => rfl
  | some p =>
    dsimp only
    rw [overlapX_empty]
    cases overlapB j d.din with
    | false => rfl
    | true => exact restrictConcX_plain g p

#print axioms restrictX_plain

/-- The base restricted conclusion is the conclusion itself or has no `*` tail. -/
theorem restrictConcU_cases {g g' : AFact} {p : PFact} (h : restrictConcU g p = some g') :
    g' = g ∨ g'.fact.kind.isStar = false := by
  unfold restrictConcU at h
  split at h
  · split at h
    · split at h
      · cases h; exact Or.inl rfl
      · cases h
    · split at h
      · cases h; right; cases p.kind <;> rfl
      · cases h
    · cases h
  · cases h

/-- The restriction keeps a summary free. -/
theorem restrictU_free {j : PFact} {g g' : AFact} {d : DemandEdge} (h : restrictU j g d = some g')
    (hf : EdgeFree j g.fact) : EdgeFree j g'.fact := by
  unfold restrictU restrictWith at h
  cases hd : d.dout with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    dsimp only at h
    split at h
    · rcases restrictConcU_cases h with rfl | hns
      · exact hf
      · intro et het; rw [het] at hns; cases hns
    · cases h

theorem startX_plain (j : PFact) (mj : Bool) : startX j mj Excl.empty = plain (startT j mj) := by
  cases mj with
  | false => rfl
  | true => exact normX_empty _

theorem recLayerX_plain (mj s : Bool) (x : AFact) :
    recLayerX mj s (plain x) = plain (recLayer mj s x) := by
  unfold recLayerX recLayer plain
  cases mj && !s <;> rfl

theorem plain_self {x : XFact} {y : AFact} (h : x = plain y) : x = plain x.af := by
  subst h; rfl

/-- With no exclusion, the support link is the base `SupLink`. -/
theorem supLinkX_iff (a j : PFact) (mj : Bool) :
    SupLinkX a Excl.empty j mj Excl.empty ↔ SupLink a j mj := by
  unfold SupLinkX SupLink
  rw [satX_empty]

/-! ### The carry-over of the restricted run -/

/-- The refined object of a base object of the restricted run: the same fact, layer and must flag,
    the empty exclusions. -/
def liftR : TObj → XObj
  | .init M j mj      => .init M j mj Excl.empty
  | .edge M j mj n f  => .edge M j mj Excl.empty n (plain f)
  | .added M a am     => .added M a am Excl.empty
  | .req M j t        => .req M j t
  | .vuln M n s d     => .vuln M n s d

theorem forget_liftR (o : TObj) : (liftR o).forget = o := by cases o <;> rfl

/-- The base object of a refined object of the restricted run, as a predicate. -/
def BaseR (R : TObj → Prop) : XObj → Prop
  | .init M j mj jex     => jex = Excl.empty ∧ R (.init M j mj)
  | .edge M j mj jex n x => jex = Excl.empty ∧ x = plain x.af ∧ R (.edge M j mj n x.af)
  | .added M a am aex    => aex = Excl.empty ∧ R (.added M a am)
  | .req M j t           => R (.req M j t)
  | .vuln M n s d        => R (.vuln M n s d)

/-- The base restricted run `R` has no callee summary with an exclusion. -/
def SumFreeR (P : Program) (R : TObj → Prop) : Prop :=
  ∀ M n c n' j mj g, (M, n, Instr.call c, n') ∈ P.edges → R (.init c.callee j mj) →
    R (.edge c.callee j mj (P.exit c.callee) g) → EdgeFree j g.fact

/-- The refined records are the base records with the empty exclusions. -/
def RecsLift (recsX : MethodId → PFact × Bool × Excl × XFact → Prop)
    (recs : MethodId → PFact × Bool × AFact → Prop) : Prop :=
  ∀ m j mj jex g, recsX m (j, mj, jex, g) ↔ (jex = Excl.empty ∧ g = plain g.af ∧ recs m (j, mj, g.af))

/-- The base records have no exclusion. -/
def RecsFree (recs : MethodId → PFact × Bool × AFact → Prop) : Prop :=
  ∀ m j mj g, recs m (j, mj, g) → EdgeFree j g.fact

section SimR
variable {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
  {demand : MethodId → DemandEdge → Prop}
  {recsX : MethodId → PFact × Bool × Excl × XFact → Prop}
  {recs : MethodId → PFact × Bool × AFact → Prop}
  {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

/-- Every base object of the restricted run (the spec instance of `DRT`), lifted, is an object of
    the refined restricted run (`DRXs`). -/
theorem drt_liftR (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFreeR P (DRT P taint counted L demand emitM satI restrictU recs sinks roots))
    (hrl : RecsLift recsX recs) (hrf : RecsFree recs) {o : TObj}
    (h : DRT P taint counted L demand emitM satI restrictU recs sinks roots o) :
    DRXs P taint counted L demand recsX sinks roots (liftR o) := by
  induction h with
  | root hM => exact DRX.root hM
  | start _ ih =>
    have h := DRX.start ih
    rw [startX_plain] at h
    exact h
  | @step M i mi n f n' s f' _ hE hf ih =>
    have hf' : plain f' ∈ (transferX taint counted L s (plain f)).facts := by
      rw [transferX_free_facts taint counted L (hP.1 _ _ _ _ hE) f]
      exact List.mem_map_of_mem hf
    exact DRX.step ih hE hf'
  | @reqStmt M i mi n f n' s t _ hE ht ih =>
    have ht' : t ∈ (transferX taint counted L s (plain f)).reqs := by
      rw [transferX_free_reqs taint counted L (hP.1 _ _ _ _ hE) f]; exact ht
    exact DRX.reqStmt ih hE ht'
  | pass _ hE hm ih => exact DRX.pass ih hE hm
  | @added M i mi n f n' c e a _ hE he ha ih =>
    have ha' : plain a ∈ (bindX (plain f) e).facts := by
      rw [bindX_free_facts f ((hP.2 _ _ _ _ hE).1 e he)]; exact List.mem_map_of_mem ha
    exact DRX.added ih hE he ha'
  | @initR m a am d j mj _ hd he ih =>
    have he' : emitTX emitX d.din a am Excl.empty = some (j, mj, Excl.empty) := by
      rw [emitTX_free]
      have he2 : emitT d.din a am = some (j, mj) := he
      rw [he2]; rfl
    exact DRX.initR ih hd he'
  | @ret M i mi n f n' c e1 a j mj g d g' r e2 r' _ hE he1 ha hj hg hd hres hsat hr he2 hr'
      ihf ihj ihg =>
    have ha' : plain a ∈ (bindX (plain f) e1).facts := by
      rw [bindX_free_facts f ((hP.2 _ _ _ _ hE).1 e1 he1)]; exact List.mem_map_of_mem ha
    have hres' : restrictX j Excl.empty (plain g) d = some (plain g') := by
      rw [restrictX_plain, hres]; rfl
    have hsat' : satX j Excl.empty a.fact Excl.empty = true := by rw [satX_empty]; exact hsat
    have hr1 : plain r ∈ (applySummaryX (plain a) j Excl.empty (plain g')).facts := by
      rw [applySummaryX_free_facts a g' (restrictU_free hres (hs _ _ _ _ _ _ _ hE hj hg))]
      exact List.mem_map_of_mem hr
    have hr2 : plain r' ∈ (bindX (plain r) e2).facts := by
      rw [bindX_free_facts r ((hP.2 _ _ _ _ hE).2 e2 he2)]; exact List.mem_map_of_mem hr'
    have h := DRX.ret ihf hE he1 ha' ihj ihg hd hres' hsat' hr1 he2 hr2
    rw [limitFX_plain] at h
    exact h
  | @retRec M i mi n f n' c e1 a j mj g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ihf =>
    have ha' : plain a ∈ (bindX (plain f) e1).facts := by
      rw [bindX_free_facts f ((hP.2 _ _ _ _ hE).1 e1 he1)]; exact List.mem_map_of_mem ha
    have hrec' : recsX c.callee (j, mj, Excl.empty, plain g) := (hrl _ _ _ _ _).mpr ⟨rfl, rfl, hrec⟩
    have hsat' : satX j Excl.empty a.fact Excl.empty = true ∨ applicable j a.fact = true := by
      rw [satX_empty]; exact hsat
    have hr1 : plain r ∈ (applySummaryX (plain a) j Excl.empty (plain g)).facts := by
      rw [applySummaryX_free_facts a g (hrf _ _ _ _ hrec)]; exact List.mem_map_of_mem hr
    have hr2 : plain r' ∈ (bindX (plain r) e2).facts := by
      rw [bindX_free_facts r ((hP.2 _ _ _ _ hE).2 e2 he2)]; exact List.mem_map_of_mem hr'
    have h := DRX.retRec ihf hE he1 ha' hrec' hsat' hr1 he2 hr2
    have e1 : satX j Excl.empty (plain a).af.fact (plain a).ex = satI j a.fact := satX_empty j a.fact
    rw [e1, recLayerX_plain, limitFX_plain] at h
    exact h
  | reqSink _ hs' hc ih => exact DRX.reqSink ih hs' (by rw [checkX_plain]; exact hc)
  | @answer M i t a am _ _ ha ho ih1 ih2 =>
    exact DRX.answer ih1 ih2 ha ((overlapX_empty a i).trans ho)
  | @reqUp m j t M ic mc n f n' c e a _ _ hE hc he ha hcl' ho ih1 ih2 =>
    have ha' : plain a ∈ (bindX (plain f) e).facts := by
      rw [bindX_free_facts f ((hP.2 _ _ _ _ hE).1 e he)]; exact List.mem_map_of_mem ha
    exact DRX.reqUp ih1 ih2 hE hc he ha' hcl' ((overlapX_empty a.fact j).trans ho)
  | vuln _ hs' hc ih => exact DRX.vuln ih hs' (by rw [checkX_plain]; exact hc)
  | clean _ hE _ _ => exact (hcl _ _ _ _ hE).elim
  | reqClean _ hE _ _ => exact (hcl _ _ _ _ hE).elim
  | filt _ hE hf ih => exact DRX.filt ih hE hf

#print axioms drt_liftR

/-- Every object of the refined restricted run is the lift of a base object (`BaseR`). -/
theorem drx_baseR (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFreeR P (DRT P taint counted L demand emitM satI restrictU recs sinks roots))
    (hrl : RecsLift recsX recs) (hrf : RecsFree recs) {o : XObj}
    (h : DRXs P taint counted L demand recsX sinks roots o) :
    BaseR (DRT P taint counted L demand emitM satI restrictU recs sinks roots) o := by
  induction h with
  | root hM => exact ⟨rfl, DRT.root hM⟩
  | @start M j mj jex _ ih =>
    obtain ⟨rfl, hD⟩ := ih
    refine ⟨rfl, plain_self (startX_plain j mj), ?_⟩
    rw [startX_af]
    exact DRT.start hD
  | @step M i mi iex n f n' s f' _ hE hf ih =>
    obtain ⟨rfl, he, hD⟩ := ih
    rw [he, transferX_free_facts taint counted L (hP.1 _ _ _ _ hE) f.af] at hf
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hf
    exact ⟨rfl, rfl, DRT.step hD hE hy⟩
  | @reqStmt M i mi iex n f n' s t _ hE ht ih =>
    obtain ⟨_, he, hD⟩ := ih
    rw [he, transferX_free_reqs taint counted L (hP.1 _ _ _ _ hE) f.af] at ht
    exact DRT.reqStmt hD hE ht
  | pass _ hE hm ih =>
    obtain ⟨h1, h2, hD⟩ := ih
    exact ⟨h1, h2, DRT.pass hD hE hm⟩
  | @added M i mi iex n f n' c e a _ hE he ha ih =>
    obtain ⟨_, hfe, hD⟩ := ih
    rw [hfe, bindX_free_facts f.af ((hP.2 _ _ _ _ hE).1 e he)] at ha
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
    exact ⟨rfl, DRT.added hD hE he ha0⟩
  | @initR m a am aex d j mj jex _ hd he ih =>
    obtain ⟨rfl, hD⟩ := ih
    rw [emitTX_free] at he
    cases hT : emitT d.din a am with
    | none => rw [hT] at he; cases he
    | some p =>
      obtain ⟨j0, mj0⟩ := p
      rw [hT] at he
      cases he
      exact ⟨rfl, DRT.initR hD hd hT⟩
  | @ret M i mi iex n f n' c e1 a j mj jex g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr'
      ihf ihj ihg =>
    obtain ⟨rfl, hfe, hfD⟩ := ihf
    obtain ⟨rfl, hjD⟩ := ihj
    obtain ⟨_, hge, hgD⟩ := ihg
    rw [hfe, bindX_free_facts f.af ((hP.2 _ _ _ _ hE).1 e1 he1)] at ha
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
    rw [hge, restrictX_plain] at hres
    cases hU : restrictU j g.af d with
    | none => rw [hU] at hres; cases hres
    | some g0 =>
      rw [hU] at hres
      cases hres
      have hsat' : satI j a0.fact = true := (satX_empty j a0.fact).symm.trans hsat
      rw [applySummaryX_free_facts a0 g0 (restrictU_free hU (hs _ _ _ _ _ _ _ hE hjD hgD))] at hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      rw [bindX_free_facts r0 ((hP.2 _ _ _ _ hE).2 e2 he2)] at hr'
      obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hr'
      rw [limitFX_plain]
      exact ⟨rfl, rfl, DRT.ret hfD hE he1 ha0 hjD hgD hd hU hsat' hr0 he2 hr1⟩
  | @retRec M i mi iex n f n' c e1 a j mj jex g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ihf =>
    obtain ⟨rfl, hfe, hfD⟩ := ihf
    obtain ⟨rfl, hge, hrec0⟩ := (hrl _ _ _ _ _).mp hrec
    rw [hfe, bindX_free_facts f.af ((hP.2 _ _ _ _ hE).1 e1 he1)] at ha
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
    have e1 : satX j Excl.empty (plain a0).af.fact (plain a0).ex = satI j a0.fact :=
      satX_empty j a0.fact
    rw [e1] at hsat
    rw [hge, applySummaryX_free_facts a0 g.af (hrf _ _ _ _ hrec0)] at hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    rw [bindX_free_facts r0 ((hP.2 _ _ _ _ hE).2 e2 he2)] at hr'
    obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp hr'
    rw [e1, recLayerX_plain, limitFX_plain]
    exact ⟨rfl, rfl, DRT.retRec hfD hE he1 ha0 hrec0 hsat hr0 he2 hr1⟩
  | @reqSink M i mi iex n f s t _ hs' hc ih =>
    obtain ⟨_, hfe, hD⟩ := ih
    rw [hfe, checkX_plain] at hc
    exact DRT.reqSink hD hs' hc
  | @answer M i t a am aex _ _ ha ho ih1 ih2 =>
    obtain ⟨rfl, hD⟩ := ih2
    exact ⟨rfl, DRT.answer ih1 hD ha ((overlapX_empty a i).symm.trans ho)⟩
  | @reqUp m j t M ic mc icx n f n' c e a _ _ hE hc he ha hcl' ho ih1 ih2 =>
    obtain ⟨_, hfe, hD⟩ := ih2
    rw [hfe, bindX_free_facts f.af ((hP.2 _ _ _ _ hE).1 e he)] at ha
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
    exact DRT.reqUp ih1 hD hE hc he ha0 hcl' ((overlapX_empty a0.fact j).symm.trans ho)
  | @vuln M i mi iex n f s _ hs' hc ih =>
    obtain ⟨_, hfe, hD⟩ := ih
    rw [hfe, checkX_plain] at hc
    exact DRT.vuln hD hs' hc
  | clean _ hE _ _ => exact (hcl _ _ _ _ hE).elim
  | reqClean _ hE _ _ => exact (hcl _ _ _ _ hE).elim
  | filt _ hE hf ih =>
    obtain ⟨h1, h2, hD⟩ := ih
    exact ⟨h1, h2, DRT.filt hD hE hf⟩

#print axioms drx_baseR

/-- THE CARRY-OVER OF THE RESTRICTED RUN (the generic lemma). For a program with no exclusion edge
    (`ExclFreeProg`), no cleaner (`NoClean`), a base run whose callee summaries are free
    (`SumFreeR`), and records that are the base records with the empty exclusions (`RecsLift`) and
    free (`RecsFree`): the objects of `DRXs` (the spec instance `emitX`, `satX`, `restrictX`) are
    EXACTLY the lifts of the objects of the spec instance of `DRT` (`emitM`, `satI`, `restrictU`):
    the same fact, layer and must flag, the empty exclusions (`liftR`). -/
theorem drx_iff_drt (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFreeR P (DRT P taint counted L demand emitM satI restrictU recs sinks roots))
    (hrl : RecsLift recsX recs) (hrf : RecsFree recs) (o : XObj) :
    DRXs P taint counted L demand recsX sinks roots o ↔
      ∃ o', DRT P taint counted L demand emitM satI restrictU recs sinks roots o' ∧ liftR o' = o := by
  constructor
  · intro h
    have hb := drx_baseR hP hcl hs hrl hrf h
    cases o with
    | init M j mj jex =>
      obtain ⟨rfl, hD⟩ := hb
      exact ⟨.init M j mj, hD, rfl⟩
    | edge M j mj jex n x =>
      obtain ⟨rfl, hx, hD⟩ := hb
      refine ⟨.edge M j mj n x.af, hD, ?_⟩
      show XObj.edge M j mj Excl.empty n (plain x.af) = .edge M j mj Excl.empty n x
      rw [← hx]
    | added M a am aex =>
      obtain ⟨rfl, hD⟩ := hb
      exact ⟨.added M a am, hD, rfl⟩
    | req M j t => exact ⟨.req M j t, hb, rfl⟩
    | vuln M n s d => exact ⟨.vuln M n s d, hb, rfl⟩
  · rintro ⟨o', h, rfl⟩
    exact drt_liftR hP hcl hs hrl hrf h

#print axioms drx_iff_drt

/-- The support carries over (`SupX` with the empty exclusion is `SupT`). -/
theorem supX_iff (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFreeR P (DRT P taint counted L demand emitM satI restrictU recs sinks roots))
    (hrl : RecsLift recsX recs) (hrf : RecsFree recs) (M : MethodId) (i : PFact) (mi : Bool)
    (iex : Excl) :
    SupX P taint counted L demand emitX satX restrictX recsX sinks roots M i mi iex ↔
      (iex = Excl.empty ∧ SupT P taint counted L demand emitM satI restrictU recs sinks roots M i mi) := by
  constructor
  · intro h
    induction h with
    | root hM => exact ⟨rfl, SupT.root hM⟩
    | @call M i mi iex n f n' c e a j mj jex _ hD hfd hE he ha had hj hl ih =>
      obtain ⟨rfl, hS⟩ := ih
      obtain ⟨_, hfe, hD'⟩ := drx_baseR hP hcl hs hrl hrf hD
      obtain ⟨rfl, hj'⟩ := drx_baseR hP hcl hs hrl hrf hj
      rw [hfe, bindX_free_facts f.af ((hP.2 _ _ _ _ hE).1 e he)] at ha
      obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
      exact ⟨rfl, SupT.call hS hD' hfd hE he ha0 had hj' ((supLinkX_iff _ _ _).mp hl)⟩
  · rintro ⟨rfl, h⟩
    induction h with
    | root hM => exact SupX.root hM
    | @call M i mi n f n' c e a j mj _ hD hfd hE he ha had hj hl ih =>
      have ha' : plain a ∈ (bindX (plain f) e).facts := by
        rw [bindX_free_facts f ((hP.2 _ _ _ _ hE).1 e he)]; exact List.mem_map_of_mem ha
      exact SupX.call ih (drt_liftR hP hcl hs hrl hrf hD) hfd hE he ha' had
        (drt_liftR hP hcl hs hrl hrf hj) ((supLinkX_iff _ _ _).mpr hl)

#print axioms supX_iff

/-- THE CONFIRMATION CARRIES OVER (the restricted run): `ConfirmedX ↔ ConfirmedT` under the
    conditions of the carry-over. -/
theorem confirmedX_iff (hP : ExclFreeProg P) (hcl : NoClean P)
    (hs : SumFreeR P (DRT P taint counted L demand emitM satI restrictU recs sinks roots))
    (hrl : RecsLift recsX recs) (hrf : RecsFree recs) (M : MethodId) (n : Node) (s : PFact) :
    ConfirmedX P taint counted L demand emitX satX restrictX recsX sinks roots M n s ↔
      ConfirmedT P taint counted L demand emitM satI restrictU recs sinks roots M n s := by
  constructor
  · rintro ⟨i, mi, iex, f, hD, hS, hfd, hsk, hc⟩
    obtain ⟨_, hfe, hD'⟩ := drx_baseR hP hcl hs hrl hrf hD
    rw [hfe, checkX_plain] at hc
    exact ⟨i, mi, f.af, hD', ((supX_iff hP hcl hs hrl hrf M i mi iex).mp hS).2, hfd, hsk, hc⟩
  · rintro ⟨i, mi, f, hD, hS, hfd, hsk, hc⟩
    exact ⟨i, mi, Excl.empty, plain f, drt_liftR hP hcl hs hrl hrf hD,
      (supX_iff hP hcl hs hrl hrf M i mi Excl.empty).mpr ⟨rfl, hS⟩, hfd, hsk,
      by rw [checkX_plain]; exact hc⟩

#print axioms confirmedX_iff

end SimR

end Carry

/-! ## Program G: the getter -/

namespace G

open ApSpec.AnyTaintCases.G (prog srcS callGet getS bIn bOut sinkP sinks taint hE00 hE01 hE10 no_clean
  no_filt Z DTO Ap J1 J1f RET1 Xd Xn Jf Jb RETn dGet)

/-! ### The refined facts (the round-1 facts with the empty exclusion) -/

def Zx : XFact := plain Z
def DTOx : XFact := plain DTO
def J1x : XFact := plain J1f
def RET1x : XFact := plain RET1
def Xdx : XFact := plain Xd
def Xnx : XFact := plain Xn
/-- The added fact `(p, [], [any-taint], {}, T)` of the normal link. -/
def ApX : XFact := plain ⟨Ap, false⟩
/-- The start fact of the must-premise `(p, [f], [any-taint], {}, T)`: itself, normal. -/
def JfX : XFact := plain ⟨Jf, false⟩
def RETnx : XFact := plain RETn

/-! ### Run 1 with the exclusion (`D6X`), completely -/

/-- Run 1 of program G with the exclusion: `policy1`, the field limit 3. -/
abbrev R1 : XObj6 → Prop := D6X prog taint cnt 3 policy1 sinks [0]

def inits1 : List (MethodId × PFact) := [(0, zeroFact), (1, J1)]
def edges1 : List (MethodId × PFact × Node × XFact) :=
  [(0, zeroFact, 0, Zx), (0, zeroFact, 1, Zx), (0, zeroFact, 1, DTOx), (0, zeroFact, 2, Zx),
   (0, zeroFact, 2, Xdx), (1, J1, 0, J1x), (1, J1, 1, J1x), (1, J1, 1, RET1x)]
def addeds1 : List (MethodId × PFact) := [(1, Ap)]
/-- The only vulnerability of run 1: `sinkAny(x)`, in the DEMAND layer. -/
def vulns1 : List (MethodId × Node × PFact × Bool) := [(0, 2, sinkP, true)]

/-- Every object of the refined run 1 is in the lists; no request; the only vulnerability is in
    the demand layer. -/
def Inv1 : XObj6 → Prop
  | .init M i => (M, i) ∈ inits1
  | .edge M i n f => (M, i, n, f) ∈ edges1
  | .added M a => (M, a) ∈ addeds1
  | .req _ _ _ => False
  | .vuln M n s d => (M, n, s, d) ∈ vulns1

instance : DecidablePred Inv1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s d => inferInstanceAs (Decidable ((M, n, s, d) ∈ vulns1))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM G WITH THE EXCLUSION (`D6X`): the objects of the round-1 run
    `AnyTaintCases.G.inv1T` with the empty exclusion; every vulnerability is in the demand layer. -/
theorem inv1 {o : XObj6} (h : R1 o) : Inv1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits1,
      Inv1 (.edge x.1 x.2 (prog.entry x.1) (startX x.2 false Excl.empty))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferX taint cnt 3 srcS x.2.2.2).facts, Inv1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transferX taint cnt 3 getS x.2.2.2).facts, Inv1 (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transferX taint cnt 3 srcS x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transferX taint cnt 3 getS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.af.fact.base callGet.touched = false → Inv1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callGet.toCallee,
          ∀ a ∈ (bindX x.2.2.2 e).facts, Inv1 (.added callGet.callee a.af.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addeds1, Inv1 (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callGet.toCallee, ∀ a ∈ (bindX x.2.2.2 e1).facts,
          ∀ y ∈ inits1, y.1 = 1 → applicable y.2 a.af.fact = true →
          ∀ z ∈ edges1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummaryX a y.2 Excl.empty z.2.2.2).facts,
          ∀ e2 ∈ callGet.fromCallee, ∀ r' ∈ (bindX r e2).facts,
            Inv1 (.edge 0 x.2.1 2 (limitFX cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 →
        checkX x.2.1 x.2.2.2 sinkP = .none ∨ checkX x.2.1 x.2.2.2 sinkP = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 →
        checkX x.2.1 x.2.2.2 sinkP = .triggered → (0, 2, sinkP, x.2.2.2.af.demand) ∈ vulns1)
        (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1

/-! ### Run 1 with the exclusion: the derivation and the theorems -/

-- the source result is `[any-taint]` with the empty exclusion, normal (a taint edge)
example : (transferX taint cnt 3 srcS Zx).facts = [Zx, DTOx] := by decide
-- the binding into `get` gives the added fact `(p, [], [any], T)` in the normal layer
example : (bindX DTOx bIn).facts = [ApX] := by decide
-- THE FLOW SUMMARY OF `ret = p.f` IS CASE `above` (as round 1): the refined transfer gives the
-- same facts with the empty exclusion; the conclusion `(ret, [], [any], *)` is DEMAND
example : (transferX taint cnt 3 getS J1x).facts = [J1x, RET1x] := by decide
-- the application keeps the layer of the summary edge; no exclusion is created
example : (applySummaryX ApX J1 Excl.empty RET1x).facts = [plain AnyTaintCases.G.RETd] := by
  decide
example : (bindX (plain AnyTaintCases.G.RETd) bOut).facts = [Xdx] := by decide
example : checkX zeroFact Xdx sinkP = .triggered := by decide

/-- Run 1: the zero fact at the entry of `root`. -/
theorem r1_e00 : R1 (.edge 0 zeroFact 0 Zx) := D6X.start (D6X.root (List.Mem.head _))
/-- Run 1: the zero fact after `dto = srcAny()`. -/
theorem r1_z01 : R1 (.edge 0 zeroFact 1 Zx) := D6X.step r1_e00 hE00 (by decide)
/-- Run 1: the source edge `zero → (dto, [], [any-taint], {}, T)`, NORMAL. -/
theorem r1_e01 : R1 (.edge 0 zeroFact 1 DTOx) := D6X.step r1_e00 hE00 (by decide)
/-- Run 1: the zero fact passes the call (it is not touched). -/
theorem r1_z02 : R1 (.edge 0 zeroFact 2 Zx) := D6X.pass r1_z01 hE01 (by decide)
/-- Run 1: the added fact `(p, [], [any], T)` of `get`. -/
theorem r1_ad : R1 (.added 1 Ap) :=
  D6X.added (c := callGet) (e := bIn) (a := ApX) r1_e01 hE01 (List.Mem.head _) (by decide)

/-- Run 1: `policy1` serves the added fact with `(p, [], *, {}, *)`. -/
theorem r1_i1 : R1 (.init 1 J1) := by
  have h : R1 (.init 1 (policy1 1 Ap)) := D6X.initA r1_ad
  have hp : policy1 1 Ap = J1 := by decide
  rw [hp] at h
  exact h

/-- Run 1: the start fact of `get`. -/
theorem r1_s10 : R1 (.edge 1 J1 0 J1x) := D6X.start r1_i1
/-- Run 1: the identity summary `(p, [], *, {}, *) → (p, [], *, {}, *)` of `get`. -/
theorem r1_exit_p : R1 (.edge 1 J1 1 J1x) := D6X.step r1_s10 hE10 (by decide)

/-- Run 1 (`D6X`): THE FLOW SUMMARY OF `get` IS `(p, [], *, {}, *) → (ret, [], [any], *)` IN THE
    DEMAND LAYER (case `above`: the read `p.f` is below the premise `p`), with the empty
    exclusion: the refined run has the round-1 summary (`AnyTaintCases.G.run1T_flow_above`). -/
theorem run1_flow_above : R1 (.edge 1 J1 1 RET1x) ∧ RET1x.af.demand = true ∧ RET1x.ex = Excl.empty :=
  ⟨D6X.step r1_s10 hE10 (by decide), rfl, rfl⟩

#print axioms run1_flow_above

/-- Run 1: the application of the demand summary gives the sink edge
    `zero → (x, [], [any], T)` in the DEMAND layer. -/
theorem r1_e02 : R1 (.edge 0 zeroFact 2 Xdx) :=
  D6X.ret (c := callGet) (e1 := bIn) (a := ApX) (j := J1) (g := RET1x)
    (r := plain AnyTaintCases.G.RETd) (e2 := bOut) (r' := Xdx) r1_e01 hE01 (List.Mem.head _)
    (by decide) r1_i1 (by decide) run1_flow_above.1 (by decide) (List.Mem.head _) (by decide)

/-- RUN 1 OF `D6X` REPORTS THE VULNERABILITY OF `G`, IN THE DEMAND LAYER. -/
theorem run1_vuln : R1 (.vuln 0 2 sinkP true) := D6X.vuln r1_e02 (List.Mem.head _) (by decide)

#print axioms run1_vuln

/-- Run 1 of `D6X` has NO normal report of `G` (the complete run `inv1`): the vulnerability is only
    demand. -/
theorem run1_no_normal : ¬ R1 (.vuln 0 2 sinkP false) := by
  intro h
  exact absurd (inv1 h) (by decide)

#print axioms run1_no_normal

/-- RUN 1 OF `D6X` DOES NOT CONFIRM `G` (`AnyTaintEx.Confirmed6X`): no normal sink edge. -/
theorem run1_not_confirmed : ¬ Confirmed6X prog taint cnt 3 policy1 sinks [0] 0 2 sinkP := by
  rintro ⟨i, f, hf, _, hd, hs, hc⟩
  have hv := D6X.vuln hf hs hc
  rw [hd] at hv
  exact run1_no_normal hv

#print axioms run1_not_confirmed

/-! ### The refined run 1 read without exclusions IS the round-1 run 1 -/

/-- The round-1 objects of run 1 that `AnyTaintCases.G` does not name. -/
theorem t1_e00 : AnyTaintCases.G.R1T (.edge 0 zeroFact 0 Z) := D6T.start (D6T.root (List.Mem.head _))
theorem t1_z01 : AnyTaintCases.G.R1T (.edge 0 zeroFact 1 Z) := D6T.step t1_e00 hE00 (by decide)
theorem t1_z02 : AnyTaintCases.G.R1T (.edge 0 zeroFact 2 Z) := D6T.pass t1_z01 hE01 (by decide)
theorem t1_s10 : AnyTaintCases.G.R1T (.edge 1 J1 0 J1f) := D6T.start AnyTaintCases.G.r1_i1
theorem t1_ad : AnyTaintCases.G.R1T (.added 1 Ap) :=
  D6T.added (c := callGet) (e := bIn) (a := ⟨Ap, false⟩) AnyTaintCases.G.r1_e01 hE01
    (List.Mem.head _) (by decide)

/-- THE REFINED RUN 1 OF `G`, READ WITHOUT ITS EXCLUSIONS (`AnyTaintExCov.forget6`, the reading of
    the backward run and of the reports in the refined pipeline), IS EXACTLY THE ROUND-1 RUN 1
    `AnyTaintCases.G.R1T` (`D6T`): every object of one is an object of the other. -/
theorem run1_forgets (o : Obj) : AnyTaintExCov.forget6 R1 o ↔ AnyTaintCases.G.R1T o := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hi := inv1 hx
    cases x with
    | init M i =>
      cases hi with
      | head => exact D6T.root (List.Mem.head _)
      | tail _ h => cases h with
        | head => exact AnyTaintCases.G.r1_i1
        | tail _ h => cases h
    | edge M i n f =>
      cases hi with
      | head => exact t1_e00
      | tail _ h => cases h with
        | head => exact t1_z01
        | tail _ h => cases h with
          | head => exact AnyTaintCases.G.r1_e01
          | tail _ h => cases h with
            | head => exact t1_z02
            | tail _ h => cases h with
              | head => exact AnyTaintCases.G.r1_e02
              | tail _ h => cases h with
                | head => exact t1_s10
                | tail _ h => cases h with
                  | head => exact AnyTaintCases.G.r1_exit_p
                  | tail _ h => cases h with
                    | head => exact AnyTaintCases.G.run1T_flow_above
                    | tail _ h => cases h
    | added M a =>
      cases hi with
      | head => exact t1_ad
      | tail _ h => cases h
    | req M i t => exact hi.elim
    | vuln M n s d =>
      cases hi with
      | head => exact AnyTaintCases.G.run1T_vuln
      | tail _ h => cases h
  · intro h
    cases o with
    | init M i =>
      have hi := AnyTaintCases.G.inv1T h
      cases hi with
      | head => exact ⟨.init 0 zeroFact, D6X.root (List.Mem.head _), rfl⟩
      | tail _ h => cases h with
        | head => exact ⟨.init 1 J1, r1_i1, rfl⟩
        | tail _ h => cases h
    | edge M i n f =>
      have hi := AnyTaintCases.G.inv1T h
      cases hi with
      | head => exact ⟨_, r1_e00, rfl⟩
      | tail _ h => cases h with
        | head => exact ⟨_, r1_z01, rfl⟩
        | tail _ h => cases h with
          | head => exact ⟨_, r1_e01, rfl⟩
          | tail _ h => cases h with
            | head => exact ⟨_, r1_z02, rfl⟩
            | tail _ h => cases h with
              | head => exact ⟨_, r1_e02, rfl⟩
              | tail _ h => cases h with
                | head => exact ⟨_, r1_s10, rfl⟩
                | tail _ h => cases h with
                  | head => exact ⟨_, r1_exit_p, rfl⟩
                  | tail _ h => cases h with
                    | head => exact ⟨_, run1_flow_above.1, rfl⟩
                    | tail _ h => cases h
    | added M a =>
      have hi := AnyTaintCases.G.inv1T h
      cases hi with
      | head => exact ⟨_, r1_ad, rfl⟩
      | tail _ h => cases h
    | req M i t => exact (AnyTaintCases.G.inv1T h).elim
    | vuln M n s d =>
      have hd : d = true := AnyTaintCases.G.inv1T h
      cases h with
      | vuln _ hs _ =>
        cases hs with
        | head => rw [hd]; exact ⟨_, run1_vuln, rfl⟩
        | tail _ hs => cases hs

#print axioms run1_forgets

/-- The same, as an equality of the runs. -/
theorem run1_forget_eq : AnyTaintExCov.forget6 R1 = AnyTaintCases.G.R1T :=
  funext fun o => propext (run1_forgets o)

#print axioms run1_forget_eq

/-! ### The hand-off of the backward run after the refined run 1

  The refined pipeline (`PipelineAnyTaintExDriver.resultSeqX`) restricts the backward run by the
  reversed summaries of run 1 read without exclusions (`forget6`); the backward run reads plain
  patterns (DESIGN A2: the hand-off drops the exclusions; here there is none). By `run1_forgets`
  that is the round-1 restriction, so the round-1 hand-off (`AnyTaintCases.G.handoff_exact`) is
  the hand-off of the refined run. -/

/-- The backward demand after the refined run 1: the reversed summaries of `forget6 R1`. -/
abbrev demBX : Dem := Backward.revSummaryDemand prog (AnyTaintExCov.forget6 R1)

/-- The hand-off of the backward run after the refined run 1. -/
abbrev HX : Dem := Backward.demOf AnyTaintCases.G.Pb (AnyTaintCases.G.BG demBX)

/-- The reversed summaries of the refined run 1 are in `AnyTaintCases.G.revDemG`. -/
theorem revDemX_bound {m : MethodId} {d : DemandEdge} (h : demBX m d) :
    (m, d) ∈ AnyTaintCases.G.revDemG := by
  have h' : Backward.revSummaryDemand prog AnyTaintCases.G.R1T m d := by
    rw [← run1_forget_eq]; exact h
  exact AnyTaintCases.G.revDemT_bound h'

#print axioms revDemX_bound

/-- The reversed FLOW summary `dRet` of `get` is a reversed summary of the refined run 1. -/
theorem revDemX_get : demBX 1 AnyTaintCases.G.dRet := by
  show Backward.revSummaryDemand prog (AnyTaintExCov.forget6 R1) 1 AnyTaintCases.G.dRet
  rw [run1_forget_eq]
  exact AnyTaintCases.G.revDemT_get

#print axioms revDemX_get

/-- THE HAND-OFF AFTER THE REFINED RUN 1 IS EXACTLY `AnyTaintCases.G.demGM`: the demand
    `dGet = ((p, [f], [any], T), some (ret, [], [any], T))` of `get` and the zero demand. -/
theorem HX_exact (m : MethodId) (d : DemandEdge) : HX m d ↔ AnyTaintCases.G.demGM m d :=
  AnyTaintCases.G.handoff_exact _ (fun _ _ h => revDemX_bound h) revDemX_get m d

#print axioms HX_exact

/-- The hand-off after the refined run 1 has THE DEMAND OF `get`. -/
theorem handoffX_get : HX 1 dGet := (HX_exact 1 dGet).mpr (Or.inr ⟨rfl, rfl⟩)

#print axioms handoffX_get

/-! ### Run 3 with must-premises and exclusions (`DRXs`): the vulnerability is CONFIRMED -/

-- THE EMISSION (`emitX`): the `[any-taint]` added fact `(p, [], [any-taint], {}, T)` against
-- `D-c = (p, [f], [any], T)` gives the MUST premise `(p, [f], [any-taint], {}, T)` (row `above`, the
-- step down `f` is admitted by the empty exclusion)
example : emitTX emitX dGet.din Ap true Excl.empty = some (Jf, true, Excl.empty) := by decide
-- a must-premise starts as itself, NORMAL
example : startX Jf true Excl.empty = JfX := by decide
-- `ret = p.f` on the must-premise: `(ret, [], [any-taint], {}, T)`, normal (case `below []`, a
-- `keep` row of `annX` with the empty exclusion: no demotion, no annotation)
example : annX JfX ⟨3, [1], st, .star⟩ Excl.empty ⟨4, [], st, .star⟩ Excl.empty =
    some (true, Excl.empty) := by decide
example : (transferX taint cnt 3 getS JfX).facts = [JfX, RETnx] := by decide
-- the restriction (`restrictX`) by `D-p = (ret, [], [any], T)` keeps it; `satX` holds
example : restrictX Jf Excl.empty RETnx dGet = some RETnx := by decide
example : satX Jf Excl.empty Ap Excl.empty = true := by decide
-- the application and the binding back: `(x, [], [any-taint], {}, T)`, normal; the sink triggers
example : (applySummaryX ApX Jf Excl.empty RETnx).facts = [RETnx] := by decide
example : (bindX RETnx bOut).facts = [Xnx] := by decide
example : limitFX cnt 3 Xnx = Xnx := by decide
example : checkX zeroFact Xnx sinkP = .triggered := by decide

/-- Run 3 of program G with the exclusion, for a demand and a record set (the spec instance
    `emitX`, `satX`, `restrictX`). -/
abbrev R3 (demand : Dem) (recs : XRecs) : XObj → Prop :=
  DRXs prog taint cnt 3 demand recs sinks [0]

section Run3
variable (demand : Dem) (recs : XRecs) (hd : demand 1 dGet)

/-- Run 3: the source edge `zero → (dto, [], [any-taint], {}, T)`, NORMAL. -/
theorem r3_e01 : R3 demand recs (.edge 0 zeroFact false Excl.empty 1 DTOx) :=
  DRX.step (DRX.start (DRX.root (List.Mem.head _))) hE00 (by decide)

/-- Run 3: the added fact of `get` is `[any-taint]` on its link (`am = true`), with the empty
    exclusion. -/
theorem r3_ad : R3 demand recs (.added 1 Ap true Excl.empty) :=
  DRX.added (c := callGet) (e := bIn) (a := ApX) (r3_e01 demand recs) hE01 (List.Mem.head _)
    (by decide)

include hd in
/-- RUN 3 (`DRXs`): the emission of the added fact `(p, [], [any-taint], {}, T)` with the demand
    `dGet` gives THE MUST PREMISE `(p, [f], [any-taint], {}, T)` of `get`. -/
theorem run3_must : R3 demand recs (.init 1 Jf true Excl.empty) :=
  DRX.initR (d := dGet) (r3_ad demand recs) hd (by decide)

#print axioms run3_must

include hd in
/-- Run 3: the start fact of the must-premise, normal. -/
theorem r3_eJ0 : R3 demand recs (.edge 1 Jf true Excl.empty 0 JfX) :=
  DRX.start (run3_must demand recs hd)

include hd in
/-- Run 3: the summary of the must-premise `(p, [f], [any-taint], {}, T) →
    (ret, [], [any-taint], {}, T)`, NORMAL. -/
theorem r3_eJ1 : R3 demand recs (.edge 1 Jf true Excl.empty 1 RETnx) :=
  DRX.step (r3_eJ0 demand recs hd) hE10 (by decide)

include hd in
/-- RUN 3 (`DRXs`): THE SINK EDGE IN `root` IS NORMAL: `zero → (x, [], [any-taint], {}, T)` at
    the sink node (the restricted summary of the must-premise, applied with `satX`). -/
theorem run3_sink_normal : R3 demand recs (.edge 0 zeroFact false Excl.empty 2 Xnx) :=
  DRX.ret (c := callGet) (e1 := bIn) (a := ApX) (j := Jf) (mj := true) (jex := Excl.empty)
    (g := RETnx) (d := dGet) (g' := RETnx) (r := RETnx) (e2 := bOut) (r' := Xnx)
    (r3_e01 demand recs) hE01 (List.Mem.head _) (by decide) (run3_must demand recs hd)
    (r3_eJ1 demand recs hd) hd (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms run3_sink_normal

include hd in
/-- Run 3 reports the vulnerability of `G` in the NORMAL layer. -/
theorem run3_vuln_normal : R3 demand recs (.vuln 0 2 sinkP false) :=
  DRX.vuln (run3_sink_normal demand recs hd) (List.Mem.head _) (by decide)

#print axioms run3_vuln_normal

include hd in
/-- The must-premise of `get` is SUPPORTED (`SupX`): the normal source edge of `root` binds the
    `[any-taint]` fact `(p, [], [any-taint], {}, T)`, and the premise `(p, [f], [any-taint], {}, T)`
    lies inside it with its mark (`SupLinkX`, the must case, `satX`). -/
theorem run3_must_supported :
    SupX prog taint cnt 3 demand emitX satX restrictX recs sinks [0] 1 Jf true Excl.empty :=
  SupX.call (c := callGet) (e := bIn) (a := ApX) (SupX.root (List.Mem.head _))
    (r3_e01 demand recs) rfl hE01 (List.Mem.head _) (by decide) rfl (run3_must demand recs hd)
    (Or.inr (Or.inr ⟨rfl, ⟨1, rfl⟩, rfl, by decide, Or.inr ⟨rfl, rfl⟩⟩))

#print axioms run3_must_supported

include hd in
/-- RUN 3 (`DRXs`) CONFIRMS PROGRAM G (`AnyTaintEx.ConfirmedX`): the normal sink edge under the
    supported zero premise of the root, with a triggered `checkX`. For every demand that has the
    demand `dGet` of `get` and every record set. -/
theorem run3_confirmed :
    ConfirmedX prog taint cnt 3 demand emitX satX restrictX recs sinks [0] 0 2 sinkP :=
  ⟨zeroFact, false, Excl.empty, Xnx, run3_sink_normal demand recs hd, SupX.root (List.Mem.head _),
    rfl, List.Mem.head _, by decide⟩

#print axioms run3_confirmed

end Run3

/-- THE REFINED ITERATION `D6X` → `DB` → `DRXs` CONFIRMS PROGRAM G: run 3 with the hand-off `HX` of
    the backward run after the refined run 1 confirms the vulnerability, for every record set. -/
theorem run3_confirmed_handoff (recs : XRecs) :
    ConfirmedX prog taint cnt 3 HX emitX satX restrictX recs sinks [0] 0 2 sinkP :=
  run3_confirmed HX recs handoffX_get

#print axioms run3_confirmed_handoff

end G

/-! ## Program C: the sink in the callee

```
root():  dto = srcAny();  use(dto);     // 0 -> 1 -> 2
use(o):  sinkAny(o.f);                  // the sink (o, [f], [any], T) at node 0 (entry = exit)
```
  The round-1 program `AnyTaintCases.C`. The demand of `use` is `dUse = (D-c = (o, [f], [any], T),
  none)` (the hand-off of the backward run, `AnyTaintCases.C.handoff_use`, for every backward
  demand and record set). Run 3 (`DRXs`) confirms the vulnerability through the must-premise
  `(o, [f], [any-taint], {}, T)` and its support link. -/

namespace C

open ApSpec.AnyTaintCases.C (prog callUse bUse sinkP sinks dUse Ao Jo hE00 hE01)

/-- The source result `(dto, [], [any-taint], {}, T)`, normal (the fact of `G`). -/
def DTOx : XFact := plain AnyTaintCases.G.DTO
/-- The added fact `(o, [], [any-taint], {}, T)` of the normal link. -/
def AoX : XFact := plain ⟨Ao, false⟩
/-- The start fact of the must-premise `(o, [f], [any-taint], {}, T)`: itself, NORMAL. -/
def JoX : XFact := plain ⟨Jo, false⟩

-- the binding gives the `[any-taint]` added fact with the empty exclusion
example : (bindX DTOx bUse).facts = [AoX] := by decide
-- the emission `emitX` gives the must-premise with the empty exclusion (row `above`)
example : emitTX emitX dUse.din Ao true Excl.empty = some (Jo, true, Excl.empty) := by decide
-- it starts as itself, normal
example : startX Jo true Excl.empty = JoX := by decide
-- the sink triggers on the NORMAL start fact of the must-premise (`checkX`: the sink pattern
-- overlaps the admitted part, here everything)
example : checkX Jo JoX sinkP = .triggered := by decide
-- the support link: the must-premise lies inside the added fact with the same mark (`satX`)
example : satX Jo Excl.empty Ao Excl.empty = true := by decide

/-- Run 3 of program C with the exclusion, for a demand and a record set. -/
abbrev R3 (demand : Dem) (recs : XRecs) : XObj → Prop :=
  DRXs prog AnyTaintCases.G.taint cnt 3 demand recs sinks [0]

section Run3
variable (demand : Dem) (recs : XRecs) (hd : demand 1 dUse)

/-- Run 3 of C: the source edge `zero → (dto, [], [any-taint], {}, T)`, NORMAL. -/
theorem c_e01 : R3 demand recs (.edge 0 zeroFact false Excl.empty 1 DTOx) :=
  DRX.step (DRX.start (DRX.root (List.Mem.head _))) hE00 (by decide)

/-- Run 3 of C: the added fact of `use` is `[any-taint]` on its link, with the empty exclusion. -/
theorem c_ad : R3 demand recs (.added 1 Ao true Excl.empty) :=
  DRX.added (c := callUse) (e := bUse) (a := AoX) (c_e01 demand recs) hE01 (List.Mem.head _)
    (by decide)

include hd in
/-- RUN 3 (`DRXs`): THE MUST-PREMISE `(o, [f], [any-taint], {}, T)` of `use`. -/
theorem run3_must : R3 demand recs (.init 1 Jo true Excl.empty) :=
  DRX.initR (d := dUse) (c_ad demand recs) hd (by decide)

#print axioms run3_must

include hd in
/-- RUN 3: THE SINK EDGE IN `use` IS NORMAL: the start fact `(o, [f], [any-taint], {}, T)` of the
    must-premise. -/
theorem run3_sink_normal : R3 demand recs (.edge 1 Jo true Excl.empty 0 JoX) :=
  DRX.start (run3_must demand recs hd)

#print axioms run3_sink_normal

include hd in
/-- Run 3 reports the vulnerability of `C` in the NORMAL layer. -/
theorem run3_vuln_normal : R3 demand recs (.vuln 1 0 sinkP false) :=
  DRX.vuln (run3_sink_normal demand recs hd) (List.Mem.head _) (by decide)

#print axioms run3_vuln_normal

include hd in
/-- THE MUST-PREMISE IS SUPPORTED THROUGH THE SUPPORT LINK (`SupX.call` with `SupLinkX`, the must
    case): `(o, [f], [any-taint], {}, T)` is a must-premise inside the normal `[any-taint]` added
    fact `(o, [], [any-taint], {}, T)` of the normal source edge of `root` (`satX`), with the same
    mark `T`. -/
theorem run3_supported :
    SupX prog AnyTaintCases.G.taint cnt 3 demand emitX satX restrictX recs sinks [0] 1 Jo true
      Excl.empty :=
  SupX.call (c := callUse) (e := bUse) (a := AoX) (SupX.root (List.Mem.head _))
    (c_e01 demand recs) rfl hE01 (List.Mem.head _) (by decide) rfl (run3_must demand recs hd)
    (Or.inr (Or.inr ⟨rfl, ⟨1, rfl⟩, rfl, by decide, Or.inr ⟨rfl, rfl⟩⟩))

#print axioms run3_supported

include hd in
/-- RUN 3 (`DRXs`) CONFIRMS PROGRAM C (`AnyTaintEx.ConfirmedX`) THROUGH A MUST-PREMISE LINK: the
    normal sink edge in `use`, under the supported must-premise `(o, [f], [any-taint], {}, T)`, with
    a triggered `checkX`. For every demand that has `dUse` and every record set. -/
theorem run3_confirmed :
    ConfirmedX prog AnyTaintCases.G.taint cnt 3 demand emitX satX restrictX recs sinks [0] 1 0
      sinkP :=
  ⟨Jo, true, Excl.empty, JoX, run3_sink_normal demand recs hd, run3_supported demand recs hd, rfl,
    List.Mem.head _, by decide⟩

#print axioms run3_confirmed

end Run3

/-- THE REFINED RUN 3 WITH THE HAND-OFF CONFIRMS PROGRAM C: the hand-off of the backward run
    (`AnyTaintCases.C.handoff_use`: it has `dUse` for every backward demand and backward record set)
    gives `ConfirmedX`, for every forward record set. -/
theorem run3_confirmed_handoff (demB : Dem) (recsB : MethodId → PFact × AFact → Prop)
    (recs : XRecs) :
    ConfirmedX prog AnyTaintCases.G.taint cnt 3
      (Backward.demOf AnyTaintCases.C.Pb (AnyTaintCases.C.BC demB recsB)) emitX satX restrictX
      recs sinks [0] 1 0 sinkP :=
  run3_confirmed _ recs (AnyTaintCases.C.handoff_use demB recsB)

#print axioms run3_confirmed_handoff

end C

/-! ## Program I: the identity callee (run 1 of `D6X` confirms)

```
root():  dto = srcAny();   // 0 -> 1
         x = id(dto);      // 1 -> 2
         sinkAny(x);       // the sink pattern (x, [], [any], T) at node 2
id(p):   return p;         // 0 -> 1: ret = p, the micro edge p.* -> ret.*
```
  The round-1 program `AnyTaintCases.I` (`G` with `return p`). The run-1 FLOW summary of `id` is
  `(p, [], *, {}, *) → (ret, [], *, {}, *)` in the normal layer; its refined application to the
  `[any-taint]` added fact `(p, [], [any-taint], {}, T)` is case `below r = []` with a `*` target
  and the empty exclusion: a `keep` row of `annX` with the empty exclusion, so the result
  `(ret, [], [any-taint], {}, T)` is NORMAL and has no annotation (`app_normal`). -/

namespace I

open ApSpec.AnyTaintCases.I (prog callId idS RETf hE00 hE01 hE10 no_clean no_filt)

def Zx : XFact := plain AnyTaintCases.G.Z
def DTOx : XFact := plain AnyTaintCases.G.DTO
def J1x : XFact := plain AnyTaintCases.G.J1f
/-- The run-1 FLOW summary conclusion `(ret, [], *, {}, *)`, normal. -/
def RETfx : XFact := plain RETf
def ApX : XFact := plain ⟨AnyTaintCases.G.Ap, false⟩
def RETnx : XFact := plain AnyTaintCases.G.RETn
/-- The sink fact `(x, [], [any-taint], {}, T)`, NORMAL. -/
def Xnx : XFact := plain AnyTaintCases.G.Xn

/-! ### Run 1 with the exclusion (`D6X`), completely -/

/-- Run 1 of program I with the exclusion: `policy1`, the field limit 3. -/
abbrev R1 : XObj6 → Prop :=
  D6X prog AnyTaintCases.G.taint cnt 3 policy1 AnyTaintCases.G.sinks [0]

def inits1 : List (MethodId × PFact) := [(0, zeroFact), (1, AnyTaintCases.G.J1)]
def edges1 : List (MethodId × PFact × Node × XFact) :=
  [(0, zeroFact, 0, Zx), (0, zeroFact, 1, Zx), (0, zeroFact, 1, DTOx), (0, zeroFact, 2, Zx),
   (0, zeroFact, 2, Xnx), (1, AnyTaintCases.G.J1, 0, J1x), (1, AnyTaintCases.G.J1, 1, J1x),
   (1, AnyTaintCases.G.J1, 1, RETfx)]
def addeds1 : List (MethodId × PFact) := [(1, AnyTaintCases.G.Ap)]
/-- The only vulnerability of run 1: `sinkAny(x)`, in the NORMAL layer. -/
def vulns1 : List (MethodId × Node × PFact × Bool) := [(0, 2, AnyTaintCases.G.sinkP, false)]

/-- Every object of the refined run 1 is in the lists; no request. -/
def Inv1 : XObj6 → Prop
  | .init M i => (M, i) ∈ inits1
  | .edge M i n f => (M, i, n, f) ∈ edges1
  | .added M a => (M, a) ∈ addeds1
  | .req _ _ _ => False
  | .vuln M n s d => (M, n, s, d) ∈ vulns1

instance : DecidablePred Inv1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s d => inferInstanceAs (Decidable ((M, n, s, d) ∈ vulns1))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM I WITH THE EXCLUSION (`D6X`): the objects of the round-1 run
    `AnyTaintCases.I.inv1T` with the empty exclusion; the only sink edge after the call is the
    NORMAL `zero → (x, [], [any-taint], {}, T)`; the only vulnerability is normal. -/
theorem inv1 {o : XObj6} (h : R1 o) : Inv1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits1,
      Inv1 (.edge x.1 x.2 (prog.entry x.1) (startX x.2 false Excl.empty))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferX AnyTaintCases.G.taint cnt 3 AnyTaintCases.G.srcS x.2.2.2).facts,
          Inv1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transferX AnyTaintCases.G.taint cnt 3 idS x.2.2.2).facts,
              Inv1 (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transferX AnyTaintCases.G.taint cnt 3 AnyTaintCases.G.srcS x.2.2.2).reqs, False)
        (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transferX AnyTaintCases.G.taint cnt 3 idS x.2.2.2).reqs, False)
            (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.af.fact.base callId.touched = false → Inv1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callId.toCallee,
          ∀ a ∈ (bindX x.2.2.2 e).facts, Inv1 (.added callId.callee a.af.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addeds1, Inv1 (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callId.toCallee, ∀ a ∈ (bindX x.2.2.2 e1).facts,
          ∀ y ∈ inits1, y.1 = 1 → applicable y.2 a.af.fact = true →
          ∀ z ∈ edges1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummaryX a y.2 Excl.empty z.2.2.2).facts,
          ∀ e2 ∈ callId.fromCallee, ∀ r' ∈ (bindX r e2).facts,
            Inv1 (.edge 0 x.2.1 2 (limitFX cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 →
        checkX x.2.1 x.2.2.2 AnyTaintCases.G.sinkP = .none ∨
          checkX x.2.1 x.2.2.2 AnyTaintCases.G.sinkP = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 →
        checkX x.2.1 x.2.2.2 AnyTaintCases.G.sinkP = .triggered →
          (0, 2, AnyTaintCases.G.sinkP, x.2.2.2.af.demand) ∈ vulns1)
        (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1

/-! ### Run 1 with the exclusion: the derivation and the theorems -/

-- THE FLOW SUMMARY OF `ret = p` IS CASE `below r = []`: `(ret, [], *, {}, *)`, normal
example : (transferX AnyTaintCases.G.taint cnt 3 idS J1x).facts = [J1x, RETfx] := by decide

/-- THE REFINED APPLICATION KEEPS THE NORMAL LAYER: the run-1 FLOW summary
    `(p, [], *, {}, *) → (ret, [], *, {}, *)` of `id` applies to the added fact `(p, [], [any], T)`
    (`applicable`); `annX` is a `keep` row with the EMPTY exclusion (`tailExcl * ∪ {}`: no
    exclusion edge meets the `.any` fact), so `applySummaryX` gives `(ret, [], [any-taint], {}, T)`
    in the NORMAL layer with no annotation; the binding back gives `(x, [], [any-taint], {}, T)`,
    normal; the field limit keeps it. -/
theorem app_normal :
    applicable AnyTaintCases.G.J1 AnyTaintCases.G.Ap = true ∧
    annX ApX AnyTaintCases.G.J1 Excl.empty RETf.fact Excl.empty = some (true, Excl.empty) ∧
    (applySummaryX ApX AnyTaintCases.G.J1 Excl.empty RETfx).facts = [RETnx] ∧
    (bindX RETnx AnyTaintCases.G.bOut).facts = [Xnx] ∧
    limitFX cnt 3 Xnx = Xnx := by decide

#print axioms app_normal

/-- Run 1: the source edge `zero → (dto, [], [any-taint], {}, T)`, NORMAL. -/
theorem r1_e01 : R1 (.edge 0 zeroFact 1 DTOx) :=
  D6X.step (D6X.start (D6X.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1: `policy1` serves the added fact `(p, [], [any], T)` with `(p, [], *, {}, *)`. -/
theorem r1_i1 : R1 (.init 1 AnyTaintCases.G.J1) := by
  have h : R1 (.init 1 (policy1 1 AnyTaintCases.G.Ap)) :=
    D6X.initA (D6X.added (c := callId) (e := AnyTaintCases.G.bIn) (a := ApX) r1_e01 hE01
      (List.Mem.head _) (by decide))
  have hp : policy1 1 AnyTaintCases.G.Ap = AnyTaintCases.G.J1 := by decide
  rw [hp] at h
  exact h

/-- Run 1 (`D6X`): THE RUN-1 FLOW SUMMARY OF `id` IS `(p, [], *, {}, *) → (ret, [], *, {}, *)` IN
    THE NORMAL LAYER (complete: a record), with the empty exclusion. -/
theorem run1_flow : R1 (.edge 1 AnyTaintCases.G.J1 1 RETfx) ∧ RETfx.af.complete = true ∧
    RETfx.ex = Excl.empty :=
  ⟨D6X.step (D6X.start r1_i1) hE10 (by decide), rfl, rfl⟩

#print axioms run1_flow

/-- Run 1 (`D6X`): the application of the FLOW summary gives THE SINK EDGE
    `zero → (x, [], [any-taint], {}, T)` IN THE NORMAL LAYER. -/
theorem run1_sink_normal : R1 (.edge 0 zeroFact 2 Xnx) :=
  D6X.ret (c := callId) (e1 := AnyTaintCases.G.bIn) (a := ApX) (j := AnyTaintCases.G.J1)
    (g := RETfx) (r := RETnx) (e2 := AnyTaintCases.G.bOut) (r' := Xnx) r1_e01 hE01
    (List.Mem.head _) (by decide) r1_i1 (by decide) run1_flow.1 (by decide) (List.Mem.head _)
    (by decide)

#print axioms run1_sink_normal

/-- Run 1 of `D6X` reports the vulnerability of program I in the NORMAL layer. -/
theorem run1_vuln_normal : R1 (.vuln 0 2 AnyTaintCases.G.sinkP false) :=
  D6X.vuln run1_sink_normal (List.Mem.head _) (by decide)

#print axioms run1_vuln_normal

/-- RUN 1 OF `D6X` CONFIRMS PROGRAM I (`AnyTaintEx.Confirmed6X`): the normal sink edge
    `zero → (x, [], [any-taint], {}, T)` under the supported zero premise of the root, with a
    triggered `checkX`. -/
theorem run1_confirmed :
    Confirmed6X prog AnyTaintCases.G.taint cnt 3 policy1 AnyTaintCases.G.sinks [0] 0 2
      AnyTaintCases.G.sinkP :=
  ⟨zeroFact, Xnx, run1_sink_normal, Sup6X.root (List.Mem.head _), rfl, List.Mem.head _, by decide⟩

#print axioms run1_confirmed

/-- Run 1 of `D6X` reports the vulnerability of program I ONLY in the normal layer (the complete
    run `inv1`). -/
theorem run1_no_demand : ¬ R1 (.vuln 0 2 AnyTaintCases.G.sinkP true) := by
  intro h
  exact absurd (inv1 h) (by decide)

#print axioms run1_no_demand

end I

/-! ## Program P: the may pass rule

```
root():  p = src();        // 0 -> 1: zero.$ -> P.$ (T)
         q = f(p);         // 1 -> 2: the micro edge P.$ (T) -> Q.[any] (T)
         sinkAny(q);       // the sink pattern (Q, [], [any], T) at node 2
```
  The round-1 program `AnyTaintCases.PassRule`: the same micro edge read as a SOURCE (a taint
  edge, `asSource`) and as a PASS RULE (not a taint edge, `asPass`). In the refined run the edge
  has an `.any` target, so `annX` gives the empty exclusion (the edge's `tex`); W6T (`w6tX`) demotes
  the pass result and drops its exclusion. -/

namespace PassRule

open ApSpec.AnyTaintCases.PassRule (prog srcP eQ qS sinkP sinks asSource asPass Pf Qn Qd hE00
  hE01 no_call no_clean no_filt)

def Zx : XFact := plain AnyTaintCases.G.Z
def Pfx : XFact := plain Pf
/-- `(Q, [], [any-taint], {}, T)`, NORMAL. -/
def Qnx : XFact := plain Qn
/-- `(Q, [], [any], T)`, DEMAND. -/
def Qdx : XFact := plain Qd

/-- THE SAME MICRO EDGE, TWO LAYERS, IN THE REFINED TRANSFER (`transferX`): as a source the result
    is `(Q, [], [any-taint], {}, T)` in the NORMAL layer; as a pass rule `w6tX` puts it in the
    DEMAND layer (`(Q, [], [any], T)`, no exclusion). -/
theorem source_vs_pass :
    (transferX asSource cnt 3 qS Pfx).facts = [Pfx, Qnx] ∧
    (transferX asPass cnt 3 qS Pfx).facts = [Pfx, Qdx] := by decide

#print axioms source_vs_pass

/-- Run 1 (`D6X`): `p = src()` gives `(P, [], $, T)` (read as a source). -/
theorem src_e01S : D6X prog asSource cnt 3 policy1 sinks [0] (.edge 0 zeroFact 1 Pfx) :=
  D6X.step (D6X.start (D6X.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1 (`D6X`): `p = src()` gives `(P, [], $, T)` (read as a pass rule). -/
theorem src_e01P : D6X prog asPass cnt 3 policy1 sinks [0] (.edge 0 zeroFact 1 Pfx) :=
  D6X.step (D6X.start (D6X.root (List.Mem.head _))) hE00 (by decide)

/-- AS A SOURCE: run 1 (`D6X`) has the NORMAL edge `zero → (Q, [], [any-taint], {}, T)`. -/
theorem source_normal : D6X prog asSource cnt 3 policy1 sinks [0] (.edge 0 zeroFact 2 Qnx) :=
  D6X.step src_e01S hE01 (by decide)

#print axioms source_normal

/-- AS A SOURCE: RUN 1 OF `D6X` CONFIRMS the vulnerability (`AnyTaintEx.Confirmed6X`): a normal
    sink edge under the zero premise. -/
theorem source_confirmed : Confirmed6X prog asSource cnt 3 policy1 sinks [0] 0 2 sinkP :=
  ⟨zeroFact, Qnx, source_normal, Sup6X.root (List.Mem.head _), rfl, List.Mem.head _, by decide⟩

#print axioms source_confirmed

/-- AS A PASS RULE: run 1 (`D6X`) has the DEMAND edge `zero → (Q, [], [any], T)`. -/
theorem pass_demand : D6X prog asPass cnt 3 policy1 sinks [0] (.edge 0 zeroFact 2 Qdx) :=
  D6X.step src_e01P hE01 (by decide)

#print axioms pass_demand

def edgesPass : List (MethodId × PFact × Node × XFact) :=
  [(0, zeroFact, 0, Zx), (0, zeroFact, 1, Zx), (0, zeroFact, 1, Pfx), (0, zeroFact, 2, Zx),
   (0, zeroFact, 2, Pfx), (0, zeroFact, 2, Qdx)]

/-- Every object of the refined pass run is in the list; no added fact, no request; every
    vulnerability is in the demand layer. -/
def InvPass : XObj6 → Prop
  | .init M i => (M, i) = (0, zeroFact)
  | .edge M i n f => (M, i, n, f) ∈ edgesPass
  | .added _ _ => False
  | .req _ _ _ => False
  | .vuln _ _ _ d => d = true

instance : DecidablePred InvPass := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) = (0, zeroFact)))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesPass))
  | .added _ _ => inferInstanceAs (Decidable False)
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ d => inferInstanceAs (Decidable (d = true))

/-- THE COMPLETE RUN 1 (`D6X`) OF PROGRAM P WITH THE PASS RULE. -/
theorem invPass {o : XObj6} (h : D6X prog asPass cnt 3 policy1 sinks [0] o) : InvPass o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    cases ih
    decide
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesPass, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferX asPass cnt 3 srcP x.2.2.2).facts, InvPass (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesPass, x.1 = 0 → x.2.2.1 = 1 →
          ∀ f' ∈ (transferX asPass cnt 3 qS x.2.2.2).facts, InvPass (.edge 0 x.2.1 2 f'))
          (0, i, 1, f) ih rfl rfl f' hf
      | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesPass, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transferX asPass cnt 3 srcP x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesPass, x.1 = 0 → x.2.2.1 = 1 →
          ∀ t ∈ (transferX asPass cnt 3 qS x.2.2.2).reqs, False) (0, i, 1, f) ih rfl rfl t ht
      | tail _ hE => cases hE
  | pass _ hE _ _ => exact (no_call hE).elim
  | added _ hE _ _ _ => exact (no_call hE).elim
  | initA _ ih => exact ih.elim
  | ret _ hE _ _ _ _ _ _ _ _ _ _ _ => exact (no_call hE).elim
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edgesPass, x.1 = 0 → x.2.2.1 = 2 →
        checkX x.2.1 x.2.2.2 sinkP = .none ∨ checkX x.2.1 x.2.2.2 sinkP = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edgesPass, x.1 = 0 → x.2.2.1 = 2 →
        checkX x.2.1 x.2.2.2 sinkP = .triggered → x.2.2.2.af.demand = true)
        (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms invPass

/-- AS A PASS RULE: run 1 of `D6X` does NOT confirm the vulnerability (a may `[any]` stays demand;
    the complete run `invPass`). -/
theorem pass_not_confirmed : ¬ Confirmed6X prog asPass cnt 3 policy1 sinks [0] 0 2 sinkP := by
  rintro ⟨i, f, hf, _, hd, hs, hc⟩
  have hv := invPass (D6X.vuln hf hs hc)
  rw [hd] at hv
  exact Bool.noConfusion hv

#print axioms pass_not_confirmed

end PassRule

/-! ## The carry-over applied to the programs (run 1)

  Programs `G`, `I` and `PassRule` satisfy the conditions of `Carry.d6x_iff_d6t`: no exclusion
  edge and no cleaner (`progFree`, by the Boolean test), and the callee summaries of the round-1
  run 1 are free (`sumFree1`, from the complete round-1 runs `AnyTaintCases.G.inv1T`,
  `AnyTaintCases.I.inv1T`; `PassRule` has no call). So their refined run 1 IS the round-1 run 1
  with the empty exclusions (`run1_carry`), and the round-1 confirmation results carry over as
  theorems (`*_carry`); they agree with the direct derivations above. (The restricted-run
  carry-over `Carry.drx_iff_drt` needs a complete base run to discharge `SumFreeR`; round 1 has
  none for `DRT`, so run 3 of `G` and `C` is derived directly above.) -/

namespace G

open ApSpec.AnyTaintCases.G (prog taint sinks sinkP)

/-- Program G has no exclusion edge and no cleaner. -/
theorem progFree : Carry.progFreeB prog = true := by decide

/-- The callee summaries of the round-1 run 1 of `G` are free. -/
theorem sumFree1 : Carry.SumFree prog AnyTaintCases.G.R1T := by
  intro M n c n' j g _ _ hg
  exact Carry.edgeFree_of_B ((by decide : ∀ x ∈ AnyTaintCases.G.edges1T, x.2.2.1 = prog.exit x.1 →
    Carry.edgeFreeB x.2.1 x.2.2.2.fact = true) (c.callee, j, prog.exit c.callee, g)
    (AnyTaintCases.G.inv1T hg) rfl)

/-- THE CARRY-OVER FOR `G` (run 1): the objects of the refined run 1 are exactly the lifts of the
    objects of the round-1 run 1 (by the generic lemma; `run1_forgets` is the direct proof). -/
theorem run1_carry (o : XObj6) : R1 o ↔ ∃ o', AnyTaintCases.G.R1T o' ∧ Carry.lift6 o' = o :=
  Carry.d6x_iff_d6t (Carry.progFree_of_B progFree).1 (Carry.progFree_of_B progFree).2 sumFree1 o

#print axioms run1_carry

/-- `run1_not_confirmed` from the round-1 result `AnyTaintCases.G.run1T_not_confirmed` by the
    carry-over. -/
theorem run1_not_confirmed_carry : ¬ Confirmed6X prog taint cnt 3 policy1 sinks [0] 0 2 sinkP :=
  fun h => AnyTaintCases.G.run1T_not_confirmed
    ((Carry.confirmed6x_iff (Carry.progFree_of_B progFree).1 (Carry.progFree_of_B progFree).2
      sumFree1 0 2 sinkP).mp h)

#print axioms run1_not_confirmed_carry

end G

namespace I

open ApSpec.AnyTaintCases.I (prog)

/-- Program I has no exclusion edge and no cleaner. -/
theorem progFree : Carry.progFreeB prog = true := by decide

/-- The callee summaries of the round-1 run 1 of `I` are free. -/
theorem sumFree1 : Carry.SumFree prog AnyTaintCases.I.R1T := by
  intro M n c n' j g _ _ hg
  exact Carry.edgeFree_of_B ((by decide : ∀ x ∈ AnyTaintCases.I.edges1T, x.2.2.1 = prog.exit x.1 →
    Carry.edgeFreeB x.2.1 x.2.2.2.fact = true) (c.callee, j, prog.exit c.callee, g)
    (AnyTaintCases.I.inv1T hg) rfl)

/-- THE CARRY-OVER FOR `I` (run 1): the refined run 1 is the round-1 run 1 with the empty
    exclusions. -/
theorem run1_carry (o : XObj6) : R1 o ↔ ∃ o', AnyTaintCases.I.R1T o' ∧ Carry.lift6 o' = o :=
  Carry.d6x_iff_d6t (Carry.progFree_of_B progFree).1 (Carry.progFree_of_B progFree).2 sumFree1 o

#print axioms run1_carry

/-- `run1_confirmed` from the round-1 result `AnyTaintCases.I.run1T_confirmed` by the carry-over. -/
theorem run1_confirmed_carry :
    Confirmed6X prog AnyTaintCases.G.taint cnt 3 policy1 AnyTaintCases.G.sinks [0] 0 2
      AnyTaintCases.G.sinkP :=
  (Carry.confirmed6x_iff (Carry.progFree_of_B progFree).1 (Carry.progFree_of_B progFree).2
    sumFree1 0 2 AnyTaintCases.G.sinkP).mpr AnyTaintCases.I.run1T_confirmed

#print axioms run1_confirmed_carry

end I

namespace PassRule

open ApSpec.AnyTaintCases.PassRule (prog sinkP sinks asSource asPass no_call)

/-- Program P has no exclusion edge and no cleaner. -/
theorem progFree : Carry.progFreeB prog = true := by decide

/-- Program P has no call: every summary condition holds. -/
theorem sumFree (R : Obj → Prop) : Carry.SumFree prog R :=
  fun _ _ _ _ _ _ hE _ _ => (no_call hE).elim

/-- THE CARRY-OVER FOR `PassRule` (run 1, both readings of the micro edge). -/
theorem run1_carry (taint : TaintEdges) (o : XObj6) :
    D6X prog taint cnt 3 policy1 sinks [0] o ↔
      ∃ o', D6T prog taint cnt 3 policy1 sinks [0] o' ∧ Carry.lift6 o' = o :=
  Carry.d6x_iff_d6t (Carry.progFree_of_B progFree).1 (Carry.progFree_of_B progFree).2
    (sumFree _) o

#print axioms run1_carry

/-- `source_confirmed` and `pass_not_confirmed` from the round-1 results by the carry-over. -/
theorem confirmed_carry :
    Confirmed6X prog asSource cnt 3 policy1 sinks [0] 0 2 sinkP ∧
    ¬ Confirmed6X prog asPass cnt 3 policy1 sinks [0] 0 2 sinkP :=
  ⟨(Carry.confirmed6x_iff (Carry.progFree_of_B progFree).1 (Carry.progFree_of_B progFree).2
      (sumFree _) 0 2 sinkP).mpr AnyTaintCases.PassRule.source_confirmed,
   fun h => AnyTaintCases.PassRule.pass_not_confirmed
    ((Carry.confirmed6x_iff (Carry.progFree_of_B progFree).1 (Carry.progFree_of_B progFree).2
      (sumFree _) 0 2 sinkP).mp h)⟩

#print axioms confirmed_carry

end PassRule

end ApSpec.AnyTaintExCases2
