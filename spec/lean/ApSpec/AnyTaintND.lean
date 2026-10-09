/-
  ApSpec.AnyTaintND — the conjunction rule for an `[any-taint]` input (decision F69/9; spec ap.md
  §4.6, §4.9, §10.6, §10.10).

  The correspondence of the base model (DESIGN §3.1): the spec tail `[any-taint]` is the
  model's `.any` tail in the NORMAL layer (every location below the position carries the mark:
  a MUST); the spec tail `[any]` is the model's `.any` tail in the demand layer (a MAY).

  Today (`ND.conjLayer`) a conjunction result is in the demand layer when an input is demand or
  when a literal does not cover its input. The NEW RULE (`conjLayerT`) keeps the result normal
  when the literal does not cover a NORMAL `.any` input: every location of that input carries the
  mark, the conjunction rule already asks that the input overlaps its literal and that it passes
  the mark gate, so the literal holds at a common location.

  Contents:
    * Part 1. `conjLayerT`, `conjFactT`; `conjLayerT_le` (the new layer is not higher than the
      old one), `conjLayerT_mono`, `conjLayerT_false` (the normal case, unfolded),
      `conjLayerT_eq` (without an `.any` input the new layer is the old one).
    * Part 2. The closures: `DNzT` (`NDZ.DNz` with `conjFactT`: THE SPEC CLOSURE) and `DNT`
      (`ND.DN` with `conjFactT`: the list model, on which the exactness is proved).
    * Part 3. THE FACT SIMULATION (`dnz_to_dnzT`, `dnzT_to_dnz`; per object `edge_dnz_dnzT`,
      `edge_dnzT_dnz`, `ninit_iffT`, `nadded_iffT`, `nreq_iffT`, `nvuln_iffT`,
      `nvuln_normal_dnz_dnzT`): `DNzT` and `DNz` have the same initial facts, added facts,
      requests and reported sinks, and the same edges (the same premise list and the same fact)
      up to the layer; the layer of a `DNzT` edge is not higher. `conj_results_corr`: a lower
      layer of a conjunction result does not change a later fact (the result has a concrete mark;
      for a concrete mark `AFact.norm` (W2), `applySummary`, `cleanRes` and `limitF` do not read
      the layer: `NDZero.Corr` and its preservation lemmas). So THE COVERAGE THEOREM
      (`nd_coverage_zT`, `nd_coverage_single_zT`, `nd_coverage_zgT`) and THE VULNERABILITY
      THEOREM (`nd_vuln_found_zT`, `nd_vuln_reach_zT`, `nd_vuln_found_zgT`) carry over.
    * Part 4. `lit_loc` (THE NEW CASE ON LOCATIONS: an `.any` input that overlaps its literal and
      passes the gate has a location in the literal); `conjFactT_corr`; the invariants of `DNT`
      (`ndInv_allT`, `ndConclusion_uncorrelatedT`, `premises_ne_nilT`) and Z0 for `DNT`
      (`zero_everywhereT`, `zero_edgeT`, `zero_calleeT`).
    * Part 5. THE EXACTNESS INVARIANT of `DNT` (`nd_edgeOKT`, `nd_edge_exact_genT`): the induction
      of `NDExact.nd_edgeOK`, copied; only the conjunction case is new (it uses `lit_loc`).
    * Part 6. Z2 for the new closures (`dnzT_to_dnT`, `dnzT_to_dnT_edge`): a normal `DNzT` edge is
      the image of a normal `DNT` edge (the proof of `NDZero.dnz_to_dn`, copied; the
      conjunction case uses `conjFactT_corr`); `premInit_zT`.
    * Part 7. THE EXACTNESS THEOREM of `DNzT` (`nd_edge_exact_zT`, `nd_edge_exact_valid_zT`), with
      the hypotheses of `NDZeroThms.nd_edge_exact_z` / `nd_edge_exact_valid_z`
      (`nd_edge_exactT`, `nd_edge_exact_validT` for `DNT`).
    * Part 8. THE CONFIRMATION of `DNzT` (`ConfirmedNzT`, `confirmedNz_vulnT`,
      `confirmed_real_NzT`, `confirmed_real_NzT_valid_of`, `confirmed_real_NzT_valid`): the proofs
      of `NDConfirmed` (for `DNT`: `SupNT`, `ConfirmedNT`, `sup_entryNT`, `sink_shapeT`,
      `confirmed_real_N_genT`, ...) and of `NDZeroThms` Part 5 (`SupNzT`, `supNz_supNT`,
      `confirmedNz_NT`), copied. Condition 1 reads COMPLETE as decision 1 says: a NORMAL sink edge,
      also with the `[any-taint]` tail (`sink_loc`: a normal `.any` sink fact has a location in
      the sink pattern). `confirmedNz_confirmedNzT`: every vulnerability that the old rule
      confirms, the new rule confirms.
    * Part 9. THE WORKED EXAMPLE (`Example`): `x = srcAny()` gives `(x, [], .any, T)` in the
      normal layer, `y = src()` gives `(y, [], $, U)`, and the conjunction
      `(x, [f], $, T) ∧ (y, [], $, U) → (z, [], $, V)`: the result is normal under `conjLayerT`
      and demand under `conjLayer` (`layer_new`, `layer_old`, `c3`, `c3z`); the support derivation
      exists (`taint_z`, `reach_z`); the vulnerability is a normal `vuln` of `DNzT` (`vuln3`),
      CONFIRMED (`confirmed`) and real (`real`); under the old rule every `vuln` at the sink is
      demand (`old_inv`, `old_vuln_demand`), so it is not confirmed (`old_not_confirmed`).

  Method (the brief, §3.2, step 2): the existing exactness induction (`NDExact.nd_edgeOK`) and
  the existing Z2 (`NDZero.dnz_to_dn`) are COPIED and adapted (only their conjunction cases
  change). A reduction to the existing theorems is not possible: the downstream edges of a
  conjunction result that only the new rule keeps normal are demand edges of `DNz`, so the
  existing theorems say nothing about them.

  No new hypothesis: every theorem has the hypotheses of the theorem of `NDZeroThms` /
  `NDConfirmed` that it extends.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.NDZeroThms

namespace ApSpec.AnyTaintND
open ApSpec ApSpec.ND ApSpec.NDZ ApSpec.NDZero ApSpec.NDExact ApSpec.NDConfirmed

/-! ## Part 1. The new layer rule -/

/-- THE NEW LAYER OF A CONJUNCTION RESULT (decision 9). The result is in the demand layer if an
    input is demand, or if a literal does not cover its input AND that input is not `.any`. A
    NORMAL `.any` input (`[any-taint]`: every location carries the mark) that overlaps its
    literal (the rule `conj` checks it) does not make the result demand. -/
def conjLayerT (cj : Conj) (f1 f2 : AFact) : Bool :=
  f1.demand || f2.demand || (!coversB cj.lit1 f1.fact && !f1.fact.kind.isAny) ||
    (!coversB cj.lit2 f2.fact && !f2.fact.kind.isAny)

/-- The conclusion of a conjunction under the new rule: the target, uncorrelated (W7). -/
def conjFactT (cj : Conj) (f1 f2 : AFact) : AFact := ⟨cj.target, conjLayerT cj f1 f2⟩

theorem bool_le6 : ∀ a b c d e g : Bool,
    DLe (a || b || (c && e) || (d && g)) (a || b || c || d) := by decide

theorem bool_mono6 : ∀ a b a' b' c d e g : Bool, DLe a a' → DLe b b' →
    DLe (a || b || (c && e) || (d && g)) (a' || b' || (c && e) || (d && g)) := by decide

/-- The new layer is not higher than the layer of `ND.conjLayer`. -/
theorem conjLayerT_le (cj : Conj) (f1 f2 : AFact) : DLe (conjLayerT cj f1 f2) (conjLayer cj f1 f2) :=
  bool_le6 _ _ _ _ _ _

#print axioms conjLayerT_le

/-- The new layer is monotone in the layers of the inputs (for the same input facts). -/
theorem conjLayerT_mono {cj : Conj} {f1 f1' f2 f2' : AFact} (h1 : f1.fact = f1'.fact)
    (h2 : f2.fact = f2'.fact) (d1 : DLe f1.demand f1'.demand) (d2 : DLe f2.demand f2'.demand) :
    DLe (conjLayerT cj f1 f2) (conjLayerT cj f1' f2') := by
  unfold conjLayerT
  rw [h1, h2]
  exact bool_mono6 _ _ _ _ _ _ _ _ d1 d2

/-- Without an `.any` input the new layer is the old one. -/
theorem conjLayerT_eq {cj : Conj} {f1 f2 : AFact} (h1 : f1.fact.kind.isAny = false)
    (h2 : f2.fact.kind.isAny = false) : conjLayerT cj f1 f2 = conjLayer cj f1 f2 := by
  unfold conjLayerT conjLayer
  rw [h1, h2]
  cases f1.demand <;> cases f2.demand <;> cases coversB cj.lit1 f1.fact <;>
    cases coversB cj.lit2 f2.fact <;> rfl

theorem isAny_eq {k : Kind} (h : k.isAny = true) : k = .any := by
  cases k with
  | star _ => cases h
  | any => rfl
  | exact => cases h

theorem and_not_false {c e : Bool} (h : (!c && !e) = false) : c = true ∨ e = true := by
  cases c <;> cases e <;> simp_all

/-- The normal case of the new rule, unfolded: both inputs are normal, and each input is covered
    by its literal or has the `.any` tail. -/
theorem conjLayerT_false {cj : Conj} {f1 f2 : AFact} (h : conjLayerT cj f1 f2 = false) :
    f1.demand = false ∧ f2.demand = false ∧
      (coversB cj.lit1 f1.fact = true ∨ f1.fact.kind = .any) ∧
      (coversB cj.lit2 f2.fact = true ∨ f2.fact.kind = .any) := by
  have hd' : (f1.demand || f2.demand || (!coversB cj.lit1 f1.fact && !f1.fact.kind.isAny) ||
      (!coversB cj.lit2 f2.fact && !f2.fact.kind.isAny)) = false := h
  obtain ⟨hd'', hcv2⟩ := Exact.or_eq_false hd'
  obtain ⟨hd''', hcv1⟩ := Exact.or_eq_false hd''
  obtain ⟨hd1, hd2⟩ := Exact.or_eq_false hd'''
  refine ⟨hd1, hd2, ?_, ?_⟩
  · rcases and_not_false hcv1 with h1 | h1
    · exact .inl h1
    · exact .inr (isAny_eq h1)
  · rcases and_not_false hcv2 with h1 | h1
    · exact .inl h1
    · exact .inr (isAny_eq h1)

#print axioms conjLayerT_false

/-- THE LOWER LAYER OF A CONJUNCTION RESULT DOES NOT CHANGE A LATER FACT. The results of the old
    and of the new rule are the same fact with a concrete mark (`NProg.WF.target`), so they
    CORRESPOND (`NDZero.Corr`: the same fact, and the same layer or a concrete mark). Every AP
    operation keeps the correspondence (`NDZero.applyEdge_corr`, `transfer_corr`, `cleanRes_corr`,
    `applySummary_corr`, `limitF_corr`): an input with a concrete mark gives results with a
    concrete mark, and for a concrete mark the normal form `AFact.norm` (W2) does not read the
    layer. `dnz_to_dnzT` / `dnzT_to_dnz` carry this through every rule. -/
theorem conj_results_corr {cj : Conj} (hT : ∃ T, cj.target.mark = .conc T) (f1 f2 : AFact) :
    Corr (conjFact cj f1 f2) (conjFactT cj f1 f2) ∧
      DLe (conjFactT cj f1 f2).demand (conjFact cj f1 f2).demand :=
  ⟨⟨rfl, .inr hT⟩, conjLayerT_le cj f1 f2⟩

#print axioms conj_results_corr

/-! ## Part 2. The closures -/

/-- `DNzT`: THE ND CLOSURE OF THE SPEC WITH THE NEW CONJUNCTION RULE. The rules of `NDZ.DNz`
    (the zero-drop at `conj` and `ndRet`), with `conjFactT` at `conj`. -/
inductive DNzT (X : Ctx) : NObj → Prop where
  | root {M} : M ∈ X.roots → DNzT X (.ninit M zeroFact)
  | start {M i} : DNzT X (.ninit M i) → DNzT X (.nedge M [i] (X.Q.prog.entry M) (startFact i))
  | step {M P n f n' s f'} :
      DNzT X (.nedge M P n f) → (M, n, Instr.stmt s, n') ∈ X.Q.prog.edges →
      f' ∈ (transfer X.counted X.FL s f).facts → DNzT X (.nedge M P n' f')
  | reqStmt {M i n f n' s t} :
      DNzT X (.nedge M [i] n f) → (M, n, Instr.stmt s, n') ∈ X.Q.prog.edges →
      t ∈ (transfer X.counted X.FL s f).reqs → DNzT X (.nreq M i t)
  | pass {M P n f n' c} :
      DNzT X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      memB f.fact.base c.touched = false → DNzT X (.nedge M P n' f)
  | added {M P n f n' c e a} :
      DNzT X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → DNzT X (.nadded c.callee a.fact)
  | initA {m a} : DNzT X (.nadded m a) → DNzT X (.ninit m (X.α m a))
  -- a single-premise callee summary keeps the premise list of the caller edge
  | ret {M P n f n' c e1 a j g r e2 r'} :
      DNzT X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DNzT X (.ninit c.callee j) → applicable j a.fact = true →
      DNzT X (.nedge c.callee [j] (X.Q.prog.exit c.callee) g) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DNzT X (.nedge M P n' (limitF X.counted X.FL r'))
  -- an ND callee summary (two or more premises) opens a standing partial match at a call
  | ndOpen {M n c n' Pc g} :
      (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      DNzT X (.nedge c.callee Pc (X.Q.prog.exit c.callee) g) → 2 ≤ Pc.length →
      DNzT X (.npart M n c n' Pc [] g)
  -- one caller edge whose binding satisfies the next callee premise; its layer joins the
  -- layer of the partial match (the result is demand if a caller edge or the summary is)
  | ndBind {M n c n' p ps P g Pf f e1 a} :
      DNzT X (.npart M n c n' (p :: ps) P g) → DNzT X (.nedge M Pf n f) →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts → applicable p a.fact = true →
      DNzT X (.npart M n c n' ps (P ++ Pf) ⟨g.fact, g.demand || a.demand⟩)
  -- every callee premise is matched: the conclusion is used as it is (no delta), bound back; the joined caller
  -- premise lists drop the zero fact (spec §4.6)
  | ndRet {M n c n' P g e2 r} :
      DNzT X (.npart M n c n' [] P g) → e2 ∈ c.fromCallee →
      r ∈ (applyEdge g e2.1 e2.2).facts → DNzT X (.nedge M (dropZ P) n' (limitF X.counted X.FL r))
  | reqSink {M i n f s t} :
      DNzT X (.nedge M [i] n f) → (M, n, s) ∈ X.sinks → check i f s = .request t →
      DNzT X (.nreq M i t)
  | answer {M i t a} :
      DNzT X (.nreq M i t) → DNzT X (.nadded M a) → a.mark = .conc t →
      overlapB a i = true → DNzT X (.ninit M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      DNzT X (.nreq m j t) → DNzT X (.nedge M [ic] n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → DNzT X (.nreq M ic t)
  -- the sink check reads the mark of a premise only for a mark-abstract conclusion; an ND
  -- conclusion has a concrete mark, so the choice of the premise does not matter
  | vuln {M P n f s i} :
      DNzT X (.nedge M P n f) → (M, n, s) ∈ X.sinks → i ∈ P → check i f s = .triggered →
      DNzT X (.nvuln M n s f.demand)
  | clean {M P n f n' cl f'} :
      DNzT X (.nedge M P n f) → (M, n, Instr.clean cl, n') ∈ X.Q.prog.edges →
      f' ∈ (cleanRes cl f).facts → DNzT X (.nedge M P n' f')
  | reqClean {M i n f n' cl t} :
      DNzT X (.nedge M [i] n f) → (M, n, Instr.clean cl, n') ∈ X.Q.prog.edges →
      t ∈ (cleanRes cl f).reqs → DNzT X (.nreq M i t)
  | filt {M P n f n' b may} :
      DNzT X (.nedge M P n f) → (M, n, Instr.filt b may, n') ∈ X.Q.prog.edges →
      (f.fact.base = b → may f.fact.path = true) → DNzT X (.nedge M P n' f)
  -- the conjunction: one edge per literal; the premise lists are joined WITHOUT the zero fact (spec §4.6)
  | conj {M P1 n f1 P2 f2 cj n'} :
      DNzT X (.nedge M P1 n f1) → DNzT X (.nedge M P2 n f2) → (M, n, cj, n') ∈ X.Q.conjs →
      overlapB f1.fact cj.lit1 = true → markGate cj.lit1.mark f1.fact.mark = .ok →
      overlapB f2.fact cj.lit2 = true → markGate cj.lit2.mark f2.fact.mark = .ok →
      DNzT X (.nedge M (dropZ (P1 ++ P2)) n' (conjFactT cj f1 f2))
  -- a literal on a mark-abstract fact raises the request of the literal mark (run 1)
  | reqConj {M i n f cj n' lit t} :
      DNzT X (.nedge M [i] n f) → (M, n, cj, n') ∈ X.Q.conjs → (lit = cj.lit1 ∨ lit = cj.lit2) →
      overlapB f.fact lit = true → markGate lit.mark f.fact.mark = .req t → DNzT X (.nreq M i t)

/-- `DNT`: the list model `ND.DN` with the new conjunction layer (`conjFactT`). An auxiliary
    closure: the exactness invariant is proved on it, as `NDExact` does on `ND.DN`. -/
inductive DNT (X : Ctx) : NObj → Prop where
  | root {M} : M ∈ X.roots → DNT X (.ninit M zeroFact)
  | start {M i} : DNT X (.ninit M i) → DNT X (.nedge M [i] (X.Q.prog.entry M) (startFact i))
  | step {M P n f n' s f'} :
      DNT X (.nedge M P n f) → (M, n, Instr.stmt s, n') ∈ X.Q.prog.edges →
      f' ∈ (transfer X.counted X.FL s f).facts → DNT X (.nedge M P n' f')
  | reqStmt {M i n f n' s t} :
      DNT X (.nedge M [i] n f) → (M, n, Instr.stmt s, n') ∈ X.Q.prog.edges →
      t ∈ (transfer X.counted X.FL s f).reqs → DNT X (.nreq M i t)
  | pass {M P n f n' c} :
      DNT X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      memB f.fact.base c.touched = false → DNT X (.nedge M P n' f)
  | added {M P n f n' c e a} :
      DNT X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → DNT X (.nadded c.callee a.fact)
  | initA {m a} : DNT X (.nadded m a) → DNT X (.ninit m (X.α m a))
  -- a single-premise callee summary keeps the premise list of the caller edge
  | ret {M P n f n' c e1 a j g r e2 r'} :
      DNT X (.nedge M P n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DNT X (.ninit c.callee j) → applicable j a.fact = true →
      DNT X (.nedge c.callee [j] (X.Q.prog.exit c.callee) g) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DNT X (.nedge M P n' (limitF X.counted X.FL r'))
  -- an ND callee summary (two or more premises) opens a standing partial match at a call
  | ndOpen {M n c n' Pc g} :
      (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      DNT X (.nedge c.callee Pc (X.Q.prog.exit c.callee) g) → 2 ≤ Pc.length →
      DNT X (.npart M n c n' Pc [] g)
  -- one caller edge whose binding satisfies the next callee premise; its layer joins the
  -- layer of the partial match (the result is demand if a caller edge or the summary is)
  | ndBind {M n c n' p ps P g Pf f e1 a} :
      DNT X (.npart M n c n' (p :: ps) P g) → DNT X (.nedge M Pf n f) →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts → applicable p a.fact = true →
      DNT X (.npart M n c n' ps (P ++ Pf) ⟨g.fact, g.demand || a.demand⟩)
  -- every callee premise is matched: the conclusion is used as it is (no delta), bound back
  | ndRet {M n c n' P g e2 r} :
      DNT X (.npart M n c n' [] P g) → e2 ∈ c.fromCallee →
      r ∈ (applyEdge g e2.1 e2.2).facts → DNT X (.nedge M P n' (limitF X.counted X.FL r))
  | reqSink {M i n f s t} :
      DNT X (.nedge M [i] n f) → (M, n, s) ∈ X.sinks → check i f s = .request t →
      DNT X (.nreq M i t)
  | answer {M i t a} :
      DNT X (.nreq M i t) → DNT X (.nadded M a) → a.mark = .conc t →
      overlapB a i = true → DNT X (.ninit M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      DNT X (.nreq m j t) → DNT X (.nedge M [ic] n f) → (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      climbsB a.fact.mark t = true → overlapB a.fact j = true → DNT X (.nreq M ic t)
  -- the sink check reads the mark of a premise only for a mark-abstract conclusion; an ND
  -- conclusion has a concrete mark, so the choice of the premise does not matter
  | vuln {M P n f s i} :
      DNT X (.nedge M P n f) → (M, n, s) ∈ X.sinks → i ∈ P → check i f s = .triggered →
      DNT X (.nvuln M n s f.demand)
  | clean {M P n f n' cl f'} :
      DNT X (.nedge M P n f) → (M, n, Instr.clean cl, n') ∈ X.Q.prog.edges →
      f' ∈ (cleanRes cl f).facts → DNT X (.nedge M P n' f')
  | reqClean {M i n f n' cl t} :
      DNT X (.nedge M [i] n f) → (M, n, Instr.clean cl, n') ∈ X.Q.prog.edges →
      t ∈ (cleanRes cl f).reqs → DNT X (.nreq M i t)
  | filt {M P n f n' b may} :
      DNT X (.nedge M P n f) → (M, n, Instr.filt b may, n') ∈ X.Q.prog.edges →
      (f.fact.base = b → may f.fact.path = true) → DNT X (.nedge M P n' f)
  -- the conjunction: one edge per literal; the premise lists are concatenated
  | conj {M P1 n f1 P2 f2 cj n'} :
      DNT X (.nedge M P1 n f1) → DNT X (.nedge M P2 n f2) → (M, n, cj, n') ∈ X.Q.conjs →
      overlapB f1.fact cj.lit1 = true → markGate cj.lit1.mark f1.fact.mark = .ok →
      overlapB f2.fact cj.lit2 = true → markGate cj.lit2.mark f2.fact.mark = .ok →
      DNT X (.nedge M (P1 ++ P2) n' (conjFactT cj f1 f2))
  -- a literal on a mark-abstract fact raises the request of the literal mark (run 1)
  | reqConj {M i n f cj n' lit t} :
      DNT X (.nedge M [i] n f) → (M, n, cj, n') ∈ X.Q.conjs → (lit = cj.lit1 ∨ lit = cj.lit2) →
      overlapB f.fact lit = true → markGate lit.mark f.fact.mark = .req t → DNT X (.nreq M i t)

/-! ## Part 3. The fact simulation `DNz` ↔ `DNzT` -/

section Sim
variable {X : Ctx}

/-- The motive of the simulation `DNz → DNzT`. The initial facts, added facts and requests are
    the same; a `vuln` has a `DNzT` image whose layer is not higher; an edge keyed by `P` has a
    `DNzT` image keyed by `P` with the corresponding fact (`NDZero.Corr`: the same fact, and the
    same layer or a concrete mark) and a layer that is not higher; the same for a partial
    match. Also the invariant that the simulation needs: an edge with two or more premises and a
    partial match have a concrete mark. -/
def SimZT (X : Ctx) : NObj → Prop
  | .ninit M i => DNzT X (.ninit M i)
  | .nadded M a => DNzT X (.nadded M a)
  | .nreq M i t => DNzT X (.nreq M i t)
  | .nvuln M n s b => ∃ b', DNzT X (.nvuln M n s b') ∧ DLe b' b
  | .nedge M P n f => (2 ≤ P.length → ∃ t, f.fact.mark = .conc t) ∧
      ∃ f', DNzT X (.nedge M P n f') ∧ Corr f f' ∧ DLe f'.demand f.demand
  | .npart M n c n' rest P g => (∃ t, g.fact.mark = .conc t) ∧
      ∃ g', DNzT X (.npart M n c n' rest P g') ∧ Corr g g' ∧ DLe g'.demand g.demand

/-- The motive of the simulation `DNzT → DNz` (the same form; the `DNz` image has a layer that
    is not lower). -/
def SimTZ (X : Ctx) : NObj → Prop
  | .ninit M i => DNz X (.ninit M i)
  | .nadded M a => DNz X (.nadded M a)
  | .nreq M i t => DNz X (.nreq M i t)
  | .nvuln M n s b => ∃ b', DNz X (.nvuln M n s b') ∧ DLe b b'
  | .nedge M P n f => (2 ≤ P.length → ∃ t, f.fact.mark = .conc t) ∧
      ∃ f', DNz X (.nedge M P n f') ∧ Corr f f' ∧ DLe f.demand f'.demand
  | .npart M n c n' rest P g => (∃ t, g.fact.mark = .conc t) ∧
      ∃ g', DNz X (.npart M n c n' rest P g') ∧ Corr g g' ∧ DLe g.demand g'.demand

/-- The summary chain keeps a concrete mark of the caller edge. -/
theorem ret_mark_conc {counted : Acc → Bool} {FL : Nat} {f a r r' : AFact} {fr to j : PFact}
    {g : AFact} {fr2 to2 : PFact} {t : Mark} (h1 : f.fact.mark = .conc t)
    (ha : a ∈ (applyEdge f fr to).facts) (hr : r ∈ (applySummary a j g).facts)
    (hr' : r' ∈ (applyEdge r fr2 to2).facts) :
    ∃ t', (limitF counted FL r').fact.mark = .conc t' := by
  obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
  obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
  obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
  exact ⟨t4, by rw [limitF_mark]; exact h4⟩

/-- THE FACT SIMULATION, `DNz → DNzT`. Every object of `DNz` is an object of `DNzT`; an edge
    (a partial match) of `DNz` keyed by `P` gives an edge (a partial match) of `DNzT` keyed by
    the same `P`, with the same fact and a layer that is NOT HIGHER. A lower layer of a
    conjunction result does not change a later fact: the result has a concrete mark, and the AP
    operations do not read the layer of a concrete-mark fact (`NDZero.Corr`). -/
theorem dnz_to_dnzT (hwf : X.Q.WF) {o : NObj} (h : DNz X o) : SimZT X o := by
  induction h with
  | root hM => exact DNzT.root hM
  | @start M i _ ih =>
    exact ⟨fun h2 => absurd h2 (Nat.not_succ_le_self 1), startFact i, DNzT.start ih,
      corr_refl _, DLe.refl _⟩
  | step _ he hf ih =>
    obtain ⟨hc2, f', hD, hc, hd⟩ := ih
    obtain ⟨r', hr', hk⟩ := transfer_corr hc hf
    exact ⟨fun h2 => let ⟨_, ht⟩ := hc2 h2; transfer_mark_conc ht hf, r', DNzT.step hD he hr',
      hk.1, hk.2.2 hd⟩
  | reqStmt _ he hq ih =>
    obtain ⟨_, f', hD, hc, _⟩ := ih
    exact DNzT.reqStmt hD he (by rw [← transfer_reqs_corr hc.1]; exact hq)
  | pass _ he hm ih =>
    obtain ⟨hc2, f', hD, hc, hd⟩ := ih
    exact ⟨hc2, f', DNzT.pass hD he (by rw [← hc.1]; exact hm), hc, hd⟩
  | added _ he he1 ha ih =>
    obtain ⟨_, f', hD, hc, _⟩ := ih
    obtain ⟨a', ha', hk⟩ := applyEdge_corr hc ha
    have h2 := DNzT.added hD he he1 ha'
    rw [← hk.1.1] at h2
    exact h2
  | initA _ ih => exact DNzT.initA ih
  | ret _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    obtain ⟨hc2, f', hD, hc, hd⟩ := ihf
    obtain ⟨_, g', hG, hcg, hdg⟩ := ihg
    obtain ⟨a', ha', hka⟩ := applyEdge_corr hc ha
    obtain ⟨r'', hr'', hcr, _, hdr⟩ := applySummary_corr hka.1 hcg hr
    obtain ⟨q, hq, hkq⟩ := applyEdge_corr hcr hr'
    obtain ⟨hl, _, hl3⟩ := limitF_corr X.counted X.FL hkq.1
    exact ⟨fun h2 => let ⟨_, ht⟩ := hc2 h2; ret_mark_conc ht ha hr hr', _,
      DNzT.ret hD he he1 ha' ihj (by rw [← hka.1.1]; exact hap) hG hr'' he2 hq, hl,
      hl3 (hkq.2.2 (hdr (hka.2.2 hd) hdg))⟩
  | @ndOpen M n c n' Pc g he _ h2 ih =>
    obtain ⟨hc2, g', hG, hcg, hdg⟩ := ih
    exact ⟨hc2 h2, g', DNzT.ndOpen he hG h2, hcg, hdg⟩
  | ndBind _ _ he1 ha hap ihp ihf =>
    obtain ⟨⟨T, hT⟩, g', hpart, hcg, hdg⟩ := ihp
    obtain ⟨_, f', hD, hc, hd⟩ := ihf
    obtain ⟨a', ha', hka⟩ := applyEdge_corr hc ha
    exact ⟨⟨T, hT⟩, _, DNzT.ndBind hpart hD he1 ha' (by rw [← hka.1.1]; exact hap),
      ⟨hcg.1, .inr ⟨T, hT⟩⟩, DLe.or hdg (hka.2.2 hd)⟩
  | ndRet _ he2 hr ih =>
    obtain ⟨⟨T, hT⟩, g', hpart, hcg, hdg⟩ := ih
    obtain ⟨r', hr', hkr⟩ := applyEdge_corr hcg hr
    obtain ⟨hl, _, hl3⟩ := limitF_corr X.counted X.FL hkr.1
    refine ⟨fun _ => ?_, _, DNzT.ndRet hpart he2 hr', hl, hl3 (hkr.2.2 hdg)⟩
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc hT hr
    exact ⟨t1, by rw [limitF_mark]; exact h1⟩
  | reqSink _ hs hc ih =>
    obtain ⟨_, f', hD, hcf, _⟩ := ih
    exact DNzT.reqSink hD hs (by rw [← check_corr hcf.1]; exact hc)
  | answer _ _ hm hov ihr iha => exact DNzT.answer ihr iha hm hov
  | reqUp _ _ he hcm he1 ha hcl hov ihr ihf =>
    obtain ⟨_, f', hD, hcf, _⟩ := ihf
    obtain ⟨a', ha', hka⟩ := applyEdge_corr hcf ha
    exact DNzT.reqUp ihr hD he hcm he1 ha' (by rw [← hka.1.1]; exact hcl)
      (by rw [← hka.1.1]; exact hov)
  | vuln _ hs hi hc ih =>
    obtain ⟨_, f', hD, hcf, hd⟩ := ih
    exact ⟨_, DNzT.vuln hD hs hi (by rw [← check_corr hcf.1]; exact hc), hd⟩
  | clean _ he hf ih =>
    obtain ⟨hc2, f', hD, hc, hd⟩ := ih
    obtain ⟨r', hr', hk⟩ := cleanRes_corr hc hf
    exact ⟨fun h2 => let ⟨_, ht⟩ := hc2 h2; cleanRes_mark_conc ht hf, r', DNzT.clean hD he hr',
      hk.1, hk.2.2 hd⟩
  | reqClean _ he hq ih =>
    obtain ⟨_, f', hD, hc, _⟩ := ih
    exact DNzT.reqClean hD he (by rw [← cleanRes_reqs_corr hc.1]; exact hq)
  | filt _ he hm ih =>
    obtain ⟨hc2, f', hD, hc, hd⟩ := ih
    exact ⟨hc2, f', DNzT.filt hD he (by rw [← hc.1]; exact hm), hc, hd⟩
  | @conj M P1 n f1 P2 f2 cj n' _ _ hcj ho1 hg1 ho2 hg2 ih1 ih2 =>
    obtain ⟨_, f1', hD1, hc1, hd1⟩ := ih1
    obtain ⟨_, f2', hD2, hc2, hd2⟩ := ih2
    obtain ⟨T, hT⟩ := (hwf.target _ _ _ _ hcj).1
    refine ⟨fun _ => ⟨T, hT⟩, _, DNzT.conj hD1 hD2 hcj (by rw [← hc1.1]; exact ho1)
      (by rw [← hc1.1]; exact hg1) (by rw [← hc2.1]; exact ho2) (by rw [← hc2.1]; exact hg2),
      ⟨rfl, .inr ⟨T, hT⟩⟩, ?_⟩
    show DLe (conjLayerT cj f1' f2') (conjLayer cj f1 f2)
    exact fun h => conjLayerT_le cj f1 f2 (conjLayerT_mono hc1.1.symm hc2.1.symm hd1 hd2 h)
  | reqConj _ hcj hlit ho hg ih =>
    obtain ⟨_, f', hD, hc, _⟩ := ih
    exact DNzT.reqConj hD hcj hlit (by rw [← hc.1]; exact ho) (by rw [← hc.1]; exact hg)

#print axioms dnz_to_dnzT

/-- THE FACT SIMULATION, `DNzT → DNz`. Every object of `DNzT` is an object of `DNz`; an edge
    (a partial match) of `DNzT` keyed by `P` gives an edge (a partial match) of `DNz` keyed by
    the same `P`, with the same fact and a layer that is NOT LOWER. -/
theorem dnzT_to_dnz (hwf : X.Q.WF) {o : NObj} (h : DNzT X o) : SimTZ X o := by
  induction h with
  | root hM => exact DNz.root hM
  | @start M i _ ih =>
    exact ⟨fun h2 => absurd h2 (Nat.not_succ_le_self 1), startFact i, DNz.start ih,
      corr_refl _, DLe.refl _⟩
  | step _ he hf ih =>
    obtain ⟨hc2, f', hD, hc, hd⟩ := ih
    obtain ⟨r', hr', hk⟩ := transfer_corr hc hf
    exact ⟨fun h2 => let ⟨_, ht⟩ := hc2 h2; transfer_mark_conc ht hf, r', DNz.step hD he hr',
      hk.1, hk.2.1 hd⟩
  | reqStmt _ he hq ih =>
    obtain ⟨_, f', hD, hc, _⟩ := ih
    exact DNz.reqStmt hD he (by rw [← transfer_reqs_corr hc.1]; exact hq)
  | pass _ he hm ih =>
    obtain ⟨hc2, f', hD, hc, hd⟩ := ih
    exact ⟨hc2, f', DNz.pass hD he (by rw [← hc.1]; exact hm), hc, hd⟩
  | added _ he he1 ha ih =>
    obtain ⟨_, f', hD, hc, _⟩ := ih
    obtain ⟨a', ha', hk⟩ := applyEdge_corr hc ha
    have h2 := DNz.added hD he he1 ha'
    rw [← hk.1.1] at h2
    exact h2
  | initA _ ih => exact DNz.initA ih
  | ret _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    obtain ⟨hc2, f', hD, hc, hd⟩ := ihf
    obtain ⟨_, g', hG, hcg, hdg⟩ := ihg
    obtain ⟨a', ha', hka⟩ := applyEdge_corr hc ha
    obtain ⟨r'', hr'', hcr, hdr, _⟩ := applySummary_corr hka.1 hcg hr
    obtain ⟨q, hq, hkq⟩ := applyEdge_corr hcr hr'
    obtain ⟨hl, hl2, _⟩ := limitF_corr X.counted X.FL hkq.1
    exact ⟨fun h2 => let ⟨_, ht⟩ := hc2 h2; ret_mark_conc ht ha hr hr', _,
      DNz.ret hD he he1 ha' ihj (by rw [← hka.1.1]; exact hap) hG hr'' he2 hq, hl,
      hl2 (hkq.2.1 (hdr (hka.2.1 hd) hdg))⟩
  | @ndOpen M n c n' Pc g he _ h2 ih =>
    obtain ⟨hc2, g', hG, hcg, hdg⟩ := ih
    exact ⟨hc2 h2, g', DNz.ndOpen he hG h2, hcg, hdg⟩
  | ndBind _ _ he1 ha hap ihp ihf =>
    obtain ⟨⟨T, hT⟩, g', hpart, hcg, hdg⟩ := ihp
    obtain ⟨_, f', hD, hc, hd⟩ := ihf
    obtain ⟨a', ha', hka⟩ := applyEdge_corr hc ha
    exact ⟨⟨T, hT⟩, _, DNz.ndBind hpart hD he1 ha' (by rw [← hka.1.1]; exact hap),
      ⟨hcg.1, .inr ⟨T, hT⟩⟩, DLe.or hdg (hka.2.1 hd)⟩
  | ndRet _ he2 hr ih =>
    obtain ⟨⟨T, hT⟩, g', hpart, hcg, hdg⟩ := ih
    obtain ⟨r', hr', hkr⟩ := applyEdge_corr hcg hr
    obtain ⟨hl, hl2, _⟩ := limitF_corr X.counted X.FL hkr.1
    refine ⟨fun _ => ?_, _, DNz.ndRet hpart he2 hr', hl, hl2 (hkr.2.1 hdg)⟩
    obtain ⟨t1, h1⟩ := applyEdge_mark_conc hT hr
    exact ⟨t1, by rw [limitF_mark]; exact h1⟩
  | reqSink _ hs hc ih =>
    obtain ⟨_, f', hD, hcf, _⟩ := ih
    exact DNz.reqSink hD hs (by rw [← check_corr hcf.1]; exact hc)
  | answer _ _ hm hov ihr iha => exact DNz.answer ihr iha hm hov
  | reqUp _ _ he hcm he1 ha hcl hov ihr ihf =>
    obtain ⟨_, f', hD, hcf, _⟩ := ihf
    obtain ⟨a', ha', hka⟩ := applyEdge_corr hcf ha
    exact DNz.reqUp ihr hD he hcm he1 ha' (by rw [← hka.1.1]; exact hcl)
      (by rw [← hka.1.1]; exact hov)
  | vuln _ hs hi hc ih =>
    obtain ⟨_, f', hD, hcf, hd⟩ := ih
    exact ⟨_, DNz.vuln hD hs hi (by rw [← check_corr hcf.1]; exact hc), hd⟩
  | clean _ he hf ih =>
    obtain ⟨hc2, f', hD, hc, hd⟩ := ih
    obtain ⟨r', hr', hk⟩ := cleanRes_corr hc hf
    exact ⟨fun h2 => let ⟨_, ht⟩ := hc2 h2; cleanRes_mark_conc ht hf, r', DNz.clean hD he hr',
      hk.1, hk.2.1 hd⟩
  | reqClean _ he hq ih =>
    obtain ⟨_, f', hD, hc, _⟩ := ih
    exact DNz.reqClean hD he (by rw [← cleanRes_reqs_corr hc.1]; exact hq)
  | filt _ he hm ih =>
    obtain ⟨hc2, f', hD, hc, hd⟩ := ih
    exact ⟨hc2, f', DNz.filt hD he (by rw [← hc.1]; exact hm), hc, hd⟩
  | @conj M P1 n f1 P2 f2 cj n' _ _ hcj ho1 hg1 ho2 hg2 ih1 ih2 =>
    obtain ⟨_, f1', hD1, hc1, hd1⟩ := ih1
    obtain ⟨_, f2', hD2, hc2, hd2⟩ := ih2
    obtain ⟨T, hT⟩ := (hwf.target _ _ _ _ hcj).1
    refine ⟨fun _ => ⟨T, hT⟩, _, DNz.conj hD1 hD2 hcj (by rw [← hc1.1]; exact ho1)
      (by rw [← hc1.1]; exact hg1) (by rw [← hc2.1]; exact ho2) (by rw [← hc2.1]; exact hg2),
      ⟨rfl, .inr ⟨T, hT⟩⟩, ?_⟩
    show DLe (conjLayerT cj f1 f2) (conjLayer cj f1' f2')
    exact fun h => conjLayerT_le cj f1' f2' (conjLayerT_mono hc1.1 hc2.1 hd1 hd2 h)
  | reqConj _ hcj hlit ho hg ih =>
    obtain ⟨_, f', hD, hc, _⟩ := ih
    exact DNz.reqConj hD hcj hlit (by rw [← hc.1]; exact ho) (by rw [← hc.1]; exact hg)

#print axioms dnzT_to_dnz

/-- The simulation per edge, `DNz → DNzT`: the same premise list, the same fact, a layer that
    is not higher. So every normal edge of `DNz` is a normal edge of `DNzT`. -/
theorem edge_dnz_dnzT (hwf : X.Q.WF) {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (h : DNz X (.nedge M P n f)) :
    ∃ f', DNzT X (.nedge M P n f') ∧ f'.fact = f.fact ∧ (f.demand = false → f'.demand = false) := by
  obtain ⟨_, f', hD, hc, hd⟩ := dnz_to_dnzT hwf h
  refine ⟨f', hD, hc.1.symm, fun h0 => ?_⟩
  cases hb : f'.demand with
  | false => rfl
  | true =>
    have h1 := hd hb
    rw [h0] at h1
    exact absurd h1 Bool.false_ne_true

/-- The simulation per edge, `DNzT → DNz`: the same premise list, the same fact, a layer that
    is not lower. -/
theorem edge_dnzT_dnz (hwf : X.Q.WF) {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (h : DNzT X (.nedge M P n f)) :
    ∃ f', DNz X (.nedge M P n f') ∧ f'.fact = f.fact ∧ (f'.demand = false → f.demand = false) := by
  obtain ⟨_, f', hD, hc, hd⟩ := dnzT_to_dnz hwf h
  refine ⟨f', hD, hc.1.symm, fun h0 => ?_⟩
  cases hb : f.demand with
  | false => rfl
  | true =>
    have h1 := hd hb
    rw [h0] at h1
    exact absurd h1 Bool.false_ne_true

/-- The initial facts, the added facts and the requests of `DNzT` and `DNz` are the same. -/
theorem ninit_iffT (hwf : X.Q.WF) {M : MethodId} {i : PFact} :
    DNzT X (.ninit M i) ↔ DNz X (.ninit M i) :=
  ⟨fun h => dnzT_to_dnz hwf h, fun h => dnz_to_dnzT hwf h⟩

theorem nadded_iffT (hwf : X.Q.WF) {M : MethodId} {a : PFact} :
    DNzT X (.nadded M a) ↔ DNz X (.nadded M a) :=
  ⟨fun h => dnzT_to_dnz hwf h, fun h => dnz_to_dnzT hwf h⟩

theorem nreq_iffT (hwf : X.Q.WF) {M : MethodId} {i : PFact} {t : Mark} :
    DNzT X (.nreq M i t) ↔ DNz X (.nreq M i t) :=
  ⟨fun h => dnzT_to_dnz hwf h, fun h => dnz_to_dnzT hwf h⟩

/-- The same sinks are reported; a normal `vuln` of `DNz` is a normal `vuln` of `DNzT`. -/
theorem nvuln_iffT (hwf : X.Q.WF) {M : MethodId} {n : Node} {s : PFact} :
    (∃ b, DNzT X (.nvuln M n s b)) ↔ ∃ b, DNz X (.nvuln M n s b) :=
  ⟨fun ⟨_, h⟩ => let ⟨b', h', _⟩ := dnzT_to_dnz hwf h; ⟨b', h'⟩,
   fun ⟨_, h⟩ => let ⟨b', h', _⟩ := dnz_to_dnzT hwf h; ⟨b', h'⟩⟩

theorem nvuln_normal_dnz_dnzT (hwf : X.Q.WF) {M : MethodId} {n : Node} {s : PFact}
    (h : DNz X (.nvuln M n s false)) : DNzT X (.nvuln M n s false) := by
  obtain ⟨b', h', hd⟩ := dnz_to_dnzT hwf h
  cases b' with
  | false => exact h'
  | true => exact absurd (hd rfl) Bool.false_ne_true

#print axioms edge_dnz_dnzT
#print axioms edge_dnzT_dnz
#print axioms ninit_iffT
#print axioms nadded_iffT
#print axioms nreq_iffT
#print axioms nvuln_normal_dnz_dnzT
#print axioms nvuln_iffT

end Sim

/-! ### The coverage and vulnerability theorems of `DNzT` -/

section Coverage
variable {X : Ctx}

/-- THE COVERAGE THEOREM OF `DNzT` (`NDZeroThms.nd_coverage_z` through the fact simulation).
    Let a derivation `TaintN Q M n l L0` be given, and one initial fact of `M` in `DNzT` for each
    support location, which covers it (the list `I`). Then the edge of `DNzT` keyed by `dropZ I`
    is at `n` and covers `l` (with the pair, for one premise and one support location), or
    `DNzT` has a request on the initial fact of one position, with the mark of the support
    location at that position. The hypotheses are those of `nd_coverage_z`. -/
theorem nd_coverage_zT (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) (hzl : ZeroLinks X)
    {M : MethodId} {n : Node} {l : Loc} {L0 : List Loc} (h : TaintN X.Q M n l L0)
    (I : List PFact) (hI : Al (fun i k => DNzT X (.ninit M i) ∧ i.covers k) I L0) :
    (∃ f, DNzT X (.nedge M (dropZ I) n f) ∧ NRel I L0 f.fact l) ∨
      ∃ i k, PairIn i k I L0 ∧ DNzT X (.nreq M i k.mark) := by
  have hI' : Al (fun i k => DNz X (.ninit M i) ∧ i.covers k) I L0 :=
    Al.mono (fun _ _ hik => ⟨(ninit_iffT hwf).mp hik.1, hik.2⟩) hI
  rcases nd_coverage_z hwf hα hZ hC hA hαz hzl h I hI' with ⟨f, hf, hrel⟩ | ⟨i, k, hp, hq⟩
  · obtain ⟨f', hf', hc, _⟩ := edge_dnz_dnzT hwf hf
    exact .inl ⟨f', hf', by rw [hc]; exact hrel⟩
  · exact .inr ⟨i, k, hp, (nreq_iffT hwf).mpr hq⟩

#print axioms nd_coverage_zT

/-- One support location and one premise (the form of `nd_coverage_single_z`). -/
theorem nd_coverage_single_zT (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) (hzl : ZeroLinks X)
    {M : MethodId} {n : Node} {l l0 : Loc} {i : PFact} (h : TaintN X.Q M n l [l0])
    (hi : DNzT X (.ninit M i)) (hc : i.covers l0) :
    (∃ f, DNzT X (.nedge M [i] n f) ∧ den i f.fact l0 l) ∨ DNzT X (.nreq M i l0.mark) := by
  rcases nd_coverage_single_z hwf hα hZ hC hA hαz hzl h ((ninit_iffT hwf).mp hi) hc with
    ⟨f, hf, hd⟩ | hq
  · obtain ⟨f', hf', hc', _⟩ := edge_dnz_dnzT hwf hf
    exact .inl ⟨f', hf', by rw [hc']; exact hd⟩
  · exact .inr ((nreq_iffT hwf).mpr hq)

#print axioms nd_coverage_single_zT

/-- THE COVERAGE THEOREM OF `DNzT` under the program conditions (`nd_coverage_zg`). -/
theorem nd_coverage_zgT (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hG : NDZeroBase.NoZeroGen X.Q) (hαZ : NDZeroBase.AlphaZero X.α)
    {M : MethodId} {n : Node} {l : Loc} {L0 : List Loc} (h : TaintN X.Q M n l L0)
    (I : List PFact) (hI : Al (fun i k => DNzT X (.ninit M i) ∧ i.covers k) I L0) :
    (∃ f, DNzT X (.nedge M (dropZ I) n f) ∧ NRel I L0 f.fact l) ∨
      ∃ i k, PairIn i k I L0 ∧ DNzT X (.nreq M i k.mark) :=
  nd_coverage_zT hwf hα hZ hC hA hαZ.zero (zeroLinks_of_noZeroGen hG hαZ) h I hI

#print axioms nd_coverage_zgT

/-- THE VULNERABILITY THEOREM OF `DNzT` for a tree witness (`nd_vuln_reach_z`). -/
theorem nd_vuln_reach_zT (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hzl : ZeroLinks X) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : ReachN X.Q X.roots M n l) (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) : ∃ b, DNzT X (.nvuln M n s b) :=
  (nvuln_iffT hwf).mpr (nd_vuln_reach_z hwf hα hzl hR hs hT hsc)

#print axioms nd_vuln_reach_zT

/-- THE VULNERABILITY THEOREM OF `DNzT` (`nd_vuln_found_z` through the fact simulation): a real
    execution from a root that taints a location covered by a sink pattern gives a `vuln` object
    of `DNzT`. The hypotheses are those of `nd_vuln_found_z`. -/
theorem nd_vuln_found_zT (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hzl : ZeroLinks X) {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach X.Q.prog X.roots M n l) (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) : ∃ b, DNzT X (.nvuln M n s b) :=
  (nvuln_iffT hwf).mpr (nd_vuln_found_z hwf hα hzl hR hs hT hsc)

#print axioms nd_vuln_found_zT

/-- The vulnerability theorem of `DNzT` under the program conditions (`nd_vuln_found_zg`). -/
theorem nd_vuln_found_zgT (hwf : X.Q.WF) (hα : ∀ m a, applicable (X.α m a) a = true)
    (hG : NDZeroBase.NoZeroGen X.Q) (hαZ : NDZeroBase.AlphaZero X.α)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hR : Reach X.Q.prog X.roots M n l) (hs : (M, n, s) ∈ X.sinks) (hT : s.mark = .conc T)
    (hsc : s.covers l) : ∃ b, DNzT X (.nvuln M n s b) :=
  nd_vuln_found_zT hwf hα (zeroLinks_of_noZeroGen hG hαZ) hR hs hT hsc

#print axioms nd_vuln_found_zgT

end Coverage

/-! ## Part 4. Lemmas for the new case; the invariants and Z0 of `DNT` -/

/-- THE NEW CASE, ON LOCATIONS. An input `f` of a conjunction literal `lit` (the same concrete
    mark: the gate passed) that the literal covers, or that has the `.any` tail and overlaps the
    literal, has a location that is also a location of the literal. For an `.any` input: if the
    literal is at or below the input, the position of the literal (the `.any` tail admits every
    continuation); if the literal is above the input, the position of the input (the overlap test
    checks that the literal tail admits the rest). -/
theorem lit_loc {lit f : PFact} {T : Mark} (hcv : coversB lit f = true ∨ f.kind = .any)
    (ho : overlapB f lit = true) (hfm : f.mark = .conc T) (hlm : lit.mark = .conc T) :
    ∃ l, f.covers l ∧ lit.covers l := by
  rcases hcv with hcv | hk
  · obtain ⟨l, hl⟩ := covers_nonempty f
    exact ⟨l, hl, coversB_sound hcv hl⟩
  · unfold overlapB at ho
    rw [Bool.and_eq_true] at ho
    obtain ⟨hb, hrel⟩ := ho
    have hbase : f.base = lit.base := CoreAux.beq_iff.mp hb
    cases hr : relate f.path lit.path with
    | below r =>
      have hp := Exact.relate_below hr
      refine ⟨⟨lit.base, lit.path, T⟩, ⟨hbase.symm, ⟨r, hp, by rw [hk]; trivial⟩, ?_⟩,
        ⟨rfl, ⟨[], (List.append_nil _).symm, Exact.tailI_nil _⟩, ?_⟩⟩
      · rw [hfm]; rfl
      · rw [hlm]; rfl
    | above r =>
      have hp := Exact.relate_above hr
      rw [hr] at hrel
      refine ⟨⟨f.base, f.path, T⟩, ⟨rfl, ⟨[], (List.append_nil _).symm, Exact.tailI_nil _⟩, ?_⟩,
        ⟨hbase, ⟨r, hp, Exact.admitsTailB_tailI hrel⟩, ?_⟩⟩
      · rw [hfm]; rfl
      · rw [hlm]; rfl
    | apart =>
      rw [hr] at hrel
      cases hrel

#print axioms lit_loc

/-- The conjunction keeps the correspondence under the new rule (`NDZero.conjFact_corr`). -/
theorem conjFactT_corr {cj : Conj} {f1 f1' f2 f2' : AFact} (h1 : f1.fact = f1'.fact)
    (h2 : f2.fact = f2'.fact) (hT : ∃ T, cj.target.mark = .conc T) :
    Corr (conjFactT cj f1 f2) (conjFactT cj f1' f2') ∧
      (DLe f1.demand f1'.demand → DLe f2.demand f2'.demand →
        DLe (conjFactT cj f1 f2).demand (conjFactT cj f1' f2').demand) :=
  ⟨⟨rfl, .inr hT⟩, fun d1 d2 => conjLayerT_mono h1 h2 d1 d2⟩

/-- The invariants of `DNT` (`ND.ndInv_all`, the same proof). -/
theorem ndInv_allT {X : Ctx} (hwf : X.Q.WF) {o : NObj} (h : DNT X o) : NInv o := by
  induction h with
  | root _ => trivial
  | @start M i _ _ =>
    show EdgeOK [i] (startFact i)
    refine ⟨List.cons_ne_nil _ _, fun i' t hP ht => ⟨t, ?_⟩, fun h2 => absurd h2 (Nat.not_succ_le_self 1)⟩
    rw [startFact_mark, (List.cons.inj hP).1]
    exact ht
  | step _ _ hf' ih =>
    obtain ⟨hne, hs, hnd⟩ := ih
    refine ⟨hne, fun i t hP ht => ?_, fun h2 => ?_⟩
    · obtain ⟨t1, h1⟩ := hs i t hP ht
      exact transfer_mark_conc h1 hf'
    · obtain ⟨⟨t1, h1⟩, hk⟩ := hnd h2
      exact ⟨transfer_mark_conc h1 hf', transfer_nonstar h1 hk hf'⟩
  | @reqStmt M i n f n' s t _ _ hq ih =>
    show ReqOK i
    intro t0 ht0
    obtain ⟨_, hs, _⟩ := ih
    obtain ⟨t1, h1⟩ := hs i t0 rfl ht0
    rw [transfer_reqs_of_conc h1] at hq
    exact List.not_mem_nil hq
  | pass _ _ _ ih => exact ih
  | added _ _ _ _ _ => trivial
  | initA _ _ => trivial
  | ret _ _ _ ha _ _ _ hr _ hr' ih _ _ =>
    obtain ⟨hne, hs, hnd⟩ := ih
    refine ⟨hne, fun i t hP ht => ?_, fun h2 => ?_⟩
    · obtain ⟨t1, h1⟩ := hs i t hP ht
      obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
      obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
      obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
      exact ⟨t4, by rw [limitF_mark]; exact h4⟩
    · obtain ⟨⟨t1, h1⟩, _⟩ := hnd h2
      obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
      obtain ⟨t3, h3⟩ := applySummary_mark_conc h2 hr
      obtain ⟨t4, h4⟩ := applyEdge_mark_conc h3 hr'
      exact ⟨⟨t4, by rw [limitF_mark]; exact h4⟩, limitF_nonstar (applyEdge_nonstar h3 hr')⟩
  | @ndOpen M n c n' Pc g _ _ h2 ih =>
    show PartOK Pc [] g
    obtain ⟨_, _, hnd⟩ := ih
    obtain ⟨hc, hk⟩ := hnd h2
    refine ⟨hc, hk, ?_⟩
    rw [List.length_nil, Nat.zero_add]
    exact h2
  | @ndBind M n c n' p ps P g Pf f e1 a _ _ _ _ _ ihp ihf =>
    show PartOK ps (P ++ Pf) ⟨g.fact, g.demand || a.demand⟩
    obtain ⟨hc, hk, hlen⟩ := ihp
    obtain ⟨hne, _, _⟩ := ihf
    refine ⟨hc, hk, ?_⟩
    have h1 : 0 < Pf.length := List.length_pos_iff.mpr hne
    have h2 : (p :: ps).length = ps.length + 1 := rfl
    rw [List.length_append]
    omega
  | @ndRet M n c n' P g e2 r _ _ hr ih =>
    show EdgeOK P (limitF X.counted X.FL r)
    obtain ⟨⟨t, ht⟩, _, hlen⟩ := ih
    have h2 : 2 ≤ P.length := hlen
    refine ⟨fun he => ?_, fun i t' hP _ => ?_, fun _ => ?_⟩
    · rw [he] at h2
      exact absurd h2 (by decide)
    · rw [hP] at h2
      exact absurd h2 (Nat.not_succ_le_self 1)
    · obtain ⟨t1, h1⟩ := applyEdge_mark_conc ht hr
      exact ⟨⟨t1, by rw [limitF_mark]; exact h1⟩, limitF_nonstar (applyEdge_nonstar ht hr)⟩
  | reqSink _ _ hc _ => exact check_request_star hc
  | answer _ _ _ _ _ _ => trivial
  | @reqUp m j t M ic n f n' c e a _ _ _ _ _ ha hcl _ _ ihf =>
    show ReqOK ic
    intro t0 ht0
    obtain ⟨_, hs, _⟩ := ihf
    obtain ⟨t1, h1⟩ := hs ic t0 rfl ht0
    obtain ⟨t2, h2⟩ := applyEdge_mark_conc h1 ha
    exact climbsB_abs hcl t2 h2
  | vuln _ _ _ _ _ => trivial
  | clean _ _ hf' ih =>
    obtain ⟨hne, hs, hnd⟩ := ih
    refine ⟨hne, fun i t hP ht => ?_, fun h2 => ?_⟩
    · obtain ⟨t1, h1⟩ := hs i t hP ht
      exact cleanRes_mark_conc h1 hf'
    · obtain ⟨⟨t1, h1⟩, hk⟩ := hnd h2
      exact ⟨cleanRes_mark_conc h1 hf', cleanRes_nonstar h1 hk hf'⟩
  | @reqClean M i n f n' cl t _ _ hq ih =>
    show ReqOK i
    intro t0 ht0
    obtain ⟨_, hs, _⟩ := ih
    obtain ⟨t1, h1⟩ := hs i t0 rfl ht0
    exact (cleanRes_reqs_abstract hq).1 t1 h1
  | filt _ _ _ ih => exact ih
  | @conj M P1 n f1 P2 f2 cj n' _ _ hcj _ _ _ _ ih1 ih2 =>
    show EdgeOK (P1 ++ P2) (conjFactT cj f1 f2)
    obtain ⟨hne1, _, _⟩ := ih1
    obtain ⟨hne2, _, _⟩ := ih2
    obtain ⟨hT, hk⟩ := hwf.target _ _ _ _ hcj
    refine ⟨fun he => hne1 (List.append_eq_nil_iff.mp he).1,
      fun i t hP _ => absurd hP (app_ne_single hne1 hne2), fun _ => ⟨hT, hk⟩⟩
  | @reqConj M i n f cj n' lit t _ _ _ _ hg ih =>
    show ReqOK i
    intro t0 ht0
    obtain ⟨_, hs, _⟩ := ih
    obtain ⟨t1, h1⟩ := hs i t0 rfl ht0
    exact gate_req_abs hg t1 h1

/-- W7, the strongest true form: an ND conclusion (two or more premises) has no `*` tail, and
    its mark is concrete. -/
theorem ndConclusion_uncorrelatedT {X : Ctx} (hwf : X.Q.WF) {M : MethodId} {P : List PFact}
    {n : Node} {f : AFact} (h : DNT X (.nedge M P n f)) (h2 : 2 ≤ P.length) :
    f.fact.kind.isStar = false ∧ ∃ t, f.fact.mark = .conc t :=
  let ⟨_, _, hnd⟩ := (ndInv_allT hwf h : EdgeOK P f)
  ⟨(hnd h2).2, (hnd h2).1⟩

#print axioms ndInv_allT
#print axioms ndConclusion_uncorrelatedT

/-- Every premise list is not empty. -/
theorem premises_ne_nilT {X : Ctx} (hwf : X.Q.WF) {M : MethodId} {P : List PFact}
    {n : Node} {f : AFact} (h : DNT X (.nedge M P n f)) : P ≠ [] :=
  (ndInv_allT hwf h : EdgeOK P f).1

#print axioms premises_ne_nilT

section ZeroT
variable {X : Ctx}


/-- The zero edge passes every instruction edge. -/
theorem zero_instrT (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) {M : MethodId}
    {n n' : Node} {ins : Instr} (he : (M, n, ins, n') ∈ X.Q.prog.edges)
    (h : DNT X (.nedge M [zeroFact] n Backward.zeroAF)) : DNT X (.nedge M [zeroFact] n' Backward.zeroAF) := by
  cases ins with
  | stmt s => exact DNT.step h he (zero_transfer (hZ.stmt _ _ _ _ he) _ _)
  | call c => exact DNT.pass h he (hC _ _ _ _ he).1
  | clean cl => exact DNT.clean h he (Backward.zero_clean (hZ.clean _ _ _ _ he))
  | filt b may => exact DNT.filt h he (fun hb => hZ.filt _ _ _ _ _ he hb.symm)

/-- The motive of Z0 for `DNT`. An edge at `n`: the zero initial fact of its method and the zero
    edge at `n`. An initial fact or an added fact: the zero initial fact. A partial match: its
    call edge, and the zero facts at its call node, or no caller edge is bound yet. -/
def ZDNT (X : Ctx) : NObj → Prop
  | .ninit M _ => DNT X (.ninit M zeroFact)
  | .nadded M _ => DNT X (.ninit M zeroFact)
  | .nedge M _ n _ => DNT X (.ninit M zeroFact) ∧ DNT X (.nedge M [zeroFact] n Backward.zeroAF)
  | .npart M n c n' rest P _ => (M, n, Instr.call c, n') ∈ X.Q.prog.edges ∧
      ((DNT X (.ninit M zeroFact) ∧ DNT X (.nedge M [zeroFact] n Backward.zeroAF)) ∨ (P = [] ∧ 2 ≤ rest.length))
  | _ => True


/-- Z0 (THE ZERO FACT IS EVERYWHERE), for `DNT`. The zero fact passes every instruction
    (`ZeroKept`), passes over every call and enters every callee through `zStar` (`ZeroCalls`),
    and the abstraction serves it by itself. -/
theorem zero_everywhereT (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {o : NObj} (h : DNT X o) :
    ZDNT X o := by
  induction h with
  | root hM => exact DNT.root hM
  | start _ ih => exact ⟨ih, DNT.start ih⟩
  | step _ he _ ih => exact ⟨ih.1, zero_instrT hZ hC he ih.2⟩
  | reqStmt => trivial
  | pass _ he _ ih => exact ⟨ih.1, zero_instrT hZ hC he ih.2⟩
  | @added M P n f n' c e a _ he _ _ ih =>
    show DNT X (.ninit c.callee zeroFact)
    have h1 : DNT X (.nadded c.callee zeroFact) := DNT.added ih.2 he (hC _ _ _ _ he).2 zero_bind
    have h2 := DNT.initA h1
    rw [hαz] at h2
    exact h2
  | initA _ ih => exact ih
  | ret _ he _ _ _ _ _ _ _ _ ih _ _ => exact ⟨ih.1, zero_instrT hZ hC he ih.2⟩
  | ndOpen he _ h2 _ => exact ⟨he, .inr ⟨rfl, h2⟩⟩
  | ndBind _ _ _ _ _ ihp ihf => exact ⟨ihp.1, .inl ihf⟩
  | ndRet _ _ _ ih =>
    obtain ⟨he, hz | ⟨_, hl⟩⟩ := ih
    · exact ⟨hz.1, zero_instrT hZ hC he hz.2⟩
    · exact absurd hl (by decide)
  | reqSink => trivial
  | answer _ _ _ _ _ iha => exact iha
  | reqUp => trivial
  | vuln => trivial
  | clean _ he _ ih => exact ⟨ih.1, zero_instrT hZ hC he ih.2⟩
  | reqClean => trivial
  | filt _ he _ ih => exact ⟨ih.1, zero_instrT hZ hC he ih.2⟩
  | conj _ _ hcj _ _ _ _ ih1 _ =>
    obtain ⟨_, hins⟩ := hA _ _ _ _ hcj
    exact ⟨ih1.1, zero_instrT hZ hC hins ih1.2⟩
  | reqConj => trivial

#print axioms zero_everywhereT

/-- Z0, the forms per object (`DNT`): an edge gives the zero edge at its node. -/
theorem zero_edgeT (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (h : DNT X (.nedge M P n f)) : DNT X (.nedge M [zeroFact] n Backward.zeroAF) :=
  (zero_everywhereT hZ hC hA hαz h).2

/-- The zero fact enters the callee of every call that an edge reaches. -/
theorem zero_calleeT (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P : List PFact} {n n' : Node}
    {f : AFact} {c : Call} (h : DNT X (.nedge M P n f)) (he : (M, n, Instr.call c, n') ∈ X.Q.prog.edges) :
    DNT X (.ninit c.callee zeroFact) := by
  have h1 : DNT X (.nadded c.callee zeroFact) :=
    DNT.added (zero_edgeT hZ hC hA hαz h) he (hC _ _ _ _ he).2 zero_bind
  have h2 := DNT.initA h1
  rw [hαz] at h2
  exact h2

end ZeroT

/-! ## Part 5. The exactness invariant of `DNT` -/

/-- THE ND EXACTNESS INVARIANT OF `DNT` (the motive `NDExact.NEdgeOK`): every normal-layer edge
    of `DNT` is exact against `TaintN` (`NExact`), with the invariants of `NEdgeOK`. Generic
    validity `ok`; the hypotheses of `NDExact.nd_edgeOK`: `MarkWF`, `FiltOK`, `BackOK`,
    `LitConc`, `ConjOK`. The proof is the induction of `nd_edgeOK`; only the conjunction case
    is new: a normal `.any` input that its literal does not cover has, by `lit_loc`, a location
    in the literal, and by the exactness of the input edge that location is tainted with every
    covered support; `TaintN.conj` gives the target. -/
theorem nd_edgeOKT {X : Ctx} {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog)
    (hfo : Exact.FiltOK X.Q.prog ok) (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q)
    (hco : ConjOK X.Q ok) {o : NObj} (h : DNT X o) : NEdgeOK X.Q ok o := by
  induction h with
  | root _ => trivial
  | @start M i _ _ =>
    refine ⟨List.cons_ne_nil _ _, fun p hp hab => ?_, fun h2 => absurd h2 (Nat.not_succ_le_self 1),
      fun _ _ hd hc => startFact_nonstar i hd hc, ?_⟩
    · rw [List.mem_singleton.mp hp] at hab
      rw [startFact_mark]
      exact hab
    · intro ha L0 l hP hrel hok
      obtain ⟨l0, rfl, _⟩ := Al.single hP
      have hd := hrel.2 i l0 rfl rfl
      have e := Exact.startFact_exact ha hd
      subst e
      exact ⟨TaintN.start M l, fun l0' hl0' => by rw [List.mem_singleton.mp hl0']; exact hok⟩
  | @step M P n f n' s f' _ hE hf ih =>
    obtain ⟨hne, habs, hcon, hns, hex⟩ := ih
    refine ⟨hne, fun p hp hab => Exact.transfer_abs (hmw.stmt _ _ _ _ hE) (habs p hp hab) hf,
      hcon, fun i hP hd hc => transfer_nonstar_n (fun h1 h2 => hns i hP h1 h2) hf hd hc, ?_⟩
    intro ha L0 l hP hrel hok
    have hfa := Exact.transfer_demand hf ha
    obtain ⟨ic, l0', hd, hsw⟩ := wit_of_rel hrel
    obtain ⟨l1, hd1, hs⟩ := Exact.transfer_exact (hmw.stmt _ _ _ _ hE) hfa hf ha hd
    have hok1 : ok l1 := by
      rcases hs with ⟨-, rfl⟩ | ⟨e, he, hde⟩
      · exact hok
      · exact hbo.stmt _ _ _ _ hE e he _ _ hde hok
    obtain ⟨hT, hok0⟩ := hex hfa L0 l1 hP (rel_of_wit hd1 hsw) hok1
    exact ⟨TaintN.step hT hE hs, hok0⟩
  | reqStmt => trivial
  | @pass M P n f n' c _ hE hm ih =>
    obtain ⟨hne, habs, hcon, hns, hex⟩ := ih
    refine ⟨hne, habs, hcon, hns, ?_⟩
    intro ha L0 l hP hrel hok
    obtain ⟨hT, hok0⟩ := hex ha L0 l hP hrel hok
    refine ⟨TaintN.pass hT hE ?_, hok0⟩
    rw [hrel.1.1]
    exact hm
  | added => trivial
  | initA => trivial
  | @ret M P n f n' c e1 a j g r e2 r' _ hE he1 ha _ happ _ hr he2 hr' ihD _ ihG =>
    obtain ⟨hne, habs, hcon, _, hex⟩ := ihD
    obtain ⟨_, habsG, _, _, hexG⟩ := ihG
    refine ⟨hne, fun p hp hab => ?_, hcon, fun i _ hd hc => ?_, ?_⟩
    · -- the mark invariant
      have hA := Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) (habs p hp hab) ha
      obtain ⟨x, hx, hxm⟩ := Exact.applySummary_mark hr
      obtain ⟨hgx, hcx⟩ := Exact.applyEdge_mark hx
      have hG := habsG j List.mem_cons_self (Exact.gate_abs hgx hA)
      have hR : Exact.absB r.fact.mark = true := by rw [hxm]; exact Exact.comp_abs hG hA hcx
      rw [limitF_mark]
      exact Exact.applyEdge_abs (hmw.fromC _ _ _ _ hE e2 he2) hR hr'
    · -- W2
      have e := Exact.limitF_exact hd
      rw [e] at hc ⊢
      exact applyEdge_nonstar_n hr' hc
    · intro hla L0 l hP hrel hok
      have e := Exact.limitF_exact hla
      rw [e] at hrel hla
      have hra := Exact.applyEdge_demand hr' hla
      obtain ⟨ic, l0', hd, hsw⟩ := wit_of_rel hrel
      -- the binding back to the caller
      obtain ⟨hp3, hc3⟩ :=
        Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2) (Exact.applyEdge_mark hr').1
      obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hp3 hc3 hra hr' hla hd
      have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
      -- the summary edge
      obtain ⟨x, hx, rfl⟩ := Exact.applySummary_mem hr hra
      obtain ⟨hxa, hga⟩ := Exact.or_eq_false hra
      have haa := Exact.applyEdge_demand hx hxa
      have hfa := Exact.applyEdge_demand ha haa
      have hp2 : Exact.premOKB j.mark a.fact.mark = true :=
        Exact.premOK_of_sub (Exact.applicable_markSub happ)
      have hc2 : Exact.concOKB g.fact.mark a.fact.mark = true :=
        Exact.concOK_of (fun hA => habsG j List.mem_cons_self
          (Exact.gate_abs (Exact.applyEdge_mark hx).1 hA))
      obtain ⟨l1', hd1', hdg⟩ := Exact.applyEdge_exact hp2 hc2 haa hx hxa hd2
      obtain ⟨hTG, hok1'⟩ := hexG hga [l1'] l2 (.cons (den_covers_init hdg) .nil)
        ⟨den_covers_final hdg, fun i0 k0 hI hK => by
          rw [← (List.cons.inj hI).1, ← (List.cons.inj hK).1]
          exact hdg⟩ hok2
      -- the binding into the callee
      obtain ⟨hp1, hc1⟩ :=
        Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (Exact.applyEdge_mark ha).1
      obtain ⟨l1, hd1, hde1⟩ := Exact.applyEdge_exact hp1 hc1 hfa ha haa hd1'
      have hok1 : ok l1 := hbo.toC _ _ _ _ hE e1 he1 _ _ hde1 (hok1' l1' List.mem_cons_self)
      obtain ⟨hTD, hok0⟩ := hex hfa L0 l1 hP (rel_of_wit hd1 hsw) hok1
      have hS : SupAll X.Q M n c [l1'] (L0 ++ []) := .cons hTD he1 hde1 .nil
      rw [List.append_nil] at hS
      exact ⟨TaintN.call hE hTG hS he2 hde2, hok0⟩
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @ndOpen M n c n' Pc g hE _ h2 ih =>
    obtain ⟨_, _, hcon, _, hex⟩ := ih
    refine ⟨hE, hcon h2, fun p hp => absurd hp List.not_mem_nil,
      by rw [List.length_nil, Nat.zero_add]; exact h2, ?_⟩
    intro hg l2 hc2 hok2 L0 hP
    cases hP
    refine ⟨[], SupAll.nil, fun _ h => absurd h List.not_mem_nil, fun Kr hKr => ?_⟩
    have hrel : NRel Pc Kr g.fact l2 := ⟨hc2, fun i _ hPi _ => by
      rw [hPi] at h2
      exact absurd h2 (Nat.not_succ_le_self 1)⟩
    exact hex hg Kr l2 hKr hrel hok2
  | @ndBind M n c n' p ps P g Pf f e1 a _ _ he1 ha happ ihp ihf =>
    obtain ⟨hE, hrest, hPc, hlen, hexp⟩ := ihp
    obtain ⟨hneF, habsF, _, hnsF, hexF⟩ := ihf
    -- the callee premise is concrete, so the added fact and the caller edge are concrete
    obtain ⟨t, hpt⟩ := absB_false_conc (hrest p List.mem_cons_self)
    have hat : a.fact.mark = .conc t := applicable_mark happ hpt
    have haA : Exact.absB a.fact.mark = false := by rw [hat]; rfl
    have hfA : Exact.absB f.fact.mark = false := by
      cases hb : Exact.absB f.fact.mark with
      | false => rfl
      | true =>
        have h1 := Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e1 he1) hb ha
        rw [haA] at h1
        cases h1
    refine ⟨hE, fun q hq => hrest q (List.mem_cons_of_mem _ hq), fun q hq => ?_, ?_, ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact hPc q hq
      · cases hb : Exact.absB q.mark with
        | false => rfl
        | true =>
          have h1 := habsF q hq hb
          rw [hfA] at h1
          cases h1
    · have h1 : 0 < Pf.length := List.length_pos_iff.mpr hneF
      have h2 : (p :: ps).length = ps.length + 1 := rfl
      rw [List.length_append]
      omega
    · intro hgd l2 hc2 hok2 L hL
      have hgd' : (g.demand || a.demand) = false := hgd
      obtain ⟨hgd1, had⟩ := Exact.or_eq_false hgd'
      obtain ⟨L0, Lf, rfl, hL0, hLf⟩ := al_splitL hL
      obtain ⟨Km, hS, hokL0, hrestT⟩ := hexp hgd1 l2 hc2 hok2 L0 hL0
      have hfd : f.demand = false := Exact.applyEdge_demand ha had
      -- a callee entry location of the added fact; the callee premise covers it
      obtain ⟨k, hak⟩ := covers_nonempty a.fact
      have hpk : p.covers k := applicable_sound happ hak
      obtain ⟨Kr0, hKr0⟩ := premCov_nonempty ps
      have hokk : ok k := (hrestT (k :: Kr0) (.cons hpk hKr0)).2 k List.mem_cons_self
      -- the caller location bound to it
      obtain ⟨hp1, hc1⟩ :=
        Exact.markEdge_ok (hmw.toC _ _ _ _ hE e1 he1) (Exact.applyEdge_mark ha).1
      obtain ⟨lk, hdk, hde⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had (den_refl hak)
      have hoklk : ok lk := hbo.toC _ _ _ _ hE e1 he1 _ _ hde hokk
      have hrel : NRel Pf Lf f.fact lk :=
        nrel_uncorr hfA (fun i hPi => hnsF i hPi hfd hfA) hLf (den_covers_final hdk)
      obtain ⟨hTf, hokLf⟩ := hexF hfd Lf lk hLf hrel hoklk
      have hS1 : SupAll X.Q M n c [k] (Lf ++ []) := .cons hTf he1 hde .nil
      rw [List.append_nil] at hS1
      refine ⟨Km ++ [k], supAll_append hS hS1, fun l0 hl0 => ?_, fun Kr hKr => ?_⟩
      · rcases List.mem_append.mp hl0 with h | h
        · exact hokL0 l0 h
        · exact hokLf l0 h
      · obtain ⟨hT, hokK⟩ := hrestT (k :: Kr) (.cons hpk hKr)
        refine ⟨?_, fun k' hk' => hokK k' (List.mem_cons_of_mem _ hk')⟩
        rw [List.append_assoc]
        exact hT
  | @ndRet M n c n' P g e2 r _ he2 hr ih =>
    obtain ⟨hE, _, hPc, hlen, hexp⟩ := ih
    have h2 : 2 ≤ P.length := hlen
    refine ⟨fun he => ?_, fun p hp hab => ?_, fun _ => hPc, fun i hP _ _ => ?_, ?_⟩
    · rw [he] at h2
      exact absurd h2 (by decide)
    · rw [hPc p hp] at hab
      cases hab
    · rw [hP] at h2
      exact absurd h2 (Nat.not_succ_le_self 1)
    · intro hd L0 l hP hrel hok
      have e := Exact.limitF_exact hd
      rw [e] at hd hrel
      have hgd := Exact.applyEdge_demand hr hd
      obtain ⟨hp3, hc3⟩ :=
        Exact.markEdge_ok (hmw.fromC _ _ _ _ hE e2 he2) (Exact.applyEdge_mark hr).1
      obtain ⟨l2, hd2, hde2⟩ := Exact.applyEdge_exact hp3 hc3 hgd hr hd (den_refl hrel.1)
      have hok2 : ok l2 := hbo.fromC _ _ _ _ hE e2 he2 _ _ hde2 hok
      obtain ⟨Km, hS, hokL0, hrestT⟩ := hexp hgd l2 (den_covers_final hd2) hok2 L0 hP
      obtain ⟨hT, _⟩ := hrestT [] .nil
      rw [List.append_nil] at hT
      exact ⟨TaintN.call hE hT hS he2 hde2, hokL0⟩
  | @clean M P n f n' cl f' _ hE hf ih =>
    obtain ⟨hne, habs, hcon, hns, hex⟩ := ih
    refine ⟨hne, fun p hp hab => Exact.cleanRes_abs (habs p hp hab) hf, hcon,
      fun i hP hd hc => cleanRes_nonstar_n (fun h1 h2 => hns i hP h1 h2) hf hd hc, ?_⟩
    intro ha L0 l hP hrel hok
    have hfa := Exact.cleanRes_demand hf ha
    obtain ⟨ic, l0', hd, hsw⟩ := wit_of_rel hrel
    obtain ⟨hd1, hcl⟩ := Exact.cleanRes_exact hf ha hd
    obtain ⟨hT, hok0⟩ := hex hfa L0 l hP (rel_of_wit hd1 hsw) hok
    exact ⟨TaintN.clean hT hE hcl, hok0⟩
  | reqClean => trivial
  | @filt M P n f n' b may _ hE hp ih =>
    obtain ⟨hne, habs, hcon, hns, hex⟩ := ih
    refine ⟨hne, habs, hcon, hns, ?_⟩
    intro ha L0 l hP hrel hok
    obtain ⟨hT, hok0⟩ := hex ha L0 l hP hrel hok
    refine ⟨TaintN.filt hT hE ?_, hok0⟩
    intro hb
    obtain ⟨hlb, ⟨σ, hlp, _⟩, _⟩ := hrel.1
    exact hfo _ _ _ _ _ hE f.fact.path σ l (hp (hlb.symm.trans hb)) hlp hok hb
  | @conj M P1 n f1 P2 f2 cj n' _ _ hcj ho1 hg1 ho2 hg2 ih1 ih2 =>
    obtain ⟨hne1, habs1, _, hns1, hex1⟩ := ih1
    obtain ⟨hne2, habs2, _, hns2, hex2⟩ := ih2
    obtain ⟨⟨T1, hT1⟩, ⟨T2, hT2⟩⟩ := hlc _ _ _ _ hcj
    -- a concrete literal passes only a concrete input
    rw [hT1] at hg1
    rw [hT2] at hg2
    have hf1A : Exact.absB f1.fact.mark = false := by rw [gate_conc_ok hg1]; rfl
    have hf2A : Exact.absB f2.fact.mark = false := by rw [gate_conc_ok hg2]; rfl
    -- so every premise is concrete
    have hall : ∀ p, p ∈ P1 ++ P2 → Exact.absB p.mark = false := by
      intro p hp
      cases hb : Exact.absB p.mark with
      | false => rfl
      | true =>
        exfalso
        rcases List.mem_append.mp hp with hp | hp
        · have h1 := habs1 p hp hb
          rw [hf1A] at h1
          cases h1
        · have h1 := habs2 p hp hb
          rw [hf2A] at h1
          cases h1
    refine ⟨fun he => hne1 (List.append_eq_nil_iff.mp he).1, fun p hp hab => ?_,
      fun _ => hall, fun i hP => absurd hP (app_ne_single hne1 hne2), ?_⟩
    · rw [hall p hp] at hab
      cases hab
    · intro hd L l' hP hrel hok
      -- the new layer: both inputs are normal, each is covered by its literal or is `.any`
      obtain ⟨hd1, hd2, hcv1, hcv2⟩ := conjLayerT_false hd
      obtain ⟨L1, L2, rfl, hL1, hL2⟩ := al_splitL hP
      have hct : cj.target.covers l' := hrel.1
      -- a location of each literal in its input (THE NEW CASE: an `.any` input that overlaps
      -- its literal and passes its gate has a location in the literal, `lit_loc`)
      obtain ⟨l1, hl1, hc1⟩ := lit_loc hcv1 ho1 (gate_conc_ok hg1) hT1
      obtain ⟨l2, hl2, hc2⟩ := lit_loc hcv2 ho2 (gate_conc_ok hg2) hT2
      have hok1 : ok l1 := (hco _ _ _ _ hcj l1 l' hct hok).1 hc1
      have hok2 : ok l2 := (hco _ _ _ _ hcj l2 l' hct hok).2 hc2
      obtain ⟨hTa, hokA⟩ := hex1 hd1 L1 l1 hL1
        (nrel_uncorr hf1A (fun i hPi => hns1 i hPi hd1 hf1A) hL1 hl1) hok1
      obtain ⟨hTb, hokB⟩ := hex2 hd2 L2 l2 hL2
        (nrel_uncorr hf2A (fun i hPi => hns2 i hPi hd2 hf2A) hL2 hl2) hok2
      refine ⟨TaintN.conj hTa hTb hcj hc1 hc2 hct, fun l0 hl0 => ?_⟩
      rcases List.mem_append.mp hl0 with h | h
      · exact hokA l0 h
      · exact hokB l0 h
  | reqConj => trivial

#print axioms nd_edgeOKT

/-- The exactness of one normal-layer edge of `DNT`, for a generic validity `ok` (the form of
    `NDExact.nd_edge_exact_gen`). -/
theorem nd_edge_exact_genT {X : Ctx} {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog) (hfo : Exact.FiltOK X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok)
    (h : DNT X (.nedge M P n f)) (ha : f.demand = false) :
    ∀ L0 l, PremCov P L0 → NRel P L0 f.fact l → ok l →
      TaintN X.Q M n l L0 ∧ ∀ l0, l0 ∈ L0 → ok l0 :=
  (nd_edgeOKT hmw hfo hbo hlc hco h).2.2.2.2 ha

#print axioms nd_edge_exact_genT

/-! ## Part 6. Z2: `DNzT` is inside `DNT` -/

section Z2T
variable {X : Ctx}


/-- The zero members of a partial match of `DNT` are bound by the caller zero edge. Each binding
    adds the zero fact to the joined list and keeps the layer. -/
theorem bind_zerosT (hC : ZeroCalls X.Q.prog) {M : MethodId} {n n' : Node} {c : Call}
    (hE : (M, n, Instr.call c, n') ∈ X.Q.prog.edges)
    (hz : DNT X (.nedge M [zeroFact] n Backward.zeroAF)) :
    ∀ {zs rest P : List PFact} {g : AFact}, (∀ z, z ∈ zs → z = zeroFact) →
      DNT X (.npart M n c n' (zs ++ rest) P g) →
      ∃ Z, (∀ z, z ∈ Z → z = zeroFact) ∧ DNT X (.npart M n c n' rest (P ++ Z) g)
  | [], _, _, _, _, h => ⟨[], fun _ h => absurd h List.not_mem_nil, by rw [List.append_nil]; exact h⟩
  | z :: zs, rest, P, g, hzs, h => by
    have hz0 := hzs z List.mem_cons_self
    subst hz0
    have h1 := DNT.ndBind h hz (hC _ _ _ _ hE).2 zero_bind applicable_zero_zero
    have hg : (⟨g.fact, g.demand || Backward.zeroAF.demand⟩ : AFact) = g := by
      show (⟨g.fact, g.demand || false⟩ : AFact) = g
      rw [Bool.or_false]
    rw [hg] at h1
    obtain ⟨Z, hZ, h2⟩ := bind_zerosT hC hE hz (fun z hz => hzs z (List.mem_cons_of_mem _ hz)) h1
    refine ⟨zeroFact :: Z, fun z hz' => ?_, by rw [List.append_assoc] at h2; exact h2⟩
    rcases List.mem_cons.mp hz' with rfl | hz'
    · rfl
    · exact hZ z hz'

theorem bind_zeros_allT (hC : ZeroCalls X.Q.prog) {M : MethodId} {n n' : Node} {c : Call}
    (hE : (M, n, Instr.call c, n') ∈ X.Q.prog.edges)
    (hz : DNT X (.nedge M [zeroFact] n Backward.zeroAF)) {zs P : List PFact} {g : AFact}
    (hzs : ∀ z, z ∈ zs → z = zeroFact) (h : DNT X (.npart M n c n' zs P g)) :
    ∃ Z, (∀ z, z ∈ Z → z = zeroFact) ∧ DNT X (.npart M n c n' [] (P ++ Z) g) :=
  bind_zerosT (rest := []) hC hE hz hzs (by rw [List.append_nil]; exact h)

/-- An edge of `DNT` with an abstract conclusion mark has one premise (W7). -/
theorem dn_single_of_absT (hwf : X.Q.WF) {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (h : DNT X (.nedge M P n f)) (habs : ∀ t, f.fact.mark ≠ .conc t) : ∃ x, P = [x] := by
  obtain ⟨hne, _, hnd⟩ := (ndInv_allT hwf h : EdgeOK P f)
  match P, hne, hnd with
  | [], hne, _ => exact absurd rfl hne
  | [x], _, _ => exact ⟨x, rfl⟩
  | _ :: _ :: _, _, hnd =>
    obtain ⟨⟨t, ht⟩, _⟩ := hnd (by show 2 ≤ _ + 1 + 1; omega)
    exact absurd ht (habs t)

/-- The motive of Z2. An object of `DNzT` is an object of `DNT`. An edge `P' → f'` is the image of
    an edge `P → f` with `dropZ P = P'`, the corresponding fact, and a layer that is not higher.
    A partial match `(rest', P', g')` is the image of a partial match `(rest, P, g)` of `DNT`
    whose remaining premises lose only zero members, whose joined list has the same members
    that are not the zero fact, and whose call node has the zero edge once a caller edge is
    bound. -/
def Z2MotT (X : Ctx) : NObj → Prop
  | .ninit M i => DNT X (.ninit M i)
  | .nadded M a => DNT X (.nadded M a)
  | .nreq M i t => DNT X (.nreq M i t)
  | .nvuln M n s b => ∃ b0, DNT X (.nvuln M n s b0) ∧ DLe b0 b
  | .nedge M P' n f' => ∃ P f, DNT X (.nedge M P n f) ∧ dropZ P = P' ∧ Corr f f' ∧
      DLe f.demand f'.demand
  | .npart M n c n' rest' P' g' => ∃ rest P g, DNT X (.npart M n c n' rest P g) ∧
      nz rest = rest' ∧ nz P = nz P' ∧ Corr g g' ∧ DLe g.demand g'.demand ∧
      (DNT X (.nedge M [zeroFact] n Backward.zeroAF) ∨ (P' = [] ∧ 2 ≤ rest'.length))


/-- Z2 (`DNzT` → `DNT`). Every object of `DNzT` corresponds to an object of `DNT`; an edge of `DNzT`
    keyed by `P'` is the image of an edge of `DNT` keyed by `P` with `dropZ P = P'`, the same fact,
    and a layer that is not higher. -/
theorem dnzT_to_dnT (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {o : NObj} (h : DNzT X o) :
    Z2MotT X o := by
  induction h with
  | root hM => exact DNT.root hM
  | @start M i _ ih => exact ⟨[i], startFact i, DNT.start ih, dropZ_single i, corr_refl _, DLe.refl _⟩
  | step _ he hf ih =>
    obtain ⟨P, f, hD, hP, hc, hd⟩ := ih
    obtain ⟨r, hr, hk⟩ := transfer_corr (corr_symm hc) hf
    exact ⟨P, r, DNT.step hD he hr, hP, corr_symm hk.1, hk.2.2 hd⟩
  | @reqStmt M i n f' n' s t _ he hq ih =>
    obtain ⟨P, f, hD, hP, hc, _⟩ := ih
    have hq' : t ∈ (transfer X.counted X.FL s f).reqs := by
      rw [transfer_reqs_corr hc.1]
      exact hq
    have habs : ∀ t', f.fact.mark ≠ .conc t' := fun t' ht => by
      rw [transfer_reqs_of_conc ht] at hq'
      exact List.not_mem_nil hq'
    obtain ⟨x, rfl⟩ := dn_single_of_absT hwf hD habs
    rw [dropZ_single] at hP
    have hx := (List.cons.inj hP).1
    subst hx
    exact DNT.reqStmt hD he hq'
  | pass _ he hm ih =>
    obtain ⟨P, f, hD, hP, hc, hd⟩ := ih
    exact ⟨P, f, DNT.pass hD he (by rw [hc.1]; exact hm), hP, hc, hd⟩
  | added _ he he1 ha ih =>
    obtain ⟨P, f, hD, _, hc, _⟩ := ih
    obtain ⟨a, ha2, hka⟩ := applyEdge_corr (corr_symm hc) ha
    have h2 := DNT.added hD he he1 ha2
    rw [← hka.1.1] at h2
    exact h2
  | initA _ ih => exact DNT.initA ih
  | @ret M P' n f' n' c e1 a' j g' r'' e2 r' _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    obtain ⟨P, f, hD, hP, hc, hd⟩ := ihf
    obtain ⟨Pc, g, hG, hPc, hcg, hdg⟩ := ihg
    obtain ⟨a, ha2, hka⟩ := applyEdge_corr (corr_symm hc) ha
    have hap2 : applicable j a.fact = true := by rw [← hka.1.1]; exact hap
    have hda : DLe a.demand a'.demand := hka.2.2 hd
    have hne := premises_ne_nilT hwf hG
    cases Pc with
    | nil => exact absurd rfl hne
    | cons x xs =>
      cases xs with
      | nil =>
        -- the summary has one premise in `DNT` too: `ret`
        rw [dropZ_single] at hPc
        have hx := (List.cons.inj hPc).1
        subst hx
        obtain ⟨r, hr2, hcr, _, hdr⟩ := applySummary_corr hka.1 (corr_symm hcg) hr
        obtain ⟨q, hq, hkq⟩ := applyEdge_corr hcr hr'
        obtain ⟨hl1, _, hl3⟩ := limitF_corr X.counted X.FL hkq.1
        exact ⟨P, _, DNT.ret hD he he1 ha2 ihj hap2 hG hr2 he2 hq, hP, corr_symm hl1,
          hl3 (hkq.2.2 (hdr hda hdg))⟩
      | cons y zs =>
        -- an ND summary of `DNT` whose `dropZ` has one member: the chain, the zero members bound
        -- by the caller zero edge
        have h2 : 2 ≤ (x :: y :: zs).length := by show 2 ≤ zs.length + 1 + 1; omega
        obtain ⟨hgk, T, hgT⟩ := ndConclusion_uncorrelatedT hwf hG h2
        have hgT' : g'.fact.mark = .conc T := by rw [← hcg.1]; exact hgT
        have hgk' : g'.fact.kind.isStar = false := by rw [← hcg.1]; exact hgk
        obtain ⟨hrf, hrd⟩ := summary_nd_fact ⟨T, hgT'⟩ hgk' hr
        have hz0 := zero_edgeT hZ hC hA hαz hD
        obtain ⟨zs1, ws, hsplit, hzs1, hws⟩ := dropZ_eq_single (List.cons_ne_nil _ _) hPc
        have hopen := DNT.ndOpen he hG h2
        rw [hsplit] at hopen
        obtain ⟨Z1, hZ1, h3⟩ := bind_zerosT hC he hz0 hzs1 hopen
        have h4 := DNT.ndBind h3 hD he1 ha2 hap2
        obtain ⟨Z2, hZ2, h5⟩ := bind_zeros_allT hC he hz0 hws h4
        -- the conclusion of the chain corresponds to the `ret` result of `DNzT`
        have hcorr : Corr r'' ⟨g.fact, g.demand || a.demand⟩ :=
          ⟨by rw [hrf]; exact hcg.1.symm, .inr ⟨T, by rw [hrf]; exact hgT'⟩⟩
        obtain ⟨q, hq, hkq⟩ := applyEdge_corr hcorr hr'
        obtain ⟨hl1, _, hl3⟩ := limitF_corr X.counted X.FL hkq.1
        have hdl : DLe (g.demand || a.demand) r''.demand := fun h => hrd (dle_comm_or hdg hda h)
        refine ⟨[] ++ Z1 ++ P ++ Z2, _, DNT.ndRet h5 he2 hq, ?_, corr_symm hl1, hl3 (hkq.2.2 hdl)⟩
        rw [List.nil_append, dropZ_sandwich hZ1 hZ2]
        exact hP
  | @ndOpen M n c n' Pc' g' he _ h2 ih =>
    obtain ⟨Pc, g, hG, hPc, hcg, hdg⟩ := ih
    have h2' : 2 ≤ (dropZ Pc).length := by rw [hPc]; exact h2
    obtain ⟨hnzP, _⟩ := two_le_dropZ h2'
    have hlen : 2 ≤ Pc.length := Nat.le_trans h2' (dropZ_length_le (premises_ne_nilT hwf hG))
    refine ⟨Pc, [], g, DNT.ndOpen he hG hlen, ?_, rfl, hcg, hdg, .inr ⟨rfl, h2⟩⟩
    rw [← hnzP]
    exact hPc
  | @ndBind M n c n' p ps P' g' Pf' f' e1 a' _ _ he1 ha hap ihp ihf =>
    obtain ⟨rest, P, g, hpart, hrest, hPP, hcg, hdg, _⟩ := ihp
    obtain ⟨Pf, f, hD, hPf, hcf, hdf⟩ := ihf
    obtain ⟨zs, tail, rfl, hzs, htail, _⟩ := nz_eq_cons hrest
    have hE := (zero_everywhereT hZ hC hA hαz hpart).1
    have hz0 := zero_edgeT hZ hC hA hαz hD
    obtain ⟨Z, hZz, h1⟩ := bind_zerosT hC hE hz0 hzs hpart
    obtain ⟨a, ha2, hka⟩ := applyEdge_corr (corr_symm hcf) ha
    have hap2 : applicable p a.fact = true := by rw [← hka.1.1]; exact hap
    have h2 := DNT.ndBind h1 hD he1 ha2 hap2
    obtain ⟨⟨T, hT⟩, _, _⟩ := (ndInv_allT hwf hpart : PartOK _ _ g)
    refine ⟨tail, (P ++ Z) ++ Pf, ⟨g.fact, g.demand || a.demand⟩, h2, htail, ?_,
      ⟨hcg.1, .inr ⟨T, hT⟩⟩, DLe.or hdg (hka.2.2 hdf), .inl hz0⟩
    rw [nz_append, nz_append, nz_allZ hZz, List.append_nil, hPP, nz_append, ← hPf, nz_dropZ]
  | @ndRet M n c n' P' g' e2 r' _ he2 hr ih =>
    obtain ⟨rest, P, g, hpart, hrest, hPP, hcg, hdg, hz⟩ := ih
    have hz0 : DNT X (.nedge M [zeroFact] n Backward.zeroAF) := by
      rcases hz with hz | ⟨_, hl⟩
      · exact hz
      · exact absurd hl (by decide)
    have hE := (zero_everywhereT hZ hC hA hαz hpart).1
    obtain ⟨Z, hZz, h1⟩ := bind_zeros_allT hC hE hz0 (nz_eq_nil_iff.mp hrest) hpart
    obtain ⟨r, hr2, hkr⟩ := applyEdge_corr (corr_symm hcg) hr
    obtain ⟨hl1, _, hl3⟩ := limitF_corr X.counted X.FL hkr.1
    refine ⟨P ++ Z, _, DNT.ndRet h1 he2 hr2, ?_, corr_symm hl1, hl3 (hkr.2.2 hdg)⟩
    rw [dropZ_append_allZ hZz]
    exact dropZ_eq_iff.mpr hPP
  | @reqSink M i n f' s t _ hs hc ih =>
    obtain ⟨P, f, hD, hP, hcf, _⟩ := ih
    have hc' : check i f s = .request t := by rw [check_corr hcf.1]; exact hc
    obtain ⟨x, rfl⟩ := dn_single_of_absT hwf hD (check_request_abs hc')
    rw [dropZ_single] at hP
    have hx := (List.cons.inj hP).1
    subst hx
    exact DNT.reqSink hD hs hc'
  | answer _ _ hm hov ihr iha => exact DNT.answer ihr iha hm hov
  | @reqUp m j t M ic n f' n' c e a' _ _ he hcm he1 ha hcl hov ihr ihf =>
    obtain ⟨P, f, hD, hP, hcf, _⟩ := ihf
    obtain ⟨a, ha2, hka⟩ := applyEdge_corr (corr_symm hcf) ha
    have hcl2 : climbsB a.fact.mark t = true := by rw [← hka.1.1]; exact hcl
    have hov2 : overlapB a.fact j = true := by rw [← hka.1.1]; exact hov
    have habs : ∀ t', f.fact.mark ≠ .conc t' := fun t' ht =>
      let ⟨t'', h''⟩ := applyEdge_mark_conc ht ha2
      climbsB_abs hcl2 t'' h''
    obtain ⟨x, rfl⟩ := dn_single_of_absT hwf hD habs
    rw [dropZ_single] at hP
    have hx := (List.cons.inj hP).1
    subst hx
    exact DNT.reqUp ihr hD he hcm he1 ha2 hcl2 hov2
  | @vuln M P' n f' s i _ hs hi hc ih =>
    obtain ⟨P, f, hD, hP, hcf, hdf⟩ := ih
    have hc' : check i f s = .triggered := by rw [check_corr hcf.1]; exact hc
    refine ⟨f.demand, ?_, hdf⟩
    rcases mark_dich f.fact.mark with ⟨t, ht⟩ | habs
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil P (premises_ne_nilT hwf hD)
      exact DNT.vuln hD hs hx (by rw [check_conc_indep (i' := i) ht]; exact hc')
    · obtain ⟨x, rfl⟩ := dn_single_of_absT hwf hD habs
      rw [dropZ_single] at hP
      rw [← hP] at hi
      exact DNT.vuln hD hs hi hc'
  | clean _ he hf ih =>
    obtain ⟨P, f, hD, hP, hc, hd⟩ := ih
    obtain ⟨r, hr, hk⟩ := cleanRes_corr (corr_symm hc) hf
    exact ⟨P, r, DNT.clean hD he hr, hP, corr_symm hk.1, hk.2.2 hd⟩
  | @reqClean M i n f' n' cl t _ he hq ih =>
    obtain ⟨P, f, hD, hP, hc, _⟩ := ih
    have hq' : t ∈ (cleanRes cl f).reqs := by rw [cleanRes_reqs_corr hc.1]; exact hq
    obtain ⟨x, rfl⟩ := dn_single_of_absT hwf hD (cleanRes_reqs_abstract hq').1
    rw [dropZ_single] at hP
    have hx := (List.cons.inj hP).1
    subst hx
    exact DNT.reqClean hD he hq'
  | filt _ he hm ih =>
    obtain ⟨P, f, hD, hP, hc, hd⟩ := ih
    exact ⟨P, f, DNT.filt hD he (by rw [hc.1]; exact hm), hP, hc, hd⟩
  | conj _ _ hcj ho1 hg1 ho2 hg2 ih1 ih2 =>
    obtain ⟨P1, f1, hD1, hP1, hc1, hd1⟩ := ih1
    obtain ⟨P2, f2, hD2, hP2, hc2, hd2⟩ := ih2
    obtain ⟨hC', hdl⟩ := conjFactT_corr hc1.1 hc2.1 (hwf.target _ _ _ _ hcj).1
    refine ⟨P1 ++ P2, _, DNT.conj hD1 hD2 hcj (by rw [hc1.1]; exact ho1) (by rw [hc1.1]; exact hg1)
      (by rw [hc2.1]; exact ho2) (by rw [hc2.1]; exact hg2), ?_, hC', hdl hd1 hd2⟩
    rw [← dropZ_dropZ_append, hP1, hP2]
  | @reqConj M i n f' cj n' lit t _ hcj hlit ho hg ih =>
    obtain ⟨P, f, hD, hP, hc, _⟩ := ih
    have hg' : markGate lit.mark f.fact.mark = .req t := by rw [hc.1]; exact hg
    obtain ⟨x, rfl⟩ := dn_single_of_absT hwf hD (gate_req_abs hg')
    rw [dropZ_single] at hP
    have hx := (List.cons.inj hP).1
    subst hx
    exact DNT.reqConj hD hcj hlit (by rw [hc.1]; exact ho) hg'

#print axioms dnzT_to_dnT


/-- The premise invariant of `DNzT`: a premise list is not empty and its members are initial
    facts of the method. -/
def PIzT (X : Ctx) : NObj → Prop
  | .nedge M P _ _ => P ≠ [] ∧ ∀ p, p ∈ P → DNzT X (.ninit M p)
  | .npart M _ _ _ rest P _ => (∀ p, p ∈ P → DNzT X (.ninit M p)) ∧ (P ≠ [] ∨ 2 ≤ rest.length)
  | _ => True

theorem premInit_zT {o : NObj} (h : DNzT X o) : PIzT X o := by
  induction h with
  | root => trivial
  | @start M i hi _ =>
    exact ⟨List.cons_ne_nil _ _, fun p hp => by rw [List.mem_singleton.mp hp]; exact hi⟩
  | step _ _ _ ih => exact ih
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initA => trivial
  | ret _ _ _ _ _ _ _ _ _ _ ih _ _ => exact ih
  | ndOpen _ _ h2 _ => exact ⟨fun _ h => absurd h List.not_mem_nil, .inr h2⟩
  | ndBind _ _ _ _ _ ihp ihf =>
    refine ⟨fun p hp => ?_, .inl fun he => ihf.1 (List.append_eq_nil_iff.mp he).2⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact ihp.1 p hp
    · exact ihf.2 p hp
  | ndRet _ _ _ ih =>
    obtain ⟨hmem, hne | hl⟩ := ih
    · exact ⟨dropZ_ne_nil _, fun p hp => hmem p (mem_of_mem_dropZ hne hp)⟩
    · exact absurd hl (by decide)
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ _ ih => exact ih
  | reqClean => trivial
  | filt _ _ _ ih => exact ih
  | @conj M P1 n f1 P2 f2 cj n' _ _ _ _ _ _ _ ih1 ih2 =>
    have hne : P1 ++ P2 ≠ [] := fun he => ih1.1 (List.append_eq_nil_iff.mp he).1
    refine ⟨dropZ_ne_nil _, fun p hp => ?_⟩
    rcases List.mem_append.mp (mem_of_mem_dropZ hne hp) with hp | hp
    · exact ih1.2 p hp
    · exact ih2.2 p hp
  | reqConj => trivial

#print axioms premInit_zT

/-- Z2 for an edge: a `DNzT` edge keyed by `P'` is the image of a `DNT` edge keyed by `P` with
    `dropZ P = P'`, the same fact, and a normal `DNT` edge if the `DNzT` edge is normal. -/
theorem dnzT_to_dnT_edge (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P' : List PFact}
    {n : Node} {f' : AFact} (h : DNzT X (.nedge M P' n f')) :
    ∃ P f, DNT X (.nedge M P n f) ∧ dropZ P = P' ∧ f.fact = f'.fact ∧
      (f'.demand = false → f.demand = false) := by
  obtain ⟨P, f, hD, hP, hc, hd⟩ := dnzT_to_dnT hwf hZ hC hA hαz h
  refine ⟨P, f, hD, hP, hc.1, fun h0 => ?_⟩
  cases hfd : f.demand with
  | false => rfl
  | true =>
    have h1 := hd hfd
    rw [h0] at h1
    exact absurd h1 Bool.false_ne_true

#print axioms dnzT_to_dnT_edge

end Z2T

/-! ## Part 7. The exactness theorem of `DNzT` -/

/-- THE ND EXACTNESS THEOREM OF `DNT` (the form of `NDExact.nd_edge_exact`). -/
theorem nd_edge_exactT {X : Ctx} {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (hmw : Exact.MarkWF X.Q.prog) (hup : Exact.FiltUp X.Q.prog) (hlc : LitConc X.Q)
    (h : DNT X (.nedge M P n f)) (ha : f.demand = false) :
    ∀ L0 l, PremCov P L0 → NRel P L0 f.fact l → TaintN X.Q M n l L0 := fun L0 l hP hrel =>
  (nd_edge_exact_genT (ok := fun _ => True) hmw (Exact.filtUp_ok hup) (Exact.backOK_true _) hlc
    (conjOK_true _) h ha L0 l hP hrel trivial).1

#print axioms nd_edge_exactT

/-- THE ND EXACTNESS THEOREM OF `DNT` FOR VALID LOCATIONS (the form of
    `NDExact.nd_edge_exact_valid`). -/
theorem nd_edge_exact_validT {X : Ctx} {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog) (hv : Exact.FiltValid X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok)
    (h : DNT X (.nedge M P n f)) (ha : f.demand = false) :
    ∀ L0 l, PremCov P L0 → NRel P L0 f.fact l → ok l →
      TaintN X.Q M n l L0 ∧ ∀ l0, l0 ∈ L0 → ok l0 :=
  nd_edge_exact_genT hmw (Exact.filtValid_ok hv) hbo hlc hco h ha

#print axioms nd_edge_exact_validT

section ExactT
variable {X : Ctx}

/-- The lift of a normal `DNzT` edge and of a support of its premises to `DNT`. -/
theorem dnzT_edge_lift (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P' : List PFact}
    {n : Node} {f' : AFact} (h : DNzT X (.nedge M P' n f')) (ha : f'.demand = false)
    {L' : List Loc} {l : Loc} (hP' : PremCov P' L') (hrel : NRel P' L' f'.fact l) :
    ∃ P f L0, DNT X (.nedge M P n f) ∧ f.demand = false ∧ PremCov P L0 ∧ NRel P L0 f.fact l ∧
      L'.Sublist L0 ∧ ∀ k, k ∈ L0 → k ∈ L' ∨ k = zeroLoc := by
  obtain ⟨P, f, hD, hPP, hfa, hfd⟩ := dnzT_to_dnT_edge hwf hZ hC hA hαz h
  subst hPP
  obtain ⟨L0, hL0, hsub, hmem⟩ := fill_dropZ (premises_ne_nilT hwf hD) hP'
  refine ⟨P, f, L0, hD, hfd ha, hL0, ⟨by rw [hfa]; exact hrel.1, fun i l0 hPi hLi => ?_⟩, hsub, hmem⟩
  subst hPi hLi
  rw [dropZ_single] at hP' hrel
  obtain ⟨k, rfl, _⟩ := Al.single hP'
  have hk : k = l0 := List.mem_singleton.mp (List.singleton_sublist.mp hsub)
  subst hk
  rw [hfa]
  exact hrel.2 i k rfl rfl

/-- THE EXACTNESS THEOREM OF `DNzT` (the form of `NDZeroThms.nd_edge_exact_z`; `nd_edge_exactT`
    through Z2, `dnzT_to_dnT`). A normal-layer edge of `DNzT` (also one that only the new
    conjunction rule keeps normal) denotes only taintings of `TaintN`: for every support `L'`
    that its premises cover and every end location in the relation `NRel`, the location is
    tainted with a support `L0` that contains `L'` as a sub-list, and whose other locations are
    the zero location (the zero fact that `dropZ` removed). The hypotheses are those of
    `nd_edge_exact_z`: `NProg.WF`, the Z0 hypotheses (`ZeroKept`, `ZeroCalls`, `ConjAdj`, the
    zero abstraction), `MarkWF` (S7), `FiltUp`, `LitConc` (S9). -/
theorem nd_edge_exact_zT (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) (hmw : Exact.MarkWF X.Q.prog)
    (hup : Exact.FiltUp X.Q.prog) (hlc : LitConc X.Q) {M : MethodId} {P' : List PFact} {n : Node}
    {f' : AFact} (h : DNzT X (.nedge M P' n f')) (ha : f'.demand = false) :
    ∀ L' l, PremCov P' L' → NRel P' L' f'.fact l →
      ∃ L0, TaintN X.Q M n l L0 ∧ L'.Sublist L0 ∧ ∀ k, k ∈ L0 → k ∈ L' ∨ k = zeroLoc := by
  intro L' l hP' hrel
  obtain ⟨P, f, L0, hD, hfd, hL0, hrel0, hsub, hmem⟩ := dnzT_edge_lift hwf hZ hC hA hαz h ha hP' hrel
  exact ⟨L0, nd_edge_exactT hmw hup hlc hD hfd L0 l hL0 hrel0, hsub, hmem⟩

#print axioms nd_edge_exact_zT

/-- THE EXACTNESS THEOREM OF `DNzT` FOR VALID LOCATIONS (the form of
    `NDZeroThms.nd_edge_exact_valid_z`; `nd_edge_exact_validT` through Z2): for a valid end
    location (prefix-closed type filters `FiltValid` (S13), validity closed backwards `BackOK`
    (S10) and from a conjunction target to its literals `ConjOK`), the normal edge is exact as in
    `nd_edge_exact_zT`, and every location of the support is valid too. The hypotheses are those
    of `nd_edge_exact_valid_z`. -/
theorem nd_edge_exact_valid_zT (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog)
    (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact)
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog) (hv : Exact.FiltValid X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok) {M : MethodId}
    {P' : List PFact} {n : Node} {f' : AFact} (h : DNzT X (.nedge M P' n f'))
    (ha : f'.demand = false) :
    ∀ L' l, PremCov P' L' → NRel P' L' f'.fact l → ok l →
      ∃ L0, TaintN X.Q M n l L0 ∧ L'.Sublist L0 ∧ (∀ k, k ∈ L0 → k ∈ L' ∨ k = zeroLoc) ∧
        ∀ k, k ∈ L0 → ok k := by
  intro L' l hP' hrel hok
  obtain ⟨P, f, L0, hD, hfd, hL0, hrel0, hsub, hmem⟩ := dnzT_edge_lift hwf hZ hC hA hαz h ha hP' hrel
  obtain ⟨hT, hokL⟩ := nd_edge_exact_validT hmw hv hbo hlc hco hD hfd L0 l hL0 hrel0 hok
  exact ⟨L0, hT, hsub, hmem, hokL⟩

#print axioms nd_edge_exact_valid_zT

end ExactT

/-! ## Part 8. The confirmation of `DNzT` -/

/-! ### The confirmation of `DNT` (the proofs of `NDConfirmed`, copied) -/

mutual
/-- `SupNT X M P`: the premise LIST `P` of an edge of `M` is supported JOINTLY.
    * `root`: `M` is a root and every premise is the zero fact;
    * `call`: ONE call statement `(M', n, c, n')` to `M` supplies every premise (`SupSlotsT`). -/
inductive SupNT (X : Ctx) : MethodId → List PFact → Prop where
  | root {M P} : M ∈ X.roots → (∀ p, p ∈ P → p = zeroFact) → SupNT X M P
  | call {M n c n' J} : (M, n, Instr.call c, n') ∈ X.Q.prog.edges → SupSlotsT X M n c J →
      SupNT X c.callee J

/-- `SupSlotsT X M n c J`: at the call node `n` of `M` (call `c`), every callee premise `j ∈ J`
    has its own normal caller edge `(Pm, f)` at `n` whose premise list `Pm` is supported
    (jointly, `SupNT`), whose binding gives the normal added fact `a`, and `j = a` (the zero
    fact, or the exact concrete answer of `a`: the condition of the base `Confirmed.Sup`). -/
inductive SupSlotsT (X : Ctx) : MethodId → Node → Call → List PFact → Prop where
  | nil {M n c} : SupSlotsT X M n c []
  | cons {M n c Pm f e a j J} :
      SupNT X M Pm → DNT X (.nedge M Pm n f) → f.demand = false →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DNT X (.ninit c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, DNT X (.nreq c.callee k t) ∧ a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧
          j = answerInit k a.fact t ∧ j = a.fact)) →
      SupSlotsT X M n c J → SupSlotsT X M n c (j :: J)
end

/-- A CONFIRMED ND vulnerability of `DNT`: a NORMAL-layer sink edge with the premise list `P`
    (condition 1, read as in decision 1: a normal edge is complete, also with the `.any` tail,
    the spec `[any-taint]`); every premise is exact with a concrete mark (condition 2); the
    premise list is supported jointly (condition 3); the sink check triggers. -/
def ConfirmedNT (X : Ctx) (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ P f, DNT X (.nedge M P n f) ∧ f.demand = false ∧ (∀ p, p ∈ P → ExactConc p) ∧
    SupNT X M P ∧ (M, n, s) ∈ X.sinks ∧ ∃ i, i ∈ P ∧ check i f s = .triggered

/-- A confirmed vulnerability is a `vuln` object of the normal layer. -/
theorem confirmedN_vulnT {X : Ctx} {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedNT X M n s) : DNT X (.nvuln M n s false) := by
  obtain ⟨P, f, hD, hc, _, _, hs, i, hi, hch⟩ := h
  have hv := DNT.vuln hD hs hi hch
  rw [hc] at hv
  exact hv

#print axioms confirmedN_vulnT

section SupportT
variable {X : Ctx} {ok : Loc → Prop}

mutual
/-- THE SUPPORT THEOREM. A jointly supported premise list covers a support `L0` that is real
    at the entry of `M` (if its locations are valid). -/
theorem sup_entryNT (hmw : Exact.MarkWF X.Q.prog) (hfo : Exact.FiltOK X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok) :
    ∀ {M P}, SupNT X M P →
      ∃ L0, PremCov P L0 ∧ ((∀ l0, l0 ∈ L0 → ok l0) → EntryN X.Q X.roots M L0)
  | _, _, .root hM hz =>
    ⟨_, premCov_zero hz, fun _ => .inl ⟨hM, fun _ hk => mem_map_zero hk⟩⟩
  | _, _, .call hE hS => by
    obtain ⟨K, hK, hR⟩ := sup_slotsNT hmw hfo hbo hlc hco hS hE
    exact ⟨K, hK, fun hok => .inr ⟨_, _, _, _, hE, rfl, hR hok⟩⟩

/-- The slots of one call: the callee entry locations are bound from reached caller
    locations at the call node. -/
theorem sup_slotsNT (hmw : Exact.MarkWF X.Q.prog) (hfo : Exact.FiltOK X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok) :
    ∀ {M n c J}, SupSlotsT X M n c J → ∀ {n'}, (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      ∃ K, PremCov J K ∧ ((∀ k, k ∈ K → ok k) → ReachAll X.Q X.roots M n c K)
  | _, _, _, _, .nil, _, _ => ⟨[], .nil, fun _ => .nil⟩
  | _, _, _, _, @SupSlotsT.cons _ M n c Pm f e a j J hSm hf hfd he1 ha had _ hj hS, _, hE => by
    have ihm := sup_entryNT hmw hfo hbo hlc hco hSm
    have ihs := sup_slotsNT hmw hfo hbo hlc hco hS hE
    obtain ⟨Lm, hLm, hent⟩ := ihm
    obtain ⟨K, hK, hR⟩ := ihs
    obtain ⟨t, hak, ham, rfl⟩ := Confirmed.sup_step hj
    have hac := exactConc_covers hak ham
    refine ⟨_ :: K, .cons hac hK, fun hok => ?_⟩
    have hokk := hok _ List.mem_cons_self
    -- the caller location bound to the callee entry location
    obtain ⟨hp1, hc1⟩ :=
      Exact.markEdge_ok (hmw.toC _ _ _ _ hE e he1) (Exact.applyEdge_mark ha).1
    obtain ⟨lk, hdk, hde⟩ := Exact.applyEdge_exact hp1 hc1 hfd ha had (den_refl hac)
    have hoklk : ok lk := hbo.toC _ _ _ _ hE e he1 _ _ hde hokk
    -- the caller edge is concrete (the added fact is), so it is uncorrelated
    have hfA : Exact.absB f.fact.mark = false := by
      cases hb : Exact.absB f.fact.mark with
      | false => rfl
      | true =>
        have h1 := Exact.applyEdge_abs (hmw.toC _ _ _ _ hE e he1) hb ha
        rw [ham] at h1
        cases h1
    have hinv : NEdgeOK X.Q ok (.nedge M Pm n f) := nd_edgeOKT hmw hfo hbo hlc hco hf
    obtain ⟨_, _, _, hns, hex⟩ := hinv
    have hrel : NRel Pm Lm f.fact lk :=
      nrel_uncorr hfA (fun i hPi => hns i hPi hfd hfA) hLm (den_covers_final hdk)
    obtain ⟨hT, hokL⟩ := hex hfd Lm lk hLm hrel hoklk
    exact .cons (entry_reachN (hent hokL) hT) he1 hde
      (hR (fun k' hk' => hok k' (List.mem_cons_of_mem _ hk')))
end

#print axioms sup_entryNT
#print axioms sup_slotsNT

end SupportT

section MainT
variable {X : Ctx} {ok : Loc → Prop}

/-- The sink fact of a normal edge with concrete premises is uncorrelated: a concrete mark and
    no `*` tail. One premise: `edge_conc` and W2 (`nd_edgeOKT`); two or more: W7. -/
theorem sink_shapeT (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog) (hfo : Exact.FiltOK X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok)
    {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (hD : DNT X (.nedge M P n f)) (hfd : f.demand = false) (hex : ∀ p, p ∈ P → ExactConc p) :
    Exact.absB f.fact.mark = false ∧ f.fact.kind.isStar = false := by
  have hinv : EdgeOK P f := ndInv_allT hwf hD
  obtain ⟨hne, hs1, hnd⟩ := hinv
  cases P with
  | nil => exact absurd rfl hne
  | cons i P' =>
    cases P' with
    | nil =>
      obtain ⟨_, t, ht⟩ := hex i List.mem_cons_self
      obtain ⟨t', ht'⟩ := hs1 i t rfl ht
      have hA : Exact.absB f.fact.mark = false := by rw [ht']; rfl
      have hok : NEdgeOK X.Q ok (.nedge M [i] n f) := nd_edgeOKT hmw hfo hbo hlc hco hD
      exact ⟨hA, hok.2.2.2.1 i rfl hfd hA⟩
    | cons i2 P'' =>
      obtain ⟨⟨t, ht⟩, hk⟩ := hnd (by show 2 ≤ P''.length + 1 + 1; omega)
      exact ⟨by rw [ht]; rfl, hk⟩

#print axioms sink_shapeT

/-- A sink fact without a `*` tail (`$` or `.any`) with the concrete mark of the sink pattern,
    that overlaps the pattern, has a location in the pattern. -/
theorem sink_loc {f s : PFact} {T : Mark} (hk : f.kind.isStar = false) (ho : overlapB f s = true)
    (hfm : f.mark = .conc T) (hsm : s.mark = .conc T) : ∃ l, f.covers l ∧ s.covers l := by
  cases hfk : f.kind with
  | star e => rw [hfk] at hk; cases hk
  | any => exact lit_loc (.inr hfk) ho hfm hsm
  | exact =>
    exact ⟨_, exactConc_covers hfk hfm, Confirmed.overlap_exact_covers hfk ho T (by rw [hsm]; rfl)⟩

#print axioms sink_loc

/-- THE ND CONFIRMATION THEOREM OF `DNT`, generic validity `ok` (the form of
    `NDConfirmed.confirmed_real_N_gen`, with a normal sink edge that may have the `.any` tail):
    a confirmed ND vulnerability has a location in the sink pattern, and that location is
    reached by a tree witness (`ReachN`) if it is valid. -/
theorem confirmed_real_N_genT (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hfo : Exact.FiltOK X.Q.prog ok) (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q)
    (hco : ConjOK X.Q ok) {M : MethodId} {n : Node} {s : PFact} (h : ConfirmedNT X M n s) :
    ∃ l, s.covers l ∧ (ok l → ReachN X.Q X.roots M n l) := by
  obtain ⟨P, f, hD, hfd, hex, hS, _, i, hi, hch⟩ := h
  obtain ⟨_, t0, him⟩ := hex i hi
  obtain ⟨T, hsm, ho, hmo, _⟩ := Confirmed.check_triggered_passes him hch
  obtain ⟨hfA, hns⟩ := sink_shapeT hwf hmw hfo hbo hlc hco hD hfd hex
  obtain ⟨T', hT'⟩ := absB_false_conc hfA
  have hTT : T' = T := by
    rw [hT'] at hmo
    exact hmo
  rw [hTT] at hT'
  -- the sink location: a location of the sink fact (`$` or `.any`) in the sink pattern
  obtain ⟨l, hfc, hsc⟩ := sink_loc hns ho hT' hsm
  -- a real support of the premises
  obtain ⟨L0, hL0, hent⟩ := sup_entryNT hmw hfo hbo hlc hco hS
  refine ⟨l, hsc, fun hok => ?_⟩
  have hrel : NRel P L0 f.fact l := nrel_uncorr hfA (fun _ _ => hns) hL0 hfc
  obtain ⟨hT, hokL⟩ := nd_edge_exact_genT hmw hfo hbo hlc hco hD hfd L0 _ hL0 hrel hok
  exact entry_reachN (hent hokL) hT

#print axioms confirmed_real_N_genT

/-- THE ND CONFIRMATION THEOREM (programs without a real type filter, `FiltUp`): a confirmed ND
    vulnerability is real against the support semantics: a tree witness from the roots reaches
    a location of the sink pattern. -/
theorem confirmed_real_NT (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hup : Exact.FiltUp X.Q.prog) (hlc : LitConc X.Q)
    {M : MethodId} {n : Node} {s : PFact} (h : ConfirmedNT X M n s) :
    ∃ l, ReachN X.Q X.roots M n l ∧ s.covers l := by
  obtain ⟨l, hsc, hR⟩ := confirmed_real_N_genT (ok := fun _ => True) hwf hmw (Exact.filtUp_ok hup)
    (Exact.backOK_true _) hlc (conjOK_true _) h
  exact ⟨l, hR trivial, hsc⟩

#print axioms confirmed_real_NT

/-- THE ND CONFIRMATION THEOREM FOR VALID LOCATIONS (prefix-closed type filters, no `FiltUp`):
    a location of the sink pattern that is reached if it is valid. -/
theorem confirmed_real_NT_valid_of (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hv : Exact.FiltValid X.Q.prog ok) (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q)
    (hco : ConjOK X.Q ok) {M : MethodId} {n : Node} {s : PFact} (h : ConfirmedNT X M n s) :
    ∃ l, s.covers l ∧ (ok l → ReachN X.Q X.roots M n l) :=
  confirmed_real_N_genT hwf hmw (Exact.filtValid_ok hv) hbo hlc hco h

#print axioms confirmed_real_NT_valid_of

/-- THE ND CONFIRMATION THEOREM FOR A REAL PROGRAM with prefix-closed type filters: if every
    location of the sink pattern is valid, a confirmed ND vulnerability is real. -/
theorem confirmed_real_NT_valid (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hv : Exact.FiltValid X.Q.prog ok) (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q)
    (hco : ConjOK X.Q ok) {M : MethodId} {n : Node} {s : PFact}
    (hok : ∀ l, s.covers l → ok l) (h : ConfirmedNT X M n s) :
    ∃ l, ReachN X.Q X.roots M n l ∧ s.covers l := by
  obtain ⟨l, hsc, hR⟩ := confirmed_real_NT_valid_of hwf hmw hv hbo hlc hco h
  exact ⟨l, hR (hok l hsc), hsc⟩

#print axioms confirmed_real_NT_valid

end MainT

/-! ### The confirmation of `DNzT` -/

mutual
/-- `SupNzT X M P`: the premise set `P` of an edge of `DNzT` is supported JOINTLY (spec §4.9
    condition 3; the form of `NDConfirmed.SupNT`).
    * `root`: `M` is a root and every premise is the zero fact;
    * `call`: ONE call statement `(M', n, c, n')` to `M` supplies every premise (`SupSlotsNzT`). -/
inductive SupNzT (X : Ctx) : MethodId → List PFact → Prop where
  | root {M P} : M ∈ X.roots → (∀ p, p ∈ P → p = zeroFact) → SupNzT X M P
  | call {M n c n' J} : (M, n, Instr.call c, n') ∈ X.Q.prog.edges → SupSlotsNzT X M n c J →
      SupNzT X c.callee J

/-- `SupSlotsNzT X M n c J`: at the call node `n` of `M` (call `c`), every callee premise `j ∈ J`
    has its own normal caller edge of `DNzT` at `n`, whose premise set is supported, whose binding
    gives the normal added fact `a`, and `j = a` (the zero fact, or the exact concrete answer of
    `a`). -/
inductive SupSlotsNzT (X : Ctx) : MethodId → Node → Call → List PFact → Prop where
  | nil {M n c} : SupSlotsNzT X M n c []
  | cons {M n c Pm f e a j J} :
      SupNzT X M Pm → DNzT X (.nedge M Pm n f) → f.demand = false →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DNzT X (.ninit c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, DNzT X (.nreq c.callee k t) ∧ a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧
          j = answerInit k a.fact t ∧ j = a.fact)) →
      SupSlotsNzT X M n c J → SupSlotsNzT X M n c (j :: J)
end

/-- A CONFIRMED vulnerability of `DNzT` (spec §4.9): a NORMAL-layer sink edge of `DNzT` with the
    premise set `P` (condition 1, read as in decision 1: a normal edge is complete, also with
    the `[any-taint]` tail, the model's normal `.any`), exact concrete premises (condition 2),
    the joint support of `P` (condition 3), and a triggered sink check. -/
def ConfirmedNzT (X : Ctx) (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ P f, DNzT X (.nedge M P n f) ∧ f.demand = false ∧ (∀ p, p ∈ P → ExactConc p) ∧
    SupNzT X M P ∧ (M, n, s) ∈ X.sinks ∧ ∃ i, i ∈ P ∧ check i f s = .triggered

/-- A confirmed vulnerability of `DNzT` is a normal `vuln` object of `DNzT`. -/
theorem confirmedNz_vulnT {X : Ctx} {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedNzT X M n s) : DNzT X (.nvuln M n s false) := by
  obtain ⟨P, f, hD, hc, _, _, hs, i, hi, hch⟩ := h
  have hv := DNzT.vuln hD hs hi hch
  rw [hc] at hv
  exact hv

#print axioms confirmedNz_vulnT

section ConfirmT
variable {X : Ctx}

/-- The zero slot of a call `(M, n, c)`: the caller zero edge is supported, the zero binding
    binds it, and the callee has the zero initial fact (Z0). -/
abbrev ZeroDataT (X : Ctx) (M : MethodId) (n : Node) (c : Call) : Prop :=
  SupNT X M [zeroFact] ∧ DNT X (.nedge M [zeroFact] n Backward.zeroAF) ∧
    (zStar, zStar) ∈ c.toCallee ∧ DNT X (.ninit c.callee zeroFact)

theorem zero_slotT {M : MethodId} {n : Node} {c : Call} {J : List PFact} (hd : ZeroDataT X M n c)
    (hS : SupSlotsT X M n c J) : SupSlotsT X M n c (zeroFact :: J) :=
  SupSlotsT.cons hd.1 hd.2.1 rfl hd.2.2.1 zero_bind rfl hd.2.2.2 (.inl ⟨rfl, rfl⟩) hS

theorem zero_slotsT {M : MethodId} {n : Node} {c : Call} (hd : ZeroDataT X M n c) :
    ∀ {Z J : List PFact}, (∀ z, z ∈ Z → z = zeroFact) → SupSlotsT X M n c J →
      SupSlotsT X M n c (Z ++ J)
  | [], _, _, hS => hS
  | z :: Z, _, hz, hS => by
    have hz0 := hz z List.mem_cons_self
    subst hz0
    exact zero_slotT hd (zero_slotsT hd (fun x hx => hz x (List.mem_cons_of_mem _ hx)) hS)

mutual
/-- A supported premise list with a member supports the zero premise `[zeroFact]` too: the zero
    edge of each caller is at the same call node (Z0). -/
theorem supN_zeroT (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) :
    ∀ {M : MethodId} {P : List PFact}, SupNT X M P → P ≠ [] → SupNT X M [zeroFact]
  | _, _, .root hM _, _ => SupNT.root hM (fun _ hp => List.mem_singleton.mp hp)
  | _, _, .call hE hS, hne => slots_zeroT hwf hZ hC hA hαz hS hE hne

theorem slots_zeroT (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) :
    ∀ {M : MethodId} {n : Node} {c : Call} {J : List PFact}, SupSlotsT X M n c J →
      ∀ {n' : Node}, (M, n, Instr.call c, n') ∈ X.Q.prog.edges → J ≠ [] →
        SupNT X c.callee [zeroFact]
  | _, _, _, _, .nil, _, _, hne => absurd rfl hne
  | _, _, _, _, .cons hSm hf _ _ _ _ _ _ _, _, hE, _ => by
    have hz := supN_zeroT hwf hZ hC hA hαz hSm (premises_ne_nilT hwf hf)
    exact SupNT.call hE (zero_slotT ⟨hz, zero_edgeT hZ hC hA hαz hf, (hC _ _ _ _ hE).2,
      zero_calleeT hZ hC hA hαz hf hE⟩ SupSlotsT.nil)
end

#print axioms supN_zeroT

mutual
/-- THE SUPPORT TRANSFER: a joint support of a `DNzT` premise set is a joint support of every
    `DNT` premise list with the same members that are not the zero fact. The zero members are
    supported by the caller zero edges at the same call (`ZeroDataT`). -/
theorem supNz_supNT (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) :
    ∀ {M : MethodId} {P' : List PFact}, SupNzT X M P' → P' ≠ [] →
      ∀ P, nz P = nz P' → SupNT X M P
  | _, _, .root hM hz, _, _, hnz =>
    SupNT.root hM (nz_eq_nil_iff.mp (hnz.trans (nz_eq_nil_iff.mpr hz)))
  | _, _, .call hE hS, hne', P, hnz =>
    SupNT.call hE (slotsNz_slotsT hwf hZ hC hA hαz hS hE (slotsNz_zdT hwf hZ hC hA hαz hS hE hne') P hnz)

/-- A call with a slot gives the zero slot at the same call node. -/
theorem slotsNz_zdT (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) :
    ∀ {M : MethodId} {n : Node} {c : Call} {J' : List PFact}, SupSlotsNzT X M n c J' →
      ∀ {n' : Node}, (M, n, Instr.call c, n') ∈ X.Q.prog.edges → J' ≠ [] → ZeroDataT X M n c
  | _, _, _, _, .nil, _, _, hne => absurd rfl hne
  | _, _, _, _, .cons hSm hf _ _ _ _ _ _ _, _, hE, _ => by
    obtain ⟨Pm0, f0, hD, hPm, _, _⟩ := dnzT_to_dnT_edge hwf hZ hC hA hαz hf
    have hS0 := supNz_supNT hwf hZ hC hA hαz hSm (premInit_zT hf).1 Pm0 (by rw [← hPm, nz_dropZ])
    exact ⟨supN_zeroT hwf hZ hC hA hαz hS0 (premises_ne_nilT hwf hD), zero_edgeT hZ hC hA hαz hD,
      (hC _ _ _ _ hE).2, zero_calleeT hZ hC hA hαz hD hE⟩

/-- The slots of a `DNzT` premise set give the slots of a `DNT` premise list with the same members
    that are not the zero fact. -/
theorem slotsNz_slotsT (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) :
    ∀ {M : MethodId} {n : Node} {c : Call} {J' : List PFact}, SupSlotsNzT X M n c J' →
      ∀ {n' : Node}, (M, n, Instr.call c, n') ∈ X.Q.prog.edges → ZeroDataT X M n c →
        ∀ J, nz J = nz J' → SupSlotsT X M n c J
  | _, _, _, _, .nil, _, _, hd, J, hnz => by
    have h := zero_slotsT hd (nz_eq_nil_iff.mp hnz) SupSlotsT.nil
    rw [List.append_nil] at h
    exact h
  | _, _, _, _, @SupSlotsNzT.cons _ M n c Pm f e a j J' hSm hf hfd he ha had hj hjc hS, _, hE, hd,
      J, hnz => by
    by_cases hj0 : j = zeroFact
    · subst hj0
      rw [nz_cons_zero] at hnz
      exact slotsNz_slotsT hwf hZ hC hA hαz hS hE hd J hnz
    · rw [nz_cons_ne _ hj0] at hnz
      obtain ⟨zs, tail, rfl, hzs, htail, _⟩ := nz_eq_cons hnz
      apply zero_slotsT hd hzs
      obtain ⟨Pm0, f0, hD, hPm, hcf, hdf⟩ := dnzT_to_dnT hwf hZ hC hA hαz hf
      have hf0d : f0.demand = false := by
        cases hb : f0.demand with
        | false => rfl
        | true =>
          have h1 := hdf hb
          rw [hfd] at h1
          exact absurd h1 Bool.false_ne_true
      obtain ⟨a0, ha0, hka⟩ := applyEdge_corr (corr_symm hcf) ha
      have ha0d : a0.demand = false := by
        cases hb : a0.demand with
        | false => rfl
        | true =>
          have h1 := hka.2.2 hdf hb
          rw [had] at h1
          exact absurd h1 Bool.false_ne_true
      have hS0 := supNz_supNT hwf hZ hC hA hαz hSm (premInit_zT hf).1 Pm0 (by rw [← hPm, nz_dropZ])
      have hjD : DNT X (.ninit c.callee j) := dnzT_to_dnT hwf hZ hC hA hαz hj
      have hfa : a.fact = a0.fact := hka.1.1
      have hjc' : (j = zeroFact ∧ a0.fact = zeroFact) ∨
          (∃ k t, DNT X (.nreq c.callee k t) ∧ a0.fact.kind = .exact ∧ a0.fact.mark = .conc t ∧
            j = answerInit k a0.fact t ∧ j = a0.fact) := by
        rw [← hfa]
        rcases hjc with h1 | ⟨k, t, hq, hak, ham, hans, hja⟩
        · exact .inl h1
        · exact .inr ⟨k, t, dnzT_to_dnT hwf hZ hC hA hαz hq, hak, ham, hans, hja⟩
      exact SupSlotsT.cons hS0 hD hf0d he ha0 ha0d hjD hjc'
        (slotsNz_slotsT hwf hZ hC hA hαz hS hE hd tail htail)
end

#print axioms supNz_supNT

/-- A CONFIRMATION OF `DNzT` IS A CONFIRMATION OF `DNT`: the corresponding `DNT` sink edge (Z2) is
    normal, its premises are exact and concrete (a zero member is the zero fact), its premise
    list is supported jointly (the zero members by the caller zero edges, `supNz_supNT`), and its
    sink check triggers. -/
theorem confirmedNz_NT (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {n : Node}
    {s : PFact} (h : ConfirmedNzT X M n s) : ConfirmedNT X M n s := by
  obtain ⟨P', f', hD', hc', hex', hS', hs, i, hi, hch⟩ := h
  obtain ⟨P, f, hD, hPP, hfa, hfd⟩ := dnzT_to_dnT_edge hwf hZ hC hA hαz hD'
  have hne := premises_ne_nilT hwf hD
  have hfd' := hfd hc'
  refine ⟨P, f, hD, hfd', fun p hp => ?_, supNz_supNT hwf hZ hC hA hαz hS' (premInit_zT hD').1 P
    (by rw [← hPP, nz_dropZ]), hs, i, mem_of_mem_dropZ hne (hPP ▸ hi), ?_⟩
  · by_cases hp0 : p = zeroFact
    · rw [hp0]
      exact ⟨rfl, zeroMark, rfl⟩
    · exact hex' p (by rw [← hPP]; exact mem_dropZ.mpr (.inl ⟨hp, hp0⟩))
  · rw [check_corr hfa]
    exact hch

#print axioms confirmedNz_NT

/-- THE CONFIRMATION THEOREM OF `DNzT` (the form of `NDZeroThms.confirmed_real_Nz`; programs
    without a real type filter, `FiltUp`; `confirmed_real_NT` through `confirmedNz_NT`): a
    confirmed vulnerability of `DNzT` (a NORMAL sink edge, also with the `[any-taint]` tail, and
    also one that only the new conjunction rule keeps normal) is real against the support
    semantics: a tree witness from the roots reaches a location of the sink pattern. The
    hypotheses are those of `confirmed_real_Nz`. -/
theorem confirmed_real_NzT (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog)
    (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact)
    (hmw : Exact.MarkWF X.Q.prog) (hup : Exact.FiltUp X.Q.prog) (hlc : LitConc X.Q)
    {M : MethodId} {n : Node} {s : PFact} (h : ConfirmedNzT X M n s) :
    ∃ l, ReachN X.Q X.roots M n l ∧ s.covers l :=
  confirmed_real_NT hwf hmw hup hlc (confirmedNz_NT hwf hZ hC hA hαz h)

#print axioms confirmed_real_NzT

/-- THE CONFIRMATION THEOREM OF `DNzT`, generic validity (the form of
    `NDZeroThms.confirmed_real_Nz_valid_of`): a confirmed vulnerability of `DNzT` has a location
    in the sink pattern, and that location is reached by a tree witness if it is valid. -/
theorem confirmed_real_NzT_valid_of (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog)
    (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact)
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog) (hv : Exact.FiltValid X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok)
    {M : MethodId} {n : Node} {s : PFact} (h : ConfirmedNzT X M n s) :
    ∃ l, s.covers l ∧ (ok l → ReachN X.Q X.roots M n l) :=
  confirmed_real_NT_valid_of hwf hmw hv hbo hlc hco (confirmedNz_NT hwf hZ hC hA hαz h)

#print axioms confirmed_real_NzT_valid_of

/-- THE CONFIRMATION THEOREM OF `DNzT` FOR VALID LOCATIONS (the form of
    `NDZeroThms.confirmed_real_Nz_valid`; prefix-closed type filters, `FiltValid`, `BackOK`,
    `ConjOK`): if every location of the sink pattern is valid, a confirmed vulnerability of
    `DNzT` is real. -/
theorem confirmed_real_NzT_valid (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog)
    (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact)
    {ok : Loc → Prop} (hmw : Exact.MarkWF X.Q.prog) (hv : Exact.FiltValid X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok)
    {M : MethodId} {n : Node} {s : PFact} (hok : ∀ l, s.covers l → ok l)
    (h : ConfirmedNzT X M n s) : ∃ l, ReachN X.Q X.roots M n l ∧ s.covers l :=
  confirmed_real_NT_valid hwf hmw hv hbo hlc hco hok (confirmedNz_NT hwf hZ hC hA hαz h)

#print axioms confirmed_real_NzT_valid

end ConfirmT

/-! ### The old confirmation is a new confirmation -/

section Lift
variable {X : Ctx}

mutual
/-- A joint support of `DNz` (`NDZeroThms.SupNz`) is a joint support of `DNzT`: the caller edges
    of `DNz` are caller edges of `DNzT` with the same facts and a layer that is not higher
    (`edge_dnz_dnzT`). -/
theorem supNz_supNzT (hwf : X.Q.WF) : ∀ {M : MethodId} {P : List PFact}, SupNz X M P → SupNzT X M P
  | _, _, .root hM hz => SupNzT.root hM hz
  | _, _, .call hE hS => SupNzT.call hE (slotsNz_slotsNzT hwf hS)

theorem slotsNz_slotsNzT (hwf : X.Q.WF) :
    ∀ {M : MethodId} {n : Node} {c : Call} {J : List PFact}, SupSlotsNz X M n c J →
      SupSlotsNzT X M n c J
  | _, _, _, _, .nil => SupSlotsNzT.nil
  | _, _, _, _, .cons hSm hf hfd he ha had hj hjc hS => by
    obtain ⟨f', hf', hfa, hdn⟩ := edge_dnz_dnzT hwf hf
    have hfd' := hdn hfd
    have hc : Corr _ f' := ⟨hfa.symm, .inl (by rw [hfd, hfd'])⟩
    obtain ⟨a', ha', hka⟩ := applyEdge_corr hc ha
    have had' : a'.demand = false := by
      cases hb : a'.demand with
      | false => rfl
      | true =>
        have h1 := hka.2.2 (fun h => by rw [hfd'] at h; cases h) hb
        rw [had] at h1
        cases h1
    refine SupSlotsNzT.cons (supNz_supNzT hwf hSm) hf' hfd' he ha' had' ((ninit_iffT hwf).mpr hj)
      ?_ (slotsNz_slotsNzT hwf hS)
    rw [← hka.1.1]
    rcases hjc with h1 | ⟨k, t, hq, hak, ham, hans, hja⟩
    · exact .inl h1
    · exact .inr ⟨k, t, (nreq_iffT hwf).mpr hq, hak, ham, hans, hja⟩
end

/-- EVERY VULNERABILITY THAT THE OLD RULE CONFIRMS, THE NEW RULE CONFIRMS: a confirmation of
    `DNz` (`NDZeroThms.ConfirmedNz`, a complete sink edge) is a confirmation of `DNzT`. The new
    rule only adds confirmations (`Example.old_not_confirmed`, `Example.confirmed`). -/
theorem confirmedNz_confirmedNzT (hwf : X.Q.WF) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedNz X M n s) : ConfirmedNzT X M n s := by
  obtain ⟨P, f, hD, hc, hex, hS, hs, i, hi, hch⟩ := h
  obtain ⟨f', hf', hfa, hdn⟩ := edge_dnz_dnzT hwf hD
  exact ⟨P, f', hf', hdn (Exact.complete_demand hc), hex, supNz_supNzT hwf hS, hs, i, hi,
    by rw [check_corr hfa]; exact hch⟩

#print axioms confirmedNz_confirmedNzT

end Lift

/-! ## Part 9. The worked example

`x = srcAny(); y = src(); z = conj(x.f, y); sink(z)`. The root method `0`; node `0 → 1` is the
source with an `[any]` target: it gives `(x, [], .any, T)` from the zero fact in the NORMAL layer
(an `[any-taint]` fact: every location below `x` carries `T`); node `1 → 2` is the source
`(y, [], $, U)`; the conjunction `(x, [f], $, T) ∧ (y, [], $, U) → (z, [], $, V)` goes from node
`2` to node `3` (beside the empty statement); the sink pattern `(z, [], $, V)` is at node `3`.
Bases: `x = 1`, `y = 2`, `z = 3`; the field `f = 5`; the marks `T = 7`, `U = 8`, `V = 9`.

The literal `(x, [f], $, T)` does not cover the input `(x, [], .any, T)` (the input has other
locations), so `ND.conjLayer` puts the result in the demand layer; `conjLayerT` keeps it normal.
Under the new rule the vulnerability is a normal `vuln` of `DNzT` and CONFIRMED
(`confirmed`), and it is real (`real`, by `confirmed_real_NzT`; `taint_z` is the support
derivation itself). Under the old rule EVERY `vuln` of `DNz` at the sink is in the demand layer
(`old_vuln_demand`), so the old rule does not confirm it (`old_not_confirmed`). -/

namespace Example

/-- The `[any-taint]` source fact `(x, [], .any, T)`. -/
def xAny : PFact := ⟨1, [], .any, .conc 7⟩
/-- The exact source fact `(y, [], $, U)`; it is also the second literal. -/
def yE : PFact := ⟨2, [], .exact, .conc 8⟩
/-- The first literal `(x, [f], $, T)`. -/
def lit1 : PFact := ⟨1, [5], .exact, .conc 7⟩
/-- The target and the sink pattern `(z, [], $, V)`. -/
def tgt : PFact := ⟨3, [], .exact, .conc 9⟩
def srcX : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, xAny)]⟩
def srcY : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, yE)]⟩
def nop : Stmt := ⟨[], []⟩
def cj : Conj := ⟨lit1, yE, tgt⟩
def prog : Program :=
  ⟨fun _ => 0, fun _ => 3, [(0, 0, .stmt srcX, 1), (0, 1, .stmt srcY, 2), (0, 2, .stmt nop, 3)]⟩
def Q : NProg := ⟨prog, [(0, 2, cj, 3)]⟩
def X : Ctx := ⟨Q, fun _ => true, 5, fun _ a => a, [(0, 3, tgt)], [0]⟩

/-- The two inputs of the conjunction at node `2`, both in the normal layer. -/
def fx : AFact := ⟨xAny, false⟩
def fy : AFact := ⟨yE, false⟩

/-- The literal does not cover the `[any-taint]` input. -/
theorem not_covered : coversB cj.lit1 fx.fact = false := by decide

/-- THE LAYERS: the new rule keeps the result normal, the old rule puts it in the demand layer. -/
theorem layer_new : conjLayerT cj fx fy = false := by decide

theorem layer_old : conjLayer cj fx fy = true := by decide

#print axioms layer_new

/-! ### The derivation of the new closure `DNzT` -/

theorem e0 : DNzT X (.nedge 0 [zeroFact] 0 ⟨zeroFact, false⟩) := DNzT.start (DNzT.root List.mem_cons_self)
theorem x1 : DNzT X (.nedge 0 [zeroFact] 1 fx) := DNzT.step e0 List.mem_cons_self (by decide)
theorem z1 : DNzT X (.nedge 0 [zeroFact] 1 ⟨zeroFact, false⟩) :=
  DNzT.step e0 List.mem_cons_self (by decide)
theorem x2 : DNzT X (.nedge 0 [zeroFact] 2 fx) :=
  DNzT.step x1 (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem y2 : DNzT X (.nedge 0 [zeroFact] 2 fy) :=
  DNzT.step z1 (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)

theorem dropZ_zz : dropZ ([zeroFact] ++ [zeroFact]) = [zeroFact] := by decide

/-- The conjunction result of `DNzT`, in the NORMAL layer. -/
theorem c3 : DNzT X (.nedge 0 [zeroFact] 3 (conjFactT cj fx fy)) := by
  have h := DNzT.conj x2 y2 List.mem_cons_self (by decide) rfl (by decide) rfl
  rw [dropZ_zz] at h
  exact h

theorem c3_normal : (conjFactT cj fx fy).demand = false := layer_new

#print axioms c3

/-- The vulnerability is a normal `vuln` of `DNzT`. -/
theorem vuln3 : DNzT X (.nvuln 0 3 tgt false) :=
  DNzT.vuln c3 List.mem_cons_self List.mem_cons_self (by decide)

#print axioms vuln3

/-- THE CONFIRMATION under the new rule: the sink edge is normal, its premise is the zero fact of
    the root, and the sink check triggers. -/
theorem confirmed : ConfirmedNzT X 0 3 tgt :=
  ⟨[zeroFact], _, c3, c3_normal, fun p hp => by rw [List.mem_singleton.mp hp]; exact ⟨rfl, zeroMark, rfl⟩,
    SupNzT.root List.mem_cons_self (fun p hp => List.mem_singleton.mp hp),
    List.mem_cons_self, zeroFact, List.mem_cons_self, by decide⟩

#print axioms confirmed

/-! ### The old closure `DNz`: the same edge in the demand layer -/

theorem e0z : DNz X (.nedge 0 [zeroFact] 0 ⟨zeroFact, false⟩) := DNz.start (DNz.root List.mem_cons_self)
theorem x1z : DNz X (.nedge 0 [zeroFact] 1 fx) := DNz.step e0z List.mem_cons_self (by decide)
theorem z1z : DNz X (.nedge 0 [zeroFact] 1 ⟨zeroFact, false⟩) :=
  DNz.step e0z List.mem_cons_self (by decide)
theorem x2z : DNz X (.nedge 0 [zeroFact] 2 fx) :=
  DNz.step x1z (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
theorem y2z : DNz X (.nedge 0 [zeroFact] 2 fy) :=
  DNz.step z1z (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)

/-- The conjunction result of `DNz`, in the DEMAND layer. -/
theorem c3z : DNz X (.nedge 0 [zeroFact] 3 (conjFact cj fx fy)) := by
  have h := DNz.conj x2z y2z List.mem_cons_self (by decide) rfl (by decide) rfl
  rw [dropZ_zz] at h
  exact h

theorem c3z_demand : (conjFact cj fx fy).demand = true := layer_old

#print axioms c3z

/-! ### The support derivation -/

def lx : Loc := ⟨1, [5], 7⟩
def ly : Loc := ⟨2, [], 8⟩
def lz : Loc := ⟨3, [], 9⟩

/-- `x.f` carries `T` at node `2` (the `[any]` target of the source taints every location of
    `x`, in particular `x.f`). -/
theorem taint_x : TaintN Q 0 2 lx [zeroLoc] :=
  TaintN.step
    (TaintN.step (TaintN.start 0 zeroLoc) List.mem_cons_self
      (.inr ⟨(zeroFact, xAny), List.mem_cons_of_mem _ List.mem_cons_self,
        ⟨rfl, rfl, rfl, rfl, trivial, [], [5], rfl, rfl, rfl, trivial⟩⟩))
    (List.mem_cons_of_mem _ List.mem_cons_self) (.inl ⟨rfl, rfl⟩)

theorem taint_z1 : TaintN Q 0 1 zeroLoc [zeroLoc] :=
  TaintN.step (TaintN.start 0 zeroLoc) List.mem_cons_self
    (.inr ⟨(zeroFact, zeroFact), List.mem_cons_self,
      ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩⟩)

theorem taint_y : TaintN Q 0 2 ly [zeroLoc] :=
  TaintN.step taint_z1 (List.mem_cons_of_mem _ List.mem_cons_self)
    (.inr ⟨(zeroFact, yE), List.mem_cons_of_mem _ List.mem_cons_self,
      ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩⟩)

/-- THE SUPPORT DERIVATION: the conjunction holds at `x.f` and `y`, so `z` carries `V` at node
    `3`, with the zero support of the root. -/
theorem taint_z : TaintN Q 0 3 lz [zeroLoc, zeroLoc] :=
  TaintN.conj taint_x taint_y List.mem_cons_self ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩
    ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩ ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

theorem reach_z : ReachN Q X.roots 0 3 lz :=
  ReachN.root List.mem_cons_self taint_z (fun k hk => by
    rcases List.mem_cons.mp hk with rfl | hk
    · rfl
    · exact List.mem_singleton.mp hk)

#print axioms taint_z
#print axioms reach_z

/-! ### The program conditions, and the confirmation theorem applied -/

theorem no_call {M n n' : Node} {c : Call} : (M, n, Instr.call c, n') ∉ prog.edges := by
  intro h
  cases h with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

theorem no_clean {M n n' : Node} {cl : Cleaner} : (M, n, Instr.clean cl, n') ∉ prog.edges := by
  intro h
  cases h with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

theorem no_filt {M n n' : Node} {b : Base} {may : List Acc → Bool} :
    (M, n, Instr.filt b may, n') ∉ prog.edges := by
  intro h
  cases h with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

/-- The statements of the program. -/
theorem stmt_cases {M n n' : Node} {s : Stmt} (h : (M, n, Instr.stmt s, n') ∈ prog.edges) :
    s = srcX ∨ s = srcY ∨ s = nop := by
  cases h with
  | head => exact .inl rfl
  | tail _ h =>
    cases h with
    | head => exact .inr (.inl rfl)
    | tail _ h =>
      cases h with
      | head => exact .inr (.inr rfl)
      | tail _ h => cases h

theorem conj_cases {M n n' : Node} {cj' : Conj} (h : (M, n, cj', n') ∈ Q.conjs) :
    M = 0 ∧ n = 2 ∧ cj' = cj ∧ n' = 3 := by
  cases h with
  | head => exact ⟨rfl, rfl, rfl, rfl⟩
  | tail _ h => cases h

theorem wf : Q.WF where
  prog := {
    stmtTouched := by
      intro M n s n' hE e he
      rcases stmt_cases hE with rfl | rfl | rfl
      · revert e; decide
      · revert e; decide
      · cases he
    toStar := fun _ _ _ _ hE => absurd hE no_call
    fromStar := fun _ _ _ _ hE => absurd hE no_call
    filtPrefix := fun _ _ _ _ _ hE => absurd hE no_filt }
  target := by
    intro M n cj' n' hE
    obtain ⟨-, -, rfl, -⟩ := conj_cases hE
    exact ⟨⟨9, rfl⟩, rfl⟩

theorem markWF : Exact.MarkWF Q.prog where
  stmt := by
    intro M n s n' hE e he
    rcases stmt_cases hE with rfl | rfl | rfl
    · revert e; decide
    · revert e; decide
    · cases he
  toC := fun _ _ _ _ hE => absurd hE no_call
  fromC := fun _ _ _ _ hE => absurd hE no_call

theorem filtUp : Exact.FiltUp Q.prog := fun _ _ _ _ _ hE => absurd hE no_filt

theorem litConc : LitConc Q := by
  intro M n cj' n' hE
  obtain ⟨-, -, rfl, -⟩ := conj_cases hE
  exact ⟨⟨7, rfl⟩, ⟨8, rfl⟩⟩

theorem zeroKept : Backward.ZeroKept Q.prog where
  stmt := by
    intro M n s n' hE ht
    rcases stmt_cases hE with rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_self
    · cases ht
  clean := fun _ _ _ _ hE => absurd hE no_clean
  filt := fun _ _ _ _ _ hE => absurd hE no_filt

theorem zeroCalls : ZeroCalls Q.prog := fun _ _ _ _ hE => absurd hE no_call

theorem conjAdj : ConjAdj Q := by
  intro M n cj' n' hE
  obtain ⟨rfl, rfl, -, rfl⟩ := conj_cases hE
  exact ⟨.stmt nop, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- THE CONFIRMED VULNERABILITY IS REAL (`confirmed_real_NzT` applied to `confirmed`): a tree
    witness from the root reaches a location of the sink pattern. -/
theorem real : ∃ l, ReachN X.Q X.roots 0 3 l ∧ tgt.covers l :=
  confirmed_real_NzT wf zeroKept zeroCalls conjAdj (fun _ => rfl) markWF filtUp litConc confirmed

#print axioms real

/-! ### Under the old rule the vulnerability is only in the demand layer -/

/-- The edge facts of `DNz` on this program: the zero fact, the two source facts, and the
    target in the DEMAND layer. -/
def InvB (f : AFact) : Bool :=
  decide (f.fact = zeroFact) || decide (f.fact = xAny) || decide (f.fact = yE) ||
    (decide (f.fact = tgt) && f.demand)

theorem invB_cases {f : AFact} (h : InvB f = true) :
    f.fact = zeroFact ∨ f.fact = xAny ∨ f.fact = yE ∨ (f.fact = tgt ∧ f.demand = true) := by
  unfold InvB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

theorem invB_conc {f : AFact} (h : InvB f = true) : ∃ t, f.fact.mark = .conc t := by
  rcases invB_cases h with h | h | h | ⟨h, _⟩ <;> rw [h]
  · exact ⟨zeroMark, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩

theorem invB_base1 {f : AFact} (h : InvB f = true) (hb : f.fact.base = 1) : f.fact = xAny := by
  rcases invB_cases h with h | h | h | ⟨h, _⟩
  · rw [h] at hb; cases hb
  · exact h
  · rw [h] at hb; cases hb
  · rw [h] at hb; cases hb

theorem invB_base3 {f : AFact} (h : InvB f = true) (hb : f.fact.base = 3) : f.demand = true := by
  rcases invB_cases h with h | h | h | ⟨_, h⟩
  · rw [h] at hb; cases hb
  · rw [h] at hb; cases hb
  · rw [h] at hb; cases hb
  · exact h

/-- The statement transfer keeps the invariant (a finite check). -/
theorem transfer_inv : ∀ s, s ∈ [srcX, srcY, nop] → ∀ φ, φ ∈ [zeroFact, xAny, yE] → ∀ d : Bool,
    (transfer (fun _ => true) 5 s ⟨φ, d⟩).facts.all InvB = true := by decide

theorem transfer_inv_tgt : ∀ s, s ∈ [srcX, srcY, nop] →
    (transfer (fun _ => true) 5 s ⟨tgt, true⟩).facts.all InvB = true := by decide

theorem transfer_invB {s : Stmt} (hs : s = srcX ∨ s = srcY ∨ s = nop) {f r : AFact}
    (hf : InvB f = true) (hr : r ∈ (transfer (fun _ => true) 5 s f).facts) : InvB r = true := by
  have hs' : s ∈ [srcX, srcY, nop] := by
    rcases hs with rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨φ, d⟩ := f
  have hall : (transfer (fun _ => true) 5 s ⟨φ, d⟩).facts.all InvB = true := by
    rcases invB_cases hf with h | h | h | ⟨h, hd⟩
    · change φ = zeroFact at h
      exact transfer_inv s hs' φ (by rw [h]; exact List.mem_cons_self) d
    · change φ = xAny at h
      exact transfer_inv s hs' φ (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self) d
    · change φ = yE at h
      exact transfer_inv s hs' φ
        (by rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) d
    · change φ = tgt at h
      change d = true at hd
      subst h hd
      exact transfer_inv_tgt s hs'
  exact List.all_eq_true.mp hall r hr

theorem check_overlap_of_trig {i s : PFact} {f : AFact} (h : check i f s = .triggered) :
    overlapB f.fact s = true := by
  cases ho : overlapB f.fact s with
  | true => rfl
  | false =>
    exfalso
    unfold check at h
    split at h <;> simp_all

/-- The motive of the old-rule invariant. -/
def OldInv : NObj → Prop
  | .ninit _ i => i = zeroFact
  | .nadded _ _ => False
  | .nreq _ _ _ => False
  | .npart .. => False
  | .nvuln _ _ _ b => b = true
  | .nedge _ _ _ f => InvB f = true

/-- THE OLD-RULE INVARIANT: in `DNz` on this program, every edge fact is the zero fact, a source
    fact, or the target in the demand layer; there is no request, no call, and every `vuln` is
    in the demand layer. -/
theorem old_inv {o : NObj} (h : DNz X o) : OldInv o := by
  induction h with
  | root _ => rfl
  | start _ ih =>
    show InvB (startFact _) = true
    rw [show _ = zeroFact from ih]
    decide
  | step _ hE hf ih => exact transfer_invB (stmt_cases hE) ih hf
  | reqStmt _ _ hq ih =>
    obtain ⟨t, ht⟩ := invB_conc ih
    rw [transfer_reqs_of_conc ht] at hq
    exact List.not_mem_nil hq
  | pass _ hE => exact (no_call hE).elim
  | added _ hE => exact (no_call hE).elim
  | initA _ ih => exact ih.elim
  | ret _ hE => exact (no_call hE).elim
  | ndOpen hE => exact (no_call hE).elim
  | ndBind _ _ _ _ _ ihp => exact ihp.elim
  | ndRet _ _ _ ih => exact ih.elim
  | reqSink _ _ hc ih =>
    obtain ⟨t, ht⟩ := invB_conc ih
    exact check_request_abs hc t ht
  | answer _ _ _ _ ihr => exact ihr.elim
  | reqUp _ _ _ _ _ _ _ _ ihr _ => exact ihr.elim
  | @vuln M P n f s i _ hs _ hc ih =>
    show f.demand = true
    have hs' : s = tgt := by
      cases hs with
      | head => rfl
      | tail _ h => cases h
    subst hs'
    exact invB_base3 ih (NDZeroBase.overlapB_base (check_overlap_of_trig hc))
  | clean _ hE => exact (no_clean hE).elim
  | reqClean _ hE => exact (no_clean hE).elim
  | filt _ hE => exact (no_filt hE).elim
  | @conj M P1 n f1 P2 f2 cj' n' _ _ hcj ho1 _ _ _ ih1 _ =>
    obtain ⟨-, -, rfl, -⟩ := conj_cases hcj
    have hx : f1.fact = xAny := invB_base1 ih1 (NDZeroBase.overlapB_base ho1)
    -- the literal does not cover the `.any` input: the old layer is demand
    have hcl : conjLayer cj f1 f2 = true := by
      unfold conjLayer
      rw [hx]
      have hcv : coversB cj.lit1 xAny = false := by decide
      rw [hcv]
      simp
    show InvB ⟨tgt, conjLayer cj f1 f2⟩ = true
    rw [hcl]
    decide
  | reqConj _ _ _ _ hg ih =>
    obtain ⟨t, ht⟩ := invB_conc ih
    exact gate_req_abs hg t ht

#print axioms old_inv

/-- UNDER THE OLD RULE every `vuln` of `DNz` at the sink is in the demand layer. -/
theorem old_vuln_demand {b : Bool} (h : DNz X (.nvuln 0 3 tgt b)) : b = true := old_inv h

#print axioms old_vuln_demand

/-- So the old rule does not confirm the vulnerability (`NDZeroThms.ConfirmedNz`), while the new
    rule does (`confirmed`). -/
theorem old_not_confirmed : ¬ ConfirmedNz X 0 3 tgt := fun h =>
  absurd (old_vuln_demand (confirmedNz_vuln h)) Bool.false_ne_true

#print axioms old_not_confirmed

end Example

end ApSpec.AnyTaintND
