/-
  ApSpec.AnyTaintCases — the WORKED PROGRAMS of the `[any-taint]` tail kind (decision F69).

  The test data of the spec: concrete programs, derivations in the closures (by the closure
  constructors, each step checked by `decide`), complete closures (an invariant over every object
  of a run, as `RCases.inv1` and `Backward.inv_b2` do), and `decide` vectors. The design brief is
  `any-taint/DESIGN.md` (§0 the user's decisions, §3.2 this file). The definitions are in
  `AnyTaintDefs.lean` (namespace `ApSpec.AnyTaint`).

  Numbers. Marks: `zeroMark = 0`, `T = 1`. Accessor `f = 1` (and `g = 2`). The field limit of
  every run is 3 (`cnt`: every accessor counts). Each CFG edge holds one statement.

  * PROGRAM G (the getter, the user's example; namespace `G`):
    ```
    root():  dto = srcAny();   // 0 -> 1: the taint edge zero.$ (zeroMark) -> dto.[any] (T)
             x = get(dto);     // 1 -> 2
             sinkAny(x);       // the sink pattern (x, [], [any], T) at node 2
    get(p):  return p.f;       // 0 -> 1: the micro edge p.f.* -> ret.*
    ```
    - (a) the old rule W6: run 1 (`W6.D6`) and run 3 (`W6.DR6` with the hand-off) report the
      vulnerability ONLY in the demand layer (`run1W6_vuln`, `run1W6_no_normal`, `run3W6_vuln`,
      `run3W6_no_normal`);
    - (b) run 1 with W6T (`D6T`): the vulnerability is in the demand layer only and it is not
      confirmed, because the FLOW summary of `ret = p.f` is case `above` (`run1T_flow_above`,
      `run1T_vuln`, `run1T_no_normal`, `run1T_not_confirmed`);
    - backward run 2 (`Backward.DB`, seeded at `sinkAny`) hands off EXACTLY the demand
      `(D-c = (p,[f],[any],T), D-p = (ret,[],[any],T))` of `get` and the zero demand
      (`handoff_exact`, `handoff_get`);
    - (c) forward run 3 with must-premises (`DRT`) and that hand-off: the added fact
      `(p,[],[any-taint],T)` emits the MUST premise `(p,[f],[any-taint],T)`, the sink edge in
      `root` is NORMAL, and `ConfirmedT` holds (`run3T_must`, `run3T_vuln_normal`,
      `run3T_confirmed`); the vulnerability is real (`vuln_real`).
    - the program is well-formed (`wf`, `bindNoAny`, `taintConc`); the must-premise of `get` is
      supported (`run3T_must_supported`).
  * PROGRAM C (the sink in the callee; namespace `C`): `root: dto = srcAny(); use(dto)`,
    `use(o): sinkAny(o.f)`. The backward run hands off `((o, [f], [any], T), none)`
    (`handoff_use`); run 3 confirms through the supported must-premise `(o, [f], [any-taint], T)`
    (`run3_must`, `run3_sink_normal`, `run3_supported`, `run3_confirmed`, `vuln_real`).
  * PROGRAM W (the strong write; namespace `W`): `root: dto = srcAny(); dto.f = cl;
    sink(dto.f)`. The keep edge `dto.*/{f} -> dto.*` puts the result `(dto,[],[any],T)` in the
    demand layer (`keep_demand`, the base `belowCase` rule), so the vulnerability is reported and
    not confirmed (`run1_vuln_demand`, `run1_not_confirmed`, `run3_vuln_demand`,
    `run3_not_confirmed`); a normal result would be a false normal edge (`keep_normal_false`,
    `keep_normal_not_endExact`) and would confirm a vulnerability that is not real
    (`vuln_not_real`, `keep_normal_confirms_unreal`).
  * PROGRAM P (the may pass rule; namespace `PassRule`): the same micro edge
    `P.$ (T) -> Q.[any] (T)` as a source (a taint edge) and as a pass rule (`source_vs_pass`):
    the source result is normal and confirmed in run 1 (`source_normal`, `source_confirmed`), the
    pass result is demand only and not confirmed (`pass_demand`, `pass_not_confirmed`).
  * THE EMISSION: the vectors of every cell of the table of decision 8 are
    `AnyTaint.EmitVec` (complete, with the `below` and `above` rows); here only the instances of
    the programs.
  * THE CUT (namespace `Cut`): an `[any-taint]` fact over the field limit becomes `[any]` in the
    demand layer (`cut_transfer`, `limitF_cut_demand`).

  FINDINGS (CEGAR). Every program behaves as the brief says; no program was changed to pass.
  * Run 1 cannot confirm `G`, with or without W6T: the run-1 FLOW summary of `ret = p.f` is case
    `above` (a demand edge), and its application keeps that layer (`run1T_no_normal`). Only the
    restricted run 3 (the must-premise from the demand) confirms `G` (`run3T_confirmed`).
  * In the base backward run `Backward.DB` the seed of the `[any]` sink pattern is a NORMAL
    `.any` edge (`Sx`); `AFact.complete` is false on it (an `.any` conclusion), so it is never a
    record: this agrees with decision 7. The hand-off patterns are `.any` in the model (the spec
    tail `[any-taint]` of `D-c`/`D-p` is a label, DESIGN §1).
  * Added hypotheses: `G.inv3W` (and so `G.run3W6_no_normal`) holds for every record set inside
    the complete run-1 records `recsList` (`G.recs1W_complete`: every complete exit edge of run 1
    is in it); an arbitrary record set could add a normal edge. `G.invB` bounds the backward
    demand by the reversed summaries of run 1 (`revDemG`, proved for both run-1 variants).

  All proofs are constructive (`propext`, `Quot.sound` only; see the `#print axioms` lines).
-/
import ApSpec.AnyTaintDefs
import ApSpec.Backward

namespace ApSpec.AnyTaintCases
open ApSpec ApSpec.AnyTaint

/-- The `*` tail with the empty exclusion. -/
def st : Kind := .star (.set [])
/-- Every accessor counts for the field limit. -/
def cnt : Acc → Bool := fun _ => true
/-- A demand (forward orientation). -/
abbrev Dem := MethodId → DemandEdge → Prop
/-- A record set with must flags (`DRT`). -/
abbrev TRecs := MethodId → PFact × Bool × AFact → Prop

/-! ## Program G: the getter -/

namespace G

/-! ### The program

  Bases: zero = 0, dto = 1, x = 2, p = 3, ret = 4. Methods: root = 0 (nodes 0, 1, 2; exit 2),
  get = 1 (nodes 0, 1; exit 1). -/

/-- The taint edge of `dto = srcAny()`: `zero.$ (zeroMark) → dto.[any] (T)`. -/
def srcE : MicroEdge := (zeroFact, ⟨1, [], .any, .conc 1⟩)
/-- `dto = srcAny()`: the zero fact is kept, `dto` is overwritten. -/
def srcS : Stmt := ⟨[0, 1], [(zeroFact, zeroFact), srcE]⟩
/-- The binding of `dto` into `p`, and of `ret` back into `x`. -/
def bIn : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
def bOut : MicroEdge := (⟨4, [], st, .star⟩, ⟨2, [], st, .star⟩)
/-- `x = get(dto)`. -/
def callGet : Call := ⟨1, [1, 2], [bIn], [bOut]⟩
/-- `return p.f`: the identity on `p` and the micro edge `p.f.* → ret.*`. -/
def getS : Stmt := ⟨[3, 4], [(⟨3, [], st, .star⟩, ⟨3, [], st, .star⟩),
  (⟨3, [1], st, .star⟩, ⟨4, [], st, .star⟩)]⟩
def prog : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 2,
  [(0, 0, .stmt srcS, 1), (0, 1, .call callGet, 2), (1, 0, .stmt getS, 1)]⟩
/-- The sink pattern of `sinkAny(x)`: `(x, [], [any], T)`. -/
def sinkP : PFact := ⟨2, [], .any, .conc 1⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sinkP)]
/-- The taint edges: the source edge only. -/
def taint : TaintEdges := fun e => decide (e = srcE)

/-- The CFG edges of program G. -/
theorem hE00 : (0, 0, Instr.stmt srcS, 1) ∈ prog.edges := List.Mem.head _
/-- The CFG edge of the call `x = get(dto)`. -/
theorem hE01 : (0, 1, Instr.call callGet, 2) ∈ prog.edges := List.Mem.tail _ (List.Mem.head _)
/-- The CFG edge of `return p.f`. -/
theorem hE10 : (1, 0, Instr.stmt getS, 1) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- Program G has no cleaner. -/
theorem no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

/-- Program G has no type filter. -/
theorem no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

/-- Program G is well-formed (`Program.WF`): every micro edge reads from a touched base, the call
    bindings are mark agnostic, and there is no type filter. -/
theorem wf : prog.WF := by
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
    exact (no_filt hE).elim

#print axioms wf

/-- No call binding of program G has an `.any` target (`AnyTaint.BindNoAny`, the hypothesis of
    the run-1 kinds invariant). -/
theorem bindNoAny : BindNoAny prog := by
  intro M n c n' hE
  cases hE with
  | tail _ hE => cases hE with
    | head =>
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · cases he with
        | head => rfl
        | tail _ he => cases he
      · cases he with
        | head => rfl
        | tail _ he => cases he
    | tail _ hE => cases hE with
      | tail _ hE => cases hE

#print axioms bindNoAny

/-- The only taint edge has the `.any` target, a concrete target mark and a concrete premise mark
    (`AnyTaint.TaintConc`). -/
theorem taintConc : TaintConc prog taint := by
  intro M n s n' hE e he ht
  cases hE with
  | head =>
    cases he with
    | head => cases ht
    | tail _ he => cases he with
      | head => exact ⟨rfl, ⟨1, rfl⟩, ⟨0, rfl⟩⟩
      | tail _ he => cases he
  | tail _ hE => cases hE with
    | tail _ hE => cases hE with
      | head =>
        cases he with
        | head => cases ht
        | tail _ he => cases he with
          | head => cases ht
          | tail _ he => cases he
      | tail _ hE => cases hE

#print axioms taintConc

/-! ### The facts -/

def Z : AFact := ⟨zeroFact, false⟩
/-- The source result `(dto, [], [any-taint], T)`: `.any` in the normal layer. -/
def DTO : AFact := ⟨⟨1, [], .any, .conc 1⟩, false⟩
/-- The same fact in the demand layer: `(dto, [], [any], T)` (W6). -/
def DTOd : AFact := ⟨DTO.fact, true⟩
/-- The added fact of `get`: `(p, [], [any], T)` (the fact of the link; its layer is the layer of
    the caller edge). -/
def Ap : PFact := ⟨3, [], .any, .conc 1⟩
/-- Run 1: the most abstract premise `(p, [], *, {}, *)` of `get` (`policy1`). -/
def J1 : PFact := ⟨3, [], st, .star⟩
def J1f : AFact := ⟨J1, false⟩
/-- Run 1: the FLOW summary conclusion `(ret, [], [any], *)` of `ret = p.f`, in the demand layer
    (case `above`: the premise `p` is above the read `p.f`). -/
def RET1 : AFact := ⟨⟨4, [], .any, .star⟩, true⟩
/-- The sink fact `(x, [], [any], T)` in the demand layer, and in the normal layer. -/
def Xd : AFact := ⟨⟨2, [], .any, .conc 1⟩, true⟩
def Xn : AFact := ⟨⟨2, [], .any, .conc 1⟩, false⟩
/-- Run 3: the premise of `get` emitted from the demand, `(p, [f], [any], T)` (= `D-c`). -/
def Jf : PFact := ⟨3, [1], .any, .conc 1⟩
def Jfd : AFact := ⟨Jf, true⟩
/-- `(ret, [], [any], T)` (= `D-p`, the backward premise of `get`). -/
def Jb : PFact := ⟨4, [], .any, .conc 1⟩
def RETn : AFact := ⟨Jb, false⟩
def RETd : AFact := ⟨Jb, true⟩
/-- THE DEMAND OF `get` (forward orientation): `D-c = (p, [f], [any], T)`,
    `D-p = (ret, [], [any], T)`. -/
def dGet : DemandEdge := ⟨Jf, some Jb⟩

/-! ### Run 1 with W6T (`D6T`), completely -/

/-- Run 1 with W6T: `policy1`, the field limit 3. -/
abbrev R1T : Obj → Prop := D6T prog taint cnt 3 policy1 sinks [0]

def inits1 : List (MethodId × PFact) := [(0, zeroFact), (1, J1)]
def edges1T : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, DTO), (0, zeroFact, 2, Z),
   (0, zeroFact, 2, Xd), (1, J1, 0, J1f), (1, J1, 1, J1f), (1, J1, 1, RET1)]
def addeds1 : List (MethodId × PFact) := [(1, Ap)]

/-- Every object of run 1 (W6T) is in the lists; no request; every vulnerability is in the demand
    layer. -/
def Inv1T : Obj → Prop
  | .init M i => (M, i) ∈ inits1
  | .edge M i n f => (M, i, n, f) ∈ edges1T
  | .added M a => (M, a) ∈ addeds1
  | .req _ _ _ => False
  | .vuln _ _ _ d => d = true

instance : DecidablePred Inv1T := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1T))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ d => inferInstanceAs (Decidable (d = true))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM G WITH W6T. -/
theorem inv1T {o : Obj} (h : R1T o) : Inv1T o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits1, Inv1T (.edge x.1 x.2 (prog.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferT taint cnt 3 srcS x.2.2.2).facts, Inv1T (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1T, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transferT taint cnt 3 getS x.2.2.2).facts, Inv1T (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transferT taint cnt 3 srcS x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1T, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transferT taint cnt 3 getS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callGet.touched = false → Inv1T (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callGet.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, Inv1T (.added callGet.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addeds1, Inv1T (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callGet.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ inits1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edges1T, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary a y.2 z.2.2.2).facts,
          ∀ e2 ∈ callGet.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            Inv1T (.edge 0 x.2.1 2 (limitF cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkP = .none ∨ check x.2.1 x.2.2.2 sinkP = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkP = .triggered → x.2.2.2.demand = true) (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1T

/-! ### Run 1 with W6T: the derivation and the theorems -/

-- the source result is `[any-taint]`: `.any` and normal (a taint edge keeps its layer)
example : (transferT taint cnt 3 srcS Z).facts = [Z, DTO] := by decide
-- the binding into `get` gives the added fact `(p, [], [any], T)` in the normal layer
example : (applyEdge DTO bIn.1 bIn.2).facts = [⟨Ap, false⟩] := by decide
-- run 1 serves it with the most abstract fact
example : policy1 1 Ap = J1 := by decide
-- THE FLOW SUMMARY OF `ret = p.f` IS CASE `above`: the micro edge reads `p.f`, the premise is `p`
example : relate [1] J1.path = .above [1] := rfl
example : aboveCase J1.kind st [1] [] st = some ([], .any, true) := by decide
example : (transferT taint cnt 3 getS J1f).facts = [J1f, RET1] := by decide
-- the application of the summary: the layer of the summary edge goes into the result
example : applicable J1 Ap = true := by decide
example : (applySummary ⟨Ap, false⟩ J1 RET1).facts = [RETd] := by decide
example : (applyEdge RETd bOut.1 bOut.2).facts = [Xd] := by decide
example : check zeroFact Xd sinkP = .triggered := by decide

/-- Run 1 (W6T): the source edge `zero → (dto, [], [any-taint], T)` is NORMAL. -/
theorem r1_e01 : R1T (.edge 0 zeroFact 1 DTO) :=
  D6T.step (D6T.start (D6T.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1: `policy1` serves the added fact `(p, [], [any], T)` with `(p, [], *, {}, *)`. -/
theorem r1_i1 : R1T (.init 1 J1) := by
  have h : R1T (.init 1 (policy1 1 Ap)) := D6T.initA (α := policy1)
    (D6T.added (c := callGet) (e := bIn) (a := ⟨Ap, false⟩) (P := prog) (taint := taint)
      (counted := cnt) (L := 3) (sinks := sinks) (roots := [0])
    r1_e01 hE01 (List.Mem.head _) (by decide))
  have hp : policy1 1 Ap = J1 := by decide
  rw [hp] at h
  exact h

/-- Run 1: the identity summary `(p, [], *, *) → (p, [], *, *)` of `get` (normal, complete). -/
theorem r1_exit_p : R1T (.edge 1 J1 1 J1f) := D6T.step (D6T.start r1_i1) hE10 (by decide)

/-- Run 1 (W6T): the FLOW summary of `get` is `(p, [], *, {}, *) → (ret, [], [any], *)` in the
    DEMAND layer (case `above`: the read `p.f` is below the premise `p`). -/
theorem run1T_flow_above : R1T (.edge 1 J1 1 RET1) :=
  D6T.step (D6T.start r1_i1) hE10 (by decide)

#print axioms run1T_flow_above

/-- Run 1: the application of the demand summary gives the sink edge
    `zero → (x, [], [any], T)` in the DEMAND layer. -/
theorem r1_e02 : R1T (.edge 0 zeroFact 2 Xd) :=
  D6T.ret (c := callGet) (e1 := bIn) (a := ⟨Ap, false⟩) (j := J1) (g := RET1) (r := RETd)
    (e2 := bOut) (r' := Xd) r1_e01 hE01 (List.Mem.head _) (by decide) r1_i1 (by decide)
    run1T_flow_above (by decide) (List.Mem.head _) (by decide)

/-- (b) Run 1 with W6T reports the vulnerability of `G`, in the DEMAND layer. -/
theorem run1T_vuln : R1T (.vuln 0 2 sinkP true) :=
  D6T.vuln r1_e02 (List.Mem.head _) (by decide)

#print axioms run1T_vuln

/-- (b) Run 1 with W6T has NO normal sink edge for `G`: the vulnerability is reported only in the
    demand layer. The source result is `[any-taint]` (normal), but the run-1 summary of `get`
    (`run1T_flow_above`) is a demand edge, and the application keeps its layer. -/
theorem run1T_no_normal : ¬ R1T (.vuln 0 2 sinkP false) := fun h => Bool.noConfusion (inv1T h)

#print axioms run1T_no_normal

/-- (b) Run 1 with W6T does not confirm `G` (`AnyTaint.ConfirmedT6`): no normal sink edge. -/
theorem run1T_not_confirmed : ¬ ConfirmedT6 prog taint cnt 3 policy1 sinks [0] 0 2 sinkP := by
  rintro ⟨i, f, hf, _, hd, hs, hc⟩
  have hv := D6T.vuln hf hs hc
  rw [hd] at hv
  exact run1T_no_normal hv

#print axioms run1T_not_confirmed

/-! ### Run 1 with W6 (the old rule), completely -/

/-- Run 1 with W6 (`W6.D6`): every `[any]` result goes to the demand layer. -/
abbrev R1W : Obj → Prop := W6.D6 prog cnt 3 policy1 sinks [0]

def edges1W : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, DTOd), (0, zeroFact, 2, Z),
   (0, zeroFact, 2, Xd), (1, J1, 0, J1f), (1, J1, 1, J1f), (1, J1, 1, RET1)]

/-- Every object of run 1 (W6) is in the lists; no request; every vulnerability is in the demand
    layer. -/
def Inv1W : Obj → Prop
  | .init M i => (M, i) ∈ inits1
  | .edge M i n f => (M, i, n, f) ∈ edges1W
  | .added M a => (M, a) ∈ addeds1
  | .req _ _ _ => False
  | .vuln _ _ _ d => d = true

instance : DecidablePred Inv1W := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1W))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ d => inferInstanceAs (Decidable (d = true))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM G WITH W6. -/
theorem inv1W {o : Obj} (h : R1W o) : Inv1W o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits1,
      Inv1W (.edge x.1 x.2 (prog.entry x.1) (W6.w6 (startFact x.2)))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 3 srcS x.2.2.2).facts, Inv1W (.edge 0 x.2.1 1 (W6.w6 f')))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1W, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 3 getS x.2.2.2).facts, Inv1W (.edge 1 x.2.1 1 (W6.w6 f')))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 3 srcS x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1W, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 3 getS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callGet.touched = false → Inv1W (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callGet.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, Inv1W (.added callGet.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addeds1, Inv1W (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callGet.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ inits1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edges1W, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary (W6.w6 a) y.2 z.2.2.2).facts,
          ∀ e2 ∈ callGet.fromCallee, ∀ r' ∈ (applyEdge (W6.w6 r) e2.1 e2.2).facts,
            Inv1W (.edge 0 x.2.1 2 (W6.w6 (limitF cnt 3 r'))))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkP = .none ∨ check x.2.1 x.2.2.2 sinkP = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkP = .triggered → x.2.2.2.demand = true) (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1W

-- W6 raises the source result: `(dto, [], [any], T)` in the demand layer
example : ((transfer cnt 3 srcS Z).facts.map W6.w6) = [Z, DTOd] := by decide

/-- Run 1 (W6): the source edge `zero → (dto, [], [any], T)` is a DEMAND edge. -/
theorem w1_e01 : R1W (.edge 0 zeroFact 1 DTOd) :=
  W6.D6.step (f' := DTO) (W6.D6.start (W6.D6.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1 (W6): the premise `(p, [], *, {}, *)` of `get`. -/
theorem w1_i1 : R1W (.init 1 J1) := by
  have h : R1W (.init 1 (policy1 1 Ap)) := W6.D6.initA (α := policy1)
    (W6.D6.added (c := callGet) (e := bIn) (a := ⟨Ap, true⟩) (P := prog) (counted := cnt)
      (L := 3) (sinks := sinks) (roots := [0])
    w1_e01 hE01 (List.Mem.head _) (by decide))
  have hp : policy1 1 Ap = J1 := by decide
  rw [hp] at h
  exact h

/-- Run 1 (W6): the identity summary of `get`. -/
theorem w1_exit_p : R1W (.edge 1 J1 1 J1f) :=
  W6.D6.step (f' := J1f) (W6.D6.start w1_i1) hE10 (by decide)

/-- Run 1 (W6): the FLOW summary `(p, [], *, *) → (ret, [], [any], *)` of `get`, demand. -/
theorem w1_exit_ret : R1W (.edge 1 J1 1 RET1) :=
  W6.D6.step (f' := RET1) (W6.D6.start w1_i1) hE10 (by decide)

/-- Run 1 (W6): the sink edge `zero → (x, [], [any], T)`, demand. -/
theorem w1_e02 : R1W (.edge 0 zeroFact 2 Xd) :=
  W6.D6.ret (c := callGet) (e1 := bIn) (a := ⟨Ap, true⟩) (j := J1) (g := RET1) (r := RETd)
    (e2 := bOut) (r' := Xd) w1_e01 hE01 (List.Mem.head _) (by decide) w1_i1 (by decide)
    w1_exit_ret (by decide) (List.Mem.head _) (by decide)

/-- (a) Run 1 with the old rule W6 reports the vulnerability of `G`, in the DEMAND layer. -/
theorem run1W6_vuln : R1W (.vuln 0 2 sinkP true) :=
  W6.D6.vuln w1_e02 (List.Mem.head _) (by decide)

#print axioms run1W6_vuln

/-- (a) Run 1 with W6 has NO normal sink edge for `G`. W6 puts the source result
    `(dto, [], [any], T)` in the demand layer, and every later result keeps that layer.
    FINDING (as expected, not a defect): without W6 (`D6T`, `run1T_no_normal`) run 1 has no normal
    sink edge either: the run-1 FLOW summary of `get` is case `above` (a demand edge), so run 1
    cannot confirm `G`; only the restricted run 3 can (`run3T_confirmed`). -/
theorem run1W6_no_normal : ¬ R1W (.vuln 0 2 sinkP false) := fun h => Bool.noConfusion (inv1W h)

#print axioms run1W6_no_normal

/-! ### Backward run 2 (`Backward.DB`), completely, and its hand-off

  The reversed program; the backward run is seeded at `sinkAny` (the sink that run 1 reported,
  `run1T_vuln`) and restricted by the reversed summaries of run 1. The zero fact starts at the
  forward exit `2` of `root`, the seed `(x, [], [any], T)` goes into `get` through the reversed
  binding back `x.* → ret.*`, and the backward demand `((ret, [], [any], *), D-p = (p, [], *, *))`
  (the reversed FLOW summary of run 1) emits the backward premise `(ret, [], [any], T)`. The
  reversed `ret = p.f` gives `(p, [f], [any], T)` at the forward entry of `get`: the backward
  summary `(ret, [], [any], T) → (p, [f], [any], T)`, the demand `dGet` of `get`. -/

def Pb : Program := Reverse.Program.rev prog

/-- The edges of the reversed program G. -/
theorem Pb_edges : Pb.edges =
    [(0, 1, .stmt (Reverse.Stmt.rev srcS), 0), (0, 2, .call (Reverse.Call.rev callGet), 1),
     (1, 1, .stmt (Reverse.Stmt.rev getS), 0)] := rfl

/-- The reversed CFG edges. -/
theorem hb_src : (0, 1, Instr.stmt (Reverse.Stmt.rev srcS), 0) ∈ Pb.edges := by
  rw [Pb_edges]; exact List.Mem.head _
theorem hb_c : (0, 2, Instr.call (Reverse.Call.rev callGet), 1) ∈ Pb.edges := by
  rw [Pb_edges]; exact List.Mem.tail _ (List.Mem.head _)
theorem hb_get : (1, 1, Instr.stmt (Reverse.Stmt.rev getS), 0) ∈ Pb.edges := by
  rw [Pb_edges]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- The reversed summaries of run 1 (with W6T or with W6: the same facts). -/
def revDemG : List (MethodId × DemandEdge) :=
  [(0, ⟨zeroFact, some zeroFact⟩), (0, ⟨Xd.fact, some zeroFact⟩), (1, ⟨J1, some J1⟩),
   (1, ⟨RET1.fact, some J1⟩)]

/-- The backward demand edge of `get` that the backward run uses: the reversed FLOW summary
    `((ret, [], [any], *), D-p = (p, [], *, {}, *))`. -/
def dRet : DemandEdge := ⟨RET1.fact, some J1⟩

/-- The reversed summaries of run 1 with W6T are in `revDemG`. -/
theorem revDemT_bound {m : MethodId} {d : DemandEdge}
    (h : Backward.revSummaryDemand prog R1T m d) : (m, d) ∈ revDemG := by
  obtain ⟨j, g, ⟨_, hor⟩, rfl⟩ := h
  rcases hor with h0 | ⟨g', hg', hgg⟩
  · cases h0
  · cases hgg
    exact (by decide : ∀ x ∈ edges1T, x.2.2.1 = prog.exit x.1 →
      (x.1, (⟨x.2.2.2.fact, some x.2.1⟩ : DemandEdge)) ∈ revDemG) (m, j, _, g') (inv1T hg') rfl

/-- The reversed summaries of run 1 with W6 are in `revDemG`. -/
theorem revDemW_bound {m : MethodId} {d : DemandEdge}
    (h : Backward.revSummaryDemand prog R1W m d) : (m, d) ∈ revDemG := by
  obtain ⟨j, g, ⟨_, hor⟩, rfl⟩ := h
  rcases hor with h0 | ⟨g', hg', hgg⟩
  · cases h0
  · cases hgg
    exact (by decide : ∀ x ∈ edges1W, x.2.2.1 = prog.exit x.1 →
      (x.1, (⟨x.2.2.2.fact, some x.2.1⟩ : DemandEdge)) ∈ revDemG) (m, j, _, g') (inv1W hg') rfl

/-- The reversed FLOW summary `dRet` of `get` is a reversed summary of run 1 with W6T. -/
theorem revDemT_get : Backward.revSummaryDemand prog R1T 1 dRet :=
  ⟨J1, RET1.fact, ⟨r1_i1, Or.inr ⟨RET1, run1T_flow_above, rfl⟩⟩, rfl⟩

/-- The reversed FLOW summary `dRet` of `get` is a reversed summary of run 1 with W6. -/
theorem revDemW_get : Backward.revSummaryDemand prog R1W 1 dRet :=
  ⟨J1, RET1.fact, ⟨w1_i1, Or.inr ⟨RET1, w1_exit_ret, rfl⟩⟩, rfl⟩

/-- Backward run 2 for a backward demand `demB`: the user's design on the reversed program,
    seeded at `sinkAny`, field limit 3, no backward record. -/
abbrev BG (demB : Dem) : Obj → Prop :=
  Backward.DB Pb cnt 3 demB emitM satI restrictU (fun _ _ => False) [] [0] sinks true

/-- The seed `(x, [], [any], T)` (the sink pattern; no cut). -/
def Sx : AFact := ⟨sinkP, false⟩
/-- `(dto, [f], [any], T)` before the call: the backward summary of `get` applied in `root`. -/
def Dd : AFact := ⟨⟨1, [1], .any, .conc 1⟩, true⟩
/-- The zero fact in the demand layer: the requirement reached the source. -/
def Zd : AFact := ⟨zeroFact, true⟩

def initsB : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (1, Jb)]
def edgesB : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, Backward.zeroAF), (0, zeroFact, 2, Sx), (0, zeroFact, 1, Backward.zeroAF),
   (0, zeroFact, 1, Dd), (0, zeroFact, 0, Backward.zeroAF), (0, zeroFact, 0, Zd),
   (1, zeroFact, 1, Backward.zeroAF), (1, zeroFact, 0, Backward.zeroAF), (1, Jb, 1, RETd),
   (1, Jb, 0, Jfd)]
def addedsB : List (MethodId × PFact) := [(1, Jb)]

def InvB : Obj → Prop
  | .init M i => (M, i) ∈ initsB
  | .edge M i n f => (M, i, n, f) ∈ edgesB
  | .added M a => (M, a) ∈ addedsB
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvB := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsB))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesB))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsB))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE BACKWARD RUN 2 OF PROGRAM G, for every backward demand inside the reversed
    summaries of run 1 (`revDemG`). -/
theorem invB (demB : Dem) (hb : ∀ m d, demB m d → (m, d) ∈ revDemG)
    {o : Obj} (h : BG demB o) : InvB o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsB, InvB (.edge x.1 x.2 (Pb.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [Pb_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer cnt 3 (Reverse.Stmt.rev srcS) x.2.2.2).facts, InvB (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesB, x.1 = 1 → x.2.2.1 = 1 →
            ∀ f' ∈ (transfer cnt 3 (Reverse.Stmt.rev getS) x.2.2.2).facts,
              InvB (.edge 1 x.2.1 0 f'))
            (1, i, 1, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [Pb_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer cnt 3 (Reverse.Stmt.rev srcS) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesB, x.1 = 1 → x.2.2.1 = 1 →
            ∀ t ∈ (transfer cnt 3 (Reverse.Stmt.rev getS) x.2.2.2).reqs, False)
            (1, i, 1, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Reverse.Call.rev callGet).touched = false →
            InvB (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Reverse.Call.rev callGet).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
            InvB (.added 1 a.fact))
          (0, i, 2, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    exact (by decide : ∀ x ∈ revDemG, ∀ y ∈ addedsB, x.1 = y.1 →
      ∀ j ∈ (emitM x.2.din y.2).toList, InvB (.init x.1 j))
      (m, d) (hb m d hd) (m, a) ih rfl j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Reverse.Call.rev callGet).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsB, y.1 = 1 →
          ∀ z ∈ edgesB, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 0 →
          ∀ dd ∈ revDemG, dd.1 = 1 → ∀ g' ∈ (restrictU y.2 z.2.2.2 dd.2).toList,
          satI y.2 a.fact = true →
          ∀ r ∈ (applySummary a y.2 g').facts,
          ∀ e2 ∈ (Reverse.Call.rev callGet).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvB (.edge 0 x.2.1 1 (limitF cnt 3 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl (1, j, 0, g) ihg rfl rfl rfl
          (1, d) (hb _ _ hd) rfl g' (RCases.mem_toList_of_eq_some hres) hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | retRec _ _ _ _ hrec _ _ _ _ _ => exact hrec.elim
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @seed M n s hs _ _ =>
    cases hs with
    | head => decide
    | tail _ h => cases h
  | @zret M n n' c g r e2 r' _ _ hE _ hr he2 hr' _ ihg =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesB, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary Backward.zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Reverse.Call.rev callGet).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvB (.edge 0 zeroFact 1 (limitF cnt 3 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

#print axioms invB

/-! #### The objects of backward run 2, derived -/

section DeriveB
variable (demB : Dem) (hd : demB 1 dRet)

/-- Backward run 2: the zero fact at the forward exit of `root`. -/
theorem b_e02 : BG demB (.edge 0 zeroFact 2 Backward.zeroAF) :=
  Backward.DB.start (Backward.DB.root (List.Mem.head _))
/-- The sink rule at the forward exit of `root`: the seed `(x, [], [any], T)`. -/
theorem b_s02 : BG demB (.edge 0 zeroFact 2 Sx) :=
  Backward.DB.seed (s := sinkP) (List.Mem.head _) (b_e02 demB)
/-- The requirement enters `get` through the reversed binding back (`x.* → ret.*`). -/
theorem b_ad : BG demB (.added 1 Jb) :=
  Backward.DB.added (c := Reverse.Call.rev callGet) (e := revEdge bOut.1 bOut.2) (a := RETn)
    (b_s02 demB) hb_c (List.Mem.head _) (by decide)

include hd in
/-- The backward demand `dRet` (the reversed FLOW summary of run 1) emits the backward premise
    `(ret, [], [any], T)`. -/
theorem b_iJb : BG demB (.init 1 Jb) := Backward.DB.initR (b_ad demB) hd (by decide)

include hd in
/-- The backward summary of `get`: `(ret, [], [any], T) → (p, [f], [any], T)` at the forward
    entry of `get`. -/
theorem b_eGb : BG demB (.edge 1 Jb 0 Jfd) :=
  Backward.DB.step (Backward.DB.start (b_iJb demB hd)) hb_get (by decide)

end DeriveB

/-! #### The hand-off, exactly -/

/-- The hand-off of program G: the demand `dGet` of `get` and the zero demand. -/
def demGM (m : MethodId) (d : DemandEdge) : Prop := d = Backward.zeroDem ∨ (m = 1 ∧ d = dGet)

def demListG : List (MethodId × DemandEdge) :=
  [(0, Backward.zeroDem), (1, Backward.zeroDem), (1, dGet)]

/-- The list `demListG` is inside `demGM`. -/
theorem demListG_cases {m : MethodId} {d : DemandEdge} (h : (m, d) ∈ demListG) : demGM m d := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ h => cases h with
    | head => exact Or.inl rfl
    | tail _ h => cases h with
      | head => exact Or.inr ⟨rfl, rfl⟩
      | tail _ h => cases h

/-- The demand edges of `demGM` (in every method). -/
theorem demGM_mem {m : MethodId} {d : DemandEdge} (h : demGM m d) :
    d ∈ [Backward.zeroDem, dGet] := by
  rcases h with rfl | ⟨_, rfl⟩
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)

/-- PROGRAM G, THE HAND-OFF EXACTLY. For every backward demand `demB` inside the reversed
    summaries of run 1 that has the reversed FLOW summary of `get`, the hand-off of backward run 2
    is the demand `dGet = ((p, [f], [any], T), some (ret, [], [any], T))` of `get` and the zero
    demand (no other demand edge of `root`: the requirement reached the source as the zero
    fact). -/
theorem handoff_exact (demB : Dem)
    (hb : ∀ m d, demB m d → (m, d) ∈ revDemG) (hd : demB 1 dRet) (m : MethodId)
    (d : DemandEdge) :
    Backward.demOf Pb (BG demB) m d ↔ demGM m d := by
  constructor
  · rintro (h | ⟨g, hg, rfl⟩ | ⟨jb, gb, hjb, hne, hgb, rfl⟩)
    · exact Or.inl h
    · have hz := (by decide : ∀ x ∈ edgesB, x.2.1 = zeroFact → x.2.2.1 = 0 →
        x.2.2.2.fact = zeroFact) (m, zeroFact, 0, g) (invB demB hb hg) rfl rfl
      exact Or.inl (by rw [hz]; rfl)
    · exact demListG_cases ((by decide : ∀ x ∈ initsB, x.2 ≠ zeroFact →
        ∀ y ∈ edgesB, y.1 = x.1 → y.2.1 = x.2 → y.2.2.1 = 0 →
          (x.1, (⟨y.2.2.2.fact, some x.2⟩ : DemandEdge)) ∈ demListG)
        (m, jb) (invB demB hb hjb) hne (m, jb, 0, gb) (invB demB hb hgb) rfl rfl rfl)
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨Jb, Jfd, b_iJb demB hd, by decide, b_eGb demB hd, rfl⟩)

#print axioms handoff_exact

/-- The hand-off after run 1 with W6T (the new iteration `D6T`, `DB`, `DRT`). -/
abbrev HT : MethodId → DemandEdge → Prop :=
  Backward.demOf Pb (BG (Backward.revSummaryDemand prog R1T))
/-- The hand-off after run 1 with W6 (the old iteration `D6`, `DB`, `DR6`). -/
abbrev HW : MethodId → DemandEdge → Prop :=
  Backward.demOf Pb (BG (Backward.revSummaryDemand prog R1W))

/-- The hand-off after run 1 with W6T is exactly `demGM`. -/
theorem HT_exact (m : MethodId) (d : DemandEdge) : HT m d ↔ demGM m d :=
  handoff_exact _ (fun _ _ h => revDemT_bound h) revDemT_get m d

/-- The hand-off after run 1 with W6 is exactly `demGM` (the same facts). -/
theorem HW_exact (m : MethodId) (d : DemandEdge) : HW m d ↔ demGM m d :=
  handoff_exact _ (fun _ _ h => revDemW_bound h) revDemW_get m d

/-- The hand-off (after run 1 with W6T) has THE DEMAND OF `get`:
    `(D-c = (p, [f], [any], T), D-p = (ret, [], [any], T))`. -/
theorem handoff_get : HT 1 dGet := (HT_exact 1 dGet).mpr (Or.inr ⟨rfl, rfl⟩)

#print axioms handoff_get

/-! ### Forward run 3 with the old rule W6 (`W6.DR6`), completely -/

/-- The complete exit edges of run 1 (the records a later run may reuse): `(zero → zero)` of
    `root` and `(p, [], *, *) → (p, [], *, *)` of `get`. -/
def recsList : List (MethodId × (PFact × AFact)) := [(0, (zeroFact, Z)), (1, (J1, J1f))]

/-- Every complete exit edge of run 1 (W6) is in `recsList`. -/
theorem recs1W_complete {m : MethodId} {j : PFact} {g : AFact}
    (h : R1W (.edge m j (prog.exit m) g)) (hc : g.complete = true) : (m, (j, g)) ∈ recsList :=
  (by decide : ∀ x ∈ edges1W, x.2.2.1 = prog.exit x.1 → x.2.2.2.complete = true →
    (x.1, (x.2.1, x.2.2.2)) ∈ recsList) (m, j, _, g) (inv1W h) rfl hc

#print axioms recs1W_complete

/-- Run 3 with W6 for a demand and a record set. -/
abbrev R3W (demand : Dem) (recs : MethodId → PFact × AFact → Prop) :
    Obj → Prop :=
  W6.DR6 prog cnt 3 demand emitM satI restrictU recs sinks [0]

def inits3 : List (MethodId × PFact) := [(0, zeroFact), (1, Jf)]
def edges3W : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, DTOd), (0, zeroFact, 2, Z),
   (0, zeroFact, 2, Xd), (1, Jf, 0, Jfd), (1, Jf, 1, Jfd), (1, Jf, 1, RETd)]

def Inv3W : Obj → Prop
  | .init M i => (M, i) ∈ inits3
  | .edge M i n f => (M, i, n, f) ∈ edges3W
  | .added M a => (M, a) ∈ addeds1
  | .req _ _ _ => False
  | .vuln _ _ _ d => d = true

instance : DecidablePred Inv3W := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits3))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges3W))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ d => inferInstanceAs (Decidable (d = true))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 3 OF PROGRAM G WITH W6, for every demand inside the hand-off (`demGM`) and
    every record set inside the complete run-1 records (`recsList`). -/
theorem inv3W (demand : Dem) (recs : MethodId → PFact × AFact → Prop)
    (hd : ∀ m d, demand m d → demGM m d) (hr : ∀ m jg, recs m jg → (m, jg) ∈ recsList)
    {o : Obj} (h : R3W demand recs o) : Inv3W o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits3,
      Inv3W (.edge x.1 x.2 (prog.entry x.1) (W6.w6 (startFact x.2)))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges3W, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 3 srcS x.2.2.2).facts, Inv3W (.edge 0 x.2.1 1 (W6.w6 f')))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges3W, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 3 getS x.2.2.2).facts, Inv3W (.edge 1 x.2.1 1 (W6.w6 f')))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges3W, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 3 srcS x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges3W, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 3 getS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3W, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callGet.touched = false → Inv3W (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3W, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callGet.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, Inv3W (.added callGet.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hdm he ih =>
    exact (by decide : ∀ y ∈ addeds1, ∀ dd ∈ [Backward.zeroDem, dGet],
      ∀ j ∈ (emitM dd.din y.2).toList, Inv3W (.init y.1 j))
      (m, a) ih d (demGM_mem (hd m d hdm)) j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ hdm hres hsat hrr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3W, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callGet.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ inits3, y.1 = 1 →
          ∀ z ∈ edges3W, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ dd ∈ [Backward.zeroDem, dGet], ∀ g' ∈ (restrictU y.2 z.2.2.2 dd).toList,
          satI y.2 a.fact = true →
          ∀ r ∈ (applySummary (W6.w6 a) y.2 (W6.w6 g')).facts,
          ∀ e2 ∈ callGet.fromCallee, ∀ r' ∈ (applyEdge (W6.w6 r) e2.1 e2.2).facts,
            Inv3W (.edge 0 x.2.1 2 (W6.w6 (limitF cnt 3 r'))))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl (1, j, 1, g) ihg rfl rfl rfl
          d (demGM_mem (hd _ d hdm)) g' (RCases.mem_toList_of_eq_some hres) hsat r hrr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hsa hrr he2 hr' ihf =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3W, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callGet.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ q ∈ recsList, q.1 = 1 →
          (satI q.2.1 a.fact = true ∨ applicable q.2.1 a.fact = true) →
          ∀ r ∈ (applySummary (W6.w6 a) q.2.1 q.2.2).facts,
          ∀ e2 ∈ callGet.fromCallee, ∀ r' ∈ (applyEdge (W6.w6 r) e2.1 e2.2).facts,
            Inv3W (.edge 0 x.2.1 2 (W6.w6 (limitF cnt 3 r'))))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, (j, g)) (hr _ _ hrec) rfl hsa r hrr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edges3W, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkP = .none ∨ check x.2.1 x.2.2.2 sinkP = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges3W, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkP = .triggered → x.2.2.2.demand = true) (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv3W

section Run3W
variable (recs : MethodId → PFact × AFact → Prop)

/-- Run 3 (W6): the source edge, demand. -/
theorem w3_e01 : R3W HW recs (.edge 0 zeroFact 1 DTOd) :=
  W6.DR6.step (f' := DTO) (W6.DR6.start (W6.DR6.root (List.Mem.head _))) hE00 (by decide)

/-- Run 3 (W6): the emission gives the premise `(p, [f], [any], T)` of `get`. -/
theorem w3_iJ : R3W HW recs (.init 1 Jf) :=
  W6.DR6.initR (d := dGet)
    (W6.DR6.added (c := callGet) (e := bIn) (a := ⟨Ap, true⟩) (w3_e01 recs) hE01
      (List.Mem.head _) (by decide))
    ((HW_exact 1 dGet).mpr (Or.inr ⟨rfl, rfl⟩)) (by decide)

/-- Run 3 (W6): the summary `(p, [f], [any], T) → (ret, [], [any], T)`, demand. -/
theorem w3_eJ1 : R3W HW recs (.edge 1 Jf 1 RETd) :=
  W6.DR6.step (f' := RETd) (W6.DR6.start (w3_iJ recs)) hE10 (by decide)

/-- Run 3 (W6): the sink edge `zero → (x, [], [any], T)`, demand. -/
theorem w3_e02 : R3W HW recs (.edge 0 zeroFact 2 Xd) :=
  W6.DR6.ret (c := callGet) (e1 := bIn) (a := ⟨Ap, true⟩) (j := Jf) (g := RETd) (d := dGet)
    (g' := RETd) (r := RETd) (e2 := bOut) (r' := Xd) (w3_e01 recs) hE01 (List.Mem.head _)
    (by decide) (w3_iJ recs) (w3_eJ1 recs) ((HW_exact 1 dGet).mpr (Or.inr ⟨rfl, rfl⟩))
    (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

/-- (a) Run 3 with W6 and the hand-off of the old iteration (`HW`) reports the vulnerability of
    `G`, in the DEMAND layer (for every record set). -/
theorem run3W6_vuln : R3W HW recs (.vuln 0 2 sinkP true) :=
  W6.DR6.vuln (w3_e02 recs) (List.Mem.head _) (by decide)

#print axioms run3W6_vuln

/-- (a) Run 3 with W6 and the hand-off has NO normal sink edge for `G` (for every record set
    inside the complete run-1 records): W6 keeps the source result `(dto, [], [any], T)` in the
    demand layer, so every later result is a demand result. -/
theorem run3W6_no_normal (hr : ∀ m jg, recs m jg → (m, jg) ∈ recsList) :
    ¬ R3W HW recs (.vuln 0 2 sinkP false) :=
  fun h => Bool.noConfusion (inv3W HW recs (fun m d h => (HW_exact m d).mp h) hr h)

#print axioms run3W6_no_normal

end Run3W

/-! ### Forward run 3 with must-premises (`DRT`): the vulnerability is CONFIRMED -/

-- THE EMISSION: the `[any-taint]` added fact `(p, [], [any-taint], T)` (normal on the link)
-- against `D-c = (p, [f], [any], T)` gives the MUST premise `(p, [f], [any-taint], T)`
-- (decision 8, row `above`, the tail of the added fact)
example : emitT dGet.din Ap true = some (Jf, true) := by decide
-- the same added fact in the demand layer (`[any]`) gives the may premise `(p, [f], [any], T)`
example : emitT dGet.din Ap false = some (Jf, false) := by decide
-- a must-premise starts in the NORMAL layer (`startT`); `startFact` puts it in the demand layer
example : startT Jf true = ⟨Jf, false⟩ := rfl
example : startFact Jf = Jfd := by decide
-- `ret = p.f` on the must-premise: `(ret, [], [any-taint], T)`, normal
example : (transferT taint cnt 3 getS ⟨Jf, false⟩).facts = [⟨Jf, false⟩, RETn] := by decide
-- the restriction by `D-p = (ret, [], [any], T)` keeps it; the caller fact satisfies the premise
example : restrictU Jf RETn dGet = some RETn := by decide
example : satI Jf Ap = true := by decide
-- the application and the binding back: `(x, [], [any-taint], T)`, normal; the sink triggers
example : (applySummary ⟨Ap, false⟩ Jf RETn).facts = [RETn] := by decide
example : (applyEdge RETn bOut.1 bOut.2).facts = [Xn] := by decide
example : limitF cnt 3 Xn = Xn := by decide
example : check zeroFact Xn sinkP = .triggered := by decide

/-- Run 3 with must-premises, for a demand and a record set. -/
abbrev R3T (demand : Dem) (recs : TRecs) :
    TObj → Prop :=
  DRT prog taint cnt 3 demand emitM satI restrictU recs sinks [0]

section Run3T
variable (demand : Dem) (recs : TRecs)
  (hd : demand 1 dGet)

/-- The source result in `root`: `(dto, [], [any-taint], T)`, NORMAL (a taint edge). -/
theorem t3_e01 : R3T demand recs (.edge 0 zeroFact false 1 DTO) :=
  DRT.step (DRT.start (DRT.root (List.Mem.head _))) hE00 (by decide)

/-- The added fact of `get` is `[any-taint]` on its link (`am = true`). -/
theorem t3_ad : R3T demand recs (.added 1 Ap true) :=
  DRT.added (c := callGet) (e := bIn) (a := ⟨Ap, false⟩) (t3_e01 demand recs) hE01
    (List.Mem.head _) (by decide)

include hd in
/-- (c) The emission of the added fact `(p, [], [any-taint], T)` with the demand `dGet` gives the
    MUST premise `(p, [f], [any-taint], T)` of `get`. -/
theorem run3T_must : R3T demand recs (.init 1 Jf true) :=
  DRT.initR (d := dGet) (t3_ad demand recs) hd (by decide)

#print axioms run3T_must

include hd in
/-- The summary of the must-premise: `(p, [f], [any-taint], T) → (ret, [], [any-taint], T)`,
    normal. -/
theorem t3_eJ1 : R3T demand recs (.edge 1 Jf true 1 RETn) :=
  DRT.step (DRT.start (run3T_must demand recs hd)) hE10 (by decide)

include hd in
/-- (c) THE SINK EDGE IN `root` IS NORMAL: `zero → (x, [], [any-taint], T)` at the sink node. -/
theorem run3T_sink_normal : R3T demand recs (.edge 0 zeroFact false 2 Xn) :=
  DRT.ret (c := callGet) (e1 := bIn) (a := ⟨Ap, false⟩) (j := Jf) (mj := true) (g := RETn)
    (d := dGet) (g' := RETn) (r := RETn) (e2 := bOut) (r' := Xn) (t3_e01 demand recs) hE01
    (List.Mem.head _) (by decide) (run3T_must demand recs hd) (t3_eJ1 demand recs hd) hd
    (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms run3T_sink_normal

include hd in
/-- (c) Run 3 reports the vulnerability of `G` in the NORMAL layer. -/
theorem run3T_vuln_normal : R3T demand recs (.vuln 0 2 sinkP false) :=
  DRT.vuln (run3T_sink_normal demand recs hd) (List.Mem.head _) (by decide)

#print axioms run3T_vuln_normal

include hd in
/-- (c) RUN 3 CONFIRMS PROGRAM G (`AnyTaint.ConfirmedT`): a normal sink edge under the supported
    zero premise of the root, with a triggered check. For every demand that has the demand `dGet`
    of `get` and every record set. -/
theorem run3T_confirmed :
    ConfirmedT prog taint cnt 3 demand emitM satI restrictU recs sinks [0] 0 2 sinkP :=
  ⟨zeroFact, false, Xn, run3T_sink_normal demand recs hd, SupT.root (List.Mem.head _), rfl,
    List.Mem.head _, by decide⟩

#print axioms run3T_confirmed

end Run3T

/-- (c) THE ITERATION `D6T` → `DB` → `DRT` CONFIRMS PROGRAM G: forward run 3 with the hand-off of
    backward run 2 (`HT`, restricted by the reversed summaries of run 1 with W6T) confirms the
    vulnerability, for every record set. -/
theorem run3T_confirmed_handoff (recs : TRecs) :
    ConfirmedT prog taint cnt 3 HT emitM satI restrictU recs sinks [0] 0 2 sinkP :=
  run3T_confirmed HT recs handoff_get

#print axioms run3T_confirmed_handoff

/-- The must-premise of `get` in run 3 is SUPPORTED (`AnyTaint.SupT`): the normal source edge of
    `root` binds the `[any-taint]` fact `(p, [], [any-taint], T)`, and the premise
    `(p, [f], [any-taint], T)` lies inside it with its mark (`SupLink`, the must case). -/
theorem run3T_must_supported (demand : Dem)
    (recs : TRecs) (hd : demand 1 dGet) :
    SupT prog taint cnt 3 demand emitM satI restrictU recs sinks [0] 1 Jf true :=
  SupT.call (c := callGet) (e := bIn) (a := ⟨Ap, false⟩) (SupT.root (List.Mem.head _))
    (t3_e01 demand recs) rfl hE01 (List.Mem.head _) (by decide) rfl (run3T_must demand recs hd)
    (Or.inr (Or.inr ⟨rfl, ⟨1, rfl⟩, rfl, by decide, Or.inr ⟨rfl, rfl⟩⟩))

#print axioms run3T_must_supported

/-! ### The vulnerability is real -/

/-- The pair relations on the witness of program G. -/
theorem den_src : den srcE.1 srcE.2 zeroLoc ⟨1, [1], 1⟩ :=
  ⟨rfl, rfl, rfl, rfl, trivial, [], [1], rfl, rfl, rfl, trivial⟩
theorem den_in : den bIn.1 bIn.2 ⟨1, [1], 1⟩ ⟨3, [1], 1⟩ :=
  ⟨rfl, rfl, trivial, rfl, trivial, [1], [1], rfl, rfl, rfl, rfl, rfl⟩
theorem den_rd :
    den (⟨3, [1], st, .star⟩ : PFact) ⟨4, [], st, .star⟩ ⟨3, [1], 1⟩ ⟨4, [], 1⟩ :=
  ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩
theorem den_out : den bOut.1 bOut.2 ⟨4, [], 1⟩ ⟨2, [], 1⟩ :=
  ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩

/-- The vulnerability of `G` is REAL: the source taints `dto.f` (every location of `dto`), `get`
    returns it into `x`, and the sink pattern `(x, [], [any], T)` covers `x`. -/
theorem vuln_real : Reach prog [0] 0 2 ⟨2, [], 1⟩ ∧ sinkP.covers ⟨2, [], 1⟩ := by
  have f0 : Flow prog 0 zeroLoc 1 ⟨1, [1], 1⟩ :=
    Flow.step (Flow.start 0 zeroLoc) hE00
      (Or.inr ⟨srcE, List.Mem.tail _ (List.Mem.head _), den_src⟩)
  have fc : Flow prog 1 ⟨3, [1], 1⟩ 1 ⟨4, [], 1⟩ :=
    Flow.step (Flow.start 1 _) hE10 (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_rd⟩)
  exact ⟨Reach.root (List.Mem.head _)
    (Flow.call f0 hE01 (List.Mem.head _) den_in fc (List.Mem.head _) den_out),
    ⟨rfl, ⟨[], rfl, trivial⟩, rfl⟩⟩

#print axioms vuln_real

end G

/-! ## Program C: the sink in the callee

```
root():  dto = srcAny();  use(dto);     // 0 -> 1 -> 2
use(o):  sinkAny(o.f);                  // the sink (o, [f], [any], T) at node 0 (entry = exit)
```
  Bases: zero = 0, dto = 1, o = 2. Methods: root = 0 (exit 2), use = 1 (entry = exit = 0). The
  demand of `use` is `(D-c = (o, [f], [any], T), none)`: the sink is in `use`, the demand does not
  reach the exit. The backward run gives it for every backward demand (`handoff_use`). -/

namespace C

def bUse : MicroEdge := (⟨1, [], st, .star⟩, ⟨2, [], st, .star⟩)
/-- `use(dto)`: no binding back. -/
def callUse : Call := ⟨1, [1], [bUse], []⟩
def prog : Program := ⟨fun _ => 0, fun m => if m = 1 then 0 else 2,
  [(0, 0, .stmt G.srcS, 1), (0, 1, .call callUse, 2)]⟩
/-- The sink pattern of `sinkAny(o.f)`: `(o, [f], [any], T)`. -/
def sinkP : PFact := ⟨2, [1], .any, .conc 1⟩
def sinks : List (MethodId × Node × PFact) := [(1, 0, sinkP)]
/-- THE DEMAND OF `use`: `(D-c = (o, [f], [any], T), none)`. -/
def dUse : DemandEdge := ⟨sinkP, none⟩
/-- The added fact `(o, [], [any], T)` and the must-premise `(o, [f], [any-taint], T)`. -/
def Ao : PFact := ⟨2, [], .any, .conc 1⟩
def Jo : PFact := ⟨2, [1], .any, .conc 1⟩

/-- The CFG edges of program C. -/
theorem hE00 : (0, 0, Instr.stmt G.srcS, 1) ∈ prog.edges := List.Mem.head _
theorem hE01 : (0, 1, Instr.call callUse, 2) ∈ prog.edges := List.Mem.tail _ (List.Mem.head _)

-- the binding gives the `[any-taint]` added fact; the emission gives the must-premise
example : (applyEdge G.DTO bUse.1 bUse.2).facts = [⟨Ao, false⟩] := by decide
example : emitT dUse.din Ao true = some (Jo, true) := by decide
example : startT Jo true = ⟨Jo, false⟩ := rfl
-- the sink triggers on the NORMAL start fact of the must-premise
example : check Jo ⟨Jo, false⟩ sinkP = .triggered := by decide

/-- Run 3 with must-premises of program C. -/
abbrev R3 (demand : Dem) (recs : TRecs) :
    TObj → Prop :=
  DRT prog G.taint cnt 3 demand emitM satI restrictU recs sinks [0]

section Run3
variable (demand : Dem) (recs : TRecs)
  (hd : demand 1 dUse)

/-- Run 3 of C: the source edge `zero → (dto, [], [any-taint], T)`, normal. -/
theorem c_e01 : R3 demand recs (.edge 0 zeroFact false 1 G.DTO) :=
  DRT.step (DRT.start (DRT.root (List.Mem.head _))) hE00 (by decide)

include hd in
/-- The must-premise `(o, [f], [any-taint], T)` of `use`. -/
theorem run3_must : R3 demand recs (.init 1 Jo true) :=
  DRT.initR (d := dUse)
    (DRT.added (c := callUse) (e := bUse) (a := ⟨Ao, false⟩) (c_e01 demand recs) hE01
      (List.Mem.head _) (by decide)) hd (by decide)

#print axioms run3_must

include hd in
/-- The sink edge in `use` is NORMAL: the start fact of the must-premise. -/
theorem run3_sink_normal : R3 demand recs (.edge 1 Jo true 0 ⟨Jo, false⟩) :=
  DRT.start (run3_must demand recs hd)

#print axioms run3_sink_normal

include hd in
/-- The must-premise is supported: `(o, [f], [any-taint], T)` lies inside the normal
    `[any-taint]` binding `(o, [], [any-taint], T)` of the normal source edge of `root`. -/
theorem run3_supported :
    SupT prog G.taint cnt 3 demand emitM satI restrictU recs sinks [0] 1 Jo true :=
  SupT.call (c := callUse) (e := bUse) (a := ⟨Ao, false⟩) (SupT.root (List.Mem.head _))
    (c_e01 demand recs) rfl hE01 (List.Mem.head _) (by decide) rfl (run3_must demand recs hd)
    (Or.inr (Or.inr ⟨rfl, ⟨1, rfl⟩, rfl, by decide, Or.inr ⟨rfl, rfl⟩⟩))

#print axioms run3_supported

include hd in
/-- RUN 3 CONFIRMS PROGRAM C (`AnyTaint.ConfirmedT`): the normal sink edge in `use`, under the
    supported must-premise `(o, [f], [any-taint], T)`, with a triggered check. For every demand
    that has `dUse` and every record set. -/
theorem run3_confirmed :
    ConfirmedT prog G.taint cnt 3 demand emitM satI restrictU recs sinks [0] 1 0 sinkP :=
  ⟨Jo, true, ⟨Jo, false⟩, run3_sink_normal demand recs hd, run3_supported demand recs hd, rfl,
    List.Mem.head _, by decide⟩

#print axioms run3_confirmed

end Run3

/-! ### The hand-off of the backward run (derived) -/

def Pb : Program := Reverse.Program.rev prog

/-- The edges of the reversed program C. -/
theorem Pb_edges : Pb.edges =
    [(0, 1, .stmt (Reverse.Stmt.rev G.srcS), 0), (0, 2, .call (Reverse.Call.rev callUse), 1)] :=
  rfl

/-- The reversed call of `use`. -/
theorem hb_c : (0, 2, Instr.call (Reverse.Call.rev callUse), 1) ∈ Pb.edges := by
  rw [Pb_edges]; exact List.Mem.tail _ (List.Mem.head _)

/-- The backward run of program C (the user's design, seeded at `sinkAny(o.f)`). -/
abbrev BC (demB : Dem) (recsB : MethodId → PFact × AFact → Prop) :
    Obj → Prop :=
  Backward.DB Pb cnt 3 demB emitM satI restrictU recsB [] [0] sinks true

/-- The zero fact enters `use` and the sink rule seeds `(o, [f], [any], T)` at its forward entry. -/
theorem b_s10 (demB : Dem) (recsB : MethodId → PFact × AFact → Prop) :
    BC demB recsB (.edge 1 zeroFact 0 ⟨sinkP, false⟩) :=
  Backward.DB.seed (s := sinkP) (List.Mem.head _)
    (Backward.DB.start (Backward.DB.zin (c := Reverse.Call.rev callUse) rfl
      (Backward.DB.start (Backward.DB.root (List.Mem.head _))) hb_c))

/-- The hand-off of the backward run has the demand `dUse = ((o, [f], [any], T), none)` of
    `use`, for every backward demand and record set. -/
theorem handoff_use (demB : Dem)
    (recsB : MethodId → PFact × AFact → Prop) :
    Backward.demOf Pb (BC demB recsB) 1 dUse :=
  Or.inr (Or.inl ⟨⟨sinkP, false⟩, b_s10 demB recsB, rfl⟩)

#print axioms handoff_use

/-- Run 3 with the hand-off confirms program C. -/
theorem run3_confirmed_handoff (demB : Dem)
    (recsB : MethodId → PFact × AFact → Prop) (recs : TRecs) :
    ConfirmedT prog G.taint cnt 3 (Backward.demOf Pb (BC demB recsB)) emitM satI restrictU recs
      sinks [0] 1 0 sinkP :=
  run3_confirmed _ recs (handoff_use demB recsB)

#print axioms run3_confirmed_handoff

/-- The vulnerability of program C is real: `dto.f` is tainted, `o.f` is it, and the sink
    pattern covers it. -/
theorem vuln_real : Reach prog [0] 1 0 ⟨2, [1], 1⟩ ∧ sinkP.covers ⟨2, [1], 1⟩ := by
  have f0 : Flow prog 0 zeroLoc 1 ⟨1, [1], 1⟩ :=
    Flow.step (Flow.start 0 zeroLoc) hE00
      (Or.inr ⟨G.srcE, List.Mem.tail _ (List.Mem.head _), G.den_src⟩)
  have hd : den bUse.1 bUse.2 ⟨1, [1], 1⟩ ⟨2, [1], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [1], [1], rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨Reach.down (Reach.root (List.Mem.head _) f0) hE01 (List.Mem.head _) hd
    (Flow.start 1 _), ⟨rfl, ⟨[], rfl, trivial⟩, rfl⟩⟩

#print axioms vuln_real

end C

/-! ## Program W: the strong write

```
root():  dto = srcAny();   // 0 -> 1: zero.$ -> dto.[any] (T), a taint edge
         dto.f = cl;       // 1 -> 2: the keep edge dto.*/{f} -> dto.*, and cl.* -> dto.f.*
         sink(dto.f);      // the sink pattern (dto, [f], $, T) at node 2
```
  Bases: zero = 0, dto = 1, cl = 5 (never tainted). The keep edge of the strong write has the
  exclusion `{f}`: on `(dto, [], [any-taint], T)` the base rule `belowCase` gives
  `(dto, [], [any], T)` in the DEMAND layer (the exclusion is not Empty; decision 5, "demote").
  The model is right to demote: `dto.f` is overwritten by the untainted `cl`, so the location
  `(dto, [f], T)` of the fact is NOT reached at node 2, and a normal `[any-taint]` result would be
  a false normal edge that confirms a vulnerability that is not real. -/

namespace W

/-- The keep edge of `dto.f = cl` (the shape of `Cases.storeF`). -/
def keepE : MicroEdge := (⟨1, [], .star (.set [1]), .star⟩, ⟨1, [], st, .star⟩)
def wrS : Stmt := ⟨[1, 5], [keepE, (⟨5, [], st, .star⟩, ⟨5, [], st, .star⟩),
  (⟨5, [], st, .star⟩, ⟨1, [1], st, .star⟩)]⟩
def prog : Program := ⟨fun _ => 0, fun _ => 2, [(0, 0, .stmt G.srcS, 1), (0, 1, .stmt wrS, 2)]⟩
/-- The sink pattern of `sink(dto.f)`: `(dto, [f], $, T)`. -/
def sinkP : PFact := ⟨1, [1], .exact, .conc 1⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sinkP)]

/-- The CFG edges of program W. -/
theorem hE00 : (0, 0, Instr.stmt G.srcS, 1) ∈ prog.edges := List.Mem.head _
theorem hE01 : (0, 1, Instr.stmt wrS, 2) ∈ prog.edges := List.Mem.tail _ (List.Mem.head _)

/-- Program W has no call, no cleaner and no type filter. -/
theorem no_call {M n c n'} (h : (M, n, Instr.call c, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

theorem no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

theorem no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

-- the base rule: `belowCase` at the premise position with the exclusion `{f}` sets the demand bit
example : belowCase .any (.star (.set [1])) [] [] st = some ([], .any, true) := by decide

/-- THE KEEP EDGE DEMOTES: the strong write `dto.f = cl` on the `[any-taint]` fact
    `(dto, [], [any-taint], T)` gives `(dto, [], [any], T)` in the DEMAND layer (and nothing
    else; the keep edge is not an `.any`-target edge, so W6T does not read it). -/
theorem keep_demand : (transferT G.taint cnt 3 wrS G.DTO).facts = [G.DTOd] := by decide

#print axioms keep_demand

/-! ### Run 1 (`D6T`), completely: the vulnerability is reported, not confirmed -/

abbrev R1 : Obj → Prop := D6T prog G.taint cnt 3 policy1 sinks [0]

def edges1 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, G.Z), (0, zeroFact, 1, G.Z), (0, zeroFact, 1, G.DTO), (0, zeroFact, 2, G.Z),
   (0, zeroFact, 2, G.DTOd)]

def Inv1 : Obj → Prop
  | .init M i => (M, i) = (0, zeroFact)
  | .edge M i n f => (M, i, n, f) ∈ edges1
  | .added _ _ => False
  | .req _ _ _ => False
  | .vuln _ _ _ d => d = true

instance : DecidablePred Inv1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) = (0, zeroFact)))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1))
  | .added _ _ => inferInstanceAs (Decidable False)
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ d => inferInstanceAs (Decidable (d = true))

/-- THE COMPLETE RUN 1 OF PROGRAM W (W6T). -/
theorem inv1 {o : Obj} (h : R1 o) : Inv1 o := by
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
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2).facts, Inv1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ f' ∈ (transferT G.taint cnt 3 wrS x.2.2.2).facts, Inv1 (.edge 0 x.2.1 2 f'))
          (0, i, 1, f) ih rfl rfl f' hf
      | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ t ∈ (transferT G.taint cnt 3 wrS x.2.2.2).reqs, False) (0, i, 1, f) ih rfl rfl t ht
      | tail _ hE => cases hE
  | pass _ hE _ _ => exact (no_call hE).elim
  | added _ hE _ _ _ => exact (no_call hE).elim
  | initA _ ih => exact ih.elim
  | ret _ hE _ _ _ _ _ _ _ _ _ _ _ => exact (no_call hE).elim
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkP = .none ∨ check x.2.1 x.2.2.2 sinkP = .triggered)
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
        check x.2.1 x.2.2.2 sinkP = .triggered → x.2.2.2.demand = true) (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1

/-- Run 1 reports the vulnerability of W in the DEMAND layer. -/
theorem run1_vuln_demand : R1 (.vuln 0 2 sinkP true) :=
  D6T.vuln (D6T.step (D6T.step (D6T.start (D6T.root (List.Mem.head _))) hE00 (by decide)
    (f' := G.DTO)) hE01
    (by decide) (f' := G.DTOd)) (List.Mem.head _) (by decide)

#print axioms run1_vuln_demand

/-- Run 1 does NOT confirm the vulnerability of W: every sink edge is a demand edge. -/
theorem run1_not_confirmed : ¬ ConfirmedT6 prog G.taint cnt 3 policy1 sinks [0] 0 2 sinkP := by
  rintro ⟨i, f, hf, _, hd, hs, hc⟩
  have hv := inv1 (D6T.vuln hf hs hc)
  rw [hd] at hv
  exact Bool.noConfusion hv

#print axioms run1_not_confirmed

/-! ### Run 3 (`DRT`), completely, for every demand and record set -/

abbrev R3 (demand : Dem) (recs : TRecs) :
    TObj → Prop :=
  DRT prog G.taint cnt 3 demand emitM satI restrictU recs sinks [0]

def edges3 : List (MethodId × PFact × Bool × Node × AFact) :=
  edges1.map (fun x => (x.1, x.2.1, false, x.2.2.1, x.2.2.2))

def Inv3 : TObj → Prop
  | .init M j mj => (M, j, mj) = (0, zeroFact, false)
  | .edge M j mj n f => (M, j, mj, n, f) ∈ edges3
  | .added _ _ _ => False
  | .req _ _ _ => False
  | .vuln _ _ _ d => d = true

instance : DecidablePred Inv3 := fun o =>
  match o with
  | .init M j mj => inferInstanceAs (Decidable ((M, j, mj) = (0, zeroFact, false)))
  | .edge M j mj n f => inferInstanceAs (Decidable ((M, j, mj, n, f) ∈ edges3))
  | .added _ _ _ => inferInstanceAs (Decidable False)
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ d => inferInstanceAs (Decidable (d = true))

/-- THE COMPLETE RUN 3 OF PROGRAM W (with must-premises), for every demand and record set (the
    program has no call, so no demand and no record is read). -/
theorem inv3 (demand : Dem) (recs : TRecs)
    {o : TObj} (h : R3 demand recs o) : Inv3 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M j mj _ ih =>
    cases ih
    decide
  | @step M i mi n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 0 →
        ∀ f' ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2.2).facts,
          Inv3 (.edge 0 x.2.1 x.2.2.1 1 f'))
        (0, i, mi, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 1 →
          ∀ f' ∈ (transferT G.taint cnt 3 wrS x.2.2.2.2).facts,
            Inv3 (.edge 0 x.2.1 x.2.2.1 2 f'))
          (0, i, mi, 1, f) ih rfl rfl f' hf
      | tail _ hE => cases hE
  | @reqStmt M i mi n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 0 →
        ∀ t ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2.2).reqs, False)
        (0, i, mi, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 1 →
          ∀ t ∈ (transferT G.taint cnt 3 wrS x.2.2.2.2).reqs, False)
          (0, i, mi, 1, f) ih rfl rfl t ht
      | tail _ hE => cases hE
  | pass _ hE _ _ => exact (no_call hE).elim
  | added _ hE _ _ _ => exact (no_call hE).elim
  | initR _ _ _ ih => exact ih.elim
  | ret _ hE _ _ _ _ _ _ _ _ _ _ _ _ _ => exact (no_call hE).elim
  | retRec _ hE _ _ _ _ _ _ _ _ => exact (no_call hE).elim
  | @reqSink M i mi n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 2 →
        check x.2.1 x.2.2.2.2 sinkP = .none ∨ check x.2.1 x.2.2.2.2 sinkP = .triggered)
        (0, i, mi, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i mi n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 2 →
        check x.2.1 x.2.2.2.2 sinkP = .triggered → x.2.2.2.2.demand = true)
        (0, i, mi, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv3

/-- Run 3 reports the vulnerability of W in the DEMAND layer. -/
theorem run3_vuln_demand (demand : Dem)
    (recs : TRecs) : R3 demand recs (.vuln 0 2 sinkP true) :=
  DRT.vuln (DRT.step (DRT.step (DRT.start (DRT.root (List.Mem.head _))) hE00 (by decide)
    (f' := G.DTO)) hE01
    (by decide) (f' := G.DTOd)) (List.Mem.head _) (by decide)

#print axioms run3_vuln_demand

/-- Run 3 does NOT confirm the vulnerability of W, for every demand and record set. -/
theorem run3_not_confirmed (demand : Dem)
    (recs : TRecs) :
    ¬ ConfirmedT prog G.taint cnt 3 demand emitM satI restrictU recs sinks [0] 0 2 sinkP := by
  rintro ⟨i, mi, f, hf, _, hd, hs, hc⟩
  have hv := inv3 demand recs (DRT.vuln hf hs hc)
  rw [hd] at hv
  exact Bool.noConfusion hv

#print axioms run3_not_confirmed

/-! ### A normal result would be a false normal edge -/

/-- The locations that reach the nodes of `root` from the zero location: the zero location, and
    after the source the locations of `dto` with the mark `T`; after the write, not below `dto.f`. -/
def InvF (n : Node) (l : Loc) : Prop :=
  l = zeroLoc ∨ (n ≠ 0 ∧ l.base = 1 ∧ l.mark = 1 ∧ (n = 2 → ∀ τ, l.path ≠ 1 :: τ))

/-- THE REACHING LOCATIONS of `root` (`InvF`): every location that the zero location of `root`
    reaches at a node. -/
theorem flow_inv {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (h : Flow prog M l0 n l) :
    M = 0 → l0 = zeroLoc → InvF n l := by
  induction h with
  | start M l0 => exact fun _ h0 => Or.inl h0
  | @step M l0 n l n' l' s _ hE hs ih =>
    intro hM h0
    have ih' := ih hM h0
    subst hM
    cases hE with
    | head =>
      rcases ih' with rfl | ⟨hn, _⟩
      · rcases hs with ⟨hm, _⟩ | ⟨e, he, hd⟩
        · exact absurd hm (by decide)
        · cases he with
          | head =>
            left
            obtain ⟨lb, lp, lm⟩ := l'
            obtain ⟨_, hb, _, hmk, _, σ, τ, _, hp, _, hτ⟩ := hd
            change lb = 0 at hb
            change lm = 0 at hmk
            change lp = [] ++ τ at hp
            change τ = [] at hτ
            subst hb hmk hτ
            rw [hp]
            rfl
          | tail _ he => cases he with
            | head =>
              obtain ⟨_, hb, _, hmk, _⟩ := hd
              exact Or.inr ⟨by decide, hb, hmk, fun h => absurd h (by decide)⟩
            | tail _ he => cases he
      · exact absurd rfl hn
    | tail _ hE => cases hE with
      | head =>
        rcases ih' with rfl | ⟨_, hb, hm, _⟩
        · rcases hs with ⟨_, hl⟩ | ⟨e, he, hd⟩
          · exact Or.inl hl
          · cases he with
            | head => exact absurd hd.1 (by decide)
            | tail _ he => cases he with
              | head => exact absurd hd.1 (by decide)
              | tail _ he => cases he with
                | head => exact absurd hd.1 (by decide)
                | tail _ he => cases he
        · rcases hs with ⟨hm', _⟩ | ⟨e, he, hd⟩
          · rw [hb] at hm'; exact absurd hm' (by decide)
          · cases he with
            | head =>
              obtain ⟨_, hb', _, hmk, _, σ, τ, _, hτp, hσ, hτ⟩ := hd
              refine Or.inr ⟨by decide, hb', ?_, ?_⟩
              · rw [hmk, ← hm]; rfl
              · intro _ τ' hp'
                rw [hτp, hτ.1] at hp'
                have hs' : σ = 1 :: τ' := hp'
                change Excl.admits (.set [1]) σ = true at hσ
                rw [hs'] at hσ
                have hf : Excl.admits (.set [1]) (1 :: τ') = false := rfl
                rw [hf] at hσ
                exact Bool.noConfusion hσ
            | tail _ he => cases he with
              | head => exact absurd (hd.1.symm.trans hb) (by decide)
              | tail _ he => cases he with
                | head => exact absurd (hd.1.symm.trans hb) (by decide)
                | tail _ he => cases he
      | tail _ hE => cases hE
  | pass _ hE _ _ => exact (no_call hE).elim
  | call _ hE _ _ _ _ _ _ _ => exact (no_call hE).elim
  | clean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms flow_inv

/-- The location `(dto, [f], T)` is NOT reached at the sink node: `dto.f` was overwritten by the
    untainted `cl`. -/
theorem not_reached : ¬ Flow prog 0 zeroLoc 2 ⟨1, [1], 1⟩ := by
  intro h
  rcases flow_inv h rfl rfl with h' | ⟨_, _, _, hp⟩
  · exact absurd h' (by decide)
  · exact hp rfl [] rfl

#print axioms not_reached

/-- A witness of program W is a flow in `root` (no call). -/
theorem reach_flow {M : MethodId} {n : Node} {l : Loc} (h : Reach prog [0] M n l) :
    Flow prog M zeroLoc n l := by
  cases h with
  | root _ hf => exact hf
  | down _ hE _ _ _ => exact (no_call hE).elim

/-- The vulnerability of W is NOT real: no location of the sink pattern `(dto, [f], $, T)` is
    reached at the sink node. -/
theorem vuln_not_real : ∀ l, sinkP.covers l → ¬ Reach prog [0] 0 2 l := by
  intro l hc hr
  obtain ⟨lb, lp, lm⟩ := l
  obtain ⟨hb, ⟨σ, hp, hσ⟩, hm⟩ := hc
  change lb = 1 at hb
  change lp = [1] ++ σ at hp
  change σ = [] at hσ
  change lm = 1 at hm
  subst hb hσ hm
  rw [hp] at hr
  exact not_reached (reach_flow hr)

#print axioms vuln_not_real

/-- A NORMAL KEEP RESULT WOULD BE A FALSE NORMAL EDGE. The edge `zero → (dto, [], [any-taint], T)`
    at node 2 (the keep result left normal) relates the zero location to `(dto, [f], T)`, which is
    not reached: it is not pair-exact (`RExact.EdgeOKR`, the motive of a non-must normal edge). -/
theorem keep_normal_false :
    den zeroFact G.DTO.fact zeroLoc ⟨1, [1], 1⟩ ∧ ¬ Flow prog 0 zeroLoc 2 ⟨1, [1], 1⟩ ∧
    ¬ RExact.EdgeOKR prog (fun _ => True) (.edge 0 zeroFact 2 G.DTO) := by
  have hd : den zeroFact G.DTO.fact zeroLoc ⟨1, [1], 1⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [1], rfl, rfl, rfl, trivial⟩
  exact ⟨hd, not_reached, fun h => not_reached ((h rfl).2 zeroLoc _ hd trivial).1⟩

#print axioms keep_normal_false

/-- The same edge is not END-EXACT either (`AnyTaint.EndExact`, the `[any-taint]` meaning: every
    location of the conclusion comes from a location of the premise). -/
theorem keep_normal_not_endExact : ¬ EndExact prog (fun _ => True) 0 zeroFact 2 G.DTO.fact := by
  intro h
  obtain ⟨l0, hc0, hf, _⟩ :=
    h ⟨1, [1], 1⟩ ⟨rfl, ⟨[1], rfl, trivial⟩, 1, rfl, rfl⟩ trivial
  obtain ⟨lb, lp, lm⟩ := l0
  obtain ⟨hb, ⟨σ, hp, hσ⟩, hm⟩ := hc0
  change lb = 0 at hb
  change lp = [] ++ σ at hp
  change σ = [] at hσ
  change lm = 0 at hm
  subst hb hσ hm
  rw [hp] at hf
  exact not_reached hf

#print axioms keep_normal_not_endExact

/-- A normal keep result would CONFIRM A VULNERABILITY THAT IS NOT REAL: its sink check
    triggers, and no location of the sink pattern is reached. -/
theorem keep_normal_confirms_unreal :
    check zeroFact G.DTO sinkP = .triggered ∧ ∀ l, sinkP.covers l → ¬ Reach prog [0] 0 2 l :=
  ⟨by decide, vuln_not_real⟩

#print axioms keep_normal_confirms_unreal

end W

/-! ## Program P: the may pass rule

```
root():  p = src();        // 0 -> 1: zero.$ -> P.$ (T)
         q = f(p);         // 1 -> 2: the micro edge P.$ (T) -> Q.[any] (T)
         sinkAny(q);       // the sink pattern (Q, [], [any], T) at node 2
```
  Bases: zero = 0, P = 1, Q = 2. The same micro edge read as a SOURCE (a conditional source with
  an `[any]` target, a must: a taint edge) and as a PASS RULE (an `AnyField` target, a may; not a
  taint edge, decision 3). -/

namespace PassRule

def srcP : Stmt := ⟨[0, 1], [(zeroFact, zeroFact), (zeroFact, ⟨1, [], .exact, .conc 1⟩)]⟩
/-- The micro edge `P.$ (T) → Q.[any] (T)`. -/
def eQ : MicroEdge := (⟨1, [], .exact, .conc 1⟩, ⟨2, [], .any, .conc 1⟩)
def qS : Stmt := ⟨[1, 2], [(⟨1, [], st, .star⟩, ⟨1, [], st, .star⟩), eQ]⟩
def prog : Program := ⟨fun _ => 0, fun _ => 2, [(0, 0, .stmt srcP, 1), (0, 1, .stmt qS, 2)]⟩
def sinkP : PFact := ⟨2, [], .any, .conc 1⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sinkP)]
/-- The micro edge read as a source: a taint edge. -/
def asSource : TaintEdges := fun e => decide (e = eQ)
/-- The micro edge read as a pass rule: no taint edge. -/
def asPass : TaintEdges := fun _ => false

def Pf : AFact := ⟨⟨1, [], .exact, .conc 1⟩, false⟩
/-- `(Q, [], [any-taint], T)` (normal) and `(Q, [], [any], T)` (demand). -/
def Qn : AFact := ⟨⟨2, [], .any, .conc 1⟩, false⟩
def Qd : AFact := ⟨⟨2, [], .any, .conc 1⟩, true⟩

/-- The CFG edges of program P. -/
theorem hE00 : (0, 0, Instr.stmt srcP, 1) ∈ prog.edges := List.Mem.head _
theorem hE01 : (0, 1, Instr.stmt qS, 2) ∈ prog.edges := List.Mem.tail _ (List.Mem.head _)

/-- THE SAME MICRO EDGE, TWO LAYERS: as a source the result is `(Q, [], [any-taint], T)` in the
    NORMAL layer; as a pass rule W6T puts it in the DEMAND layer (`(Q, [], [any], T)`). -/
theorem source_vs_pass :
    (transferT asSource cnt 3 qS Pf).facts = [Pf, Qn] ∧
    (transferT asPass cnt 3 qS Pf).facts = [Pf, Qd] := by decide

#print axioms source_vs_pass

/-- Run 1: `p = src()` gives `(P, [], $, T)` (read as a source). -/
theorem src_e01S : D6T prog asSource cnt 3 policy1 sinks [0] (.edge 0 zeroFact 1 Pf) :=
  D6T.step (D6T.start (D6T.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1: `p = src()` gives `(P, [], $, T)` (read as a pass rule). -/
theorem src_e01P : D6T prog asPass cnt 3 policy1 sinks [0] (.edge 0 zeroFact 1 Pf) :=
  D6T.step (D6T.start (D6T.root (List.Mem.head _))) hE00 (by decide)

/-- As a source: run 1 (`D6T`) has the NORMAL edge `zero → (Q, [], [any-taint], T)`. -/
theorem source_normal : D6T prog asSource cnt 3 policy1 sinks [0] (.edge 0 zeroFact 2 Qn) :=
  D6T.step src_e01S hE01 (by decide)

#print axioms source_normal

/-- As a source: run 1 CONFIRMS the vulnerability (`AnyTaint.ConfirmedT6`): a normal sink edge
    under the zero premise. -/
theorem source_confirmed : ConfirmedT6 prog asSource cnt 3 policy1 sinks [0] 0 2 sinkP :=
  ⟨zeroFact, Qn, source_normal, Sup6T.root (List.Mem.head _), rfl, List.Mem.head _, by decide⟩

#print axioms source_confirmed

/-- As a pass rule: run 1 has the DEMAND edge `zero → (Q, [], [any], T)`. -/
theorem pass_demand : D6T prog asPass cnt 3 policy1 sinks [0] (.edge 0 zeroFact 2 Qd) :=
  D6T.step src_e01P hE01 (by decide)

#print axioms pass_demand

/-- Program P has no call, no cleaner and no type filter. -/
theorem no_call {M n c n'} (h : (M, n, Instr.call c, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

theorem no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

theorem no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

def edgesPass : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, G.Z), (0, zeroFact, 1, G.Z), (0, zeroFact, 1, Pf), (0, zeroFact, 2, G.Z),
   (0, zeroFact, 2, Pf), (0, zeroFact, 2, Qd)]

def InvPass : Obj → Prop
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

/-- THE COMPLETE RUN 1 OF PROGRAM P WITH THE PASS RULE. -/
theorem invPass {o : Obj} (h : D6T prog asPass cnt 3 policy1 sinks [0] o) : InvPass o := by
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
        ∀ f' ∈ (transferT asPass cnt 3 srcP x.2.2.2).facts, InvPass (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesPass, x.1 = 0 → x.2.2.1 = 1 →
          ∀ f' ∈ (transferT asPass cnt 3 qS x.2.2.2).facts, InvPass (.edge 0 x.2.1 2 f'))
          (0, i, 1, f) ih rfl rfl f' hf
      | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesPass, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transferT asPass cnt 3 srcP x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesPass, x.1 = 0 → x.2.2.1 = 1 →
          ∀ t ∈ (transferT asPass cnt 3 qS x.2.2.2).reqs, False) (0, i, 1, f) ih rfl rfl t ht
      | tail _ hE => cases hE
  | pass _ hE _ _ => exact (no_call hE).elim
  | added _ hE _ _ _ => exact (no_call hE).elim
  | initA _ ih => exact ih.elim
  | ret _ hE _ _ _ _ _ _ _ _ _ _ _ => exact (no_call hE).elim
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edgesPass, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 sinkP = .none ∨ check x.2.1 x.2.2.2 sinkP = .triggered)
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
        check x.2.1 x.2.2.2 sinkP = .triggered → x.2.2.2.demand = true) (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms invPass

/-- As a pass rule: run 1 does NOT confirm the vulnerability (a may `[any]` stays demand). -/
theorem pass_not_confirmed : ¬ ConfirmedT6 prog asPass cnt 3 policy1 sinks [0] 0 2 sinkP := by
  rintro ⟨i, f, hf, _, hd, hs, hc⟩
  have hv := invPass (D6T.vuln hf hs hc)
  rw [hd] at hv
  exact Bool.noConfusion hv

#print axioms pass_not_confirmed

end PassRule

/-! ## The emission

  The vectors of EVERY CELL of the table of decision 8, with the `below` and the `above` rows,
  are `AnyTaint.EmitVec` (in `AnyTaintDefs.lean`); they are complete and not repeated here. The
  instances in the programs: `G` (`emitT dGet.din Ap true = some (Jf, true)`, the `above` row with
  an `[any-taint]` added fact; with an `[any]` added fact the premise is not must) and `C`
  (`emitT dUse.din Ao true = some (Jo, true)`). -/

/-! ## The cut: an `[any-taint]` fact over the field limit becomes `[any]` (demand) -/

namespace Cut

/-- `dto.f.g = srcAny()`: the taint edge `zero.$ → dto.f.g.[any] (T)`. -/
def srcE : MicroEdge := (zeroFact, ⟨1, [1, 2], .any, .conc 1⟩)
def srcS : Stmt := ⟨[0, 1], [(zeroFact, zeroFact), srcE]⟩
def taint : TaintEdges := fun e => decide (e = srcE)

-- the field limit 1 cuts `(dto, [f, g], [any-taint], T)` to `(dto, [f], [any], T)` in the DEMAND
-- layer; the field limit 2 keeps it, normal
example : limitF cnt 1 ⟨⟨1, [1, 2], .any, .conc 1⟩, false⟩ =
    ⟨⟨1, [1], .any, .conc 1⟩, true⟩ := by decide
example : limitF cnt 2 ⟨⟨1, [1, 2], .any, .conc 1⟩, false⟩ =
    ⟨⟨1, [1, 2], .any, .conc 1⟩, false⟩ := by decide
-- the same for a `$` fact (the base rule)
example : limitF cnt 1 ⟨⟨1, [1, 2], .exact, .conc 1⟩, false⟩ =
    ⟨⟨1, [1], .any, .conc 1⟩, true⟩ := by decide
-- an accessor that does not count does not cut
example : limitF (fun a => a == 1) 1 ⟨⟨1, [1, 2], .any, .conc 1⟩, false⟩ =
    ⟨⟨1, [1, 2], .any, .conc 1⟩, false⟩ := by decide

/-- THE CUT IN THE TRANSFER: the source `dto.f.g = srcAny()` under the field limit 1 gives
    `(dto, [f], [any], T)` in the DEMAND layer; under the field limit 2 it gives
    `(dto, [f, g], [any-taint], T)` in the normal layer. -/
theorem cut_transfer :
    (transferT taint cnt 1 srcS ⟨zeroFact, false⟩).facts =
      [⟨zeroFact, false⟩, ⟨⟨1, [1], .any, .conc 1⟩, true⟩] ∧
    (transferT taint cnt 2 srcS ⟨zeroFact, false⟩).facts =
      [⟨zeroFact, false⟩, ⟨⟨1, [1, 2], .any, .conc 1⟩, false⟩] := by decide

#print axioms cut_transfer

/-- The cut always demotes: a fact whose path is over the limit becomes an `.any` fact in the
    demand layer (so an `[any-taint]` fact becomes `[any]`). -/
theorem limitF_cut_demand {counted : Acc → Bool} {L : Nat} {f : AFact} {p : List Acc}
    (h : cutPath counted L f.fact.path = some p) :
    limitF counted L f = ⟨⟨f.fact.base, p, .any, f.fact.mark⟩, true⟩ := by
  unfold limitF
  rw [h]

#print axioms limitF_cut_demand

end Cut

end ApSpec.AnyTaintCases

/-! # Programs I and S (appended)

  Two more worked programs, each in its own namespace, with the numbers and the conventions of
  the programs above (marks `zeroMark = 0`, `T = 1`; the field limit 3 with `cnt`; one statement
  per CFG edge; the source of `G`, `G.srcS`, and its taint edge `G.taint`).

  * PROGRAM I (the identity callee; namespace `I`): `root: dto = srcAny(); x = id(dto);
    sinkAny(x)`, `id(p): return p`. Run 1 with W6T (`D6T`, `policy1`) has the FLOW summary
    `(p, [], *, *) → (ret, [], *, *)` of `id` in the normal layer (`run1T_flow`); its application
    to the `[any-taint]` added fact `(p, [], [any-taint], T)` gives `(x, [], [any-taint], T)` in
    the NORMAL layer (`app_normal`, `run1T_sink_normal`), so run 1 CONFIRMS
    (`run1T_confirmed`); the complete run has no demand report (`inv1T`, `run1T_no_demand`); the
    vulnerability is real (`vuln_real`). For contrast, the old rule W6 (`W6.D6`) reports it ONLY in
    the demand layer (`inv1W`, `run1W6_vuln`, `run1W6_no_normal`).
  * PROGRAM S (the setter record, decision 5; namespace `S`): `root: dto = srcAny();
    dto.setName(c); sink(dto.name); sink(dto.email)`, `setName(n): this.name = n`. Run 1 makes the
    record `(this, [], *, *) → (this, [], */{name}, *)` (`run1_record`, `recs1_complete`); applied
    to `(this, [], [any-taint], T)` it gives `(this, [], [any], T)` in the DEMAND layer (the
    exclusion `{name}`, `belowCase`; `record_app_demand`). Backward run 2 hands off exactly the
    demand `((this, [email], $, T), (this, [email], $, T))` of `setName` and the zero demand
    (`handoff_exact`, `HT_exact`). Forward run 3 (`DRT`) with that demand and the record:
    `sink(dto.name)` is a DEMAND entry only (`run3_name_demand`, `run3_name_no_normal`,
    `run3_name_not_confirmed`), it comes only from the record (`run3_name_needs_record`), and it
    is not real (`name_not_real`); `sink(dto.email)` has a NORMAL sink edge through the restricted
    summary of `setName` and is CONFIRMED (`run3_email_sink_normal`, `run3_email_confirmed`,
    `run3_handoff`), also with the `.any` form of the demand (a must-premise;
    `run3A_email_confirmed`); it is real (`email_real`).

  FINDINGS (CEGAR). Both programs behave as the brief says; no program was changed to pass.
  * I: the FLOW summary of `ret = p` is case `below r = []` (in `G` the read `p.f` is case
    `above`), so W6T alone makes run 1 confirm; no restricted run is necessary.
  * S: run 1 reports BOTH sinks in the demand layer only (`run1_vulns`, `run1_no_normal`): the
    demoted record result `(dto, [], [any], T)` covers `dto.email` too (the accepted precision
    loss). The next forward run repairs it for `dto.email` through the demand. In run 3 the email
    sink is in both layers (normal by the restricted summary, demand by the record:
    `run3_email_demand`).
  * S: the backward run gives no demand for `this.name` (the exclusion of the reversed record
    rejects the requirement `(this, [name], $, T)`), so the demand entry of `sink(dto.name)` stays
    in every forward run that reads the record (R4), and no run confirms or removes it.
  * S: the demand from the backward run has the `$` tail (the sink pattern is `$`): the premise
    `(this, [email], $, T)` is not a must-premise, and the normal result comes from case `above`
    with an `[any-taint]` added fact (nothing is lost). The `.any` form gives the must-premise
    `(this, [email], [any-taint], T)` (supported: `run3A_must_supported`).
  * Hypotheses: the complete run-3 invariants (`S.inv3`, `S.inv3N`) hold for every demand inside
    `demS` and every record set inside the run-1 records `recsList`; with the derived hand-off
    `HT` (`run3_handoff`) only the record set is fixed (`recsS`). `S.invB` bounds the backward
    demand by the reversed summaries of run 1 (`revDemS`). No other hypothesis.

  All proofs are constructive (`propext`, `Quot.sound` only; see the `#print axioms` lines). -/

namespace ApSpec.AnyTaintCases
open ApSpec ApSpec.AnyTaint

/-! ## Program I: the identity callee (run 1 confirms)

```
root():  dto = srcAny();   // 0 -> 1: the taint edge zero.$ (zeroMark) -> dto.[any] (T)
         x = id(dto);      // 1 -> 2
         sinkAny(x);       // the sink pattern (x, [], [any], T) at node 2
id(p):   return p;         // 0 -> 1: ret = p, the micro edge p.* -> ret.*
```
  Bases: zero = 0, dto = 1, x = 2, p = 3, ret = 4 (as in `G`). Methods: root = 0 (nodes 0, 1, 2;
  exit 2), id = 1 (nodes 0, 1; exit 1). The program is `G` with `return p` in place of
  `return p.f`.

  What it shows:
  * run 1 with W6T (`D6T`, the run-1 policy `policy1`): the run-1 FLOW summary of `id` is
    `(p, [], *, *) → (ret, [], *, *)` in the NORMAL layer (`run1T_flow`; a complete edge, a
    record). The micro edge `p.* → ret.*` is case `below r = []`, so nothing is lost;
  * its application to the added fact `(p, [], [any-taint], T)` (`.any`, normal on the link) is
    case `below r = []` with a `*` target and the Empty exclusion: the result is
    `(ret, [], [any-taint], T)` in the NORMAL layer (ap.md §4.1 step 3, the row `*`, `[]`,
    `[any-taint]`), and the binding back gives `(x, [], [any-taint], T)`, NORMAL
    (`app_normal`, `run1T_sink_normal`);
  * so the sink edge is normal and run 1 CONFIRMS the vulnerability (`run1T_vuln_normal`,
    `run1T_confirmed`, `AnyTaint.ConfirmedT6`); the complete run 1 has no demand-layer report
    (`inv1T`, `run1T_no_demand`); the vulnerability is real (`vuln_real`);
  * for contrast, the old rule W6 (`W6.D6`) puts the source result `(dto, [], [any], T)` in the
    demand layer, so the same vulnerability is reported ONLY in the demand layer: no normal sink
    edge (`inv1W`, `run1W6_vuln`, `run1W6_no_normal`). -/

namespace I

/-! ### The program -/

/-- `x = id(dto)`: the binding `dto.* → p.*` and the binding back `ret.* → x.*` (those of `G`). -/
def callId : Call := ⟨1, [1, 2], [G.bIn], [G.bOut]⟩
/-- `return p` (`ret = p`): the identity on `p` and the micro edge `p.* → ret.*`. -/
def idS : Stmt := ⟨[3, 4], [(⟨3, [], st, .star⟩, ⟨3, [], st, .star⟩),
  (⟨3, [], st, .star⟩, ⟨4, [], st, .star⟩)]⟩
/-- Program I: `root` (method 0) and `id` (method 1). -/
def prog : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 2,
  [(0, 0, .stmt G.srcS, 1), (0, 1, .call callId, 2), (1, 0, .stmt idS, 1)]⟩

/-- The CFG edge of `dto = srcAny()`. -/
theorem hE00 : (0, 0, Instr.stmt G.srcS, 1) ∈ prog.edges := List.Mem.head _
/-- The CFG edge of the call `x = id(dto)`. -/
theorem hE01 : (0, 1, Instr.call callId, 2) ∈ prog.edges := List.Mem.tail _ (List.Mem.head _)
/-- The CFG edge of `return p`. -/
theorem hE10 : (1, 0, Instr.stmt idS, 1) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- Program I has no cleaner. -/
theorem no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

/-- Program I has no type filter. -/
theorem no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

/-- Program I is well-formed (`Program.WF`): every micro edge reads from a touched base, the call
    bindings are mark agnostic, and there is no type filter. -/
theorem wf : prog.WF := by
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
    exact (no_filt hE).elim

#print axioms wf

/-- No call binding of program I has an `.any` target (`AnyTaint.BindNoAny`). -/
theorem bindNoAny : BindNoAny prog := by
  intro M n c n' hE
  cases hE with
  | tail _ hE => cases hE with
    | head =>
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · cases he with
        | head => rfl
        | tail _ he => cases he
      · cases he with
        | head => rfl
        | tail _ he => cases he
    | tail _ hE => cases hE with
      | tail _ hE => cases hE

#print axioms bindNoAny

/-- The only taint edge (the source of `G`) has the `.any` target and concrete marks
    (`AnyTaint.TaintConc`). -/
theorem taintConc : TaintConc prog G.taint := by
  intro M n s n' hE e he ht
  cases hE with
  | head =>
    cases he with
    | head => cases ht
    | tail _ he => cases he with
      | head => exact ⟨rfl, ⟨1, rfl⟩, ⟨0, rfl⟩⟩
      | tail _ he => cases he
  | tail _ hE => cases hE with
    | tail _ hE => cases hE with
      | head =>
        cases he with
        | head => cases ht
        | tail _ he => cases he with
          | head => cases ht
          | tail _ he => cases he
      | tail _ hE => cases hE

#print axioms taintConc

/-! ### The facts

  The facts of `G` are reused: `G.Z` (zero), `G.DTO` (`(dto, [], [any-taint], T)`, normal),
  `G.DTOd` (the same in the demand layer), `G.Ap` (the added fact `(p, [], [any], T)` of the
  link), `G.J1` (the run-1 premise `(p, [], *, {}, *)`), `G.J1f`, `G.RETn` / `G.RETd`
  (`(ret, [], [any], T)` normal / demand) and `G.Xn` / `G.Xd` (the sink fact). -/

/-- Run 1: the FLOW summary conclusion `(ret, [], *, {}, *)` of `ret = p`, in the NORMAL layer. -/
def RETf : AFact := ⟨⟨4, [], st, .star⟩, false⟩

/-! ### Run 1 with W6T (`D6T`), completely -/

/-- Run 1 of program I with W6T: `policy1`, the field limit 3. -/
abbrev R1T : Obj → Prop := D6T prog G.taint cnt 3 policy1 G.sinks [0]

/-- The initial facts of run 1: the zero fact of `root`, the policy fact of `id`. -/
def inits1 : List (MethodId × PFact) := [(0, zeroFact), (1, G.J1)]
/-- The edges of run 1 with W6T. -/
def edges1T : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, G.Z), (0, zeroFact, 1, G.Z), (0, zeroFact, 1, G.DTO), (0, zeroFact, 2, G.Z),
   (0, zeroFact, 2, G.Xn), (1, G.J1, 0, G.J1f), (1, G.J1, 1, G.J1f), (1, G.J1, 1, RETf)]
/-- The added facts of run 1. -/
def addeds1 : List (MethodId × PFact) := [(1, G.Ap)]

/-- Every object of run 1 (W6T) is in the lists; no request; every vulnerability is in the
    NORMAL layer. -/
def Inv1T : Obj → Prop
  | .init M i => (M, i) ∈ inits1
  | .edge M i n f => (M, i, n, f) ∈ edges1T
  | .added M a => (M, a) ∈ addeds1
  | .req _ _ _ => False
  | .vuln _ _ _ d => d = false

instance : DecidablePred Inv1T := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1T))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ d => inferInstanceAs (Decidable (d = false))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM I WITH W6T: every object is in the lists above. The exit edges
    of `id` are the identity `(p, [], *, *) → (p, [], *, *)` and the FLOW summary
    `(p, [], *, *) → (ret, [], *, *)`, both normal; the only sink edge is the normal
    `zero → (x, [], [any-taint], T)`. -/
theorem inv1T {o : Obj} (h : R1T o) : Inv1T o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits1, Inv1T (.edge x.1 x.2 (prog.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2).facts, Inv1T (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1T, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transferT G.taint cnt 3 idS x.2.2.2).facts, Inv1T (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1T, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transferT G.taint cnt 3 idS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callId.touched = false → Inv1T (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callId.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, Inv1T (.added callId.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addeds1, Inv1T (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callId.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ inits1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edges1T, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary a y.2 z.2.2.2).facts,
          ∀ e2 ∈ callId.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            Inv1T (.edge 0 x.2.1 2 (limitF cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 G.sinkP = .none ∨ check x.2.1 x.2.2.2 G.sinkP = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 G.sinkP = .triggered → x.2.2.2.demand = false)
        (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1T

/-! ### Run 1 with W6T: the derivation and the theorems -/

-- the source result is `[any-taint]`: `.any` and normal (a taint edge keeps its layer)
example : (transferT G.taint cnt 3 G.srcS G.Z).facts = [G.Z, G.DTO] := by decide
-- the binding into `id` gives the added fact `(p, [], [any], T)` in the normal layer: on the
-- link it is `[any-taint]`
example : (applyEdge G.DTO G.bIn.1 G.bIn.2).facts = [⟨G.Ap, false⟩] := by decide
-- run 1 serves it with the most abstract fact `(p, [], *, {}, *)`
example : policy1 1 G.Ap = G.J1 := by decide
-- THE FLOW SUMMARY OF `ret = p` IS CASE `below r = []`: the micro edge reads `p.*`, the premise
-- is `p`; the result is `(ret, [], *, {}, *)`, normal (no approximation)
example : relate [] G.J1.path = .below [] := rfl
example : belowCase st st [] [] st = some ([], st, false) := by decide
example : (transferT G.taint cnt 3 idS G.J1f).facts = [G.J1f, RETf] := by decide

/-- THE APPLICATION KEEPS THE NORMAL LAYER (ap.md §4.1 step 3, case `below r = []`, the row
    `*` target / `[any-taint]` fact): the run-1 FLOW summary `(p, [], *, {}, *) →
    (ret, [], *, {}, *)` of `id` applies to the added fact `(p, [], [any], T)` of the normal link
    (`applicable`), and gives `(ret, [], [any], T)` in the NORMAL layer (`belowCase` with the
    Empty exclusion sets no demand bit); the binding back gives `(x, [], [any], T)`, normal, and
    the field limit keeps it. In the spec tails: `(ret, ., [any-taint], T)` and
    `(x, ., [any-taint], T)`. -/
theorem app_normal :
    applicable G.J1 G.Ap = true ∧
    belowCase .any st [] [] st = some ([], .any, false) ∧
    (applySummary ⟨G.Ap, false⟩ G.J1 RETf).facts = [G.RETn] ∧
    (applyEdge G.RETn G.bOut.1 G.bOut.2).facts = [G.Xn] ∧
    limitF cnt 3 G.Xn = G.Xn := by decide

#print axioms app_normal

/-- Run 1 (W6T): the source edge `zero → (dto, [], [any-taint], T)` is NORMAL. -/
theorem r1_e01 : R1T (.edge 0 zeroFact 1 G.DTO) :=
  D6T.step (D6T.start (D6T.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1: `policy1` serves the added fact `(p, [], [any], T)` with `(p, [], *, {}, *)`. -/
theorem r1_i1 : R1T (.init 1 G.J1) := by
  have h : R1T (.init 1 (policy1 1 G.Ap)) := D6T.initA (α := policy1)
    (D6T.added (c := callId) (e := G.bIn) (a := ⟨G.Ap, false⟩) (P := prog) (taint := G.taint)
      (counted := cnt) (L := 3) (sinks := G.sinks) (roots := [0])
    r1_e01 hE01 (List.Mem.head _) (by decide))
  have hp : policy1 1 G.Ap = G.J1 := by decide
  rw [hp] at h
  exact h

/-- Run 1 (W6T): THE RUN-1 FLOW SUMMARY OF `id` IS `(p, [], *, {}, *) → (ret, [], *, {}, *)` IN
    THE NORMAL LAYER (and complete: it is a record). -/
theorem run1T_flow : R1T (.edge 1 G.J1 1 RETf) ∧ RETf.complete = true :=
  ⟨D6T.step (D6T.start r1_i1) hE10 (by decide), rfl⟩

#print axioms run1T_flow

/-- Run 1 (W6T): the application of the FLOW summary to the `[any-taint]` added fact gives THE
    SINK EDGE `zero → (x, [], [any-taint], T)` IN THE NORMAL LAYER. -/
theorem run1T_sink_normal : R1T (.edge 0 zeroFact 2 G.Xn) :=
  D6T.ret (c := callId) (e1 := G.bIn) (a := ⟨G.Ap, false⟩) (j := G.J1) (g := RETf) (r := G.RETn)
    (e2 := G.bOut) (r' := G.Xn) r1_e01 hE01 (List.Mem.head _) (by decide) r1_i1 (by decide)
    run1T_flow.1 (by decide) (List.Mem.head _) (by decide)

#print axioms run1T_sink_normal

/-- Run 1 with W6T reports the vulnerability of program I in the NORMAL layer. -/
theorem run1T_vuln_normal : R1T (.vuln 0 2 G.sinkP false) :=
  D6T.vuln run1T_sink_normal (List.Mem.head _) (by decide)

#print axioms run1T_vuln_normal

/-- RUN 1 CONFIRMS PROGRAM I (`AnyTaint.ConfirmedT6`): the normal sink edge
    `zero → (x, [], [any-taint], T)` under the supported zero premise of the root, with a
    triggered check. -/
theorem run1T_confirmed : ConfirmedT6 prog G.taint cnt 3 policy1 G.sinks [0] 0 2 G.sinkP :=
  ⟨zeroFact, G.Xn, run1T_sink_normal, Sup6T.root (List.Mem.head _), rfl, List.Mem.head _,
    by decide⟩

#print axioms run1T_confirmed

/-- Run 1 with W6T reports the vulnerability of program I ONLY in the normal layer: the complete
    run has no demand-layer sink edge (`inv1T`). -/
theorem run1T_no_demand : ¬ R1T (.vuln 0 2 G.sinkP true) := fun h => Bool.noConfusion (inv1T h)

#print axioms run1T_no_demand

/-! ### Run 1 with W6 (the old rule), completely: the same vulnerability is demand only -/

/-- Run 1 of program I with W6 (`W6.D6`): every `[any]` result goes to the demand layer. -/
abbrev R1W : Obj → Prop := W6.D6 prog cnt 3 policy1 G.sinks [0]

/-- The edges of run 1 with W6. -/
def edges1W : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, G.Z), (0, zeroFact, 1, G.Z), (0, zeroFact, 1, G.DTOd), (0, zeroFact, 2, G.Z),
   (0, zeroFact, 2, G.Xd), (1, G.J1, 0, G.J1f), (1, G.J1, 1, G.J1f), (1, G.J1, 1, RETf)]

/-- Every object of run 1 (W6) is in the lists; no request; every vulnerability is in the
    DEMAND layer. -/
def Inv1W : Obj → Prop
  | .init M i => (M, i) ∈ inits1
  | .edge M i n f => (M, i, n, f) ∈ edges1W
  | .added M a => (M, a) ∈ addeds1
  | .req _ _ _ => False
  | .vuln _ _ _ d => d = true

instance : DecidablePred Inv1W := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1W))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ d => inferInstanceAs (Decidable (d = true))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM I WITH W6: the same summaries as with W6T (the FLOW summary of
    `id` is normal), but the source result `(dto, [], [any], T)` is in the demand layer, and so
    is the only sink edge. -/
theorem inv1W {o : Obj} (h : R1W o) : Inv1W o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits1,
      Inv1W (.edge x.1 x.2 (prog.entry x.1) (W6.w6 (startFact x.2)))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transfer cnt 3 G.srcS x.2.2.2).facts, Inv1W (.edge 0 x.2.1 1 (W6.w6 f')))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1W, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transfer cnt 3 idS x.2.2.2).facts, Inv1W (.edge 1 x.2.1 1 (W6.w6 f')))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transfer cnt 3 G.srcS x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1W, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transfer cnt 3 idS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callId.touched = false → Inv1W (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callId.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, Inv1W (.added callId.callee a.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addeds1, Inv1W (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callId.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ inits1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edges1W, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary (W6.w6 a) y.2 z.2.2.2).facts,
          ∀ e2 ∈ callId.fromCallee, ∀ r' ∈ (applyEdge (W6.w6 r) e2.1 e2.2).facts,
            Inv1W (.edge 0 x.2.1 2 (W6.w6 (limitF cnt 3 r'))))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    cases hs with
    | head =>
      rcases (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 G.sinkP = .none ∨ check x.2.1 x.2.2.2 G.sinkP = .triggered)
        (0, i, 2, f) ih rfl rfl with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges1W, x.1 = 0 → x.2.2.1 = 2 →
        check x.2.1 x.2.2.2 G.sinkP = .triggered → x.2.2.2.demand = true)
        (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1W

-- W6 raises the source result: `(dto, [], [any], T)` in the demand layer; the added fact of the
-- link is then in the demand layer too, and the same FLOW summary gives a demand result
example : ((transfer cnt 3 G.srcS G.Z).facts.map W6.w6) = [G.Z, G.DTOd] := by decide
example : (applySummary ⟨G.Ap, true⟩ G.J1 RETf).facts = [G.RETd] := by decide
example : (applyEdge G.RETd G.bOut.1 G.bOut.2).facts = [G.Xd] := by decide

/-- Run 1 (W6): the source edge `zero → (dto, [], [any], T)` is a DEMAND edge. -/
theorem w1_e01 : R1W (.edge 0 zeroFact 1 G.DTOd) :=
  W6.D6.step (f' := G.DTO) (W6.D6.start (W6.D6.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1 (W6): the premise `(p, [], *, {}, *)` of `id`. -/
theorem w1_i1 : R1W (.init 1 G.J1) := by
  have h : R1W (.init 1 (policy1 1 G.Ap)) := W6.D6.initA (α := policy1)
    (W6.D6.added (c := callId) (e := G.bIn) (a := ⟨G.Ap, true⟩) (P := prog) (counted := cnt)
      (L := 3) (sinks := G.sinks) (roots := [0])
    w1_e01 hE01 (List.Mem.head _) (by decide))
  have hp : policy1 1 G.Ap = G.J1 := by decide
  rw [hp] at h
  exact h

/-- Run 1 (W6): the FLOW summary `(p, [], *, *) → (ret, [], *, *)` of `id`, normal (W6 does not
    read it: it has no `[any]` tail). -/
theorem w1_flow : R1W (.edge 1 G.J1 1 RETf) :=
  W6.D6.step (f' := RETf) (W6.D6.start w1_i1) hE10 (by decide)

/-- Run 1 (W6): the sink edge `zero → (x, [], [any], T)`, demand. -/
theorem w1_sink : R1W (.edge 0 zeroFact 2 G.Xd) :=
  W6.D6.ret (c := callId) (e1 := G.bIn) (a := ⟨G.Ap, true⟩) (j := G.J1) (g := RETf) (r := G.RETd)
    (e2 := G.bOut) (r' := G.Xd) w1_e01 hE01 (List.Mem.head _) (by decide) w1_i1 (by decide)
    w1_flow (by decide) (List.Mem.head _) (by decide)

/-- For contrast: run 1 with the old rule W6 reports the vulnerability of program I in the
    DEMAND layer. -/
theorem run1W6_vuln : R1W (.vuln 0 2 G.sinkP true) :=
  W6.D6.vuln w1_sink (List.Mem.head _) (by decide)

#print axioms run1W6_vuln

/-- For contrast: run 1 with the old rule W6 has NO normal sink edge for program I (the complete
    run `inv1W`): W6 puts the source result `(dto, [], [any], T)` in the demand layer, and the
    application of the normal FLOW summary of `id` keeps that layer. With W6T the same summary
    gives a normal sink edge (`run1T_sink_normal`). -/
theorem run1W6_no_normal : ¬ R1W (.vuln 0 2 G.sinkP false) := fun h => Bool.noConfusion (inv1W h)

#print axioms run1W6_no_normal

/-! ### The vulnerability is real -/

/-- The pair relation of the source on the witness of program I: `zero → dto` (every location of
    `dto` gets the mark `T`; here `dto` itself). -/
theorem den_src0 : den G.srcE.1 G.srcE.2 zeroLoc ⟨1, [], 1⟩ :=
  ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, trivial⟩
/-- The pair relation of the binding `dto.* → p.*` on the witness. -/
theorem den_in0 : den G.bIn.1 G.bIn.2 ⟨1, [], 1⟩ ⟨3, [], 1⟩ :=
  ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩
/-- The pair relation of `ret = p` (`p.* → ret.*`) on the witness. -/
theorem den_id :
    den (⟨3, [], st, .star⟩ : PFact) ⟨4, [], st, .star⟩ ⟨3, [], 1⟩ ⟨4, [], 1⟩ :=
  ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩
/-- The pair relation of the binding back `ret.* → x.*` on the witness. -/
theorem den_out0 : den G.bOut.1 G.bOut.2 ⟨4, [], 1⟩ ⟨2, [], 1⟩ :=
  ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl⟩

/-- The vulnerability of program I is REAL: the source taints `dto` (every location of it), `id`
    returns it into `x`, and the sink pattern `(x, [], [any], T)` covers `x`. -/
theorem vuln_real : Reach prog [0] 0 2 ⟨2, [], 1⟩ ∧ G.sinkP.covers ⟨2, [], 1⟩ := by
  have f0 : Flow prog 0 zeroLoc 1 ⟨1, [], 1⟩ :=
    Flow.step (Flow.start 0 zeroLoc) hE00
      (Or.inr ⟨G.srcE, List.Mem.tail _ (List.Mem.head _), den_src0⟩)
  have fc : Flow prog 1 ⟨3, [], 1⟩ 1 ⟨4, [], 1⟩ :=
    Flow.step (Flow.start 1 _) hE10 (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), den_id⟩)
  exact ⟨Reach.root (List.Mem.head _)
    (Flow.call f0 hE01 (List.Mem.head _) den_in0 fc (List.Mem.head _) den_out0),
    ⟨rfl, ⟨[], rfl, trivial⟩, rfl⟩⟩

#print axioms vuln_real

end I

/-! ## Program S: the setter record (decision 5, the accepted precision loss)

```
root():  dto = srcAny();   // 0 -> 1: the taint edge zero.$ (zeroMark) -> dto.[any] (T)
         dto.setName(c);   // 1 -> 2; c is clean (never tainted)
         sink(dto.name);   // the sink pattern (dto, [name], $, T) at node 2
         sink(dto.email);  // the sink pattern (dto, [email], $, T) at node 2
setName(n):  this.name = n;  // 0 -> 1: the keep edge this.*/{name} -> this.* and the gen edge
                             //         n.* -> this.name.*
```
  Bases: zero = 0, dto = 1, c = 2, this = 3, n = 4. Accessors: name = 1, email = 2. Methods:
  root = 0 (nodes 0, 1, 2; exit 2), setName = 1 (nodes 0, 1; exit 1). The call binds
  `dto.* → this.*` and `c.* → n.*`, and back `this.* → dto.*` and `n.* → c.*`.

  What it shows:
  * run 1 (`D6T`, `policy1`) derives THE RECORD of `setName`:
    `(this, [], *, {}, *) → (this, [], */{name}, *)`, normal and complete (`run1_record`;
    `recs1_complete`: the complete exit edges of run 1 are `recsList`);
  * THE RECORD APPLICATION DEMOTES (`record_app_demand`): the record applied to the added fact
    `(this, [], [any-taint], T)` (`.any`, normal on the link) is case `below r = []` with the
    exclusion `{name}`: `belowCase` gives `(this, [], [any], T)` in the DEMAND layer (decision 5,
    "demote"), and the binding back gives `(dto, [], [any], T)`, demand. Run 1 has no normal
    sink edge (`run1_no_normal`);
  * backward run 2 (`Backward.DB`, seeded at both sinks, restricted by the reversed run-1
    summaries) hands off EXACTLY the zero demand and the demand
    `dEmail = (D-c = (this, [email], $, T), D-p = (this, [email], $, T))` of `setName`
    (`handoff_exact`): the requirement `(this, [name], $, T)` meets the reversed record
    `(this, [], */{name}, *)`, whose exclusion rejects it, so it gives no demand;
  * forward run 3 (`DRT`) with a demand inside the hand-off (written by hand: `demS`; or the
    derived hand-off `HT`) and the run-1 record as a record:
    - `sink(dto.name)` is reported ONLY in the demand layer (`run3_name_demand`,
      `run3_name_no_normal`, `inv3`): a DEMAND entry, not confirmed (`run3_name_not_confirmed`),
      and not real (`name_not_real`: `dto.name` was overwritten by the clean `c`);
    - `sink(dto.email)` has a NORMAL sink edge through the RESTRICTED summary
      `(this, [email], $, T) → (this, [email], $, T)` of `setName` (`run3_email_sink_normal`)
      and is CONFIRMED (`run3_email_confirmed`); it is real (`email_real`). The record gives it
      in the demand layer too (`run3_email_demand`): the precision loss of the record is
      repaired by the demand of the next run;
    - with the `.any` demand `(this, [email], [any], T)` (the other form of the demand) the
      premise is the MUST premise `(this, [email], [any-taint], T)`, and the vulnerability is
      confirmed too (`run3A_email_confirmed`). -/

namespace S

/-! ### The program -/

/-- The keep edge of the strong write `this.name = n`: `this.*/{name} → this.*`. -/
def keepS : MicroEdge := (⟨3, [], .star (.set [1]), .star⟩, ⟨3, [], st, .star⟩)
/-- The gen edge of `this.name = n`: `n.* → this.name.*`. -/
def genS : MicroEdge := (⟨4, [], st, .star⟩, ⟨3, [1], st, .star⟩)
/-- `this.name = n`: the keep edge, the identity on `n`, the gen edge. -/
def setS : Stmt := ⟨[3, 4], [keepS, (⟨4, [], st, .star⟩, ⟨4, [], st, .star⟩), genS]⟩
/-- The binding of the receiver of `dto.setName(c)`: `dto.* → this.*`. -/
def bThis : MicroEdge := (⟨1, [], st, .star⟩, ⟨3, [], st, .star⟩)
/-- The binding of the argument: `c.* → n.*`. -/
def bN : MicroEdge := (⟨2, [], st, .star⟩, ⟨4, [], st, .star⟩)
/-- The binding back of the receiver: `this.* → dto.*`. -/
def bBack : MicroEdge := (⟨3, [], st, .star⟩, ⟨1, [], st, .star⟩)
/-- The binding back of the argument: `n.* → c.*`. -/
def bNBack : MicroEdge := (⟨4, [], st, .star⟩, ⟨2, [], st, .star⟩)
/-- `dto.setName(c)`. -/
def callSet : Call := ⟨1, [1, 2], [bThis, bN], [bBack, bNBack]⟩
/-- Program S: `root` (method 0) and `setName` (method 1). -/
def prog : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 2,
  [(0, 0, .stmt G.srcS, 1), (0, 1, .call callSet, 2), (1, 0, .stmt setS, 1)]⟩
/-- The sink pattern of `sink(dto.name)`: `(dto, [name], $, T)`. -/
def sinkName : PFact := ⟨1, [1], .exact, .conc 1⟩
/-- The sink pattern of `sink(dto.email)`: `(dto, [email], $, T)`. -/
def sinkEmail : PFact := ⟨1, [2], .exact, .conc 1⟩
/-- Both sinks are at node 2 of `root` (two sink calls that change no location are two sink
    patterns at one node). -/
def sinks : List (MethodId × Node × PFact) := [(0, 2, sinkName), (0, 2, sinkEmail)]

/-- The CFG edge of `dto = srcAny()`. -/
theorem hE00 : (0, 0, Instr.stmt G.srcS, 1) ∈ prog.edges := List.Mem.head _
/-- The CFG edge of the call `dto.setName(c)`. -/
theorem hE01 : (0, 1, Instr.call callSet, 2) ∈ prog.edges := List.Mem.tail _ (List.Mem.head _)
/-- The CFG edge of `this.name = n`. -/
theorem hE10 : (1, 0, Instr.stmt setS, 1) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- The name sink is a sink of program S. -/
theorem hsN : ((0 : MethodId), (2 : Node), sinkName) ∈ sinks := List.Mem.head _
/-- The email sink is a sink of program S. -/
theorem hsE : ((0 : MethodId), (2 : Node), sinkEmail) ∈ sinks := List.Mem.tail _ (List.Mem.head _)

/-- Program S has no cleaner. -/
theorem no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

/-- Program S has no type filter. -/
theorem no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h

/-- Program S is well-formed (`Program.WF`): every micro edge reads from a touched base, the call
    bindings are mark agnostic, and there is no type filter. -/
theorem wf : prog.WF := by
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
            | tail _ he => cases he with
              | head => rfl
              | tail _ he => cases he
        | tail _ hE => cases hE
  · intro M n c n' hE e he
    cases hE with
    | tail _ hE => cases hE with
      | head => cases he with
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
        | tail _ he => cases he with
          | head => rfl
          | tail _ he => cases he
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  · intro M n b may n' hE
    exact (no_filt hE).elim

#print axioms wf

/-- No call binding of program S has an `.any` target (`AnyTaint.BindNoAny`). -/
theorem bindNoAny : BindNoAny prog := by
  intro M n c n' hE
  cases hE with
  | tail _ hE => cases hE with
    | head =>
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · cases he with
        | head => rfl
        | tail _ he => cases he with
          | head => rfl
          | tail _ he => cases he
      · cases he with
        | head => rfl
        | tail _ he => cases he with
          | head => rfl
          | tail _ he => cases he
    | tail _ hE => cases hE with
      | tail _ hE => cases hE

#print axioms bindNoAny

/-- The only taint edge (the source of `G`) has the `.any` target and concrete marks
    (`AnyTaint.TaintConc`). -/
theorem taintConc : TaintConc prog G.taint := by
  intro M n s n' hE e he ht
  cases hE with
  | head =>
    cases he with
    | head => cases ht
    | tail _ he => cases he with
      | head => exact ⟨rfl, ⟨1, rfl⟩, ⟨0, rfl⟩⟩
      | tail _ he => cases he
  | tail _ hE => cases hE with
    | tail _ hE => cases hE with
      | head =>
        cases he with
        | head => cases ht
        | tail _ he => cases he with
          | head => cases ht
          | tail _ he => cases he with
            | head => cases ht
            | tail _ he => cases he
      | tail _ hE => cases hE

#print axioms taintConc

/-! ### The facts

  Reused from `G`: `G.Z` (zero), `G.DTO` (`(dto, [], [any-taint], T)`, normal) and `G.DTOd`
  (`(dto, [], [any], T)`, demand). -/

/-- The added fact of `setName`: `(this, [], [any], T)` (on the normal link: `[any-taint]`). -/
def Athis : PFact := ⟨3, [], .any, .conc 1⟩
/-- Run 1: the most abstract premise `(this, [], *, {}, *)` of `setName` (`policy1`). -/
def Jthis : PFact := ⟨3, [], st, .star⟩
/-- The start fact of `Jthis`, normal. -/
def JthisF : AFact := ⟨Jthis, false⟩
/-- THE RECORD CONCLUSION of `setName`: `(this, [], */{name}, *)`, normal (the keep edge). -/
def KEEP : AFact := ⟨⟨3, [], .star (.set [1]), .star⟩, false⟩
/-- The record application on the `[any-taint]` added fact: `(this, [], [any], T)`, DEMAND. -/
def THISd : AFact := ⟨Athis, true⟩
/-- Run 3: the premise `(this, [email], $, T)` of `setName` emitted from the demand `dEmail`. -/
def Jem : PFact := ⟨3, [2], .exact, .conc 1⟩
/-- The start fact of `Jem`, normal. -/
def JemF : AFact := ⟨Jem, false⟩
/-- The sink fact `(dto, [email], $, T)`, normal (the restricted summary, bound back). -/
def EMn : AFact := ⟨⟨1, [2], .exact, .conc 1⟩, false⟩
/-- THE DEMAND OF `setName` (forward orientation): `D-c = D-p = (this, [email], $, T)`. -/
def dEmail : DemandEdge := ⟨Jem, some Jem⟩

/-! ### Run 1 (`D6T`), completely: the record of `setName` -/

/-- Run 1 of program S with W6T: `policy1`, the field limit 3. -/
abbrev R1 : Obj → Prop := D6T prog G.taint cnt 3 policy1 sinks [0]

/-- The initial facts of run 1: the zero fact of `root`, the policy fact of `setName`. -/
def inits1 : List (MethodId × PFact) := [(0, zeroFact), (1, Jthis)]
/-- The edges of run 1. -/
def edges1 : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, G.Z), (0, zeroFact, 1, G.Z), (0, zeroFact, 1, G.DTO), (0, zeroFact, 2, G.Z),
   (0, zeroFact, 2, G.DTOd), (1, Jthis, 0, JthisF), (1, Jthis, 1, KEEP)]
/-- The added facts of run 1. -/
def addeds1 : List (MethodId × PFact) := [(1, Athis)]

/-- Every object of run 1 is in the lists; no request; every vulnerability is in the demand
    layer. -/
def Inv1 : Obj → Prop
  | .init M i => (M, i) ∈ inits1
  | .edge M i n f => (M, i, n, f) ∈ edges1
  | .added M a => (M, a) ∈ addeds1
  | .req _ _ _ => False
  | .vuln _ _ _ d => d = true

instance : DecidablePred Inv1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ d => inferInstanceAs (Decidable (d = true))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM S (W6T): the only exit edge of `setName` is the record
    `(this, [], *, *) → (this, [], */{name}, *)`; the only sink edge is the demand
    `zero → (dto, [], [any], T)`. -/
theorem inv1 {o : Obj} (h : R1 o) : Inv1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits1, Inv1 (.edge x.1 x.2 (prog.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2).facts, Inv1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transferT G.taint cnt 3 setS x.2.2.2).facts, Inv1 (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ t ∈ (transferT G.taint cnt 3 setS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callSet.touched = false → Inv1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callSet.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, Inv1 (.added callSet.callee a.fact))
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
          ∀ e1 ∈ callSet.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ inits1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edges1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary a y.2 z.2.2.2).facts,
          ∀ e2 ∈ callSet.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            Inv1 (.edge 0 x.2.1 2 (limitF cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 → ∀ s ∈ [sinkName, sinkEmail],
        check x.2.1 x.2.2.2 s = .none ∨ check x.2.1 x.2.2.2 s = .triggered := by decide
    cases hs with
    | head =>
      rcases hnr (0, i, 2, f) ih rfl rfl sinkName (List.Mem.head _) with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs with
      | head =>
        rcases hnr (0, i, 2, f) ih rfl rfl sinkEmail (List.Mem.tail _ (List.Mem.head _)) with h | h
        · rw [h] at hc; exact Check.noConfusion hc
        · rw [h] at hc; exact Check.noConfusion hc
      | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    have hv : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 → ∀ s ∈ [sinkName, sinkEmail],
        check x.2.1 x.2.2.2 s = .triggered → x.2.2.2.demand = true := by decide
    cases hs with
    | head => exact hv (0, i, 2, f) ih rfl rfl sinkName (List.Mem.head _) hc
    | tail _ hs => cases hs with
      | head => exact hv (0, i, 2, f) ih rfl rfl sinkEmail (List.Mem.tail _ (List.Mem.head _)) hc
      | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1

/-! ### Run 1: the record, and the record application -/

-- the keep edge on the most abstract premise: case `below r = []`, the result `*/{name}`
example : belowCase st (.star (.set [1])) [] [] st = some ([], .star (.set [1]), false) := by
  decide
example : (transferT G.taint cnt 3 setS JthisF).facts = [KEEP] := by decide
-- the binding into `setName` gives the added fact `(this, [], [any], T)`, normal on the link
example : (applyEdge G.DTO bThis.1 bThis.2).facts = [⟨Athis, false⟩] := by decide
example : policy1 1 Athis = Jthis := by decide

/-- Run 1: the source edge `zero → (dto, [], [any-taint], T)`, normal. -/
theorem r1_e01 : R1 (.edge 0 zeroFact 1 G.DTO) :=
  D6T.step (D6T.start (D6T.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1: `policy1` serves the added fact `(this, [], [any], T)` with `(this, [], *, {}, *)`. -/
theorem r1_i1 : R1 (.init 1 Jthis) := by
  have h : R1 (.init 1 (policy1 1 Athis)) := D6T.initA (α := policy1)
    (D6T.added (c := callSet) (e := bThis) (a := ⟨Athis, false⟩) (P := prog) (taint := G.taint)
      (counted := cnt) (L := 3) (sinks := sinks) (roots := [0])
    r1_e01 hE01 (List.Mem.head _) (by decide))
  have hp : policy1 1 Athis = Jthis := by decide
  rw [hp] at h
  exact h

/-- THE RUN-1 RECORD OF `setName`: `(this, [], *, {}, *) → (this, [], */{name}, *)` (the keep
    edge of `this.name = n`), in the NORMAL layer and complete (a persisted record, ap.md §8.7
    R1). -/
theorem run1_record : R1 (.edge 1 Jthis 1 KEEP) ∧ KEEP.complete = true :=
  ⟨D6T.step (D6T.start r1_i1) hE10 (by decide), rfl⟩

#print axioms run1_record

/-- THE RECORD APPLICATION DEMOTES (decision 5; ap.md §4.1 step 3, case `below r = []`, the row
    `*` target / `[any-taint]` fact with `E ≠ {}`): the added fact `(this, [], [any], T)` of the
    normal link (spec: `[any-taint]`) satisfies the record premise in both directions (`satI`
    and `applicable`); the application is `belowCase` with the exclusion `{name}`, which sets the
    demand bit; the result is `(this, [], [any], T)` in the DEMAND layer, and the binding back
    gives `(dto, [], [any], T)` in the demand layer (the field limit keeps it). -/
theorem record_app_demand :
    satI Jthis Athis = true ∧ applicable Jthis Athis = true ∧
    belowCase .any st [] [] (.star (.set [1])) = some ([], .any, true) ∧
    (applySummary ⟨Athis, false⟩ Jthis KEEP).facts = [THISd] ∧
    (applyEdge THISd bBack.1 bBack.2).facts = [G.DTOd] ∧
    (applyEdge THISd bNBack.1 bNBack.2).facts = [] ∧
    limitF cnt 3 G.DTOd = G.DTOd := by decide

#print axioms record_app_demand

/-- Run 1: the record application gives the sink edge `zero → (dto, [], [any], T)`, DEMAND. -/
theorem r1_e02 : R1 (.edge 0 zeroFact 2 G.DTOd) :=
  D6T.ret (c := callSet) (e1 := bThis) (a := ⟨Athis, false⟩) (j := Jthis) (g := KEEP)
    (r := THISd) (e2 := bBack) (r' := G.DTOd) r1_e01 hE01 (List.Mem.head _) (by decide) r1_i1
    (by decide) run1_record.1 (by decide) (List.Mem.head _) (by decide)

/-- Run 1 reports both sinks of program S, in the DEMAND layer. -/
theorem run1_vulns : R1 (.vuln 0 2 sinkName true) ∧ R1 (.vuln 0 2 sinkEmail true) :=
  ⟨D6T.vuln r1_e02 hsN (by decide), D6T.vuln r1_e02 hsE (by decide)⟩

#print axioms run1_vulns

/-- Run 1 has NO normal sink edge in program S (the complete run `inv1`): every result after the
    call comes from the demoted record application. -/
theorem run1_no_normal (s : PFact) : ¬ R1 (.vuln 0 2 s false) := fun h => Bool.noConfusion (inv1 h)

#print axioms run1_no_normal

/-- The complete exit edges of run 1, as records with must flags (no must-premise in run 1): the
    zero edge of `root` and THE RECORD of `setName`. -/
def recsList : List (MethodId × (PFact × Bool × AFact)) :=
  [(0, (zeroFact, false, G.Z)), (1, (Jthis, false, KEEP))]

/-- Every complete exit edge of run 1 is in `recsList` (so `recsList` is the record set that run 1
    passes on, ap.md §8.7 R1). -/
theorem recs1_complete {m : MethodId} {j : PFact} {g : AFact}
    (h : R1 (.edge m j (prog.exit m) g)) (hc : g.complete = true) :
    (m, (j, false, g)) ∈ recsList :=
  (by decide : ∀ x ∈ edges1, x.2.2.1 = prog.exit x.1 → x.2.2.2.complete = true →
    (x.1, (x.2.1, false, x.2.2.2)) ∈ recsList) (m, j, _, g) (inv1 h) rfl hc

#print axioms recs1_complete

/-! ### Backward run 2 (`Backward.DB`), completely, and its hand-off

  The reversed program; the backward run is seeded at both sinks (run 1 reported both,
  `run1_vulns`) and restricted by the reversed summaries of run 1 (`revDemS`). The requirement
  `(dto, [email], $, T)` enters `setName` as `(this, [email], $, T)`; the reversed record
  `((this, [], */{name}, *), D-p = (this, [], *, *))` emits it as the backward premise; the
  reversed keep edge `this.* → this.*/{name}` keeps it. So `setName` has the backward summary
  `(this, [email], $, T) → (this, [email], $, T)`: the demand `dEmail`. The requirement
  `(dto, [name], $, T)` enters as `(this, [name], $, T)`, and the exclusion `{name}` of the
  reversed record rejects it: no premise, no demand (the backward run knows that `this.name` is
  overwritten). -/

/-- The reversed program S. -/
def Pb : Program := Reverse.Program.rev prog

/-- The edges of the reversed program S. -/
theorem Pb_edges : Pb.edges =
    [(0, 1, .stmt (Reverse.Stmt.rev G.srcS), 0), (0, 2, .call (Reverse.Call.rev callSet), 1),
     (1, 1, .stmt (Reverse.Stmt.rev setS), 0)] := rfl

/-- The reversed CFG edge of `dto = srcAny()`. -/
theorem hb_src : (0, 1, Instr.stmt (Reverse.Stmt.rev G.srcS), 0) ∈ Pb.edges := by
  rw [Pb_edges]; exact List.Mem.head _
/-- The reversed CFG edge of the call `dto.setName(c)`. -/
theorem hb_c : (0, 2, Instr.call (Reverse.Call.rev callSet), 1) ∈ Pb.edges := by
  rw [Pb_edges]; exact List.Mem.tail _ (List.Mem.head _)
/-- The reversed CFG edge of `this.name = n`. -/
theorem hb_set : (1, 1, Instr.stmt (Reverse.Stmt.rev setS), 0) ∈ Pb.edges := by
  rw [Pb_edges]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- The reversed summaries of run 1. -/
def revDemS : List (MethodId × DemandEdge) :=
  [(0, ⟨zeroFact, some zeroFact⟩), (0, ⟨G.DTOd.fact, some zeroFact⟩), (1, ⟨KEEP.fact, some Jthis⟩)]

/-- The reversed record of `setName`: `((this, [], */{name}, *), D-p = (this, [], *, {}, *))`. -/
def dKeep : DemandEdge := ⟨KEEP.fact, some Jthis⟩

/-- The reversed summaries of run 1 are in `revDemS`. -/
theorem revDem_bound {m : MethodId} {d : DemandEdge}
    (h : Backward.revSummaryDemand prog R1 m d) : (m, d) ∈ revDemS := by
  obtain ⟨j, g, ⟨_, hor⟩, rfl⟩ := h
  rcases hor with h0 | ⟨g', hg', hgg⟩
  · cases h0
  · cases hgg
    exact (by decide : ∀ x ∈ edges1, x.2.2.1 = prog.exit x.1 →
      (x.1, (⟨x.2.2.2.fact, some x.2.1⟩ : DemandEdge)) ∈ revDemS) (m, j, _, g') (inv1 hg') rfl

/-- The reversed record `dKeep` is a reversed summary of run 1. -/
theorem revDem_set : Backward.revSummaryDemand prog R1 1 dKeep :=
  ⟨Jthis, KEEP.fact, ⟨r1_i1, Or.inr ⟨KEEP, run1_record.1, rfl⟩⟩, rfl⟩

/-- Backward run 2 for a backward demand `demB`: the user's design on the reversed program,
    seeded at both sinks, field limit 3, no backward record. -/
abbrev BS (demB : Dem) : Obj → Prop :=
  Backward.DB Pb cnt 3 demB emitM satI restrictU (fun _ _ => False) [] [0] sinks true

/-- The seed `(dto, [name], $, T)` (the sink pattern; no cut). -/
def SN : AFact := ⟨sinkName, false⟩
/-- The seed `(dto, [email], $, T)` (the sink pattern; no cut). -/
def SE : AFact := ⟨sinkEmail, false⟩
/-- The backward added fact of the name requirement in `setName`: `(this, [name], $, T)`. -/
def ANb : PFact := ⟨3, [1], .exact, .conc 1⟩

/-- The initial facts of backward run 2. -/
def initsB : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (1, Jem)]
/-- The edges of backward run 2 (`EMn` is here the requirement `(dto, [email], $, T)` before
    the call). -/
def edgesB : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 2, Backward.zeroAF), (0, zeroFact, 2, SN), (0, zeroFact, 2, SE),
   (0, zeroFact, 1, Backward.zeroAF), (0, zeroFact, 1, EMn), (0, zeroFact, 0, Backward.zeroAF),
   (1, zeroFact, 1, Backward.zeroAF), (1, zeroFact, 0, Backward.zeroAF), (1, Jem, 1, JemF),
   (1, Jem, 0, JemF)]
/-- The added facts of backward run 2: the name and the email requirements in `setName`. -/
def addedsB : List (MethodId × PFact) := [(1, ANb), (1, Jem)]

/-- Every object of backward run 2 is in the lists; no request; no vulnerability. -/
def InvB : Obj → Prop
  | .init M i => (M, i) ∈ initsB
  | .edge M i n f => (M, i, n, f) ∈ edgesB
  | .added M a => (M, a) ∈ addedsB
  | .req _ _ _ => False
  | .vuln _ _ _ _ => False

instance : DecidablePred InvB := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ initsB))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesB))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addedsB))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ _ _ => inferInstanceAs (Decidable False)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE BACKWARD RUN 2 OF PROGRAM S, for every backward demand inside the reversed
    summaries of run 1 (`revDemS`): the only non-zero premise is `(this, [email], $, T)` in
    `setName`; the name requirement `(this, [name], $, T)` is an added fact with no premise. -/
theorem invB (demB : Dem) (hb : ∀ m d, demB m d → (m, d) ∈ revDemS)
    {o : Obj} (h : BS demB o) : InvB o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ initsB, InvB (.edge x.1 x.2 (Pb.entry x.1) (startFact x.2)))
      (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    rw [Pb_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB, x.1 = 0 → x.2.2.1 = 1 →
        ∀ f' ∈ (transfer cnt 3 (Reverse.Stmt.rev G.srcS) x.2.2.2).facts,
          InvB (.edge 0 x.2.1 0 f'))
        (0, i, 1, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesB, x.1 = 1 → x.2.2.1 = 1 →
            ∀ f' ∈ (transfer cnt 3 (Reverse.Stmt.rev setS) x.2.2.2).facts,
              InvB (.edge 1 x.2.1 0 f'))
            (1, i, 1, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    rw [Pb_edges] at hE
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edgesB, x.1 = 0 → x.2.2.1 = 1 →
        ∀ t ∈ (transfer cnt 3 (Reverse.Stmt.rev G.srcS) x.2.2.2).reqs, False)
        (0, i, 1, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edgesB, x.1 = 1 → x.2.2.1 = 1 →
            ∀ t ∈ (transfer cnt 3 (Reverse.Stmt.rev setS) x.2.2.2).reqs, False)
            (1, i, 1, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB, x.1 = 0 → x.2.2.1 = 2 →
          memB x.2.2.2.fact.base (Reverse.Call.rev callSet).touched = false →
            InvB (.edge 0 x.2.1 1 x.2.2.2))
          (0, i, 2, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e ∈ (Reverse.Call.rev callSet).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
            InvB (.added 1 a.fact))
          (0, i, 2, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a d j _ hd he ih =>
    exact (by decide : ∀ x ∈ revDemS, ∀ y ∈ addedsB, x.1 = y.1 →
      ∀ j ∈ (emitM x.2.din y.2).toList, InvB (.init x.1 j))
      (m, d) (hb m d hd) (m, a) ih rfl j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edgesB, x.1 = 0 → x.2.2.1 = 2 →
          ∀ e1 ∈ (Reverse.Call.rev callSet).toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ initsB, y.1 = 1 →
          ∀ z ∈ edgesB, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 0 →
          ∀ dd ∈ revDemS, dd.1 = 1 → ∀ g' ∈ (restrictU y.2 z.2.2.2 dd.2).toList,
          satI y.2 a.fact = true →
          ∀ r ∈ (applySummary a y.2 g').facts,
          ∀ e2 ∈ (Reverse.Call.rev callSet).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvB (.edge 0 x.2.1 1 (limitF cnt 3 r')))
          (0, i, 2, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl (1, j, 0, g) ihg rfl rfl rfl
          (1, d) (hb _ _ hd) rfl g' (RCases.mem_toList_of_eq_some hres) hsat
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | retRec _ _ _ _ hrec _ _ _ _ _ => exact hrec.elim
  | reqSink _ hs _ _ => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | vuln _ hs _ _ => cases hs
  | @clean M i n f n' cl f' _ hE _ _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE _ _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @filt M i n f n' b may _ hE _ _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zpass M n n' c _ hE _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @zin M n n' c _ _ hE _ =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head => decide
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @seed M n s hs _ _ =>
    cases hs with
    | head => decide
    | tail _ h => cases h with
      | head => decide
      | tail _ h => cases h
  | @zret M n n' c g r e2 r' _ _ hE _ hr he2 hr' _ ihg =>
    rw [Pb_edges] at hE
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ y ∈ edgesB, y.1 = 1 → y.2.1 = zeroFact → y.2.2.1 = 0 →
          ∀ r ∈ (applySummary Backward.zeroAF zeroFact y.2.2.2).facts,
          ∀ e2 ∈ (Reverse.Call.rev callSet).fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            InvB (.edge 0 zeroFact 1 (limitF cnt 3 r')))
          (1, zeroFact, 0, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

#print axioms invB

-- the name requirement: the exclusion `{name}` of the reversed record rejects it (no premise);
-- the email requirement: the reversed record emits it as the backward premise
example : emitM dKeep.din ANb = none := by decide
example : emitM dKeep.din Jem = some Jem := by decide
-- the reversed keep edge `this.* → this.*/{name}` keeps `(this, [email], $, T)`
example : (transfer cnt 3 (Reverse.Stmt.rev setS) JemF).facts = [JemF] := by decide

/-! #### The objects of backward run 2, derived -/

section DeriveB
variable (demB : Dem) (hd : demB 1 dKeep)

/-- Backward run 2: the zero fact at the forward exit of `root`. -/
theorem b_e02 : BS demB (.edge 0 zeroFact 2 Backward.zeroAF) :=
  Backward.DB.start (Backward.DB.root (List.Mem.head _))
/-- The sink rule at the forward exit of `root`: the seed `(dto, [email], $, T)`. -/
theorem b_sE : BS demB (.edge 0 zeroFact 2 SE) :=
  Backward.DB.seed (s := sinkEmail) hsE (b_e02 demB)
/-- The email requirement enters `setName` through the reversed binding back
    (`dto.* → this.*`): the added fact `(this, [email], $, T)`. -/
theorem b_ad : BS demB (.added 1 Jem) :=
  Backward.DB.added (c := Reverse.Call.rev callSet) (e := revEdge bBack.1 bBack.2)
    (a := JemF) (b_sE demB) hb_c (List.Mem.head _) (by decide)

include hd in
/-- The reversed record `dKeep` emits the backward premise `(this, [email], $, T)`. -/
theorem b_iJem : BS demB (.init 1 Jem) := Backward.DB.initR (b_ad demB) hd (by decide)

include hd in
/-- The backward summary of `setName`: `(this, [email], $, T) → (this, [email], $, T)` at the
    forward entry of `setName`. -/
theorem b_eJem : BS demB (.edge 1 Jem 0 JemF) :=
  Backward.DB.step (Backward.DB.start (b_iJem demB hd)) hb_set (by decide)

end DeriveB

/-! #### The hand-off, exactly -/

/-- The hand-off of program S: the demand `dEmail` of `setName` and the zero demand (THE DEMAND
    WRITTEN BY HAND for run 3). -/
def demS (m : MethodId) (d : DemandEdge) : Prop := d = Backward.zeroDem ∨ (m = 1 ∧ d = dEmail)

/-- The demand edges of `demS` as a list. -/
def demListS : List (MethodId × DemandEdge) :=
  [(0, Backward.zeroDem), (1, Backward.zeroDem), (1, dEmail)]

/-- The list `demListS` is inside `demS`. -/
theorem demListS_cases {m : MethodId} {d : DemandEdge} (h : (m, d) ∈ demListS) : demS m d := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ h => cases h with
    | head => exact Or.inl rfl
    | tail _ h => cases h with
      | head => exact Or.inr ⟨rfl, rfl⟩
      | tail _ h => cases h

/-- The demand edges of `demS` (in every method). -/
theorem demS_mem {m : MethodId} {d : DemandEdge} (h : demS m d) :
    d ∈ [Backward.zeroDem, dEmail] := by
  rcases h with rfl | ⟨_, rfl⟩
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)

/-- PROGRAM S, THE HAND-OFF EXACTLY. For every backward demand `demB` inside the reversed
    summaries of run 1 that has the reversed record `dKeep` of `setName`, the hand-off of
    backward run 2 is the demand `dEmail = ((this, [email], $, T), some (this, [email], $, T))`
    of `setName` and the zero demand. There is NO demand for `this.name`. -/
theorem handoff_exact (demB : Dem)
    (hb : ∀ m d, demB m d → (m, d) ∈ revDemS) (hd : demB 1 dKeep) (m : MethodId)
    (d : DemandEdge) :
    Backward.demOf Pb (BS demB) m d ↔ demS m d := by
  constructor
  · rintro (h | ⟨g, hg, rfl⟩ | ⟨jb, gb, hjb, hne, hgb, rfl⟩)
    · exact Or.inl h
    · have hz := (by decide : ∀ x ∈ edgesB, x.2.1 = zeroFact → x.2.2.1 = 0 →
        x.2.2.2.fact = zeroFact) (m, zeroFact, 0, g) (invB demB hb hg) rfl rfl
      exact Or.inl (by rw [hz]; rfl)
    · exact demListS_cases ((by decide : ∀ x ∈ initsB, x.2 ≠ zeroFact →
        ∀ y ∈ edgesB, y.1 = x.1 → y.2.1 = x.2 → y.2.2.1 = 0 →
          (x.1, (⟨y.2.2.2.fact, some x.2⟩ : DemandEdge)) ∈ demListS)
        (m, jb) (invB demB hb hjb) hne (m, jb, 0, gb) (invB demB hb hgb) rfl rfl rfl)
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨Jem, JemF, b_iJem demB hd, by decide, b_eJem demB hd, rfl⟩)

#print axioms handoff_exact

/-- The hand-off after run 1 (the iteration `D6T`, `DB`, `DRT`). -/
abbrev HT : MethodId → DemandEdge → Prop :=
  Backward.demOf Pb (BS (Backward.revSummaryDemand prog R1))

/-- The hand-off after run 1 is exactly the demand written by hand, `demS`. -/
theorem HT_exact (m : MethodId) (d : DemandEdge) : HT m d ↔ demS m d :=
  handoff_exact _ (fun _ _ h => revDem_bound h) revDem_set m d

#print axioms HT_exact

/-! ### Forward run 3 with must-premises (`DRT`), completely

  For every demand inside `demS` and every record set inside the run-1 records `recsList`. -/

/-- Run 3 of program S for a demand and a record set. -/
abbrev R3 (demand : Dem) (recs : TRecs) : TObj → Prop :=
  DRT prog G.taint cnt 3 demand emitM satI restrictU recs sinks [0]

/-- The run-1 records as a record set. -/
def recsS : TRecs := fun m x => (m, x) ∈ recsList

/-- The initial facts of run 3. -/
def inits3 : List (MethodId × PFact × Bool) := [(0, zeroFact, false), (1, Jem, false)]
/-- The edges of run 3. -/
def edges3 : List (MethodId × PFact × Bool × Node × AFact) :=
  [(0, zeroFact, false, 0, G.Z), (0, zeroFact, false, 1, G.Z), (0, zeroFact, false, 1, G.DTO),
   (0, zeroFact, false, 2, G.Z), (0, zeroFact, false, 2, EMn), (0, zeroFact, false, 2, G.DTOd),
   (1, Jem, false, 0, JemF), (1, Jem, false, 1, JemF)]
/-- The added facts of run 3: `(this, [], [any], T)`, `[any-taint]` on its link. -/
def addeds3 : List (MethodId × PFact × Bool) := [(1, Athis, true)]

/-- Every object of run 3 is in the lists; no request; a normal vulnerability is at the email
    sink. -/
def Inv3 : TObj → Prop
  | .init M j mj => (M, j, mj) ∈ inits3
  | .edge M j mj n f => (M, j, mj, n, f) ∈ edges3
  | .added M a am => (M, a, am) ∈ addeds3
  | .req _ _ _ => False
  | .vuln _ _ s d => d = true ∨ s = sinkEmail

instance : DecidablePred Inv3 := fun o =>
  match o with
  | .init M j mj => inferInstanceAs (Decidable ((M, j, mj) ∈ inits3))
  | .edge M j mj n f => inferInstanceAs (Decidable ((M, j, mj, n, f) ∈ edges3))
  | .added M a am => inferInstanceAs (Decidable ((M, a, am) ∈ addeds3))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ s d => inferInstanceAs (Decidable (d = true ∨ s = sinkEmail))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 3 OF PROGRAM S (with must-premises), for every demand inside `demS` and
    every record set inside the run-1 records: the only premise of `setName` is
    `(this, [email], $, T)` (not must: its tail is `$`); the sink edges at node 2 are the normal
    `zero → (dto, [email], $, T)` (the restricted summary) and the demand
    `zero → (dto, [], [any], T)` (the record); no normal sink edge triggers the name sink. -/
theorem inv3 (demand : Dem) (recs : TRecs)
    (hd : ∀ m d, demand m d → demS m d) (hr : ∀ m x, recs m x → (m, x) ∈ recsList)
    {o : TObj} (h : R3 demand recs o) : Inv3 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M j mj _ ih =>
    exact (by decide : ∀ x ∈ inits3,
      Inv3 (.edge x.1 x.2.1 x.2.2 (prog.entry x.1) (startT x.2.1 x.2.2))) (M, j, mj) ih
  | @step M i mi n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 0 →
        ∀ f' ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2.2).facts,
          Inv3 (.edge 0 x.2.1 x.2.2.1 1 f'))
        (0, i, mi, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges3, x.1 = 1 → x.2.2.2.1 = 0 →
            ∀ f' ∈ (transferT G.taint cnt 3 setS x.2.2.2.2).facts,
              Inv3 (.edge 1 x.2.1 x.2.2.1 1 f'))
            (1, i, mi, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i mi n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 0 →
        ∀ t ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2.2).reqs, False)
        (0, i, mi, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges3, x.1 = 1 → x.2.2.2.1 = 0 →
            ∀ t ∈ (transferT G.taint cnt 3 setS x.2.2.2.2).reqs, False)
            (1, i, mi, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i mi n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 1 →
          memB x.2.2.2.2.fact.base callSet.touched = false →
            Inv3 (.edge 0 x.2.1 x.2.2.1 2 x.2.2.2.2))
          (0, i, mi, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i mi n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 1 → ∀ e ∈ callSet.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2.2 e.1 e.2).facts,
            Inv3 (.added callSet.callee a.fact (a.fact.kind.isAny && !a.demand)))
          (0, i, mi, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a am d j mj _ hdm he ih =>
    exact (by decide : ∀ y ∈ addeds3, ∀ dd ∈ [Backward.zeroDem, dEmail],
      ∀ jm ∈ (emitTWith emitM dd.din y.2.1 y.2.2).toList, Inv3 (.init y.1 jm.1 jm.2))
      (m, a, am) ih d (demS_mem (hd m d hdm)) (j, mj) (RCases.mem_toList_of_eq_some he)
  | @ret M i mi n f n' c e1 a j mj g d g' r e2 r' _ hE he1 ha _ _ hdm hres hsat hrr he2 hr'
      ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 1 →
          ∀ e1 ∈ callSet.toCallee, ∀ a ∈ (applyEdge x.2.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ inits3, y.1 = 1 →
          ∀ z ∈ edges3, z.1 = 1 → z.2.1 = y.2.1 → z.2.2.1 = y.2.2 → z.2.2.2.1 = 1 →
          ∀ dd ∈ [Backward.zeroDem, dEmail], ∀ g' ∈ (restrictU y.2.1 z.2.2.2.2 dd).toList,
          satI y.2.1 a.fact = true →
          ∀ r ∈ (applySummary a y.2.1 g').facts,
          ∀ e2 ∈ callSet.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            Inv3 (.edge 0 x.2.1 x.2.2.1 2 (limitF cnt 3 r')))
          (0, i, mi, 1, f) ihf rfl rfl e1 he1 a ha (1, j, mj) ihj rfl (1, j, mj, 1, g) ihg rfl
          rfl rfl rfl d (demS_mem (hd _ d hdm)) g' (RCases.mem_toList_of_eq_some hres) hsat r hrr
          e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @retRec M i mi n f n' c e1 a j mj g r e2 r' _ hE he1 ha hrec hsa hrr he2 hr' ihf =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 1 →
          ∀ e1 ∈ callSet.toCallee, ∀ a ∈ (applyEdge x.2.2.2.2 e1.1 e1.2).facts,
          ∀ q ∈ recsList, q.1 = 1 →
          (satI q.2.1 a.fact = true ∨ applicable q.2.1 a.fact = true) →
          ∀ r ∈ (applySummary a q.2.1 q.2.2.2).facts,
          ∀ e2 ∈ callSet.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            Inv3 (.edge 0 x.2.1 x.2.2.1 2
              (limitF cnt 3 (recLayer q.2.2.1 (satI q.2.1 a.fact) r'))))
          (0, i, mi, 1, f) ihf rfl rfl e1 he1 a ha (1, (j, mj, g)) (hr _ _ hrec) rfl hsa r hrr
          e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i mi n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 2 → ∀ s ∈ [sinkName, sinkEmail],
        check x.2.1 x.2.2.2.2 s = .none ∨ check x.2.1 x.2.2.2.2 s = .triggered := by decide
    cases hs with
    | head =>
      rcases hnr (0, i, mi, 2, f) ih rfl rfl sinkName (List.Mem.head _) with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs with
      | head =>
        rcases hnr (0, i, mi, 2, f) ih rfl rfl sinkEmail (List.Mem.tail _ (List.Mem.head _))
          with h | h
        · rw [h] at hc; exact Check.noConfusion hc
        · rw [h] at hc; exact Check.noConfusion hc
      | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i mi n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact Or.inl ((by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.1 = 2 →
        check x.2.1 x.2.2.2.2 sinkName = .triggered → x.2.2.2.2.demand = true)
        (0, i, mi, 2, f) ih rfl rfl hc)
    | tail _ hs => cases hs with
      | head => exact Or.inr rfl
      | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv3

/-! ### Run 3: the derivations -/

-- THE EMISSION: the `[any-taint]` added fact `(this, [], [any-taint], T)` against
-- `D-c = (this, [email], $, T)` gives the premise `(this, [email], $, T)`, not must (decision 8,
-- row `[any-taint]`, column `$`)
example : emitT dEmail.din Athis true = some (Jem, false) := by decide
-- `this.name = n` on the premise: the keep edge keeps `(this, [email], $, T)` (`email ∉ {name}`)
example : (transferT G.taint cnt 3 setS JemF).facts = [JemF] := by decide
-- the restriction by `D-p = (this, [email], $, T)` keeps it; the added fact satisfies the premise
example : restrictU Jem JemF dEmail = some JemF := by decide
example : satI Jem Athis = true := by decide

/-- THE RESTRICTED SUMMARY GIVES THE NORMAL `email` FACT: the summary
    `(this, [email], $, T) → (this, [email], $, T)` of `setName`, restricted by `dEmail`, applied
    to the added fact `(this, [], [any], T)` of the normal link (spec: `[any-taint]`), is case
    `above` with an `[any-taint]` fact: every location below `this` carries the mark, so nothing
    is lost (ap.md §4.1 step 3, case `above`, the row `$`): `(this, [email], $, T)` in the NORMAL
    layer; the binding back gives `(dto, [email], $, T)`, normal; it triggers the email sink and
    not the name sink. -/
theorem email_app_normal :
    aboveCase .any .exact [2] [2] .exact = some ([2], .exact, false) ∧
    (applySummary ⟨Athis, false⟩ Jem JemF).facts = [JemF] ∧
    (applyEdge JemF bBack.1 bBack.2).facts = [EMn] ∧
    limitF cnt 3 EMn = EMn ∧
    check zeroFact EMn sinkEmail = .triggered ∧ check zeroFact EMn sinkName = .none := by decide

#print axioms email_app_normal

/-- The record application triggers both sinks (in the demand layer). -/
theorem record_sinks :
    check zeroFact G.DTOd sinkName = .triggered ∧ check zeroFact G.DTOd sinkEmail = .triggered := by
  decide

section Run3
variable (demand : Dem) (recs : TRecs)

/-- Run 3: the source edge `zero → (dto, [], [any-taint], T)`, normal. -/
theorem t3_e01 : R3 demand recs (.edge 0 zeroFact false 1 G.DTO) :=
  DRT.step (DRT.start (DRT.root (List.Mem.head _))) hE00 (by decide)

/-- Run 3: the added fact of `setName` is `[any-taint]` on its link (`am = true`). -/
theorem t3_ad : R3 demand recs (.added 1 Athis true) :=
  DRT.added (c := callSet) (e := bThis) (a := ⟨Athis, false⟩) (t3_e01 demand recs) hE01
    (List.Mem.head _) (by decide)

/-- Run 3, the record: for every record set that has the run-1 record of `setName`, the record
    application gives the sink edge `zero → (dto, [], [any], T)` in the DEMAND layer (the
    exclusion `{name}` demotes it; `recLayer` keeps it: the record is not must). -/
theorem t3_rec (hrec : recs 1 (Jthis, false, KEEP)) :
    R3 demand recs (.edge 0 zeroFact false 2 G.DTOd) :=
  DRT.retRec (c := callSet) (e1 := bThis) (a := ⟨Athis, false⟩) (j := Jthis) (mj := false)
    (g := KEEP) (r := THISd) (e2 := bBack) (r' := G.DTOd) (t3_e01 demand recs) hE01
    (List.Mem.head _) (by decide) hrec (Or.inl (by decide)) (by decide) (List.Mem.head _)
    (by decide)

/-- Run 3 reports `sink(dto.name)` in the DEMAND layer (through the record). -/
theorem run3_name_demand (hrec : recs 1 (Jthis, false, KEEP)) :
    R3 demand recs (.vuln 0 2 sinkName true) :=
  DRT.vuln (t3_rec demand recs hrec) hsN (by decide)

#print axioms run3_name_demand

/-- Run 3 reports `sink(dto.email)` in the demand layer too (through the record). -/
theorem run3_email_demand (hrec : recs 1 (Jthis, false, KEEP)) :
    R3 demand recs (.vuln 0 2 sinkEmail true) :=
  DRT.vuln (t3_rec demand recs hrec) hsE (by decide)

#print axioms run3_email_demand

variable (hd : demand 1 dEmail)

include hd in
/-- Run 3: the emission gives the premise `(this, [email], $, T)` of `setName` (not must). -/
theorem t3_iJem : R3 demand recs (.init 1 Jem false) :=
  DRT.initR (d := dEmail) (t3_ad demand recs) hd (by decide)

include hd in
/-- Run 3: the summary `(this, [email], $, T) → (this, [email], $, T)` of `setName`, normal. -/
theorem t3_eJem : R3 demand recs (.edge 1 Jem false 1 JemF) :=
  DRT.step (DRT.start (t3_iJem demand recs hd)) hE10 (by decide)

include hd in
/-- THE EMAIL SINK EDGE IS NORMAL: the restricted summary of `setName` gives
    `zero → (dto, [email], $, T)` at the sink node, in the NORMAL layer. -/
theorem run3_email_sink_normal : R3 demand recs (.edge 0 zeroFact false 2 EMn) :=
  DRT.ret (c := callSet) (e1 := bThis) (a := ⟨Athis, false⟩) (j := Jem) (mj := false) (g := JemF)
    (d := dEmail) (g' := JemF) (r := JemF) (e2 := bBack) (r' := EMn) (t3_e01 demand recs) hE01
    (List.Mem.head _) (by decide) (t3_iJem demand recs hd) (t3_eJem demand recs hd) hd
    (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms run3_email_sink_normal

include hd in
/-- Run 3 reports `sink(dto.email)` in the NORMAL layer. -/
theorem run3_email_vuln_normal : R3 demand recs (.vuln 0 2 sinkEmail false) :=
  DRT.vuln (run3_email_sink_normal demand recs hd) hsE (by decide)

#print axioms run3_email_vuln_normal

include hd in
/-- RUN 3 CONFIRMS `sink(dto.email)` (`AnyTaint.ConfirmedT`): the normal sink edge under the
    supported zero premise of the root, with a triggered check. For every demand that has the
    demand `dEmail` of `setName` and every record set. -/
theorem run3_email_confirmed :
    ConfirmedT prog G.taint cnt 3 demand emitM satI restrictU recs sinks [0] 0 2 sinkEmail :=
  ⟨zeroFact, false, EMn, run3_email_sink_normal demand recs hd, SupT.root (List.Mem.head _), rfl,
    hsE, by decide⟩

#print axioms run3_email_confirmed

end Run3

/-- Run 3 does NOT report `sink(dto.name)` in the normal layer, for every demand inside `demS` and
    every record set inside the run-1 records (the complete run `inv3`): the only fact that
    triggers it is the demoted record result `(dto, [], [any], T)`. -/
theorem run3_name_no_normal (demand : Dem) (recs : TRecs)
    (hd : ∀ m d, demand m d → demS m d) (hr : ∀ m x, recs m x → (m, x) ∈ recsList) :
    ¬ R3 demand recs (.vuln 0 2 sinkName false) := by
  intro h
  rcases inv3 demand recs hd hr h with h' | h'
  · exact Bool.noConfusion h'
  · exact absurd h' (by decide)

#print axioms run3_name_no_normal

/-- Run 3 does NOT confirm `sink(dto.name)`: it is a DEMAND entry only. -/
theorem run3_name_not_confirmed (demand : Dem) (recs : TRecs)
    (hd : ∀ m d, demand m d → demS m d) (hr : ∀ m x, recs m x → (m, x) ∈ recsList) :
    ¬ ConfirmedT prog G.taint cnt 3 demand emitM satI restrictU recs sinks [0] 0 2 sinkName := by
  rintro ⟨i, mi, f, hf, _, hdem, hs, hc⟩
  have hv := DRT.vuln hf hs hc
  rw [hdem] at hv
  exact run3_name_no_normal demand recs hd hr hv

#print axioms run3_name_not_confirmed

/-! ### Run 3 without a record: the name sink is not reported at all

  The demand entry of `sink(dto.name)` comes ONLY from the record: the backward run hands off no
  demand for `this.name` (`handoff_exact`), so without the record run 3 has no fact that
  triggers the name sink. -/

/-- The edges of run 3 without a record: those of `edges3` without the record result
    `zero → (dto, [], [any], T)`. -/
def edges3N : List (MethodId × PFact × Bool × Node × AFact) :=
  [(0, zeroFact, false, 0, G.Z), (0, zeroFact, false, 1, G.Z), (0, zeroFact, false, 1, G.DTO),
   (0, zeroFact, false, 2, G.Z), (0, zeroFact, false, 2, EMn), (1, Jem, false, 0, JemF),
   (1, Jem, false, 1, JemF)]

/-- Every object of run 3 without a record is in the lists; every vulnerability is the normal
    email vulnerability. -/
def Inv3N : TObj → Prop
  | .init M j mj => (M, j, mj) ∈ inits3
  | .edge M j mj n f => (M, j, mj, n, f) ∈ edges3N
  | .added M a am => (M, a, am) ∈ addeds3
  | .req _ _ _ => False
  | .vuln _ _ s d => s = sinkEmail ∧ d = false

instance : DecidablePred Inv3N := fun o =>
  match o with
  | .init M j mj => inferInstanceAs (Decidable ((M, j, mj) ∈ inits3))
  | .edge M j mj n f => inferInstanceAs (Decidable ((M, j, mj, n, f) ∈ edges3N))
  | .added M a am => inferInstanceAs (Decidable ((M, a, am) ∈ addeds3))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln _ _ s d => inferInstanceAs (Decidable (s = sinkEmail ∧ d = false))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 3 OF PROGRAM S WITHOUT A RECORD, for every demand inside `demS`: the only
    sink edge at node 2 (besides zero) is the normal `zero → (dto, [email], $, T)`, so the only
    vulnerability is the normal email vulnerability. -/
theorem inv3N (demand : Dem) (hd : ∀ m d, demand m d → demS m d)
    {o : TObj} (h : R3 demand (fun _ _ => False) o) : Inv3N o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M j mj _ ih =>
    exact (by decide : ∀ x ∈ inits3,
      Inv3N (.edge x.1 x.2.1 x.2.2 (prog.entry x.1) (startT x.2.1 x.2.2))) (M, j, mj) ih
  | @step M i mi n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges3N, x.1 = 0 → x.2.2.2.1 = 0 →
        ∀ f' ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2.2).facts,
          Inv3N (.edge 0 x.2.1 x.2.2.1 1 f'))
        (0, i, mi, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges3N, x.1 = 1 → x.2.2.2.1 = 0 →
            ∀ f' ∈ (transferT G.taint cnt 3 setS x.2.2.2.2).facts,
              Inv3N (.edge 1 x.2.1 x.2.2.1 1 f'))
            (1, i, mi, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE
  | @reqStmt M i mi n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges3N, x.1 = 0 → x.2.2.2.1 = 0 →
        ∀ t ∈ (transferT G.taint cnt 3 G.srcS x.2.2.2.2).reqs, False)
        (0, i, mi, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges3N, x.1 = 1 → x.2.2.2.1 = 0 →
            ∀ t ∈ (transferT G.taint cnt 3 setS x.2.2.2.2).reqs, False)
            (1, i, mi, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i mi n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3N, x.1 = 0 → x.2.2.2.1 = 1 →
          memB x.2.2.2.2.fact.base callSet.touched = false →
            Inv3N (.edge 0 x.2.1 x.2.2.1 2 x.2.2.2.2))
          (0, i, mi, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i mi n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3N, x.1 = 0 → x.2.2.2.1 = 1 → ∀ e ∈ callSet.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2.2 e.1 e.2).facts,
            Inv3N (.added callSet.callee a.fact (a.fact.kind.isAny && !a.demand)))
          (0, i, mi, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @initR m a am d j mj _ hdm he ih =>
    exact (by decide : ∀ y ∈ addeds3, ∀ dd ∈ [Backward.zeroDem, dEmail],
      ∀ jm ∈ (emitTWith emitM dd.din y.2.1 y.2.2).toList, Inv3N (.init y.1 jm.1 jm.2))
      (m, a, am) ih d (demS_mem (hd m d hdm)) (j, mj) (RCases.mem_toList_of_eq_some he)
  | @ret M i mi n f n' c e1 a j mj g d g' r e2 r' _ hE he1 ha _ _ hdm hres hsat hrr he2 hr'
      ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3N, x.1 = 0 → x.2.2.2.1 = 1 →
          ∀ e1 ∈ callSet.toCallee, ∀ a ∈ (applyEdge x.2.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ inits3, y.1 = 1 →
          ∀ z ∈ edges3N, z.1 = 1 → z.2.1 = y.2.1 → z.2.2.1 = y.2.2 → z.2.2.2.1 = 1 →
          ∀ dd ∈ [Backward.zeroDem, dEmail], ∀ g' ∈ (restrictU y.2.1 z.2.2.2.2 dd).toList,
          satI y.2.1 a.fact = true →
          ∀ r ∈ (applySummary a y.2.1 g').facts,
          ∀ e2 ∈ callSet.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            Inv3N (.edge 0 x.2.1 x.2.2.1 2 (limitF cnt 3 r')))
          (0, i, mi, 1, f) ihf rfl rfl e1 he1 a ha (1, j, mj) ihj rfl (1, j, mj, 1, g) ihg rfl
          rfl rfl rfl d (demS_mem (hd _ d hdm)) g' (RCases.mem_toList_of_eq_some hres) hsat r hrr
          e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | retRec _ _ _ _ hrec _ _ _ _ _ => exact hrec.elim
  | @reqSink M i mi n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges3N, x.1 = 0 → x.2.2.2.1 = 2 → ∀ s ∈ [sinkName, sinkEmail],
        check x.2.1 x.2.2.2.2 s = .none ∨ check x.2.1 x.2.2.2.2 s = .triggered := by decide
    cases hs with
    | head =>
      rcases hnr (0, i, mi, 2, f) ih rfl rfl sinkName (List.Mem.head _) with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs with
      | head =>
        rcases hnr (0, i, mi, 2, f) ih rfl rfl sinkEmail (List.Mem.tail _ (List.Mem.head _))
          with h | h
        · rw [h] at hc; exact Check.noConfusion hc
        · rw [h] at hc; exact Check.noConfusion hc
      | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i mi n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact absurd hc ((by decide : ∀ x ∈ edges3N, x.1 = 0 → x.2.2.2.1 = 2 →
        check x.2.1 x.2.2.2.2 sinkName ≠ .triggered) (0, i, mi, 2, f) ih rfl rfl)
    | tail _ hs => cases hs with
      | head =>
        exact ⟨rfl, (by decide : ∀ x ∈ edges3N, x.1 = 0 → x.2.2.2.1 = 2 →
          check x.2.1 x.2.2.2.2 sinkEmail = .triggered → x.2.2.2.2.demand = false)
          (0, i, mi, 2, f) ih rfl rfl hc⟩
      | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv3N

/-- WITHOUT THE RECORD, run 3 does not report `sink(dto.name)` in any layer (for every demand
    inside `demS`): its demand entry in `run3_name_demand` comes only from the record. -/
theorem run3_name_needs_record (demand : Dem) (hd : ∀ m d, demand m d → demS m d) (b : Bool) :
    ¬ R3 demand (fun _ _ => False) (.vuln 0 2 sinkName b) := by
  intro h
  exact absurd (inv3N demand hd h).1 (by decide)

#print axioms run3_name_needs_record

/-! ### Run 3 with the derived hand-off: the iteration `D6T` → `DB` → `DRT` -/

/-- THE ITERATION ON PROGRAM S, with the hand-off `HT` of backward run 2 and the run-1 records
    (`recsS`): `sink(dto.email)` is CONFIRMED, and `sink(dto.name)` is reported in the demand
    layer only (not confirmed). -/
theorem run3_handoff :
    ConfirmedT prog G.taint cnt 3 HT emitM satI restrictU recsS sinks [0] 0 2 sinkEmail ∧
    R3 HT recsS (.vuln 0 2 sinkName true) ∧
    ¬ R3 HT recsS (.vuln 0 2 sinkName false) ∧
    ¬ ConfirmedT prog G.taint cnt 3 HT emitM satI restrictU recsS sinks [0] 0 2 sinkName :=
  ⟨run3_email_confirmed HT recsS ((HT_exact 1 dEmail).mpr (Or.inr ⟨rfl, rfl⟩)),
   run3_name_demand HT recsS (List.Mem.tail _ (List.Mem.head _)),
   run3_name_no_normal HT recsS (fun m d h => (HT_exact m d).mp h) (fun _ _ h => h),
   run3_name_not_confirmed HT recsS (fun m d h => (HT_exact m d).mp h) (fun _ _ h => h)⟩

#print axioms run3_handoff

/-! ### The `.any` form of the demand: a must-premise

  With the demand `(this, [email], [any], T)` (the `[any]` form of `dEmail`), the `[any-taint]`
  added fact emits the MUST premise `(this, [email], [any-taint], T)`; it starts in the normal
  layer, the keep edge keeps it, and the restricted summary gives the normal
  `(dto, [email], [any-taint], T)`, which triggers the email sink. -/

/-- The `[any]` form of the email pattern: `(this, [email], [any], T)`. -/
def JemA : PFact := ⟨3, [2], .any, .conc 1⟩
/-- `(this, [email], [any-taint], T)`, normal. -/
def JemAn : AFact := ⟨JemA, false⟩
/-- The `[any]` form of the demand of `setName`: `D-c = D-p = (this, [email], [any], T)`. -/
def dEmailA : DemandEdge := ⟨JemA, some JemA⟩
/-- `(dto, [email], [any-taint], T)`, normal. -/
def EMAn : AFact := ⟨⟨1, [2], .any, .conc 1⟩, false⟩

example : emitT dEmailA.din Athis true = some (JemA, true) := by decide
example : startT JemA true = JemAn := rfl
example : (transferT G.taint cnt 3 setS JemAn).facts = [JemAn] := by decide
example : restrictU JemA JemAn dEmailA = some JemAn := by decide
example : (applySummary ⟨Athis, false⟩ JemA JemAn).facts = [JemAn] := by decide
example : (applyEdge JemAn bBack.1 bBack.2).facts = [EMAn] := by decide
example : check zeroFact EMAn sinkEmail = .triggered := by decide
-- the `[any]` email fact overlaps only the email sink
example : check zeroFact EMAn sinkName = .none := by decide

section Run3A
variable (demand : Dem) (recs : TRecs) (hd : demand 1 dEmailA)

include hd in
/-- Run 3, the `.any` demand: the MUST premise `(this, [email], [any-taint], T)` of `setName`. -/
theorem run3A_must : R3 demand recs (.init 1 JemA true) :=
  DRT.initR (d := dEmailA) (t3_ad demand recs) hd (by decide)

#print axioms run3A_must

include hd in
/-- The summary of the must-premise: `(this, [email], [any-taint], T) →
    (this, [email], [any-taint], T)`, normal. -/
theorem t3A_e : R3 demand recs (.edge 1 JemA true 1 JemAn) :=
  DRT.step (DRT.start (run3A_must demand recs hd)) hE10 (by decide)

include hd in
/-- The `.any` demand: the email sink edge `zero → (dto, [email], [any-taint], T)` is NORMAL. -/
theorem run3A_email_sink_normal : R3 demand recs (.edge 0 zeroFact false 2 EMAn) :=
  DRT.ret (c := callSet) (e1 := bThis) (a := ⟨Athis, false⟩) (j := JemA) (mj := true)
    (g := JemAn) (d := dEmailA) (g' := JemAn) (r := JemAn) (e2 := bBack) (r' := EMAn)
    (t3_e01 demand recs) hE01 (List.Mem.head _) (by decide) (run3A_must demand recs hd)
    (t3A_e demand recs hd) hd (by decide) (by decide) (by decide) (List.Mem.head _) (by decide)

#print axioms run3A_email_sink_normal

include hd in
/-- The `.any` demand: RUN 3 CONFIRMS `sink(dto.email)` (`AnyTaint.ConfirmedT`). -/
theorem run3A_email_confirmed :
    ConfirmedT prog G.taint cnt 3 demand emitM satI restrictU recs sinks [0] 0 2 sinkEmail :=
  ⟨zeroFact, false, EMAn, run3A_email_sink_normal demand recs hd, SupT.root (List.Mem.head _),
    rfl, hsE, by decide⟩

#print axioms run3A_email_confirmed

include hd in
/-- The must-premise of the `.any` demand is SUPPORTED (`AnyTaint.SupT`): it lies inside the
    normal `[any-taint]` binding `(this, [], [any-taint], T)` with its mark. -/
theorem run3A_must_supported :
    SupT prog G.taint cnt 3 demand emitM satI restrictU recs sinks [0] 1 JemA true :=
  SupT.call (c := callSet) (e := bThis) (a := ⟨Athis, false⟩) (SupT.root (List.Mem.head _))
    (t3_e01 demand recs) rfl hE01 (List.Mem.head _) (by decide) rfl (run3A_must demand recs hd)
    (Or.inr (Or.inr ⟨rfl, ⟨1, rfl⟩, rfl, by decide, Or.inr ⟨rfl, rfl⟩⟩))

#print axioms run3A_must_supported

end Run3A

/-! ### `sink(dto.name)` is not real; `sink(dto.email)` is real -/

/-- The reaching locations of `setName` from an entry location `l0`: at the entry, `l0` itself;
    at the exit, a location that came from `this` is a location of `this` whose path does not
    start with `name` (the keep edge excludes `name`, and the gen edge reads `n`). -/
def InvC (n : Node) (l0 l : Loc) : Prop :=
  (n = 0 → l = l0) ∧ (n = 1 → l0.base = 3 → l.base = 3 ∧ ∀ τ, l.path ≠ 1 :: τ)

/-- The reaching locations of `root` from the zero location: the zero location; after the source
    the locations of `dto`; after the call, not below `dto.name`. -/
def InvR (n : Node) (l : Loc) : Prop :=
  l = zeroLoc ∨ (n ≠ 0 ∧ l.base = 1 ∧ (n = 2 → ∀ τ, l.path ≠ 1 :: τ))

/-- THE REACHING LOCATIONS of program S (`InvC` in `setName`, `InvR` in `root`). -/
theorem flow_inv {M : MethodId} {l0 : Loc} {n : Node} {l : Loc} (h : Flow prog M l0 n l) :
    (M = 1 → InvC n l0 l) ∧ (M = 0 → l0 = zeroLoc → InvR n l) := by
  induction h with
  | start M l0 =>
    refine ⟨fun _ => ⟨fun _ => rfl, fun h1 => absurd h1 (by decide : ¬ ((0 : Node) = 1))⟩,
      fun _ h0 => Or.inl h0⟩
  | @step M l0 n l n' l' s _ hE hs ih =>
    cases hE with
    | head =>
      refine ⟨fun h1 => absurd h1 (by decide), fun _ h0 => ?_⟩
      rcases ih.2 rfl h0 with rfl | ⟨hn, _⟩
      · rcases hs with ⟨hm, _⟩ | ⟨e, he, hd⟩
        · exact absurd hm (by decide)
        · cases he with
          | head =>
            left
            obtain ⟨lb, lp, lm⟩ := l'
            obtain ⟨_, hb, _, hmk, _, σ, τ, _, hp, _, hτ⟩ := hd
            change lb = 0 at hb
            change lm = 0 at hmk
            change lp = [] ++ τ at hp
            change τ = [] at hτ
            subst hb hmk hτ
            rw [hp]
            rfl
          | tail _ he => cases he with
            | head =>
              obtain ⟨_, hb, _, _, _⟩ := hd
              exact Or.inr ⟨by decide, hb, fun h => absurd h (by decide)⟩
            | tail _ he => cases he
      · exact absurd rfl hn
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          refine ⟨fun _ => ⟨fun h => absurd h (by decide), fun _ hb0 => ?_⟩,
            fun h0 => absurd h0 (by decide)⟩
          have hl : l = l0 := ih.1 rfl |>.1 rfl
          subst hl
          rcases hs with ⟨hm, _⟩ | ⟨e, he, hd⟩
          · obtain ⟨lb, lp, lm⟩ := l
            change lb = 3 at hb0
            subst hb0
            exact absurd hm (by decide : ¬ (memB 3 setS.touched = false))
          · cases he with
            | head =>
              obtain ⟨_, hb', _, _, _, σ, τ, hσp, hτp, hσ, hτ⟩ := hd
              refine ⟨hb', fun τ' hp' => ?_⟩
              rw [hτp, hτ.1] at hp'
              have hs' : σ = 1 :: τ' := hp'
              change Excl.admits (.set [1]) σ = true at hσ
              rw [hs'] at hσ
              have hf : Excl.admits (.set [1]) (1 :: τ') = false := rfl
              rw [hf] at hσ
              exact Bool.noConfusion hσ
            | tail _ he => cases he with
              | head => exact absurd (hd.1.symm.trans hb0) (by decide)
              | tail _ he => cases he with
                | head => exact absurd (hd.1.symm.trans hb0) (by decide)
                | tail _ he => cases he
        | tail _ hE => cases hE
  | @pass M l0 n l n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        refine ⟨fun h1 => absurd h1 (by decide), fun _ h0 => ?_⟩
        rcases ih.2 rfl h0 with rfl | ⟨_, hb, _⟩
        · exact Or.inl rfl
        · obtain ⟨lb, lp, lm⟩ := l
          change lb = 1 at hb
          subst hb
          exact absurd hm (by decide : ¬ (memB 1 callSet.touched = false))
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @call M l0 n l n' c e1 e2 l1 l2 l3 _ hE he1 hd1 _ he2 hd2 ih ihc =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        refine ⟨fun h1 => absurd h1 (by decide), fun _ h0 => ?_⟩
        have hl := ih.2 rfl h0
        cases he1 with
        | head =>
          have hb1 : l1.base = 3 := hd1.2.1
          obtain ⟨hb2, hp2⟩ := (ihc.1 rfl).2 rfl hb1
          cases he2 with
          | head =>
            obtain ⟨_, hb3, _, _, _, σ, τ, hσp, hτp, _, hτ⟩ := hd2
            refine Or.inr ⟨by decide, hb3, fun _ τ' hp' => ?_⟩
            rw [hτp, hτ.1] at hp'
            exact hp2 τ' (by rw [hσp]; exact hp')
          | tail _ he2 => cases he2 with
            | head => exact absurd (hd2.1.symm.trans hb2) (by decide)
            | tail _ he2 => cases he2
        | tail _ he1 => cases he1 with
          | head =>
            have hb : l.base = 2 := hd1.1
            rcases hl with rfl | ⟨_, hb', _⟩
            · exact absurd hb (by decide)
            · exact absurd (hb.symm.trans hb') (by decide)
          | tail _ he1 => cases he1
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | clean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms flow_inv

/-- The location `(dto, [name], T)` is NOT reached at the sink node: `dto.name` was overwritten by
    the clean `c` in `setName`. -/
theorem name_not_reached : ¬ Flow prog 0 zeroLoc 2 ⟨1, [1], 1⟩ := by
  intro h
  rcases (flow_inv h).2 rfl rfl with h' | ⟨_, _, hp⟩
  · exact absurd h' (by decide)
  · exact hp rfl [] rfl

#print axioms name_not_reached

/-- A witness in `root` of program S is a flow in `root`. -/
theorem reach_root {M : MethodId} {n : Node} {l : Loc} (h : Reach prog [0] M n l) :
    M = 0 → Flow prog 0 zeroLoc n l := by
  cases h with
  | root hM hf =>
    intro h0
    subst h0
    exact hf
  | down _ hE _ _ _ =>
    intro h0
    cases hE with
    | tail _ hE => cases hE with
      | head => exact absurd h0 (by decide)
      | tail _ hE => cases hE with
        | tail _ hE => cases hE

/-- `sink(dto.name)` is NOT REAL: no location of the sink pattern `(dto, [name], $, T)` is
    reached at the sink node. -/
theorem name_not_real : ∀ l, sinkName.covers l → ¬ Reach prog [0] 0 2 l := by
  intro l hc hr
  obtain ⟨lb, lp, lm⟩ := l
  obtain ⟨hb, ⟨σ, hp, hσ⟩, hm⟩ := hc
  change lb = 1 at hb
  change lp = [1] ++ σ at hp
  change σ = [] at hσ
  change lm = 1 at hm
  subst hb hσ hm
  rw [hp] at hr
  exact name_not_reached (reach_root hr rfl)

#print axioms name_not_real

/-- The pair relation of the source on the email witness: `zero → dto.email`. -/
theorem den_srcE : den G.srcE.1 G.srcE.2 zeroLoc ⟨1, [2], 1⟩ :=
  ⟨rfl, rfl, rfl, rfl, trivial, [], [2], rfl, rfl, rfl, trivial⟩
/-- The pair relation of the binding `dto.* → this.*` on the email witness. -/
theorem den_this : den bThis.1 bThis.2 ⟨1, [2], 1⟩ ⟨3, [2], 1⟩ :=
  ⟨rfl, rfl, trivial, rfl, trivial, [2], [2], rfl, rfl, rfl, rfl, rfl⟩
/-- The pair relation of the keep edge `this.*/{name} → this.*` on `this.email`. -/
theorem den_keep : den keepS.1 keepS.2 ⟨3, [2], 1⟩ ⟨3, [2], 1⟩ :=
  ⟨rfl, rfl, trivial, rfl, trivial, [2], [2], rfl, rfl, rfl, rfl, rfl⟩
/-- The pair relation of the binding back `this.* → dto.*` on the email witness. -/
theorem den_back : den bBack.1 bBack.2 ⟨3, [2], 1⟩ ⟨1, [2], 1⟩ :=
  ⟨rfl, rfl, trivial, rfl, trivial, [2], [2], rfl, rfl, rfl, rfl, rfl⟩

/-- `sink(dto.email)` is REAL: the source taints `dto.email`, the keep edge of `this.name = n`
    keeps `this.email`, the binding back returns it to `dto.email`, and the sink pattern covers
    it. -/
theorem email_real : Reach prog [0] 0 2 ⟨1, [2], 1⟩ ∧ sinkEmail.covers ⟨1, [2], 1⟩ := by
  have f0 : Flow prog 0 zeroLoc 1 ⟨1, [2], 1⟩ :=
    Flow.step (Flow.start 0 zeroLoc) hE00
      (Or.inr ⟨G.srcE, List.Mem.tail _ (List.Mem.head _), den_srcE⟩)
  have fc : Flow prog 1 ⟨3, [2], 1⟩ 1 ⟨3, [2], 1⟩ :=
    Flow.step (Flow.start 1 _) hE10 (Or.inr ⟨keepS, List.Mem.head _, den_keep⟩)
  exact ⟨Reach.root (List.Mem.head _)
    (Flow.call f0 hE01 (List.Mem.head _) den_this fc (List.Mem.head _) den_back),
    ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩⟩

#print axioms email_real

end S

end ApSpec.AnyTaintCases
