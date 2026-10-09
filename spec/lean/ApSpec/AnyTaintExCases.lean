/-
  ApSpec.AnyTaintExCases — the WORKED PROGRAMS of the refined forward model where the
  `[any-taint]` conclusion carries an EXCLUSION `E` of first accessors (decision F69, DESIGN §6,
  amendment A2).

  The test data of the spec: concrete programs, derivations in the refined closures `D6X` (run 1)
  and `DRXs` (the restricted forward run) of `AnyTaintExDefs.lean` (by the closure constructors,
  each step checked by `decide`), complete closures (an invariant over every object of a run, as
  `AnyTaintCases.S.inv1` does), and `decide` vectors of the refined operations. For contrast, the
  base model `AnyTaint.D6T` (the demotion of decision 5) on the same program.

  Numbers. Marks: `zeroMark = 0`, `T = 1`. The field limit of every run is 3 (`cnt`: every
  accessor counts), except the run of `CUT` (limit 0). Each CFG edge holds one statement. The
  source of every program is `srcAny()` of `AnyTaintCases.G`: the taint edge
  `zero.$ (zeroMark) → b.[any] (T)` (`srcE`, `srcS`, `taint`; base `b = 1`). A sink `sink(x.p)`
  is the pattern `(x, p, $, T)`, a sink `sinkAny(x)` the pattern `(x, [], [any], T)`.

  The programs (each in its own namespace):
  * `S` (the setter): `root(){ dto = srcAny(); dto.setName(c); sink(dto.name); sink(dto.email); }`,
    `setName(n){ this.name = n; }`. The same program as `AnyTaintCases.S`.
  * `SD` (the deep setter): `root` calls `setNameDeep(c){ this.setName(c); }`.
  * `B` (the broad demand): `root1(){ d = srcAny(); d.setName(c); sink(d.name); }`,
    `root2(){ e = srcAny(); e.setName(c); sinkAny(e); }`; run 1 and run 3 with the broad demand
    `(D-c = (this, [], [any], T), D-p = (this, [], [any], T))` of `setName`.
  * `X` (a two-level write in one statement): `x = srcAny(); x.f.g = c; sink(x.f.g); sink(x.f.h);
    sink(x.k)`.
  * `R` (a read through an excluded accessor): `S` and then `y = dto.name; z = dto.email;
    sinkAny(y); sinkAny(z)`.
  * `CL` (the cleaners at `x.f`): `x = srcAny(); clean(x.f, reach); sink(x.f); sink(x.f.g);
    sink(x.k)` for the three reaches.
  * `CUT` (the field limit): the program `X` with the field limit 0.

  The theorems and the FINDINGS are listed at the end of the file (the section "Summary").

  All proofs are constructive (`propext`, `Quot.sound` only; see the `#print axioms` lines).
-/
import ApSpec.AnyTaintExDefs

namespace ApSpec.AnyTaintExCases
open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx

/-- The `*` tail with the empty exclusion. -/
def st : Kind := .star (.set [])
/-- Every accessor counts for the field limit. -/
def cnt : Acc → Bool := fun _ => true
/-- A demand (forward orientation). -/
abbrev Dem := MethodId → DemandEdge → Prop
/-- A record set of the refined restricted run: premise, must flag, premise exclusion, annotated
    conclusion. -/
abbrev XRecs := MethodId → PFact × Bool × Excl × XFact → Prop

/-- The element of an `Option` is in its list. -/
theorem mem_toList_of_eq_some {α : Type} {o : Option α} {a : α} (h : o = some a) :
    a ∈ o.toList := by
  subst h; exact List.Mem.head _

/-- The taint edge of `b = srcAny()` (base `b = 1`): `zero.$ (zeroMark) → b.[any] (T)`. -/
def srcE : MicroEdge := (zeroFact, ⟨1, [], .any, .conc 1⟩)
/-- `b = srcAny()`: the zero fact is kept, `b` is overwritten. -/
def srcS : Stmt := ⟨[0, 1], [(zeroFact, zeroFact), srcE]⟩
/-- The taint edges: the source edge only. -/
def taint : TaintEdges := fun e => decide (e = srcE)

/-- The zero fact, normal, with no exclusion. -/
def Zx : XFact := plain ⟨zeroFact, false⟩
/-- The source result `(b, [], [any-taint], {}, T)`: `.any`, normal, the empty exclusion. -/
def DTOx : XFact := ⟨⟨⟨1, [], .any, .conc 1⟩, false⟩, Excl.empty⟩
/-- The source result in the base model: `(b, [], [any-taint], T)` (`.any`, normal). -/
def DTO : AFact := ⟨⟨1, [], .any, .conc 1⟩, false⟩
/-- The same fact in the demand layer: `(b, [], [any], T)`. -/
def DTOd : AFact := ⟨DTO.fact, true⟩

/-! ## Program S: the setter

```
root():  dto = srcAny();   // 0 -> 1: the taint edge zero.$ (zeroMark) -> dto.[any] (T)
         dto.setName(c);   // 1 -> 2; c is clean (never tainted)
         sink(dto.name);   // the sink pattern (dto, [name], $, T) at node 2
         sink(dto.email);  // the sink pattern (dto, [email], $, T) at node 2
setName(n):  this.name = n;  // 0 -> 1: the keep edge this.*/{name} -> this.* (spec: this.* ->_{name}
                             //         this.*) and the gen edge n.* -> this.name.*
```
  Bases: zero = 0, dto = 1, c = 2, this = 3, n = 4. Accessors: name = 1, email = 2. Methods:
  root = 0 (nodes 0, 1, 2; exit 2), setName = 1 (nodes 0, 1; exit 1). The call binds
  `dto.* → this.*` and `c.* → n.*`, and back `this.* → dto.*` and `n.* → c.*`. The program is
  `AnyTaintCases.S` (the same terms).

  What it shows:
  * run 1 with the exclusion (`D6X`, `policy1`) derives the record of `setName`
    `(this, [], *, {}, *) → (this, [], */{name}, *)` (`run1_record`). Its application to the
    added fact `(this, [], [any-taint], {}, T)` is case `below r = []` with the exclusion `{name}`:
    the refined rule (A2: "an exclusion edge at `r = []` gives `E ∪ E'`, normal") gives
    `(this, [], [any-taint], {name}, T)` in the NORMAL layer, and the binding back gives
    `dto = (dto, [], [any-taint], {name}, T)`, NORMAL (`record_app`, `run1_dto_ann`);
  * `sink(dto.name)` is NOT reported: no vulnerability object at all, in no layer
    (`run1_name_not_reported`), because the sink pattern is in the excluded part
    (`run1_name_no_trigger`); this is correct: `dto.name` is not tainted (`name_not_real`);
  * `sink(dto.email)` is reported in the NORMAL layer and run 1 CONFIRMS it (`run1_email_normal`,
    `run1_email_confirmed`); it is real (`email_real`); the complete run 1 has no demand-layer
    report (`run1_no_demand`);
  * contrast, the base model `AnyTaint.D6T` (the demotion of decision 5): the same record
    application gives `(dto, [], [any], T)` in the DEMAND layer, so BOTH sinks are demand entries
    and nothing is confirmed (`inv1T`, `run1T_vulns`, `run1T_no_normal`, `run1T_not_confirmed`;
    the facts of `AnyTaintCases.S.run1_vulns`, `AnyTaintCases.S.run1_no_normal`, re-derived); the
    refined normal edge is that base demand edge with the exclusion (`refines_dto`). -/

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
  [(0, 0, .stmt srcS, 1), (0, 1, .call callSet, 2), (1, 0, .stmt setS, 1)]⟩
/-- The sink pattern of `sink(dto.name)`: `(dto, [name], $, T)`. -/
def sinkName : PFact := ⟨1, [1], .exact, .conc 1⟩
/-- The sink pattern of `sink(dto.email)`: `(dto, [email], $, T)`. -/
def sinkEmail : PFact := ⟨1, [2], .exact, .conc 1⟩
/-- Both sinks are at node 2 of `root`. -/
def sinks : List (MethodId × Node × PFact) := [(0, 2, sinkName), (0, 2, sinkEmail)]

/-- The CFG edge of `dto = srcAny()`. -/
theorem hE00 : (0, 0, Instr.stmt srcS, 1) ∈ prog.edges := List.Mem.head _
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

/-! ### The facts -/

/-- The added fact of `setName`: `(this, [], [any], T)` (on the normal link: `[any-taint]`). -/
def Athis : PFact := ⟨3, [], .any, .conc 1⟩
/-- The added fact with its layer and its (empty) exclusion, as the binding gives it. -/
def AthisX : XFact := ⟨⟨Athis, false⟩, Excl.empty⟩
/-- Run 1: the most abstract premise `(this, [], *, {}, *)` of `setName` (`policy1`). -/
def Jthis : PFact := ⟨3, [], st, .star⟩
/-- The start fact of `Jthis`, normal. -/
def JthisX : XFact := plain ⟨Jthis, false⟩
/-- THE RECORD CONCLUSION of `setName`: `(this, [], */{name}, *)`, normal (the keep edge). -/
def KEEP : AFact := ⟨⟨3, [], .star (.set [1]), .star⟩, false⟩
def KEEPx : XFact := plain KEEP
/-- The record application on the `[any-taint]` added fact: `(this, [], [any-taint], {name}, T)`,
    NORMAL. -/
def THISann : XFact := ⟨⟨Athis, false⟩, .set [1]⟩
/-- THE SINK FACT: `(dto, [], [any-taint], {name}, T)`, NORMAL: every location below `dto` but
    the ones below `dto.name` carries `T`. -/
def DTOann : XFact := ⟨⟨⟨1, [], .any, .conc 1⟩, false⟩, .set [1]⟩

/-! ### Run 1 with the exclusion (`D6X`), completely -/

/-- Run 1 of program S with the exclusion: `policy1`, the field limit 3. -/
abbrev R1 : XObj6 → Prop := D6X prog taint cnt 3 policy1 sinks [0]

/-- The initial facts of run 1. -/
def inits1 : List (MethodId × PFact) := [(0, zeroFact), (1, Jthis)]
/-- The edges of run 1. -/
def edges1 : List (MethodId × PFact × Node × XFact) :=
  [(0, zeroFact, 0, Zx), (0, zeroFact, 1, Zx), (0, zeroFact, 1, DTOx), (0, zeroFact, 2, Zx),
   (0, zeroFact, 2, DTOann), (1, Jthis, 0, JthisX), (1, Jthis, 1, KEEPx)]
/-- The added facts of run 1. -/
def addeds1 : List (MethodId × PFact) := [(1, Athis)]
/-- The vulnerabilities of run 1: only the email sink, in the normal layer. -/
def vulns1 : List (MethodId × Node × PFact × Bool) := [(0, 2, sinkEmail, false)]

/-- Every object of run 1 is in the lists; no request. -/
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
/-- THE COMPLETE RUN 1 OF PROGRAM S WITH THE EXCLUSION: the only exit edge of `setName` is the
    record `(this, [], *, *) → (this, [], */{name}, *)`; the sink edges are the zero edge and the
    NORMAL `zero → (dto, [], [any-taint], {name}, T)`; no request; the only vulnerability is the
    email sink, in the normal layer. -/
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
            ∀ f' ∈ (transferX taint cnt 3 setS x.2.2.2).facts, Inv1 (.edge 1 x.2.1 1 f'))
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
            ∀ t ∈ (transferX taint cnt 3 setS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.af.fact.base callSet.touched = false → Inv1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callSet.toCallee,
          ∀ a ∈ (bindX x.2.2.2 e).facts, Inv1 (.added callSet.callee a.af.fact))
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
          ∀ e1 ∈ callSet.toCallee, ∀ a ∈ (bindX x.2.2.2 e1).facts,
          ∀ y ∈ inits1, y.1 = 1 → applicable y.2 a.af.fact = true →
          ∀ z ∈ edges1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummaryX a y.2 Excl.empty z.2.2.2).facts,
          ∀ e2 ∈ callSet.fromCallee, ∀ r' ∈ (bindX r e2).facts,
            Inv1 (.edge 0 x.2.1 2 (limitFX cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 → ∀ s ∈ [sinkName, sinkEmail],
        checkX x.2.1 x.2.2.2 s = .none ∨ checkX x.2.1 x.2.2.2 s = .triggered := by decide
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
        checkX x.2.1 x.2.2.2 s = .triggered → (0, 2, s, x.2.2.2.af.demand) ∈ vulns1 := by decide
    cases hs with
    | head => exact hv (0, i, 2, f) ih rfl rfl sinkName (List.Mem.head _) hc
    | tail _ hs => cases hs with
      | head => exact hv (0, i, 2, f) ih rfl rfl sinkEmail (List.Mem.tail _ (List.Mem.head _)) hc
      | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1

/-! ### Run 1 with the exclusion: the record and its application -/

-- the source result is `[any-taint]` with the empty exclusion, normal
example : (transferX taint cnt 3 srcS Zx).facts = [Zx, DTOx] := by decide
-- the binding into `setName` gives the added fact `(this, [], [any], T)`, normal on the link
example : (bindX DTOx bThis).facts = [AthisX] := by decide
example : policy1 1 Athis = Jthis := by decide
-- the keep edge on the most abstract premise: the record conclusion `(this, [], */{name}, *)`
example : (transferX taint cnt 3 setS JthisX).facts = [KEEPx] := by decide

/-- THE RECORD APPLICATION KEEPS THE LAYER AND CARRIES THE EXCLUSION (DESIGN A2, "an exclusion
    edge at `r = []`, the keep edge of a strong write, a `*/E` summary or record, gives `E ∪ E'`,
    normal; no demotion"): the added fact `(this, [], [any-taint], {}, T)` meets the record
    `(this, [], *, {}, *) → (this, [], */{name}, *)` at `r = []` (`annX`: a `keep` row with the
    exclusion `{name}`); the result is `(this, [], [any-taint], {name}, T)` in the NORMAL layer
    (the base `applySummary` gives it in the DEMAND layer); the binding back `this.* → dto.*` (a
    `*` target at `r = []`, a `keep` row) gives `(dto, [], [any-taint], {name}, T)`, NORMAL; the
    binding back of `n` gives nothing; the field limit keeps it. -/
theorem record_app :
    applicable Jthis Athis = true ∧
    annX AthisX Jthis Excl.empty KEEP.fact Excl.empty = some (true, .set [1]) ∧
    (applySummaryX AthisX Jthis Excl.empty KEEPx).facts = [THISann] ∧
    (applySummary AthisX.af Jthis KEEP).facts = [⟨Athis, true⟩] ∧
    (bindX THISann bBack).facts = [DTOann] ∧
    (bindX THISann bNBack).facts = [] ∧
    limitFX cnt 3 DTOann = DTOann := by decide

#print axioms record_app

/-- The keep edge `this.* →_{name} this.*` of the brief has two model forms: the exclusion on the
    premise (`this.*/{name} → this.*`, `keepS`, as `AnyTaintCases.S`) or on the target
    (`this.* → this.*/{name}`, as `AnyTaintEx.Vec.keepEdge`). On the `[any-taint]` fact both give
    the same NORMAL `(this, [], [any-taint], {name}, T)` (`annX` adds the premise exclusion and the
    target exclusion alike). -/
theorem keep_forms :
    bindX AthisX keepS = ⟨[THISann], []⟩ ∧
    bindX AthisX (⟨3, [], st, .star⟩, ⟨3, [], .star (.set [1]), .star⟩) = ⟨[THISann], []⟩ := by
  decide

#print axioms keep_forms

/-- Run 1: the source edge `zero → (dto, [], [any-taint], {}, T)`, normal. -/
theorem r1_e01 : R1 (.edge 0 zeroFact 1 DTOx) :=
  D6X.step (D6X.start (D6X.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1: the added fact `(this, [], [any], T)` of `setName`. -/
theorem r1_ad : R1 (.added 1 Athis) :=
  D6X.added (c := callSet) (e := bThis) (a := AthisX) r1_e01 hE01 (List.Mem.head _) (by decide)

/-- Run 1: `policy1` serves the added fact with `(this, [], *, {}, *)`. -/
theorem r1_i1 : R1 (.init 1 Jthis) := by
  have h : R1 (.init 1 (policy1 1 Athis)) := D6X.initA r1_ad
  have hp : policy1 1 Athis = Jthis := by decide
  rw [hp] at h
  exact h

/-- THE RUN-1 RECORD OF `setName`: `(this, [], *, {}, *) → (this, [], */{name}, *)` (the keep edge
    of `this.name = n`), in the NORMAL layer and complete (a persisted record, ap.md §8.7 R1). -/
theorem run1_record : R1 (.edge 1 Jthis 1 KEEPx) ∧ KEEPx.af.complete = true :=
  ⟨D6X.step (D6X.start r1_i1) hE10 (by decide), rfl⟩

#print axioms run1_record

/-- THE SINK EDGE IS NORMAL WITH THE EXCLUSION `{name}`: run 1 derives
    `zero → (dto, [], [any-taint], {name}, T)` at the sink node, in the NORMAL layer (the record
    application, `record_app`). -/
theorem run1_dto_ann :
    R1 (.edge 0 zeroFact 2 DTOann) ∧ DTOann.af.demand = false ∧ DTOann.ex = .set [1] :=
  ⟨D6X.ret (c := callSet) (e1 := bThis) (a := AthisX) (j := Jthis) (g := KEEPx) (r := THISann)
    (e2 := bBack) (r' := DTOann) r1_e01 hE01 (List.Mem.head _) (by decide) r1_i1 (by decide)
    run1_record.1 (by decide) (List.Mem.head _) (by decide), rfl, rfl⟩

#print axioms run1_dto_ann

/-- No sink edge of run 1 triggers `sink(dto.name)`: the sink pattern `(dto, [name], $, T)` lies in
    the EXCLUDED part of `(dto, [], [any-taint], {name}, T)` (`checkX` reads the exclusion; the base
    check on the same fact triggers). -/
theorem run1_name_no_trigger :
    (∀ i f, R1 (.edge 0 i 2 f) → checkX i f sinkName = .none) ∧
    check zeroFact DTOann.af sinkName = .triggered := by
  refine ⟨fun i f h => ?_, by decide⟩
  exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 → checkX x.2.1 x.2.2.2 sinkName = .none)
    (0, i, 2, f) (inv1 h) rfl rfl

#print axioms run1_name_no_trigger

/-- `sink(dto.name)` IS NOT REPORTED in run 1: there is no vulnerability object for it, in no
    layer (the complete run `inv1`). -/
theorem run1_name_not_reported (d : Bool) : ¬ R1 (.vuln 0 2 sinkName d) := by
  intro h
  have h' := inv1 h
  cases d <;> exact absurd h' (by decide)

#print axioms run1_name_not_reported

/-- `sink(dto.email)` is reported in run 1 in the NORMAL layer. -/
theorem run1_email_normal : R1 (.vuln 0 2 sinkEmail false) :=
  D6X.vuln run1_dto_ann.1 hsE (by decide)

#print axioms run1_email_normal

/-- RUN 1 CONFIRMS `sink(dto.email)` (`AnyTaintEx.Confirmed6X`): the normal sink edge
    `zero → (dto, [], [any-taint], {name}, T)` under the supported zero premise of the root, with
    a triggered `checkX` (`email ∉ {name}`). -/
theorem run1_email_confirmed : Confirmed6X prog taint cnt 3 policy1 sinks [0] 0 2 sinkEmail :=
  ⟨zeroFact, DTOann, run1_dto_ann.1, Sup6X.root (List.Mem.head _), rfl, hsE, by decide⟩

#print axioms run1_email_confirmed

/-- The complete run 1 has no demand-layer report. -/
theorem run1_no_demand (s : PFact) : ¬ R1 (.vuln 0 2 s true) := by
  intro h
  have h' : (0, 2, s, true) ∈ vulns1 := inv1 h
  exact absurd h' (by
    intro hm
    cases hm with
    | tail _ hm => cases hm)

#print axioms run1_no_demand

/-! ### Contrast: the base model `AnyTaint.D6T` (the demotion of decision 5), completely

  The facts of `AnyTaintCases.S` (`run1_vulns`, `run1_no_normal`), re-derived here on the same
  program (this file does not import `AnyTaintCases`). -/

/-- Run 1 of program S in the base model (W6T, the demotion at an exclusion). -/
abbrev R1T : Obj → Prop := D6T prog taint cnt 3 policy1 sinks [0]

def Z : AFact := ⟨zeroFact, false⟩
def JthisF : AFact := ⟨Jthis, false⟩
/-- The base record application: `(this, [], [any], T)`, DEMAND. -/
def THISd : AFact := ⟨Athis, true⟩

/-- The edges of the base run 1. -/
def edges1T : List (MethodId × PFact × Node × AFact) :=
  [(0, zeroFact, 0, Z), (0, zeroFact, 1, Z), (0, zeroFact, 1, DTO), (0, zeroFact, 2, Z),
   (0, zeroFact, 2, DTOd), (1, Jthis, 0, JthisF), (1, Jthis, 1, KEEP)]

/-- Every object of the base run 1 is in the lists; no request; every vulnerability is in the
    demand layer. -/
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
/-- THE COMPLETE BASE RUN 1 OF PROGRAM S (`AnyTaint.D6T`): the only sink edge after the call is
    the DEMAND `zero → (dto, [], [any], T)`; every vulnerability is in the demand layer
    (`AnyTaintCases.S.inv1`, re-derived). -/
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
            ∀ f' ∈ (transferT taint cnt 3 setS x.2.2.2).facts, Inv1T (.edge 1 x.2.1 1 f'))
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
            ∀ t ∈ (transferT taint cnt 3 setS x.2.2.2).reqs, False) (1, i, 0, f) ih rfl rfl t ht
        | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.fact.base callSet.touched = false → Inv1T (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callSet.toCallee,
          ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts, Inv1T (.added callSet.callee a.fact))
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
          ∀ e1 ∈ callSet.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e1.1 e1.2).facts,
          ∀ y ∈ inits1, y.1 = 1 → applicable y.2 a.fact = true →
          ∀ z ∈ edges1T, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummary a y.2 z.2.2.2).facts,
          ∀ e2 ∈ callSet.fromCallee, ∀ r' ∈ (applyEdge r e2.1 e2.2).facts,
            Inv1T (.edge 0 x.2.1 2 (limitF cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 2 → ∀ s ∈ [sinkName, sinkEmail],
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
    have hv : ∀ x ∈ edges1T, x.1 = 0 → x.2.2.1 = 2 → ∀ s ∈ [sinkName, sinkEmail],
        check x.2.1 x.2.2.2 s = .triggered → x.2.2.2.demand = true := by decide
    cases hs with
    | head => exact hv (0, i, 2, f) ih rfl rfl sinkName (List.Mem.head _) hc
    | tail _ hs => cases hs with
      | head => exact hv (0, i, 2, f) ih rfl rfl sinkEmail (List.Mem.tail _ (List.Mem.head _)) hc
      | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1T

/-- The base run 1: the source edge, normal. -/
theorem r1T_e01 : R1T (.edge 0 zeroFact 1 DTO) :=
  D6T.step (D6T.start (D6T.root (List.Mem.head _))) hE00 (by decide)

/-- The base run 1: the premise `(this, [], *, {}, *)` of `setName`. -/
theorem r1T_i1 : R1T (.init 1 Jthis) := by
  have h : R1T (.init 1 (policy1 1 Athis)) := D6T.initA (α := policy1)
    (D6T.added (c := callSet) (e := bThis) (a := ⟨Athis, false⟩) (P := prog) (taint := taint)
      (counted := cnt) (L := 3) (sinks := sinks) (roots := [0])
    r1T_e01 hE01 (List.Mem.head _) (by decide))
  have hp : policy1 1 Athis = Jthis := by decide
  rw [hp] at h
  exact h

/-- The base run 1: the record application gives `zero → (dto, [], [any], T)`, DEMAND. -/
theorem r1T_e02 : R1T (.edge 0 zeroFact 2 DTOd) :=
  D6T.ret (c := callSet) (e1 := bThis) (a := ⟨Athis, false⟩) (j := Jthis) (g := KEEP)
    (r := THISd) (e2 := bBack) (r' := DTOd) r1T_e01 hE01 (List.Mem.head _) (by decide) r1T_i1
    (by decide) (D6T.step (D6T.start r1T_i1) hE10 (by decide)) (by decide) (List.Mem.head _)
    (by decide)

/-- CONTRAST (the base model): run 1 of `AnyTaint.D6T` reports BOTH sinks of program S, in the
    DEMAND layer (the demotion of decision 5 puts the record application in the demand layer). -/
theorem run1T_vulns : R1T (.vuln 0 2 sinkName true) ∧ R1T (.vuln 0 2 sinkEmail true) :=
  ⟨D6T.vuln r1T_e02 hsN (by decide), D6T.vuln r1T_e02 hsE (by decide)⟩

#print axioms run1T_vulns

/-- CONTRAST (the base model): run 1 of `AnyTaint.D6T` has NO normal report in program S. -/
theorem run1T_no_normal (s : PFact) : ¬ R1T (.vuln 0 2 s false) :=
  fun h => Bool.noConfusion (inv1T h)

#print axioms run1T_no_normal

/-- CONTRAST (the base model): run 1 of `AnyTaint.D6T` does not confirm `sink(dto.email)`. -/
theorem run1T_not_confirmed : ¬ ConfirmedT6 prog taint cnt 3 policy1 sinks [0] 0 2 sinkEmail := by
  rintro ⟨i, f, hf, _, hd, hs, hc⟩
  have hv := D6T.vuln hf hs hc
  rw [hd] at hv
  exact run1T_no_normal _ hv

#print axioms run1T_not_confirmed

/-- THE REFINED EDGE IS THE BASE DEMAND EDGE WITH THE EXCLUSION (`AnyTaintEx.Refines6`): the
    normal `zero → (dto, [], [any-taint], {name}, T)` of `D6X` and the demand
    `zero → (dto, [], [any], T)` of `D6T` have the same fact; the refined edge is normal only
    because the exclusion replaces the demotion. -/
theorem refines_dto :
    R1 (.edge 0 zeroFact 2 DTOann) ∧ R1T (.edge 0 zeroFact 2 DTOd) ∧
    Refines6 (.edge 0 zeroFact 2 DTOann) (.edge 0 zeroFact 2 DTOd) :=
  ⟨run1_dto_ann.1, r1T_e02, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

#print axioms refines_dto

/-! ### `sink(dto.name)` is not real; `sink(dto.email)` is real

  The flow proofs of `AnyTaintCases.S` (`name_not_real`, `email_real`), re-derived on the same
  program. -/

/-- The reaching locations of `setName` from an entry location `l0`: at the entry, `l0` itself;
    at the exit, a location that came from `this` is a location of `this` whose path does not
    start with `name`. -/
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

/-- `sink(dto.name)` IS NOT REAL: no location of the sink pattern `(dto, [name], $, T)` is reached
    at the sink node (`dto.name` was overwritten by the clean `c`). So the refined run 1, which
    does not report it (`run1_name_not_reported`), loses no real vulnerability here. -/
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
  rcases (flow_inv (reach_root hr rfl)).2 rfl rfl with h' | ⟨_, _, hp'⟩
  · exact absurd h' (by decide)
  · exact hp' rfl [] rfl

#print axioms name_not_real

/-- `sink(dto.email)` IS REAL: the source taints `dto.email`, the keep edge of `this.name = n`
    keeps `this.email`, the binding back returns it to `dto.email`, and the sink pattern covers
    it. -/
theorem email_real : Reach prog [0] 0 2 ⟨1, [2], 1⟩ ∧ sinkEmail.covers ⟨1, [2], 1⟩ := by
  have d0 : den srcE.1 srcE.2 zeroLoc ⟨1, [2], 1⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [2], rfl, rfl, rfl, trivial⟩
  have d1 : den bThis.1 bThis.2 ⟨1, [2], 1⟩ ⟨3, [2], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [2], [2], rfl, rfl, rfl, rfl, rfl⟩
  have d2 : den keepS.1 keepS.2 ⟨3, [2], 1⟩ ⟨3, [2], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [2], [2], rfl, rfl, rfl, rfl, rfl⟩
  have d3 : den bBack.1 bBack.2 ⟨3, [2], 1⟩ ⟨1, [2], 1⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [2], [2], rfl, rfl, rfl, rfl, rfl⟩
  have f0 : Flow prog 0 zeroLoc 1 ⟨1, [2], 1⟩ :=
    Flow.step (Flow.start 0 zeroLoc) hE00 (Or.inr ⟨srcE, List.Mem.tail _ (List.Mem.head _), d0⟩)
  have fc : Flow prog 1 ⟨3, [2], 1⟩ 1 ⟨3, [2], 1⟩ :=
    Flow.step (Flow.start 1 _) hE10 (Or.inr ⟨keepS, List.Mem.head _, d2⟩)
  exact ⟨Reach.root (List.Mem.head _)
    (Flow.call f0 hE01 (List.Mem.head _) d1 fc (List.Mem.head _) d3),
    ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩⟩

#print axioms email_real

end S

/-! ## Program SD: the deep setter

```
root():            dto = srcAny();       // 0 -> 1
                   dto.setNameDeep(c);   // 1 -> 2
                   sink(dto.name);       // (dto, [name], $, T) at node 2
                   sink(dto.email);      // (dto, [email], $, T) at node 2
setNameDeep(c'):   this'.setName(c');    // 0 -> 1 (this' = the receiver of setNameDeep)
setName(n):        this.name = n;        // 0 -> 1 (`S.setS`)
```
  Bases: zero = 0, dto = 1, c = 2, this = 3, n = 4, this' = 5, c' = 6. Methods: root = 0
  (nodes 0, 1, 2; exit 2), setNameDeep = 1 (nodes 0, 1; exit 1), setName = 2 (nodes 0, 1;
  exit 1). The calls bind `dto.* → this'.*`, `c.* → c'.*` (and back), and `this'.* → this.*`,
  `c'.* → n.*` (and back).

  What it shows: run 1 (`D6X`) gives THE SAME RESULT as for `S` (`same_result`). The record of
  `setName` (`S.run1_record` in method 2) applied to the `*` added fact `(this, [], *, {}, *)` of
  `setNameDeep` is case `below r = []` on a `*` fact (no `[any-taint]`, no demotion in either
  model): it gives the record `(this', [], *, {}, *) → (this', [], */{name}, *)` of
  `setNameDeep` (`run1_deep_record`). Its application in `root` to the `[any-taint]` added fact is
  the record application of `S`: `(dto, [], [any-taint], {name}, T)`, NORMAL (`run1_dto_ann`). So
  `sink(dto.name)` is not reported (`run1_name_not_reported`) and `sink(dto.email)` is confirmed
  (`run1_email_confirmed`). -/

namespace SD

/-! ### The program -/

/-- The binding of the receiver of `dto.setNameDeep(c)`: `dto.* → this'.*`. -/
def bD : MicroEdge := (⟨1, [], st, .star⟩, ⟨5, [], st, .star⟩)
/-- The binding of the argument: `c.* → c'.*`. -/
def bDc : MicroEdge := (⟨2, [], st, .star⟩, ⟨6, [], st, .star⟩)
/-- The binding back of the receiver: `this'.* → dto.*`. -/
def bDBack : MicroEdge := (⟨5, [], st, .star⟩, ⟨1, [], st, .star⟩)
/-- The binding back of the argument: `c'.* → c.*`. -/
def bDcBack : MicroEdge := (⟨6, [], st, .star⟩, ⟨2, [], st, .star⟩)
/-- `dto.setNameDeep(c)`. -/
def callDeep : Call := ⟨1, [1, 2], [bD, bDc], [bDBack, bDcBack]⟩
/-- The binding of the receiver of `this'.setName(c')`: `this'.* → this.*`. -/
def bS : MicroEdge := (⟨5, [], st, .star⟩, ⟨3, [], st, .star⟩)
/-- The binding of the argument: `c'.* → n.*`. -/
def bSn : MicroEdge := (⟨6, [], st, .star⟩, ⟨4, [], st, .star⟩)
/-- The binding back of the receiver: `this.* → this'.*`. -/
def bSBack : MicroEdge := (⟨3, [], st, .star⟩, ⟨5, [], st, .star⟩)
/-- The binding back of the argument: `n.* → c'.*`. -/
def bSnBack : MicroEdge := (⟨4, [], st, .star⟩, ⟨6, [], st, .star⟩)
/-- `this'.setName(c')`. -/
def callSet : Call := ⟨2, [5, 6], [bS, bSn], [bSBack, bSnBack]⟩
/-- Program SD: `root` (0), `setNameDeep` (1), `setName` (2). -/
def prog : Program := ⟨fun _ => 0, fun m => if m = 0 then 2 else 1,
  [(0, 0, .stmt srcS, 1), (0, 1, .call callDeep, 2), (1, 0, .call callSet, 1),
   (2, 0, .stmt S.setS, 1)]⟩

/-- The CFG edge of method 0 at node 0. -/
theorem hE00 : (0, 0, Instr.stmt srcS, 1) ∈ prog.edges := List.Mem.head _
/-- The CFG edge of method 0 at node 1. -/
theorem hE01 : (0, 1, Instr.call callDeep, 2) ∈ prog.edges := List.Mem.tail _ (List.Mem.head _)
/-- The CFG edge of method 1 at node 0. -/
theorem hE10 : (1, 0, Instr.call callSet, 1) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
/-- The CFG edge of method 2 at node 0. -/
theorem hE20 : (2, 0, Instr.stmt S.setS, 1) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- Program SD has no cleaner. -/
theorem no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h

/-- Program SD has no type filter. -/
theorem no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h

/-! ### The facts -/

/-- The added fact of `setNameDeep`: `(this', [], [any], T)` (on the normal link:
    `[any-taint]`). -/
def A5 : PFact := ⟨5, [], .any, .conc 1⟩
def A5X : XFact := ⟨⟨A5, false⟩, Excl.empty⟩
/-- Run 1: the premise `(this', [], *, {}, *)` of `setNameDeep` (`policy1`). -/
def J5 : PFact := ⟨5, [], st, .star⟩
def J5X : XFact := plain ⟨J5, false⟩
/-- THE RECORD CONCLUSION of `setNameDeep`: `(this', [], */{name}, *)`, normal. -/
def KEEP5x : XFact := plain ⟨⟨5, [], .star (.set [1]), .star⟩, false⟩
/-- The record application on the `[any-taint]` added fact: `(this', [], [any-taint], {name}, T)`,
    NORMAL. -/
def SELFann : XFact := ⟨⟨A5, false⟩, .set [1]⟩

/-! ### Run 1 with the exclusion (`D6X`), completely -/

abbrev R1 : XObj6 → Prop := D6X prog taint cnt 3 policy1 S.sinks [0]

def inits1 : List (MethodId × PFact) := [(0, zeroFact), (1, J5), (2, S.Jthis)]
def edges1 : List (MethodId × PFact × Node × XFact) :=
  [(0, zeroFact, 0, Zx), (0, zeroFact, 1, Zx), (0, zeroFact, 1, DTOx), (0, zeroFact, 2, Zx),
   (0, zeroFact, 2, S.DTOann), (1, J5, 0, J5X), (1, J5, 1, KEEP5x), (2, S.Jthis, 0, S.JthisX),
   (2, S.Jthis, 1, S.KEEPx)]
def addeds1 : List (MethodId × PFact) := [(1, A5), (2, S.Jthis)]

/-- Every object of run 1 is in the lists; no request; the vulnerabilities are those of `S`. -/
def Inv1 : XObj6 → Prop
  | .init M i => (M, i) ∈ inits1
  | .edge M i n f => (M, i, n, f) ∈ edges1
  | .added M a => (M, a) ∈ addeds1
  | .req _ _ _ => False
  | .vuln M n s d => (M, n, s, d) ∈ S.vulns1

instance : DecidablePred Inv1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ inits1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s d => inferInstanceAs (Decidable ((M, n, s, d) ∈ S.vulns1))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM SD WITH THE EXCLUSION: the exit edges are the record of `setName`
    and the record `(this', [], *, *) → (this', [], */{name}, *)` of `setNameDeep`; the sink edges
    are those of `S`; no request; the only vulnerability is the email sink, normal. -/
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
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges1, x.1 = 2 → x.2.2.1 = 0 →
              ∀ f' ∈ (transferX taint cnt 3 S.setS x.2.2.2).facts, Inv1 (.edge 2 x.2.1 1 f'))
              (2, i, 0, f) ih rfl rfl f' hf
          | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ t ∈ (transferX taint cnt 3 srcS x.2.2.2).reqs, False) (0, i, 0, f) ih rfl rfl t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges1, x.1 = 2 → x.2.2.1 = 0 →
              ∀ t ∈ (transferX taint cnt 3 S.setS x.2.2.2).reqs, False) (2, i, 0, f) ih rfl rfl t ht
          | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.af.fact.base callDeep.touched = false → Inv1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            memB x.2.2.2.af.fact.base callSet.touched = false → Inv1 (.edge 1 x.2.1 1 x.2.2.2))
            (1, i, 0, f) ih rfl rfl hm
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callDeep.toCallee,
          ∀ a ∈ (bindX x.2.2.2 e).facts, Inv1 (.added callDeep.callee a.af.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 → ∀ e ∈ callSet.toCallee,
            ∀ a ∈ (bindX x.2.2.2 e).facts, Inv1 (.added callSet.callee a.af.fact))
            (1, i, 0, f) ih rfl rfl e he a ha
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addeds1, Inv1 (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callDeep.toCallee, ∀ a ∈ (bindX x.2.2.2 e1).facts,
          ∀ y ∈ inits1, y.1 = 1 → applicable y.2 a.af.fact = true →
          ∀ z ∈ edges1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummaryX a y.2 Excl.empty z.2.2.2).facts,
          ∀ e2 ∈ callDeep.fromCallee, ∀ r' ∈ (bindX r e2).facts,
            Inv1 (.edge 0 x.2.1 2 (limitFX cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ e1 ∈ callSet.toCallee, ∀ a ∈ (bindX x.2.2.2 e1).facts,
            ∀ y ∈ inits1, y.1 = 2 → applicable y.2 a.af.fact = true →
            ∀ z ∈ edges1, z.1 = 2 → z.2.1 = y.2 → z.2.2.1 = 1 →
            ∀ r ∈ (applySummaryX a y.2 Excl.empty z.2.2.2).facts,
            ∀ e2 ∈ callSet.fromCallee, ∀ r' ∈ (bindX r e2).facts,
              Inv1 (.edge 1 x.2.1 1 (limitFX cnt 3 r')))
            (1, i, 0, f) ihf rfl rfl e1 he1 a ha (2, j) ihj rfl hap (2, j, 1, g) ihg rfl rfl rfl
            r hr e2 he2 r' hr'
        | tail _ hE => cases hE with
          | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 → ∀ s ∈ [S.sinkName, S.sinkEmail],
        checkX x.2.1 x.2.2.2 s = .none ∨ checkX x.2.1 x.2.2.2 s = .triggered := by decide
    cases hs with
    | head =>
      rcases hnr (0, i, 2, f) ih rfl rfl S.sinkName (List.Mem.head _) with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs with
      | head =>
        rcases hnr (0, i, 2, f) ih rfl rfl S.sinkEmail (List.Mem.tail _ (List.Mem.head _))
          with h | h
        · rw [h] at hc; exact Check.noConfusion hc
        · rw [h] at hc; exact Check.noConfusion hc
      | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    have hv : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 → ∀ s ∈ [S.sinkName, S.sinkEmail],
        checkX x.2.1 x.2.2.2 s = .triggered → (0, 2, s, x.2.2.2.af.demand) ∈ S.vulns1 := by
      decide
    cases hs with
    | head => exact hv (0, i, 2, f) ih rfl rfl S.sinkName (List.Mem.head _) hc
    | tail _ hs => cases hs with
      | head =>
        exact hv (0, i, 2, f) ih rfl rfl S.sinkEmail (List.Mem.tail _ (List.Mem.head _)) hc
      | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1

/-! ### Run 1: the derivations -/

/-- Run 1: the source edge `zero → (b, [], [any-taint], {}, T)`, normal. -/
theorem r1_e01 : R1 (.edge 0 zeroFact 1 DTOx) :=
  D6X.step (D6X.start (D6X.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1: the zero edge passes the call to the sink node. -/
theorem r1_z2 : R1 (.edge 0 zeroFact 2 Zx) :=
  D6X.pass (D6X.step (D6X.start (D6X.root (List.Mem.head _))) hE00 (by decide)) hE01 (by decide)

/-- Run 1: `policy1` serves the added fact `(this', [], [any], T)` of `setNameDeep` with
    `(this', [], *, {}, *)`. -/
theorem r1_i1 : R1 (.init 1 J5) := by
  have h : R1 (.init 1 (policy1 1 A5)) :=
    D6X.initA (D6X.added (c := callDeep) (e := bD) (a := A5X) r1_e01 hE01 (List.Mem.head _)
      (by decide))
  have hp : policy1 1 A5 = J5 := by decide
  rw [hp] at h
  exact h

/-- Run 1: the added fact of `setName` is the `*` start fact `(this, [], *, {}, *)` of
    `setNameDeep`, bound by `this'.* → this.*`; `policy1` serves it with itself. -/
theorem r1_i2 : R1 (.init 2 S.Jthis) := by
  have h : R1 (.init 2 (policy1 2 S.Jthis)) :=
    D6X.initA (D6X.added (c := callSet) (e := bS) (a := S.JthisX) (D6X.start r1_i1) hE10
      (List.Mem.head _) (by decide))
  have hp : policy1 2 S.Jthis = S.Jthis := by decide
  rw [hp] at h
  exact h

/-- Run 1: the record of `setName` (method 2), as in `S`. -/
theorem r1_rec2 : R1 (.edge 2 S.Jthis 1 S.KEEPx) := D6X.step (D6X.start r1_i2) hE20 (by decide)

/-- THE RUN-1 RECORD OF `setNameDeep`: `(this', [], *, {}, *) → (this', [], */{name}, *)`, normal
    and complete. The record of `setName` applied to the `*` added fact `(this, [], *, {}, *)` is
    case `below r = []` on a `*` fact: the exclusion `{name}` goes into the `*` tail (no
    `[any-taint]`, no `keep` row), and the binding back gives the record of `setNameDeep`. -/
theorem run1_deep_record : R1 (.edge 1 J5 1 KEEP5x) ∧ KEEP5x.af.complete = true :=
  ⟨D6X.ret (c := callSet) (e1 := bS) (a := S.JthisX) (j := S.Jthis) (g := S.KEEPx) (r := S.KEEPx)
    (e2 := bSBack) (r' := KEEP5x) (D6X.start r1_i1) hE10 (List.Mem.head _) (by decide) r1_i2
    (by decide) r1_rec2 (by decide) (List.Mem.head _) (by decide), rfl⟩

#print axioms run1_deep_record

/-- THE SINK EDGE IS THE ONE OF `S`: the deep record applied to the `[any-taint]` added fact
    `(this', [], [any-taint], {}, T)` (a `keep` row with `{name}`) and bound back gives
    `zero → (dto, [], [any-taint], {name}, T)`, NORMAL. -/
theorem run1_dto_ann : R1 (.edge 0 zeroFact 2 S.DTOann) :=
  D6X.ret (c := callDeep) (e1 := bD) (a := A5X) (j := J5) (g := KEEP5x) (r := SELFann)
    (e2 := bDBack) (r' := S.DTOann) r1_e01 hE01 (List.Mem.head _) (by decide) r1_i1 (by decide)
    run1_deep_record.1 (by decide) (List.Mem.head _) (by decide)

#print axioms run1_dto_ann

/-- `sink(dto.name)` IS NOT REPORTED in run 1 of SD (no vulnerability object, in no layer). -/
theorem run1_name_not_reported (d : Bool) : ¬ R1 (.vuln 0 2 S.sinkName d) := by
  intro h
  have h' := inv1 h
  cases d <;> exact absurd h' (by decide)

#print axioms run1_name_not_reported

/-- RUN 1 CONFIRMS `sink(dto.email)` in SD (`Confirmed6X`). -/
theorem run1_email_confirmed :
    Confirmed6X prog taint cnt 3 policy1 S.sinks [0] 0 2 S.sinkEmail :=
  ⟨zeroFact, S.DTOann, run1_dto_ann, Sup6X.root (List.Mem.head _), rfl, S.hsE, by decide⟩

#print axioms run1_email_confirmed

/-- THE SAME RESULT IN RUN 1 AS FOR `S`: the sink edges at the sink node of `root` and the
    vulnerabilities of run 1 are the same in SD and in S (both complete runs). -/
theorem same_result :
    (∀ i f, R1 (.edge 0 i 2 f) ↔ S.R1 (.edge 0 i 2 f)) ∧
    (∀ s d, R1 (.vuln 0 2 s d) ↔ S.R1 (.vuln 0 2 s d)) := by
  have hz : S.R1 (.edge 0 zeroFact 2 Zx) :=
    D6X.pass (D6X.step (D6X.start (D6X.root (List.Mem.head _))) S.hE00 (by decide)) S.hE01
      (by decide)
  refine ⟨fun i f => ⟨fun h => ?_, fun h => ?_⟩, fun s d => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨rfl, rfl | rfl⟩ := (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 →
      x.2.1 = zeroFact ∧ (x.2.2.2 = Zx ∨ x.2.2.2 = S.DTOann)) (0, i, 2, f) (inv1 h) rfl rfl
    · exact hz
    · exact S.run1_dto_ann.1
  · obtain ⟨rfl, rfl | rfl⟩ := (by decide : ∀ x ∈ S.edges1, x.1 = 0 → x.2.2.1 = 2 →
      x.2.1 = zeroFact ∧ (x.2.2.2 = Zx ∨ x.2.2.2 = S.DTOann)) (0, i, 2, f) (S.inv1 h) rfl rfl
    · exact r1_z2
    · exact run1_dto_ann
  · obtain ⟨rfl, rfl⟩ := (by decide : ∀ x ∈ S.vulns1, x.1 = 0 → x.2.1 = 2 →
      x.2.2.1 = S.sinkEmail ∧ x.2.2.2 = false) (0, 2, s, d) (inv1 h) rfl rfl
    exact S.run1_email_normal
  · obtain ⟨rfl, rfl⟩ := (by decide : ∀ x ∈ S.vulns1, x.1 = 0 → x.2.1 = 2 →
      x.2.2.1 = S.sinkEmail ∧ x.2.2.2 = false) (0, 2, s, d) (S.inv1 h) rfl rfl
    exact D6X.vuln run1_dto_ann S.hsE (by decide)

#print axioms same_result

end SD

/-! ## Program B: the broad demand

```
root1():  d = srcAny();    // 0 -> 1: zero.$ (zeroMark) -> d.[any] (T)
          d.setName(c);    // 1 -> 2
          sink(d.name);    // (d, [name], $, T) at node 2
root2():  e = srcAny();    // 0 -> 1: zero.$ (zeroMark) -> e.[any] (T)
          e.setName(c);    // 1 -> 2
          sinkAny(e);      // (e, [], [any], T) at node 2
setName(n):  this.name = n;  // `S.setS`
```
  Bases: zero = 0, d = 1, c = 2, this = 3, n = 4, e = 5. Methods: root1 = 0, root2 = 1 (nodes
  0, 1, 2; exit 2), setName = 2 (nodes 0, 1; exit 1). Both are roots.

  What it shows:
  * run 1 (`D6X`, complete: `inv1`): the record of `setName` gives `(d, [], [any-taint], {name}, T)`
    and `(e, [], [any-taint], {name}, T)`, both NORMAL; `sink(d.name)` is not reported
    (`run1_name_not_reported`); `sinkAny(e)` triggers (the pattern `(e, [], [any], T)` meets the
    admitted part) and run 1 CONFIRMS it (`run1_anyE_confirmed`);
  * run 3 (`DRXs`, the spec instance `emitX`, `satX`, `restrictX`) with the BROAD demand of
    `setName` `dBroad = (D-c = (this, [], [any], T), D-p = (this, [], [any], T))` (written by hand,
    `demB`) and any record set inside the run-1 records (`recs1`, `recs1_complete`): the
    `[any-taint]` added fact emits the MUST-PREMISE `(this, [], [any-taint], {}, T)` (`run3_must`);
    its start fact is normal, and the keep edge of `this.name = n` gives THE SUMMARY
    `(this, [], [any-taint]) → (this, [], [any-taint], {name}, T)`, NORMAL (`run3_summary`; the
    base model demotes it); the restricted summary gives `(d, [], [any-taint], {name}, T)`
    (`run3_d_ann`), so `sink(d.name)` is STILL NOT REPORTED (`inv3`, `run3_name_not_reported`);
    `sinkAny(e)` is confirmed (`run3_anyE_confirmed`). -/

namespace B

/-! ### The program -/

/-- The taint edge of `e = srcAny()`: `zero.$ (zeroMark) → e.[any] (T)`. -/
def srcE2 : MicroEdge := (zeroFact, ⟨5, [], .any, .conc 1⟩)
/-- `e = srcAny()`. -/
def srcS2 : Stmt := ⟨[0, 5], [(zeroFact, zeroFact), srcE2]⟩
/-- The taint edges of program B: the two sources. -/
def taintB : TaintEdges := fun e => decide (e = srcE) || decide (e = srcE2)
/-- `d.setName(c)`: the bindings of `S`. -/
def callSet1 : Call := ⟨2, [1, 2], [S.bThis, S.bN], [S.bBack, S.bNBack]⟩
/-- The binding of the receiver of `e.setName(c)`: `e.* → this.*`. -/
def bThisE : MicroEdge := (⟨5, [], st, .star⟩, ⟨3, [], st, .star⟩)
/-- The binding back of the receiver: `this.* → e.*`. -/
def bBackE : MicroEdge := (⟨3, [], st, .star⟩, ⟨5, [], st, .star⟩)
/-- `e.setName(c)`. -/
def callSet2 : Call := ⟨2, [5, 2], [bThisE, S.bN], [bBackE, S.bNBack]⟩
/-- Program B: `root1` (0), `root2` (1), `setName` (2). -/
def prog : Program := ⟨fun _ => 0, fun m => if m = 2 then 1 else 2,
  [(0, 0, .stmt srcS, 1), (0, 1, .call callSet1, 2), (1, 0, .stmt srcS2, 1),
   (1, 1, .call callSet2, 2), (2, 0, .stmt S.setS, 1)]⟩
/-- The sink pattern of `sinkAny(e)`: `(e, [], [any], T)`. -/
def sinkAnyE : PFact := ⟨5, [], .any, .conc 1⟩
/-- `sink(d.name)` in `root1`, `sinkAny(e)` in `root2`. -/
def sinks : List (MethodId × Node × PFact) := [(0, 2, S.sinkName), (1, 2, sinkAnyE)]
/-- Both `root1` and `root2` are roots. -/
def roots : List MethodId := [0, 1]

/-- The CFG edge of method 0 at node 0. -/
theorem hE00 : (0, 0, Instr.stmt srcS, 1) ∈ prog.edges := List.Mem.head _
/-- The CFG edge of method 0 at node 1. -/
theorem hE01 : (0, 1, Instr.call callSet1, 2) ∈ prog.edges := List.Mem.tail _ (List.Mem.head _)
/-- The CFG edge of method 1 at node 0. -/
theorem hE10 : (1, 0, Instr.stmt srcS2, 1) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
/-- The CFG edge of method 1 at node 1. -/
theorem hE11 : (1, 1, Instr.call callSet2, 2) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
/-- The CFG edge of method 2 at node 0. -/
theorem hE20 : (2, 0, Instr.stmt S.setS, 1) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
/-- The sink is a sink of the program. -/
theorem hsAny : ((1 : MethodId), (2 : Node), sinkAnyE) ∈ sinks := List.Mem.tail _ (List.Mem.head _)

/-- Program B has no cleaner. -/
theorem no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h with
          | tail _ h => cases h

/-- Program B has no type filter. -/
theorem no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h with
          | tail _ h => cases h

/-! ### The facts -/

/-- The source result `(e, [], [any-taint], {}, T)`, normal. -/
def Ex : XFact := ⟨⟨⟨5, [], .any, .conc 1⟩, false⟩, Excl.empty⟩
/-- The sink fact `(e, [], [any-taint], {name}, T)`, NORMAL. -/
def Eann : XFact := ⟨⟨⟨5, [], .any, .conc 1⟩, false⟩, .set [1]⟩
/-- THE MUST-PREMISE of run 3: `(this, [], [any-taint], {}, T)` (the fact `S.Athis`). -/
def Jany : PFact := ⟨3, [], .any, .conc 1⟩
/-- Its start fact: itself, NORMAL, with no exclusion. -/
def JanyX : XFact := ⟨⟨Jany, false⟩, Excl.empty⟩
/-- THE BROAD DEMAND of `setName`: `D-c = D-p = (this, [], [any], T)`. -/
def dBroad : DemandEdge := ⟨Jany, some Jany⟩
/-- The demand of run 3, by hand: `dBroad` for `setName`, nothing else. -/
def demB : Dem := fun m d => m = 2 ∧ d = dBroad

/-! ### Run 1 with the exclusion (`D6X`), completely -/

abbrev R1 : XObj6 → Prop := D6X prog taintB cnt 3 policy1 sinks roots

def inits1 : List (MethodId × PFact) := [(0, zeroFact), (1, zeroFact), (2, S.Jthis)]
def edges1 : List (MethodId × PFact × Node × XFact) :=
  [(0, zeroFact, 0, Zx), (0, zeroFact, 1, Zx), (0, zeroFact, 1, DTOx), (0, zeroFact, 2, Zx),
   (0, zeroFact, 2, S.DTOann),
   (1, zeroFact, 0, Zx), (1, zeroFact, 1, Zx), (1, zeroFact, 1, Ex), (1, zeroFact, 2, Zx),
   (1, zeroFact, 2, Eann),
   (2, S.Jthis, 0, S.JthisX), (2, S.Jthis, 1, S.KEEPx)]
def addeds1 : List (MethodId × PFact) := [(2, S.Athis)]
/-- The vulnerabilities: only `sinkAny(e)`, in the normal layer. -/
def vulns1 : List (MethodId × Node × PFact × Bool) := [(1, 2, sinkAnyE, false)]

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
/-- THE COMPLETE RUN 1 OF PROGRAM B WITH THE EXCLUSION: the sink edges are the zero edges and the
    NORMAL `(d, [], [any-taint], {name}, T)`, `(e, [], [any-taint], {name}, T)`; no request; the
    only vulnerability is `sinkAny(e)`, normal. -/
theorem inv1 {o : XObj6} (h : R1 o) : Inv1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h with
      | head => decide
      | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ inits1,
      Inv1 (.edge x.1 x.2 (prog.entry x.1) (startX x.2 false Excl.empty))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferX taintB cnt 3 srcS x.2.2.2).facts, Inv1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
            ∀ f' ∈ (transferX taintB cnt 3 srcS2 x.2.2.2).facts, Inv1 (.edge 1 x.2.1 1 f'))
            (1, i, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head =>
              exact (by decide : ∀ x ∈ edges1, x.1 = 2 → x.2.2.1 = 0 →
                ∀ f' ∈ (transferX taintB cnt 3 S.setS x.2.2.2).facts,
                  Inv1 (.edge 2 x.2.1 1 f'))
                (2, i, 0, f) ih rfl rfl f' hf
            | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    have hq : ∀ x ∈ edges1, ∀ s ∈ [srcS, srcS2, S.setS],
        ∀ t ∈ (transferX taintB cnt 3 s x.2.2.2).reqs, False := by decide
    cases hE with
    | head => exact hq (0, i, 0, f) ih srcS (List.Mem.head _) t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact hq (1, i, 0, f) ih srcS2 (List.Mem.tail _ (List.Mem.head _)) t ht
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head =>
              exact hq (2, i, 0, f) ih S.setS
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) t ht
            | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.af.fact.base callSet1.touched = false → Inv1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 1 →
              memB x.2.2.2.af.fact.base callSet2.touched = false →
                Inv1 (.edge 1 x.2.1 2 x.2.2.2))
              (1, i, 1, f) ih rfl rfl hm
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ callSet1.toCallee,
          ∀ a ∈ (bindX x.2.2.2 e).facts, Inv1 (.added callSet1.callee a.af.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 1 → ∀ e ∈ callSet2.toCallee,
              ∀ a ∈ (bindX x.2.2.2 e).facts, Inv1 (.added callSet2.callee a.af.fact))
              (1, i, 1, f) ih rfl rfl e he a ha
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ addeds1, Inv1 (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ callSet1.toCallee, ∀ a ∈ (bindX x.2.2.2 e1).facts,
          ∀ y ∈ inits1, y.1 = 2 → applicable y.2 a.af.fact = true →
          ∀ z ∈ edges1, z.1 = 2 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummaryX a y.2 Excl.empty z.2.2.2).facts,
          ∀ e2 ∈ callSet1.fromCallee, ∀ r' ∈ (bindX r e2).facts,
            Inv1 (.edge 0 x.2.1 2 (limitFX cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (2, j) ihj rfl hap (2, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 1 →
              ∀ e1 ∈ callSet2.toCallee, ∀ a ∈ (bindX x.2.2.2 e1).facts,
              ∀ y ∈ inits1, y.1 = 2 → applicable y.2 a.af.fact = true →
              ∀ z ∈ edges1, z.1 = 2 → z.2.1 = y.2 → z.2.2.1 = 1 →
              ∀ r ∈ (applySummaryX a y.2 Excl.empty z.2.2.2).facts,
              ∀ e2 ∈ callSet2.fromCallee, ∀ r' ∈ (bindX r e2).facts,
                Inv1 (.edge 1 x.2.1 2 (limitFX cnt 3 r')))
              (1, i, 1, f) ihf rfl rfl e1 he1 a ha (2, j) ihj rfl hap (2, j, 1, g) ihg rfl rfl
              rfl r hr e2 he2 r' hr'
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges1, ∀ s ∈ [S.sinkName, sinkAnyE],
        checkX x.2.1 x.2.2.2 s = .none ∨ checkX x.2.1 x.2.2.2 s = .triggered := by decide
    cases hs with
    | head =>
      rcases hnr (0, i, 2, f) ih S.sinkName (List.Mem.head _) with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs with
      | head =>
        rcases hnr (1, i, 2, f) ih sinkAnyE (List.Mem.tail _ (List.Mem.head _)) with h | h
        · rw [h] at hc; exact Check.noConfusion hc
        · rw [h] at hc; exact Check.noConfusion hc
      | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 →
        checkX x.2.1 x.2.2.2 S.sinkName = .triggered →
          (0, 2, S.sinkName, x.2.2.2.af.demand) ∈ vulns1) (0, i, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 2 →
          checkX x.2.1 x.2.2.2 sinkAnyE = .triggered →
            (1, 2, sinkAnyE, x.2.2.2.af.demand) ∈ vulns1) (1, i, 2, f) ih rfl rfl hc
      | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1

/-! ### Run 1: the derivations -/

/-- Run 1: the source edge `zero → (b, [], [any-taint], {}, T)`, normal. -/
theorem r1_e01 : R1 (.edge 0 zeroFact 1 DTOx) :=
  D6X.step (D6X.start (D6X.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1: the source edge `zero → (e, [], [any-taint], {}, T)` of `root2`, normal. -/
theorem r1_e11 : R1 (.edge 1 zeroFact 1 Ex) :=
  D6X.step (D6X.start (D6X.root (List.Mem.tail _ (List.Mem.head _)))) hE10 (by decide)

/-- Run 1: `policy1` serves the added fact `(this, [], [any], T)` of `setName` with
    `(this, [], *, {}, *)`. -/
theorem r1_i2 : R1 (.init 2 S.Jthis) := by
  have h : R1 (.init 2 (policy1 2 S.Athis)) :=
    D6X.initA (D6X.added (c := callSet1) (e := S.bThis) (a := S.AthisX) r1_e01 hE01
      (List.Mem.head _) (by decide))
  have hp : policy1 2 S.Athis = S.Jthis := by decide
  rw [hp] at h
  exact h

/-- Run 1: the record of `setName`, as in `S`. -/
theorem r1_rec : R1 (.edge 2 S.Jthis 1 S.KEEPx) := D6X.step (D6X.start r1_i2) hE20 (by decide)

/-- Run 1: `zero → (d, [], [any-taint], {name}, T)` at the sink node of `root1`, NORMAL. -/
theorem run1_d_ann : R1 (.edge 0 zeroFact 2 S.DTOann) :=
  D6X.ret (c := callSet1) (e1 := S.bThis) (a := S.AthisX) (j := S.Jthis) (g := S.KEEPx)
    (r := S.THISann) (e2 := S.bBack) (r' := S.DTOann) r1_e01 hE01 (List.Mem.head _) (by decide)
    r1_i2 (by decide) r1_rec (by decide) (List.Mem.head _) (by decide)

#print axioms run1_d_ann

/-- Run 1: `zero → (e, [], [any-taint], {name}, T)` at the sink node of `root2`, NORMAL. -/
theorem run1_e_ann : R1 (.edge 1 zeroFact 2 Eann) :=
  D6X.ret (c := callSet2) (e1 := bThisE) (a := S.AthisX) (j := S.Jthis) (g := S.KEEPx)
    (r := S.THISann) (e2 := bBackE) (r' := Eann) r1_e11 hE11 (List.Mem.head _) (by decide)
    r1_i2 (by decide) r1_rec (by decide) (List.Mem.head _) (by decide)

#print axioms run1_e_ann

/-- Run 1 does NOT report `sink(d.name)` (no vulnerability object, in no layer). -/
theorem run1_name_not_reported (d : Bool) : ¬ R1 (.vuln 0 2 S.sinkName d) := by
  intro h
  have h' := inv1 h
  cases d <;> exact absurd h' (by decide)

#print axioms run1_name_not_reported

/-- RUN 1 CONFIRMS `sinkAny(e)` (`Confirmed6X`): the sink pattern `(e, [], [any], T)` meets the
    admitted part of the normal `(e, [], [any-taint], {name}, T)` (at the path `[]` every
    exclusion admits the empty continuation). -/
theorem run1_anyE_confirmed : Confirmed6X prog taintB cnt 3 policy1 sinks roots 1 2 sinkAnyE :=
  ⟨zeroFact, Eann, run1_e_ann, Sup6X.root (List.Mem.tail _ (List.Mem.head _)), rfl, hsAny,
    by decide⟩

#print axioms run1_anyE_confirmed

/-- The complete exit edges of run 1, as the records of the restricted run (no must-premise, no
    premise exclusion in run 1): the zero edges of the roots and the record of `setName`. -/
def recs1 : List (MethodId × (PFact × Bool × Excl × XFact)) :=
  [(0, (zeroFact, false, Excl.empty, Zx)), (1, (zeroFact, false, Excl.empty, Zx)),
   (2, (S.Jthis, false, Excl.empty, S.KEEPx))]

/-- Every complete exit edge of run 1 is in `recs1` (ap.md §8.7 R1). -/
theorem recs1_complete {m : MethodId} {j : PFact} {g : XFact}
    (h : R1 (.edge m j (prog.exit m) g)) (hc : g.af.complete = true) :
    (m, (j, false, Excl.empty, g)) ∈ recs1 :=
  (by decide : ∀ x ∈ edges1, x.2.2.1 = prog.exit x.1 → x.2.2.2.af.complete = true →
    (x.1, (x.2.1, false, Excl.empty, x.2.2.2)) ∈ recs1) (m, j, _, g) (inv1 h) rfl hc

#print axioms recs1_complete

/-! ### Run 3 with the broad demand (`DRXs`), completely -/

/-- Run 3 of program B for a demand and a record set (the spec instance `emitX`, `satX`,
    `restrictX`). -/
abbrev R3 (demand : Dem) (recs : XRecs) : XObj → Prop :=
  DRXs prog taintB cnt 3 demand recs sinks roots

def inits3 : List (MethodId × PFact × Bool × Excl) :=
  [(0, zeroFact, false, Excl.empty), (1, zeroFact, false, Excl.empty), (2, Jany, true, Excl.empty)]
def edges3 : List (MethodId × PFact × Bool × Excl × Node × XFact) :=
  [(0, zeroFact, false, Excl.empty, 0, Zx), (0, zeroFact, false, Excl.empty, 1, Zx),
   (0, zeroFact, false, Excl.empty, 1, DTOx), (0, zeroFact, false, Excl.empty, 2, Zx),
   (0, zeroFact, false, Excl.empty, 2, S.DTOann),
   (1, zeroFact, false, Excl.empty, 0, Zx), (1, zeroFact, false, Excl.empty, 1, Zx),
   (1, zeroFact, false, Excl.empty, 1, Ex), (1, zeroFact, false, Excl.empty, 2, Zx),
   (1, zeroFact, false, Excl.empty, 2, Eann),
   (2, Jany, true, Excl.empty, 0, JanyX), (2, Jany, true, Excl.empty, 1, S.THISann)]
def addeds3 : List (MethodId × PFact × Bool × Excl) := [(2, S.Athis, true, Excl.empty)]

def Inv3 : XObj → Prop
  | .init M j mj jex => (M, j, mj, jex) ∈ inits3
  | .edge M j mj jex n f => (M, j, mj, jex, n, f) ∈ edges3
  | .added M a am aex => (M, a, am, aex) ∈ addeds3
  | .req _ _ _ => False
  | .vuln M n s d => (M, n, s, d) ∈ vulns1

instance : DecidablePred Inv3 := fun o =>
  match o with
  | .init M j mj jex => inferInstanceAs (Decidable ((M, j, mj, jex) ∈ inits3))
  | .edge M j mj jex n f => inferInstanceAs (Decidable ((M, j, mj, jex, n, f) ∈ edges3))
  | .added M a am aex => inferInstanceAs (Decidable ((M, a, am, aex) ∈ addeds3))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s d => inferInstanceAs (Decidable ((M, n, s, d) ∈ vulns1))

/-- A demand edge equal to `dBroad` is in the list `[dBroad]`. -/
theorem dem_mem {d : DemandEdge} (h : d = dBroad) : d ∈ [dBroad] := by
  subst h; exact List.Mem.head _

set_option synthInstance.maxSize 16384 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- THE COMPLETE RUN 3 OF PROGRAM B with the broad demand, for every demand that has only `dBroad`
    and every record set inside the run-1 records: the only premise of `setName` is the
    must-premise `(this, [], [any-taint], {}, T)`; its summary is
    `(this, [], [any-taint]) → (this, [], [any-taint], {name}, T)`, normal; the sink edges are
    those of run 1; no request; the only vulnerability is `sinkAny(e)`, normal. -/
theorem inv3 (demand : Dem) (recs : XRecs)
    (hd : ∀ m d, demand m d → d = dBroad) (hr : ∀ m x, recs m x → (m, x) ∈ recs1)
    {o : XObj} (h : R3 demand recs o) : Inv3 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h with
      | head => decide
      | tail _ h => cases h
  | @start M j mj jex _ ih =>
    exact (by decide : ∀ x ∈ inits3, Inv3 (.edge x.1 x.2.1 x.2.2.1 x.2.2.2 (prog.entry x.1)
      (startX x.2.1 x.2.2.1 x.2.2.2))) (M, j, mj, jex) ih
  | @step M i mi iex n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.2.1 = 0 →
        ∀ f' ∈ (transferX taintB cnt 3 srcS x.2.2.2.2.2).facts,
          Inv3 (.edge 0 x.2.1 x.2.2.1 x.2.2.2.1 1 f'))
        (0, i, mi, iex, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head =>
          exact (by decide : ∀ x ∈ edges3, x.1 = 1 → x.2.2.2.2.1 = 0 →
            ∀ f' ∈ (transferX taintB cnt 3 srcS2 x.2.2.2.2.2).facts,
              Inv3 (.edge 1 x.2.1 x.2.2.1 x.2.2.2.1 1 f'))
            (1, i, mi, iex, 0, f) ih rfl rfl f' hf
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head =>
              exact (by decide : ∀ x ∈ edges3, x.1 = 2 → x.2.2.2.2.1 = 0 →
                ∀ f' ∈ (transferX taintB cnt 3 S.setS x.2.2.2.2.2).facts,
                  Inv3 (.edge 2 x.2.1 x.2.2.1 x.2.2.2.1 1 f'))
                (2, i, mi, iex, 0, f) ih rfl rfl f' hf
            | tail _ hE => cases hE
  | @reqStmt M i mi iex n f n' s t _ hE ht ih =>
    have hq : ∀ x ∈ edges3, ∀ s ∈ [srcS, srcS2, S.setS],
        ∀ t ∈ (transferX taintB cnt 3 s x.2.2.2.2.2).reqs, False := by decide
    cases hE with
    | head => exact hq (0, i, mi, iex, 0, f) ih srcS (List.Mem.head _) t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact hq (1, i, mi, iex, 0, f) ih srcS2 (List.Mem.tail _ (List.Mem.head _)) t ht
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | head =>
              exact hq (2, i, mi, iex, 0, f) ih S.setS
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) t ht
            | tail _ hE => cases hE
  | @pass M i mi iex n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.2.1 = 1 →
          memB x.2.2.2.2.2.af.fact.base callSet1.touched = false →
            Inv3 (.edge 0 x.2.1 x.2.2.1 x.2.2.2.1 2 x.2.2.2.2.2))
          (0, i, mi, iex, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges3, x.1 = 1 → x.2.2.2.2.1 = 1 →
              memB x.2.2.2.2.2.af.fact.base callSet2.touched = false →
                Inv3 (.edge 1 x.2.1 x.2.2.1 x.2.2.2.1 2 x.2.2.2.2.2))
              (1, i, mi, iex, 1, f) ih rfl rfl hm
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | @added M i mi iex n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.2.1 = 1 → ∀ e ∈ callSet1.toCallee,
          ∀ a ∈ (bindX x.2.2.2.2.2 e).facts,
            Inv3 (.added callSet1.callee a.af.fact (a.af.fact.kind.isAny && !a.af.demand) a.ex))
          (0, i, mi, iex, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges3, x.1 = 1 → x.2.2.2.2.1 = 1 →
              ∀ e ∈ callSet2.toCallee, ∀ a ∈ (bindX x.2.2.2.2.2 e).facts,
                Inv3 (.added callSet2.callee a.af.fact (a.af.fact.kind.isAny && !a.af.demand)
                  a.ex))
              (1, i, mi, iex, 1, f) ih rfl rfl e he a ha
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | @initR m a am aex d j mj jex _ hdm he ih =>
    exact (by decide : ∀ y ∈ addeds3, ∀ dd ∈ [dBroad],
      ∀ jm ∈ (emitTX emitX dd.din y.2.1 y.2.2.1 y.2.2.2).toList,
        Inv3 (.init y.1 jm.1 jm.2.1 jm.2.2))
      (m, a, am, aex) ih d (dem_mem (hd m d hdm)) (j, mj, jex) (mem_toList_of_eq_some he)
  | @ret M i mi iex n f n' c e1 a j mj jex g d g' r e2 r' _ hE he1 ha _ _ hdm hres hsat hrr
      he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.2.1 = 1 →
          ∀ e1 ∈ callSet1.toCallee, ∀ a ∈ (bindX x.2.2.2.2.2 e1).facts,
          ∀ y ∈ inits3, y.1 = 2 →
          ∀ z ∈ edges3, z.1 = 2 → z.2.1 = y.2.1 → z.2.2.1 = y.2.2.1 → z.2.2.2.1 = y.2.2.2 →
            z.2.2.2.2.1 = 1 →
          ∀ dd ∈ [dBroad], ∀ g' ∈ (restrictX y.2.1 y.2.2.2 z.2.2.2.2.2 dd).toList,
          satX y.2.1 y.2.2.2 a.af.fact a.ex = true →
          ∀ r ∈ (applySummaryX a y.2.1 y.2.2.2 g').facts,
          ∀ e2 ∈ callSet1.fromCallee, ∀ r' ∈ (bindX r e2).facts,
            Inv3 (.edge 0 x.2.1 x.2.2.1 x.2.2.2.1 2 (limitFX cnt 3 r')))
          (0, i, mi, iex, 1, f) ihf rfl rfl e1 he1 a ha (2, j, mj, jex) ihj rfl
          (2, j, mj, jex, 1, g) ihg rfl rfl rfl rfl rfl d (dem_mem (hd _ d hdm)) g'
          (mem_toList_of_eq_some hres) hsat r hrr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges3, x.1 = 1 → x.2.2.2.2.1 = 1 →
              ∀ e1 ∈ callSet2.toCallee, ∀ a ∈ (bindX x.2.2.2.2.2 e1).facts,
              ∀ y ∈ inits3, y.1 = 2 →
              ∀ z ∈ edges3, z.1 = 2 → z.2.1 = y.2.1 → z.2.2.1 = y.2.2.1 →
                z.2.2.2.1 = y.2.2.2 → z.2.2.2.2.1 = 1 →
              ∀ dd ∈ [dBroad], ∀ g' ∈ (restrictX y.2.1 y.2.2.2 z.2.2.2.2.2 dd).toList,
              satX y.2.1 y.2.2.2 a.af.fact a.ex = true →
              ∀ r ∈ (applySummaryX a y.2.1 y.2.2.2 g').facts,
              ∀ e2 ∈ callSet2.fromCallee, ∀ r' ∈ (bindX r e2).facts,
                Inv3 (.edge 1 x.2.1 x.2.2.1 x.2.2.2.1 2 (limitFX cnt 3 r')))
              (1, i, mi, iex, 1, f) ihf rfl rfl e1 he1 a ha (2, j, mj, jex) ihj rfl
              (2, j, mj, jex, 1, g) ihg rfl rfl rfl rfl rfl d (dem_mem (hd _ d hdm)) g'
              (mem_toList_of_eq_some hres) hsat r hrr e2 he2 r' hr'
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | @retRec M i mi iex n f n' c e1 a j mj jex g r e2 r' _ hE he1 ha hrec hsa hrr he2 hr' ihf =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.2.1 = 1 →
          ∀ e1 ∈ callSet1.toCallee, ∀ a ∈ (bindX x.2.2.2.2.2 e1).facts,
          ∀ q ∈ recs1, q.1 = 2 →
          (satX q.2.1 q.2.2.2.1 a.af.fact a.ex = true ∨ applicable q.2.1 a.af.fact = true) →
          ∀ r ∈ (applySummaryX a q.2.1 q.2.2.2.1 q.2.2.2.2).facts,
          ∀ e2 ∈ callSet1.fromCallee, ∀ r' ∈ (bindX r e2).facts,
            Inv3 (.edge 0 x.2.1 x.2.2.1 x.2.2.2.1 2
              (limitFX cnt 3 (recLayerX q.2.2.1 (satX q.2.1 q.2.2.2.1 a.af.fact a.ex) r'))))
          (0, i, mi, iex, 1, f) ihf rfl rfl e1 he1 a ha (2, (j, mj, jex, g)) (hr _ _ hrec) rfl
          hsa r hrr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges3, x.1 = 1 → x.2.2.2.2.1 = 1 →
              ∀ e1 ∈ callSet2.toCallee, ∀ a ∈ (bindX x.2.2.2.2.2 e1).facts,
              ∀ q ∈ recs1, q.1 = 2 →
              (satX q.2.1 q.2.2.2.1 a.af.fact a.ex = true ∨ applicable q.2.1 a.af.fact = true) →
              ∀ r ∈ (applySummaryX a q.2.1 q.2.2.2.1 q.2.2.2.2).facts,
              ∀ e2 ∈ callSet2.fromCallee, ∀ r' ∈ (bindX r e2).facts,
                Inv3 (.edge 1 x.2.1 x.2.2.1 x.2.2.2.1 2
                  (limitFX cnt 3 (recLayerX q.2.2.1 (satX q.2.1 q.2.2.2.1 a.af.fact a.ex) r'))))
              (1, i, mi, iex, 1, f) ihf rfl rfl e1 he1 a ha (2, (j, mj, jex, g)) (hr _ _ hrec)
              rfl hsa r hrr e2 he2 r' hr'
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | @reqSink M i mi iex n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges3, ∀ s ∈ [S.sinkName, sinkAnyE],
        checkX x.2.1 x.2.2.2.2.2 s = .none ∨ checkX x.2.1 x.2.2.2.2.2 s = .triggered := by decide
    cases hs with
    | head =>
      rcases hnr (0, i, mi, iex, 2, f) ih S.sinkName (List.Mem.head _) with h | h
      · rw [h] at hc; exact Check.noConfusion hc
      · rw [h] at hc; exact Check.noConfusion hc
    | tail _ hs => cases hs with
      | head =>
        rcases hnr (1, i, mi, iex, 2, f) ih sinkAnyE (List.Mem.tail _ (List.Mem.head _)) with h | h
        · rw [h] at hc; exact Check.noConfusion hc
        · rw [h] at hc; exact Check.noConfusion hc
      | tail _ hs => cases hs
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i mi iex n f s _ hs hc ih =>
    cases hs with
    | head =>
      exact (by decide : ∀ x ∈ edges3, x.1 = 0 → x.2.2.2.2.1 = 2 →
        checkX x.2.1 x.2.2.2.2.2 S.sinkName = .triggered →
          (0, 2, S.sinkName, x.2.2.2.2.2.af.demand) ∈ vulns1) (0, i, mi, iex, 2, f) ih rfl rfl hc
    | tail _ hs => cases hs with
      | head =>
        exact (by decide : ∀ x ∈ edges3, x.1 = 1 → x.2.2.2.2.1 = 2 →
          checkX x.2.1 x.2.2.2.2.2 sinkAnyE = .triggered →
            (1, 2, sinkAnyE, x.2.2.2.2.2.af.demand) ∈ vulns1) (1, i, mi, iex, 2, f) ih rfl rfl hc
      | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv3

/-! ### Run 3: the derivations -/

/-- THE MUST-PREMISE AND ITS SUMMARY, the operations (DESIGN A2; decision 8): the `[any-taint]`
    added fact `(this, [], [any-taint], {}, T)` against `D-c = (this, [], [any], T)` emits the
    must-premise `(this, [], [any-taint], {}, T)` (the tail of the added fact); it starts as itself,
    NORMAL; the keep edge of `this.name = n` gives `(this, [], [any-taint], {name}, T)`, NORMAL
    (the base model demotes it to `(this, [], [any], T)` in the demand layer); the restriction by
    `D-p = (this, [], [any], T)` keeps the summary; the added fact satisfies the premise (`satX`),
    and the application gives the conclusion with its exclusion. -/
theorem must_summary_ops :
    emitTX emitX dBroad.din S.Athis true Excl.empty = some (Jany, true, Excl.empty) ∧
    startX Jany true Excl.empty = JanyX ∧
    transferX taintB cnt 3 S.setS JanyX = ⟨[S.THISann], []⟩ ∧
    (transferT taintB cnt 3 S.setS JanyX.af).facts = [⟨Jany, true⟩] ∧
    restrictX Jany Excl.empty S.THISann dBroad = some S.THISann ∧
    satX Jany Excl.empty S.Athis Excl.empty = true ∧
    applySummaryX S.AthisX Jany Excl.empty S.THISann = ⟨[S.THISann], []⟩ ∧
    S.THISann.af.demand = false ∧ S.THISann.ex = .set [1] := by decide

#print axioms must_summary_ops

section Run3
variable (recs : XRecs)

/-- Run 3: the source edge `zero → (d, [], [any-taint], {}, T)` of `root1`, normal. -/
theorem r3_e01 : R3 demB recs (.edge 0 zeroFact false Excl.empty 1 DTOx) :=
  DRX.step (DRX.start (DRX.root (List.Mem.head _))) hE00 (by decide)

/-- Run 3: the source edge `zero → (e, [], [any-taint], {}, T)` of `root2`, normal. -/
theorem r3_e11 : R3 demB recs (.edge 1 zeroFact false Excl.empty 1 Ex) :=
  DRX.step (DRX.start (DRX.root (List.Mem.tail _ (List.Mem.head _)))) hE10 (by decide)

/-- Run 3: the added fact of `setName` is `[any-taint]` on its link (`am = true`), with no
    exclusion. -/
theorem r3_ad : R3 demB recs (.added 2 S.Athis true Excl.empty) :=
  DRX.added (c := callSet1) (e := S.bThis) (a := S.AthisX) (r3_e01 recs) hE01 (List.Mem.head _)
    (by decide)

/-- Run 3: THE MUST-PREMISE `(this, [], [any-taint], {}, T)` of `setName`, emitted from the broad
    demand. -/
theorem run3_must : R3 demB recs (.init 2 Jany true Excl.empty) :=
  DRX.initR (d := dBroad) (r3_ad recs) ⟨rfl, rfl⟩ (by decide)

#print axioms run3_must

/-- Run 3: THE SUMMARY OF THE MUST-PREMISE: `(this, [], [any-taint], {}, T) →
    (this, [], [any-taint], {name}, T)`, in the NORMAL layer (an end-exact edge of a must-premise:
    every location below `this` but the ones below `this.name` keeps the mark). -/
theorem run3_summary :
    R3 demB recs (.edge 2 Jany true Excl.empty 1 S.THISann) ∧ S.THISann.af.fact = Jany ∧
    S.THISann.af.demand = false ∧ S.THISann.ex = .set [1] :=
  ⟨DRX.step (DRX.start (run3_must recs)) hE20 (by decide), rfl, rfl, rfl⟩

#print axioms run3_summary

/-- Run 3: the restricted summary gives `zero → (d, [], [any-taint], {name}, T)` in `root1`,
    NORMAL. -/
theorem run3_d_ann : R3 demB recs (.edge 0 zeroFact false Excl.empty 2 S.DTOann) :=
  DRX.ret (c := callSet1) (e1 := S.bThis) (a := S.AthisX) (j := Jany) (mj := true)
    (jex := Excl.empty) (g := S.THISann) (d := dBroad) (g' := S.THISann) (r := S.THISann)
    (e2 := S.bBack) (r' := S.DTOann) (r3_e01 recs) hE01 (List.Mem.head _) (by decide)
    (run3_must recs) (run3_summary recs).1 ⟨rfl, rfl⟩ (by decide) (by decide) (by decide)
    (List.Mem.head _) (by decide)

#print axioms run3_d_ann

/-- Run 3: the restricted summary gives `zero → (e, [], [any-taint], {name}, T)` in `root2`,
    NORMAL. -/
theorem run3_e_ann : R3 demB recs (.edge 1 zeroFact false Excl.empty 2 Eann) :=
  DRX.ret (c := callSet2) (e1 := bThisE) (a := S.AthisX) (j := Jany) (mj := true)
    (jex := Excl.empty) (g := S.THISann) (d := dBroad) (g' := S.THISann) (r := S.THISann)
    (e2 := bBackE) (r' := Eann) (r3_e11 recs) hE11 (List.Mem.head _) (by decide)
    (run3_must recs) (run3_summary recs).1 ⟨rfl, rfl⟩ (by decide) (by decide) (by decide)
    (List.Mem.head _) (by decide)

#print axioms run3_e_ann

/-- RUN 3 CONFIRMS `sinkAny(e)` (`ConfirmedX`): the normal sink edge under the supported zero
    premise of `root2`. -/
theorem run3_anyE_confirmed :
    ConfirmedX prog taintB cnt 3 demB emitX satX restrictX recs sinks roots 1 2 sinkAnyE :=
  ⟨zeroFact, false, Excl.empty, Eann, run3_e_ann recs,
    SupX.root (List.Mem.tail _ (List.Mem.head _)), rfl, hsAny, by decide⟩

#print axioms run3_anyE_confirmed

end Run3

/-- RUN 3 STILL DOES NOT REPORT `sink(d.name)`: with the broad demand (the must-premise
    `(this, [], [any-taint], T)` of `setName`) and any record set inside the run-1 records, there is
    no vulnerability object for it, in no layer (the complete run `inv3`). -/
theorem run3_name_not_reported (recs : XRecs) (hr : ∀ m x, recs m x → (m, x) ∈ recs1)
    (d : Bool) : ¬ R3 demB recs (.vuln 0 2 S.sinkName d) := by
  intro h
  have h' := inv3 demB recs (fun _ _ hd => hd.2) hr h
  cases d <;> exact absurd h' (by decide)

#print axioms run3_name_not_reported

/-- The run-1 record set of program B (`recs1`) as a record set. -/
def recsB : XRecs := fun m x => (m, x) ∈ recs1

/-- The iteration with the run-1 records: run 3 with the broad demand and the records `recsB` (the
    complete exit edges of run 1, `recs1_complete`) derives the normal sink edge of `root1`, does
    not report `sink(d.name)`, and confirms `sinkAny(e)`. -/
theorem run3_with_records :
    R3 demB recsB (.edge 0 zeroFact false Excl.empty 2 S.DTOann) ∧
    (∀ d, ¬ R3 demB recsB (.vuln 0 2 S.sinkName d)) ∧
    ConfirmedX prog taintB cnt 3 demB emitX satX restrictX recsB sinks roots 1 2 sinkAnyE :=
  ⟨run3_d_ann recsB, run3_name_not_reported recsB (fun _ _ h => h), run3_anyE_confirmed recsB⟩

#print axioms run3_with_records

end B

/-! ## Program X: a two-level write in one statement

```
root():  x = srcAny();   // 0 -> 1: zero.$ (zeroMark) -> x.[any] (T)
         x.f.g = c;      // 1 -> 2: the keep edges x.*/{f} -> x.* (spec: x.* ->_{f} x.*) and
                         //         x.f.*/{g} -> x.f.* (spec: x.f.* ->_{g} x.f.*), the identity
                         //         on c, the gen edge c.* -> x.f.g.*
         sink(x.f.g);    // (x, [f, g], $, T) at node 2
         sink(x.f.h);    // (x, [f, h], $, T) at node 2
         sink(x.k);      // (x, [k], $, T) at node 2
```
  Bases: zero = 0, x = 1, c = 2. Accessors: f = 1, g = 2, h = 3, k = 4. Method root = 0 (nodes
  0, 1, 2; exit 2).

  What it shows: the statement on `(x, [], [any-taint], {}, T)` gives TWO results, both NORMAL
  (`two_results`): the first keep edge is case `below r = []` (`E ∪ {f}`): `(x, [], [any-taint],
  {f}, T)`; the second keep edge is case `above [f]` with a `*` target (A2: "the result of a `*`
  target is `[any-taint]` with the EDGE's exclusion"): `(x, [f], [any-taint], {g}, T)`. The base
  model gives both in the demand layer. Together they cover every location below `x` but the ones
  below `x.f.g` (`locations_exact`). So `sink(x.f.g)` is not reported (`fg_not_reported`), and
  `sink(x.f.h)` and `sink(x.k)` are reported in the NORMAL layer and confirmed (`fh_confirmed`,
  `k_confirmed`; the complete run: `inv1`). -/

namespace X

/-! ### The program -/

/-- The keep edge of `x.f.g = c` at `x`: `x.*/{f} → x.*`. -/
def keep1 : MicroEdge := (⟨1, [], .star (.set [1]), .star⟩, ⟨1, [], st, .star⟩)
/-- The keep edge of `x.f.g = c` at `x.f`: `x.f.*/{g} → x.f.*`. -/
def keep2 : MicroEdge := (⟨1, [1], .star (.set [2]), .star⟩, ⟨1, [1], st, .star⟩)
/-- The identity on `c`. -/
def idC : MicroEdge := (⟨2, [], st, .star⟩, ⟨2, [], st, .star⟩)
/-- The gen edge: `c.* → x.f.g.*`. -/
def gen : MicroEdge := (⟨2, [], st, .star⟩, ⟨1, [1, 2], st, .star⟩)
/-- `x.f.g = c`. -/
def wrS : Stmt := ⟨[1, 2], [keep1, keep2, idC, gen]⟩
/-- Program X. -/
def prog : Program := ⟨fun _ => 0, fun _ => 2, [(0, 0, .stmt srcS, 1), (0, 1, .stmt wrS, 2)]⟩
/-- `sink(x.f.g)`: `(x, [f, g], $, T)`. -/
def sFG : PFact := ⟨1, [1, 2], .exact, .conc 1⟩
/-- `sink(x.f.h)`: `(x, [f, h], $, T)`. -/
def sFH : PFact := ⟨1, [1, 3], .exact, .conc 1⟩
/-- `sink(x.k)`: `(x, [k], $, T)`. -/
def sK : PFact := ⟨1, [4], .exact, .conc 1⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sFG), (0, 2, sFH), (0, 2, sK)]

/-- The CFG edge of method 0 at node 0. -/
theorem hE00 : (0, 0, Instr.stmt srcS, 1) ∈ prog.edges := List.Mem.head _
/-- The CFG edge of method 0 at node 1. -/
theorem hE01 : (0, 1, Instr.stmt wrS, 2) ∈ prog.edges := List.Mem.tail _ (List.Mem.head _)
/-- The sink is a sink of the program. -/
theorem hsFH : ((0 : MethodId), (2 : Node), sFH) ∈ sinks := List.Mem.tail _ (List.Mem.head _)
/-- The sink is a sink of the program. -/
theorem hsK : ((0 : MethodId), (2 : Node), sK) ∈ sinks :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- The program has no call. -/
theorem no_call {M n c n'} (h : (M, n, Instr.call c, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

/-- The program has no cleaner. -/
theorem no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

/-- The program has no type filter. -/
theorem no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

/-! ### The facts -/

/-- `(x, [], [any-taint], {f}, T)`, NORMAL. -/
def XF : XFact := ⟨⟨⟨1, [], .any, .conc 1⟩, false⟩, .set [1]⟩
/-- `(x, [f], [any-taint], {g}, T)`, NORMAL. -/
def XFG : XFact := ⟨⟨⟨1, [1], .any, .conc 1⟩, false⟩, .set [2]⟩

/-- THE TWO RESULTS (DESIGN A2): on `(x, [], [any-taint], {}, T)` the first keep edge is a `keep`
    row at `r = []` with the exclusion `{f}`, the second keep edge a `keep` row of case `above [f]`
    with the edge's exclusion `{g}`; the identity on `c` and the gen edge do not apply; the field
    limit keeps both. The statement gives exactly `(x, [], [any-taint], {f}, T)` and
    `(x, [f], [any-taint], {g}, T)`, both NORMAL. The base model (`transferT`) gives the same two
    facts in the DEMAND layer. -/
theorem two_results :
    annX DTOx keep1.1 Excl.empty keep1.2 Excl.empty = some (true, .set [1]) ∧
    relate keep2.1.path DTOx.af.fact.path = .above [1] ∧
    annX DTOx keep2.1 Excl.empty keep2.2 Excl.empty = some (true, .set [2]) ∧
    transferX taint cnt 3 wrS DTOx = ⟨[XF, XFG], []⟩ ∧
    (transferT taint cnt 3 wrS DTO).facts = [⟨XF.af.fact, true⟩, ⟨XFG.af.fact, true⟩] :=
  ⟨by decide, rfl, by decide, by decide, by decide⟩

#print axioms two_results

/-- THE LOCATION SETS OF THE TWO RESULTS are exact: a location `(x, τ, T)` is in
    `(x, [], [any-taint], {f}, T)` or in `(x, [f], [any-taint], {g}, T)` iff `τ` does not start with
    `[f, g]` (the write `x.f.g = c` overwrites exactly the locations below `x.f.g`). -/
theorem locations_exact (τ : List Acc) :
    (coversFX XF.af.fact XF.ex ⟨1, τ, 1⟩ ∨ coversFX XFG.af.fact XFG.ex ⟨1, τ, 1⟩) ↔
    ¬ ∃ ρ, τ = 1 :: 2 :: ρ := by
  constructor
  · rintro (⟨_, ⟨τ', hp, _, ha⟩, _⟩ | ⟨_, ⟨τ', hp, _, ha⟩, _⟩) ⟨ρ, rfl⟩
    · change 1 :: 2 :: ρ = τ' at hp
      subst hp
      have h0 : XF.ex.admits (1 :: 2 :: ρ) = false := rfl
      rw [h0] at ha
      exact Bool.noConfusion ha
    · change 1 :: 2 :: ρ = 1 :: τ' at hp
      have h2 := (List.cons.inj hp).2
      subst h2
      have h0 : XFG.ex.admits (2 :: ρ) = false := rfl
      rw [h0] at ha
      exact Bool.noConfusion ha
  · intro hn
    match τ with
    | [] => exact Or.inl ⟨rfl, ⟨[], rfl, trivial, rfl⟩, 1, rfl, rfl⟩
    | a :: τ' =>
      cases ha : Nat.beq a 1 with
      | false =>
        refine Or.inl ⟨rfl, ⟨a :: τ', rfl, trivial, ?_⟩, 1, rfl, rfl⟩
        show (!(Nat.beq a 1 || false)) = true
        rw [ha]; rfl
      | true =>
        have ha' : a = 1 := Nat.eq_of_beq_eq_true ha
        subst ha'
        match τ' with
        | [] => exact Or.inr ⟨rfl, ⟨[], rfl, trivial, rfl⟩, 1, rfl, rfl⟩
        | b :: ρ =>
          cases hb : Nat.beq b 2 with
          | false =>
            refine Or.inr ⟨rfl, ⟨b :: ρ, rfl, trivial, ?_⟩, 1, rfl, rfl⟩
            show (!(Nat.beq b 2 || false)) = true
            rw [hb]; rfl
          | true =>
            have hb' : b = 2 := Nat.eq_of_beq_eq_true hb
            subst hb'
            exact absurd ⟨ρ, rfl⟩ hn

#print axioms locations_exact

/-! ### Run 1 with the exclusion (`D6X`), completely -/

abbrev R1 : XObj6 → Prop := D6X prog taint cnt 3 policy1 sinks [0]

def edges1 : List (MethodId × PFact × Node × XFact) :=
  [(0, zeroFact, 0, Zx), (0, zeroFact, 1, Zx), (0, zeroFact, 1, DTOx), (0, zeroFact, 2, Zx),
   (0, zeroFact, 2, XF), (0, zeroFact, 2, XFG)]
/-- The vulnerabilities: `sink(x.f.h)` and `sink(x.k)`, normal. -/
def vulns1 : List (MethodId × Node × PFact × Bool) := [(0, 2, sFH, false), (0, 2, sK, false)]

def Inv1 : XObj6 → Prop
  | .init M i => (M, i) ∈ [((0 : MethodId), zeroFact)]
  | .edge M i n f => (M, i, n, f) ∈ edges1
  | .added _ _ => False
  | .req _ _ _ => False
  | .vuln M n s d => (M, n, s, d) ∈ vulns1

instance : DecidablePred Inv1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ [((0 : MethodId), zeroFact)]))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1))
  | .added _ _ => inferInstanceAs (Decidable False)
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s d => inferInstanceAs (Decidable ((M, n, s, d) ∈ vulns1))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM X WITH THE EXCLUSION: the sink edges are the zero edge and the two
    NORMAL results; no request; the vulnerabilities are `sink(x.f.h)` and `sink(x.k)`, normal. -/
theorem inv1 {o : XObj6} (h : R1 o) : Inv1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ [((0 : MethodId), zeroFact)],
      Inv1 (.edge x.1 x.2 (prog.entry x.1) (startX x.2 false Excl.empty))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferX taint cnt 3 srcS x.2.2.2).facts, Inv1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ f' ∈ (transferX taint cnt 3 wrS x.2.2.2).facts, Inv1 (.edge 0 x.2.1 2 f'))
          (0, i, 1, f) ih rfl rfl f' hf
      | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    have hq : ∀ x ∈ edges1, ∀ s ∈ [srcS, wrS], ∀ t ∈ (transferX taint cnt 3 s x.2.2.2).reqs,
        False := by decide
    cases hE with
    | head => exact hq (0, i, 0, f) ih srcS (List.Mem.head _) t ht
    | tail _ hE => cases hE with
      | head => exact hq (0, i, 1, f) ih wrS (List.Mem.tail _ (List.Mem.head _)) t ht
      | tail _ hE => cases hE
  | pass _ hE _ _ => exact (no_call hE).elim
  | added _ hE _ _ _ => exact (no_call hE).elim
  | initA _ ih => exact ih.elim
  | ret _ hE _ _ _ _ _ _ _ _ _ _ _ => exact (no_call hE).elim
  | @reqSink M i n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges1, ∀ s ∈ [sFG, sFH, sK],
        checkX x.2.1 x.2.2.2 s = .none ∨ checkX x.2.1 x.2.2.2 s = .triggered := by decide
    have hs' : s ∈ [sFG, sFH, sK] := by
      cases hs with
      | head => exact List.Mem.head _
      | tail _ hs => cases hs with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ hs => cases hs with
          | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
          | tail _ hs => cases hs
    rcases hnr (M, i, n, f) ih s hs' with h | h
    · rw [h] at hc; exact Check.noConfusion hc
    · rw [h] at hc; exact Check.noConfusion hc
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    have hv : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 → ∀ s ∈ [sFG, sFH, sK],
        checkX x.2.1 x.2.2.2 s = .triggered → (0, 2, s, x.2.2.2.af.demand) ∈ vulns1 := by decide
    cases hs with
    | head => exact hv (0, i, 2, f) ih rfl rfl sFG (List.Mem.head _) hc
    | tail _ hs => cases hs with
      | head => exact hv (0, i, 2, f) ih rfl rfl sFH (List.Mem.tail _ (List.Mem.head _)) hc
      | tail _ hs => cases hs with
        | head =>
          exact hv (0, i, 2, f) ih rfl rfl sK
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) hc
        | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1

/-! ### Run 1: the derivations and the theorems -/

/-- Run 1: the source edge `zero → (b, [], [any-taint], {}, T)`, normal. -/
theorem r1_e01 : R1 (.edge 0 zeroFact 1 DTOx) :=
  D6X.step (D6X.start (D6X.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1 derives the TWO NORMAL RESULTS of `x.f.g = c` at the sink node, and no other fact on
    `x` (`inv1`). -/
theorem run1_results :
    R1 (.edge 0 zeroFact 2 XF) ∧ R1 (.edge 0 zeroFact 2 XFG) ∧
    (∀ i f, R1 (.edge 0 i 2 f) → f = Zx ∨ f = XF ∨ f = XFG) :=
  ⟨D6X.step r1_e01 hE01 (by decide), D6X.step r1_e01 hE01 (by decide), fun i f h =>
    (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 →
      x.2.2.2 = Zx ∨ x.2.2.2 = XF ∨ x.2.2.2 = XFG) (0, i, 2, f) (inv1 h) rfl rfl⟩

#print axioms run1_results

/-- `sink(x.f.g)` IS NOT REPORTED (no vulnerability object, in no layer): the pattern lies in the
    excluded part of both results. -/
theorem fg_not_reported (d : Bool) : ¬ R1 (.vuln 0 2 sFG d) := by
  intro h
  have h' := inv1 h
  cases d <;> exact absurd h' (by decide)

#print axioms fg_not_reported

/-- `sink(x.f.h)` is reported in the NORMAL layer (by `(x, [f], [any-taint], {g}, T)`) and run 1
    CONFIRMS it. -/
theorem fh_confirmed :
    R1 (.vuln 0 2 sFH false) ∧ Confirmed6X prog taint cnt 3 policy1 sinks [0] 0 2 sFH :=
  ⟨D6X.vuln run1_results.2.1 hsFH (by decide),
    ⟨zeroFact, XFG, run1_results.2.1, Sup6X.root (List.Mem.head _), rfl, hsFH, by decide⟩⟩

#print axioms fh_confirmed

/-- `sink(x.k)` is reported in the NORMAL layer (by `(x, [], [any-taint], {f}, T)`) and run 1
    CONFIRMS it. -/
theorem k_confirmed :
    R1 (.vuln 0 2 sK false) ∧ Confirmed6X prog taint cnt 3 policy1 sinks [0] 0 2 sK :=
  ⟨D6X.vuln run1_results.1 hsK (by decide),
    ⟨zeroFact, XF, run1_results.1, Sup6X.root (List.Mem.head _), rfl, hsK, by decide⟩⟩

#print axioms k_confirmed

/-- The complete run 1 has no demand-layer report. -/
theorem run1_no_demand (s : PFact) : ¬ R1 (.vuln 0 2 s true) := by
  intro h
  have h' : (0, 2, s, true) ∈ vulns1 := inv1 h
  exact absurd h' (by
    intro hm
    cases hm with
    | tail _ hm => cases hm with
      | tail _ hm => cases hm)

#print axioms run1_no_demand

end X

/-! ## Program R: a read through an excluded accessor

```
root():  dto = srcAny();    // 0 -> 1
         dto.setName(c);    // 1 -> 2 (the call of `S`)
         y = dto.name;      // 2 -> 3: the identity on dto, the read dto.name.* -> y.*
         z = dto.email;     // 3 -> 4: the identity on dto, the read dto.email.* -> z.*
         sinkAny(y);        // (y, [], [any], T) at node 4
         sinkAny(z);        // (z, [], [any], T) at node 4
setName(n):  this.name = n;   // `S.setS`
```
  Bases: zero = 0, dto = 1, c = 2, this = 3, n = 4, y = 5, z = 6. Accessors: name = 1,
  email = 2. Methods: root = 0 (nodes 0 .. 4; exit 4), setName = 1.

  What it shows: after the setter, `dto` is `(dto, [], [any-taint], {name}, T)` (as in `S`). The read
  `y = dto.name` is case `above [name]`, and `{name}` does not admit it (A2: "a read `y = c.P.g`
  with `g ∈ E`: nothing"): NO FACT FOR `y`, at no node (`reads`, `no_y`), so `sinkAny(y)` is not
  reported (`y_not_reported`). The read `z = dto.email` (`email ∉ {name}`) gives
  `(z, [], [any-taint], {}, T)`, NORMAL (`run1_z`), and `sinkAny(z)` is confirmed
  (`z_confirmed`). -/

namespace R

/-! ### The program -/

/-- The identity on `dto`. -/
def idDto : MicroEdge := (⟨1, [], st, .star⟩, ⟨1, [], st, .star⟩)
/-- The read of `y = dto.name`: `dto.name.* → y.*`. -/
def readNameE : MicroEdge := (⟨1, [1], st, .star⟩, ⟨5, [], st, .star⟩)
/-- The read of `z = dto.email`: `dto.email.* → z.*`. -/
def readEmailE : MicroEdge := (⟨1, [2], st, .star⟩, ⟨6, [], st, .star⟩)
/-- `y = dto.name`. -/
def readName : Stmt := ⟨[1, 5], [idDto, readNameE]⟩
/-- `z = dto.email`. -/
def readEmail : Stmt := ⟨[1, 6], [idDto, readEmailE]⟩
/-- Program R. -/
def prog : Program := ⟨fun _ => 0, fun m => if m = 1 then 1 else 4,
  [(0, 0, .stmt srcS, 1), (0, 1, .call S.callSet, 2), (0, 2, .stmt readName, 3),
   (0, 3, .stmt readEmail, 4), (1, 0, .stmt S.setS, 1)]⟩
/-- `sinkAny(y)`: `(y, [], [any], T)`. -/
def sinkY : PFact := ⟨5, [], .any, .conc 1⟩
/-- `sinkAny(z)`: `(z, [], [any], T)`. -/
def sinkZ : PFact := ⟨6, [], .any, .conc 1⟩
def sinks : List (MethodId × Node × PFact) := [(0, 4, sinkY), (0, 4, sinkZ)]

/-- The CFG edge of method 0 at node 0. -/
theorem hE00 : (0, 0, Instr.stmt srcS, 1) ∈ prog.edges := List.Mem.head _
/-- The CFG edge of method 0 at node 1. -/
theorem hE01 : (0, 1, Instr.call S.callSet, 2) ∈ prog.edges := List.Mem.tail _ (List.Mem.head _)
/-- The CFG edge of method 0 at node 2. -/
theorem hE02 : (0, 2, Instr.stmt readName, 3) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
/-- The CFG edge of method 0 at node 3. -/
theorem hE03 : (0, 3, Instr.stmt readEmail, 4) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
/-- The CFG edge of method 1 at node 0. -/
theorem hE10 : (1, 0, Instr.stmt S.setS, 1) ∈ prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
/-- The sink is a sink of the program. -/
theorem hsZ : ((0 : MethodId), (4 : Node), sinkZ) ∈ sinks := List.Mem.tail _ (List.Mem.head _)

/-- The program has no cleaner. -/
theorem no_clean {M n cl n'} (h : (M, n, Instr.clean cl, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h with
          | tail _ h => cases h

/-- The program has no type filter. -/
theorem no_filt {M n b may n'} (h : (M, n, Instr.filt b may, n') ∈ prog.edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h with
      | tail _ h => cases h with
        | tail _ h => cases h with
          | tail _ h => cases h

/-- The result of `z = dto.email`: `(z, [], [any-taint], {}, T)`, NORMAL. -/
def Zz : XFact := ⟨⟨⟨6, [], .any, .conc 1⟩, false⟩, Excl.empty⟩

/-- THE READS (DESIGN A2): on `(dto, [], [any-taint], {name}, T)` the read `dto.name.* → y.*` is
    case `above [name]`; `{name}` does not admit `[name]`, so it gives NO result and no request
    (the base operation on the same fact gives `(y, [], [any-taint], T)`); the statement
    `y = dto.name` keeps only `dto`. The read `dto.email.* → z.*` gives `(z, [], [any-taint], {}, T)`,
    NORMAL (the edge's exclusion: empty). -/
theorem reads :
    bindX S.DTOann readNameE = ResX.none ∧
    (applyEdge S.DTOann.af readNameE.1 readNameE.2).facts = [⟨⟨5, [], .any, .conc 1⟩, false⟩] ∧
    transferX taint cnt 3 readName S.DTOann = ⟨[S.DTOann], []⟩ ∧
    bindX S.DTOann readEmailE = ⟨[Zz], []⟩ ∧
    transferX taint cnt 3 readEmail S.DTOann = ⟨[S.DTOann, Zz], []⟩ := by decide

#print axioms reads

/-! ### Run 1 with the exclusion (`D6X`), completely -/

abbrev R1 : XObj6 → Prop := D6X prog taint cnt 3 policy1 sinks [0]

def edges1 : List (MethodId × PFact × Node × XFact) :=
  [(0, zeroFact, 0, Zx), (0, zeroFact, 1, Zx), (0, zeroFact, 1, DTOx), (0, zeroFact, 2, Zx),
   (0, zeroFact, 2, S.DTOann), (0, zeroFact, 3, Zx), (0, zeroFact, 3, S.DTOann),
   (0, zeroFact, 4, Zx), (0, zeroFact, 4, S.DTOann), (0, zeroFact, 4, Zz),
   (1, S.Jthis, 0, S.JthisX), (1, S.Jthis, 1, S.KEEPx)]
/-- The vulnerabilities: only `sinkAny(z)`, normal. -/
def vulns1 : List (MethodId × Node × PFact × Bool) := [(0, 4, sinkZ, false)]

def Inv1 : XObj6 → Prop
  | .init M i => (M, i) ∈ S.inits1
  | .edge M i n f => (M, i, n, f) ∈ edges1
  | .added M a => (M, a) ∈ S.addeds1
  | .req _ _ _ => False
  | .vuln M n s d => (M, n, s, d) ∈ vulns1

instance : DecidablePred Inv1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ S.inits1))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1))
  | .added M a => inferInstanceAs (Decidable ((M, a) ∈ S.addeds1))
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s d => inferInstanceAs (Decidable ((M, n, s, d) ∈ vulns1))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM R WITH THE EXCLUSION: no fact on `y` at any node; the only
    vulnerability is `sinkAny(z)`, normal. -/
theorem inv1 {o : XObj6} (h : R1 o) : Inv1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ S.inits1,
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
          exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 →
            ∀ f' ∈ (transferX taint cnt 3 readName x.2.2.2).facts, Inv1 (.edge 0 x.2.1 3 f'))
            (0, i, 2, f) ih rfl rfl f' hf
        | tail _ hE => cases hE with
          | head =>
            exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 3 →
              ∀ f' ∈ (transferX taint cnt 3 readEmail x.2.2.2).facts,
                Inv1 (.edge 0 x.2.1 4 f'))
              (0, i, 3, f) ih rfl rfl f' hf
          | tail _ hE => cases hE with
            | head =>
              exact (by decide : ∀ x ∈ edges1, x.1 = 1 → x.2.2.1 = 0 →
                ∀ f' ∈ (transferX taint cnt 3 S.setS x.2.2.2).facts,
                  Inv1 (.edge 1 x.2.1 1 f'))
                (1, i, 0, f) ih rfl rfl f' hf
            | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    have hq : ∀ x ∈ edges1, ∀ s ∈ [srcS, readName, readEmail, S.setS],
        ∀ t ∈ (transferX taint cnt 3 s x.2.2.2).reqs, False := by decide
    cases hE with
    | head => exact hq (0, i, 0, f) ih srcS (List.Mem.head _) t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE with
        | head => exact hq (0, i, 2, f) ih readName (List.Mem.tail _ (List.Mem.head _)) t ht
        | tail _ hE => cases hE with
          | head =>
            exact hq (0, i, 3, f) ih readEmail
              (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) t ht
          | tail _ hE => cases hE with
            | head =>
              exact hq (1, i, 0, f) ih S.setS
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) t ht
            | tail _ hE => cases hE
  | @pass M i n f n' c _ hE hm ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          memB x.2.2.2.af.fact.base S.callSet.touched = false → Inv1 (.edge 0 x.2.1 2 x.2.2.2))
          (0, i, 1, f) ih rfl rfl hm
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | @added M i n f n' c e a _ hE he ha ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 → ∀ e ∈ S.callSet.toCallee,
          ∀ a ∈ (bindX x.2.2.2 e).facts, Inv1 (.added S.callSet.callee a.af.fact))
          (0, i, 1, f) ih rfl rfl e he a ha
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | @initA m a _ ih =>
    exact (by decide : ∀ y ∈ S.addeds1, Inv1 (.init y.1 (policy1 y.1 y.2))) (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ e1 ∈ S.callSet.toCallee, ∀ a ∈ (bindX x.2.2.2 e1).facts,
          ∀ y ∈ S.inits1, y.1 = 1 → applicable y.2 a.af.fact = true →
          ∀ z ∈ edges1, z.1 = 1 → z.2.1 = y.2 → z.2.2.1 = 1 →
          ∀ r ∈ (applySummaryX a y.2 Excl.empty z.2.2.2).facts,
          ∀ e2 ∈ S.callSet.fromCallee, ∀ r' ∈ (bindX r e2).facts,
            Inv1 (.edge 0 x.2.1 2 (limitFX cnt 3 r')))
          (0, i, 1, f) ihf rfl rfl e1 he1 a ha (1, j) ihj rfl hap (1, j, 1, g) ihg rfl rfl rfl
          r hr e2 he2 r' hr'
      | tail _ hE => cases hE with
        | tail _ hE => cases hE with
          | tail _ hE => cases hE with
            | tail _ hE => cases hE
  | @reqSink M i n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges1, ∀ s ∈ [sinkY, sinkZ],
        checkX x.2.1 x.2.2.2 s = .none ∨ checkX x.2.1 x.2.2.2 s = .triggered := by decide
    have hs' : s ∈ [sinkY, sinkZ] := by
      cases hs with
      | head => exact List.Mem.head _
      | tail _ hs => cases hs with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ hs => cases hs
    rcases hnr (M, i, n, f) ih s hs' with h | h
    · rw [h] at hc; exact Check.noConfusion hc
    · rw [h] at hc; exact Check.noConfusion hc
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    have hv : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 4 → ∀ s ∈ [sinkY, sinkZ],
        checkX x.2.1 x.2.2.2 s = .triggered → (0, 4, s, x.2.2.2.af.demand) ∈ vulns1 := by decide
    cases hs with
    | head => exact hv (0, i, 4, f) ih rfl rfl sinkY (List.Mem.head _) hc
    | tail _ hs => cases hs with
      | head => exact hv (0, i, 4, f) ih rfl rfl sinkZ (List.Mem.tail _ (List.Mem.head _)) hc
      | tail _ hs => cases hs
  | clean _ hE _ _ => exact (no_clean hE).elim
  | reqClean _ hE _ _ => exact (no_clean hE).elim
  | filt _ hE _ _ => exact (no_filt hE).elim

#print axioms inv1

/-! ### Run 1: the derivations and the theorems -/

/-- Run 1: the source edge `zero → (b, [], [any-taint], {}, T)`, normal. -/
theorem r1_e01 : R1 (.edge 0 zeroFact 1 DTOx) :=
  D6X.step (D6X.start (D6X.root (List.Mem.head _))) hE00 (by decide)

/-- Run 1: `policy1` serves the added fact of `setName` with `(this, [], *, {}, *)`. -/
theorem r1_i1 : R1 (.init 1 S.Jthis) := by
  have h : R1 (.init 1 (policy1 1 S.Athis)) :=
    D6X.initA (D6X.added (c := S.callSet) (e := S.bThis) (a := S.AthisX) r1_e01 hE01
      (List.Mem.head _) (by decide))
  have hp : policy1 1 S.Athis = S.Jthis := by decide
  rw [hp] at h
  exact h

/-- Run 1: after the setter, `dto` is `(dto, [], [any-taint], {name}, T)`, NORMAL. -/
theorem r1_e02 : R1 (.edge 0 zeroFact 2 S.DTOann) :=
  D6X.ret (c := S.callSet) (e1 := S.bThis) (a := S.AthisX) (j := S.Jthis) (g := S.KEEPx)
    (r := S.THISann) (e2 := S.bBack) (r' := S.DTOann) r1_e01 hE01 (List.Mem.head _) (by decide)
    r1_i1 (by decide) (D6X.step (D6X.start r1_i1) hE10 (by decide)) (by decide) (List.Mem.head _)
    (by decide)

/-- `y = dto.name` GIVES NO FACT FOR `y`: no edge of the complete run 1 has the base `y`. -/
theorem no_y {M : MethodId} {i : PFact} {n : Node} {f : XFact} (h : R1 (.edge M i n f)) :
    f.af.fact.base ≠ 5 :=
  (by decide : ∀ x ∈ edges1, x.2.2.2.af.fact.base ≠ 5) (M, i, n, f) (inv1 h)

#print axioms no_y

/-- `z = dto.email` gives `(z, [], [any-taint], {}, T)`, NORMAL, with the empty exclusion. -/
theorem run1_z : R1 (.edge 0 zeroFact 4 Zz) ∧ Zz.af.demand = false ∧ Zz.ex = Excl.empty :=
  ⟨D6X.step (f' := Zz) (D6X.step (f' := S.DTOann) r1_e02 hE02 (by decide)) hE03 (by decide),
    rfl, rfl⟩

#print axioms run1_z

/-- `sinkAny(y)` IS NOT REPORTED (no vulnerability object, in no layer). -/
theorem y_not_reported (d : Bool) : ¬ R1 (.vuln 0 4 sinkY d) := by
  intro h
  have h' := inv1 h
  cases d <;> exact absurd h' (by decide)

#print axioms y_not_reported

/-- RUN 1 CONFIRMS `sinkAny(z)` (`Confirmed6X`). -/
theorem z_confirmed : Confirmed6X prog taint cnt 3 policy1 sinks [0] 0 4 sinkZ :=
  ⟨zeroFact, Zz, run1_z.1, Sup6X.root (List.Mem.head _), rfl, hsZ, by decide⟩

#print axioms z_confirmed

end R

/-! ## Program CL: the cleaners at `x.f` on `(x, [], [any-taint], T)`

```
root():  x = srcAny();       // 0 -> 1
         clean(x.f, reach);  // 1 -> 2: the cleaner (x, [f], reach, T)
         sink(x.f);          // (x, [f], $, T) at node 2
         sink(x.f.g);        // (x, [f, g], $, T) at node 2
         sink(x.k);          // (x, [k], $, T) at node 2
```
  Bases: zero = 0, x = 1. Accessors: f = 1, g = 2, k = 4. One program for each reach
  (`prog reach`).

  What it shows (DESIGN A2, the cleaners one accessor below the fact; `clean_vectors`):
  * `atAndBelow` at `x.f`: `(x, [], [any-taint], {f}, T)`, NORMAL. `sink(x.f)` and `sink(x.f.g)` are
    not reported; `sink(x.k)` is confirmed (`atAndBelow_result`);
  * `below` at `x.f`: `(x, [], [any-taint], {f}, T)` and the position `(x, [f], $, T)`, both
    NORMAL. `sink(x.f)` is confirmed (the position keeps the mark), `sink(x.f.g)` is not reported,
    `sink(x.k)` is confirmed (`below_result`);
  * `exact` at `x.f`: `(x, [], [any], T)` in the DEMAND layer, no exclusion (the demotion stays:
    there is no shape for "every location but one"). Every sink is a demand entry, nothing is
    confirmed (`exact_result`);
  * the base model gives the demand `(x, [], [any], T)` for all three reaches. -/

namespace CL

/-! ### The program -/

/-- The three reaches. -/
def allReach : List CleanReach := [.exact, .below, .atAndBelow]

/-- Every reach is in `allReach`. -/
theorem mem_allReach (r : CleanReach) : r ∈ allReach := by cases r <;> decide

/-- The cleaner at `x.f` with the reach `r` and the mark `T`. -/
def clAt (r : CleanReach) : Cleaner := ⟨1, [1], r, some 1⟩
/-- Program CL for the reach `r`. -/
def prog (r : CleanReach) : Program :=
  ⟨fun _ => 0, fun _ => 2, [(0, 0, .stmt srcS, 1), (0, 1, .clean (clAt r), 2)]⟩
/-- `sink(x.f)`: `(x, [f], $, T)`. -/
def sF : PFact := ⟨1, [1], .exact, .conc 1⟩
/-- `sink(x.f.g)`: `(x, [f, g], $, T)`. -/
def sFG : PFact := ⟨1, [1, 2], .exact, .conc 1⟩
/-- `sink(x.k)`: `(x, [k], $, T)`. -/
def sK : PFact := ⟨1, [4], .exact, .conc 1⟩
def sinks : List (MethodId × Node × PFact) := [(0, 2, sF), (0, 2, sFG), (0, 2, sK)]

/-- The CFG edge of method 0 at node 0. -/
theorem hE00 (r : CleanReach) : (0, 0, Instr.stmt srcS, 1) ∈ (prog r).edges := List.Mem.head _
/-- The CFG edge of method 0 at node 1. -/
theorem hE01 (r : CleanReach) : (0, 1, Instr.clean (clAt r), 2) ∈ (prog r).edges :=
  List.Mem.tail _ (List.Mem.head _)
/-- The sink is a sink of the program. -/
theorem hsF : ((0 : MethodId), (2 : Node), sF) ∈ sinks := List.Mem.head _
/-- The sink is a sink of the program. -/
theorem hsK : ((0 : MethodId), (2 : Node), sK) ∈ sinks :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- The program has no call. -/
theorem no_call (r : CleanReach) {M n c n'} (h : (M, n, Instr.call c, n') ∈ (prog r).edges) :
    False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

/-- The program has no type filter. -/
theorem no_filt (r : CleanReach) {M n b may n'}
    (h : (M, n, Instr.filt b may, n') ∈ (prog r).edges) : False := by
  cases h with
  | tail _ h => cases h with
    | tail _ h => cases h

/-! ### The facts and the cleaner vectors -/

/-- `(x, [], [any-taint], {f}, T)`, NORMAL. -/
def XF : XFact := ⟨⟨⟨1, [], .any, .conc 1⟩, false⟩, .set [1]⟩
/-- The position `(x, [f], $, T)`, NORMAL (the `below` cleaner cleans only strictly below it). -/
def XFpos : XFact := ⟨⟨⟨1, [1], .exact, .conc 1⟩, false⟩, Excl.empty⟩
/-- `(x, [], [any], T)` in the DEMAND layer, no exclusion. -/
def XDd : XFact := ⟨⟨⟨1, [], .any, .conc 1⟩, true⟩, Excl.empty⟩

/-- The results of the cleaner on `(x, [], [any-taint], {}, T)`, by reach. -/
def results : CleanReach → List XFact
  | .atAndBelow => [XF]
  | .below      => [XF, XFpos]
  | .exact      => [XDd]

/-- THE CLEANERS AT `x.f` (DESIGN A2): on `(x, [], [any-taint], {}, T)`, `atAndBelow` gives
    `E ∪ {f}`, normal; `below` gives `E ∪ {f}` and `(x, [f], $, T)`, normal; `exact` gives the base
    `concPart`: `(x, [], [any], T)`, DEMAND, no exclusion. No request. The base cleaner gives the
    demand `(x, [], [any], T)` for every reach. -/
theorem clean_vectors :
    cleanResX (clAt .atAndBelow) DTOx = ⟨[XF], []⟩ ∧
    cleanResX (clAt .below) DTOx = ⟨[XF, XFpos], []⟩ ∧
    cleanResX (clAt .exact) DTOx = ⟨[XDd], []⟩ ∧
    (∀ r ∈ allReach, cleanResX (clAt r) DTOx = ⟨results r, []⟩) ∧
    (∀ r ∈ allReach, (cleanRes (clAt r) DTO).facts = [DTOd]) := by decide

#print axioms clean_vectors

/-! ### Run 1 with the exclusion (`D6X`), completely, for each reach -/

abbrev R1 (r : CleanReach) : XObj6 → Prop := D6X (prog r) taint cnt 3 policy1 sinks [0]

def edgesOf (r : CleanReach) : List (MethodId × PFact × Node × XFact) :=
  [(0, zeroFact, 0, Zx), (0, zeroFact, 1, Zx), (0, zeroFact, 1, DTOx), (0, zeroFact, 2, Zx)] ++
  (results r).map (fun f => (0, zeroFact, 2, f))

/-- The vulnerabilities of run 1, by reach. -/
def vulnsOf : CleanReach → List (MethodId × Node × PFact × Bool)
  | .atAndBelow => [(0, 2, sK, false)]
  | .below      => [(0, 2, sF, false), (0, 2, sK, false)]
  | .exact      => [(0, 2, sF, true), (0, 2, sFG, true), (0, 2, sK, true)]

def Inv (r : CleanReach) : XObj6 → Prop
  | .init M i => (M, i) ∈ [((0 : MethodId), zeroFact)]
  | .edge M i n f => (M, i, n, f) ∈ edgesOf r
  | .added _ _ => False
  | .req _ _ _ => False
  | .vuln M n s d => (M, n, s, d) ∈ vulnsOf r

instance (r : CleanReach) : DecidablePred (Inv r) := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ [((0 : MethodId), zeroFact)]))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edgesOf r))
  | .added _ _ => inferInstanceAs (Decidable False)
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s d => inferInstanceAs (Decidable ((M, n, s, d) ∈ vulnsOf r))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM CL, for each reach: the sink edges are the zero edge and the
    cleaner results `results r`; no request; the vulnerabilities are `vulnsOf r`. -/
theorem inv (r : CleanReach) {o : XObj6} (h : R1 r o) : Inv r o := by
  have hr := mem_allReach r
  induction h with
  | @root M hM =>
    cases hM with
    | head => exact (by decide : ∀ r ∈ allReach, Inv r (.init 0 zeroFact)) r hr
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ r ∈ allReach, ∀ x ∈ [((0 : MethodId), zeroFact)],
      Inv r (.edge x.1 x.2 ((prog r).entry x.1) (startX x.2 false Excl.empty))) r hr (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ r ∈ allReach, ∀ x ∈ edgesOf r, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferX taint cnt 3 srcS x.2.2.2).facts, Inv r (.edge 0 x.2.1 1 f'))
        r hr (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ r ∈ allReach, ∀ x ∈ edgesOf r,
        ∀ t ∈ (transferX taint cnt 3 srcS x.2.2.2).reqs, False) r hr (0, i, 0, f) ih t ht
    | tail _ hE => cases hE with
      | tail _ hE => cases hE
  | pass _ hE _ _ => exact (no_call r hE).elim
  | added _ hE _ _ _ => exact (no_call r hE).elim
  | initA _ ih => exact ih.elim
  | ret _ hE _ _ _ _ _ _ _ _ _ _ _ => exact (no_call r hE).elim
  | @reqSink M i n f s t _ hs hc ih =>
    have hnr : ∀ r ∈ allReach, ∀ x ∈ edgesOf r, ∀ s ∈ [sF, sFG, sK],
        checkX x.2.1 x.2.2.2 s = .none ∨ checkX x.2.1 x.2.2.2 s = .triggered := by decide
    have hs' : s ∈ [sF, sFG, sK] := by
      cases hs with
      | head => exact List.Mem.head _
      | tail _ hs => cases hs with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ hs => cases hs with
          | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
          | tail _ hs => cases hs
    rcases hnr r hr (M, i, n, f) ih s hs' with h | h
    · rw [h] at hc; exact Check.noConfusion hc
    · rw [h] at hc; exact Check.noConfusion hc
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    have hv : ∀ r ∈ allReach, ∀ x ∈ edgesOf r, x.1 = 0 → x.2.2.1 = 2 → ∀ s ∈ [sF, sFG, sK],
        checkX x.2.1 x.2.2.2 s = .triggered → (0, 2, s, x.2.2.2.af.demand) ∈ vulnsOf r := by
      decide
    cases hs with
    | head => exact hv r hr (0, i, 2, f) ih rfl rfl sF (List.Mem.head _) hc
    | tail _ hs => cases hs with
      | head => exact hv r hr (0, i, 2, f) ih rfl rfl sFG (List.Mem.tail _ (List.Mem.head _)) hc
      | tail _ hs => cases hs with
        | head =>
          exact hv r hr (0, i, 2, f) ih rfl rfl sK
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) hc
        | tail _ hs => cases hs
  | @clean M i n f n' cl f' _ hE hf ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ r ∈ allReach, ∀ x ∈ edgesOf r, x.1 = 0 → x.2.2.1 = 1 →
          ∀ f' ∈ (cleanResX (clAt r) x.2.2.2).facts, Inv r (.edge 0 x.2.1 2 f'))
          r hr (0, i, 1, f) ih rfl rfl f' hf
      | tail _ hE => cases hE
  | @reqClean M i n f n' cl t _ hE ht ih =>
    cases hE with
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ r ∈ allReach, ∀ x ∈ edgesOf r,
          ∀ t ∈ (cleanResX (clAt r) x.2.2.2).reqs, False) r hr (0, i, 1, f) ih t ht
      | tail _ hE => cases hE
  | filt _ hE _ _ => exact (no_filt r hE).elim

#print axioms inv

/-! ### Run 1: the theorems -/

/-- Run 1: the source edge `zero → (b, [], [any-taint], {}, T)`, normal. -/
theorem r1_e01 (r : CleanReach) : R1 r (.edge 0 zeroFact 1 DTOx) :=
  D6X.step (D6X.start (D6X.root (List.Mem.head _))) (hE00 r) (by decide)

/-- THE `atAndBelow` CLEANER AT `x.f`: run 1 derives `(x, [], [any-taint], {f}, T)`, NORMAL;
    `sink(x.f)` and `sink(x.f.g)` are not reported (no vulnerability object); `sink(x.k)` is
    confirmed. -/
theorem atAndBelow_result :
    R1 .atAndBelow (.edge 0 zeroFact 2 XF) ∧ XF.af.demand = false ∧ XF.ex = .set [1] ∧
    (∀ d, ¬ R1 .atAndBelow (.vuln 0 2 sF d)) ∧ (∀ d, ¬ R1 .atAndBelow (.vuln 0 2 sFG d)) ∧
    Confirmed6X (prog .atAndBelow) taint cnt 3 policy1 sinks [0] 0 2 sK := by
  have he : R1 .atAndBelow (.edge 0 zeroFact 2 XF) :=
    D6X.clean (r1_e01 .atAndBelow) (hE01 .atAndBelow) (by decide)
  refine ⟨he, rfl, rfl, fun d h => ?_, fun d h => ?_,
    ⟨zeroFact, XF, he, Sup6X.root (List.Mem.head _), rfl, hsK, by decide⟩⟩
  · have h' := inv _ h
    cases d <;> exact absurd h' (by decide)
  · have h' := inv _ h
    cases d <;> exact absurd h' (by decide)

#print axioms atAndBelow_result

/-- THE `below` CLEANER AT `x.f`: run 1 derives `(x, [], [any-taint], {f}, T)` and the position
    `(x, [f], $, T)`, both NORMAL; `sink(x.f)` is confirmed (by the position), `sink(x.f.g)` is not
    reported, `sink(x.k)` is confirmed. -/
theorem below_result :
    R1 .below (.edge 0 zeroFact 2 XF) ∧ R1 .below (.edge 0 zeroFact 2 XFpos) ∧
    Confirmed6X (prog .below) taint cnt 3 policy1 sinks [0] 0 2 sF ∧
    (∀ d, ¬ R1 .below (.vuln 0 2 sFG d)) ∧
    Confirmed6X (prog .below) taint cnt 3 policy1 sinks [0] 0 2 sK := by
  have he : R1 .below (.edge 0 zeroFact 2 XF) :=
    D6X.clean (r1_e01 .below) (hE01 .below) (by decide)
  have hp : R1 .below (.edge 0 zeroFact 2 XFpos) :=
    D6X.clean (r1_e01 .below) (hE01 .below) (by decide)
  refine ⟨he, hp, ⟨zeroFact, XFpos, hp, Sup6X.root (List.Mem.head _), rfl, hsF, by decide⟩,
    fun d h => ?_, ⟨zeroFact, XF, he, Sup6X.root (List.Mem.head _), rfl, hsK, by decide⟩⟩
  have h' := inv _ h
  cases d <;> exact absurd h' (by decide)

#print axioms below_result

/-- THE `exact` CLEANER AT `x.f`: the demotion stays. Run 1 derives `(x, [], [any], T)` in the
    DEMAND layer with no exclusion; there is no normal report, so nothing is confirmed (each sink
    is a demand entry). -/
theorem exact_result :
    R1 .exact (.edge 0 zeroFact 2 XDd) ∧ XDd.af.demand = true ∧ XDd.ex = Excl.empty ∧
    (∀ s, ¬ R1 .exact (.vuln 0 2 s false)) ∧
    R1 .exact (.vuln 0 2 sF true) ∧ R1 .exact (.vuln 0 2 sK true) ∧
    ¬ Confirmed6X (prog .exact) taint cnt 3 policy1 sinks [0] 0 2 sK := by
  have he : R1 .exact (.edge 0 zeroFact 2 XDd) :=
    D6X.clean (r1_e01 .exact) (hE01 .exact) (by decide)
  have hn : ∀ s, ¬ R1 .exact (.vuln 0 2 s false) := by
    intro s h
    have h' : (0, 2, s, false) ∈ vulnsOf .exact := inv _ h
    exact absurd h' (by
      intro hm
      cases hm with
      | tail _ hm => cases hm with
        | tail _ hm => cases hm with
          | tail _ hm => cases hm)
  refine ⟨he, rfl, rfl, hn, D6X.vuln he hsF (by decide), D6X.vuln he hsK (by decide), ?_⟩
  rintro ⟨i, f, hf, _, hd, hs, hc⟩
  have hv := D6X.vuln hf hs hc
  rw [hd] at hv
  exact hn _ hv

#print axioms exact_result

end CL

/-! ## Program CUT: the field limit on an annotated fact

  Program `X` with the field limit 0 (`D6X X.prog taint cnt 0 …`). The statement `x.f.g = c`
  first gives the two annotated results of `X` (`X.two_results`); the field limit then cuts
  `(x, [f], [any-taint], {g}, T)` (one counted accessor, over the limit 0) to the base cut fact
  `(x, [], [any], T)` in the DEMAND layer and DROPS the exclusion (DESIGN A2: "the field limit cut
  still demotes to `[any]`, the exclusion is dropped"; `cut_ops`). `(x, [], [any-taint], {f}, T)` has
  no accessor and stays (`run1_cut`). So `sink(x.f.h)`, confirmed with the limit 3
  (`X.fh_confirmed`), is a demand entry only, and `sink(x.f.g)` becomes a demand entry
  (`cut_reports`, the complete run `inv1`). -/

namespace CUT

/-- Run 1 of program X with the field limit 0. -/
abbrev R1 : XObj6 → Prop := D6X X.prog taint cnt 0 policy1 X.sinks [0]

/-- The cut fact `(x, [], [any], T)`, DEMAND, no exclusion. -/
def CUTd : XFact := ⟨⟨⟨1, [], .any, .conc 1⟩, true⟩, Excl.empty⟩

/-- THE CUT (DESIGN A2, ap.md §4.4): before the field limit, the statement gives the annotated
    `(x, [f], [any-taint], {g}, T)`; its path `[f]` is over the limit 0 (`cutPath`); `limitFX` gives
    `(x, [], [any], T)` in the DEMAND layer with the EMPTY exclusion; the fact with no accessor
    stays; the statement transfer gives exactly the two facts. -/
theorem cut_ops :
    (applyAllXT taint DTOx X.wrS.edges).facts = [X.XF, X.XFG] ∧
    cutPath cnt 0 X.XFG.af.fact.path = some [] ∧
    limitFX cnt 0 X.XFG = CUTd ∧ CUTd.af.demand = true ∧ CUTd.ex = Excl.empty ∧
    limitFX cnt 0 X.XF = X.XF ∧
    transferX taint cnt 0 X.wrS DTOx = ⟨[X.XF, CUTd], []⟩ := by decide

#print axioms cut_ops

def edges1 : List (MethodId × PFact × Node × XFact) :=
  [(0, zeroFact, 0, Zx), (0, zeroFact, 1, Zx), (0, zeroFact, 1, DTOx), (0, zeroFact, 2, Zx),
   (0, zeroFact, 2, X.XF), (0, zeroFact, 2, CUTd)]
/-- The vulnerabilities with the limit 0: `sink(x.f.g)` and `sink(x.f.h)` in the demand layer only,
    `sink(x.k)` in both layers. -/
def vulns1 : List (MethodId × Node × PFact × Bool) :=
  [(0, 2, X.sFG, true), (0, 2, X.sFH, true), (0, 2, X.sK, false), (0, 2, X.sK, true)]

def Inv1 : XObj6 → Prop
  | .init M i => (M, i) ∈ [((0 : MethodId), zeroFact)]
  | .edge M i n f => (M, i, n, f) ∈ edges1
  | .added _ _ => False
  | .req _ _ _ => False
  | .vuln M n s d => (M, n, s, d) ∈ vulns1

instance : DecidablePred Inv1 := fun o =>
  match o with
  | .init M i => inferInstanceAs (Decidable ((M, i) ∈ [((0 : MethodId), zeroFact)]))
  | .edge M i n f => inferInstanceAs (Decidable ((M, i, n, f) ∈ edges1))
  | .added _ _ => inferInstanceAs (Decidable False)
  | .req _ _ _ => inferInstanceAs (Decidable False)
  | .vuln M n s d => inferInstanceAs (Decidable ((M, n, s, d) ∈ vulns1))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- THE COMPLETE RUN 1 OF PROGRAM X WITH THE FIELD LIMIT 0. -/
theorem inv1 {o : XObj6} (h : R1 o) : Inv1 o := by
  induction h with
  | @root M hM =>
    cases hM with
    | head => decide
    | tail _ h => cases h
  | @start M i _ ih =>
    exact (by decide : ∀ x ∈ [((0 : MethodId), zeroFact)],
      Inv1 (.edge x.1 x.2 (X.prog.entry x.1) (startX x.2 false Excl.empty))) (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    cases hE with
    | head =>
      exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 0 →
        ∀ f' ∈ (transferX taint cnt 0 srcS x.2.2.2).facts, Inv1 (.edge 0 x.2.1 1 f'))
        (0, i, 0, f) ih rfl rfl f' hf
    | tail _ hE => cases hE with
      | head =>
        exact (by decide : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 1 →
          ∀ f' ∈ (transferX taint cnt 0 X.wrS x.2.2.2).facts, Inv1 (.edge 0 x.2.1 2 f'))
          (0, i, 1, f) ih rfl rfl f' hf
      | tail _ hE => cases hE
  | @reqStmt M i n f n' s t _ hE ht ih =>
    have hq : ∀ x ∈ edges1, ∀ s ∈ [srcS, X.wrS], ∀ t ∈ (transferX taint cnt 0 s x.2.2.2).reqs,
        False := by decide
    cases hE with
    | head => exact hq (0, i, 0, f) ih srcS (List.Mem.head _) t ht
    | tail _ hE => cases hE with
      | head => exact hq (0, i, 1, f) ih X.wrS (List.Mem.tail _ (List.Mem.head _)) t ht
      | tail _ hE => cases hE
  | pass _ hE _ _ => exact (X.no_call hE).elim
  | added _ hE _ _ _ => exact (X.no_call hE).elim
  | initA _ ih => exact ih.elim
  | ret _ hE _ _ _ _ _ _ _ _ _ _ _ => exact (X.no_call hE).elim
  | @reqSink M i n f s t _ hs hc ih =>
    have hnr : ∀ x ∈ edges1, ∀ s ∈ [X.sFG, X.sFH, X.sK],
        checkX x.2.1 x.2.2.2 s = .none ∨ checkX x.2.1 x.2.2.2 s = .triggered := by decide
    have hs' : s ∈ [X.sFG, X.sFH, X.sK] := by
      cases hs with
      | head => exact List.Mem.head _
      | tail _ hs => cases hs with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ hs => cases hs with
          | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
          | tail _ hs => cases hs
    rcases hnr (M, i, n, f) ih s hs' with h | h
    · rw [h] at hc; exact Check.noConfusion hc
    · rw [h] at hc; exact Check.noConfusion hc
  | answer _ _ _ _ ih => exact ih.elim
  | reqUp _ _ _ _ _ _ _ _ ih => exact ih.elim
  | @vuln M i n f s _ hs hc ih =>
    have hv : ∀ x ∈ edges1, x.1 = 0 → x.2.2.1 = 2 → ∀ s ∈ [X.sFG, X.sFH, X.sK],
        checkX x.2.1 x.2.2.2 s = .triggered → (0, 2, s, x.2.2.2.af.demand) ∈ vulns1 := by decide
    cases hs with
    | head => exact hv (0, i, 2, f) ih rfl rfl X.sFG (List.Mem.head _) hc
    | tail _ hs => cases hs with
      | head => exact hv (0, i, 2, f) ih rfl rfl X.sFH (List.Mem.tail _ (List.Mem.head _)) hc
      | tail _ hs => cases hs with
        | head =>
          exact hv (0, i, 2, f) ih rfl rfl X.sK
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) hc
        | tail _ hs => cases hs
  | clean _ hE _ _ => exact (X.no_clean hE).elim
  | reqClean _ hE _ _ => exact (X.no_clean hE).elim
  | filt _ hE _ _ => exact (X.no_filt hE).elim

#print axioms inv1

/-- Run 1 (limit 0): the source edge `zero → (x, [], [any-taint], {}, T)`, normal. -/
theorem r1_e01 : R1 (.edge 0 zeroFact 1 DTOx) :=
  D6X.step (D6X.start (D6X.root (List.Mem.head _))) X.hE00 (by decide)

/-- With the limit 0, run 1 derives the cut fact `(x, [], [any], T)` (DEMAND, no exclusion) and the
    fact `(x, [], [any-taint], {f}, T)` (normal) at the sink node. -/
theorem run1_cut : R1 (.edge 0 zeroFact 2 CUTd) ∧ R1 (.edge 0 zeroFact 2 X.XF) :=
  ⟨D6X.step r1_e01 X.hE01 (by decide), D6X.step r1_e01 X.hE01 (by decide)⟩

#print axioms run1_cut

/-- THE CUT LOSES PRECISION: with the limit 0, `sink(x.f.g)` and `sink(x.f.h)` are demand entries
    (the cut fact covers them); only `sink(x.k)` has a normal report; `sink(x.f.h)`, confirmed with
    the limit 3 (`X.fh_confirmed`), is not confirmed. -/
theorem cut_reports :
    R1 (.vuln 0 2 X.sFG true) ∧ R1 (.vuln 0 2 X.sFH true) ∧
    (∀ s, R1 (.vuln 0 2 s false) → s = X.sK) ∧
    ¬ Confirmed6X X.prog taint cnt 0 policy1 X.sinks [0] 0 2 X.sFH := by
  have hn : ∀ s, R1 (.vuln 0 2 s false) → s = X.sK := fun s h =>
    (by decide : ∀ x ∈ vulns1, x.2.2.2 = false → x.2.2.1 = X.sK) (0, 2, s, false) (inv1 h) rfl
  refine ⟨D6X.vuln run1_cut.1 (List.Mem.head _) (by decide),
    D6X.vuln run1_cut.1 X.hsFH (by decide), hn, ?_⟩
  rintro ⟨i, f, hf, _, hd, hs, hc⟩
  have hv := D6X.vuln hf hs hc
  rw [hd] at hv
  exact absurd (hn _ hv) (by decide)

#print axioms cut_reports

end CUT

/-! ## Summary

  THE THEOREMS (each with `#print axioms`; only `propext`, `Quot.sound`, or none).
  * `S` (the setter):
    - `S.inv1`: the complete run 1 of `D6X` (no request; the only vulnerability is the email sink,
      normal);
    - `S.record_app`: the record `(this, [], *, *) → (this, [], */{name}, *)` on the `[any-taint]`
      added fact is a `keep` row: `(this, [], [any-taint], {name}, T)` NORMAL (the base gives it in
      the demand layer), bound back to `(dto, [], [any-taint], {name}, T)`;
      `S.keep_forms`: the exclusion on the premise or on the target of the keep edge gives the same;
    - `S.run1_record`: the run-1 record of `setName`, normal and complete;
    - `S.run1_dto_ann`: `zero → (dto, [], [any-taint], {name}, T)` at the sink node, NORMAL;
    - `S.run1_name_no_trigger`, `S.run1_name_not_reported`: no sink edge triggers `sink(dto.name)`
      (the base check on the same fact does); no vulnerability object for it, in no layer;
    - `S.run1_email_normal`, `S.run1_email_confirmed`: `sink(dto.email)` is reported normal and
      `Confirmed6X` holds; `S.run1_no_demand`: no demand-layer report;
    - contrast (`AnyTaint.D6T`): `S.inv1T`, `S.run1T_vulns` (both sinks in the demand layer),
      `S.run1T_no_normal`, `S.run1T_not_confirmed`; `S.refines_dto` (`Refines6` of the refined
      normal edge to the base demand edge);
    - `S.name_not_real` (`dto.name` is not reached: the non-report loses nothing), `S.email_real`.
  * `SD` (the deep setter): `SD.inv1`; `SD.run1_deep_record` (`(this', [], *) →
    (this', [], */{name}, *)`, normal, complete); `SD.run1_dto_ann`; `SD.run1_name_not_reported`;
    `SD.run1_email_confirmed`; `SD.same_result` (the sink edges and the vulnerabilities of `root`
    are those of `S`).
  * `B` (the broad demand): run 1: `B.inv1`, `B.run1_d_ann`, `B.run1_e_ann`,
    `B.run1_name_not_reported`, `B.run1_anyE_confirmed`, `B.recs1_complete`; run 3 (`DRXs`, the
    demand `dBroad` by hand): `B.inv3` (for every demand with only `dBroad` and every record set
    inside `recs1`), `B.must_summary_ops`, `B.run3_must` (the must-premise
    `(this, [], [any-taint], {}, T)`), `B.run3_summary` (`(this, [], [any-taint]) →
    (this, [], [any-taint], {name}, T)`, NORMAL), `B.run3_d_ann`, `B.run3_e_ann`,
    `B.run3_name_not_reported`, `B.run3_anyE_confirmed` (`ConfirmedX`), `B.run3_with_records`.
  * `X` (the two-level write): `X.two_results` (exactly `(x, [], [any-taint], {f}, T)` and
    `(x, [f], [any-taint], {g}, T)`, both NORMAL; the base: both demand), `X.locations_exact` (they
    cover exactly the locations not below `x.f.g`), `X.inv1`, `X.run1_results`,
    `X.fg_not_reported`, `X.fh_confirmed`, `X.k_confirmed`, `X.run1_no_demand`.
  * `R` (the reads): `R.reads` (the read through `name ∈ E` gives nothing; through `email`:
    `(z, [], [any-taint], {}, T)`, normal), `R.inv1`, `R.no_y`, `R.run1_z`, `R.y_not_reported`,
    `R.z_confirmed`.
  * `CL` (the cleaners): `CL.clean_vectors`, `CL.inv` (for each reach), `CL.atAndBelow_result`,
    `CL.below_result`, `CL.exact_result`.
  * `CUT` (the field limit): `CUT.cut_ops`, `CUT.inv1`, `CUT.run1_cut`, `CUT.cut_reports`.

  FINDINGS (CEGAR). Every program behaves as the brief says; no program was changed to pass.
  * Build state: the built `AnyTaintCases.olean` is older than `AnyTaintCases.lean`: it has the
    programs G, C, W, P and the cut, but NOT the appended programs I and S. So this file does not
    import `AnyTaintCases`: it defines program S again (the same terms) and re-derives the facts of
    `AnyTaintCases.S` that it needs (`inv1T`, `run1T_vulns`, `run1T_no_normal`, `name_not_real`,
    `email_real`).
  * The refined run REMOVES reports, not only layers: in `S`, `SD`, `B`, `X`, `R`, `CL` a sink in the
    excluded part has no vulnerability object in `D6X`/`DRXs`, where the base run has a demand
    entry (proved for `S`: `S.run1T_vulns`; for the others the base operation gives a fact that
    covers the sink: `X.two_results`, `R.reads`, `CL.clean_vectors`, `S.run1_name_no_trigger`).
    This agrees with the direction of `Sim6X` (a refined object has a base
    object), but the coverage of the refined runs (every real vulnerability is reported) does not
    follow from `Sim6X` and the base coverage: it needs the location reading of `E`. The programs
    check it case by case: the removed reports are not real (`S.name_not_real`;
    `X.locations_exact`).
  * `SD`: the exclusion travels through a `*`-tail record: `setNameDeep` has no `[any-taint]` in
    run 1 (its record is `(this', [], */{name}, *)`); only the application in `root` makes
    `[any-taint]/{name}`.
  * `B`: the broad demand does not bring a report of `sink(d.name)` back: the must-premise summary
    and the run-1 record give the same sink fact `(d, [], [any-taint], {name}, T)`.
  * `CL`, `exact` reach: every sink is a demand entry, also `sink(x.f)`, which is not real (the
    accepted precision loss: no shape for "every location but one").
  * `CUT`: the cut is the one rule of these programs that drops an exclusion: with the limit 0,
    `sink(x.f.h)` (confirmed with the limit 3, `X.fh_confirmed`) is a demand entry only.
  * Hypotheses: `B.inv3` (and so `B.run3_name_not_reported`) holds for every demand that has only
    `dBroad` and every record set inside the run-1 records `recs1` (`B.recs1_complete`: every
    complete exit edge of run 1 is in it). No other hypothesis. -/

end ApSpec.AnyTaintExCases
