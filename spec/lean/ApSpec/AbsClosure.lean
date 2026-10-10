/-
  ApSpec.AbsClosure — finite closure invariants for the CEGAR programs of F72 (`AbsCases.lean`).

  A finite state `LS` (lists of initial facts, edges, added facts, requests, vulnerabilities) is
  CLOSED under the rules of a closure if every rule with premises in the state has its conclusion
  in the state. The closedness test is decidable (`decide` computes it), and a closed state bounds
  the closure (the closure is the LEAST set closed under the rules):
    * `closedD_sound`  for run 1, `D … policy1 …` (with the request rules);
    * `closedRA_sound` for the forward restricted run `DRA` (no request rule), every emission,
      satisfaction and restriction, a demand and records given as lists;
    * `closedBA_sound` for the backward restricted run `DBA` (no request rule, the zero rules of the
      user's design), the same parameters and the seeds.
  So each complete closure of `AbsCases.lean` is ONE `decide` (the state comes from an executable
  simulation; the proof does not trust it, the kernel checks the closedness).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.AbsDefs

namespace ApSpec.Abs
open ApSpec ApSpec.Reverse ApSpec.Handoff

set_option synthInstance.maxSize 65536
set_option synthInstance.maxHeartbeats 4000000

/-- A finite state of a closure. -/
structure LS where
  inits  : List (MethodId × PFact)
  edges  : List (MethodId × PFact × Node × AFact)
  addeds : List (MethodId × PFact)
  reqs   : List (MethodId × PFact × Mark)
  vulns  : List (MethodId × Node × PFact × Bool)

/-- The objects of a finite state. -/
def LS.Inv (S : LS) : Obj → Prop
  | .init M i => (M, i) ∈ S.inits
  | .edge M i n f => (M, i, n, f) ∈ S.edges
  | .added M a => (M, a) ∈ S.addeds
  | .req M i t => (M, i, t) ∈ S.reqs
  | .vuln M n s b => (M, n, s, b) ∈ S.vulns

abbrev EdgeT := MethodId × PFact × Node × AFact

/-- The demand edges of a method `m` in a demand list, with the zero demand (it is accepted in every
    method). -/
def demFor (demL : List (MethodId × DemandEdge)) (m : MethodId) : List DemandEdge :=
  Backward.zeroDem :: demL.filterMap (fun x => if x.1 = m then some x.2 else none)

theorem mem_demFor {demL : List (MethodId × DemandEdge)} {m : MethodId} {d : DemandEdge}
    (h : (m, d) ∈ demL) : d ∈ demFor demL m := by
  apply List.mem_cons_of_mem
  apply List.mem_filterMap.mpr
  exact ⟨(m, d), h, by rw [if_pos rfl]⟩

theorem zero_mem_demFor (demL : List (MethodId × DemandEdge)) (m : MethodId) :
    Backward.zeroDem ∈ demFor demL m := List.mem_cons_self

#print axioms mem_demFor
#print axioms zero_mem_demFor

/-! ## 1. Run 1 (`D` with `policy1`, the request rules) -/

section D1
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) (S : LS)

/-- The rules of one instruction at the edge `x`, for run 1. -/
def InstrD (x : EdgeT) (n' : Node) : Instr → Prop
  | .stmt s => (∀ f' ∈ (transfer counted L s x.2.2.2).facts, (x.1, x.2.1, n', f') ∈ S.edges) ∧
      (∀ t ∈ (transfer counted L s x.2.2.2).reqs, (x.1, x.2.1, t) ∈ S.reqs)
  | .call c => (memB x.2.2.2.fact.base c.touched = false → (x.1, x.2.1, n', x.2.2.2) ∈ S.edges) ∧
      ∀ e ∈ c.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
        (c.callee, a.fact) ∈ S.addeds ∧
        (∀ y ∈ S.inits, y.1 = c.callee → applicable y.2 a.fact = true →
          ∀ z ∈ S.edges, z.1 = c.callee → z.2.1 = y.2 → z.2.2.1 = P.exit c.callee →
          ∀ r ∈ (applySummary a y.2 z.2.2.2).facts, ∀ e2 ∈ c.fromCallee,
          ∀ r' ∈ (applyEdge r e2.1 e2.2).facts, (x.1, x.2.1, n', limitF counted L r') ∈ S.edges) ∧
        (∀ q ∈ S.reqs, q.1 = c.callee → climbsB a.fact.mark q.2.2 = true →
          overlapB a.fact q.2.1 = true → (x.1, x.2.1, q.2.2) ∈ S.reqs)
  | .clean cl => (∀ f' ∈ (cleanRes cl x.2.2.2).facts, (x.1, x.2.1, n', f') ∈ S.edges) ∧
      (∀ t ∈ (cleanRes cl x.2.2.2).reqs, (x.1, x.2.1, t) ∈ S.reqs)
  | .filt b may => (x.2.2.2.fact.base = b → may x.2.2.2.fact.path = true) →
      (x.1, x.2.1, n', x.2.2.2) ∈ S.edges

instance instDecInstrD (x : EdgeT) (n' : Node) : (ins : Instr) → Decidable (InstrD P counted L S x n' ins)
  | .stmt _ => by dsimp only [InstrD]; exact inferInstance
  | .call _ => by dsimp only [InstrD]; exact inferInstance
  | .clean _ => by dsimp only [InstrD]; exact inferInstance
  | .filt _ _ => by dsimp only [InstrD]; exact inferInstance

/-- The sink rules of run 1 for a check result. -/
def CheckD (x : EdgeT) (s : PFact) : Check → Prop
  | .triggered => (x.1, x.2.2.1, s, x.2.2.2.demand) ∈ S.vulns
  | .request t => (x.1, x.2.1, t) ∈ S.reqs
  | .none => True

instance instDecCheckD (x : EdgeT) (s : PFact) : (c : Check) → Decidable (CheckD S x s c)
  | .triggered => by dsimp only [CheckD]; exact inferInstance
  | .request _ => by dsimp only [CheckD]; exact inferInstance
  | .none => by dsimp only [CheckD]; exact inferInstance

/-- THE STATE IS CLOSED UNDER THE RULES OF RUN 1. -/
def ClosedD : Prop :=
  (∀ M ∈ roots, (M, zeroFact) ∈ S.inits) ∧
  (∀ y ∈ S.inits, (y.1, y.2, P.entry y.1, startFact y.2) ∈ S.edges) ∧
  (∀ x ∈ S.edges, ∀ pe ∈ P.edges, pe.1 = x.1 → pe.2.1 = x.2.2.1 →
    InstrD P counted L S x pe.2.2.2 pe.2.2.1) ∧
  (∀ x ∈ S.edges, ∀ sk ∈ sinks, sk.1 = x.1 → sk.2.1 = x.2.2.1 →
    CheckD S x sk.2.2 (check x.2.1 x.2.2.2 sk.2.2)) ∧
  (∀ y ∈ S.addeds, (y.1, policy1 y.1 y.2) ∈ S.inits) ∧
  (∀ q ∈ S.reqs, ∀ y ∈ S.addeds, y.1 = q.1 → y.2.mark = .conc q.2.2 → overlapB y.2 q.2.1 = true →
    (q.1, answerInit q.2.1 y.2 q.2.2) ∈ S.inits)

instance instDecClosedD : Decidable (ClosedD P counted L sinks roots S) := by
  unfold ClosedD; exact inferInstance

/-- A CLOSED STATE BOUNDS RUN 1. -/
theorem closedD_sound (hC : ClosedD P counted L sinks roots S) {o : Obj}
    (h : D P counted L policy1 sinks roots o) : S.Inv o := by
  obtain ⟨hroot, hstart, hinstr, hsink, hinit, hans⟩ := hC
  induction h with
  | root hM => exact hroot _ hM
  | @start M i _ ih => exact hstart (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    exact (hinstr (M, i, n, f) ih (M, n, .stmt s, n') hE rfl rfl).1 f' hf
  | @reqStmt M i n f n' s t _ hE ht ih =>
    exact (hinstr (M, i, n, f) ih (M, n, .stmt s, n') hE rfl rfl).2 t ht
  | @pass M i n f n' c _ hE hm ih =>
    exact (hinstr (M, i, n, f) ih (M, n, .call c, n') hE rfl rfl).1 hm
  | @added M i n f n' c e a _ hE he ha ih =>
    exact ((hinstr (M, i, n, f) ih (M, n, .call c, n') hE rfl rfl).2 e he a ha).1
  | @initA m a _ ih => exact hinit (m, a) ih
  | @ret M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    exact ((hinstr (M, i, n, f) ihf (M, n, .call c, n') hE rfl rfl).2 e1 he1 a ha).2.1
      (c.callee, j) ihj rfl hap (c.callee, j, P.exit c.callee, g) ihg rfl rfl rfl r hr e2 he2 r' hr'
  | @reqSink M i n f s t _ hs hc ih =>
    have h := hsink (M, i, n, f) ih (M, n, s) hs rfl rfl
    rw [hc] at h
    exact h
  | @answer M i t a _ _ ham hov ihq iha => exact hans (M, i, t) ihq (M, a) iha rfl ham hov
  | @reqUp m j t M ic n f n' c e a _ _ hE hcm he ha hcl hov ihq ihf =>
    subst hcm
    exact ((hinstr (M, ic, n, f) ihf (M, n, .call c, n') hE rfl rfl).2 e he a ha).2.2
      (c.callee, j, t) ihq rfl hcl hov
  | @vuln M i n f s _ hs hc ih =>
    have h := hsink (M, i, n, f) ih (M, n, s) hs rfl rfl
    rw [hc] at h
    exact h
  | @clean M i n f n' cl f' _ hE hf ih =>
    exact (hinstr (M, i, n, f) ih (M, n, .clean cl, n') hE rfl rfl).1 f' hf
  | @reqClean M i n f n' cl t _ hE ht ih =>
    exact (hinstr (M, i, n, f) ih (M, n, .clean cl, n') hE rfl rfl).2 t ht
  | @filt M i n f n' b may _ hE hl ih =>
    exact hinstr (M, i, n, f) ih (M, n, .filt b may, n') hE rfl rfl hl

end D1

#print axioms closedD_sound

/-! ## 2. The forward restricted run `DRA` -/

section RA
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demL : List (MethodId × DemandEdge))
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recL : List (MethodId × (PFact × AFact)))
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) (S : LS)

/-- The rules of one instruction at the edge `x`, for `DRA`. -/
def InstrRA (x : EdgeT) (n' : Node) : Instr → Prop
  | .stmt s => ∀ f' ∈ (transfer counted L s x.2.2.2).facts, (x.1, x.2.1, n', f') ∈ S.edges
  | .call c => (memB x.2.2.2.fact.base c.touched = false → (x.1, x.2.1, n', x.2.2.2) ∈ S.edges) ∧
      ∀ e ∈ c.toCallee, ∀ a ∈ (applyEdge x.2.2.2 e.1 e.2).facts,
        (c.callee, a.fact) ∈ S.addeds ∧
        (∀ y ∈ S.inits, y.1 = c.callee →
          ∀ z ∈ S.edges, z.1 = c.callee → z.2.1 = y.2 → z.2.2.1 = P.exit c.callee →
          ∀ dd ∈ demFor demL c.callee, ∀ g' ∈ (restrict y.2 z.2.2.2 dd).toList,
          sat y.2 a.fact = true →
          ∀ r ∈ (applySummary a y.2 g').facts, ∀ e2 ∈ c.fromCallee,
          ∀ r' ∈ (applyEdge r e2.1 e2.2).facts, (x.1, x.2.1, n', limitF counted L r') ∈ S.edges) ∧
        (∀ y ∈ recL, y.1 = c.callee → (sat y.2.1 a.fact = true ∨ applicable y.2.1 a.fact = true) →
          ∀ r ∈ (applySummary a y.2.1 y.2.2).facts, ∀ e2 ∈ c.fromCallee,
          ∀ r' ∈ (applyEdge r e2.1 e2.2).facts, (x.1, x.2.1, n', limitF counted L r') ∈ S.edges)
  | .clean cl => ∀ f' ∈ (cleanRes cl x.2.2.2).facts, (x.1, x.2.1, n', f') ∈ S.edges
  | .filt b may => (x.2.2.2.fact.base = b → may x.2.2.2.fact.path = true) →
      (x.1, x.2.1, n', x.2.2.2) ∈ S.edges

instance instDecInstrRA (x : EdgeT) (n' : Node) :
    (ins : Instr) → Decidable (InstrRA P counted L demL sat restrict recL S x n' ins)
  | .stmt _ => by dsimp only [InstrRA]; exact inferInstance
  | .call _ => by dsimp only [InstrRA]; exact inferInstance
  | .clean _ => by dsimp only [InstrRA]; exact inferInstance
  | .filt _ _ => by dsimp only [InstrRA]; exact inferInstance

/-- THE STATE IS CLOSED UNDER THE RULES OF `DRA` (no request rule; the state has no request). -/
def ClosedRA : Prop :=
  (∀ M ∈ roots, (M, zeroFact) ∈ S.inits) ∧
  (∀ y ∈ S.inits, (y.1, y.2, P.entry y.1, startFact y.2) ∈ S.edges) ∧
  (∀ x ∈ S.edges, ∀ pe ∈ P.edges, pe.1 = x.1 → pe.2.1 = x.2.2.1 →
    InstrRA P counted L demL sat restrict recL S x pe.2.2.2 pe.2.2.1) ∧
  (∀ x ∈ S.edges, ∀ sk ∈ sinks, sk.1 = x.1 → sk.2.1 = x.2.2.1 →
    check x.2.1 x.2.2.2 sk.2.2 = .triggered → (x.1, x.2.2.1, sk.2.2, x.2.2.2.demand) ∈ S.vulns) ∧
  (∀ y ∈ S.addeds, ∀ dd ∈ demFor demL y.1, ∀ j ∈ (emit dd.din y.2).toList, (y.1, j) ∈ S.inits)

instance instDecClosedRA : Decidable (ClosedRA P counted L demL emit sat restrict recL sinks roots S) := by
  unfold ClosedRA; exact inferInstance

/-- A CLOSED STATE BOUNDS `DRA`, for every demand inside the demand list (with the zero demand) and
    every record set inside the record list. -/
theorem closedRA_sound (hC : ClosedRA P counted L demL emit sat restrict recL sinks roots S)
    {dem : MethodId → DemandEdge → Prop} (hdem : ∀ m d, dem m d → d ∈ demFor demL m)
    {recs : Recs} (hrecs : ∀ m x, recs m x → (m, x) ∈ recL) {o : Obj}
    (h : DRA P counted L dem emit sat restrict recs sinks roots o) : S.Inv o := by
  obtain ⟨hroot, hstart, hinstr, hsink, hinit⟩ := hC
  induction h with
  | root hM => exact hroot _ hM
  | @start M i _ ih => exact hstart (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    exact hinstr (M, i, n, f) ih (M, n, .stmt s, n') hE rfl rfl f' hf
  | @pass M i n f n' c _ hE hm ih =>
    exact (hinstr (M, i, n, f) ih (M, n, .call c, n') hE rfl rfl).1 hm
  | @added M i n f n' c e a _ hE he ha ih =>
    exact ((hinstr (M, i, n, f) ih (M, n, .call c, n') hE rfl rfl).2 e he a ha).1
  | @initR m a d j _ hd he ih =>
    exact hinit (m, a) ih d (hdem m d hd) j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    exact ((hinstr (M, i, n, f) ihf (M, n, .call c, n') hE rfl rfl).2 e1 he1 a ha).2.1
      (c.callee, j) ihj rfl (c.callee, j, P.exit c.callee, g) ihg rfl rfl rfl d (hdem _ d hd)
      g' (RCases.mem_toList_of_eq_some hres) hsat r hr e2 he2 r' hr'
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ih =>
    exact ((hinstr (M, i, n, f) ih (M, n, .call c, n') hE rfl rfl).2 e1 he1 a ha).2.2
      (c.callee, (j, g)) (hrecs _ _ hrec) rfl hsat r hr e2 he2 r' hr'
  | @vuln M i n f s _ hs hc ih => exact hsink (M, i, n, f) ih (M, n, s) hs rfl rfl hc
  | @clean M i n f n' cl f' _ hE hf ih =>
    exact hinstr (M, i, n, f) ih (M, n, .clean cl, n') hE rfl rfl f' hf
  | @filt M i n f n' b may _ hE hl ih =>
    exact hinstr (M, i, n, f) ih (M, n, .filt b may, n') hE rfl rfl hl

end RA

#print axioms closedRA_sound

/-! ## 3. The backward restricted run `DBA` -/

section BA
variable (Pb : Program) (counted : Acc → Bool) (L : Nat)
  (demL : List (MethodId × DemandEdge))
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recL : List (MethodId × (PFact × AFact)))
  (sinks : List (MethodId × Node × PFact)) (roots : List MethodId)
  (seeds : List (MethodId × Node × PFact)) (S : LS)

/-- The zero rules of one instruction at a zero edge `x` (only a call has them). -/
def ZeroBA (x : EdgeT) (n' : Node) : Instr → Prop
  | .call c => (x.1, zeroFact, n', Backward.zeroAF) ∈ S.edges ∧ (c.callee, zeroFact) ∈ S.inits ∧
      (∀ z ∈ S.edges, z.1 = c.callee → z.2.1 = zeroFact → z.2.2.1 = Pb.exit c.callee →
        ∀ r ∈ (applySummary Backward.zeroAF zeroFact z.2.2.2).facts, ∀ e2 ∈ c.fromCallee,
        ∀ r' ∈ (applyEdge r e2.1 e2.2).facts, (x.1, zeroFact, n', limitF counted L r') ∈ S.edges)
  | _ => True

instance instDecZeroBA (x : EdgeT) (n' : Node) :
    (ins : Instr) → Decidable (ZeroBA Pb counted L S x n' ins)
  | .stmt _ => isTrue trivial
  | .call _ => by dsimp only [ZeroBA]; exact inferInstance
  | .clean _ => isTrue trivial
  | .filt _ _ => isTrue trivial

/-- THE STATE IS CLOSED UNDER THE RULES OF `DBA` with the zero binding (`zbind = true`). -/
def ClosedBA : Prop :=
  ClosedRA Pb counted L demL emit sat restrict recL sinks roots S ∧
  (∀ x ∈ S.edges, x.2.1 = zeroFact → x.2.2.2 = Backward.zeroAF → ∀ pe ∈ Pb.edges, pe.1 = x.1 →
    pe.2.1 = x.2.2.1 → ZeroBA Pb counted L S x pe.2.2.2 pe.2.2.1) ∧
  (∀ sd ∈ seeds, (sd.1, zeroFact, sd.2.1, Backward.zeroAF) ∈ S.edges →
    (sd.1, zeroFact, sd.2.1, limitF counted L ⟨sd.2.2, false⟩) ∈ S.edges)

instance instDecClosedBA :
    Decidable (ClosedBA Pb counted L demL emit sat restrict recL sinks roots seeds S) := by
  unfold ClosedBA; exact inferInstance

/-- A CLOSED STATE BOUNDS `DBA`, for every demand inside the demand list (with the zero demand) and
    every record set inside the record list. -/
theorem closedBA_sound (hC : ClosedBA Pb counted L demL emit sat restrict recL sinks roots seeds S)
    {dem : MethodId → DemandEdge → Prop} (hdem : ∀ m d, dem m d → d ∈ demFor demL m)
    {recs : Recs} (hrecs : ∀ m x, recs m x → (m, x) ∈ recL) {o : Obj}
    (h : DBA Pb counted L dem emit sat restrict recs sinks roots seeds true o) : S.Inv o := by
  obtain ⟨⟨hroot, hstart, hinstr, hsink, hinit⟩, hzero, hseed⟩ := hC
  induction h with
  | root hM => exact hroot _ hM
  | @start M i _ ih => exact hstart (M, i) ih
  | @step M i n f n' s f' _ hE hf ih =>
    exact hinstr (M, i, n, f) ih (M, n, .stmt s, n') hE rfl rfl f' hf
  | @pass M i n f n' c _ hE hm ih =>
    exact (hinstr (M, i, n, f) ih (M, n, .call c, n') hE rfl rfl).1 hm
  | @added M i n f n' c e a _ hE he ha ih =>
    exact ((hinstr (M, i, n, f) ih (M, n, .call c, n') hE rfl rfl).2 e he a ha).1
  | @initR m a d j _ hd he ih =>
    exact hinit (m, a) ih d (hdem m d hd) j (RCases.mem_toList_of_eq_some he)
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    exact ((hinstr (M, i, n, f) ihf (M, n, .call c, n') hE rfl rfl).2 e1 he1 a ha).2.1
      (c.callee, j) ihj rfl (c.callee, j, Pb.exit c.callee, g) ihg rfl rfl rfl d (hdem _ d hd)
      g' (RCases.mem_toList_of_eq_some hres) hsat r hr e2 he2 r' hr'
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha hrec hsat hr he2 hr' ih =>
    exact ((hinstr (M, i, n, f) ih (M, n, .call c, n') hE rfl rfl).2 e1 he1 a ha).2.2
      (c.callee, (j, g)) (hrecs _ _ hrec) rfl hsat r hr e2 he2 r' hr'
  | @vuln M i n f s _ hs hc ih => exact hsink (M, i, n, f) ih (M, n, s) hs rfl rfl hc
  | @clean M i n f n' cl f' _ hE hf ih =>
    exact hinstr (M, i, n, f) ih (M, n, .clean cl, n') hE rfl rfl f' hf
  | @filt M i n f n' b may _ hE hl ih =>
    exact hinstr (M, i, n, f) ih (M, n, .filt b may, n') hE rfl rfl hl
  | @zpass M n n' c _ hE ih =>
    exact (hzero (M, zeroFact, n, Backward.zeroAF) ih rfl rfl (M, n, .call c, n') hE rfl rfl).1
  | @zin M n n' c _ _ hE ih =>
    exact (hzero (M, zeroFact, n, Backward.zeroAF) ih rfl rfl (M, n, .call c, n') hE rfl rfl).2.1
  | @seed M n s hs _ ih => exact hseed (M, n, s) hs ih
  | @zret M n n' c g r e2 r' _ _ hE _ hr he2 hr' ih ihg =>
    exact (hzero (M, zeroFact, n, Backward.zeroAF) ih rfl rfl (M, n, .call c, n') hE rfl rfl).2.2
      (c.callee, zeroFact, Pb.exit c.callee, g) ihg rfl rfl rfl r hr e2 he2 r' hr'

end BA

#print axioms closedBA_sound

end ApSpec.Abs
