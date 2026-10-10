/-
  ApSpec.HandoffExclusion — THE EXCLUSION THEOREM of the hand-off of the DEMAND EDGES only
  (decision F70): a method with no demand is not analysed again, except from the zero fact.

  The user's observation (2026-10-09): with the new hand-off, a method key with no demand edge in
  run i gets no demand in run i + 1, so it is never analysed again (except the zero fact): it is
  complete. The formal form:
    * BACKWARD (`exclusion_backward`): in the backward run, if every initial fact of the method
      `M` is the zero fact (for example: `M` has no demand edge, `exclusion_backward_nodem`) and
      no seed lies in a method that `M` reaches through calls (its call subtree, `M` included),
      then every edge of `M` is the zero-premise edge with the zero fact.
    * THE HAND-OFF (`exclusion_demand`): so `demOfN` gives `M` only the zero pattern
      `(zero, none)`.
    * FORWARD (`exclusion_forward`, `forward_zero_init`, `forward_zero_edges`): so the next
      forward run (`DR` with the emission `emitM`) has only the zero fact as an initial fact of
      `M`, and every edge of `M` has the zero premise.
    * ONE ROUND (`exclusion_round`): a method key with no NON-CROSSABLE exit edge in forward run
      `k` and no seed in its call subtree is analysed only from the zero fact in forward run
      `k + 1`, if the backward demand is the forward hand-off `handF`.

  The program conditions (the backward run must not put a fact other than the zero fact on the
  zero base, and must not take the zero fact out of the zero base):
    * `NoZeroGenP P`: the three program conditions of `NDZeroBase.NoZeroGen` (a)–(c) on a program
      without conjunctions: (a) the only statement micro edge into the zero base is the zero keep
      edge `(zeroFact, zeroFact)`; (b) the only binding into the callee whose target is on the
      zero base is the zero binding `(zStar, zStar)`; (c) no binding back has its target on the
      zero base;
    * no cleaner is on the zero base (the field `clean` of `Backward.ZeroKept`).
  The run conditions: a mark-copying emission and concrete seeds (`BExact.DB_no_request`: the
  backward run has no request, so the rule `answer` never fires).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffDefs
import ApSpec.BackwardExact

namespace ApSpec.HandoffExclusion
open ApSpec ApSpec.Reverse ApSpec.Backward ApSpec.Handoff

/-! ## 1. The conditions -/

/-- The zero binding `zero.* → zero.*` (`NDZ.zStar`). -/
def zStarE : PFact := ⟨zeroBase, [], .star Excl.empty, .star⟩

/-- The program conditions (a)–(c) of `NDZeroBase.NoZeroGen`, for a `Program`. -/
structure NoZeroGenP (P : Program) : Prop where
  /-- (a) the only statement micro edge into the zero base is the zero keep edge -/
  stmt : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ P.edges →
    ∀ e ∈ s.edges, e.2.base = zeroBase → e = (zeroFact, zeroFact)
  /-- (b) the only binding into the zero base of the callee is the zero binding -/
  toCallee : ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    ∀ e ∈ c.toCallee, e.2.base = zeroBase → e = (zStarE, zStarE)
  /-- (c) no binding back goes to the zero base -/
  fromCallee : ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    ∀ e ∈ c.fromCallee, e.2.base ≠ zeroBase

/-- The methods that `M` reaches through calls: its call subtree, `M` included. -/
inductive Reaches (P : Program) (M : MethodId) : MethodId → Prop where
  | refl : Reaches P M M
  | call {N n c n'} : Reaches P M N → (N, n, Instr.call c, n') ∈ P.edges →
      Reaches P M c.callee

/-! ## 2. The zero fact gives only the zero fact -/

/-- An edge applies only to a fact on its premise base. -/
theorem applyEdge_base {c x : AFact} {fr to : PFact} (hx : x ∈ (applyEdge c fr to).facts) :
    c.fact.base = fr.base := by
  cases hb : Nat.beq c.fact.base fr.base with
  | true => exact Nat.eq_of_beq_eq_true hb
  | false =>
    unfold applyEdge at hx
    rw [hb, if_neg Bool.false_ne_true] at hx
    cases hx

/-- The premise of a reversed edge is on the target base of the edge. -/
theorem revEdge_fst_base (i f : PFact) : (revEdge i f).1.base = f.base := by
  rw [revEdge_eq]

theorem zero_keep_rev : revEdge zeroFact zeroFact = (zeroFact, zeroFact) := by decide

theorem apply_zero_keep : (applyEdge zeroAF zeroFact zeroFact).facts = [zeroAF] := by decide

theorem apply_zero_id : (applyEdge zeroAF (idEdge zeroBase).1 (idEdge zeroBase).2).facts =
    [zeroAF] := by decide

theorem apply_zero_zstar :
    (applyEdge zeroAF (revEdge zStarE zStarE).1 (revEdge zStarE zStarE).2).facts = [zeroAF] := by
  decide

theorem applySummary_zero : (applySummary zeroAF zeroFact zeroAF).facts = [zeroAF] := by decide

/-- A reversed statement takes the zero fact only to the zero fact (condition (a)). -/
theorem transfer_zero_only {s : Stmt}
    (hs : ∀ e ∈ s.edges, e.2.base = zeroBase → e = (zeroFact, zeroFact))
    {counted : Acc → Bool} {L : Nat} {f : AFact}
    (hf : f ∈ (transfer counted L (Stmt.rev s) zeroAF).facts) : f = zeroAF := by
  rcases Invariant.transfer_mem hf with h | ⟨x, e, he, hx, rfl⟩
  · exact h
  · have hb := applyEdge_base hx
    rcases List.mem_append.mp he with h1 | h2
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp h1
      rw [revEdge_fst_base] at hb
      have hz := hs e0 he0 hb.symm
      rw [hz, zero_keep_rev] at hx
      rw [apply_zero_keep, List.mem_singleton] at hx
      rw [hx]
      rfl
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp h2
      have hb' : b = zeroBase := hb.symm
      subst hb'
      rw [apply_zero_id, List.mem_singleton] at hx
      rw [hx]
      rfl

/-- A cleaner off the zero base keeps the zero fact and gives nothing else. -/
theorem cleanRes_zero_only {cl : Cleaner} (h : cl.base ≠ zeroBase) {f : AFact}
    (hf : f ∈ (cleanRes cl zeroAF).facts) : f = zeroAF := by
  have hb : Nat.beq zeroAF.fact.base cl.base = false := by
    cases hb : Nat.beq zeroAF.fact.base cl.base with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb).symm h
  have hp : cleanPos cl zeroAF.fact = .disjoint := by
    unfold cleanPos
    rw [hb]
    rfl
  unfold cleanRes at hf
  rw [hp] at hf
  exact List.mem_singleton.mp hf

/-- A reversed binding back never reads the zero fact (condition (c)). -/
theorem bindBack_zero_none {e : MicroEdge} (he : e.2.base ≠ zeroBase) {x : AFact} :
    x ∉ (applyEdge zeroAF (revEdge e.1 e.2).1 (revEdge e.1 e.2).2).facts := by
  intro hx
  have hb := applyEdge_base hx
  rw [revEdge_fst_base] at hb
  exact he hb.symm

/-- A reversed binding into the callee takes the zero fact only to the zero fact
    (condition (b)). -/
theorem bindIn_zero_only {e : MicroEdge} (he : e.2.base = zeroBase → e = (zStarE, zStarE))
    {x : AFact} (hx : x ∈ (applyEdge zeroAF (revEdge e.1 e.2).1 (revEdge e.1 e.2).2).facts) :
    x = zeroAF := by
  have hb := applyEdge_base hx
  rw [revEdge_fst_base] at hb
  have hz := he hb.symm
  rw [hz, apply_zero_zstar, List.mem_singleton] at hx
  exact hx

#print axioms transfer_zero_only
#print axioms cleanRes_zero_only
#print axioms bindBack_zero_none
#print axioms bindIn_zero_only

/-! ## 3. The backward run -/

section Backward
variable {P : Program} {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
  {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
  {restrict : PFact → AFact → DemandEdge → Option AFact}
  {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
  {rootsB : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}

local notation "DBr" =>
  DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind

/-- Every edge has its premise as an initial fact. -/
def EdgeInit (R : Obj → Prop) : Obj → Prop
  | .edge M i _ _ => R (.init M i)
  | _ => True

theorem DB_edgeInit {o : Obj} (h : DBr o) : EdgeInit DBr o := by
  induction h with
  | root => trivial
  | start h0 _ => exact h0
  | step _ _ _ ih => exact ih
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ => exact ih
  | retRec _ _ _ _ _ _ _ _ _ ih => exact ih
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ _ ih => exact ih
  | reqClean => trivial
  | filt _ _ _ ih => exact ih
  | zpass _ _ ih => exact ih
  | zin => trivial
  | seed _ _ ih => exact ih
  | zret _ _ _ _ _ _ _ ih _ => exact ih

theorem DB_edge_init {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : DBr (.edge M i n f)) : DBr (.init M i) :=
  DB_edgeInit h

#print axioms DB_edge_init

/-- The invariant: in a call-closed set of methods `S` with no seed, every zero-premise edge has
    the zero fact. -/
def ZInv (S : MethodId → Prop) : Obj → Prop
  | .edge N i _ f => S N → i = zeroFact → f = zeroAF
  | _ => True

/-- THE ZERO INVARIANT. Let `S` be a set of methods closed under the callees, with no seed. Then
    every zero-premise edge of a method of `S` in the backward run has the zero fact. The rules:
    the start fact of the zero fact is the zero fact; a reversed statement, a cleaner off the zero
    base, a filter, a pass keep only the zero fact (conditions (a), `hcl`); no reversed binding
    back reads the zero fact (condition (c)), so `ret` and `retRec` never fire on it; the balanced
    return `zret` applies a zero-premise summary of a callee in `S` (so the zero fact) through
    the zero binding (condition (b)); the sink rule `seed` has no seed in `S`. -/
theorem zinv_all (hG : NoZeroGenP P)
    (hcl : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → cl.base ≠ zeroBase)
    {S : MethodId → Prop}
    (hS : ∀ N n c n', S N → (N, n, Instr.call c, n') ∈ P.edges → S c.callee)
    (hseed : ∀ N n s, (N, n, s) ∈ seeds → ¬ S N) {o : Obj} (h : DBr o) : ZInv S o := by
  induction h with
  | root => trivial
  | @start M i _ _ =>
    intro _ hi
    subst hi
    rfl
  | @step M i n f n' s f' _ hE hf ih =>
    intro hN hi
    have hf0 := ih hN hi
    subst hf0
    obtain ⟨s0, hE0, rfl⟩ := rev_stmt_inv hE
    exact transfer_zero_only (hG.stmt _ _ _ _ hE0) hf
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | @ret M i n f n' c e1 a j g d g' r e2 r' _ hE he1 ha _ _ _ _ _ _ _ _ ih _ _ =>
    intro hN hi
    have hf0 := ih hN hi
    subst hf0
    obtain ⟨c0, hE0, rfl⟩ := rev_call_inv hE
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he1
    exact absurd ha (bindBack_zero_none (hG.fromCallee _ _ _ _ hE0 e0 he0))
  | @retRec M i n f n' c e1 a j g r e2 r' _ hE he1 ha _ _ _ _ _ ih =>
    intro hN hi
    have hf0 := ih hN hi
    subst hf0
    obtain ⟨c0, hE0, rfl⟩ := rev_call_inv hE
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he1
    exact absurd ha (bindBack_zero_none (hG.fromCallee _ _ _ _ hE0 e0 he0))
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | @clean M i n f n' cl f' _ hE hf ih =>
    intro hN hi
    have hf0 := ih hN hi
    subst hf0
    exact cleanRes_zero_only (hcl _ _ _ _ (rev_clean_inv hE)) hf
  | reqClean => trivial
  | filt _ _ _ ih => exact ih
  | zpass _ _ _ => exact fun _ _ => rfl
  | zin => trivial
  | @seed M n s hs _ _ =>
    intro hN _
    exact absurd hN (hseed _ _ _ hs)
  | @zret M n n' c g r e2 r' _ _ hE _ hr he2 hr' _ ihg =>
    intro hN _
    obtain ⟨c0, hE0, rfl⟩ := rev_call_inv hE
    have hSc : S c0.callee := hS _ _ _ _ hN hE0
    have hg0 := ihg hSc rfl
    subst hg0
    rw [applySummary_zero, List.mem_singleton] at hr
    subst hr
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he2
    rw [bindIn_zero_only (hG.toCallee _ _ _ _ hE0 e0 he0) hr']
    rfl

#print axioms zinv_all

/-- The call subtree of `M` is closed under the callees. -/
theorem reaches_closed {M : MethodId} :
    ∀ N n c n', Reaches P M N → (N, n, Instr.call c, n') ∈ P.edges → Reaches P M c.callee :=
  fun _ _ _ _ hN hE => Reaches.call hN hE

/-- THE EXCLUSION THEOREM, BACKWARD. If every initial fact of `M` in the backward run is the zero
    fact and no seed lies in the call subtree of `M`, every edge of `M` is the zero-premise edge
    with the zero fact. -/
theorem exclusion_backward (hG : NoZeroGenP P)
    (hcl : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → cl.base ≠ zeroBase)
    {M : MethodId} (hinit : ∀ i, DBr (.init M i) → i = zeroFact)
    (hseed : ∀ N n s, (N, n, s) ∈ seeds → ¬ Reaches P M N) :
    ∀ i n f, DBr (.edge M i n f) → i = zeroFact ∧ f = zeroAF := by
  intro i n f h
  have hi := hinit i (DB_edge_init h)
  exact ⟨hi, zinv_all hG hcl reaches_closed hseed h Reaches.refl hi⟩

#print axioms exclusion_backward

/-- With a mark-copying emission and concrete seeds, a method with no demand edge has only the
    zero fact as an initial fact in the backward run (rules `root` and `zin`; `initR` needs a
    demand edge, `answer` needs a request, and the run has none). -/
theorem init_zero_nodem (hem : EmitCopiesMark emit) (hsd : BExact.SeedsConc seeds)
    {M : MethodId} (hdem : ∀ d, ¬ demB M d) {i : PFact} (h : DBr (.init M i)) : i = zeroFact := by
  cases h with
  | root _ => rfl
  | initR _ hd _ => exact absurd hd (hdem _)
  | answer hq _ _ _ => exact absurd hq (BExact.DB_no_request hem hsd _ _ _)
  | zin _ _ _ => rfl

#print axioms init_zero_nodem

/-- THE EXCLUSION THEOREM, BACKWARD, for a method with no demand edge. -/
theorem exclusion_backward_nodem (hG : NoZeroGenP P)
    (hcl : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → cl.base ≠ zeroBase)
    (hem : EmitCopiesMark emit) (hsd : BExact.SeedsConc seeds)
    {M : MethodId} (hdem : ∀ d, ¬ demB M d)
    (hseed : ∀ N n s, (N, n, s) ∈ seeds → ¬ Reaches P M N) :
    ∀ i n f, DBr (.edge M i n f) → i = zeroFact ∧ f = zeroAF :=
  exclusion_backward hG hcl (fun _ h => init_zero_nodem hem hsd hdem h) hseed

#print axioms exclusion_backward_nodem

/-- THE HAND-OFF. If every edge of `M` in the backward run is the zero-premise edge with the zero
    fact, `demOfN` gives `M` only the zero pattern `(zero, none)` (for every publication). -/
theorem exclusion_demand {M : MethodId}
    (hM : ∀ i n f, DBr (.edge M i n f) → i = zeroFact ∧ f = zeroAF) (pub : Pub) :
    ∀ d, demOfN (Program.rev P) DBr pub M d → d = ⟨zeroFact, none⟩ := by
  intro d hd
  rcases hd with h1 | ⟨g, hg, rfl⟩ | ⟨jb, gb, gb', hjb, hne, hgb, _, _, _⟩
  · exact h1
  · rw [(hM _ _ _ hg).2]
    rfl
  · exact absurd (hM _ _ _ hgb).1 hne

#print axioms exclusion_demand

end Backward

/-! ## 4. The next forward run -/

/-- The emission from the zero pattern gives only the zero fact. -/
theorem emitM_zero_din {a j : PFact} (h : emitM zeroFact a = some j) : j = zeroFact := by
  obtain ⟨hb, hm, ⟨hq, h1⟩ | ⟨x, r, _, hx, _⟩ | ⟨r, _, hP, hr, _, _⟩⟩ := RCore.emitM_cases h
  · subst h1
    have hab : a.base = zeroBase := (Nat.eq_of_beq_eq_true hb).symm
    have ham : a.mark = .conc zeroMark := by
      cases h' : a.mark with
      | conc t =>
        rw [h'] at hm
        have e : zeroMark = t := Nat.eq_of_beq_eq_true hm
        rw [e]
      | star => rw [h'] at hm; cases hm
      | starEx _ => rw [h'] at hm; cases hm
    have hk : meetK a.kind zeroFact.kind = .exact := by
      show meetK a.kind .exact = .exact
      cases a.kind <;> rfl
    have hp : a.path = [] := hq
    show (⟨a.base, a.path, meetK a.kind zeroFact.kind, a.mark⟩ : PFact) = zeroFact
    rw [hab, hp, hk, ham]
    rfl
  · cases hx
  · have h0 : ([] : List Acc) = a.path ++ r := hP
    exact absurd (List.append_eq_nil_iff.mp h0.symm).2 hr

#print axioms emitM_zero_din

section Forward
variable {P : Program} {counted : Acc → Bool} {L : Nat} {dem : MethodId → DemandEdge → Prop}
  {sat : PFact → PFact → Bool} {restrict : PFact → AFact → DemandEdge → Option AFact}
  {rc : Recs} {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}

local notation "DRr" => DR P counted L dem emitM sat restrict rc sinks roots

/-- A forward run whose demand gives `M` only the zero pattern has only the zero fact as an
    initial fact of `M` (rules `root`, `initR`; `answer` needs a request, and a run with `emitM`
    has none, `RCov.no_reqR`). -/
theorem forward_zero_init {M : MethodId} (hdem : ∀ d, dem M d → d.din = zeroFact)
    {i : PFact} (h : DRr (.init M i)) : i = zeroFact := by
  cases h with
  | root _ => rfl
  | initR _ hd he =>
    rw [hdem _ hd] at he
    exact emitM_zero_din he
  | answer hq _ _ _ =>
    exact absurd hq (RCov.no_reqR P counted L dem emitM sat restrict rc sinks roots
      RCov.emitM_copies)

#print axioms forward_zero_init

/-- Every edge of a forward run has its premise as an initial fact. -/
theorem DR_edgeInit {o : Obj} (h : DRr o) : EdgeInit DRr o := by
  induction h with
  | root => trivial
  | start h0 _ => exact h0
  | step _ _ _ ih => exact ih
  | reqStmt => trivial
  | pass _ _ _ ih => exact ih
  | added => trivial
  | initR => trivial
  | ret _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ => exact ih
  | retRec _ _ _ _ _ _ _ _ _ ih => exact ih
  | reqSink => trivial
  | answer => trivial
  | reqUp => trivial
  | vuln => trivial
  | clean _ _ _ ih => exact ih
  | reqClean => trivial
  | filt _ _ _ ih => exact ih

/-- In such a forward run every edge of `M` has the zero premise. -/
theorem forward_zero_edges {M : MethodId} (hdem : ∀ d, dem M d → d.din = zeroFact)
    {i : PFact} {n : Node} {f : AFact} (h : DRr (.edge M i n f)) : i = zeroFact :=
  forward_zero_init hdem (DR_edgeInit h)

#print axioms forward_zero_edges

end Forward

/-! ## 5. The exclusion theorem and its one-round corollary -/

/-- THE EXCLUSION THEOREM. In the backward run
    `DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind` with a
    mark-copying emission and concrete seeds, if the method `M` has no demand edge and no seed lies
    in its call subtree, then (1) every edge of `M` is the zero-premise edge with the zero fact,
    (2) `demOfN` gives `M` only the zero pattern, and (3) the next forward run with that demand
    (any field limit, satisfaction, restriction, records, sinks and roots) has only the zero fact
    as an initial fact of `M`, and every edge of `M` there has the zero premise. -/
theorem exclusion_theorem {P : Program} (hG : NoZeroGenP P)
    (hcl : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → cl.base ≠ zeroBase)
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
    {rootsB : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hem : EmitCopiesMark emit) (hsd : BExact.SeedsConc seeds)
    {M : MethodId} (hdem : ∀ d, ¬ demB M d)
    (hseed : ∀ N n s, (N, n, s) ∈ seeds → ¬ Reaches P M N) (pub : Pub)
    {counted' : Acc → Bool} {L' : Nat} {sat' : PFact → PFact → Bool}
    {restrict' : PFact → AFact → DemandEdge → Option AFact} {rc' : Recs}
    {sinks' : List (MethodId × Node × PFact)} {roots' : List MethodId} :
    (∀ i n f, DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind
        (.edge M i n f) → i = zeroFact ∧ f = zeroAF) ∧
    (∀ d, demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind) pub
        M d → d = ⟨zeroFact, none⟩) ∧
    (∀ i, DR P counted' L' (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind) pub)
        emitM sat' restrict' rc' sinks' roots' (.init M i) → i = zeroFact) ∧
    (∀ i n f, DR P counted' L' (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind) pub)
        emitM sat' restrict' rc' sinks' roots' (.edge M i n f) → i = zeroFact) := by
  have hB := exclusion_backward_nodem (counted := counted) (L := L) (sat := sat)
    (restrict := restrict) (recsB := recsB) (sinksB := sinksB) (rootsB := rootsB) (zbind := zbind)
    hG hcl hem hsd hdem hseed
  have hD := exclusion_demand hB pub
  have hZ : ∀ d, demOfN (Program.rev P)
      (DB (Program.rev P) counted L demB emit sat restrict recsB sinksB rootsB seeds zbind) pub
      M d → d.din = zeroFact := fun d h => by rw [hD d h]
  exact ⟨hB, hD, fun _ h => forward_zero_init hZ h, fun _ _ _ h => forward_zero_edges hZ h⟩

#print axioms exclusion_theorem

/-- THE ONE-ROUND COROLLARY. Forward run `Rk` with the publication `pub`; the backward demand is
    the forward hand-off (`demB` lies inside `handF P Rk pub`, and `B_generalN` needs the other
    inclusion). A method key `M` with no NON-CROSSABLE exit edge in `Rk` and no seed in its call
    subtree is analysed only from the zero fact in the next forward run: every initial fact and
    every edge premise of `M` there is the zero fact. -/
theorem exclusion_round {P : Program} (hG : NoZeroGenP P)
    (hcl : ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → cl.base ≠ zeroBase)
    {Rk : Obj → Prop} {pub : Pub}
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    (hdemB : ∀ m d, demB m d → handF P Rk pub m d)
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)}
    {rootsB : List MethodId} {seeds : List (MethodId × Node × PFact)} {zbind : Bool}
    (hsd : BExact.SeedsConc seeds)
    {M : MethodId}
    (hcross : ∀ j g, Rk (.init M j) → Rk (.edge M j (P.exit M) g) → Cross j g)
    (hseed : ∀ N n s, (N, n, s) ∈ seeds → ¬ Reaches P M N)
    {counted' : Acc → Bool} {L' : Nat} {sat' : PFact → PFact → Bool}
    {restrict' : PFact → AFact → DemandEdge → Option AFact} {rc' : Recs}
    {sinks' : List (MethodId × Node × PFact)} {roots' : List MethodId} :
    (∀ i, DR P counted' L' (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB rootsB seeds zbind)
        (pubR demB)) emitM sat' restrict' rc' sinks' roots' (.init M i) → i = zeroFact) ∧
    (∀ i n f, DR P counted' L' (demOfN (Program.rev P)
        (DB (Program.rev P) counted L demB emitM satI restrictI recsB sinksB rootsB seeds zbind)
        (pubR demB)) emitM sat' restrict' rc' sinks' roots' (.edge M i n f) → i = zeroFact) := by
  have hdem : ∀ d, ¬ demB M d := by
    intro d hd
    obtain ⟨j, g, _, hj, hg, hnc, _, _⟩ := hdemB M d hd
    exact hnc (hcross j g hj hg)
  obtain ⟨_, _, h3, h4⟩ := exclusion_theorem (counted := counted) (L := L) (sat := satI)
    (restrict := restrictI) (recsB := recsB) (sinksB := sinksB) (rootsB := rootsB)
    (zbind := zbind) hG hcl RCov.emitM_copies hsd hdem hseed (pubR demB)
    (counted' := counted') (L' := L') (sat' := sat') (restrict' := restrict') (rc' := rc')
    (sinks' := sinks') (roots' := roots')
  exact ⟨h3, h4⟩

#print axioms exclusion_round

end ApSpec.HandoffExclusion
