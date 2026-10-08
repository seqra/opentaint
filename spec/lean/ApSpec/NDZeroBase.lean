/-
  ApSpec.NDZeroBase — the zero base of the ND closure of the spec `NDZ.DNz` holds only the zero
  fact (ap.md §3.5, §4.6, S11 (c), (d); interpreter.md I11 (c), (d); analyzer-core.md §5.4).

  The program condition `NoZeroGen Q` states the interpreter rules that put a fact on the zero
  base:
    (a) a statement micro edge whose target is on the zero base is the zero keep edge
        `(zeroFact, zeroFact)` (interpreter.md I11 (d): the only edge into the zero base is the
        keep edge);
    (b) a binding into the callee whose target is on the zero base is the zero binding
        `(zStar, zStar)` (ap.md §3.5);
    (c) no binding back has its target on the zero base (ap.md S11 (c), I11 (c); this is the
        forward form of `Backward.NoZeroBack`, which reads the reversed binding);
    (d) no conjunction target is on the zero base (interpreter.md §5.3: the target of a
        conjunctive source rule is a program location with a concrete mark).
  The abstraction condition `AlphaZero α`: the abstraction keeps the base of the added fact and
  serves the zero fact by itself. `policy` (so also `policy1`) satisfies it
  (`policy_alphaZero`, `policy1_alphaZero`). The answer `answerInit` needs no condition: an
  answer on the zero base answers the zero fact with the zero fact (`answerInit_zero`).

  Main theorems (under `NoZeroGen X.Q` and `AlphaZero X.α`):
    * `zero_base_inv`: every fact of `DNz` on the zero base is the zero fact: the initial facts,
      the premises and the conclusion of every edge, the added facts, the premises of the
      requests and of the partial matches.
    * The forms per object: `dnz_init_zero`, `dnz_edge_zero`, `dnz_premise_zero`,
      `dnz_added_zero`.
    * `dnz_applicable_zero`: a premise `p` of an edge of `DNz` that a fact on the zero base
      satisfies (`applicable p a = true`) is the zero fact. So `applicable p zeroFact = true →
      p = zeroFact`.
    * `zero_binding`: the zero binding takes the zero fact to the zero fact (the added fact of
      the zero subscription is `zeroFact`).
  `PipelineNDZ.clDNz_ndpub_zero_sub` uses them: the zero subscription never takes part in a
  k-ary join.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.NDZ
import ApSpec.Restricted

namespace ApSpec.NDZeroBase
open ApSpec ApSpec.ND ApSpec.NDZ

/-! ## 1. The conditions -/

/-- A fact on the zero base is the zero fact. -/
def ZOnly (p : PFact) : Prop := p.base = zeroBase → p = zeroFact

theorem zOnly_zero : ZOnly zeroFact := fun _ => rfl

/-- The interpreter rules that put a fact on the zero base (see the header). -/
structure NoZeroGen (Q : NProg) : Prop where
  /-- (a) the only statement micro edge into the zero base is the zero keep edge -/
  stmt : ∀ M n s n', (M, n, Instr.stmt s, n') ∈ Q.prog.edges →
    ∀ e ∈ s.edges, e.2.base = zeroBase → e = (zeroFact, zeroFact)
  /-- (b) the only binding into the zero base of the callee is the zero binding -/
  toCallee : ∀ M n c n', (M, n, Instr.call c, n') ∈ Q.prog.edges →
    ∀ e ∈ c.toCallee, e.2.base = zeroBase → e = (zStar, zStar)
  /-- (c) no binding back goes to the zero base -/
  fromCallee : ∀ M n c n', (M, n, Instr.call c, n') ∈ Q.prog.edges →
    ∀ e ∈ c.fromCallee, e.2.base ≠ zeroBase
  /-- (d) no conjunction target is on the zero base -/
  conj : ∀ M n cj n', (M, n, cj, n') ∈ Q.conjs → cj.target.base ≠ zeroBase

/-- The abstraction keeps the base and serves the zero fact by itself. -/
structure AlphaZero (α : MethodId → PFact → PFact) : Prop where
  base : ∀ m a, (α m a).base = a.base
  zero : ∀ m, α m zeroFact = zeroFact

theorem policy_alphaZero (demand : MethodId → List PFact) : AlphaZero (policy demand) where
  base m a := by
    unfold policy
    by_cases h : a = zeroFact
    · rw [if_pos h, h]
    · rw [if_neg h]
      split <;> rfl
  zero _ := by
    unfold policy
    rw [if_pos rfl]

/-- The run-1 policy of the spec satisfies the condition. -/
theorem policy1_alphaZero : AlphaZero policy1 := policy_alphaZero _

/-! ## 2. The AP operations on the zero base -/

theorem norm_base (f : AFact) : (AFact.norm f).fact.base = f.fact.base := by
  unfold AFact.norm
  split <;> rfl

/-- A result of `applyEdge` is on the base of the target, and the fact is on the base of the
    source. -/
theorem applyEdge_base {c : AFact} {fr to : PFact} {r : AFact}
    (h : r ∈ (applyEdge c fr to).facts) : r.fact.base = to.base ∧ c.fact.base = fr.base := by
  unfold applyEdge at h
  split at h
  · rename_i hb
    refine ⟨?_, Nat.eq_of_beq_eq_true hb⟩
    simp only at h
    split at h
    · simp [Res.none] at h
    · split at h
      · simp [Res.none] at h
      · simp at h
      · split at h
        · simp [Res.none] at h
        · rw [List.mem_singleton.1 h, norm_base]
  · simp [Res.none] at h

/-- The zero keep edge takes the zero fact to the zero fact. -/
theorem applyEdge_keep (d : Bool) :
    applyEdge ⟨zeroFact, d⟩ zeroFact zeroFact = ⟨[⟨zeroFact, d⟩], []⟩ := by
  cases d <;> rfl

/-- The zero binding takes the zero fact to the zero fact. -/
theorem applyEdge_zStar (d : Bool) :
    applyEdge ⟨zeroFact, d⟩ zStar zStar = ⟨[⟨zeroFact, d⟩], []⟩ := by
  cases d <;> rfl

/-- The added fact of the zero subscription is the zero fact (ap.md §3.5). -/
theorem zero_binding : applyEdge ⟨zeroFact, false⟩ zStar zStar = ⟨[⟨zeroFact, false⟩], []⟩ :=
  applyEdge_zStar false

theorem limitF_base (counted : Acc → Bool) (L : Nat) (f : AFact) :
    (limitF counted L f).fact.base = f.fact.base := by
  unfold limitF
  split <;> rfl

theorem limitF_zeroF (counted : Acc → Bool) (L : Nat) (d : Bool) :
    limitF counted L ⟨zeroFact, d⟩ = ⟨zeroFact, d⟩ := rfl

theorem mem_applyAll_inv {c r : AFact} :
    ∀ {es : List MicroEdge}, r ∈ (applyAll c es).facts →
      ∃ e ∈ es, r ∈ (applyEdge c e.1 e.2).facts
  | [], h => absurd h List.not_mem_nil
  | e :: es, h => by
    rcases List.mem_append.1 h with h | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', h'⟩ := mem_applyAll_inv h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

/-- An abstract fact whose path fact is the zero fact. -/
theorem afact_zero {f : AFact} (h : f.fact = zeroFact) : f = ⟨zeroFact, f.demand⟩ := by
  obtain ⟨_, _⟩ := f
  cases h
  rfl

/-- A statement whose edges into the zero base are the keep edge puts on the zero base only the
    zero fact. -/
theorem transfer_zero {counted : Acc → Bool} {L : Nat} {s : Stmt} {f f' : AFact}
    (hs : ∀ e ∈ s.edges, e.2.base = zeroBase → e = (zeroFact, zeroFact)) (hf : ZOnly f.fact)
    (h : f' ∈ (transfer counted L s f).facts) : ZOnly f'.fact := by
  unfold transfer at h
  split at h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
    obtain ⟨e, he, hre⟩ := mem_applyAll_inv hr
    intro hz
    rw [limitF_base] at hz
    have ⟨hb1, hb2⟩ := applyEdge_base hre
    obtain rfl := hs e he (hb1 ▸ hz)
    rw [afact_zero (hf hb2)] at hre
    rw [applyEdge_keep] at hre
    rw [List.mem_singleton.1 hre]
    rfl
  · rw [List.mem_singleton.1 h]
    exact hf

theorem cleanRes_base {cl : Cleaner} {c r : AFact} (h : r ∈ (cleanRes cl c).facts) :
    r.fact.base = c.fact.base := by
  unfold cleanRes at h
  split at h
  · rw [List.mem_singleton.1 h]
  · split at h
    · split at h
      · simp [Res.none] at h
      · rw [List.mem_singleton.1 h]
    · rw [List.mem_singleton.1 h]
    · simp [Res.none] at h
  · split at h
    · split at h
      · rw [List.mem_singleton.1 h]
        unfold concPart
        split <;> rfl
      · rw [List.mem_singleton.1 h]
    · rw [List.mem_singleton.1 h]
    · rw [List.mem_singleton.1 h, norm_base]

/-- A cleaner keeps the zero fact or drops it; it makes no other fact from it. -/
theorem cleanRes_zero {cl : Cleaner} {d : Bool} {r : AFact}
    (h : r ∈ (cleanRes cl ⟨zeroFact, d⟩).facts) : r.fact = zeroFact := by
  unfold cleanRes at h
  split at h
  · rw [List.mem_singleton.1 h]
  · split at h
    · split at h
      · simp [Res.none] at h
      · rw [List.mem_singleton.1 h]
    · rename_i hm
      exact absurd rfl (hm zeroMark)
    · simp [Res.none] at h
  · split at h
    · split at h
      · rw [List.mem_singleton.1 h]
        rfl
      · rw [List.mem_singleton.1 h]
    · rename_i hm
      exact absurd rfl (hm zeroMark)
    · rw [List.mem_singleton.1 h]
      rfl

theorem startFact_base (i : PFact) : (startFact i).fact.base = i.base := by
  unfold startFact
  split <;> rfl

theorem answerInit_base (i a : PFact) (t : Mark) : (answerInit i a t).base = i.base := by
  unfold answerInit
  split <;> rfl

/-- The answer of a request of the zero fact. -/
theorem answerInit_zero (a : PFact) (t : Mark) :
    answerInit zeroFact a t = ⟨zeroBase, [], .exact, .conc t⟩ := by
  unfold answerInit
  split <;> rfl

theorem overlapB_base {a b : PFact} (h : overlapB a b = true) : a.base = b.base := by
  unfold overlapB at h
  exact Nat.eq_of_beq_eq_true (Bool.and_eq_true _ _ ▸ h).1

theorem applicable_base {p a : PFact} (h : applicable p a = true) : p.base = a.base := by
  unfold applicable coversB at h
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1.1.1

theorem mem_dropZ {P : List PFact} {p : PFact} (h : p ∈ dropZ P) : p ∈ P ∨ p = zeroFact := by
  unfold dropZ at h
  split at h
  · exact .inr (List.mem_singleton.1 h)
  · exact .inl (List.mem_filter.1 h).1

theorem dropZ_zOnly {P : List PFact} (h : ∀ p ∈ P, ZOnly p) : ∀ p ∈ dropZ P, ZOnly p := by
  intro p hp
  rcases mem_dropZ hp with hp | rfl
  · exact h p hp
  · exact zOnly_zero

/-! ## 3. The invariant -/

/-- The zero-base invariant of an object of `DNz`. A partial match also keeps its call
    statement (the binding back of `ndRet` needs it). -/
def ZMot (X : Ctx) : NObj → Prop
  | .ninit _ i => ZOnly i
  | .nedge _ P _ f => (∀ p ∈ P, ZOnly p) ∧ ZOnly f.fact
  | .nadded _ a => ZOnly a
  | .nreq _ i _ => ZOnly i
  | .nvuln .. => True
  | .npart M n c n' _ P _ => (M, n, Instr.call c, n') ∈ X.Q.prog.edges ∧ ∀ p ∈ P, ZOnly p

variable {X : Ctx}

/-- A result of a binding back is not on the zero base. -/
theorem back_not_zero (hG : NoZeroGen X.Q) {M : MethodId} {n n' : Node} {c : Call}
    (hc : (M, n, Instr.call c, n') ∈ X.Q.prog.edges) {e2 : MicroEdge} (he2 : e2 ∈ c.fromCallee)
    {r r' : AFact} (hr' : r' ∈ (applyEdge r e2.1 e2.2).facts) :
    ZOnly (limitF X.counted X.FL r').fact := by
  intro hz
  rw [limitF_base, (applyEdge_base hr').1] at hz
  exact absurd hz (hG.fromCallee _ _ _ _ hc e2 he2)

/-- THE ZERO-BASE THEOREM: every fact of `DNz` on the zero base is the zero fact. -/
theorem zero_base_inv (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) {o : NObj} (h : DNz X o) :
    ZMot X o := by
  induction h with
  | root => exact zOnly_zero
  | start _ ih =>
    refine ⟨fun p hp => (List.mem_singleton.1 hp) ▸ ih, ?_⟩
    intro hz
    rw [startFact_base] at hz
    rw [ih hz]
    rfl
  | step _ he hf ih => exact ⟨ih.1, transfer_zero (hG.stmt _ _ _ _ he) ih.2 hf⟩
  | reqStmt _ _ _ ih => exact ih.1 _ List.mem_cons_self
  | pass _ _ _ ih => exact ih
  | added _ he he1 ha ih =>
    intro hz
    have ⟨hb1, hb2⟩ := applyEdge_base ha
    obtain rfl := hG.toCallee _ _ _ _ he _ he1 (hb1 ▸ hz)
    rw [afact_zero (ih.2 hb2), applyEdge_zStar] at ha
    rw [List.mem_singleton.1 ha]
  | initA _ ih =>
    intro hz
    rw [hα.base] at hz
    rw [ih hz, hα.zero]
  | ret _ he _ _ _ _ _ _ he2 hr' ihf => exact ⟨ihf.1, back_not_zero hG he he2 hr'⟩
  | ndOpen he => exact ⟨he, fun _ hp => absurd hp List.not_mem_nil⟩
  | ndBind _ _ _ _ _ ihp ihf =>
    refine ⟨ihp.1, fun p hp => ?_⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact ihp.2 p hp
    · exact ihf.1 p hp
  | ndRet _ he2 hr ihp => exact ⟨dropZ_zOnly ihp.2, back_not_zero hG ihp.1 he2 hr⟩
  | reqSink _ _ _ ih => exact ih.1 _ List.mem_cons_self
  | @answer M i t a _ _ hm hov ihr iha =>
    intro hz
    rw [answerInit_base] at hz
    have hi := ihr hz
    subst hi
    have ha := iha ((overlapB_base hov).trans hz)
    subst ha
    cases hm
    rw [answerInit_zero]
    rfl
  | reqUp _ _ _ _ _ _ _ _ _ ihf => exact ihf.1 _ List.mem_cons_self
  | vuln => trivial
  | clean _ _ hf ih =>
    refine ⟨ih.1, fun hz => ?_⟩
    rw [cleanRes_base hf] at hz
    rw [afact_zero (ih.2 hz)] at hf
    exact cleanRes_zero hf
  | reqClean _ _ _ ih => exact ih.1 _ List.mem_cons_self
  | filt _ _ _ ih => exact ih
  | conj _ _ hcj _ _ _ _ ih1 ih2 =>
    refine ⟨dropZ_zOnly fun p hp => ?_, fun hz => absurd hz (hG.conj _ _ _ _ hcj)⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact ih1.1 p hp
    · exact ih2.1 p hp
  | reqConj _ _ _ _ _ ih => exact ih.1 _ List.mem_cons_self

/-! ## 4. The forms per object -/

theorem dnz_init_zero (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) {M : MethodId} {i : PFact}
    (h : DNz X (.ninit M i)) (hz : i.base = zeroBase) : i = zeroFact :=
  zero_base_inv hG hα h hz

theorem dnz_edge_zero (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) {M : MethodId}
    {P : List PFact} {n : Node} {f : AFact} (h : DNz X (.nedge M P n f))
    (hz : f.fact.base = zeroBase) : f.fact = zeroFact :=
  (zero_base_inv hG hα h).2 hz

theorem dnz_premise_zero (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) {M : MethodId}
    {P : List PFact} {n : Node} {f : AFact} (h : DNz X (.nedge M P n f)) {p : PFact}
    (hp : p ∈ P) (hz : p.base = zeroBase) : p = zeroFact :=
  (zero_base_inv hG hα h).1 p hp hz

theorem dnz_added_zero (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) {M : MethodId} {a : PFact}
    (h : DNz X (.nadded M a)) (hz : a.base = zeroBase) : a = zeroFact :=
  zero_base_inv hG hα h hz

/-- A premise of an edge of `DNz` that a fact on the zero base satisfies is the zero fact. In
    particular `applicable p zeroFact = true → p = zeroFact`. -/
theorem dnz_applicable_zero (hG : NoZeroGen X.Q) (hα : AlphaZero X.α) {M : MethodId}
    {P : List PFact} {n : Node} {f : AFact} (h : DNz X (.nedge M P n f)) {p a : PFact}
    (hp : p ∈ P) (hap : applicable p a = true) (hz : a.base = zeroBase) : p = zeroFact :=
  dnz_premise_zero hG hα h hp ((applicable_base hap).trans hz)

/-! ## 5. Axiom audit -/

#print axioms policy_alphaZero
#print axioms policy1_alphaZero
#print axioms zero_binding
#print axioms zero_base_inv
#print axioms dnz_init_zero
#print axioms dnz_edge_zero
#print axioms dnz_premise_zero
#print axioms dnz_added_zero
#print axioms dnz_applicable_zero

end ApSpec.NDZeroBase
