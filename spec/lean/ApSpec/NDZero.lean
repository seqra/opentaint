/-
  ApSpec.NDZero — the zero-drop closure `NDZ.DNz` and the list model `ND.DN` give the same edges
  (spec ap.md §2.4, §4.6; analyzer-core.md §5.4).

  `ND.DN` keeps the zero fact in the joined premise list of a conjunction and of an ND summary
  application. `NDZ.DNz` drops it (`dropZ`). The zero fact is at every node that an edge reaches,
  so the two closures have the same edges up to the zero members of the premise lists. This file
  proves it.

  Contents:
    * Part 1. The hypotheses. `ZeroCalls` (a call does not touch the zero base, and it has the
      zero binding `zStar → zStar`, spec §3.5), `ConjAdj` (a conjunction sits beside an
      instruction edge), and `Backward.ZeroKept` (S11 (d)). `ZeroLinks` (only for `dn_to_dnz`):
      a caller edge whose binding gives the zero fact to a callee has only zero premises.
    * Part 2. The `dropZ` lemmas. `nz P` is the filter of `dropZ`; `dropZ P = dropZ Q ↔ nz P =
      nz Q` (`dropZ_eq_iff`). Idempotence (`dropZ_idem`), `dropZ_append_zero`,
      `dropZ_dropZ_append`, membership (`mem_dropZ`, `mem_nz`, `dropZ_eq_zero_iff`), the length
      facts (`dropZ_ne_nil`, `one_le_dropZ`, `dropZ_length_le`, `two_le_dropZ`).
    * Part 3. Z0, THE ZERO FACT IS EVERYWHERE (`zero_everywhere` for `DN`, `zero_everywhere_z` for
      `DNz`): an edge at a node gives the zero edge `[zeroFact] → zeroAF` there and the zero
      initial fact of its method; an initial fact and an added fact give the zero initial fact;
      a partial match gives its call edge, and the zero edge at its call node once a caller edge
      is bound (`zero_edge_of_part`). A partial match that `ndOpen` has just opened binds no
      caller edge, so it does not give the zero edge: this is the strongest true form.
    * Part 4. The layer correspondence `Corr` (the same fact; the same layer, or a concrete mark)
      and its preservation by every AP operation (`applyEdge_corr`, `transfer_corr`,
      `cleanRes_corr`, `applySummary_corr`, `limitF_corr`, `conjFact_corr`). For a concrete mark
      the normal form does not read the layer, so the layer can differ. An ND summary applied
      as a single-premise summary gives its own fact (`summary_nd_fact`, `summary_nd_exists`):
      the Lean `applyEdge` of a concrete, non-`*` conclusion gives the conclusion with the layer
      of the added fact OR'd in, or the demand layer (the `* ∘ $` case).
    * Part 5. Z2, `dnz_to_dn`: every object of `DNz` is an object of `DN`. An edge `P' → f'`
      comes from an edge `P → f` of `DN` with `dropZ P = P'` and the same fact, and `f` is in a
      layer that is NOT HIGHER (a normal `DNz` edge comes from a normal `DN` edge). The zero
      members of a `DN` summary are bound by the caller zero edges of Z0.
    * Part 6. Z1, `dn_to_dnz`: under `ZeroLinks`, every object of `DN` is an object of `DNz`;
      an edge `P → f` gives an edge `dropZ P → f'` with the same fact (the layer can differ; the
      uses of Z1 do not read it). Z1 needs only `NProg.WF` and `ZeroLinks`, not the Z0
      hypotheses: `DNz` never binds a zero member.
    * Part 7. The forms per object: `dnz_to_dn_edge`, `dn_to_dnz_edge`, `edge_iff` (the edges of
      `DNz` keyed by `P'` are the edges of `DN` keyed by a `P` with `dropZ P = P'`, with the same
      facts), `ninit_iff`, `nadded_iff`, `nreq_iff`, `nvuln_dnz_to_dn`, `nvuln_dn_to_dnz`.

  Design choices:
    * An ND summary of `DN` whose `dropZ` has ONE member is an ordinary summary of `DNz`. `DNz`
      applies it with `ret`, `DN` with the chain `ndOpen`/`ndBind`/`ndRet`. `summary_nd_fact`
      shows that `ret` gives the same fact in a layer that is not lower.
    * Z1 needs `ZeroLinks`. Without it `DN` can bind the zero member of a callee summary with a
      caller edge that has other premises (a caller fact with other premises whose binding
      gives the zero fact). `DNz` has no zero member to bind, so its edge does not have these
      premises, and the key `dropZ P` is not exact. `NDZeroThms.zeroLinks_of_noZeroGen` derives
      `ZeroLinks` from the program condition `NDZeroBase.NoZeroGen` and `NDZeroBase.AlphaZero`.
    * The layer in Z1. For an ND summary whose `dropZ` has one member, the `ret` of `DNz` can
      put the result in the demand layer where the chain of `DN` keeps it normal (the `* ∘ $`
      case and `lostCorr` of `applyEdge`, with an abstract added fact). So Z1 keeps the fact,
      not the layer. Z2 keeps the layer order: a normal `DNz` edge comes from a normal `DN` edge.
    * Z2 needs no such hypothesis: every zero member of a `DN` summary is bound by the caller
      zero edge (Z0), which adds only the zero fact to the joined list.

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.NDZ
import ApSpec.NDConfirmed
import ApSpec.Backward

namespace ApSpec.NDZero
open ApSpec ApSpec.ND ApSpec.NDZ

/-! ## Part 1. The hypotheses -/

/-- Every call passes the zero fact over (the zero base is not touched) and has the zero binding
    `zero.* → zero.*` (spec §3.5, §5.3). -/
def ZeroCalls (P : Program) : Prop :=
  ∀ M n c n', (M, n, Instr.call c, n') ∈ P.edges →
    memB zeroBase c.touched = false ∧ (zStar, zStar) ∈ c.toCallee

/-- Every conjunction sits beside an instruction edge of the program (the interpreter places the
    rule statement of a call beside the call, spec §5.3 step 3). -/
def ConjAdj (Q : NProg) : Prop :=
  ∀ M n cj n', (M, n, cj, n') ∈ Q.conjs → ∃ ins, (M, n, ins, n') ∈ Q.prog.edges

/-- A caller edge of `DN` whose binding gives an added fact that satisfies the zero premise has
    only zero premises (spec §3.5: the zero base of a callee is bound only by the zero binding
    from the caller zero fact). Only Z1 (`dn_to_dnz`) needs it. -/
def ZeroLinks (X : Ctx) : Prop :=
  ∀ M P n f n' c e a, (M, n, Instr.call c, n') ∈ X.Q.prog.edges → DN X (.nedge M P n f) →
    e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → applicable zeroFact a.fact = true →
    ∀ p, p ∈ P → p = zeroFact

/-! ## Part 2. The `dropZ` lemmas -/

/-- The filter of `dropZ`: the members that are not the zero fact. -/
def nz (P : List PFact) : List PFact := P.filter (fun i => i != zeroFact)

theorem bne_zero_false : (zeroFact != zeroFact) = false := bne_self_eq_false _

theorem bne_zero_true {i : PFact} (h : i ≠ zeroFact) : (i != zeroFact) = true := bne_iff_ne.mpr h

theorem nz_nil : nz [] = [] := rfl

theorem nz_cons_zero (P : List PFact) : nz (zeroFact :: P) = nz P := by
  unfold nz
  rw [List.filter_cons, bne_zero_false]
  rfl

theorem nz_cons_ne {i : PFact} (P : List PFact) (h : i ≠ zeroFact) : nz (i :: P) = i :: nz P := by
  unfold nz
  rw [List.filter_cons, bne_zero_true h]
  rfl

theorem nz_append (A B : List PFact) : nz (A ++ B) = nz A ++ nz B := List.filter_append ..

theorem mem_nz {i : PFact} {P : List PFact} : i ∈ nz P ↔ i ∈ P ∧ i ≠ zeroFact := by
  unfold nz
  rw [List.mem_filter, bne_iff_ne]

theorem nz_eq_nil_iff {P : List PFact} : nz P = [] ↔ ∀ p, p ∈ P → p = zeroFact := by
  induction P with
  | nil => exact ⟨fun _ _ h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | cons p P ih =>
    by_cases hp : p = zeroFact
    · subst hp
      rw [nz_cons_zero]
      refine ⟨fun h q hq => ?_, fun h => ih.mpr fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · rfl
      · exact ih.mp h q hq
    · rw [nz_cons_ne _ hp]
      exact ⟨fun h => absurd h (List.cons_ne_nil _ _), fun h => absurd (h p List.mem_cons_self) hp⟩

theorem nz_allZ {Z : List PFact} (h : ∀ p, p ∈ Z → p = zeroFact) : nz Z = [] := nz_eq_nil_iff.mpr h

theorem nz_nz (P : List PFact) : nz (nz P) = nz P := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    by_cases hp : p = zeroFact
    · subst hp
      rw [nz_cons_zero]
      exact ih
    · rw [nz_cons_ne _ hp, nz_cons_ne _ hp, ih]

theorem nz_single_zero : nz [zeroFact] = [] := nz_cons_zero []

/-- The two cases of `dropZ`. -/
theorem dropZ_cases (P : List PFact) :
    (nz P = [] ∧ dropZ P = [zeroFact]) ∨ (nz P ≠ [] ∧ dropZ P = nz P) := by
  cases h : nz P with
  | nil =>
    left
    refine ⟨rfl, ?_⟩
    unfold dropZ
    unfold nz at h
    rw [h]
  | cons x L =>
    right
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    unfold dropZ
    unfold nz at h
    rw [h]

theorem dropZ_of_nz_nil {P : List PFact} (h : nz P = []) : dropZ P = [zeroFact] := by
  rcases dropZ_cases P with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2
  · exact absurd h h1

theorem dropZ_of_nz_ne {P : List PFact} (h : nz P ≠ []) : dropZ P = nz P := by
  rcases dropZ_cases P with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact absurd h1 h
  · exact h2

/-- `dropZ` keeps the members that are not the zero fact. -/
theorem nz_dropZ (P : List PFact) : nz (dropZ P) = nz P := by
  rcases dropZ_cases P with ⟨h1, h2⟩ | ⟨_, h2⟩
  · rw [h2, h1]
    exact nz_single_zero
  · rw [h2, nz_nz]

/-- `dropZ` reads only the members that are not the zero fact. -/
theorem dropZ_eq_iff {P Q : List PFact} : dropZ P = dropZ Q ↔ nz P = nz Q := by
  constructor
  · intro h
    rw [← nz_dropZ P, ← nz_dropZ Q, h]
  · intro h
    unfold dropZ
    unfold nz at h
    rw [h]

/-- Idempotence. -/
theorem dropZ_idem (P : List PFact) : dropZ (dropZ P) = dropZ P :=
  dropZ_eq_iff.mpr (nz_dropZ P)

/-- The zero fact inside a list does not count. -/
theorem dropZ_append_zero (A B : List PFact) : dropZ (A ++ [zeroFact] ++ B) = dropZ (A ++ B) := by
  apply dropZ_eq_iff.mpr
  rw [nz_append, nz_append, nz_append, nz_single_zero, List.append_nil]

/-- `dropZ` of a join is `dropZ` of the joined `dropZ` lists. -/
theorem dropZ_dropZ_append (A B : List PFact) : dropZ (dropZ A ++ dropZ B) = dropZ (A ++ B) := by
  apply dropZ_eq_iff.mpr
  rw [nz_append, nz_append, nz_dropZ, nz_dropZ]

/-- Zero members appended to a list do not count. -/
theorem dropZ_append_allZ {P Z : List PFact} (hZ : ∀ p, p ∈ Z → p = zeroFact) :
    dropZ (P ++ Z) = dropZ P := by
  apply dropZ_eq_iff.mpr
  rw [nz_append, nz_allZ hZ, List.append_nil]

theorem dropZ_allZ_append {P Z : List PFact} (hZ : ∀ p, p ∈ Z → p = zeroFact) :
    dropZ (Z ++ P) = dropZ P := by
  apply dropZ_eq_iff.mpr
  rw [nz_append, nz_allZ hZ, List.nil_append]

theorem dropZ_ne_nil (P : List PFact) : dropZ P ≠ [] := by
  rcases dropZ_cases P with ⟨_, h2⟩ | ⟨h1, h2⟩
  · rw [h2]
    exact List.cons_ne_nil _ _
  · rw [h2]
    exact h1

theorem one_le_dropZ (P : List PFact) : 1 ≤ (dropZ P).length :=
  List.length_pos_iff.mpr (dropZ_ne_nil P)

/-- `dropZ` of a list with a member is not longer. -/
theorem dropZ_length_le {P : List PFact} (h : P ≠ []) : (dropZ P).length ≤ P.length := by
  rcases dropZ_cases P with ⟨_, h2⟩ | ⟨_, h2⟩
  · rw [h2]
    exact List.length_pos_iff.mpr h
  · rw [h2]
    exact List.length_filter_le _ _

/-- Membership: a member of `dropZ P` is a member of `P` that is not the zero fact, or the zero
    fact when every member of `P` is the zero fact. -/
theorem mem_dropZ {i : PFact} {P : List PFact} :
    i ∈ dropZ P ↔ (i ∈ P ∧ i ≠ zeroFact) ∨ (i = zeroFact ∧ ∀ p, p ∈ P → p = zeroFact) := by
  rcases dropZ_cases P with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, List.mem_singleton]
    have hall := nz_eq_nil_iff.mp h1
    constructor
    · intro hi
      exact .inr ⟨hi, hall⟩
    · rintro (⟨hi, hne⟩ | ⟨hi, _⟩)
      · exact absurd (hall i hi) hne
      · exact hi
  · rw [h2, mem_nz]
    constructor
    · exact .inl
    · rintro (h | ⟨_, hall⟩)
      · exact h
      · exact absurd (nz_eq_nil_iff.mpr hall) h1

theorem dropZ_eq_zero_iff {P : List PFact} : dropZ P = [zeroFact] ↔ ∀ p, p ∈ P → p = zeroFact := by
  rcases dropZ_cases P with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2]
    exact ⟨fun _ => nz_eq_nil_iff.mp h1, fun _ => rfl⟩
  · rw [h2]
    constructor
    · intro h
      have hz : zeroFact ∈ nz P := by rw [h]; exact List.mem_cons_self
      exact absurd rfl (mem_nz.mp hz).2
    · intro h
      exact absurd (nz_eq_nil_iff.mpr h) h1

/-- A member of `dropZ P` is a member of `P` (for a list with a member). -/
theorem mem_of_mem_dropZ {i : PFact} {P : List PFact} (hP : P ≠ []) (h : i ∈ dropZ P) : i ∈ P := by
  rcases mem_dropZ.mp h with ⟨hi, _⟩ | ⟨rfl, hall⟩
  · exact hi
  · obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil P hP
    rw [← hall p hp]
    exact hp

/-- A singleton is its own `dropZ`. -/
theorem dropZ_single (x : PFact) : dropZ [x] = [x] := by
  by_cases hx : x = zeroFact
  · subst hx
    exact dropZ_of_nz_nil nz_single_zero
  · have h : nz [x] = [x] := nz_cons_ne [] hx
    rw [dropZ_of_nz_ne (by rw [h]; exact List.cons_ne_nil _ _), h]

/-- A list with two or more members after the zero-drop has no zero member. -/
theorem two_le_dropZ {P : List PFact} (h : 2 ≤ (dropZ P).length) :
    dropZ P = nz P ∧ ∀ p, p ∈ dropZ P → p ≠ zeroFact := by
  rcases dropZ_cases P with ⟨_, h2⟩ | ⟨_, h2⟩
  · rw [h2] at h
    exact absurd h (by decide)
  · refine ⟨h2, fun p hp => ?_⟩
    rw [h2] at hp
    exact (mem_nz.mp hp).2

/-- A list without a zero member is its own `nz`. -/
theorem nz_of_noZ {P : List PFact} (h : ∀ p, p ∈ P → p ≠ zeroFact) : nz P = P := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    rw [nz_cons_ne _ (h p List.mem_cons_self),
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- A split of a list along the first member that is not the zero fact. -/
theorem nz_eq_cons {P : List PFact} {x : PFact} {L : List PFact} (h : nz P = x :: L) :
    ∃ zs tail, P = zs ++ x :: tail ∧ (∀ z, z ∈ zs → z = zeroFact) ∧ nz tail = L ∧ x ≠ zeroFact := by
  induction P with
  | nil => exact absurd h (List.cons_ne_nil _ _).symm
  | cons p P ih =>
    by_cases hp : p = zeroFact
    · subst hp
      rw [nz_cons_zero] at h
      obtain ⟨zs, tail, rfl, hz, ht, hx⟩ := ih h
      refine ⟨zeroFact :: zs, tail, rfl, fun z hz' => ?_, ht, hx⟩
      rcases List.mem_cons.mp hz' with rfl | hz'
      · rfl
      · exact hz z hz'
    · rw [nz_cons_ne _ hp] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact ⟨[], P, rfl, fun _ h => absurd h List.not_mem_nil, rfl, hp⟩

/-- A list whose `dropZ` is one member `j`: zero members around one `j`. -/
theorem dropZ_eq_single {P : List PFact} {j : PFact} (hP : P ≠ []) (h : dropZ P = [j]) :
    ∃ zs ws, P = zs ++ j :: ws ∧ (∀ z, z ∈ zs → z = zeroFact) ∧ (∀ z, z ∈ ws → z = zeroFact) := by
  rcases dropZ_cases P with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    have hall := nz_eq_nil_iff.mp h1
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hP
    have hx := hall x List.mem_cons_self
    subst hx
    exact ⟨[], xs, rfl, fun _ h => absurd h List.not_mem_nil,
      fun z hz => hall z (List.mem_cons_of_mem _ hz)⟩
  · rw [h2] at h
    obtain ⟨zs, tail, rfl, hz, ht, _⟩ := nz_eq_cons h
    exact ⟨zs, tail, rfl, hz, nz_eq_nil_iff.mp ht⟩

#print axioms dropZ_idem
#print axioms dropZ_append_zero
#print axioms dropZ_dropZ_append
#print axioms mem_dropZ

/-! ## Part 3. Z0: the zero fact is everywhere -/

section Zero

/-- The zero binding takes the zero fact to the zero fact. -/
theorem zero_bind_eq : applyEdge Backward.zeroAF zStar zStar = ⟨[Backward.zeroAF], []⟩ := rfl

theorem zero_bind : Backward.zeroAF ∈ (applyEdge Backward.zeroAF zStar zStar).facts := by
  rw [zero_bind_eq]
  exact List.mem_singleton_self _

/-- The zero keep edge takes the zero fact to the zero fact. -/
theorem zero_keep_eq : applyEdge Backward.zeroAF zeroFact zeroFact = ⟨[Backward.zeroAF], []⟩ := rfl

/-- A statement that keeps the zero fact (S11 (d)) passes it. -/
theorem zero_transfer {s : Stmt} (h : memB zeroBase s.touched = true → (zeroFact, zeroFact) ∈ s.edges)
    (counted : Acc → Bool) (L : Nat) : Backward.zeroAF ∈ (transfer counted L s Backward.zeroAF).facts := by
  unfold transfer
  cases ht : memB Backward.zeroAF.fact.base s.touched with
  | false => exact List.Mem.head _
  | true =>
    show Backward.zeroAF ∈ (applyAll Backward.zeroAF s.edges).facts.map (limitF counted L)
    refine List.mem_map.mpr ⟨Backward.zeroAF, Backward.mem_applyAll (h ht) ?_, Backward.limitF_zero counted L⟩
    rw [zero_keep_eq]
    exact List.mem_singleton_self _

theorem applicable_zero_zero : applicable zeroFact zeroFact = true := rfl

variable {X : Ctx}

/-- The zero edge passes every instruction edge. -/
theorem zero_instr (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) {M : MethodId}
    {n n' : Node} {ins : Instr} (he : (M, n, ins, n') ∈ X.Q.prog.edges)
    (h : DN X (.nedge M [zeroFact] n Backward.zeroAF)) : DN X (.nedge M [zeroFact] n' Backward.zeroAF) := by
  cases ins with
  | stmt s => exact DN.step h he (zero_transfer (hZ.stmt _ _ _ _ he) _ _)
  | call c => exact DN.pass h he (hC _ _ _ _ he).1
  | clean cl => exact DN.clean h he (Backward.zero_clean (hZ.clean _ _ _ _ he))
  | filt b may => exact DN.filt h he (fun hb => hZ.filt _ _ _ _ _ he hb.symm)

theorem zero_instr_z (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) {M : MethodId}
    {n n' : Node} {ins : Instr} (he : (M, n, ins, n') ∈ X.Q.prog.edges)
    (h : DNz X (.nedge M [zeroFact] n Backward.zeroAF)) : DNz X (.nedge M [zeroFact] n' Backward.zeroAF) := by
  cases ins with
  | stmt s => exact DNz.step h he (zero_transfer (hZ.stmt _ _ _ _ he) _ _)
  | call c => exact DNz.pass h he (hC _ _ _ _ he).1
  | clean cl => exact DNz.clean h he (Backward.zero_clean (hZ.clean _ _ _ _ he))
  | filt b may => exact DNz.filt h he (fun hb => hZ.filt _ _ _ _ _ he hb.symm)

/-- The motive of Z0 for `DN`. An edge at `n`: the zero initial fact of its method and the zero
    edge at `n`. An initial fact or an added fact: the zero initial fact. A partial match: its
    call edge, and the zero facts at its call node, or no caller edge is bound yet. -/
def ZDN (X : Ctx) : NObj → Prop
  | .ninit M _ => DN X (.ninit M zeroFact)
  | .nadded M _ => DN X (.ninit M zeroFact)
  | .nedge M _ n _ => DN X (.ninit M zeroFact) ∧ DN X (.nedge M [zeroFact] n Backward.zeroAF)
  | .npart M n c n' rest P _ => (M, n, Instr.call c, n') ∈ X.Q.prog.edges ∧
      ((DN X (.ninit M zeroFact) ∧ DN X (.nedge M [zeroFact] n Backward.zeroAF)) ∨ (P = [] ∧ 2 ≤ rest.length))
  | _ => True

/-- The motive of Z0 for `DNz`. -/
def ZDNz (X : Ctx) : NObj → Prop
  | .ninit M _ => DNz X (.ninit M zeroFact)
  | .nadded M _ => DNz X (.ninit M zeroFact)
  | .nedge M _ n _ => DNz X (.ninit M zeroFact) ∧ DNz X (.nedge M [zeroFact] n Backward.zeroAF)
  | .npart M n c n' rest P _ => (M, n, Instr.call c, n') ∈ X.Q.prog.edges ∧
      ((DNz X (.ninit M zeroFact) ∧ DNz X (.nedge M [zeroFact] n Backward.zeroAF)) ∨ (P = [] ∧ 2 ≤ rest.length))
  | _ => True

/-- Z0 (THE ZERO FACT IS EVERYWHERE), for `DN`. The zero fact passes every instruction
    (`ZeroKept`), passes over every call and enters every callee through `zStar` (`ZeroCalls`),
    and the abstraction serves it by itself. -/
theorem zero_everywhere (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {o : NObj} (h : DN X o) :
    ZDN X o := by
  induction h with
  | root hM => exact DN.root hM
  | start _ ih => exact ⟨ih, DN.start ih⟩
  | step _ he _ ih => exact ⟨ih.1, zero_instr hZ hC he ih.2⟩
  | reqStmt => trivial
  | pass _ he _ ih => exact ⟨ih.1, zero_instr hZ hC he ih.2⟩
  | @added M P n f n' c e a _ he _ _ ih =>
    show DN X (.ninit c.callee zeroFact)
    have h1 : DN X (.nadded c.callee zeroFact) := DN.added ih.2 he (hC _ _ _ _ he).2 zero_bind
    have h2 := DN.initA h1
    rw [hαz] at h2
    exact h2
  | initA _ ih => exact ih
  | ret _ he _ _ _ _ _ _ _ _ ih _ _ => exact ⟨ih.1, zero_instr hZ hC he ih.2⟩
  | ndOpen he _ h2 _ => exact ⟨he, .inr ⟨rfl, h2⟩⟩
  | ndBind _ _ _ _ _ ihp ihf => exact ⟨ihp.1, .inl ihf⟩
  | ndRet _ _ _ ih =>
    obtain ⟨he, hz | ⟨_, hl⟩⟩ := ih
    · exact ⟨hz.1, zero_instr hZ hC he hz.2⟩
    · exact absurd hl (by decide)
  | reqSink => trivial
  | answer _ _ _ _ _ iha => exact iha
  | reqUp => trivial
  | vuln => trivial
  | clean _ he _ ih => exact ⟨ih.1, zero_instr hZ hC he ih.2⟩
  | reqClean => trivial
  | filt _ he _ ih => exact ⟨ih.1, zero_instr hZ hC he ih.2⟩
  | conj _ _ hcj _ _ _ _ ih1 _ =>
    obtain ⟨_, hins⟩ := hA _ _ _ _ hcj
    exact ⟨ih1.1, zero_instr hZ hC hins ih1.2⟩
  | reqConj => trivial

#print axioms zero_everywhere

/-- Z0 for `DNz` (the same proof). -/
theorem zero_everywhere_z (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {o : NObj} (h : DNz X o) :
    ZDNz X o := by
  induction h with
  | root hM => exact DNz.root hM
  | start _ ih => exact ⟨ih, DNz.start ih⟩
  | step _ he _ ih => exact ⟨ih.1, zero_instr_z hZ hC he ih.2⟩
  | reqStmt => trivial
  | pass _ he _ ih => exact ⟨ih.1, zero_instr_z hZ hC he ih.2⟩
  | @added M P n f n' c e a _ he _ _ ih =>
    show DNz X (.ninit c.callee zeroFact)
    have h1 : DNz X (.nadded c.callee zeroFact) := DNz.added ih.2 he (hC _ _ _ _ he).2 zero_bind
    have h2 := DNz.initA h1
    rw [hαz] at h2
    exact h2
  | initA _ ih => exact ih
  | ret _ he _ _ _ _ _ _ _ _ ih _ _ => exact ⟨ih.1, zero_instr_z hZ hC he ih.2⟩
  | ndOpen he _ h2 _ => exact ⟨he, .inr ⟨rfl, h2⟩⟩
  | ndBind _ _ _ _ _ ihp ihf => exact ⟨ihp.1, .inl ihf⟩
  | ndRet _ _ _ ih =>
    obtain ⟨he, hz | ⟨_, hl⟩⟩ := ih
    · exact ⟨hz.1, zero_instr_z hZ hC he hz.2⟩
    · exact absurd hl (by decide)
  | reqSink => trivial
  | answer _ _ _ _ _ iha => exact iha
  | reqUp => trivial
  | vuln => trivial
  | clean _ he _ ih => exact ⟨ih.1, zero_instr_z hZ hC he ih.2⟩
  | reqClean => trivial
  | filt _ he _ ih => exact ⟨ih.1, zero_instr_z hZ hC he ih.2⟩
  | conj _ _ hcj _ _ _ _ ih1 _ =>
    obtain ⟨_, hins⟩ := hA _ _ _ _ hcj
    exact ⟨ih1.1, zero_instr_z hZ hC hins ih1.2⟩
  | reqConj => trivial

#print axioms zero_everywhere_z

/-- Z0, the forms per object (`DN`): an edge gives the zero edge at its node. -/
theorem zero_edge (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (h : DN X (.nedge M P n f)) : DN X (.nedge M [zeroFact] n Backward.zeroAF) :=
  (zero_everywhere hZ hC hA hαz h).2

theorem zero_init_of_edge (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P : List PFact}
    {n : Node} {f : AFact} (h : DN X (.nedge M P n f)) : DN X (.ninit M zeroFact) :=
  (zero_everywhere hZ hC hA hαz h).1

theorem zero_init (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {i : PFact}
    (h : DN X (.ninit M i)) : DN X (.ninit M zeroFact) :=
  zero_everywhere hZ hC hA hαz h

theorem zero_init_of_added (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {a : PFact}
    (h : DN X (.nadded M a)) : DN X (.ninit M zeroFact) :=
  zero_everywhere hZ hC hA hαz h

/-- A partial match with a bound caller edge gives the zero edge at its call node. -/
theorem zero_edge_of_part (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {n n' : Node}
    {c : Call} {rest P : List PFact} {g : AFact} (h : DN X (.npart M n c n' rest P g))
    (hP : P ≠ []) : DN X (.nedge M [zeroFact] n Backward.zeroAF) := by
  obtain ⟨_, hz | ⟨hP0, _⟩⟩ := zero_everywhere hZ hC hA hαz h
  · exact hz.2
  · exact absurd hP0 hP

/-- The zero fact enters the callee of every call that an edge reaches. -/
theorem zero_callee (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P : List PFact} {n n' : Node}
    {f : AFact} {c : Call} (h : DN X (.nedge M P n f)) (he : (M, n, Instr.call c, n') ∈ X.Q.prog.edges) :
    DN X (.ninit c.callee zeroFact) := by
  have h1 : DN X (.nadded c.callee zeroFact) :=
    DN.added (zero_edge hZ hC hA hαz h) he (hC _ _ _ _ he).2 zero_bind
  have h2 := DN.initA h1
  rw [hαz] at h2
  exact h2

/-- Z0, the forms per object (`DNz`). -/
theorem zero_edge_z (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (h : DNz X (.nedge M P n f)) : DNz X (.nedge M [zeroFact] n Backward.zeroAF) :=
  (zero_everywhere_z hZ hC hA hαz h).2

theorem zero_init_z (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog) (hA : ConjAdj X.Q)
    (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {i : PFact}
    (h : DNz X (.ninit M i)) : DNz X (.ninit M zeroFact) :=
  zero_everywhere_z hZ hC hA hαz h

theorem zero_init_of_edge_z (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P : List PFact}
    {n : Node} {f : AFact} (h : DNz X (.nedge M P n f)) : DNz X (.ninit M zeroFact) :=
  (zero_everywhere_z hZ hC hA hαz h).1

theorem zero_init_of_added_z (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {a : PFact}
    (h : DNz X (.nadded M a)) : DNz X (.ninit M zeroFact) :=
  zero_everywhere_z hZ hC hA hαz h

theorem zero_edge_of_part_z (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {n n' : Node}
    {c : Call} {rest P : List PFact} {g : AFact} (h : DNz X (.npart M n c n' rest P g))
    (hP : P ≠ []) : DNz X (.nedge M [zeroFact] n Backward.zeroAF) := by
  obtain ⟨_, hz | ⟨hP0, _⟩⟩ := zero_everywhere_z hZ hC hA hαz h
  · exact hz.2
  · exact absurd hP0 hP

theorem zero_callee_z (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P : List PFact}
    {n n' : Node} {f : AFact} {c : Call} (h : DNz X (.nedge M P n f))
    (he : (M, n, Instr.call c, n') ∈ X.Q.prog.edges) : DNz X (.ninit c.callee zeroFact) := by
  have h1 : DNz X (.nadded c.callee zeroFact) :=
    DNz.added (zero_edge_z hZ hC hA hαz h) he (hC _ _ _ _ he).2 zero_bind
  have h2 := DNz.initA h1
  rw [hαz] at h2
  exact h2

end Zero

/-! ## Part 4. The layer correspondence -/

section Corr

/-- The layer order: the layer `b` is not higher than the layer `b'`. -/
abbrev DLe (b b' : Bool) : Prop := b = true → b' = true

theorem DLe.refl (b : Bool) : DLe b b := id

theorem DLe.or {a b a' b' : Bool} (h1 : DLe a a') (h2 : DLe b b') : DLe (a || b) (a' || b') := by
  revert h1 h2
  cases a <;> cases b <;> cases a' <;> cases b' <;> decide

theorem DLe.or_right {a a' : Bool} (b : Bool) (h : DLe a a') : DLe (a || b) (a' || b) :=
  DLe.or h (DLe.refl b)

/-- Two final facts CORRESPOND: the same fact, and the same layer or a concrete mark. -/
abbrev Corr (f f' : AFact) : Prop :=
  f.fact = f'.fact ∧ (f.demand = f'.demand ∨ ∃ t, f.fact.mark = .conc t)

/-- The results `r`, `r'` of the inputs `c`, `c'` correspond, and they keep the layer order of
    the inputs, in both directions. -/
abbrev CorrK (c c' r r' : AFact) : Prop :=
  Corr r r' ∧ (DLe c.demand c'.demand → DLe r.demand r'.demand) ∧
    (DLe c'.demand c.demand → DLe r'.demand r.demand)

theorem corr_refl (f : AFact) : Corr f f := ⟨rfl, .inl rfl⟩

theorem corr_symm {f f' : AFact} (h : Corr f f') : Corr f' f := by
  refine ⟨h.1.symm, ?_⟩
  rcases h.2 with h2 | ⟨t, ht⟩
  · exact .inl h2.symm
  · exact .inr ⟨t, by rw [← h.1]; exact ht⟩

theorem corr_conc {f f' : AFact} (h : f.fact = f'.fact) (hc : ∃ t, f.fact.mark = .conc t) :
    Corr f f' := ⟨h, .inr hc⟩

theorem corrK_self {c c' : AFact} (h : Corr c c') : CorrK c c' c c' := ⟨h, id, id⟩

theorem corrK_trans {c c' x x' r r' : AFact} (h1 : CorrK c c' x x') (h2 : CorrK x x' r r') :
    CorrK c c' r r' :=
  ⟨h2.1, fun h => h2.2.1 (h1.2.1 h), fun h => h2.2.2 (h1.2.2 h)⟩

/-- For a concrete mark the normal form does not read the layer. -/
theorem norm_corr (x : PFact) (d d' : Bool) (h : d = d' ∨ ∃ t, x.mark = .conc t) :
    CorrK ⟨x, d⟩ ⟨x, d'⟩ (AFact.norm ⟨x, d⟩) (AFact.norm ⟨x, d'⟩) := by
  rcases h with rfl | ⟨t, ht⟩
  · exact ⟨corr_refl _, fun _ h => h, fun _ h => h⟩
  · obtain ⟨b, p, k, m⟩ := x
    change m = .conc t at ht
    subst ht
    cases k with
    | star e =>
      cases e with
      | univ => exact ⟨⟨rfl, .inl rfl⟩, fun _ => id, fun _ => id⟩
      | set xs => exact ⟨⟨rfl, .inl rfl⟩, fun _ => id, fun _ => id⟩
    | any => exact ⟨⟨rfl, .inr ⟨t, rfl⟩⟩, id, id⟩
    | exact => exact ⟨⟨rfl, .inr ⟨t, rfl⟩⟩, id, id⟩

/-- The normal form of a fact without a `*` tail is the fact. -/
theorem norm_of_nonstar {x : PFact} (d : Bool) (h : x.kind.isStar = false) :
    AFact.norm ⟨x, d⟩ = ⟨x, d⟩ := by
  obtain ⟨b, p, k, m⟩ := x
  cases k with
  | star e => cases h
  | any => rfl
  | exact => rfl

/-- The normal form never lowers the layer. -/
theorem norm_demand_ge (x : PFact) (d : Bool) : DLe d (AFact.norm ⟨x, d⟩).demand := by
  intro hd
  subst hd
  obtain ⟨b, p, k, m⟩ := x
  cases k with
  | star e => cases e <;> cases m <;> rfl
  | any => rfl
  | exact => rfl

theorem applyEdge_beq {c r : AFact} {fr to : PFact} (h : r ∈ (applyEdge c fr to).facts) :
    Nat.beq c.fact.base fr.base = true := by
  rw [CoreAux.applyEdge_eq] at h
  cases hb : Nat.beq c.fact.base fr.base with
  | false =>
    rw [hb, if_neg Bool.false_ne_true] at h
    exact absurd h List.not_mem_nil
  | true => rfl

theorem mem_applyEdge_of {c : AFact} {fr to : PFact} {p : List Acc} {k : Kind} {ap : Bool}
    {m : MarkA} (hb : Nat.beq c.fact.base fr.base = true)
    (hg : CoreAux.geo c.fact.kind fr.kind fr.path c.fact.path to.path to.kind = some (p, k, ap))
    (hgt : markGate fr.mark c.fact.mark = .ok) (hmc : markComp to.mark c.fact.mark = some m) :
    AFact.norm ⟨⟨to.base, p, k, m⟩, c.demand || ap⟩ ∈ (applyEdge c fr to).facts := by
  rw [CoreAux.applyEdge_eq, hb, if_pos rfl, hg, CoreAux.fin_some, hgt, CoreAux.finG_ok, hmc]
  exact List.mem_singleton_self _

/-- `applyEdge` keeps the correspondence. -/
theorem applyEdge_corr {c c' r : AFact} {fr to : PFact} (hc : Corr c c')
    (hr : r ∈ (applyEdge c fr to).facts) :
    ∃ r', r' ∈ (applyEdge c' fr to).facts ∧ CorrK c c' r r' := by
  obtain ⟨cf, cd⟩ := c
  obtain ⟨cf', cd'⟩ := c'
  obtain ⟨hf, hd⟩ := hc
  change cf = cf' at hf
  subst hf
  have hb := applyEdge_beq hr
  obtain ⟨p, k, ap, m, hg, hgt, hmc, rfl⟩ := CoreAux.mem_applyEdge_facts_inv hr
  refine ⟨_, mem_applyEdge_of (c := ⟨cf, cd'⟩) hb hg hgt hmc, ?_⟩
  have hcor : (cd || ap) = (cd' || ap) ∨ ∃ t, (⟨to.base, p, k, m⟩ : PFact).mark = .conc t := by
    rcases hd with hd | ⟨t, ht⟩
    · change cd = cd' at hd
      rw [hd]
      exact .inl rfl
    · right
      change cf.mark = .conc t at ht
      change markComp to.mark cf.mark = some m at hmc
      rw [ht] at hmc
      obtain ⟨t', ht'⟩ := CoreAux.markComp_conc hmc
      exact ⟨t', ht'⟩
  obtain ⟨hC, h1, h2⟩ := norm_corr ⟨to.base, p, k, m⟩ (cd || ap) (cd' || ap) hcor
  exact ⟨hC, fun hle => h1 (DLe.or_right ap hle), fun hle => h2 (DLe.or_right ap hle)⟩

theorem applyAll_corr {c c' r : AFact} (hc : Corr c c') :
    ∀ {es : List MicroEdge}, r ∈ (applyAll c es).facts →
      ∃ r', r' ∈ (applyAll c' es).facts ∧ CorrK c c' r r'
  | [], h => absurd h List.not_mem_nil
  | _ :: _, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨r', hr', hk⟩ := applyEdge_corr hc h
      exact ⟨r', List.mem_append_left _ hr', hk⟩
    · obtain ⟨r', hr', hk⟩ := applyAll_corr hc h
      exact ⟨r', List.mem_append_right _ hr', hk⟩

theorem limitF_corr (counted : Acc → Bool) (L : Nat) {f f' : AFact} (h : Corr f f') :
    CorrK f f' (limitF counted L f) (limitF counted L f') := by
  obtain ⟨ff, fd⟩ := f
  obtain ⟨ff', fd'⟩ := f'
  obtain ⟨hf, hd⟩ := h
  change ff = ff' at hf
  subst hf
  unfold limitF
  dsimp only
  cases cutPath counted L ff.path with
  | none => exact ⟨⟨rfl, hd⟩, id, id⟩
  | some p => exact ⟨⟨rfl, .inl rfl⟩, fun _ => id, fun _ => id⟩

/-- The statement transfer keeps the correspondence. -/
theorem transfer_corr {counted : Acc → Bool} {L : Nat} {s : Stmt} {c c' r : AFact}
    (hc : Corr c c') (hr : r ∈ (transfer counted L s c).facts) :
    ∃ r', r' ∈ (transfer counted L s c').facts ∧ CorrK c c' r r' := by
  have hb : c'.fact.base = c.fact.base := by rw [hc.1]
  unfold transfer at hr ⊢
  rw [hb]
  split at hr
  · rename_i ht
    rw [if_pos ht]
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    obtain ⟨x', hx', hk⟩ := applyAll_corr hc hx
    exact ⟨_, List.mem_map_of_mem hx', corrK_trans hk (limitF_corr counted L hk.1)⟩
  · rename_i ht
    rw [if_neg ht]
    rw [List.mem_singleton.mp hr]
    exact ⟨c', List.mem_singleton_self _, corrK_self hc⟩

/-- The cleaner keeps the correspondence. -/
theorem cleanRes_corr {cl : Cleaner} {c c' r : AFact} (hc : Corr c c')
    (hr : r ∈ (cleanRes cl c).facts) :
    ∃ r', r' ∈ (cleanRes cl c').facts ∧ CorrK c c' r r' := by
  obtain ⟨cf, cd⟩ := c
  obtain ⟨cf', cd'⟩ := c'
  obtain ⟨hf, hd⟩ := hc
  change cf = cf' at hf
  subst hf
  rcases hd with hd | ⟨t, ht⟩
  · change cd = cd' at hd
    subst hd
    exact ⟨r, hr, corr_refl _, fun _ h => h, fun _ h => h⟩
  · change cf.mark = .conc t at ht
    unfold cleanRes at hr ⊢
    dsimp only at hr ⊢
    rw [ht] at hr ⊢
    dsimp only at hr ⊢
    cases hpos : cleanPos cl cf with
    | disjoint =>
      rw [hpos] at hr
      dsimp only
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, ⟨rfl, .inr ⟨t, ht⟩⟩, id, id⟩
    | inside =>
      rw [hpos] at hr
      dsimp only at hr ⊢
      cases hm : cl.markB t with
      | true =>
        rw [hm, if_pos rfl] at hr
        exact absurd hr List.not_mem_nil
      | false =>
        rw [hm, if_neg Bool.false_ne_true] at hr
        rw [if_neg Bool.false_ne_true]
        rw [List.mem_singleton.mp hr]
        exact ⟨_, List.mem_singleton_self _, ⟨rfl, .inr ⟨t, ht⟩⟩, id, id⟩
    | part =>
      rw [hpos] at hr
      dsimp only at hr ⊢
      cases hm : cl.markB t with
      | true =>
        rw [hm, if_pos rfl] at hr
        rw [if_pos rfl]
        rw [List.mem_singleton.mp hr]
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        unfold concPart
        dsimp only
        split
        · exact ⟨⟨rfl, .inr ⟨t, ht⟩⟩, id, id⟩
        · exact ⟨⟨rfl, .inl rfl⟩, fun _ => id, fun _ => id⟩
      | false =>
        rw [hm, if_neg Bool.false_ne_true] at hr
        rw [if_neg Bool.false_ne_true]
        rw [List.mem_singleton.mp hr]
        exact ⟨_, List.mem_singleton_self _, ⟨rfl, .inr ⟨t, ht⟩⟩, id, id⟩

/-- The summary application keeps the correspondence of the added fact and of the summary. -/
theorem applySummary_corr {a a' g g' r : AFact} {j : PFact} (ha : Corr a a') (hg : Corr g g')
    (hr : r ∈ (applySummary a j g).facts) :
    ∃ r', r' ∈ (applySummary a' j g').facts ∧ Corr r r' ∧
      (DLe a.demand a'.demand → DLe g.demand g'.demand → DLe r.demand r'.demand) ∧
      (DLe a'.demand a.demand → DLe g'.demand g.demand → DLe r'.demand r.demand) := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  have hx0 := hx
  rw [hg.1] at hx
  obtain ⟨x', hx', hxc, hx1, hx2⟩ := applyEdge_corr ha hx
  have hcor : (x.demand || g.demand) = (x'.demand || g'.demand) ∨ ∃ t, x.fact.mark = .conc t := by
    rcases hxc.2 with hxd | hxt
    · rcases hg.2 with hgd | ⟨T, hT⟩
      · left
        rw [hxd, hgd]
      · right
        have hm := CoreAux.mem_applyEdge_facts hx0
        rw [hT] at hm
        exact ⟨T, (Option.some.inj hm).symm⟩
    · exact .inr hxt
  refine ⟨AFact.norm ⟨x'.fact, x'.demand || g'.demand⟩, List.mem_map_of_mem hx', ?_⟩
  rw [← hxc.1]
  obtain ⟨hC, h1, h2⟩ := norm_corr x.fact (x.demand || g.demand) (x'.demand || g'.demand) hcor
  exact ⟨hC, fun ha' hg' => h1 (DLe.or (hx1 ha') hg'), fun ha' hg' => h2 (DLe.or (hx2 ha') hg')⟩

/-- The conjunction keeps the correspondence (its target has a concrete mark). -/
theorem conjFact_corr {cj : Conj} {f1 f1' f2 f2' : AFact} (h1 : f1.fact = f1'.fact)
    (h2 : f2.fact = f2'.fact) (hT : ∃ T, cj.target.mark = .conc T) :
    Corr (conjFact cj f1 f2) (conjFact cj f1' f2') ∧
      (DLe f1.demand f1'.demand → DLe f2.demand f2'.demand →
        DLe (conjFact cj f1 f2).demand (conjFact cj f1' f2').demand) := by
  refine ⟨⟨rfl, .inr hT⟩, fun d1 d2 => ?_⟩
  show DLe (conjLayer cj f1 f2) (conjLayer cj f1' f2')
  unfold conjLayer
  rw [h1, h2]
  exact DLe.or_right _ (DLe.or_right _ (DLe.or d1 d2))

/-- The sink check reads the fact, not the layer. -/
theorem check_corr {i s : PFact} {f f' : AFact} (h : f.fact = f'.fact) :
    check i f s = check i f' s := by
  obtain ⟨ff, fd⟩ := f
  obtain ⟨ff', fd'⟩ := f'
  change ff = ff' at h
  subst h
  rfl

/-- The requests of `applyEdge` read the fact, not the layer. -/
theorem applyEdge_reqs_corr {c c' : AFact} {fr to : PFact} (h : c.fact = c'.fact) :
    (applyEdge c fr to).reqs = (applyEdge c' fr to).reqs := by
  obtain ⟨cf, cd⟩ := c
  obtain ⟨cf', cd'⟩ := c'
  change cf = cf' at h
  subst h
  rw [CoreAux.applyEdge_eq, CoreAux.applyEdge_eq]
  dsimp only
  cases Nat.beq cf.base fr.base with
  | false => rfl
  | true =>
    show (CoreAux.fin _ fr to _).reqs = (CoreAux.fin _ fr to _).reqs
    cases CoreAux.geo cf.kind fr.kind fr.path cf.path to.path to.kind with
    | none => rfl
    | some x =>
      obtain ⟨p, k, ap⟩ := x
      rw [CoreAux.fin_some, CoreAux.fin_some]
      dsimp only
      cases markGate fr.mark cf.mark with
      | ok =>
        rw [CoreAux.finG_ok, CoreAux.finG_ok]
        dsimp only
        cases markComp to.mark cf.mark <;> rfl
      | no => rfl
      | req t => rfl

theorem applyAll_reqs_corr {c c' : AFact} (h : c.fact = c'.fact) :
    ∀ {es : List MicroEdge}, (applyAll c es).reqs = (applyAll c' es).reqs
  | [] => rfl
  | e :: es => by
    show (applyEdge c e.1 e.2).reqs ++ (applyAll c es).reqs =
      (applyEdge c' e.1 e.2).reqs ++ (applyAll c' es).reqs
    rw [applyEdge_reqs_corr h, applyAll_reqs_corr h]

theorem transfer_reqs_corr {counted : Acc → Bool} {L : Nat} {s : Stmt} {c c' : AFact}
    (h : c.fact = c'.fact) : (transfer counted L s c).reqs = (transfer counted L s c').reqs := by
  unfold transfer
  rw [h]
  split
  · exact applyAll_reqs_corr h
  · rfl

theorem cleanRes_reqs_corr {cl : Cleaner} {c c' : AFact} (h : c.fact = c'.fact) :
    (cleanRes cl c).reqs = (cleanRes cl c').reqs := by
  obtain ⟨cf, cd⟩ := c
  obtain ⟨cf', cd'⟩ := c'
  change cf = cf' at h
  subst h
  unfold cleanRes
  dsimp only
  cases cleanPos cl cf with
  | disjoint => rfl
  | inside =>
    dsimp only
    split
    · split <;> rfl
    · rfl
    · rfl
  | part =>
    dsimp only
    split
    · split <;> rfl
    · rfl
    · rfl

/-! ### An ND conclusion applied as a single-premise summary -/

theorem belowCase_nonstar {ck fk tk : Kind} {r toPath p : List Acc} {k : Kind} {ap : Bool}
    (h : belowCase ck fk r toPath tk = some (p, k, ap)) (htk : tk.isStar = false) :
    p = toPath ∧ (k = tk ∨ (k = .star .univ ∧ tk = .exact)) := by
  unfold belowCase at h
  split at h
  · cases tk with
    | star _ => cases htk
    | any =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, .inl rfl⟩
    | exact =>
      dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨rfl, .inl rfl⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ⟨rfl, .inl rfl⟩
  · cases h

theorem aboveCase_nonstar {ck fk tk : Kind} {r toPath p : List Acc} {k : Kind} {ap : Bool}
    (h : aboveCase ck fk r toPath tk = some (p, k, ap)) (htk : tk.isStar = false) :
    p = toPath ∧ k = tk := by
  unfold aboveCase at h
  split at h
  · cases tk with
    | star _ => cases htk
    | any =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, rfl⟩
    | exact =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨rfl, rfl⟩
  · cases h

theorem geo_nonstar {ck fk tk : Kind} {P q toPath p : List Acc} {k : Kind} {ap : Bool}
    (h : CoreAux.geo ck fk P q toPath tk = some (p, k, ap)) (htk : tk.isStar = false) :
    p = toPath ∧ (k = tk ∨ (k = .star .univ ∧ tk = .exact)) := by
  unfold CoreAux.geo at h
  split at h
  · exact belowCase_nonstar h htk
  · obtain ⟨h1, h2⟩ := aboveCase_nonstar h htk
    exact ⟨h1, .inl h2⟩
  · cases h

/-- An ND conclusion (a concrete mark, no `*` tail) applied as a single-premise summary gives
    the conclusion itself, in the layer of the added fact and of the summary or higher (the Lean
    `applyEdge` can add the demand layer: the case `*` on `$` with the empty position). -/
theorem summary_nd_fact {a g r : AFact} {j : PFact} (hT : ∃ T, g.fact.mark = .conc T)
    (hk : g.fact.kind.isStar = false) (hr : r ∈ (applySummary a j g).facts) :
    r.fact = g.fact ∧ DLe (a.demand || g.demand) r.demand := by
  obtain ⟨⟨gb, gp, gk, gm⟩, gd⟩ := g
  obtain ⟨T, hT⟩ := hT
  change gm = .conc T at hT
  subst hT
  change gk.isStar = false at hk
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  obtain ⟨p, k, ap, m, hg, _, hmc, rfl⟩ := CoreAux.mem_applyEdge_facts_inv hx
  change markComp (.conc T) a.fact.mark = some m at hmc
  have hm : m = .conc T := (Option.some.inj hmc).symm
  subst hm
  obtain ⟨hp, hkk⟩ := geo_nonstar hg hk
  change p = gp at hp
  subst hp
  have hdl : DLe (a.demand || gd) ((a.demand || ap) || gd) :=
    DLe.or_right gd (fun h => by rw [h]; rfl)
  cases gk with
  | star e => cases hk
  | any =>
    rcases hkk with hkk | ⟨_, hgk⟩
    · change k = .any at hkk
      subst hkk
      exact ⟨rfl, hdl⟩
    · cases hgk
  | exact =>
    rcases hkk with hkk | ⟨hkk, _⟩
    · change k = .exact at hkk
      subst hkk
      exact ⟨rfl, hdl⟩
    · change k = .star .univ at hkk
      subst hkk
      exact ⟨rfl, fun _ => rfl⟩

/-- An ND conclusion applied as a single-premise summary always gives a result. -/
theorem summary_nd_exists {a g : AFact} {j : PFact} (hap : applicable j a.fact = true)
    (hT : ∃ T, g.fact.mark = .conc T) (hk : g.fact.kind.isStar = false) :
    ∃ r, r ∈ (applySummary a j g).facts := by
  obtain ⟨l1, hl1⟩ := NDExact.covers_nonempty a.fact
  obtain ⟨l2, hl2⟩ := NDExact.covers_nonempty g.fact
  obtain ⟨T, hT⟩ := hT
  have hdg : den j g.fact l1 l2 :=
    NDExact.den_uncorr (by rw [hT]; rfl) hk (applicable_sound hap hl1) hl2
  obtain ⟨r, hr, _⟩ := summary_step hap (den_refl hl1) hdg
  exact ⟨r, hr⟩

/-- A request comes only from a fact with an abstract mark. -/
theorem check_request_abs {i s : PFact} {f : AFact} {t : Mark} (h : check i f s = .request t) :
    ∀ t', f.fact.mark ≠ .conc t' := by
  intro t' ht
  unfold check at h
  rw [ht] at h
  dsimp only at h
  split at h
  · exact Check.noConfusion h
  · exact Check.noConfusion h
  · split at h
    · split at h
      · exact Check.noConfusion h
      · exact Check.noConfusion h
    · exact Check.noConfusion h

#print axioms applyEdge_corr
#print axioms transfer_corr
#print axioms cleanRes_corr
#print axioms applySummary_corr
#print axioms summary_nd_fact
#print axioms summary_nd_exists

end Corr

/-! ## Part 5. Z2: `DNz` is inside `DN` -/

section Z2
variable {X : Ctx}

/-- The zero members of a partial match of `DN` are bound by the caller zero edge. Each binding
    adds the zero fact to the joined list and keeps the layer. -/
theorem bind_zeros (hC : ZeroCalls X.Q.prog) {M : MethodId} {n n' : Node} {c : Call}
    (hE : (M, n, Instr.call c, n') ∈ X.Q.prog.edges)
    (hz : DN X (.nedge M [zeroFact] n Backward.zeroAF)) :
    ∀ {zs rest P : List PFact} {g : AFact}, (∀ z, z ∈ zs → z = zeroFact) →
      DN X (.npart M n c n' (zs ++ rest) P g) →
      ∃ Z, (∀ z, z ∈ Z → z = zeroFact) ∧ DN X (.npart M n c n' rest (P ++ Z) g)
  | [], _, _, _, _, h => ⟨[], fun _ h => absurd h List.not_mem_nil, by rw [List.append_nil]; exact h⟩
  | z :: zs, rest, P, g, hzs, h => by
    have hz0 := hzs z List.mem_cons_self
    subst hz0
    have h1 := DN.ndBind h hz (hC _ _ _ _ hE).2 zero_bind applicable_zero_zero
    have hg : (⟨g.fact, g.demand || Backward.zeroAF.demand⟩ : AFact) = g := by
      show (⟨g.fact, g.demand || false⟩ : AFact) = g
      rw [Bool.or_false]
    rw [hg] at h1
    obtain ⟨Z, hZ, h2⟩ := bind_zeros hC hE hz (fun z hz => hzs z (List.mem_cons_of_mem _ hz)) h1
    refine ⟨zeroFact :: Z, fun z hz' => ?_, by rw [List.append_assoc] at h2; exact h2⟩
    rcases List.mem_cons.mp hz' with rfl | hz'
    · rfl
    · exact hZ z hz'

theorem bind_zeros_all (hC : ZeroCalls X.Q.prog) {M : MethodId} {n n' : Node} {c : Call}
    (hE : (M, n, Instr.call c, n') ∈ X.Q.prog.edges)
    (hz : DN X (.nedge M [zeroFact] n Backward.zeroAF)) {zs P : List PFact} {g : AFact}
    (hzs : ∀ z, z ∈ zs → z = zeroFact) (h : DN X (.npart M n c n' zs P g)) :
    ∃ Z, (∀ z, z ∈ Z → z = zeroFact) ∧ DN X (.npart M n c n' [] (P ++ Z) g) :=
  bind_zeros (rest := []) hC hE hz hzs (by rw [List.append_nil]; exact h)

/-- An edge of `DN` with an abstract conclusion mark has one premise (W7). -/
theorem dn_single_of_abs (hwf : X.Q.WF) {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (h : DN X (.nedge M P n f)) (habs : ∀ t, f.fact.mark ≠ .conc t) : ∃ x, P = [x] := by
  obtain ⟨hne, _, hnd⟩ := (ndInv_all hwf h : EdgeOK P f)
  match P, hne, hnd with
  | [], hne, _ => exact absurd rfl hne
  | [x], _, _ => exact ⟨x, rfl⟩
  | _ :: _ :: _, _, hnd =>
    obtain ⟨⟨t, ht⟩, _⟩ := hnd (by show 2 ≤ _ + 1 + 1; omega)
    exact absurd ht (habs t)

theorem dropZ_sandwich {Z1 P Z2 : List PFact} (h1 : ∀ z, z ∈ Z1 → z = zeroFact)
    (h2 : ∀ z, z ∈ Z2 → z = zeroFact) : dropZ (Z1 ++ P ++ Z2) = dropZ P := by
  rw [dropZ_append_allZ h2, dropZ_allZ_append h1]

/-- The motive of Z2. An object of `DNz` is an object of `DN`. An edge `P' → f'` is the image of
    an edge `P → f` with `dropZ P = P'`, the corresponding fact, and a layer that is not higher.
    A partial match `(rest', P', g')` is the image of a partial match `(rest, P, g)` of `DN`
    whose remaining premises lose only zero members, whose joined list has the same members
    that are not the zero fact, and whose call node has the zero edge once a caller edge is
    bound. -/
def Z2Mot (X : Ctx) : NObj → Prop
  | .ninit M i => DN X (.ninit M i)
  | .nadded M a => DN X (.nadded M a)
  | .nreq M i t => DN X (.nreq M i t)
  | .nvuln M n s b => ∃ b0, DN X (.nvuln M n s b0) ∧ DLe b0 b
  | .nedge M P' n f' => ∃ P f, DN X (.nedge M P n f) ∧ dropZ P = P' ∧ Corr f f' ∧
      DLe f.demand f'.demand
  | .npart M n c n' rest' P' g' => ∃ rest P g, DN X (.npart M n c n' rest P g) ∧
      nz rest = rest' ∧ nz P = nz P' ∧ Corr g g' ∧ DLe g.demand g'.demand ∧
      (DN X (.nedge M [zeroFact] n Backward.zeroAF) ∨ (P' = [] ∧ 2 ≤ rest'.length))

theorem dle_comm_or {a b a' b' : Bool} (h1 : DLe a a') (h2 : DLe b b') : DLe (a || b) (b' || a') := by
  rw [Bool.or_comm b' a']
  exact DLe.or h1 h2

/-- Z2 (`DNz` → `DN`). Every object of `DNz` corresponds to an object of `DN`; an edge of `DNz`
    keyed by `P'` is the image of an edge of `DN` keyed by `P` with `dropZ P = P'`, the same fact,
    and a layer that is not higher. -/
theorem dnz_to_dn (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {o : NObj} (h : DNz X o) :
    Z2Mot X o := by
  induction h with
  | root hM => exact DN.root hM
  | @start M i _ ih => exact ⟨[i], startFact i, DN.start ih, dropZ_single i, corr_refl _, DLe.refl _⟩
  | step _ he hf ih =>
    obtain ⟨P, f, hD, hP, hc, hd⟩ := ih
    obtain ⟨r, hr, hk⟩ := transfer_corr (corr_symm hc) hf
    exact ⟨P, r, DN.step hD he hr, hP, corr_symm hk.1, hk.2.2 hd⟩
  | @reqStmt M i n f' n' s t _ he hq ih =>
    obtain ⟨P, f, hD, hP, hc, _⟩ := ih
    have hq' : t ∈ (transfer X.counted X.FL s f).reqs := by
      rw [transfer_reqs_corr hc.1]
      exact hq
    have habs : ∀ t', f.fact.mark ≠ .conc t' := fun t' ht => by
      rw [transfer_reqs_of_conc ht] at hq'
      exact List.not_mem_nil hq'
    obtain ⟨x, rfl⟩ := dn_single_of_abs hwf hD habs
    rw [dropZ_single] at hP
    have hx := (List.cons.inj hP).1
    subst hx
    exact DN.reqStmt hD he hq'
  | pass _ he hm ih =>
    obtain ⟨P, f, hD, hP, hc, hd⟩ := ih
    exact ⟨P, f, DN.pass hD he (by rw [hc.1]; exact hm), hP, hc, hd⟩
  | added _ he he1 ha ih =>
    obtain ⟨P, f, hD, _, hc, _⟩ := ih
    obtain ⟨a, ha2, hka⟩ := applyEdge_corr (corr_symm hc) ha
    have h2 := DN.added hD he he1 ha2
    rw [← hka.1.1] at h2
    exact h2
  | initA _ ih => exact DN.initA ih
  | @ret M P' n f' n' c e1 a' j g' r'' e2 r' _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    obtain ⟨P, f, hD, hP, hc, hd⟩ := ihf
    obtain ⟨Pc, g, hG, hPc, hcg, hdg⟩ := ihg
    obtain ⟨a, ha2, hka⟩ := applyEdge_corr (corr_symm hc) ha
    have hap2 : applicable j a.fact = true := by rw [← hka.1.1]; exact hap
    have hda : DLe a.demand a'.demand := hka.2.2 hd
    have hne := premises_ne_nil hwf hG
    cases Pc with
    | nil => exact absurd rfl hne
    | cons x xs =>
      cases xs with
      | nil =>
        -- the summary has one premise in `DN` too: `ret`
        rw [dropZ_single] at hPc
        have hx := (List.cons.inj hPc).1
        subst hx
        obtain ⟨r, hr2, hcr, _, hdr⟩ := applySummary_corr hka.1 (corr_symm hcg) hr
        obtain ⟨q, hq, hkq⟩ := applyEdge_corr hcr hr'
        obtain ⟨hl1, _, hl3⟩ := limitF_corr X.counted X.FL hkq.1
        exact ⟨P, _, DN.ret hD he he1 ha2 ihj hap2 hG hr2 he2 hq, hP, corr_symm hl1,
          hl3 (hkq.2.2 (hdr hda hdg))⟩
      | cons y zs =>
        -- an ND summary of `DN` whose `dropZ` has one member: the chain, the zero members bound
        -- by the caller zero edge
        have h2 : 2 ≤ (x :: y :: zs).length := by show 2 ≤ zs.length + 1 + 1; omega
        obtain ⟨hgk, T, hgT⟩ := ndConclusion_uncorrelated hwf hG h2
        have hgT' : g'.fact.mark = .conc T := by rw [← hcg.1]; exact hgT
        have hgk' : g'.fact.kind.isStar = false := by rw [← hcg.1]; exact hgk
        obtain ⟨hrf, hrd⟩ := summary_nd_fact ⟨T, hgT'⟩ hgk' hr
        have hz0 := zero_edge hZ hC hA hαz hD
        obtain ⟨zs1, ws, hsplit, hzs1, hws⟩ := dropZ_eq_single (List.cons_ne_nil _ _) hPc
        have hopen := DN.ndOpen he hG h2
        rw [hsplit] at hopen
        obtain ⟨Z1, hZ1, h3⟩ := bind_zeros hC he hz0 hzs1 hopen
        have h4 := DN.ndBind h3 hD he1 ha2 hap2
        obtain ⟨Z2, hZ2, h5⟩ := bind_zeros_all hC he hz0 hws h4
        -- the conclusion of the chain corresponds to the `ret` result of `DNz`
        have hcorr : Corr r'' ⟨g.fact, g.demand || a.demand⟩ :=
          ⟨by rw [hrf]; exact hcg.1.symm, .inr ⟨T, by rw [hrf]; exact hgT'⟩⟩
        obtain ⟨q, hq, hkq⟩ := applyEdge_corr hcorr hr'
        obtain ⟨hl1, _, hl3⟩ := limitF_corr X.counted X.FL hkq.1
        have hdl : DLe (g.demand || a.demand) r''.demand := fun h => hrd (dle_comm_or hdg hda h)
        refine ⟨[] ++ Z1 ++ P ++ Z2, _, DN.ndRet h5 he2 hq, ?_, corr_symm hl1, hl3 (hkq.2.2 hdl)⟩
        rw [List.nil_append, dropZ_sandwich hZ1 hZ2]
        exact hP
  | @ndOpen M n c n' Pc' g' he _ h2 ih =>
    obtain ⟨Pc, g, hG, hPc, hcg, hdg⟩ := ih
    have h2' : 2 ≤ (dropZ Pc).length := by rw [hPc]; exact h2
    obtain ⟨hnzP, _⟩ := two_le_dropZ h2'
    have hlen : 2 ≤ Pc.length := Nat.le_trans h2' (dropZ_length_le (premises_ne_nil hwf hG))
    refine ⟨Pc, [], g, DN.ndOpen he hG hlen, ?_, rfl, hcg, hdg, .inr ⟨rfl, h2⟩⟩
    rw [← hnzP]
    exact hPc
  | @ndBind M n c n' p ps P' g' Pf' f' e1 a' _ _ he1 ha hap ihp ihf =>
    obtain ⟨rest, P, g, hpart, hrest, hPP, hcg, hdg, _⟩ := ihp
    obtain ⟨Pf, f, hD, hPf, hcf, hdf⟩ := ihf
    obtain ⟨zs, tail, rfl, hzs, htail, _⟩ := nz_eq_cons hrest
    have hE := (zero_everywhere hZ hC hA hαz hpart).1
    have hz0 := zero_edge hZ hC hA hαz hD
    obtain ⟨Z, hZz, h1⟩ := bind_zeros hC hE hz0 hzs hpart
    obtain ⟨a, ha2, hka⟩ := applyEdge_corr (corr_symm hcf) ha
    have hap2 : applicable p a.fact = true := by rw [← hka.1.1]; exact hap
    have h2 := DN.ndBind h1 hD he1 ha2 hap2
    obtain ⟨⟨T, hT⟩, _, _⟩ := (ndInv_all hwf hpart : PartOK _ _ g)
    refine ⟨tail, (P ++ Z) ++ Pf, ⟨g.fact, g.demand || a.demand⟩, h2, htail, ?_,
      ⟨hcg.1, .inr ⟨T, hT⟩⟩, DLe.or hdg (hka.2.2 hdf), .inl hz0⟩
    rw [nz_append, nz_append, nz_allZ hZz, List.append_nil, hPP, nz_append, ← hPf, nz_dropZ]
  | @ndRet M n c n' P' g' e2 r' _ he2 hr ih =>
    obtain ⟨rest, P, g, hpart, hrest, hPP, hcg, hdg, hz⟩ := ih
    have hz0 : DN X (.nedge M [zeroFact] n Backward.zeroAF) := by
      rcases hz with hz | ⟨_, hl⟩
      · exact hz
      · exact absurd hl (by decide)
    have hE := (zero_everywhere hZ hC hA hαz hpart).1
    obtain ⟨Z, hZz, h1⟩ := bind_zeros_all hC hE hz0 (nz_eq_nil_iff.mp hrest) hpart
    obtain ⟨r, hr2, hkr⟩ := applyEdge_corr (corr_symm hcg) hr
    obtain ⟨hl1, _, hl3⟩ := limitF_corr X.counted X.FL hkr.1
    refine ⟨P ++ Z, _, DN.ndRet h1 he2 hr2, ?_, corr_symm hl1, hl3 (hkr.2.2 hdg)⟩
    rw [dropZ_append_allZ hZz]
    exact dropZ_eq_iff.mpr hPP
  | @reqSink M i n f' s t _ hs hc ih =>
    obtain ⟨P, f, hD, hP, hcf, _⟩ := ih
    have hc' : check i f s = .request t := by rw [check_corr hcf.1]; exact hc
    obtain ⟨x, rfl⟩ := dn_single_of_abs hwf hD (check_request_abs hc')
    rw [dropZ_single] at hP
    have hx := (List.cons.inj hP).1
    subst hx
    exact DN.reqSink hD hs hc'
  | answer _ _ hm hov ihr iha => exact DN.answer ihr iha hm hov
  | @reqUp m j t M ic n f' n' c e a' _ _ he hcm he1 ha hcl hov ihr ihf =>
    obtain ⟨P, f, hD, hP, hcf, _⟩ := ihf
    obtain ⟨a, ha2, hka⟩ := applyEdge_corr (corr_symm hcf) ha
    have hcl2 : climbsB a.fact.mark t = true := by rw [← hka.1.1]; exact hcl
    have hov2 : overlapB a.fact j = true := by rw [← hka.1.1]; exact hov
    have habs : ∀ t', f.fact.mark ≠ .conc t' := fun t' ht =>
      let ⟨t'', h''⟩ := applyEdge_mark_conc ht ha2
      climbsB_abs hcl2 t'' h''
    obtain ⟨x, rfl⟩ := dn_single_of_abs hwf hD habs
    rw [dropZ_single] at hP
    have hx := (List.cons.inj hP).1
    subst hx
    exact DN.reqUp ihr hD he hcm he1 ha2 hcl2 hov2
  | @vuln M P' n f' s i _ hs hi hc ih =>
    obtain ⟨P, f, hD, hP, hcf, hdf⟩ := ih
    have hc' : check i f s = .triggered := by rw [check_corr hcf.1]; exact hc
    refine ⟨f.demand, ?_, hdf⟩
    rcases mark_dich f.fact.mark with ⟨t, ht⟩ | habs
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil P (premises_ne_nil hwf hD)
      exact DN.vuln hD hs hx (by rw [check_conc_indep (i' := i) ht]; exact hc')
    · obtain ⟨x, rfl⟩ := dn_single_of_abs hwf hD habs
      rw [dropZ_single] at hP
      rw [← hP] at hi
      exact DN.vuln hD hs hi hc'
  | clean _ he hf ih =>
    obtain ⟨P, f, hD, hP, hc, hd⟩ := ih
    obtain ⟨r, hr, hk⟩ := cleanRes_corr (corr_symm hc) hf
    exact ⟨P, r, DN.clean hD he hr, hP, corr_symm hk.1, hk.2.2 hd⟩
  | @reqClean M i n f' n' cl t _ he hq ih =>
    obtain ⟨P, f, hD, hP, hc, _⟩ := ih
    have hq' : t ∈ (cleanRes cl f).reqs := by rw [cleanRes_reqs_corr hc.1]; exact hq
    obtain ⟨x, rfl⟩ := dn_single_of_abs hwf hD (cleanRes_reqs_abstract hq').1
    rw [dropZ_single] at hP
    have hx := (List.cons.inj hP).1
    subst hx
    exact DN.reqClean hD he hq'
  | filt _ he hm ih =>
    obtain ⟨P, f, hD, hP, hc, hd⟩ := ih
    exact ⟨P, f, DN.filt hD he (by rw [hc.1]; exact hm), hP, hc, hd⟩
  | conj _ _ hcj ho1 hg1 ho2 hg2 ih1 ih2 =>
    obtain ⟨P1, f1, hD1, hP1, hc1, hd1⟩ := ih1
    obtain ⟨P2, f2, hD2, hP2, hc2, hd2⟩ := ih2
    obtain ⟨hC', hdl⟩ := conjFact_corr hc1.1 hc2.1 (hwf.target _ _ _ _ hcj).1
    refine ⟨P1 ++ P2, _, DN.conj hD1 hD2 hcj (by rw [hc1.1]; exact ho1) (by rw [hc1.1]; exact hg1)
      (by rw [hc2.1]; exact ho2) (by rw [hc2.1]; exact hg2), ?_, hC', hdl hd1 hd2⟩
    rw [← dropZ_dropZ_append, hP1, hP2]
  | @reqConj M i n f' cj n' lit t _ hcj hlit ho hg ih =>
    obtain ⟨P, f, hD, hP, hc, _⟩ := ih
    have hg' : markGate lit.mark f.fact.mark = .req t := by rw [hc.1]; exact hg
    obtain ⟨x, rfl⟩ := dn_single_of_abs hwf hD (gate_req_abs hg')
    rw [dropZ_single] at hP
    have hx := (List.cons.inj hP).1
    subst hx
    exact DN.reqConj hD hcj hlit (by rw [hc.1]; exact ho) hg'

#print axioms dnz_to_dn

end Z2


/-! ## Part 6. Z1: `DN` is inside `DNz` (under `ZeroLinks`) -/

section Z1
variable {X : Ctx}

/-- The premise invariant of `DNz`: a premise list is not empty and its members are initial
    facts of the method. -/
def PIz (X : Ctx) : NObj → Prop
  | .nedge M P _ _ => P ≠ [] ∧ ∀ p, p ∈ P → DNz X (.ninit M p)
  | .npart M _ _ _ rest P _ => (∀ p, p ∈ P → DNz X (.ninit M p)) ∧ (P ≠ [] ∨ 2 ≤ rest.length)
  | _ => True

theorem premInit_z {o : NObj} (h : DNz X o) : PIz X o := by
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

#print axioms premInit_z

/-- One bound callee premise of a partial match of `DN`, with the image of its caller edge in
    `DNz`: the premise `p`, the caller premise list `Pf` of `DN`, the caller fact `f'` of `DNz`,
    the binding `e1` and the added fact `a'`. -/
structure ZSlot where
  p  : PFact
  Pf : List PFact
  f' : AFact
  e1 : MicroEdge
  a' : AFact

/-- A slot is in `DNz`, and a zero slot has only zero premises (`ZeroLinks`). -/
abbrev SlotOK (X : Ctx) (M : MethodId) (n : Node) (c : Call) (b : ZSlot) : Prop :=
  DNz X (.nedge M (dropZ b.Pf) n b.f') ∧ b.e1 ∈ c.toCallee ∧
    b.a' ∈ (applyEdge b.f' b.e1.1 b.e1.2).facts ∧ applicable b.p b.a'.fact = true ∧
    (b.p = zeroFact → ∀ q, q ∈ b.Pf → q = zeroFact)

/-- The joined list of `DNz` for the slots: the slots of the members that are not the zero fact. -/
def nzSlots (B : List ZSlot) : List PFact :=
  ((B.filter (fun b => b.p != zeroFact)).map (fun b => dropZ b.Pf)).flatten

theorem nzSlots_nil : nzSlots [] = [] := rfl

theorem nzSlots_cons_zero {b : ZSlot} (B : List ZSlot) (h : b.p = zeroFact) :
    nzSlots (b :: B) = nzSlots B := by
  unfold nzSlots
  rw [List.filter_cons, h, bne_zero_false]
  rfl

theorem nzSlots_cons_ne {b : ZSlot} (B : List ZSlot) (h : b.p ≠ zeroFact) :
    nzSlots (b :: B) = dropZ b.Pf ++ nzSlots B := by
  unfold nzSlots
  rw [List.filter_cons, bne_zero_true h]
  rfl

/-- The joined list of `DN` and the joined list of `DNz` have the same members that are not the
    zero fact: a zero slot has only zero premises. -/
theorem nz_nzSlots : ∀ {B : List ZSlot}, (∀ b, b ∈ B → b.p = zeroFact → nz b.Pf = []) →
    nz (B.map ZSlot.Pf).flatten = nz (nzSlots B)
  | [], _ => rfl
  | b :: B, h => by
    have ih := nz_nzSlots (B := B) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    show nz (b.Pf ++ (B.map ZSlot.Pf).flatten) = _
    rw [nz_append, ih]
    by_cases hb : b.p = zeroFact
    · rw [nzSlots_cons_zero B hb, h b List.mem_cons_self hb, List.nil_append]
    · rw [nzSlots_cons_ne B hb, nz_append, nz_dropZ]

theorem nz_slots_allZ : ∀ {B : List ZSlot}, nz (B.map ZSlot.p) = [] →
    (∀ b, b ∈ B → b.p = zeroFact → nz b.Pf = []) → nz (B.map ZSlot.Pf).flatten = []
  | [], _, _ => rfl
  | b :: B, hn, h => by
    have hall := nz_eq_nil_iff.mp hn
    have hb : b.p = zeroFact := hall _ List.mem_cons_self
    have hn' : nz (B.map ZSlot.p) = [] :=
      nz_eq_nil_iff.mpr fun q hq => hall q (List.mem_cons_of_mem _ hq)
    show nz (b.Pf ++ (B.map ZSlot.Pf).flatten) = []
    rw [nz_append, h b List.mem_cons_self hb,
      nz_slots_allZ hn' (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

/-- The slot of the one member that is not the zero fact. -/
theorem pick_slot {j : PFact} : ∀ {B : List ZSlot}, nz (B.map ZSlot.p) = [j] →
    (∀ b, b ∈ B → b.p = zeroFact → nz b.Pf = []) →
    ∃ b, b ∈ B ∧ b.p = j ∧ nz (B.map ZSlot.Pf).flatten = nz b.Pf
  | [], hn, _ => absurd hn (List.cons_ne_nil _ _).symm
  | b :: B, hn, h => by
    have h' := fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases hb : b.p = zeroFact
    · have hn' : nz (B.map ZSlot.p) = [j] := by
        rw [List.map_cons, hb, nz_cons_zero] at hn
        exact hn
      obtain ⟨b', hb', hbp, hnz⟩ := pick_slot hn' h'
      refine ⟨b', List.mem_cons_of_mem _ hb', hbp, ?_⟩
      show nz (b.Pf ++ (B.map ZSlot.Pf).flatten) = _
      rw [nz_append, h b List.mem_cons_self hb, List.nil_append, hnz]
    · rw [List.map_cons, nz_cons_ne _ hb] at hn
      obtain ⟨hbj, hrest⟩ := List.cons.inj hn
      refine ⟨b, List.mem_cons_self, hbj, ?_⟩
      show nz (b.Pf ++ (B.map ZSlot.Pf).flatten) = _
      rw [nz_append, nz_slots_allZ hrest h', List.append_nil]

/-- `DNz` binds the slots of the members that are not the zero fact, in order. -/
theorem dnz_chain {M : MethodId} {n n' : Node} {c : Call} :
    ∀ {B : List ZSlot} {rest Pacc : List PFact} {g : AFact},
      (∀ b, b ∈ B → SlotOK X M n c b) →
      DNz X (.npart M n c n' (nz (B.map ZSlot.p) ++ rest) Pacc g) →
      ∃ g', g'.fact = g.fact ∧ DNz X (.npart M n c n' rest (Pacc ++ nzSlots B) g')
  | [], _, _, g, _, h => ⟨g, rfl, by rw [nzSlots_nil, List.append_nil]; exact h⟩
  | b :: B, rest, Pacc, g, hok, h => by
    obtain ⟨hf, he1, ha, hap, _⟩ := hok b List.mem_cons_self
    have hok' := fun x hx => hok x (List.mem_cons_of_mem _ hx)
    by_cases hb : b.p = zeroFact
    · rw [List.map_cons, hb, nz_cons_zero] at h
      obtain ⟨g', hg', h'⟩ := dnz_chain hok' h
      exact ⟨g', hg', by rw [nzSlots_cons_zero B hb]; exact h'⟩
    · rw [List.map_cons, nz_cons_ne _ hb] at h
      have h1 := DNz.ndBind h hf he1 ha hap
      obtain ⟨g', hg', h'⟩ := dnz_chain hok' h1
      exact ⟨g', hg', by rw [nzSlots_cons_ne B hb, ← List.append_assoc]; exact h'⟩

/-- The motive of Z1. An object of `DN` is an object of `DNz`. An edge `P → f` gives an edge
    `dropZ P → f'` with the corresponding fact. A partial match of `DN` records the callee
    summary image in `DNz` and one slot per bound premise; `DNz` builds its own application at
    `ndRet` (a chain over the slots that are not zero, or `ret` if one member is left). -/
def Z1Mot (X : Ctx) : NObj → Prop
  | .ninit M i => DNz X (.ninit M i)
  | .nadded M a => DNz X (.nadded M a)
  | .nreq M i t => DNz X (.nreq M i t)
  | .nvuln M n s _ => ∃ b, DNz X (.nvuln M n s b)
  | .nedge M P n f => ∃ f', DNz X (.nedge M (dropZ P) n f') ∧ Corr f f'
  | .npart M n c n' rest P g => (M, n, Instr.call c, n') ∈ X.Q.prog.edges ∧
      ∃ (Pc : List PFact) (g0 : AFact) (B : List ZSlot),
        DNz X (.nedge c.callee (dropZ Pc) (X.Q.prog.exit c.callee) g0) ∧
        g0.fact = g.fact ∧ (∃ T, g.fact.mark = .conc T) ∧ g.fact.kind.isStar = false ∧
        2 ≤ Pc.length ∧ Pc = B.map ZSlot.p ++ rest ∧ P = (B.map ZSlot.Pf).flatten ∧
        ∀ b, b ∈ B → SlotOK X M n c b

/-- A list whose `dropZ` has fewer than two members has one. -/
theorem dropZ_one {P : List PFact} (h : (dropZ P).length < 2) : ∃ j, dropZ P = [j] := by
  have hne := dropZ_ne_nil P
  match hd : dropZ P, hne, h with
  | [j], _, _ => exact ⟨j, rfl⟩
  | _ :: _ :: _, _, h => exact absurd h (by simp)

/-- Z1 (`DN` → `DNz`), under `ZeroLinks`. Every object of `DN` is an object of `DNz`; an edge of
    `DN` keyed by `P` gives an edge of `DNz` keyed by `dropZ P` with the same fact (the layer can
    differ: for coverage and the vulnerability theorem it does not matter). -/
theorem dn_to_dnz (hwf : X.Q.WF) (hzl : ZeroLinks X) {o : NObj} (h : DN X o) : Z1Mot X o := by
  induction h with
  | root hM => exact DNz.root hM
  | @start M i _ ih => exact ⟨startFact i, by rw [dropZ_single]; exact DNz.start ih, corr_refl _⟩
  | step _ he hf ih =>
    obtain ⟨f', hD, hc⟩ := ih
    obtain ⟨r', hr', hk⟩ := transfer_corr hc hf
    exact ⟨r', DNz.step hD he hr', hk.1⟩
  | reqStmt _ he hq ih =>
    obtain ⟨f', hD, hc⟩ := ih
    rw [dropZ_single] at hD
    exact DNz.reqStmt hD he (by rw [← transfer_reqs_corr hc.1]; exact hq)
  | pass _ he hm ih =>
    obtain ⟨f', hD, hc⟩ := ih
    exact ⟨f', DNz.pass hD he (by rw [← hc.1]; exact hm), hc⟩
  | added _ he he1 ha ih =>
    obtain ⟨f', hD, hc⟩ := ih
    obtain ⟨a', ha', hk⟩ := applyEdge_corr hc ha
    have h2 := DNz.added hD he he1 ha'
    rw [← hk.1.1] at h2
    exact h2
  | initA _ ih => exact DNz.initA ih
  | ret _ he he1 ha _ hap _ hr he2 hr' ihf ihj ihg =>
    obtain ⟨f', hD, hc⟩ := ihf
    obtain ⟨g', hG, hcg⟩ := ihg
    rw [dropZ_single] at hG
    obtain ⟨a', ha', hka⟩ := applyEdge_corr hc ha
    obtain ⟨r'', hr'', hcr, _, _⟩ := applySummary_corr hka.1 hcg hr
    obtain ⟨q, hq, hkq⟩ := applyEdge_corr hcr hr'
    obtain ⟨hl, _, _⟩ := limitF_corr X.counted X.FL hkq.1
    exact ⟨_, DNz.ret hD he he1 ha' ihj (by rw [← hka.1.1]; exact hap) hG hr'' he2 hq, hl⟩
  | @ndOpen M n c n' Pc g he hG h2 ih =>
    obtain ⟨g', hG', hcg⟩ := ih
    obtain ⟨hgk, hgT⟩ := ndConclusion_uncorrelated hwf hG h2
    exact ⟨he, Pc, g', [], hG', hcg.1.symm, hgT, hgk, h2, rfl, rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | @ndBind M n c n' p ps P g Pf f e1 a _ hf he1 ha hap ihp ihf =>
    obtain ⟨hE, Pc, g0, B, hG0, hg0, hT, hgk, h2, hPc, hP, hok⟩ := ihp
    obtain ⟨f', hD, hc⟩ := ihf
    obtain ⟨a', ha', hka⟩ := applyEdge_corr hc ha
    have hzb : p = zeroFact → ∀ q, q ∈ Pf → q = zeroFact := fun hz =>
      hzl M Pf n f n' c e1 a hE hf he1 ha (by rw [← hz]; exact hap)
    refine ⟨hE, Pc, g0, B ++ [⟨p, Pf, f', e1, a'⟩], hG0, hg0, hT, hgk, h2, ?_, ?_, fun x hx => ?_⟩
    · rw [hPc, List.map_append, List.append_assoc]
      rfl
    · rw [hP, List.map_append, List.flatten_append]
      simp
    · rcases List.mem_append.mp hx with hx | hx
      · exact hok x hx
      · rw [List.mem_singleton.mp hx]
        exact ⟨hD, he1, ha', by rw [← hka.1.1]; exact hap, hzb⟩
  | @ndRet M n c n' P g e2 r _ he2 hr ih =>
    obtain ⟨hE, Pc, g0, B, hG0, hg0, ⟨T, hT⟩, hgk, h2, hPc, hP, hok⟩ := ih
    rw [List.append_nil] at hPc
    have hzero : ∀ b, b ∈ B → b.p = zeroFact → nz b.Pf = [] :=
      fun b hb hz => nz_allZ ((hok b hb).2.2.2.2 hz)
    have hT0 : ∃ T, g0.fact.mark = .conc T := ⟨T, by rw [hg0]; exact hT⟩
    have hk0 : g0.fact.kind.isStar = false := by rw [hg0]; exact hgk
    rcases Nat.lt_or_ge (dropZ Pc).length 2 with hlt | hge
    · -- one member is left: `DNz` applies the summary with `ret`
      obtain ⟨j, hj⟩ := dropZ_one hlt
      have hinit : DNz X (.ninit c.callee j) :=
        (premInit_z hG0).2 j (by rw [hj]; exact List.mem_singleton_self _)
      have hB : B ≠ [] := by
        intro hB
        rw [hB] at hPc
        rw [hPc] at h2
        exact absurd h2 (by decide)
      obtain ⟨b, hbB, hbp, hnzb⟩ : ∃ b, b ∈ B ∧ b.p = j ∧ nz (B.map ZSlot.Pf).flatten = nz b.Pf := by
        rcases dropZ_cases Pc with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
        · rw [h1'] at hj
          have hj0 : j = zeroFact := (List.cons.inj hj).1.symm
          rw [hPc] at h1
          obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hB
          have hbz : b.p = zeroFact :=
            nz_eq_nil_iff.mp h1 _ (List.mem_map_of_mem hb)
          refine ⟨b, hb, by rw [hbz, hj0], ?_⟩
          rw [nz_slots_allZ h1 hzero, hzero b hb hbz]
        · rw [h1', hPc] at hj
          exact pick_slot hj hzero
      obtain ⟨hf, he1, ha, hap, _⟩ := hok b hbB
      rw [hbp] at hap
      rw [hj] at hG0
      obtain ⟨r'', hr''⟩ := summary_nd_exists hap hT0 hk0
      obtain ⟨hrf, _⟩ := summary_nd_fact hT0 hk0 hr''
      have hcr : Corr g r'' := ⟨by rw [hrf, hg0], .inr ⟨T, hT⟩⟩
      obtain ⟨r', hr', hkr⟩ := applyEdge_corr hcr hr
      obtain ⟨hl1, _, _⟩ := limitF_corr X.counted X.FL hkr.1
      have hres := DNz.ret hf hE he1 ha hinit hap hG0 hr'' he2 hr'
      have hl : dropZ b.Pf = dropZ P := by
        rw [hP]
        exact dropZ_eq_iff.mpr hnzb.symm
      rw [hl] at hres
      exact ⟨_, hres, hl1⟩
    · -- two or more members are left: `DNz` opens its own partial match and binds them
      obtain ⟨hnzP, _⟩ := two_le_dropZ hge
      have hopen := DNz.ndOpen hE hG0 hge
      rw [hnzP, hPc] at hopen
      obtain ⟨g', hg', hch⟩ := dnz_chain (rest := []) hok (by rw [List.append_nil]; exact hopen)
      have hcg' : Corr g g' := ⟨by rw [hg', hg0], .inr ⟨T, hT⟩⟩
      obtain ⟨r', hr', hkr⟩ := applyEdge_corr hcg' hr
      obtain ⟨hl1, _, _⟩ := limitF_corr X.counted X.FL hkr.1
      have hres := DNz.ndRet hch he2 hr'
      have hl : dropZ ([] ++ nzSlots B) = dropZ P := by
        rw [List.nil_append, hP]
        exact dropZ_eq_iff.mpr (nz_nzSlots hzero).symm
      rw [hl] at hres
      exact ⟨_, hres, hl1⟩
  | reqSink _ hs hc ih =>
    obtain ⟨f', hD, hcf⟩ := ih
    rw [dropZ_single] at hD
    exact DNz.reqSink hD hs (by rw [← check_corr hcf.1]; exact hc)
  | answer _ _ hm hov ihr iha => exact DNz.answer ihr iha hm hov
  | reqUp _ _ he hcm he1 ha hcl hov ihr ihf =>
    obtain ⟨f', hD, hcf⟩ := ihf
    rw [dropZ_single] at hD
    obtain ⟨a', ha', hka⟩ := applyEdge_corr hcf ha
    exact DNz.reqUp ihr hD he hcm he1 ha' (by rw [← hka.1.1]; exact hcl)
      (by rw [← hka.1.1]; exact hov)
  | @vuln M P n f s i hD0 hs hi hc ih =>
    obtain ⟨f', hD, hcf⟩ := ih
    rcases mark_dich f.fact.mark with ⟨t, ht⟩ | habs
    · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (dropZ_ne_nil P)
      exact ⟨_, DNz.vuln hD hs hx
        (by rw [← check_corr hcf.1, check_conc_indep (i' := i) ht]; exact hc)⟩
    · obtain ⟨x, rfl⟩ := dn_single_of_abs hwf hD0 habs
      rw [dropZ_single] at hD
      exact ⟨_, DNz.vuln hD hs hi (by rw [← check_corr hcf.1]; exact hc)⟩
  | clean _ he hf ih =>
    obtain ⟨f', hD, hc⟩ := ih
    obtain ⟨r', hr', hk⟩ := cleanRes_corr hc hf
    exact ⟨r', DNz.clean hD he hr', hk.1⟩
  | reqClean _ he hq ih =>
    obtain ⟨f', hD, hc⟩ := ih
    rw [dropZ_single] at hD
    exact DNz.reqClean hD he (by rw [← cleanRes_reqs_corr hc.1]; exact hq)
  | filt _ he hm ih =>
    obtain ⟨f', hD, hc⟩ := ih
    exact ⟨f', DNz.filt hD he (by rw [← hc.1]; exact hm), hc⟩
  | conj _ _ hcj ho1 hg1 ho2 hg2 ih1 ih2 =>
    obtain ⟨f1', hD1, hc1⟩ := ih1
    obtain ⟨f2', hD2, hc2⟩ := ih2
    obtain ⟨hC', _⟩ := conjFact_corr hc1.1 hc2.1 (hwf.target _ _ _ _ hcj).1
    have h3 := DNz.conj hD1 hD2 hcj (by rw [← hc1.1]; exact ho1) (by rw [← hc1.1]; exact hg1)
      (by rw [← hc2.1]; exact ho2) (by rw [← hc2.1]; exact hg2)
    rw [dropZ_dropZ_append] at h3
    exact ⟨_, h3, hC'⟩
  | reqConj _ hcj hlit ho hg ih =>
    obtain ⟨f', hD, hc⟩ := ih
    rw [dropZ_single] at hD
    exact DNz.reqConj hD hcj hlit (by rw [← hc.1]; exact ho) (by rw [← hc.1]; exact hg)

#print axioms dn_to_dnz

end Z1


/-! ## Part 7. The correspondence per object -/

section PerObject
variable {X : Ctx}

/-- Z2 for an edge: a `DNz` edge keyed by `P'` is the image of a `DN` edge keyed by `P` with
    `dropZ P = P'`, the same fact, and a normal `DN` edge if the `DNz` edge is normal. -/
theorem dnz_to_dn_edge (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {P' : List PFact}
    {n : Node} {f' : AFact} (h : DNz X (.nedge M P' n f')) :
    ∃ P f, DN X (.nedge M P n f) ∧ dropZ P = P' ∧ f.fact = f'.fact ∧
      (f'.demand = false → f.demand = false) := by
  obtain ⟨P, f, hD, hP, hc, hd⟩ := dnz_to_dn hwf hZ hC hA hαz h
  refine ⟨P, f, hD, hP, hc.1, fun h0 => ?_⟩
  cases hfd : f.demand with
  | false => rfl
  | true =>
    have h1 := hd hfd
    rw [h0] at h1
    exact absurd h1 Bool.false_ne_true

/-- Z1 for an edge (under `ZeroLinks`): a `DN` edge keyed by `P` gives a `DNz` edge keyed by
    `dropZ P` with the same fact. -/
theorem dn_to_dnz_edge (hwf : X.Q.WF) (hzl : ZeroLinks X) {M : MethodId} {P : List PFact}
    {n : Node} {f : AFact} (h : DN X (.nedge M P n f)) :
    ∃ f', DNz X (.nedge M (dropZ P) n f') ∧ f'.fact = f.fact := by
  obtain ⟨f', hD, hc⟩ := dn_to_dnz hwf hzl h
  exact ⟨f', hD, hc.1.symm⟩

/-- The initial facts, the added facts and the requests are the same in `DN` and `DNz` (Z1
    and Z2). -/
theorem ninit_iff (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) (hzl : ZeroLinks X)
    {M : MethodId} {i : PFact} : DNz X (.ninit M i) ↔ DN X (.ninit M i) :=
  ⟨fun h => dnz_to_dn hwf hZ hC hA hαz h, fun h => dn_to_dnz hwf hzl h⟩

theorem nadded_iff (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) (hzl : ZeroLinks X)
    {M : MethodId} {a : PFact} : DNz X (.nadded M a) ↔ DN X (.nadded M a) :=
  ⟨fun h => dnz_to_dn hwf hZ hC hA hαz h, fun h => dn_to_dnz hwf hzl h⟩

theorem nreq_iff (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) (hzl : ZeroLinks X)
    {M : MethodId} {i : PFact} {t : Mark} : DNz X (.nreq M i t) ↔ DN X (.nreq M i t) :=
  ⟨fun h => dnz_to_dn hwf hZ hC hA hαz h, fun h => dn_to_dnz hwf hzl h⟩

/-- The vulnerabilities: the same sinks; a normal `DNz` vulnerability is a normal `DN` one. -/
theorem nvuln_dnz_to_dn (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) {M : MethodId} {n : Node}
    {s : PFact} {b : Bool} (h : DNz X (.nvuln M n s b)) :
    ∃ b0, DN X (.nvuln M n s b0) ∧ (b = false → b0 = false) := by
  obtain ⟨b0, hb0, hd⟩ := dnz_to_dn hwf hZ hC hA hαz h
  refine ⟨b0, hb0, fun h0 => ?_⟩
  cases hb : b0 with
  | false => rfl
  | true =>
    have h1 := hd hb
    rw [h0] at h1
    exact absurd h1 Bool.false_ne_true

theorem nvuln_dn_to_dnz (hwf : X.Q.WF) (hzl : ZeroLinks X) {M : MethodId} {n : Node}
    {s : PFact} {b : Bool} (h : DN X (.nvuln M n s b)) : ∃ b', DNz X (.nvuln M n s b') :=
  dn_to_dnz hwf hzl h

/-- THE CORRESPONDENCE OF THE EDGES: `DNz` has an edge keyed by `P'` with the fact `φ` at `n` iff
    `DN` has an edge keyed by a list `P` with `dropZ P = P'` and the fact `φ` at `n`. -/
theorem edge_iff (hwf : X.Q.WF) (hZ : Backward.ZeroKept X.Q.prog) (hC : ZeroCalls X.Q.prog)
    (hA : ConjAdj X.Q) (hαz : ∀ m, X.α m zeroFact = zeroFact) (hzl : ZeroLinks X)
    {M : MethodId} {P' : List PFact} {n : Node} {φ : PFact} :
    (∃ f', DNz X (.nedge M P' n f') ∧ f'.fact = φ) ↔
      ∃ P f, DN X (.nedge M P n f) ∧ dropZ P = P' ∧ f.fact = φ := by
  constructor
  · rintro ⟨f', hf', rfl⟩
    obtain ⟨P, f, hD, hP, hfa, _⟩ := dnz_to_dn_edge hwf hZ hC hA hαz hf'
    exact ⟨P, f, hD, hP, hfa⟩
  · rintro ⟨P, f, hD, rfl, rfl⟩
    exact dn_to_dnz_edge hwf hzl hD

#print axioms dnz_to_dn_edge
#print axioms dn_to_dnz_edge
#print axioms edge_iff
#print axioms ninit_iff

end PerObject

end ApSpec.NDZero
