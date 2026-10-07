/-
  ApSpec.NDConfirmed — the CONFIRMATION of an ND vulnerability (spec §4.9 with §4.6): a
  confirmed vulnerability on an edge with a premise LIST is real against the support semantics,
  with a tree witness (`ND.ReachN`). It proves the joint support of spec §4.9 condition 3; a per-premise reading of the
  support would be false (`CexSites`).

  Main results:
    * `SupN`, `SupSlots`: the JOINT support of a premise list. At a root: every premise is the
      zero fact. In a callee: ONE call statement `(M', n, c)` to the callee supplies EVERY
      premise `j` of the list; for each `j` a normal caller edge `(Pj, normal) → cj` at `n` whose
      premise list `Pj` is itself jointly supported, whose binding gives the normal added fact
      `a`, and `j = a` (the zero fact, or the exact concrete answer of `a`, as in the base
      `Confirmed.Sup`). Different premises may use different caller edges at that call, and the
      caller edges may be supported through different calls of the caller (the tree).
    * `ConfirmedN`: the three conditions (complete sink edge; exact concrete premises; joint
      support) and a triggered sink check. `confirmedN_vuln`: it is a normal `vuln`.
    * `sup_entryN`: a supported premise list covers a support that is real at the entry of the
      method (`EntryN`: zero locations of a root, or the entry locations of ONE reached call).
    * `confirmed_real_N` (`FiltUp`), `confirmed_real_N_valid` / `_valid_of` (prefix-closed type
      filters, `FiltValid`, `BackOK`, `ConjOK`), `confirmed_real_N_gen`: THE ND CONFIRMATION
      THEOREM. Hypotheses: `Q.WF`, `MarkWF`, `LitConc`.
    * `CexSites.cex_sites`: THE PER-PREMISE RULE IS FALSE. `SupP`/`ConfirmedP` is the per-premise
      reading ("each premise is supported"); two premises of one ND callee edge are
      supported through two DIFFERENT calls, the vulnerability is per-premise confirmed and
      normal, but no execution reaches the sink; `ConfirmedN` rejects it. `supN_supP`: the
      joint rule is stronger. `GoodSite`: the same callee with ONE call binding both premises is
      confirmed by the joint rule, and real.
    * `confirmed_lift`, `confirmedN_iff`: a base confirmation is an ND confirmation; without
      conjunctions the two are the same (`DN_lower`: `DN` without conjunctions is `D`).
    * Each hypothesis is necessary: `CexBase.cexN_filt` (`FiltUp`), `CexBase.cexN_mark`
      (`MarkWF`), `CexLitConf.cex_lit_conf` (`LitConc`: an abstract literal passes a cleaned
      `*∖{5}` fact, the ND summary forgets the exclusion), `CexConjOKConf.cex_conjOK_conf`
      (`ConjOK`, valid form: the literal location is rejected by a type filter). The first two
      come from `Confirmed.CexConfFilt`, `CexConfMark` through `reachN_reach` (without
      conjunctions a tree witness is a `Reach` chain).
    * `Example.confirmed`, `Example.real`: the `NDRule` sample is a confirmed ND vulnerability,
      and it is real.

  No layer condition on the ND summary chain is needed: a caller edge made by `ndRet` is exact
  by `nd_edge_exact` (the chain ORs the layers of the bound caller edges).

  Only `propext` and `Quot.sound` are used (see the `#print axioms` lines).
-/
import ApSpec.NDExact
import ApSpec.Confirmed

namespace ApSpec.NDConfirmed
open ApSpec ApSpec.ND ApSpec.NDExact

/-! ## 1. Support and confirmation -/

/-- Condition 2 of the confirmation: an exact premise with a concrete mark (the zero fact is
    one). -/
abbrev ExactConc (p : PFact) : Prop := p.kind = .exact ∧ ∃ t, p.mark = .conc t

mutual
/-- `SupN X M P`: the premise LIST `P` of an edge of `M` is supported JOINTLY.
    * `root`: `M` is a root and every premise is the zero fact;
    * `call`: ONE call statement `(M', n, c, n')` to `M` supplies every premise (`SupSlots`). -/
inductive SupN (X : Ctx) : MethodId → List PFact → Prop where
  | root {M P} : M ∈ X.roots → (∀ p, p ∈ P → p = zeroFact) → SupN X M P
  | call {M n c n' J} : (M, n, Instr.call c, n') ∈ X.Q.prog.edges → SupSlots X M n c J →
      SupN X c.callee J

/-- `SupSlots X M n c J`: at the call node `n` of `M` (call `c`), every callee premise `j ∈ J`
    has its own normal caller edge `(Pm, f)` at `n` whose premise list `Pm` is supported
    (jointly, `SupN`), whose binding gives the normal added fact `a`, and `j = a` (the zero
    fact, or the exact concrete answer of `a`: the condition of the base `Confirmed.Sup`). -/
inductive SupSlots (X : Ctx) : MethodId → Node → Call → List PFact → Prop where
  | nil {M n c} : SupSlots X M n c []
  | cons {M n c Pm f e a j J} :
      SupN X M Pm → DN X (.nedge M Pm n f) → f.demand = false →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts → a.demand = false →
      DN X (.ninit c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, DN X (.nreq c.callee k t) ∧ a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧
          j = answerInit k a.fact t ∧ j = a.fact)) →
      SupSlots X M n c J → SupSlots X M n c (j :: J)
end

/-- A CONFIRMED ND vulnerability: a complete (normal-layer, no `[any]`) sink edge with the
    premise list `P` (condition 1); every premise is exact with a concrete mark (condition 2);
    the premise list is supported jointly (condition 3); the sink check triggers. -/
def ConfirmedN (X : Ctx) (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ P f, DN X (.nedge M P n f) ∧ f.complete = true ∧ (∀ p, p ∈ P → ExactConc p) ∧
    SupN X M P ∧ (M, n, s) ∈ X.sinks ∧ ∃ i, i ∈ P ∧ check i f s = .triggered

/-- A confirmed vulnerability is a `vuln` object of the normal layer. -/
theorem confirmedN_vuln {X : Ctx} {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedN X M n s) : DN X (.nvuln M n s false) := by
  obtain ⟨P, f, hD, hc, _, _, hs, i, hi, hch⟩ := h
  have hv := DN.vuln hD hs hi hch
  rw [Exact.complete_demand hc] at hv
  exact hv

#print axioms confirmedN_vuln

/-! ## 2. Entry locations of a tree witness -/

/-- `EntryN Q roots M L0`: the support `L0` of `M` is real: the zero locations of a root, or
    the entry locations of ONE call to `M` whose caller locations are reached (`ReachAll`). -/
def EntryN (Q : NProg) (roots : List MethodId) (M : MethodId) (L0 : List Loc) : Prop :=
  (M ∈ roots ∧ ∀ k, k ∈ L0 → k = zeroLoc) ∨
  ∃ M' n c n', (M', n, Instr.call c, n') ∈ Q.prog.edges ∧ c.callee = M ∧
    ReachAll Q roots M' n c L0

theorem entry_reachN {Q : NProg} {roots : List MethodId} {M : MethodId} {L0 : List Loc}
    {n : Node} {l : Loc} (he : EntryN Q roots M L0) (hT : TaintN Q M n l L0) :
    ReachN Q roots M n l := by
  rcases he with ⟨hM, hz⟩ | ⟨M', n0, c, n', hE, rfl, hall⟩
  · exact ReachN.root hM hT hz
  · exact ReachN.down hE hall hT

#print axioms entry_reachN

theorem premCov_zero : ∀ {P : List PFact}, (∀ p, p ∈ P → p = zeroFact) →
    PremCov P (P.map (fun _ => zeroLoc))
  | [], _ => .nil
  | p :: P, h => by
    have hp := h p List.mem_cons_self
    subst hp
    exact .cons zeroFact_covers (premCov_zero (fun q hq => h q (List.mem_cons_of_mem _ hq)))

theorem mem_map_zero {P : List PFact} {k : Loc} (h : k ∈ P.map (fun _ => zeroLoc)) :
    k = zeroLoc := by
  obtain ⟨_, _, hk⟩ := List.mem_map.mp h
  exact hk.symm

/-- The location of an exact concrete fact. -/
theorem exactConc_covers {a : PFact} {t : Mark} (hk : a.kind = .exact) (hm : a.mark = .conc t) :
    a.covers ⟨a.base, a.path, t⟩ :=
  ⟨rfl, ⟨[], (List.append_nil _).symm, by rw [hk]; rfl⟩, by rw [hm]; rfl⟩

/-! ## 3. A supported premise list has a real support -/

section Support
variable {X : Ctx} {ok : Loc → Prop}

mutual
/-- THE SUPPORT THEOREM. A jointly supported premise list covers a support `L0` that is real
    at the entry of `M` (if its locations are valid). -/
theorem sup_entryN (hmw : Exact.MarkWF X.Q.prog) (hfo : Exact.FiltOK X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok) :
    ∀ {M P}, SupN X M P →
      ∃ L0, PremCov P L0 ∧ ((∀ l0, l0 ∈ L0 → ok l0) → EntryN X.Q X.roots M L0)
  | _, _, .root hM hz =>
    ⟨_, premCov_zero hz, fun _ => .inl ⟨hM, fun _ hk => mem_map_zero hk⟩⟩
  | _, _, .call hE hS => by
    obtain ⟨K, hK, hR⟩ := sup_slotsN hmw hfo hbo hlc hco hS hE
    exact ⟨K, hK, fun hok => .inr ⟨_, _, _, _, hE, rfl, hR hok⟩⟩

/-- The slots of one call: the callee entry locations are bound from reached caller
    locations at the call node. -/
theorem sup_slotsN (hmw : Exact.MarkWF X.Q.prog) (hfo : Exact.FiltOK X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok) :
    ∀ {M n c J}, SupSlots X M n c J → ∀ {n'}, (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      ∃ K, PremCov J K ∧ ((∀ k, k ∈ K → ok k) → ReachAll X.Q X.roots M n c K)
  | _, _, _, _, .nil, _, _ => ⟨[], .nil, fun _ => .nil⟩
  | _, _, _, _, @SupSlots.cons _ M n c Pm f e a j J hSm hf hfd he1 ha had _ hj hS, _, hE => by
    have ihm := sup_entryN hmw hfo hbo hlc hco hSm
    have ihs := sup_slotsN hmw hfo hbo hlc hco hS hE
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
    have hinv : NEdgeOK X.Q ok (.nedge M Pm n f) := nd_edgeOK hmw hfo hbo hlc hco hf
    obtain ⟨_, _, _, hns, hex⟩ := hinv
    have hrel : NRel Pm Lm f.fact lk :=
      nrel_uncorr hfA (fun i hPi => hns i hPi hfd hfA) hLm (den_covers_final hdk)
    obtain ⟨hT, hokL⟩ := hex hfd Lm lk hLm hrel hoklk
    exact .cons (entry_reachN (hent hokL) hT) he1 hde
      (hR (fun k' hk' => hok k' (List.mem_cons_of_mem _ hk')))
end

#print axioms sup_entryN
#print axioms sup_slotsN

end Support

/-- The callee premises of the slots are exact with a concrete mark. -/
theorem slots_exactConc {X : Ctx} : ∀ {M : MethodId} {n : Node} {c : Call} {J : List PFact},
    SupSlots X M n c J → ∀ p, p ∈ J → ExactConc p
  | _, _, _, _, .nil => fun _ hp => absurd hp List.not_mem_nil
  | _, _, _, _, .cons _ _ _ _ _ _ _ hj hS => by
    have ih := slots_exactConc hS
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · obtain ⟨t, hak, ham, rfl⟩ := Confirmed.sup_step hj
      exact ⟨hak, t, ham⟩
    · exact ih p hp'

/-- A supported premise is exact with a concrete mark: condition 2 follows from condition 3. -/
theorem supN_exactConc {X : Ctx} {M : MethodId} {P : List PFact} (h : SupN X M P) :
    ∀ p, p ∈ P → ExactConc p := by
  cases h with
  | root _ hz =>
    intro p hp
    rw [hz p hp]
    exact ⟨rfl, zeroMark, rfl⟩
  | call _ hS => exact slots_exactConc hS

#print axioms supN_exactConc

/-! ## 4. THE CONFIRMATION THEOREM -/

section Main
variable {X : Ctx} {ok : Loc → Prop}

/-- The sink fact of a normal edge with concrete premises is uncorrelated: a concrete mark and
    no `*` tail. One premise: `edge_conc` and W2 (`nd_edgeOK`); two or more: W7. -/
theorem sink_shape (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog) (hfo : Exact.FiltOK X.Q.prog ok)
    (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q) (hco : ConjOK X.Q ok)
    {M : MethodId} {P : List PFact} {n : Node} {f : AFact}
    (hD : DN X (.nedge M P n f)) (hfd : f.demand = false) (hex : ∀ p, p ∈ P → ExactConc p) :
    Exact.absB f.fact.mark = false ∧ f.fact.kind.isStar = false := by
  have hinv : EdgeOK P f := ndInv_all hwf hD
  obtain ⟨hne, hs1, hnd⟩ := hinv
  cases P with
  | nil => exact absurd rfl hne
  | cons i P' =>
    cases P' with
    | nil =>
      obtain ⟨_, t, ht⟩ := hex i List.mem_cons_self
      obtain ⟨t', ht'⟩ := hs1 i t rfl ht
      have hA : Exact.absB f.fact.mark = false := by rw [ht']; rfl
      have hok : NEdgeOK X.Q ok (.nedge M [i] n f) := nd_edgeOK hmw hfo hbo hlc hco hD
      exact ⟨hA, hok.2.2.2.1 i rfl hfd hA⟩
    | cons i2 P'' =>
      obtain ⟨⟨t, ht⟩, hk⟩ := hnd (by show 2 ≤ P''.length + 1 + 1; omega)
      exact ⟨by rw [ht]; rfl, hk⟩

#print axioms sink_shape

/-- THE ND CONFIRMATION THEOREM, generic validity `ok` (the form of
    `Confirmed.confirmed_real_valid_of`): a confirmed ND vulnerability has a location in the
    sink pattern, and that location is reached by a tree witness (`ReachN`) if it is valid. -/
theorem confirmed_real_N_gen (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hfo : Exact.FiltOK X.Q.prog ok) (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q)
    (hco : ConjOK X.Q ok) {M : MethodId} {n : Node} {s : PFact} (h : ConfirmedN X M n s) :
    ∃ l, s.covers l ∧ (ok l → ReachN X.Q X.roots M n l) := by
  obtain ⟨P, f, hD, hc, hex, hS, _, i, hi, hch⟩ := h
  have hfd := Exact.complete_demand hc
  obtain ⟨_, t0, him⟩ := hex i hi
  obtain ⟨T, hsm, ho, hmo, _⟩ := Confirmed.check_triggered_passes him hch
  obtain ⟨hfA, hns⟩ := sink_shape hwf hmw hfo hbo hlc hco hD hfd hex
  have hfk := Confirmed.complete_nonstar_exact hc hns
  obtain ⟨T', hT'⟩ := absB_false_conc hfA
  have hTT : T' = T := by
    rw [hT'] at hmo
    exact hmo
  rw [hTT] at hT'
  -- the sink location: the position of the exact sink fact, with the sink mark
  have hsc : s.covers ⟨f.fact.base, f.fact.path, T⟩ :=
    Confirmed.overlap_exact_covers hfk ho T (by rw [hsm]; rfl)
  have hfc : f.fact.covers ⟨f.fact.base, f.fact.path, T⟩ := exactConc_covers hfk hT'
  -- a real support of the premises
  obtain ⟨L0, hL0, hent⟩ := sup_entryN hmw hfo hbo hlc hco hS
  refine ⟨_, hsc, fun hok => ?_⟩
  have hrel : NRel P L0 f.fact ⟨f.fact.base, f.fact.path, T⟩ :=
    nrel_uncorr hfA (fun _ _ => hns) hL0 hfc
  obtain ⟨hT, hokL⟩ := nd_edge_exact_gen hmw hfo hbo hlc hco hD hfd L0 _ hL0 hrel hok
  exact entry_reachN (hent hokL) hT

#print axioms confirmed_real_N_gen

/-- THE ND CONFIRMATION THEOREM (programs without a real type filter, `FiltUp`): a confirmed ND
    vulnerability is real against the support semantics: a tree witness from the roots reaches
    a location of the sink pattern. -/
theorem confirmed_real_N (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hup : Exact.FiltUp X.Q.prog) (hlc : LitConc X.Q)
    {M : MethodId} {n : Node} {s : PFact} (h : ConfirmedN X M n s) :
    ∃ l, ReachN X.Q X.roots M n l ∧ s.covers l := by
  obtain ⟨l, hsc, hR⟩ := confirmed_real_N_gen (ok := fun _ => True) hwf hmw (Exact.filtUp_ok hup)
    (Exact.backOK_true _) hlc (conjOK_true _) h
  exact ⟨l, hR trivial, hsc⟩

#print axioms confirmed_real_N

/-- THE ND CONFIRMATION THEOREM FOR VALID LOCATIONS (prefix-closed type filters, no `FiltUp`):
    a location of the sink pattern that is reached if it is valid. -/
theorem confirmed_real_N_valid_of (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hv : Exact.FiltValid X.Q.prog ok) (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q)
    (hco : ConjOK X.Q ok) {M : MethodId} {n : Node} {s : PFact} (h : ConfirmedN X M n s) :
    ∃ l, s.covers l ∧ (ok l → ReachN X.Q X.roots M n l) :=
  confirmed_real_N_gen hwf hmw (Exact.filtValid_ok hv) hbo hlc hco h

#print axioms confirmed_real_N_valid_of

/-- THE ND CONFIRMATION THEOREM FOR A REAL PROGRAM with prefix-closed type filters: if every
    location of the sink pattern is valid, a confirmed ND vulnerability is real. -/
theorem confirmed_real_N_valid (hwf : X.Q.WF) (hmw : Exact.MarkWF X.Q.prog)
    (hv : Exact.FiltValid X.Q.prog ok) (hbo : Exact.BackOK X.Q.prog ok) (hlc : LitConc X.Q)
    (hco : ConjOK X.Q ok) {M : MethodId} {n : Node} {s : PFact}
    (hok : ∀ l, s.covers l → ok l) (h : ConfirmedN X M n s) :
    ∃ l, ReachN X.Q X.roots M n l ∧ s.covers l := by
  obtain ⟨l, hsc, hR⟩ := confirmed_real_N_valid_of hwf hmw hv hbo hlc hco h
  exact ⟨l, hR (hok l hsc), hsc⟩

#print axioms confirmed_real_N_valid

end Main

/-! ## 5. The base confirmation is an ND confirmation -/

section Lift
variable {X : Ctx}

/-- The base support of one premise is the joint support of the single-premise list. -/
theorem sup_lift {M : MethodId} {i : PFact}
    (h : Confirmed.Sup X.Q.prog X.counted X.FL X.α X.sinks X.roots M i) : SupN X M [i] := by
  induction h with
  | root hM => exact SupN.root hM (fun p hp => List.mem_singleton.mp hp)
  | call _ hD hfd hE he ha had hinit hj ih =>
    refine SupN.call hE (SupSlots.cons ih (D_sub_DN hD) hfd he ha had (D_sub_DN hinit) ?_
      SupSlots.nil)
    rcases hj with h0 | ⟨k, t, hq, hak, ham, hans, hja⟩
    · exact .inl h0
    · exact .inr ⟨k, t, D_sub_DN hq, hak, ham, hans, hja⟩

#print axioms sup_lift

/-- A base confirmation (`Confirmed.Confirmed`, on the program of `X` without its
    conjunctions) is an ND confirmation with the premise list `[i]`. -/
theorem confirmed_lift {M : MethodId} {n : Node} {s : PFact}
    (h : Confirmed.Confirmed X.Q.prog X.counted X.FL X.α X.sinks X.roots M n s) :
    ConfirmedN X M n s := by
  obtain ⟨i, f, hD, hS, hc, hs, hch⟩ := h
  have hS' := sup_lift hS
  exact ⟨[i], f, D_sub_DN hD, hc, supN_exactConc hS', hS', hs, i, List.mem_cons_self, hch⟩

#print axioms confirmed_lift

end Lift

/-! ## 6. Example: the `NDRule` sample is a confirmed ND vulnerability -/

namespace Example
open ND.Example

/-- The `NDRule` sample: the edge `[zeroFact, zeroFact] → C` is complete, its premises are the
    zero fact of the root, and the sink triggers. -/
theorem confirmed : ConfirmedN X 0 3 zC :=
  ⟨[zeroFact, zeroFact], _, c3, by decide,
    fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨rfl, zeroMark, rfl⟩
      · rw [List.mem_singleton.mp hp]; exact ⟨rfl, zeroMark, rfl⟩,
    SupN.root List.mem_cons_self (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact List.mem_singleton.mp hp),
    List.mem_cons_self, zeroFact, List.mem_cons_self, by decide⟩

#print axioms confirmed

theorem wf : X.Q.WF where
  prog := {
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
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h =>
            cases h with
            | head => rfl
            | tail _ h => cases h
        | tail _ h =>
          cases h with
          | head => cases he
          | tail _ h => cases h
    toStar := by
      intro M n c n' hE
      cases hE with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
    fromStar := by
      intro M n c n' hE
      cases hE with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
    filtPrefix := by
      intro M n b may n' hE
      cases hE with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h }
  target := by
    intro M n cj' n' hE
    cases hE with
    | head => exact ⟨⟨9, rfl⟩, rfl⟩
    | tail _ h => cases h

theorem filtUp : Exact.FiltUp X.Q.prog := by
  intro M n b may n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

/-- The confirmed vulnerability of the sample is real: a tree witness reaches the sink. -/
theorem real : ∃ l, ReachN X.Q X.roots 0 3 l ∧ zC.covers l :=
  confirmed_real_N wf NDExact.CexConjOK.markWF filtUp NDExact.CexConjOK.litConc confirmed

#print axioms real

end Example

/-! ## 7. The per-premise reading of the rule is FALSE

  The spec text says "EACH premise is SUPPORTED", one premise at a time. `SupP` is that reading:
  a premise is supported through ANY normal caller edge, at ANY call to the callee. For a premise
  LIST it is too weak: two premises of one ND edge can be supported through two DIFFERENT call
  statements, while a real execution (`ReachN.down`) enters the callee through ONE call, with
  every entry location bound at that call. `SupN` is stronger than `SupP` (`supN_supP`). -/

/-- The per-premise reading of condition 3. -/
inductive SupP (X : Ctx) : MethodId → PFact → Prop where
  | root {M} : M ∈ X.roots → SupP X M zeroFact
  | call {M Pc n f n' c e a j} :
      (∀ p, p ∈ Pc → SupP X M p) → DN X (.nedge M Pc n f) → f.demand = false →
      (M, n, Instr.call c, n') ∈ X.Q.prog.edges → e ∈ c.toCallee →
      a ∈ (applyEdge f e.1 e.2).facts → a.demand = false → DN X (.ninit c.callee j) →
      ((j = zeroFact ∧ a.fact = zeroFact) ∨
       (∃ k t, DN X (.nreq c.callee k t) ∧ a.fact.kind = .exact ∧ a.fact.mark = .conc t ∧
          j = answerInit k a.fact t ∧ j = a.fact)) →
      SupP X c.callee j

/-- The per-premise confirmation. -/
def ConfirmedP (X : Ctx) (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ P f, DN X (.nedge M P n f) ∧ f.complete = true ∧ (∀ p, p ∈ P → ExactConc p) ∧
    (∀ p, p ∈ P → SupP X M p) ∧ (M, n, s) ∈ X.sinks ∧ ∃ i, i ∈ P ∧ check i f s = .triggered

mutual
/-- The joint support gives the support of each premise. -/
theorem supN_supP {X : Ctx} : ∀ {M : MethodId} {P : List PFact}, SupN X M P →
    ∀ p, p ∈ P → SupP X M p
  | _, _, .root hM hz => fun p hp => by rw [hz p hp]; exact SupP.root hM
  | _, _, .call hE hS => slots_supP hS hE

theorem slots_supP {X : Ctx} : ∀ {M : MethodId} {n : Node} {c : Call} {J : List PFact},
    SupSlots X M n c J → ∀ {n'}, (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      ∀ p, p ∈ J → SupP X c.callee p
  | _, _, _, _, .nil, _, _ => fun _ hp => absurd hp List.not_mem_nil
  | _, _, _, _, .cons hSm hf hfd he1 ha had hinit hj hS, _, hE => by
    have ihm := supN_supP hSm
    have ihs := slots_supP hS hE
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact SupP.call ihm hf hfd hE he1 ha had hinit hj
    · exact ihs p hp'
end

#print axioms supN_supP

theorem confirmedN_confirmedP {X : Ctx} {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedN X M n s) : ConfirmedP X M n s := by
  obtain ⟨P, f, hD, hc, hex, hS, hs, hi⟩ := h
  exact ⟨P, f, hD, hc, hex, supN_supP hS, hs, hi⟩

/-! THE COUNTEREXAMPLE TO THE PER-PREMISE RULE. The root `0` makes `A` (base `1`, mark `7`) and
    `B` (base `2`, mark `8`), calls the method `1` with `A` (call `c1`, node `1`), then calls it
    again with `B` (call `c2`, node `2`). The method `1` has the conjunction `A ∧ B → C` (base `3`,
    mark `9`) and the sink `C`. Run 1 (the policy with the empty demand): each call gives an
    abstract initial fact, the literal asks for its mark, and the answer is the exact concrete
    `A` (resp. `B`). The edge `[A, B] → C` is complete and triggers the sink. Each premise is
    supported (`A` through `c1`, `B` through `c2`), so the per-premise rule confirms it. But no
    call binds both `A` and `B`: no execution taints `C` at the sink. -/

namespace CexSites

def zA : PFact := ⟨1, [], .exact, .conc 7⟩
def zB : PFact := ⟨2, [], .exact, .conc 8⟩
def zC : PFact := ⟨3, [], .exact, .conc 9⟩
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, zA), (zeroFact, zB)]⟩
def bA : MicroEdge := (⟨1, [], .exact, .star⟩, ⟨1, [], .exact, .star⟩)
def bB : MicroEdge := (⟨2, [], .exact, .star⟩, ⟨2, [], .exact, .star⟩)
def c1 : Call := ⟨1, [1], [bA], []⟩
def c2 : Call := ⟨1, [2], [bB], []⟩
def cj : Conj := ⟨zA, zB, zC⟩
def prog : Program :=
  ⟨fun _ => 0, fun _ => 1, [(0, 0, .stmt src, 1), (0, 1, .call c1, 2), (0, 2, .call c2, 3)]⟩
def Q : NProg := ⟨prog, [(1, 0, cj, 1)]⟩
/-- Run 1: the policy with the empty demand; the sink `C` at the node `1` of the method `1`. -/
def X : Ctx := ⟨Q, fun _ => true, 3, policy (fun _ => []), [(1, 1, zC)], [0]⟩
def icA : PFact := ⟨1, [], .star Excl.empty, .star⟩
def icB : PFact := ⟨2, [], .star Excl.empty, .star⟩

theorem e0 : DN X (.nedge 0 [zeroFact] 0 ⟨zeroFact, false⟩) := DN.start (DN.root List.mem_cons_self)

theorem a1 : DN X (.nedge 0 [zeroFact] 1 ⟨zA, false⟩) :=
  DN.step e0 List.mem_cons_self (by decide)

theorem b1 : DN X (.nedge 0 [zeroFact] 1 ⟨zB, false⟩) :=
  DN.step e0 List.mem_cons_self (by decide)

theorem hE1 : (0, 1, Instr.call c1, 2) ∈ X.Q.prog.edges := List.Mem.tail _ List.mem_cons_self

theorem hE2 : (0, 2, Instr.call c2, 3) ∈ X.Q.prog.edges :=
  List.Mem.tail _ (List.Mem.tail _ List.mem_cons_self)

theorem b2 : DN X (.nedge 0 [zeroFact] 2 ⟨zB, false⟩) := DN.pass b1 hE1 rfl

theorem addA : DN X (.nadded 1 zA) :=
  DN.added (a := ⟨zA, false⟩) (c := c1) (e := bA) a1 hE1 List.mem_cons_self (by decide)

theorem addB : DN X (.nadded 1 zB) :=
  DN.added (a := ⟨zB, false⟩) (c := c2) (e := bB) b2 hE2 List.mem_cons_self (by decide)

theorem iA0 : DN X (.ninit 1 icA) := by
  have h := DN.initA addA
  have e : X.α 1 zA = icA := by decide
  rw [e] at h
  exact h

theorem iB0 : DN X (.ninit 1 icB) := by
  have h := DN.initA addB
  have e : X.α 1 zB = icB := by decide
  rw [e] at h
  exact h

theorem hcj : (1, 0, cj, 1) ∈ X.Q.conjs := List.mem_cons_self

/-- The literal `A` on the abstract initial fact asks for the mark `7`. -/
theorem rqA : DN X (.nreq 1 icA 7) :=
  DN.reqConj (DN.start iA0) hcj (.inl rfl) (by decide) rfl

theorem rqB : DN X (.nreq 1 icB 8) :=
  DN.reqConj (DN.start iB0) hcj (.inr rfl) (by decide) rfl

/-- The answers: the exact concrete `A` and `B`. -/
theorem iA : DN X (.ninit 1 zA) := by
  have h := DN.answer rqA addA rfl (by decide)
  have e : answerInit icA zA 7 = zA := by decide
  rw [e] at h
  exact h

theorem iB : DN X (.ninit 1 zB) := by
  have h := DN.answer rqB addB rfl (by decide)
  have e : answerInit icB zB 8 = zB := by decide
  rw [e] at h
  exact h

/-- The ND sink edge `[A, B] → C`, complete. -/
theorem cEdge : DN X (.nedge 1 [zA, zB] 1 (conjFact cj ⟨zA, false⟩ ⟨zB, false⟩)) :=
  DN.conj (DN.start iA) (DN.start iB) hcj (by decide) rfl (by decide) rfl

theorem vuln : DN X (.nvuln 1 1 zC false) :=
  DN.vuln cEdge List.mem_cons_self List.mem_cons_self (by decide)

theorem supZ : ∀ p, p ∈ [zeroFact] → SupP X 0 p := fun p hp => by
  rw [List.mem_singleton.mp hp]
  exact SupP.root List.mem_cons_self

theorem supA : SupP X 1 zA :=
  SupP.call (c := c1) (e := bA) (a := ⟨zA, false⟩) supZ a1 rfl hE1 List.mem_cons_self
    (by decide) rfl iA (.inr ⟨icA, 7, rqA, rfl, rfl, by decide, rfl⟩)

theorem supB : SupP X 1 zB :=
  SupP.call (c := c2) (e := bB) (a := ⟨zB, false⟩) supZ b2 rfl hE2 List.mem_cons_self
    (by decide) rfl iB (.inr ⟨icB, 8, rqB, rfl, rfl, by decide, rfl⟩)

/-- The per-premise rule confirms the vulnerability. -/
theorem confirmedP : ConfirmedP X 1 1 zC := by
  refine ⟨[zA, zB], _, cEdge, by decide, fun p hp => ?_, fun p hp => ?_, List.mem_cons_self,
    zA, List.mem_cons_self, by decide⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨rfl, 7, rfl⟩
    · rw [List.mem_singleton.mp hp]; exact ⟨rfl, 8, rfl⟩
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact supA
    · rw [List.mem_singleton.mp hp]; exact supB

#print axioms confirmedP

/-- In the method `1`, a location at the node `0` is its own support; at the node `1` the
    support is one location of `A` and one of `B`. -/
theorem taint1 : ∀ {M n l L}, TaintN Q M n l L → M = 1 →
    (n = 0 ∧ L = [l]) ∨ (n = 1 ∧ ∃ l1 l2, L = [l1, l2] ∧ l1.base = 1 ∧ l2.base = 2)
  | _, _, _, _, .start _ l => fun _ => .inl ⟨rfl, rfl⟩
  | _, _, _, _, .step _ hE _ => by
    cases hE with
    | head => intro hM; exact absurd hM (by decide)
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .pass _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | head => intro hM; exact absurd hM (by decide)
      | tail _ h =>
        cases h with
        | head => intro hM; exact absurd hM (by decide)
        | tail _ h => cases h
  | _, _, _, _, .clean _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .filt _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .conj h1 h2 hcj' hc1 hc2 _ => by
    have i1 := taint1 h1
    have i2 := taint1 h2
    cases hcj' with
    | head =>
      intro _
      rcases i1 rfl with ⟨_, hL1⟩ | ⟨hn, _⟩
      · rcases i2 rfl with ⟨_, hL2⟩ | ⟨hn, _⟩
        · subst hL1 hL2
          exact .inr ⟨rfl, _, _, rfl, hc1.1, hc2.1⟩
        · exact absurd hn (by decide)
      · exact absurd hn (by decide)
    | tail _ h => cases h
  | _, _, _, _, .call hE _ _ _ _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | head => intro hM; exact absurd hM (by decide)
      | tail _ h =>
        cases h with
        | head => intro hM; exact absurd hM (by decide)
        | tail _ h => cases h

/-- No tree witness reaches the node `1` of the method `1`: a call binds only one of the two
    support locations. -/
theorem not_reach : ∀ {M n l}, ReachN Q [0] M n l → M = 1 → n = 1 → False
  | _, _, _, .root hM _ _ => fun e _ => by
    subst e
    exact absurd (List.mem_singleton.mp hM) (by decide)
  | _, _, _, .down hE hall hT => fun _ en => by
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        rcases taint1 hT rfl with ⟨hn, _⟩ | ⟨_, l1, l2, hK, _, hb2⟩
        · rw [en] at hn; exact absurd hn (by decide)
        · subst hK
          cases hall with
          | cons _ _ _ hrest =>
            cases hrest with
            | cons _ he2 hd2 _ =>
              cases he2 with
              | head =>
                have hb : l2.base = 1 := hd2.2.1
                rw [hb2] at hb
                exact absurd hb (by decide)
              | tail _ h => cases h
      | tail _ h =>
        cases h with
        | head =>
          rcases taint1 hT rfl with ⟨hn, _⟩ | ⟨_, l1, l2, hK, hb1, _⟩
          · rw [en] at hn; exact absurd hn (by decide)
          · subst hK
            cases hall with
            | cons _ he1 hd1 _ =>
              cases he1 with
              | head =>
                have hb : l1.base = 2 := hd1.2.1
                rw [hb1] at hb
                exact absurd hb (by decide)
              | tail _ h => cases h
        | tail _ h => cases h

theorem not_real : ¬ ∃ l, ReachN X.Q X.roots 1 1 l ∧ zC.covers l :=
  fun ⟨_, hR, _⟩ => not_reach hR rfl rfl

theorem wf : X.Q.WF where
  prog := {
    stmtTouched := by
      intro M n s n' hE e he
      cases hE with
      | head =>
        cases he with
        | head => rfl
        | tail _ h =>
          cases h with
          | head => rfl
          | tail _ h =>
            cases h with
            | head => rfl
            | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
    toStar := by
      intro M n c n' hE e he
      cases hE with
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h =>
          cases h with
          | head =>
            cases he with
            | head => rfl
            | tail _ h => cases h
          | tail _ h => cases h
    fromStar := by
      intro M n c n' hE e he
      cases hE with
      | tail _ h =>
        cases h with
        | head => cases he
        | tail _ h =>
          cases h with
          | head => cases he
          | tail _ h => cases h
    filtPrefix := by
      intro M n b may n' hE
      cases hE with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h }
  target := by
    intro M n cj' n' hE
    cases hE with
    | head => exact ⟨⟨9, rfl⟩, rfl⟩
    | tail _ h => cases h

theorem markWF : Exact.MarkWF X.Q.prog where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h =>
        cases h with
        | head => rfl
        | tail _ h =>
          cases h with
          | head => rfl
          | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  toC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h => cases h
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h => cases h
  fromC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head => cases he
      | tail _ h =>
        cases h with
        | head => cases he
        | tail _ h => cases h

theorem filtUp : Exact.FiltUp X.Q.prog := by
  intro M n b may n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

theorem litConc : LitConc X.Q := by
  intro M n cj' n' hE
  cases hE with
  | head => exact ⟨⟨7, rfl⟩, ⟨8, rfl⟩⟩
  | tail _ h => cases h

/-- The joint rule does NOT confirm it (by the confirmation theorem). -/
theorem not_confirmedN : ¬ ConfirmedN X 1 1 zC := fun h =>
  not_real (confirmed_real_N wf markWF filtUp litConc h)

/-- THE PER-PREMISE COUNTEREXAMPLE: every hypothesis of `confirmed_real_N` holds (and the run-1
    policy is applicable), the per-premise rule confirms a normal-layer vulnerability, no tree
    witness reaches the sink, and the joint rule `ConfirmedN` does not confirm it. -/
theorem cex_sites :
    X.Q.WF ∧ Exact.MarkWF X.Q.prog ∧ Exact.FiltUp X.Q.prog ∧ LitConc X.Q ∧
    (∀ m a, applicable (X.α m a) a = true) ∧ DN X (.nvuln 1 1 zC false) ∧
    ConfirmedP X 1 1 zC ∧ (¬ ∃ l, ReachN X.Q X.roots 1 1 l ∧ zC.covers l) ∧
    ¬ ConfirmedN X 1 1 zC :=
  ⟨wf, markWF, filtUp, litConc, policy_applicable _, vuln, confirmedP, not_real, not_confirmedN⟩

#print axioms cex_sites

end CexSites

/-! THE JOINT RULE ON A CALLEE. The program of `CexSites` with ONE call `c12` that binds both `A`
  and `B`: the same ND sink edge `[A, B] → C` in the callee is supported jointly (two slots at
  the one call), so it is confirmed, and the confirmation theorem makes it real. -/

namespace GoodSite
open CexSites (zA zB zC src bA bB cj icA icB)

def c12 : Call := ⟨1, [1, 2], [bA, bB], []⟩
def prog : Program := ⟨fun _ => 0, fun _ => 1, [(0, 0, .stmt src, 1), (0, 1, .call c12, 2)]⟩
def Q : NProg := ⟨prog, [(1, 0, cj, 1)]⟩
def X : Ctx := ⟨Q, fun _ => true, 3, policy (fun _ => []), [(1, 1, zC)], [0]⟩

theorem e0 : DN X (.nedge 0 [zeroFact] 0 ⟨zeroFact, false⟩) := DN.start (DN.root List.mem_cons_self)
theorem a1 : DN X (.nedge 0 [zeroFact] 1 ⟨zA, false⟩) := DN.step e0 List.mem_cons_self (by decide)
theorem b1 : DN X (.nedge 0 [zeroFact] 1 ⟨zB, false⟩) := DN.step e0 List.mem_cons_self (by decide)
theorem hE : (0, 1, Instr.call c12, 2) ∈ X.Q.prog.edges := List.Mem.tail _ List.mem_cons_self
theorem hcj : (1, 0, cj, 1) ∈ X.Q.conjs := List.mem_cons_self

theorem addA : DN X (.nadded 1 zA) :=
  DN.added (a := ⟨zA, false⟩) (c := c12) (e := bA) a1 hE List.mem_cons_self (by decide)

theorem addB : DN X (.nadded 1 zB) :=
  DN.added (a := ⟨zB, false⟩) (c := c12) (e := bB) b1 hE (List.Mem.tail _ List.mem_cons_self)
    (by decide)

theorem rqA : DN X (.nreq 1 icA 7) := by
  have h := DN.initA addA
  have e : X.α 1 zA = icA := by decide
  rw [e] at h
  exact DN.reqConj (DN.start h) hcj (.inl rfl) (by decide) rfl

theorem rqB : DN X (.nreq 1 icB 8) := by
  have h := DN.initA addB
  have e : X.α 1 zB = icB := by decide
  rw [e] at h
  exact DN.reqConj (DN.start h) hcj (.inr rfl) (by decide) rfl

theorem iA : DN X (.ninit 1 zA) := by
  have h := DN.answer rqA addA rfl (by decide)
  have e : answerInit icA zA 7 = zA := by decide
  rw [e] at h
  exact h

theorem iB : DN X (.ninit 1 zB) := by
  have h := DN.answer rqB addB rfl (by decide)
  have e : answerInit icB zB 8 = zB := by decide
  rw [e] at h
  exact h

theorem supZ : SupN X 0 [zeroFact] :=
  SupN.root List.mem_cons_self (fun _ hp => List.mem_singleton.mp hp)

/-- The joint support: both premises through the one call `c12`. -/
theorem sup : SupN X 1 [zA, zB] :=
  SupN.call (c := c12) hE
    (SupSlots.cons (e := bA) (a := ⟨zA, false⟩) supZ a1 rfl List.mem_cons_self (by decide) rfl iA
      (.inr ⟨icA, 7, rqA, rfl, rfl, by decide, rfl⟩)
      (SupSlots.cons (e := bB) (a := ⟨zB, false⟩) supZ b1 rfl
        (List.Mem.tail _ List.mem_cons_self) (by decide) rfl iB
        (.inr ⟨icB, 8, rqB, rfl, rfl, by decide, rfl⟩) SupSlots.nil))

theorem confirmed : ConfirmedN X 1 1 zC :=
  ⟨[zA, zB], _, DN.conj (DN.start iA) (DN.start iB) hcj (by decide) rfl (by decide) rfl,
    by decide, supN_exactConc sup, sup, List.mem_cons_self, zA, List.mem_cons_self, by decide⟩

#print axioms confirmed

theorem wf : X.Q.WF where
  prog := {
    stmtTouched := by
      intro M n s n' hE e he
      cases hE with
      | head =>
        cases he with
        | head => rfl
        | tail _ h =>
          cases h with
          | head => rfl
          | tail _ h =>
            cases h with
            | head => rfl
            | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h => cases h
    toStar := by
      intro M n c n' hE e he
      cases hE with
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h =>
            cases h with
            | head => rfl
            | tail _ h => cases h
        | tail _ h => cases h
    fromStar := by
      intro M n c n' hE e he
      cases hE with
      | tail _ h =>
        cases h with
        | head => cases he
        | tail _ h => cases h
    filtPrefix := by
      intro M n b may n' hE
      cases hE with
      | tail _ h =>
        cases h with
        | tail _ h => cases h }
  target := by
    intro M n cj' n' hE
    cases hE with
    | head => exact ⟨⟨9, rfl⟩, rfl⟩
    | tail _ h => cases h

theorem markWF : Exact.MarkWF X.Q.prog where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h =>
        cases h with
        | head => rfl
        | tail _ h =>
          cases h with
          | head => rfl
          | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h => cases h
  toC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h =>
          cases h with
          | head => rfl
          | tail _ h => cases h
      | tail _ h => cases h
  fromC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head => cases he
      | tail _ h => cases h

theorem filtUp : Exact.FiltUp X.Q.prog := by
  intro M n b may n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h => cases h

theorem litConc : LitConc X.Q := by
  intro M n cj' n' hE
  cases hE with
  | head => exact ⟨⟨7, rfl⟩, ⟨8, rfl⟩⟩
  | tail _ h => cases h

/-- The confirmed callee vulnerability is real: a tree witness enters the callee through `c12`
    with both `A` and `B`. -/
theorem real : ∃ l, ReachN X.Q X.roots 1 1 l ∧ zC.covers l :=
  confirmed_real_N wf markWF filtUp litConc confirmed

#print axioms real

end GoodSite

/-! ## 8. Without conjunctions the ND confirmation IS the base confirmation

  On a program without conjunctions every object of `DN` is (the lift of) an object of `D`:
  every edge has ONE premise and no partial match exists (`DN_lower`, the converse of
  `D_sub_DN`). So `ConfirmedN` and `Confirmed.Confirmed` agree (`confirmedN_iff`). -/

section ConjFree
variable {X : Ctx}

/-- The object of `D` below an object of `DN`. -/
def Lower (X : Ctx) : NObj → Prop
  | .ninit M i => D X.Q.prog X.counted X.FL X.α X.sinks X.roots (.init M i)
  | .nedge M P n f => ∃ i, P = [i] ∧ D X.Q.prog X.counted X.FL X.α X.sinks X.roots (.edge M i n f)
  | .nadded M a => D X.Q.prog X.counted X.FL X.α X.sinks X.roots (.added M a)
  | .nreq M i t => D X.Q.prog X.counted X.FL X.α X.sinks X.roots (.req M i t)
  | .nvuln M n s d => D X.Q.prog X.counted X.FL X.α X.sinks X.roots (.vuln M n s d)
  | .npart .. => False

theorem lower_single {M : MethodId} {i : PFact} {n : Node} {f : AFact}
    (h : Lower X (.nedge M [i] n f)) : D X.Q.prog X.counted X.FL X.α X.sinks X.roots (.edge M i n f) := by
  obtain ⟨i', hi, hD⟩ := h
  rw [(List.cons.inj hi).1]
  exact hD

/-- `DN` without conjunctions is `D`: the converse of `D_sub_DN`. -/
theorem DN_lower (hc : X.Q.conjs = []) {o : NObj} (h : DN X o) : Lower X o := by
  induction h with
  | root hM => exact D.root hM
  | start _ ih => exact ⟨_, rfl, D.start ih⟩
  | step _ he hf ih =>
    obtain ⟨i, rfl, hD⟩ := ih
    exact ⟨i, rfl, D.step hD he hf⟩
  | reqStmt _ he hq ih => exact D.reqStmt (lower_single ih) he hq
  | pass _ he hm ih =>
    obtain ⟨i, rfl, hD⟩ := ih
    exact ⟨i, rfl, D.pass hD he hm⟩
  | added _ he he1 ha ih =>
    obtain ⟨i, rfl, hD⟩ := ih
    exact D.added hD he he1 ha
  | initA _ ih => exact D.initA ih
  | ret _ hE he1 ha _ happ _ hr he2 hr' ihF ihJ ihG =>
    obtain ⟨i, rfl, hD⟩ := ihF
    exact ⟨i, rfl, D.ret hD hE he1 ha ihJ happ (lower_single ihG) hr he2 hr'⟩
  | ndOpen _ _ h2 ih =>
    obtain ⟨i, rfl, _⟩ := ih
    exact absurd h2 (Nat.not_succ_le_self 1)
  | ndBind _ _ _ _ _ ihP _ => exact ihP.elim
  | ndRet _ _ _ ih => exact ih.elim
  | reqSink _ hs hch ih => exact D.reqSink (lower_single ih) hs hch
  | answer _ _ hm hov ihq iha => exact D.answer ihq iha hm hov
  | reqUp _ _ hE hcc he ha hcl hov ihq ihF => exact D.reqUp ihq (lower_single ihF) hE hcc he ha hcl hov
  | vuln _ hs hi hch ih =>
    obtain ⟨i, rfl, hD⟩ := ih
    rw [List.mem_singleton.mp hi] at hch
    exact D.vuln hD hs hch
  | clean _ he hf ih =>
    obtain ⟨i, rfl, hD⟩ := ih
    exact ⟨i, rfl, D.clean hD he hf⟩
  | reqClean _ he hq ih => exact D.reqClean (lower_single ih) he hq
  | filt _ he hp ih =>
    obtain ⟨i, rfl, hD⟩ := ih
    exact ⟨i, rfl, D.filt hD he hp⟩
  | conj _ _ hcj =>
    rw [hc] at hcj
    exact absurd hcj List.not_mem_nil
  | reqConj _ hcj =>
    rw [hc] at hcj
    exact absurd hcj List.not_mem_nil

#print axioms DN_lower

mutual
/-- Without conjunctions, the joint support gives the base support of each premise. -/
theorem supN_base (hc : X.Q.conjs = []) : ∀ {M : MethodId} {P : List PFact}, SupN X M P →
    ∀ p, p ∈ P → Confirmed.Sup X.Q.prog X.counted X.FL X.α X.sinks X.roots M p
  | _, _, .root hM hz => fun p hp => by rw [hz p hp]; exact Confirmed.Sup.root hM
  | _, _, .call hE hS => slots_base hc hS hE

theorem slots_base (hc : X.Q.conjs = []) : ∀ {M : MethodId} {n : Node} {c : Call}
    {J : List PFact}, SupSlots X M n c J → ∀ {n'}, (M, n, Instr.call c, n') ∈ X.Q.prog.edges →
      ∀ p, p ∈ J → Confirmed.Sup X.Q.prog X.counted X.FL X.α X.sinks X.roots c.callee p
  | _, _, _, _, .nil, _, _ => fun _ hp => absurd hp List.not_mem_nil
  | _, _, _, _, .cons hSm hf hfd he1 ha had hinit hj hS, _, hE => by
    have ihm := supN_base hc hSm
    have ihs := slots_base hc hS hE
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · have hl : Lower X _ := DN_lower hc hf
      obtain ⟨i, rfl, hD⟩ := hl
      refine Confirmed.Sup.call (ihm i List.mem_cons_self) hD hfd hE he1 ha had
        (DN_lower hc hinit) ?_
      rcases hj with h0 | ⟨k, t, hq, hak, ham, hans, hja⟩
      · exact .inl h0
      · exact .inr ⟨k, t, DN_lower hc hq, hak, ham, hans, hja⟩
    · exact ihs p hp'
end

#print axioms supN_base

/-- Without conjunctions an ND confirmation is a base confirmation. -/
theorem confirmedN_base (hc : X.Q.conjs = []) {M : MethodId} {n : Node} {s : PFact}
    (h : ConfirmedN X M n s) :
    Confirmed.Confirmed X.Q.prog X.counted X.FL X.α X.sinks X.roots M n s := by
  obtain ⟨P, f, hD, hcp, _, hS, hs, i, hi, hch⟩ := h
  have hl : Lower X _ := DN_lower hc hD
  obtain ⟨i', rfl, hD'⟩ := hl
  rw [List.mem_singleton.mp hi] at hch
  exact ⟨i', f, hD', supN_base hc hS i' List.mem_cons_self, hcp, hs, hch⟩

#print axioms confirmedN_base

/-- THE AGREEMENT: on a program without conjunctions, the ND confirmation and the base
    confirmation are the same. -/
theorem confirmedN_iff (hc : X.Q.conjs = []) {M : MethodId} {n : Node} {s : PFact} :
    ConfirmedN X M n s ↔ Confirmed.Confirmed X.Q.prog X.counted X.FL X.α X.sinks X.roots M n s :=
  ⟨confirmedN_base hc, confirmed_lift⟩

#print axioms confirmedN_iff

end ConjFree

/-! ## 9. Each hypothesis is necessary

  * `MarkWF` and `FiltUp`: the base counterexamples `Confirmed.CexConfFilt`, `CexConfMark` are
    programs without conjunctions; `confirmed_lift` makes them ND confirmations, and without
    conjunctions a tree witness is a `Reach` chain (`reachN_reach`), so none is real.
  * `LitConc`: `CexLitConf` below. -/

section NoConj
variable {Q : NProg}

mutual
/-- Without conjunctions a support derivation is a data flow from ONE entry location. -/
theorem taintN_flow (hc : Q.conjs = []) : ∀ {M n l L}, TaintN Q M n l L →
    ∃ l0, L = [l0] ∧ Flow Q.prog M l0 n l
  | _, _, _, _, .start M l => ⟨l, rfl, Flow.start M l⟩
  | _, _, _, _, .step h he hs => by
    have ih := taintN_flow hc h
    obtain ⟨l0, rfl, hf⟩ := ih
    exact ⟨l0, rfl, Flow.step hf he hs⟩
  | _, _, _, _, .pass h he hm => by
    have ih := taintN_flow hc h
    obtain ⟨l0, rfl, hf⟩ := ih
    exact ⟨l0, rfl, Flow.pass hf he hm⟩
  | _, _, _, _, .clean h he hcl => by
    have ih := taintN_flow hc h
    obtain ⟨l0, rfl, hf⟩ := ih
    exact ⟨l0, rfl, Flow.clean hf he hcl⟩
  | _, _, _, _, .filt h he hb => by
    have ih := taintN_flow hc h
    obtain ⟨l0, rfl, hf⟩ := ih
    exact ⟨l0, rfl, Flow.filt hf he hb⟩
  | _, _, _, _, .conj _ _ hcj _ _ _ => by
    rw [hc] at hcj
    exact absurd hcj List.not_mem_nil
  | _, _, _, _, .call he hcal hsup he2 hd2 => by
    have ihc := taintN_flow hc hcal
    have ihs := supAll_flow hc hsup
    obtain ⟨k, rfl, hfc⟩ := ihc
    obtain ⟨lk, e1, l0, rfl, hf, he1, hd1⟩ := ihs k rfl
    exact ⟨l0, rfl, Flow.call hf he he1 hd1 hfc he2 hd2⟩

theorem supAll_flow (hc : Q.conjs = []) : ∀ {M n c K L}, SupAll Q M n c K L →
    ∀ k, K = [k] → ∃ lk e l0, L = [l0] ∧ Flow Q.prog M l0 n lk ∧ e ∈ c.toCallee ∧
      den e.1 e.2 lk k
  | _, _, _, _, _, .nil => fun _ hk => nomatch hk
  | _, _, _, _, _, .cons hT he1 hd1 hS => by
    have ih := taintN_flow hc hT
    intro k hk
    obtain ⟨hkk, hK⟩ := List.cons.inj hk
    subst hkk hK
    cases hS with
    | nil =>
      obtain ⟨l0, rfl, hf⟩ := ih
      exact ⟨_, _, l0, rfl, hf, he1, hd1⟩
end

#print axioms taintN_flow

mutual
/-- Without conjunctions a tree witness is a `Reach` chain (the converse of `reach_reachN`). -/
theorem reachN_reach {roots : List MethodId} (hc : Q.conjs = []) :
    ∀ {M n l}, ReachN Q roots M n l → Reach Q.prog roots M n l
  | _, _, _, .root hM hT hz => by
    obtain ⟨l0, rfl, hf⟩ := taintN_flow hc hT
    rw [hz l0 List.mem_cons_self] at hf
    exact Reach.root hM hf
  | _, _, _, .down hE hall hT => by
    have ih := reachAll_reach hc hall
    obtain ⟨k, rfl, hfc⟩ := taintN_flow hc hT
    obtain ⟨lk, e, hR, he1, hd⟩ := ih k rfl
    exact Reach.down hR hE he1 hd hfc

theorem reachAll_reach {roots : List MethodId} (hc : Q.conjs = []) :
    ∀ {M n c K}, ReachAll Q roots M n c K → ∀ k, K = [k] →
      ∃ lk e, Reach Q.prog roots M n lk ∧ e ∈ c.toCallee ∧ den e.1 e.2 lk k
  | _, _, _, _, .nil => fun _ hk => nomatch hk
  | _, _, _, _, .cons hR he1 hd1 _ => by
    have ih := reachN_reach hc hR
    intro k hk
    rw [(List.cons.inj hk).1] at hd1
    exact ⟨_, _, ih, he1, hd1⟩
end

#print axioms reachN_reach

end NoConj

namespace CexBase
open Confirmed

/-- The filter counterexample as an ND context (no conjunctions). -/
def XF : Ctx := ⟨⟨CexConfFilt.P, []⟩, fun _ => true, 3, CexConfFilt.α, CexConfFilt.sinks, [0]⟩

/-- Without `FiltUp` the ND confirmation theorem is FALSE (all other hypotheses hold). -/
theorem cexN_filt :
    XF.Q.WF ∧ Exact.MarkWF XF.Q.prog ∧ ¬ Exact.FiltUp XF.Q.prog ∧ LitConc XF.Q ∧
    ConfirmedN XF 0 3 CexConfFilt.sinkPat ∧
    ¬ ∃ l, ReachN XF.Q XF.roots 0 3 l ∧ CexConfFilt.sinkPat.covers l := by
  obtain ⟨hwf, hmw, hnf, hconf, hnr⟩ := CexConfFilt.cex_conf_filt
  exact ⟨⟨hwf, fun _ _ _ _ h => absurd h List.not_mem_nil⟩, hmw, hnf,
    fun _ _ _ _ h => absurd h List.not_mem_nil, confirmed_lift hconf,
    fun ⟨l, hR, hcv⟩ => hnr ⟨l, reachN_reach rfl hR, hcv⟩⟩

#print axioms cexN_filt

/-- The mark counterexample as an ND context (no conjunctions). -/
def XM : Ctx := ⟨⟨CexConfMark.P, []⟩, fun _ => true, 3, CexConfMark.α, CexConfMark.sinks, [1]⟩

/-- Without `MarkWF` the ND confirmation theorem is FALSE (all other hypotheses hold). -/
theorem cexN_mark :
    XM.Q.WF ∧ Exact.FiltUp XM.Q.prog ∧ ¬ Exact.MarkWF XM.Q.prog ∧ LitConc XM.Q ∧
    ConfirmedN XM 1 2 CexConfMark.sinkPat ∧
    ¬ ∃ l, ReachN XM.Q XM.roots 1 2 l ∧ CexConfMark.sinkPat.covers l := by
  obtain ⟨hwf, hfu, hnm, hconf, hnr⟩ := CexConfMark.cex_conf_mark
  exact ⟨⟨hwf, fun _ _ _ _ h => absurd h List.not_mem_nil⟩, hfu, hnm,
    fun _ _ _ _ h => absurd h List.not_mem_nil, confirmed_lift hconf,
    fun ⟨l, hR, hcv⟩ => hnr ⟨l, reachN_reach rfl hR, hcv⟩⟩

#print axioms cexN_mark

end CexBase

/-! THE LITERAL COUNTEREXAMPLE TO THE CONFIRMATION. The root `1` makes `4 = source(5)` and calls
  the method `0` with it (base `4` to base `1`); the result base `2` comes back as base `3`. The
  method `0` cleans the mark `5` on its base `1` and then has the conjunction
  `(1,.,[any],{},*) ∧ (1,.,[any],{},*) → (2,.,$,{},9)` with an ABSTRACT literal. Run 1: the
  callee initial fact is `(1,.,*,{},*)`; the cleaner gives `(1,.,*,{},*∖{5})`; the abstract
  literal passes it (gate `ok`, cover `true`), so the ND summary `[ic, ic] → (2,$,9)` is normal.
  The root binds its fact `(4,$,5)` to both callee premises: the caller edge
  `[zero, zero] → (3,$,9)` is normal, its premises are the zero fact of the root, and the sink
  `(3,$,9)` triggers: CONFIRMED. But the only callee entry location is `1` with the mark `5`, and
  the cleaner removes it: no execution reaches the sink. Every other hypothesis holds. -/

namespace CexLitConf

def z4 : PFact := ⟨4, [], .exact, .conc 5⟩
def src : Stmt := ⟨[zeroBase], [(zeroFact, zeroFact), (zeroFact, z4)]⟩
def bnd : MicroEdge := (⟨4, [], .exact, .star⟩, ⟨1, [], .exact, .star⟩)
def back : MicroEdge := (⟨2, [], .exact, .star⟩, ⟨3, [], .exact, .star⟩)
def cc : Call := ⟨0, [4], [bnd], [back]⟩
def cl : Cleaner := ⟨1, [], .atAndBelow, some 5⟩
def lit : PFact := ⟨1, [], .any, .star⟩
def tgt : PFact := ⟨2, [], .exact, .conc 9⟩
def cj : Conj := ⟨lit, lit, tgt⟩
def sk : PFact := ⟨3, [], .exact, .conc 9⟩
def prog : Program :=
  ⟨fun _ => 0, fun _ => 2, [(1, 0, .stmt src, 1), (1, 1, .call cc, 2), (0, 0, .clean cl, 1)]⟩
def Q : NProg := ⟨prog, [(0, 1, cj, 2)]⟩
def X : Ctx := ⟨Q, fun _ => true, 3, policy (fun _ => []), [(1, 2, sk)], [1]⟩
def ic : PFact := ⟨1, [], .star (.set []), .star⟩
def a5 : AFact := ⟨⟨1, [], .exact, .conc 5⟩, false⟩
def c1 : AFact := ⟨⟨1, [], .star (.set []), .starEx [5]⟩, false⟩
def fr : AFact := ⟨sk, false⟩
def z4loc : Loc := ⟨4, [], 5⟩

theorem hE : (1, 1, Instr.call cc, 2) ∈ X.Q.prog.edges := List.Mem.tail _ List.mem_cons_self

theorem r1 : DN X (.nedge 1 [zeroFact] 1 ⟨z4, false⟩) :=
  DN.step (DN.start (DN.root List.mem_cons_self)) List.mem_cons_self (by decide)

/-- The ND summary of the callee: `[ic, ic] → (2,$,9)`, normal. -/
theorem gEdge : DN X (.nedge 0 [ic, ic] 2 (conjFact cj c1 c1)) := by
  have h3 : DN X (.nadded 0 a5.fact) :=
    DN.added (a := a5) (c := cc) (e := bnd) r1 hE List.mem_cons_self (by decide)
  have h4 := DN.initA h3
  have e : X.α 0 a5.fact = ic := by decide
  rw [e] at h4
  have h5 : DN X (.nedge 0 [ic] 1 c1) :=
    DN.clean (DN.start h4) (List.Mem.tail _ (List.Mem.tail _ List.mem_cons_self)) (by decide)
  exact DN.conj h5 h5 List.mem_cons_self (by decide) rfl (by decide) rfl

/-- The root binds `(4,$,5)` to both callee premises: the edge `[zero, zero] → (3,$,9)`. -/
theorem fEdge : DN X (.nedge 1 [zeroFact, zeroFact] 2 fr) := by
  have hop := DN.ndOpen (M := 1) (n := 1) (n' := 2) hE gEdge (by decide)
  have hb1 := DN.ndBind hop r1 List.mem_cons_self (a := a5) (by decide) (by decide)
  have hb2 := DN.ndBind hb1 r1 List.mem_cons_self (a := a5) (by decide) (by decide)
  have hr := DN.ndRet hb2 List.mem_cons_self (r := fr) (by decide)
  have e : limitF X.counted X.FL fr = fr := by decide
  rw [e] at hr
  exact hr

theorem confirmed : ConfirmedN X 1 2 sk :=
  ⟨[zeroFact, zeroFact], fr, fEdge, by decide,
    fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨rfl, zeroMark, rfl⟩
      · rw [List.mem_singleton.mp hp]; exact ⟨rfl, zeroMark, rfl⟩,
    SupN.root List.mem_cons_self (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact List.mem_singleton.mp hp),
    List.mem_cons_self, zeroFact, List.mem_cons_self, by decide⟩

#print axioms confirmed

/-- A micro edge to an exact concrete target gives its location. -/
theorem den_target_conc {e1 e2 : PFact} {l l' : Loc} {t : Mark} (hk : e2.kind = .exact)
    (hm : e2.mark = .conc t) (hd : den e1 e2 l l') : l' = ⟨e2.base, e2.path, t⟩ := by
  obtain ⟨_, hb, _, hm', _, σ, τ, _, hp, _, ht⟩ := hd
  have ht' : τ = [] := by rw [hk] at ht; exact ht
  refine Confirmed.loc_eq hb (by rw [hp, ht', List.append_nil]) (by rw [hm', hm]; rfl)

/-- A mark-agnostic micro edge between exact positions keeps the mark. -/
theorem den_target_star {e1 e2 : PFact} {l l' : Loc} (hk2 : e2.kind = .exact) (hm : e2.mark = .star) (hd : den e1 e2 l l') :
    l' = ⟨e2.base, e2.path, l.mark⟩ := by
  obtain ⟨_, hb, _, hm', _, σ, τ, _, hp, _, ht⟩ := hd
  have ht' : τ = [] := by rw [hk2] at ht; exact ht
  refine Confirmed.loc_eq hb (by rw [hp, ht', List.append_nil]) (by rw [hm', hm]; rfl)

theorem src_step {l' : Loc} (h : src.step zeroLoc l') : l' = zeroLoc ∨ l' = z4loc := by
  rcases h with ⟨hm, _⟩ | ⟨e, he, hd⟩
  · exact absurd hm (by decide)
  · cases he with
    | head => exact .inl (den_target_conc rfl rfl hd)
    | tail _ h =>
      cases h with
      | head => exact .inr (den_target_conc rfl rfl hd)
      | tail _ h => cases h

/-- The callee `0`: a location after the cleaner has an uncleaned, non-empty support. -/
theorem taint0 : ∀ {M n l L}, TaintN Q M n l L → M = 0 →
    (n = 0 → L = [l]) ∧ (n ≠ 0 → ∀ k, k ∈ L → cl.cleansB k = false) ∧ L ≠ []
  | _, _, _, _, .start _ l => fun _ =>
    ⟨fun _ => rfl, fun hn => absurd rfl hn, List.cons_ne_nil _ _⟩
  | _, _, _, _, .step _ hE _ => by
    cases hE with
    | head => intro hM; exact absurd hM (by decide)
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .pass _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | head => intro hM; exact absurd hM (by decide)
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .clean h hE hc => by
    have ih := taint0 h
    cases hE with
    | tail _ h' =>
      cases h' with
      | tail _ h'' =>
        cases h'' with
        | head =>
          intro _
          have hL := (ih rfl).1 rfl
          subst hL
          refine ⟨fun h1 => absurd h1 (by decide), fun _ k hk => ?_, List.cons_ne_nil _ _⟩
          rw [List.mem_singleton.mp hk]
          exact hc
        | tail _ h3 => cases h3
  | _, _, _, _, .filt _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .conj h1 h2 hcj _ _ _ => by
    have i1 := taint0 h1
    have i2 := taint0 h2
    cases hcj with
    | head =>
      intro _
      obtain ⟨_, a1, n1⟩ := i1 rfl
      obtain ⟨_, a2, _⟩ := i2 rfl
      refine ⟨fun h => absurd h (by decide), fun _ k hk => ?_,
        fun he => n1 (List.append_eq_nil_iff.mp he).1⟩
      rcases List.mem_append.mp hk with hk | hk
      · exact a1 (by decide) k hk
      · exact a2 (by decide) k hk
    | tail _ h => cases h
  | _, _, _, _, .call hE _ _ _ _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | head => intro hM; exact absurd hM (by decide)
      | tail _ h =>
        cases h with
        | tail _ h => cases h

/-- The root `1` at the nodes `0` and `1`, from the zero location: only the zero location and
    `4` with the mark `5`. -/
theorem taint1 : ∀ {M n l L}, TaintN Q M n l L → M = 1 → (∀ k, k ∈ L → k = zeroLoc) →
    (n = 0 → l = zeroLoc) ∧ (n = 1 → l = zeroLoc ∨ l = z4loc)
  | _, _, _, _, .start _ l => fun _ hz =>
    ⟨fun _ => hz l List.mem_cons_self, fun h1 => absurd (show (0 : Nat) = 1 from h1) (by decide)⟩
  | _, _, _, _, .step h hE hs => by
    have ih := taint1 h
    cases hE with
    | head =>
      intro _ hz
      have hl := (ih rfl hz).1 rfl
      subst hl
      exact ⟨fun h0 => absurd h0 (by decide), fun _ => src_step hs⟩
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .pass _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | head => intro _ _; exact ⟨fun h0 => absurd h0 (by decide), fun h1 => absurd h1 (by decide)⟩
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .clean _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head => intro hM; exact absurd hM (by decide)
        | tail _ h => cases h
  | _, _, _, _, .filt _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .conj _ _ hcj _ _ _ => by
    cases hcj with
    | head => intro hM; exact absurd hM (by decide)
    | tail _ h => cases h
  | _, _, _, _, .call hE _ _ _ _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | head => intro _ _; exact ⟨fun h0 => absurd h0 (by decide), fun h1 => absurd h1 (by decide)⟩
      | tail _ h =>
        cases h with
        | tail _ h => cases h

/-- The root `1` at the node `2`, from the zero location: never the base `3`. The call needs a
    callee entry location bound from `4` with the mark `5`, and the callee cleans it. -/
theorem taint1_exit : ∀ {M n l L}, TaintN Q M n l L → M = 1 → n = 2 →
    (∀ k, k ∈ L → k = zeroLoc) → l.base ≠ 3
  | _, _, _, _, .start _ _ => fun _ hn => absurd (show (0 : Nat) = 2 from hn) (by decide)
  | _, _, _, _, .step _ hE _ => by
    cases hE with
    | head => intro _ hn; exact absurd hn (by decide)
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .pass h hE _ => by
    cases hE with
    | tail _ h' =>
      cases h' with
      | head =>
        intro _ _ hz
        rcases (taint1 h rfl hz).2 rfl with rfl | rfl
        · decide
        · decide
      | tail _ h' =>
        cases h' with
        | tail _ h' => cases h'
  | _, _, _, _, .clean _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head => intro hM; exact absurd hM (by decide)
        | tail _ h => cases h
  | _, _, _, _, .filt _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .conj _ _ hcj _ _ _ => by
    cases hcj with
    | head => intro hM; exact absurd hM (by decide)
    | tail _ h => cases h
  | _, _, _, _, .call hE hcal hsup _ _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        intro _ _ hz
        obtain ⟨_, hcl, hne⟩ := taint0 hcal rfl
        cases hsup with
        | nil => exact absurd rfl hne
        | cons hT he1 hd1 _ =>
          have hzk : ∀ k, k ∈ _ → k = zeroLoc := fun k hk => hz k (List.mem_append_left _ hk)
          cases he1 with
          | head =>
            have hlk := (taint1 hT rfl hzk).2 rfl
            have hb4 : _ = (4 : Nat) := hd1.1
            rcases hlk with rfl | rfl
            · exact absurd hb4 (by decide)
            · have hk := den_target_star rfl rfl hd1
              have hc := hcl (by decide) _ List.mem_cons_self
              rw [hk] at hc
              exact absurd hc (by decide)
          | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem not_reach : ∀ {M n l}, ReachN Q [1] M n l → M = 1 → n = 2 → l.base = 3 → False
  | _, _, _, .root _ hT hz => fun hM hn hb => taint1_exit hT hM hn hz hb
  | _, _, _, .down hE _ _ => fun hM _ _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | head => exact absurd hM (by decide)
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem not_real : ¬ ∃ l, ReachN X.Q X.roots 1 2 l ∧ sk.covers l :=
  fun ⟨_, hR, hc⟩ => not_reach hR rfl rfl hc.1

theorem wf : X.Q.WF where
  prog := {
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
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
    toStar := by
      intro M n c n' hE e he
      cases hE with
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h =>
          cases h with
          | tail _ h => cases h
    fromStar := by
      intro M n c n' hE e he
      cases hE with
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h =>
          cases h with
          | tail _ h => cases h
    filtPrefix := by
      intro M n b may n' hE
      cases hE with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h }
  target := by
    intro M n cj' n' hE
    cases hE with
    | head => exact ⟨⟨9, rfl⟩, rfl⟩
    | tail _ h => cases h

theorem markWF : Exact.MarkWF X.Q.prog where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h =>
        cases h with
        | head => rfl
        | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  toC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  fromC := by
    intro M n c n' hE e he
    cases hE with
    | tail _ h =>
      cases h with
      | head =>
        cases he with
        | head => rfl
        | tail _ h => cases h
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem filtUp : Exact.FiltUp X.Q.prog := by
  intro M n b may n' hE
  cases hE with
  | tail _ h =>
    cases h with
    | tail _ h =>
      cases h with
      | tail _ h => cases h

theorem not_litConc : ¬ LitConc X.Q := by
  intro h
  obtain ⟨⟨T, hT⟩, _⟩ := h 0 1 cj 2 List.mem_cons_self
  cases hT

/-- THE LITERAL COUNTEREXAMPLE TO THE CONFIRMATION: every hypothesis of `confirmed_real_N`
    except `LitConc` holds (and `ConjOK`, and the run-1 policy is applicable); the vulnerability
    is confirmed, but no tree witness reaches the sink. -/
theorem cex_lit_conf :
    X.Q.WF ∧ Exact.MarkWF X.Q.prog ∧ Exact.FiltUp X.Q.prog ∧ ConjOK X.Q (fun _ => True) ∧
    (∀ m a, applicable (X.α m a) a = true) ∧ ¬ LitConc X.Q ∧ ConfirmedN X 1 2 sk ∧
    ¬ ∃ l, ReachN X.Q X.roots 1 2 l ∧ sk.covers l :=
  ⟨wf, markWF, filtUp, conjOK_true _, policy_applicable _, not_litConc, confirmed, not_real⟩

#print axioms cex_lit_conf

end CexLitConf

/-! THE `ConjOK` COUNTEREXAMPLE TO THE VALID FORM. The root `0`: a source gives the normal
  `[any]` fact `(1,.,[any],{},7)` and the exact `(4,.,$,{},8)`; a type filter on the base `1`
  admits only the path `[]`; the read `2 = 1.7` gives the exact `(2,.,$,{},7)`; the conjunction
  `(2,$,7) ∧ (4,$,8) → (3,$,9)` and the sink `(3,$,9)`. The valid locations: the zero base,
  `1.[]`, and the bases `3` and `4`. `FiltValid`, `BackOK` (the read ends at the invalid base
  `2`), `LitConc` and the validity of the sink locations hold; `ConjOK` fails (the target is
  valid, the literal `2` is not). The vulnerability is confirmed, but the filter rejects `1.7`,
  so no execution reaches the sink. -/

namespace CexConjOKConf

def zAny : PFact := ⟨1, [], .any, .conc 7⟩
def z4 : PFact := ⟨4, [], .exact, .conc 8⟩
def src : Stmt := ⟨[zeroBase], [(zeroFact, zAny), (zeroFact, z4)]⟩
def may (p : List Acc) : Bool := p.isEmpty
def rd : MicroEdge := (⟨1, [7], .exact, .star⟩, ⟨2, [], .exact, .star⟩)
def s2 : Stmt := ⟨[1], [rd]⟩
def lit1 : PFact := ⟨2, [], .exact, .conc 7⟩
def tgt : PFact := ⟨3, [], .exact, .conc 9⟩
def cj : Conj := ⟨lit1, z4, tgt⟩
def prog : Program :=
  ⟨fun _ => 0, fun _ => 4, [(0, 0, .stmt src, 1), (0, 1, .filt 1 may, 2), (0, 2, .stmt s2, 3)]⟩
def Q : NProg := ⟨prog, [(0, 3, cj, 4)]⟩
def X : Ctx := ⟨Q, fun _ => true, 3, fun _ a => a, [(0, 4, tgt)], [0]⟩
def ok (l : Loc) : Prop := l.base = 0 ∨ (l.base = 1 ∧ l.path = []) ∨ l.base = 3 ∨ l.base = 4

theorem e0 : DN X (.nedge 0 [zeroFact] 0 ⟨zeroFact, false⟩) := DN.start (DN.root List.mem_cons_self)

theorem cEdge : DN X (.nedge 0 [zeroFact, zeroFact] 4 (conjFact cj ⟨lit1, false⟩ ⟨z4, false⟩)) := by
  have e1 : DN X (.nedge 0 [zeroFact] 1 ⟨zAny, false⟩) := DN.step e0 List.mem_cons_self (by decide)
  have f1 : DN X (.nedge 0 [zeroFact] 1 ⟨z4, false⟩) := DN.step e0 List.mem_cons_self (by decide)
  have hF : (0, 1, Instr.filt 1 may, 2) ∈ X.Q.prog.edges := List.Mem.tail _ List.mem_cons_self
  have hR : (0, 2, Instr.stmt s2, 3) ∈ X.Q.prog.edges :=
    List.Mem.tail _ (List.Mem.tail _ List.mem_cons_self)
  have e2 : DN X (.nedge 0 [zeroFact] 2 ⟨zAny, false⟩) := DN.filt e1 hF (fun _ => rfl)
  have f2 : DN X (.nedge 0 [zeroFact] 2 ⟨z4, false⟩) :=
    DN.filt f1 hF (fun h => absurd h (by decide))
  have e3 : DN X (.nedge 0 [zeroFact] 3 ⟨lit1, false⟩) := DN.step e2 hR (by decide)
  have f3 : DN X (.nedge 0 [zeroFact] 3 ⟨z4, false⟩) := DN.step f2 hR (by decide)
  exact DN.conj e3 f3 List.mem_cons_self (by decide) rfl (by decide) rfl

theorem confirmed : ConfirmedN X 0 4 tgt :=
  ⟨[zeroFact, zeroFact], _, cEdge, by decide,
    fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨rfl, zeroMark, rfl⟩
      · rw [List.mem_singleton.mp hp]; exact ⟨rfl, zeroMark, rfl⟩,
    SupN.root List.mem_cons_self (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact List.mem_singleton.mp hp),
    List.mem_cons_self, zeroFact, List.mem_cons_self, by decide⟩

#print axioms confirmed

/-- The locations of the root from the zero location, node by node. -/
abbrev Inv (n : Node) (l : Loc) : Prop :=
  (n = 0 → l = zeroLoc) ∧ (n = 1 → l.base ≠ 2) ∧ (n = 2 → l.base ≠ 2 ∧ (l.base = 1 → l.path = [])) ∧
    (n = 3 → l.base ≠ 2) ∧ n ≠ 4

theorem taint_inv : ∀ {M n l L}, TaintN Q M n l L → M = 0 → (∀ k, k ∈ L → k = zeroLoc) →
    Inv n l
  | _, _, _, _, .start _ l => fun _ hz =>
    ⟨fun _ => hz l List.mem_cons_self, fun h => absurd (show (0 : Nat) = 1 from h) (by decide),
      fun h => absurd (show (0 : Nat) = 2 from h) (by decide),
      fun h => absurd (show (0 : Nat) = 3 from h) (by decide),
      fun h => absurd (show (0 : Nat) = 4 from h) (by decide)⟩
  | _, _, _, _, @TaintN.step _ _ _ _ _ _ l' _ h hE hs => by
    have ih := taint_inv h
    cases hE with
    | head =>
      intro _ hz
      have hl := (ih rfl hz).1 rfl
      subst hl
      have hb : l'.base ≠ 2 := by
        rcases hs with ⟨hm, _⟩ | ⟨e, he, hd⟩
        · exact absurd hm (by decide)
        · have hb' := hd.2.1
          cases he with
          | head => rw [hb']; decide
          | tail _ h =>
            cases h with
            | head => rw [hb']; decide
            | tail _ h => cases h
      exact ⟨fun h => absurd h (by decide), fun _ => hb, fun h => absurd h (by decide),
        fun h => absurd h (by decide), by decide⟩
    | tail _ h' =>
      cases h' with
      | tail _ h'' =>
        cases h'' with
        | head =>
          intro _ hz
          obtain ⟨hb2, hp1⟩ := (ih rfl hz).2.2.1 rfl
          have hb : l'.base ≠ 2 := by
            rcases hs with ⟨_, rfl⟩ | ⟨e, he, hd⟩
            · exact hb2
            · cases he with
              | head =>
                obtain ⟨hb0, _, _, _, _, σ, _, hp0, _, _, _⟩ := hd
                have hp := hp1 hb0
                rw [hp] at hp0
                cases hp0
              | tail _ h => cases h
          exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
            fun h => absurd h (by decide), fun _ => hb, by decide⟩
        | tail _ h3 => cases h3
  | _, _, _, _, .pass _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, .clean _ hE _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  | _, _, _, _, @TaintN.filt _ _ _ l _ _ _ _ h hE hb => by
    have ih := taint_inv h
    cases hE with
    | tail _ h' =>
      cases h' with
      | head =>
        intro _ hz
        obtain ⟨_, hb1, _, _, _⟩ := ih rfl hz
        refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
          fun _ => ⟨hb1 rfl, fun h1 => ?_⟩, fun h => absurd h (by decide), by decide⟩
        have hm := hb h1
        cases hlp : l.path with
        | nil => rfl
        | cons a p => rw [hlp] at hm; cases hm
      | tail _ h'' =>
        cases h'' with
        | tail _ h3 => cases h3
  | _, _, _, _, .conj h1 _ hcj hc1 _ _ => by
    have i1 := taint_inv h1
    cases hcj with
    | head =>
      intro _ hz
      obtain ⟨_, _, _, hb3, _⟩ := i1 rfl (fun k hk => hz k (List.mem_append_left _ hk))
      exact absurd hc1.1 (hb3 rfl)
    | tail _ h => cases h
  | _, _, _, _, .call hE _ _ _ _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem not_reach : ∀ {M n l}, ReachN Q [0] M n l → M = 0 → n = 4 → False
  | _, _, _, .root _ hT hz => fun hM hn => (taint_inv hT hM hz).2.2.2.2 hn
  | _, _, _, .down hE _ _ => by
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem not_real : ¬ ∃ l, ReachN X.Q X.roots 0 4 l ∧ tgt.covers l :=
  fun ⟨_, hR, _⟩ => not_reach hR rfl rfl

theorem wf : X.Q.WF where
  prog := {
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
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | head =>
            cases he with
            | head => rfl
            | tail _ h => cases h
          | tail _ h => cases h
    toStar := by
      intro M n c n' hE
      cases hE with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
    fromStar := by
      intro M n c n' hE
      cases hE with
      | tail _ h =>
        cases h with
        | tail _ h =>
          cases h with
          | tail _ h => cases h
    filtPrefix := by
      intro M n b may' n' hE p q h
      cases hE with
      | tail _ h' =>
        cases h' with
        | head =>
          cases p with
          | nil => rfl
          | cons a p => cases h
        | tail _ h'' =>
          cases h'' with
          | tail _ h3 => cases h3 }
  target := by
    intro M n cj' n' hE
    cases hE with
    | head => exact ⟨⟨9, rfl⟩, rfl⟩
    | tail _ h => cases h

theorem markWF : Exact.MarkWF X.Q.prog where
  stmt := by
    intro M n s n' hE e he
    cases hE with
    | head =>
      cases he with
      | head => rfl
      | tail _ h =>
        cases h with
        | head => rfl
        | tail _ h => cases h
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head => rfl
          | tail _ h => cases h
        | tail _ h => cases h
  toC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  fromC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem filtValid : Exact.FiltValid X.Q.prog ok := by
  intro M n b may' n' hE l hok hb
  cases hE with
  | tail _ h =>
    cases h with
    | head =>
      rcases hok with h0 | ⟨_, hp⟩ | h3 | h4
      · rw [hb] at h0; cases h0
      · show l.path.isEmpty = true
        rw [hp]
        rfl
      · rw [hb] at h3; cases h3
      · rw [hb] at h4; cases h4
    | tail _ h =>
      cases h with
      | tail _ h => cases h

/-- Every source edge starts at the zero base; the read ends at the invalid base `2`. -/
theorem backOK : Exact.BackOK X.Q.prog ok where
  stmt := by
    intro M n s n' hE e he l1 l2 hd hok
    cases hE with
    | head =>
      have h0 : l1.base = 0 := by
        cases he with
        | head => exact hd.1
        | tail _ h =>
          cases h with
          | head => exact hd.1
          | tail _ h => cases h
      exact .inl h0
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | head =>
          cases he with
          | head =>
            have hb : l2.base = 2 := hd.2.1
            rcases hok with h0 | ⟨h1, _⟩ | h3 | h4
            · rw [hb] at h0; cases h0
            · rw [hb] at h1; cases h1
            · rw [hb] at h3; cases h3
            · rw [hb] at h4; cases h4
          | tail _ h => cases h
        | tail _ h => cases h
  toC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h
  fromC := by
    intro M n c n' hE
    cases hE with
    | tail _ h =>
      cases h with
      | tail _ h =>
        cases h with
        | tail _ h => cases h

theorem litConc : LitConc X.Q := by
  intro M n cj' n' hE
  cases hE with
  | head => exact ⟨⟨7, rfl⟩, ⟨8, rfl⟩⟩
  | tail _ h => cases h

theorem not_conjOK : ¬ ConjOK X.Q ok := by
  intro h
  have h1 := (h 0 3 cj 4 List.mem_cons_self ⟨2, [], 7⟩ ⟨3, [], 9⟩ ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩
    (.inr (.inr (.inl rfl)))).1 ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩
  rcases h1 with h0 | ⟨h1, _⟩ | h3 | h4
  · cases h0
  · cases h1
  · cases h3
  · cases h4

theorem sink_ok : ∀ l, tgt.covers l → ok l := fun _ hc => .inr (.inr (.inl hc.1))

/-- THE `ConjOK` COUNTEREXAMPLE TO `confirmed_real_N_valid`: every other hypothesis holds, every
    location of the sink pattern is valid, the vulnerability is confirmed, and no tree witness
    reaches the sink. -/
theorem cex_conjOK_conf :
    X.Q.WF ∧ Exact.MarkWF X.Q.prog ∧ Exact.FiltValid X.Q.prog ok ∧ Exact.BackOK X.Q.prog ok ∧
    LitConc X.Q ∧ ¬ ConjOK X.Q ok ∧ (∀ l, tgt.covers l → ok l) ∧ ConfirmedN X 0 4 tgt ∧
    ¬ ∃ l, ReachN X.Q X.roots 0 4 l ∧ tgt.covers l :=
  ⟨wf, markWF, filtValid, backOK, litConc, not_conjOK, sink_ok, confirmed, not_real⟩

#print axioms cex_conjOK_conf

end CexConjOKConf

end ApSpec.NDConfirmed
