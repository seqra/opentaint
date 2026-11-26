/-
  ApSpec.BackNDRefine — rule B3: the backward seed of a literal of an ND sink is REFINED by the
  inputs that the forward run captured for that literal.

  ## What is modelled

  An ND sink is a condition alternative with two or more positive literals (for example
  `ContainsMark(a, T) AND ContainsMarkOnAnyField(b, U)`). Today (ap.md §9.2 SEEDS, interpreter.md
  §4.8 CURRENT PREDICATE REVERSAL, §4.9 SEEDS) the backward run after a forward run that reports a
  DEMAND witness of it seeds the FULL pattern of every positive literal (`b.[any] (U)` for an
  `[any]` literal). The seed does not change from run to run, so a witness that stays DEMAND gives
  the same backward output each time.

  Rule B3. The forward run CAPTURES, for each literal `j` of the witness, the input facts that
  satisfied `j` in ALL completed combinations of the witness (not only the selected proof): the
  capture `cap : Cap`, a list of `(j, a, aex)` (literal index, captured input fact with a concrete
  mark, its `[any-taint]` exclusion). The backward seed of literal `j` (`refine lits cap`) is:
    * `cap` has entries for `j`: the location MEET of the literal pattern `lits[j]` with each of
      them (`meetLit`), dropping the empty meets;
    * `cap` has no entry for `j` (an OR branch with no witness, an end-fact trigger): the full
      pattern `(j, lits[j], Excl.empty)`, as today (the FALLBACK).
  The meet is the emission of ap.md §6.3 for a concrete pattern: `meetLit = emitX`
  (`AnyTaintExDefs.lean`), the location intersection of an added fact (here: the captured input)
  with a concrete pattern (here: the literal). `meetLit_inter` proves that for a concrete captured
  input it is EXACTLY the intersection, exclusions and marks included. The same refinement applies
  to the reversed literals of an ND source, with the inputs captured at the source statement: the
  definitions and theorems below read only patterns and captured inputs, not the role.

  ## Results (constructive; see the `#print axioms` lines)

    `meetLit_inter`        the meet of a literal `d` with a concrete captured input `(a, aex)` covers
                           exactly the locations of `d` that `(a, aex)` covers.
    `meetLit_forget_inside` the meet with its exclusion forgotten (the backward form, below) still
                           lies inside the literal.
    `mem_refine`, `mem_refine3` the members of `refine`: fallbacks and meets.
    `emitX_split`          the two rows of `emitX` that give a result.
    1 `refine_cover`       a location of `lits[j]` covered by a concrete captured input of `j` is
                           covered by a refined seed of `j`.
    2 `refine_fallback`    no captured input for `j`: the only refined seed of `j` is today's seed
                           `(j, lits[j], Excl.empty)`, which covers every location of `lits[j]`.
    3 `refine_inside`      every refined seed of `j` lies inside `lits[j]` (never wider than today),
                           and a seed that is not a fallback lies inside the captured input it came
                           from (and is the meet of the two).
    4 `refine_sound`       with `ForwardCapturedF lits cap Real` every `Real j l` is covered by a
                           refined seed of `j`; `refine_sound_strict` with the stricter
                           `ForwardCaptured` of the task. `forwardCaptured_of_combos`: capturing
                           every input of EVERY completed combination gives `ForwardCaptured` from
                           the forward coverage of the real vulnerabilities (`CombosCover`).
    5 `refine_mono`        captured inputs that shrink (each one inside a captured input of `cap`
                           with the same index) and no NEW fallback give refined seeds inside the
                           refined seeds of `cap` with the same index; `refine_mono_seq`: the same
                           over a sequence of runs.
    6 `refine_det`, `refine_det_set` equal inputs (or inputs with the same members) give equal seeds
                           (seeds with the same members). `refine_shape`: a seed path is the literal
                           path or a captured path, its exclusion is empty or a captured one;
                           `refine_length`: `(refine lits cap).length ≤ cap.length + lits.length`.
                           No new depth: the seeds stay in a finite universe when the captured
                           depths are bounded. `refine_legal`: with literal patterns and captured
                           inputs of tail `$`/`[any]` and concrete marks, every seed has the tail
                           `$`/`[any]` and a concrete mark (a legal `Backward.DB` seed).
    7 `Vec.cex_selected_only` two completed combinations (two routes) give the inputs `x.a $` and
                           `x.b $` for the literal `x.[any]`; with only the selected proof's input
                           captured, the real location `x.b` is covered by no refined seed, while
                           the capture of both combinations covers it (`Vec.all_combos_cover`,
                           `Vec.all_covers_locB`). So `ForwardCaptured` needs the inputs of ALL
                           completed combinations. `Vec.meet_rows`: the rows of the meet.
    8 STRETCH (done): `Backward.B_general` and `Backward.B_fragment_rep` read the seeds only through
                           `demanded_gen` / `demanded_fragment`: a seed `(M, n, s')` with a concrete
                           mark, the tail `$`/`[any]` and `s'.covers l` for the witness location
                           `l`. `SeedsCover` is that contract; `B_general_cov`, `B_fragment_rep_cov`
                           are the two theorems with it in place of "every reported sink is
                           seeded" (`seedsCover_full` gives back the old hypothesis).
                           `seedsCover_refined`: the refined seeding (`RefinedSeeding`) satisfies
                           `SeedsCover`; `B_general_refined`, `iteration_general_refined`: contract
                           B and the general iteration theorem with refined seeds.

  ## Hypotheses

    * `CapConc cap`: every captured input has a concrete mark (needed by `refine_inside`,
      `refine_sound`, `refine_mono`; `refine_cover` needs it for the one input it uses).
    * `ForwardCaptured lits cap Real` (task form): every `Real j l` is covered by `lits[j]` and by
      a captured input of `j`. `ForwardCapturedF` is weaker: a literal with no captured input needs
      only the cover by `lits[j]` (the fallback serves it).
    * `refine_mono`: every captured input of `cap'` lies inside a captured input of `cap` with the
      same index, and every literal that has an input in `cap` has one in `cap'` (no new fallback;
      the task's "`cap'` has an entry for `j` iff `cap` has" implies it).
    * Stretch: the hypotheses of `B_general` / `B_fragment_rep` without the sink-seeding one, and
      `RefinedSeeding`: each reported sink pattern `s` is the literal `j` of a literal list whose
      capture is well formed (`CapWF`) and covers every witness location of that literal
      (`ForwardCapturedF` for the witness predicate of the contract), and whose refined seeds (the
      exclusion forgotten, `seedsAt`) are seeded at its `(M, n)`; the sinks have the tail
      `$`/`[any]` (as in `B_general`).

  ## Counterexamples

    (all in the namespace `Vec`)
    * `cex_selected_only` (above).
    * `cex_abstract_mark`: a captured input with the mark `*` meets nothing (`emitX` needs the mark
      of a concrete pattern), so the literal gets NO seed at all (not even the fallback, since it
      has an entry), although the input covers a location of the literal. DESIGN POINT: the
      capture must store the concrete mark that the sink check matched (in run 1 a `*`-marked fact
      triggers through the mark of its initial fact, `check`).
    * `cex_star_capture`: a captured input with a `*/E` tail gives a seed with a `*` tail and a
      concrete mark, which is not a legal `DB` seed (`Backward.legal_seed`). DESIGN POINT: the
      capture must store a `*/E` input as `[any]` with the exclusion `E` (the same location set).
    * `cex_mono_fallback`: a literal that LOSES all its captured inputs falls back to the full
      pattern, so the seeds grow: the "no new fallback" hypothesis of `refine_mono` is needed.
      DESIGN POINT: the per-run seed of a DEMAND witness is non-increasing only while the set of
      literals with captured inputs does not shrink (for example, if another alternative of the
      same occurrence completes in a later run, the literals of the first one fall back).

  ## Model and production

    * The production capture is per (method key, statement, rule occurrence, literal); the model
      takes the capture of ONE witness occurrence, so the key is implicit and the index is the
      literal. The stretch attaches the seeds of one witness to its `(M, n)`.
    * The layer of a refined seed stays DEMAND; layers are not modelled here (a seed is a pattern
      with an exclusion; `Backward.DB.seed` puts it in the normal layer of the base model, which
      the base theorems allow).
    * The backward run has no `[any-taint]` (I14): a backward `[any]` has no exclusion, so the
      production seed is the meet WITH ITS EXCLUSION FORGOTTEN. That is wider than the meet, still
      inside the literal (`meetLit_forget_inside`, `refine_forget_inside`); the stretch uses this
      form (`seedsAt`). `refine_mono` is stated for the meets with their exclusions.
    * The seed is cut by the backward field limit in `DB.seed` (`limitF`), as today.
    * The base model has no ND sink: a literal is checked as its own sink. So the stretch reads the
      ND literal `j` as the sink `(M, n, lits[j])`, and `RefinedSeeding` asks that the capture
      covers every witness location of the literal (the base contract `BackwardContractD` quantifies
      over every den-aware location of a reported sink pattern). For a real ND sink the capture
      covers only the locations that take part in a real vulnerability (all positive literals of an
      alternative real, `forwardCaptured_of_combos`); the base contract asks more. The change that
      the ND case needs is in the contract, not in the seed lemma: an ND form of
      `BackwardContractD` (and of `vuln_foundR` / `iteration_invariant_D`) whose witness is a real
      ND vulnerability. `demanded_gen` itself needs no change: it takes any covering seed.
-/
import ApSpec.AnyTaintExCov
import ApSpec.HandoffXRestrict
import ApSpec.Backward

namespace ApSpec.BackND
open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx

/-! ## 1. The capture and the refined seeds -/

/-- The capture of one witness occurrence: `(j, a, aex)` = literal index, captured input fact (a
    concrete mark, the tail `$` or `[any]`), its exclusion. -/
abbrev Cap := List (Nat × PFact × Excl)

/-- A backward seed: literal index, pattern, exclusion. -/
abbrev Seed := Nat × PFact × Excl

/-- The capture has an input for the literal `j`. -/
def hasCap (cap : Cap) (j : Nat) : Bool := cap.any (fun e => e.1 == j)

/-- The meet of the literal pattern `d` with the captured input `(a, aex)`: the emission of
    ap.md §6.3 (`emitX`), the location intersection of an added fact with a concrete pattern. -/
def meetLit (d a : PFact) (aex : Excl) : Option (PFact × Excl) := emitX d a aex

/-- Today's seeds for the literals that have no captured input. -/
def fallbacks (lits : List PFact) (cap : Cap) : List Seed :=
  lits.zipIdx.filterMap (fun x => if hasCap cap x.2 then none else some (x.2, x.1, Excl.empty))

/-- The meets of every captured input with its literal (the empty meets dropped). -/
def meets (lits : List PFact) (cap : Cap) : List Seed :=
  cap.filterMap (fun e =>
    match lits[e.1]? with
    | none   => none
    | some d => (meetLit d e.2.1 e.2.2).map (fun p => (e.1, p.1, p.2)))

/-- RULE B3: the refined backward seeds of the literals `lits` with the capture `cap`. -/
def refine (lits : List PFact) (cap : Cap) : List Seed := fallbacks lits cap ++ meets lits cap

/-- Every captured input has a concrete mark. -/
def CapConc (cap : Cap) : Prop := ∀ e, e ∈ cap → ∃ t, e.2.1.mark = .conc t

/-- Every captured input has a concrete mark and the tail `$` or `[any]`. -/
def CapWF (cap : Cap) : Prop :=
  ∀ e, e ∈ cap → (∃ t, e.2.1.mark = .conc t) ∧ (e.2.1.kind = .exact ∨ e.2.1.kind = .any)

/-- The task form: every real location of literal `j` is covered by `lits[j]` and by a captured
    input of `j`. -/
def ForwardCaptured (lits : List PFact) (cap : Cap) (Real : Nat → Loc → Prop) : Prop :=
  ∀ j l, Real j l → ∃ d : PFact, lits[j]? = some d ∧ d.covers l ∧
    ∃ (a : PFact) (aex : Excl), (j, a, aex) ∈ cap ∧ coversX a aex l

/-- The weaker form: a literal with captured inputs needs a captured input that covers its real
    location; a literal with none is served by the fallback. -/
def ForwardCapturedF (lits : List PFact) (cap : Cap) (Real : Nat → Loc → Prop) : Prop :=
  ∀ j l, Real j l → ∃ d : PFact, lits[j]? = some d ∧ d.covers l ∧
    (hasCap cap j = true → ∃ (a : PFact) (aex : Excl), (j, a, aex) ∈ cap ∧ coversX a aex l)

theorem capWF_conc {cap : Cap} (h : CapWF cap) : CapConc cap := fun e he => (h e he).1

/-! ## 2. Small lemmas -/

theorem hasCap_iff {cap : Cap} {j : Nat} : hasCap cap j = true ↔ ∃ a aex, (j, a, aex) ∈ cap := by
  unfold hasCap
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨j', a, aex⟩, hm, hj⟩
    have hj' : j' = j := beq_iff_eq.mp hj
    subst hj'
    exact ⟨a, aex, hm⟩
  · rintro ⟨a, aex, hm⟩
    exact ⟨(j, a, aex), hm, beq_iff_eq.mpr rfl⟩

theorem hasCap_of_mem {cap : Cap} {j : Nat} {a : PFact} {aex : Excl} (h : (j, a, aex) ∈ cap) :
    hasCap cap j = true :=
  hasCap_iff.mpr ⟨a, aex, h⟩

theorem not_mem_of_hasCap {cap : Cap} {j : Nat} (h : hasCap cap j = false) (a : PFact) (aex : Excl) :
    (j, a, aex) ∉ cap := by
  intro hm
  rw [hasCap_of_mem hm] at h
  cases h

theorem mem_fallbacks {lits : List PFact} {cap : Cap} {s : Seed} :
    s ∈ fallbacks lits cap ↔
      ∃ j d, lits[j]? = some d ∧ hasCap cap j = false ∧ s = (j, d, Excl.empty) := by
  unfold fallbacks
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨d, j⟩, hm, hf⟩
    rw [List.mem_zipIdx_iff_getElem?] at hm
    cases hc : hasCap cap j with
    | true => rw [hc] at hf; cases hf
    | false =>
      rw [hc] at hf
      cases hf
      exact ⟨j, d, hm, hc, rfl⟩
  · rintro ⟨j, d, hd, hc, rfl⟩
    refine ⟨(d, j), List.mem_zipIdx_iff_getElem?.mpr hd, ?_⟩
    simp only [hc]
    rfl

theorem mem_meets {lits : List PFact} {cap : Cap} {s : Seed} :
    s ∈ meets lits cap ↔
      ∃ j a aex d p pex, (j, a, aex) ∈ cap ∧ lits[j]? = some d ∧
        meetLit d a aex = some (p, pex) ∧ s = (j, p, pex) := by
  unfold meets
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨j, a, aex⟩, hm, hf⟩
    dsimp only at hf
    cases hd : lits[j]? with
    | none => rw [hd] at hf; cases hf
    | some d =>
      rw [hd] at hf
      dsimp only at hf
      cases he : meetLit d a aex with
      | none => rw [he] at hf; cases hf
      | some q =>
        rw [he] at hf
        obtain ⟨p, pex⟩ := q
        cases hf
        exact ⟨j, a, aex, d, p, pex, hm, hd, he, rfl⟩
  · rintro ⟨j, a, aex, d, p, pex, hm, hd, he, rfl⟩
    refine ⟨(j, a, aex), hm, ?_⟩
    dsimp only
    rw [hd]
    dsimp only
    rw [he]
    rfl

/-- THE MEMBERS OF `refine`: a fallback of a literal with no captured input, or a meet of a
    literal with one of its captured inputs. -/
theorem mem_refine {lits : List PFact} {cap : Cap} {s : Seed} :
    s ∈ refine lits cap ↔
      (∃ j d, lits[j]? = some d ∧ hasCap cap j = false ∧ s = (j, d, Excl.empty)) ∨
      (∃ j a aex d p pex, (j, a, aex) ∈ cap ∧ lits[j]? = some d ∧
        meetLit d a aex = some (p, pex) ∧ s = (j, p, pex)) := by
  unfold refine
  rw [List.mem_append, mem_fallbacks, mem_meets]

#print axioms mem_refine

/-- The members of `refine`, read on a seed `(j, p, pex)`. -/
theorem mem_refine3 {lits : List PFact} {cap : Cap} {j : Nat} {p : PFact} {pex : Excl} :
    (j, p, pex) ∈ refine lits cap ↔
      (lits[j]? = some p ∧ hasCap cap j = false ∧ pex = Excl.empty) ∨
      (∃ a aex d, (j, a, aex) ∈ cap ∧ lits[j]? = some d ∧ meetLit d a aex = some (p, pex)) := by
  rw [mem_refine]
  constructor
  · rintro (⟨j', d, hd, hc, he⟩ | ⟨j', a, aex, d, p', pex', hm, hd, hme, he⟩)
    · cases he
      exact Or.inl ⟨hd, hc, rfl⟩
    · cases he
      exact Or.inr ⟨a, aex, d, hm, hd, hme⟩
  · rintro (⟨hd, hc, hpex⟩ | ⟨a, aex, d, hm, hd, hme⟩)
    · exact Or.inl ⟨j, p, hd, hc, by rw [hpex]⟩
    · exact Or.inr ⟨j, a, aex, d, p, pex, hm, hd, hme, rfl⟩

#print axioms mem_refine3

/-- The two rows of `emitX` that give a result: above the pattern chain (the chain, no exclusion,
    if the exclusion admits the step down), or not above (the exclusion in normal form). -/
theorem emitX_split {d a p : PFact} {aex pex : Excl} (h : emitX d a aex = some (p, pex)) :
    emitM d a = some p ∧
    ((∃ r, relate d.path a.path = .above r ∧ aex.admits r = true ∧ pex = Excl.empty) ∨
     ((∀ r, relate d.path a.path ≠ .above r) ∧ pex = normJ p aex)) := by
  have hM := HandoffX.emitX_emitM h
  refine ⟨hM, ?_⟩
  unfold emitX at h
  rw [hM] at h
  dsimp only at h
  cases hr : relate d.path a.path with
  | above r =>
    rw [hr] at h
    dsimp only at h
    cases ha : aex.admits r with
    | false => rw [ha] at h; cases h
    | true =>
      rw [ha] at h
      cases h
      exact Or.inl ⟨r, rfl, ha, rfl⟩
  | below r =>
    rw [hr] at h
    cases h
    exact Or.inr ⟨(fun r' h' => by cases h'), rfl⟩
  | apart =>
    rw [hr] at h
    cases h
    exact Or.inr ⟨(fun r' h' => by cases h'), rfl⟩

#print axioms emitX_split

/-- A pattern mark that matches a concrete mark `t` admits it. -/
theorem markMatch_admits {dm : MarkA} {t m : Mark} (h : markMatchB dm (.conc t) = true)
    (hm : m = t) : dm.admits m := by
  subst hm
  cases dm with
  | star => trivial
  | conc T =>
    have h' : Nat.beq T m = true := h
    show m = T
    exact (Nat.eq_of_beq_eq_true h').symm
  | starEx x =>
    have h' : (!(memB m x)) = true := h
    show memB m x = false
    cases hx : memB m x with
    | false => rfl
    | true => rw [hx] at h'; cases h'

/-- The base form of the meet (`emitM`) with a concrete input: a location of the result is a
    location of the literal `d` (with its mark) and of the input `a`. -/
theorem emitM_inside_conc {d a p : PFact} {t : Mark} (hM : emitM d a = some p)
    (ha : a.mark = .conc t) {l : Loc} (hp : p.covers l) : d.covers l ∧ a.covers l := by
  obtain ⟨hac, hdl⟩ := (RCore.emitM_inter hM l).mp hp
  obtain ⟨_, hmm, _⟩ := RCore.emitM_cases hM
  have hlt : l.mark = t := by
    have h' := hac.2.2
    rw [ha] at h'
    exact h'
  rw [ha] at hmm
  exact ⟨⟨hdl.1, hdl.2, markMatch_admits hmm hlt⟩, hac⟩

/-- The path of a meet: the path of the input (not above the pattern chain), or the pattern chain
    below the input (above). -/
theorem emitM_path_split {d a p : PFact} (hM : emitM d a = some p) :
    ((∀ r, relate d.path a.path ≠ .above r) → p.path = a.path) ∧
    (∀ r, relate d.path a.path = .above r → p.path = d.path) := by
  obtain ⟨_, _, hc⟩ := RCore.emitM_cases hM
  constructor
  · intro hnr
    rcases hc with ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨r, hr, _, _, _, _⟩
    · rw [h1]
    · rw [h2]
    · exact absurd hr (hnr r)
  · intro r hr
    rcases hc with ⟨hq, _⟩ | ⟨x, r', hq, _, _⟩ | ⟨_, _, _, _, _, h3⟩
    · rw [hq, RCore.relate_self] at hr
      cases hr
    · rw [hq, CoreAux.relate_below (CoreAux.dropPrefix_some.mpr rfl)] at hr
      cases hr
    · rw [h3]

/-- THE MEET IS THE LOCATION INTERSECTION. For a concrete captured input `(a, aex)`, a location is
    covered by the meet (with its exclusion) iff the literal `d` covers it and `(a, aex)` covers it
    (exclusions and marks included). `→` from `RCore.emitM_inter` and the two rows of `emitX`; `←`
    from the emission contract `AnyTaintExCov.emitX_contract`. -/
theorem meetLit_inter {d a p : PFact} {aex pex : Excl} {t : Mark} (ha : a.mark = .conc t)
    (h : meetLit d a aex = some (p, pex)) (l : Loc) :
    coversX p pex l ↔ d.covers l ∧ coversX a aex l := by
  constructor
  · intro hp
    obtain ⟨hM, hsplit⟩ := emitX_split h
    obtain ⟨hd, hac⟩ := emitM_inside_conc hM ha (coversX_covers hp)
    obtain ⟨hpaths1, hpaths2⟩ := emitM_path_split hM
    refine ⟨hd, hac.1, ?_, hac.2.2⟩
    obtain ⟨σa, hpa, hta⟩ := hac.2.1
    obtain ⟨_, ⟨σ, hpp, htp, hep⟩, _⟩ := hp
    refine ⟨σa, hpa, hta, ?_⟩
    rcases hsplit with ⟨r, hr, har, _⟩ | ⟨hnr, hpex⟩
    · -- above the pattern chain: `p.path = d.path = a.path ++ r`, `r ≠ []`
      have hdp : d.path = a.path ++ r := RCore.relate_above_path hr
      have hpd : p.path = d.path := hpaths2 r hr
      have hσ : σa = r ++ σ := by
        have e1 : a.path ++ σa = a.path ++ (r ++ σ) := by
          rw [← hpa, hpp, hpd, hdp, List.append_assoc]
        exact List.append_cancel_left e1
      rw [hσ]
      cases r with
      | nil => exact absurd rfl (RCore.relate_above_ne hr)
      | cons x r' => rw [admits_cons_append]; exact har
    · -- at or below the pattern chain: `p.path = a.path`, the exclusion in normal form
      have hpa' : p.path = a.path := hpaths1 hnr
      have hσ : σa = σ := by
        have e1 : a.path ++ σa = a.path ++ σ := by rw [← hpa, hpp, hpa']
        exact List.append_cancel_left e1
      rw [hσ]
      rw [hpex] at hep
      unfold normJ at hep
      cases hk : p.kind with
      | exact =>
        rw [hk] at htp
        have h0 : σ = [] := htp
        rw [h0]
        exact CoreAux.admits_nil aex
      | any => rw [hk] at hep; exact hep
      | star e => rw [hk] at hep; exact hep
  · intro ⟨hd, hc⟩
    obtain ⟨j, jex, he, hcov, _⟩ := AnyTaintExCov.emitX_contract d a aex l t ha hd hc
    have e1 : some (j, jex) = some (p, pex) := he.symm.trans h
    cases e1
    exact hcov

#print axioms meetLit_inter

/-- The meet with its exclusion FORGOTTEN (the backward form of the seed: a backward `[any]` has no
    exclusion, I14) still lies inside the literal. -/
theorem meetLit_forget_inside {d a p : PFact} {aex pex : Excl} {t : Mark} (ha : a.mark = .conc t)
    (h : meetLit d a aex = some (p, pex)) {l : Loc} (hp : p.covers l) : d.covers l :=
  (emitM_inside_conc (HandoffX.emitX_emitM h) ha hp).1

#print axioms meetLit_forget_inside

/-! ## 3. Theorems 1 and 2: cover and fallback -/

/-- THEOREM 1. A location of the literal `lits[j]` covered by a concrete captured input of `j` is
    covered by a refined seed of `j`. -/
theorem refine_cover {lits : List PFact} {cap : Cap} {j : Nat} {d a : PFact} {aex : Excl}
    {t : Mark} {l : Loc} (hd : lits[j]? = some d) (hm : (j, a, aex) ∈ cap)
    (ha : a.mark = .conc t) (hdl : d.covers l) (hal : coversX a aex l) :
    ∃ p pex, (j, p, pex) ∈ refine lits cap ∧ coversX p pex l := by
  obtain ⟨p, pex, he, hcov, _⟩ := AnyTaintExCov.emitX_contract d a aex l t ha hdl hal
  exact ⟨p, pex, mem_refine.mpr (Or.inr ⟨j, a, aex, d, p, pex, hm, hd, he, rfl⟩), hcov⟩

#print axioms refine_cover

/-- THEOREM 2. A literal with no captured input keeps today's seed: `(j, lits[j], Excl.empty)` is
    a refined seed, it is the only refined seed of `j`, and it covers every location of
    `lits[j]`. -/
theorem refine_fallback {lits : List PFact} {cap : Cap} {j : Nat} {d : PFact}
    (hd : lits[j]? = some d) (hc : hasCap cap j = false) :
    (j, d, Excl.empty) ∈ refine lits cap ∧
    (∀ p pex, (j, p, pex) ∈ refine lits cap → p = d ∧ pex = Excl.empty) ∧
    (∀ l, d.covers l → coversX d Excl.empty l) := by
  refine ⟨mem_refine.mpr (Or.inl ⟨j, d, hd, hc, rfl⟩), ?_, fun _ h => covers_coversX h⟩
  intro p pex hm
  rcases mem_refine3.mp hm with ⟨hd', _, hpex⟩ | ⟨a, aex, _, hma, _, _⟩
  · rw [hd] at hd'
    exact ⟨(Option.some.inj hd').symm, hpex⟩
  · exact absurd hma (not_mem_of_hasCap hc a aex)

#print axioms refine_fallback

/-! ## 4. Theorem 3: inside -/

/-- THEOREM 3. Every refined seed of `j` lies inside the literal `lits[j]` (never wider than
    today's seed), and a seed that is not a fallback is the meet of `lits[j]` with a captured input
    of `j` and lies inside that input. -/
theorem refine_inside {lits : List PFact} {cap : Cap} (hcc : CapConc cap) {j : Nat} {p : PFact}
    {pex : Excl} (hm : (j, p, pex) ∈ refine lits cap) :
    ∃ d, lits[j]? = some d ∧ (∀ l, coversX p pex l → d.covers l) ∧
      ((hasCap cap j = false ∧ p = d ∧ pex = Excl.empty) ∨
       (∃ a aex, (j, a, aex) ∈ cap ∧ meetLit d a aex = some (p, pex) ∧
          ∀ l, coversX p pex l → coversX a aex l)) := by
  rcases mem_refine3.mp hm with ⟨hd, hc, hpex⟩ | ⟨a, aex, d, hma, hd, hme⟩
  · exact ⟨p, hd, fun l h => coversX_covers h, Or.inl ⟨hc, rfl, hpex⟩⟩
  · obtain ⟨t, ht⟩ := hcc _ hma
    refine ⟨d, hd, fun l h => ((meetLit_inter ht hme l).mp h).1, Or.inr ⟨a, aex, hma, hme, ?_⟩⟩
    exact fun l h => ((meetLit_inter ht hme l).mp h).2

#print axioms refine_inside

/-- THEOREM 3, the backward form: every refined seed of `j` with its exclusion FORGOTTEN lies
    inside `lits[j]`. -/
theorem refine_forget_inside {lits : List PFact} {cap : Cap} (hcc : CapConc cap) {j : Nat}
    {p : PFact} {pex : Excl} (hm : (j, p, pex) ∈ refine lits cap) :
    ∃ d, lits[j]? = some d ∧ ∀ l, p.covers l → d.covers l := by
  rcases mem_refine3.mp hm with ⟨hd, _, _⟩ | ⟨a, aex, d, hma, hd, hme⟩
  · exact ⟨p, hd, fun _ h => h⟩
  · obtain ⟨t, ht⟩ := hcc _ hma
    exact ⟨d, hd, fun _ h => meetLit_forget_inside ht hme h⟩

#print axioms refine_forget_inside

/-! ## 4b. Theorem 3b: progress (the seed follows the forward facts) -/

/-- The meet path extends the path of the captured input and the path of the literal: it is the
    longer of the two. -/
theorem meet_deepens {d a p : PFact} {aex pex : Excl} (h : meetLit d a aex = some (p, pex)) :
    a.path <+: p.path ∧ d.path <+: p.path := by
  obtain ⟨_, _, ⟨hq, h1⟩ | ⟨x, r, hq, _, h2⟩ | ⟨r, _, hq, _, _, h3⟩⟩ :=
    RCore.emitM_cases (HandoffX.emitX_emitM h)
  · rw [h1]; exact ⟨List.prefix_refl _, by rw [hq]; exact List.prefix_refl _⟩
  · rw [h2]; exact ⟨List.prefix_refl _, ⟨x :: r, hq.symm⟩⟩
  · rw [h3]; exact ⟨⟨r, hq.symm⟩, List.prefix_refl _⟩

#print axioms meet_deepens

/-- THEOREM 3b, PROGRESS. A refined seed that is not a fallback comes from a captured input `a`
    of its literal `d`. It lies inside `a` and inside `d`, also with the exclusions forgotten (the
    backward `[any]` has none), and its path extends the paths of both. So the seed is never
    shallower than the forward fact that the run before captured: a field that the forward run
    added below the demand stays in the next demand. A fallback seed is the literal. -/
theorem refine_deepens {lits : List PFact} {cap : Cap} (hcc : CapConc cap) {j : Nat} {p : PFact}
    {pex : Excl} (hm : (j, p, pex) ∈ refine lits cap) :
    ∃ d, lits[j]? = some d ∧
      ((hasCap cap j = false ∧ p = d) ∨
       (∃ a aex, (j, a, aex) ∈ cap ∧ a.path <+: p.path ∧ d.path <+: p.path ∧
          ∀ l, p.covers l → a.covers l ∧ d.covers l)) := by
  rcases mem_refine3.mp hm with ⟨hd, hc, _⟩ | ⟨a, aex, d, hma, hd, hme⟩
  · exact ⟨p, hd, Or.inl ⟨hc, rfl⟩⟩
  · obtain ⟨t, ht⟩ := hcc _ hma
    obtain ⟨h1, h2⟩ := meet_deepens hme
    refine ⟨d, hd, Or.inr ⟨a, aex, hma, h1, h2, fun l hl => ?_⟩⟩
    obtain ⟨hdl, hal⟩ := emitM_inside_conc (HandoffX.emitX_emitM hme) ht hl
    exact ⟨hal, hdl⟩

#print axioms refine_deepens

/-- The depth form of THEOREM 3b: a seed from a captured input is at least as deep as that input
    and as its literal. -/
theorem refine_depth {lits : List PFact} {cap : Cap} (hcc : CapConc cap) {j : Nat} {p : PFact}
    {pex : Excl} (hm : (j, p, pex) ∈ refine lits cap) (hc : hasCap cap j = true) :
    ∃ d a aex, lits[j]? = some d ∧ (j, a, aex) ∈ cap ∧
      a.path.length ≤ p.path.length ∧ d.path.length ≤ p.path.length := by
  obtain ⟨d, hd, ⟨hc', _⟩ | ⟨a, aex, hma, h1, h2, _⟩⟩ := refine_deepens hcc hm
  · rw [hc] at hc'; cases hc'
  · exact ⟨d, a, aex, hd, hma, h1.length_le, h2.length_le⟩

#print axioms refine_depth

/-! ## 4c. The capture tree

Three rules of the forward capture (spec §I.3). MEET FIRST: the forward run stores
`meet(input, literal)`, not the input. LEAVES ONLY: no `$` or `[any-taint]` fact is stored; a meet
is a LEAF with its exclusion dropped: a `$` meet is a `$` leaf, a field meet an `[any]` leaf. ONE
TREE: the leaves of a literal are merged; an `[any]` leaf subsumes each leaf at or below its path.
The next backward run seeds the merged tree of each literal (the literal itself if it has no
leaf). -/

/-- A leaf of a capture tree: the literal index and the meet pattern (no exclusion). -/
abbrev Leaf := Nat × PFact

/-- MEET FIRST, LEAVES ONLY: the leaves that the forward run stores. -/
def capMeets (lits : List PFact) (cap : Cap) : List Leaf :=
  (meets lits cap).map (fun s => (s.1, s.2.1))

def isAnyB : Kind → Bool
  | .any => true
  | _    => false

/-- `s` subsumes `t`: the same leaf, or an `[any]` leaf of the same literal, base and mark at a
    prefix of the path of `t`. -/
def subsumesB (s t : Leaf) : Bool :=
  decide (s = t) ||
    (decide (s.1 = t.1) && decide (s.2.base = t.2.base) && decide (s.2.mark = t.2.mark) &&
      isAnyB s.2.kind && (dropPrefix s.2.path t.2.path).isSome)

/-- Insert a leaf into a merged tree. -/
def insertLeaf (t : Leaf) (L : List Leaf) : List Leaf :=
  if L.any (fun s => subsumesB s t) then L else t :: L.filter (fun s => !subsumesB t s)

/-- ONE TREE: the merged leaves. -/
def mergeLeaves (ts : List Leaf) : List Leaf := ts.foldr insertLeaf []

def hasLeaf (ts : List Leaf) (j : Nat) : Bool := ts.any (fun t => t.1 == j)

/-- The seeds of the next backward run: the merged tree of each literal; a literal with no leaf
    keeps today's seed. -/
def treeSeeds (lits : List PFact) (ts : List Leaf) : List Leaf :=
  lits.zipIdx.filterMap (fun x => if hasLeaf ts x.2 then none else some (x.2, x.1)) ++
    mergeLeaves ts

/-- The leaf `t` serves the location `l` of literal `j`. -/
def LeafCov (j : Nat) (l : Loc) (t : Leaf) : Prop := t.1 = j ∧ t.2.covers l

theorem isAnyB_iff {k : Kind} : isAnyB k = true ↔ k = .any := by
  cases k <;> simp [isAnyB]

/-- A subsuming leaf serves every location that the subsumed leaf serves. -/
theorem subsumes_cov {s t : Leaf} {j : Nat} {l : Loc} (h : subsumesB s t = true)
    (ht : LeafCov j l t) : LeafCov j l s := by
  simp only [subsumesB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h1 | ⟨⟨⟨⟨hj, hb⟩, hm⟩, hk⟩, hp⟩
  · subst h1; exact ht
  · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hp
    have hpath := CoreAux.dropPrefix_some.mp hr
    obtain ⟨htj, hlb, ⟨σ, hσ, _⟩, hlm⟩ := ht
    refine ⟨hj.trans htj, hlb.trans hb.symm, ⟨r ++ σ, ?_, ?_⟩, ?_⟩
    · rw [hσ, hpath, List.append_assoc]
    · rw [isAnyB_iff.mp hk]; exact trivial
    · rw [hm]; exact hlm

#print axioms subsumes_cov

/-- Insertion keeps the served locations exactly: the old ones and those of the new leaf. -/
theorem insertLeaf_cov {t : Leaf} {L : List Leaf} {j : Nat} {l : Loc} :
    (∃ s ∈ insertLeaf t L, LeafCov j l s) ↔ LeafCov j l t ∨ ∃ s ∈ L, LeafCov j l s := by
  unfold insertLeaf
  split
  · rename_i h
    obtain ⟨s0, hs0, hsub⟩ := List.any_eq_true.mp h
    constructor
    · exact fun hx => Or.inr hx
    · rintro (ht | hx)
      · exact ⟨s0, hs0, subsumes_cov hsub ht⟩
      · exact hx
  · constructor
    · rintro ⟨s, hs, hc⟩
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact Or.inl hc
      · exact Or.inr ⟨s, (List.mem_filter.mp hs').1, hc⟩
    · rintro (ht | ⟨s, hs, hc⟩)
      · exact ⟨t, List.mem_cons.mpr (Or.inl rfl), ht⟩
      · cases hts : subsumesB t s with
        | true => exact ⟨t, List.mem_cons.mpr (Or.inl rfl), subsumes_cov hts hc⟩
        | false =>
          refine ⟨s, List.mem_cons.mpr (Or.inr (List.mem_filter.mpr ⟨hs, ?_⟩)), hc⟩
          simp [hts]

#print axioms insertLeaf_cov

/-- THEOREM 3c, ONE TREE IS EXACT. The merged tree serves exactly the locations that the leaves
    serve: merging loses nothing and adds nothing. -/
theorem mergeLeaves_cov {ts : List Leaf} {j : Nat} {l : Loc} :
    (∃ s ∈ mergeLeaves ts, LeafCov j l s) ↔ ∃ s ∈ ts, LeafCov j l s := by
  induction ts with
  | nil => exact Iff.rfl
  | cons t ts ih =>
    show (∃ s ∈ insertLeaf t (mergeLeaves ts), LeafCov j l s) ↔ _
    rw [insertLeaf_cov, ih]
    constructor
    · rintro (h | ⟨s, hs, hc⟩)
      · exact ⟨t, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact ⟨s, List.mem_cons.mpr (Or.inr hs), hc⟩
    · rintro ⟨s, hs, hc⟩
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact Or.inl hc
      · exact Or.inr ⟨s, hs', hc⟩

#print axioms mergeLeaves_cov

theorem insertLeaf_sub {t s : Leaf} {L : List Leaf} (h : s ∈ insertLeaf t L) : s ∈ t :: L := by
  unfold insertLeaf at h
  split at h
  · exact List.mem_cons.mpr (Or.inr h)
  · rcases List.mem_cons.mp h with rfl | h'
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (List.mem_filter.mp h').1)

/-- Each leaf of the merged tree is a stored leaf. -/
theorem mergeLeaves_sub {ts : List Leaf} {s : Leaf} (h : s ∈ mergeLeaves ts) : s ∈ ts := by
  induction ts with
  | nil => exact h
  | cons t ts ih =>
    have h' : s ∈ insertLeaf t (mergeLeaves ts) := h
    rcases List.mem_cons.mp (insertLeaf_sub h') with rfl | h''
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (ih h''))

#print axioms mergeLeaves_sub

theorem insertLeaf_length (t : Leaf) (L : List Leaf) : (insertLeaf t L).length ≤ L.length + 1 := by
  unfold insertLeaf
  split
  · exact Nat.le_succ _
  · exact Nat.succ_le_succ (List.length_filter_le _ _)

/-- The merged tree has at most as many leaves as were stored. -/
theorem mergeLeaves_length (ts : List Leaf) : (mergeLeaves ts).length ≤ ts.length := by
  induction ts with
  | nil => exact Nat.le_refl _
  | cons t ts ih => exact Nat.le_trans (insertLeaf_length t (mergeLeaves ts)) (Nat.succ_le_succ ih)

#print axioms mergeLeaves_length

/-- THEOREM 4c, SOUNDNESS OF THE TREE. Every real location of literal `j` (covered by the literal
    and by a captured input) is served by a leaf of the merged tree of `j`. -/
theorem tree_sound {lits : List PFact} {cap : Cap} {Real : Nat → Loc → Prop}
    (hcc : CapConc cap) (hfc : ForwardCaptured lits cap Real) {j : Nat} {l : Loc}
    (hr : Real j l) : ∃ s ∈ mergeLeaves (capMeets lits cap), LeafCov j l s := by
  obtain ⟨d, hd, hdl, a, aex, hm, hal⟩ := hfc j l hr
  obtain ⟨t, ht⟩ := hcc _ hm
  obtain ⟨p, pex, he, hcov, _⟩ := AnyTaintExCov.emitX_contract d a aex l t ht hdl hal
  refine mergeLeaves_cov.mpr ⟨(j, p), List.mem_map.mpr ⟨(j, p, pex),
    mem_meets.mpr ⟨j, a, aex, d, p, pex, hm, hd, he, rfl⟩, rfl⟩, rfl, coversX_covers hcov⟩

#print axioms tree_sound

/-- THEOREM 3d, PROGRESS OF THE TREE. Each leaf of the merged tree of `j` is the meet of the
    literal `lits[j]` with a captured input of `j`: it lies inside both (exclusions forgotten) and
    its path extends both paths. -/
theorem tree_deepens {lits : List PFact} {cap : Cap} (hcc : CapConc cap) {j : Nat} {p : PFact}
    (hm : (j, p) ∈ mergeLeaves (capMeets lits cap)) :
    ∃ d a aex, lits[j]? = some d ∧ (j, a, aex) ∈ cap ∧ a.path <+: p.path ∧ d.path <+: p.path ∧
      ∀ l, p.covers l → a.covers l ∧ d.covers l := by
  obtain ⟨s, hs, hsp⟩ := List.mem_map.mp (mergeLeaves_sub hm)
  obtain ⟨j', a, aex, d, p', pex, hma, hd, he, rfl⟩ := mem_meets.mp hs
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsp
  obtain ⟨t, ht⟩ := hcc _ hma
  obtain ⟨h1, h2⟩ := meet_deepens he
  refine ⟨d, a, aex, hd, hma, h1, h2, fun l hl => ?_⟩
  obtain ⟨hdl, hal⟩ := emitM_inside_conc (HandoffX.emitX_emitM he) ht hl
  exact ⟨hal, hdl⟩

#print axioms tree_deepens

/-! ## 5. Theorem 4: soundness -/

theorem forwardCaptured_weak {lits : List PFact} {cap : Cap} {Real : Nat → Loc → Prop}
    (h : ForwardCaptured lits cap Real) : ForwardCapturedF lits cap Real := by
  intro j l hr
  obtain ⟨d, hd, hdl, a, aex, hm, hal⟩ := h j l hr
  exact ⟨d, hd, hdl, fun _ => ⟨a, aex, hm, hal⟩⟩

/-- THEOREM 4. THE REFINED SEEDING IS SOUND: if the forward run captured, for every literal with
    captured inputs, an input that covers each real location of the literal, then every real
    location of literal `j` is covered by a refined seed of `j`. Since every real location is a
    location of `lits[j]` (the full seed), the refined seeding keeps every real location that the
    full seeding has. -/
theorem refine_sound {lits : List PFact} {cap : Cap} {Real : Nat → Loc → Prop}
    (hcc : CapConc cap) (hfc : ForwardCapturedF lits cap Real) {j : Nat} {l : Loc}
    (hr : Real j l) : ∃ p pex, (j, p, pex) ∈ refine lits cap ∧ coversX p pex l := by
  obtain ⟨d, hd, hdl, hcap⟩ := hfc j l hr
  cases hc : hasCap cap j with
  | false =>
    exact ⟨d, Excl.empty, (refine_fallback hd hc).1, covers_coversX hdl⟩
  | true =>
    obtain ⟨a, aex, hm, hal⟩ := hcap hc
    obtain ⟨t, ht⟩ := hcc _ hm
    exact refine_cover hd hm ht hdl hal

#print axioms refine_sound

/-- THEOREM 4 with the task form `ForwardCaptured`. -/
theorem refine_sound_strict {lits : List PFact} {cap : Cap} {Real : Nat → Loc → Prop}
    (hcc : CapConc cap) (hfc : ForwardCaptured lits cap Real) {j : Nat} {l : Loc}
    (hr : Real j l) : ∃ p pex, (j, p, pex) ∈ refine lits cap ∧ coversX p pex l :=
  refine_sound hcc (forwardCaptured_weak hfc) hr

#print axioms refine_sound_strict

/-! ### Where `ForwardCaptured` comes from: every input of EVERY completed combination -/

/-- A completed combination of a witness: one captured input `(fact, exclusion)` per literal, in
    literal order. -/
abbrev Combo := List (PFact × Excl)

/-- The capture of a list of completed combinations: the input of literal `j` of every
    combination, with the index `j`. -/
def capOf (cs : List Combo) : Cap :=
  cs.flatMap (fun c => c.zipIdx.map (fun x => (x.2, x.1.1, x.1.2)))

/-- The real locations of the real vulnerabilities `vs` of a witness (one real location per
    literal): `l` is the location of literal `j` of some real vulnerability. -/
def RealOf (vs : List (List Loc)) (j : Nat) (l : Loc) : Prop := ∃ ls, ls ∈ vs ∧ ls[j]? = some l

/-- The forward coverage at the sink statement (ap.md §6.6) read on the combinations: the location
    of literal `j` of a real vulnerability is a location of `lits[j]`, and every real vulnerability
    has a COMPLETED combination whose input `j` covers its location `j`, for every literal `j` (each
    location is covered by an input fact, each such input satisfies its literal, so the tuple of
    these inputs is a completed combination; the capture must keep all of them). -/
def CombosCover (lits : List PFact) (vs : List (List Loc)) (cs : List Combo) : Prop :=
  ∀ ls, ls ∈ vs →
    (∀ (j : Nat) (l : Loc), ls[j]? = some l → ∃ d : PFact, lits[j]? = some d ∧ d.covers l) ∧
    ∃ c, c ∈ cs ∧ ∀ (j : Nat) (l : Loc), ls[j]? = some l →
      ∃ x : PFact × Excl, c[j]? = some x ∧ coversX x.1 x.2 l

theorem mem_capOf {cs : List Combo} {c : Combo} {j : Nat} {x : PFact × Excl} (hc : c ∈ cs)
    (hx : c[j]? = some x) : (j, x.1, x.2) ∈ capOf cs := by
  unfold capOf
  rw [List.mem_flatMap]
  refine ⟨c, hc, ?_⟩
  rw [List.mem_map]
  exact ⟨(x, j), List.mem_zipIdx_iff_getElem?.mpr hx, rfl⟩

/-- THE CAPTURE OF ALL COMPLETED COMBINATIONS GIVES `ForwardCaptured`. -/
theorem forwardCaptured_of_combos {lits : List PFact} {vs : List (List Loc)} {cs : List Combo}
    (h : CombosCover lits vs cs) : ForwardCaptured lits (capOf cs) (RealOf vs) := by
  intro j l hr
  obtain ⟨ls, hls, hl⟩ := hr
  obtain ⟨hlit, c, hc, hcov⟩ := h ls hls
  obtain ⟨d, hd, hdl⟩ := hlit j l hl
  obtain ⟨x, hx, hxl⟩ := hcov j l hl
  exact ⟨d, hd, hdl, x.1, x.2, mem_capOf hc hx, hxl⟩

#print axioms forwardCaptured_of_combos

/-! ## 6. Theorem 5: non-increasing over runs -/

/-- THEOREM 5. If every captured input of `cap'` lies inside a captured input of `cap` with the
    same index, and every literal with an input in `cap` has one in `cap'` (no new fallback; the
    task's "iff" implies it), then every refined seed of `cap'` lies inside the union of the refined
    seeds of `cap` with the same index. So over runs whose captured inputs shrink the refined
    seeds do not grow. -/
theorem refine_mono {lits : List PFact} {cap cap' : Cap} (hcc : CapConc cap) (hcc' : CapConc cap')
    (hin : ∀ j a' aex', (j, a', aex') ∈ cap' →
      ∃ a aex, (j, a, aex) ∈ cap ∧ ∀ l, coversX a' aex' l → coversX a aex l)
    (hfb : ∀ j, hasCap cap j = true → hasCap cap' j = true)
    {j : Nat} {p' : PFact} {pex' : Excl} (hm : (j, p', pex') ∈ refine lits cap') {l : Loc}
    (hl : coversX p' pex' l) : ∃ p pex, (j, p, pex) ∈ refine lits cap ∧ coversX p pex l := by
  obtain ⟨d, hd, hdl, hrow⟩ := refine_inside hcc' hm
  rcases hrow with ⟨hc', hpd, hpex⟩ | ⟨a', aex', hma', _, hal'⟩
  · -- a fallback of `cap'`: also a fallback of `cap`
    have hc : hasCap cap j = false := by
      cases h : hasCap cap j with
      | false => rfl
      | true => rw [hfb j h] at hc'; cases hc'
    refine ⟨p', pex', ?_, hl⟩
    rw [hpd, hpex]
    exact (refine_fallback hd hc).1
  · -- a meet of `cap'`: inside its input, inside an input of `cap`
    obtain ⟨a, aex, hma, hsub⟩ := hin j a' aex' hma'
    obtain ⟨t, ht⟩ := hcc _ hma
    exact refine_cover hd hma ht (hdl l hl) (hsub l (hal' l hl))

#print axioms refine_mono

/-- The non-increasing form for a whole sequence of runs: if the capture of each run satisfies the
    hypotheses of `refine_mono` against the previous one, every refined seed of run `k` lies inside
    the union of the refined seeds of run `0` with the same index. -/
theorem refine_mono_seq {lits : List PFact} {caps : Nat → Cap} (hcc : ∀ k, CapConc (caps k))
    (hin : ∀ k j a' aex', (j, a', aex') ∈ caps (k + 1) →
      ∃ a aex, (j, a, aex) ∈ caps k ∧ ∀ l, coversX a' aex' l → coversX a aex l)
    (hfb : ∀ k j, hasCap (caps k) j = true → hasCap (caps (k + 1)) j = true) :
    ∀ k j p pex, (j, p, pex) ∈ refine lits (caps k) → ∀ l, coversX p pex l →
      ∃ p0 pex0, (j, p0, pex0) ∈ refine lits (caps 0) ∧ coversX p0 pex0 l := by
  intro k
  induction k with
  | zero => exact fun j p pex hm l hl => ⟨p, pex, hm, hl⟩
  | succ k ih =>
    intro j p pex hm l hl
    obtain ⟨p1, pex1, hm1, hl1⟩ :=
      refine_mono (hcc k) (hcc (k + 1)) (hin k) (hfb k) hm hl
    exact ih j p1 pex1 hm1 l hl1

#print axioms refine_mono_seq

/-! ## 7. Theorem 6: determinism and shape -/

/-- THEOREM 6a. Equal inputs give equal seeds. -/
theorem refine_det {lits lits' : List PFact} {cap cap' : Cap} (hl : lits = lits')
    (hc : cap = cap') : refine lits cap = refine lits' cap' := by
  rw [hl, hc]

#print axioms refine_det

theorem hasCap_congr {cap cap' : Cap} (h : ∀ e, e ∈ cap ↔ e ∈ cap') (j : Nat) :
    hasCap cap j = hasCap cap' j := by
  cases h1 : hasCap cap j with
  | true =>
    obtain ⟨a, aex, hm⟩ := hasCap_iff.mp h1
    exact (hasCap_of_mem ((h _).mp hm)).symm
  | false =>
    cases h2 : hasCap cap' j with
    | false => rfl
    | true =>
      obtain ⟨a, aex, hm⟩ := hasCap_iff.mp h2
      rw [hasCap_of_mem ((h _).mpr hm)] at h1
      cases h1

/-- THEOREM 6b. The seeds depend only on the MEMBERS of the capture (a production capture is a
    set): captures with the same members give seeds with the same members. -/
theorem refine_det_set {lits : List PFact} {cap cap' : Cap} (h : ∀ e, e ∈ cap ↔ e ∈ cap')
    (s : Seed) : s ∈ refine lits cap ↔ s ∈ refine lits cap' := by
  rw [mem_refine, mem_refine]
  constructor
  · rintro (⟨j, d, hd, hc, rfl⟩ | ⟨j, a, aex, d, p, pex, hm, hd, he, rfl⟩)
    · exact Or.inl ⟨j, d, hd, by rw [← hasCap_congr h]; exact hc, rfl⟩
    · exact Or.inr ⟨j, a, aex, d, p, pex, (h _).mp hm, hd, he, rfl⟩
  · rintro (⟨j, d, hd, hc, rfl⟩ | ⟨j, a, aex, d, p, pex, hm, hd, he, rfl⟩)
    · exact Or.inl ⟨j, d, hd, by rw [hasCap_congr h]; exact hc, rfl⟩
    · exact Or.inr ⟨j, a, aex, d, p, pex, (h _).mpr hm, hd, he, rfl⟩

#print axioms refine_det_set

/-- THEOREM 6c. THE SHAPE OF A SEED: its path is the path of its literal or of a captured input of
    its literal, and its exclusion is empty or the exclusion of that captured input. So no seed is
    deeper than its literal and the captured inputs. -/
theorem refine_shape {lits : List PFact} {cap : Cap} {j : Nat} {p : PFact} {pex : Excl}
    (hm : (j, p, pex) ∈ refine lits cap) :
    ∃ d, lits[j]? = some d ∧
      ((p.path = d.path ∧ pex = Excl.empty) ∨
       (∃ a aex, (j, a, aex) ∈ cap ∧ (p.path = d.path ∨ p.path = a.path) ∧
          (pex = Excl.empty ∨ pex = aex))) := by
  rcases mem_refine3.mp hm with ⟨hd, _, hpex⟩ | ⟨a, aex, d, hma, hd, hme⟩
  · exact ⟨p, hd, Or.inl ⟨rfl, hpex⟩⟩
  · obtain ⟨hM, hsplit⟩ := emitX_split hme
    refine ⟨d, hd, Or.inr ⟨a, aex, hma, ?_, ?_⟩⟩
    · rcases RCore.emitM_shape hM with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rcases hsplit with ⟨_, _, _, h⟩ | ⟨_, h⟩
      · exact Or.inl h
      · rw [h]
        unfold normJ
        cases p.kind with
        | exact => exact Or.inl rfl
        | any => exact Or.inr rfl
        | star e => exact Or.inr rfl

#print axioms refine_shape

/-- THEOREM 6d. The number of seeds is at most the number of captured inputs plus the number of
    literals. -/
theorem refine_length (lits : List PFact) (cap : Cap) :
    (refine lits cap).length ≤ cap.length + lits.length := by
  unfold refine
  rw [List.length_append, Nat.add_comm cap.length]
  apply Nat.add_le_add
  · unfold fallbacks
    exact Nat.le_trans (List.length_filterMap_le _ _) (Nat.le_of_eq List.length_zipIdx)
  · exact List.length_filterMap_le _ _

#print axioms refine_length

/-- The meet of two tails `$`/`[any]` is `$` or `[any]`. -/
theorem meetK_ea {k1 k2 : Kind} (h1 : k1 = .exact ∨ k1 = .any) (h2 : k2 = .exact ∨ k2 = .any) :
    meetK k1 k2 = .exact ∨ meetK k1 k2 = .any := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- THEOREM 6e. A seed of a literal with the tail `$`/`[any]` and a concrete mark, from captured
    inputs with the tail `$`/`[any]` and concrete marks, has the tail `$`/`[any]` and a concrete
    mark: a legal seed of the backward run (`Backward.legal_seed`). -/
theorem refine_legal {lits : List PFact} {cap : Cap} (hwf : CapWF cap) {j : Nat} {d p : PFact}
    {pex : Excl} (hd : lits[j]? = some d) (hdk : d.kind = .exact ∨ d.kind = .any)
    (hdm : ∃ T, d.mark = .conc T) (hm : (j, p, pex) ∈ refine lits cap) :
    (p.kind = .exact ∨ p.kind = .any) ∧ ∃ T, p.mark = .conc T := by
  rcases mem_refine3.mp hm with ⟨hd', _, _⟩ | ⟨a, aex, d', hma, hd', hme⟩
  · rw [hd] at hd'
    cases hd'
    exact ⟨hdk, hdm⟩
  · rw [hd] at hd'
    cases hd'
    obtain ⟨⟨t, ht⟩, hak⟩ := hwf _ hma
    have hM := HandoffX.emitX_emitM hme
    refine ⟨?_, ⟨t, by rw [RCore.emitM_mark hM]; exact ht⟩⟩
    obtain ⟨_, _, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨_, _, _, _, _, h3⟩⟩ := RCore.emitM_cases hM
    · rw [h1]; exact meetK_ea hak hdk
    · rw [h2]; exact hak
    · rw [h3]; exact hdk

#print axioms refine_legal

/-! ## 8. Counterexamples and vectors -/

namespace Vec

/-- The literal `x.[any] (U)` (`x = 1`, `U = 7`). -/
def litX : PFact := ⟨1, [], .any, .conc 7⟩
/-- The input of route 1: `x.a $ (U)` (`a = 3`). -/
def inA : PFact := ⟨1, [3], .exact, .conc 7⟩
/-- The input of route 2: `x.b $ (U)` (`b = 4`). -/
def inB : PFact := ⟨1, [4], .exact, .conc 7⟩
/-- The real locations of the two routes. -/
def locA : Loc := ⟨1, [3], 7⟩
def locB : Loc := ⟨1, [4], 7⟩

/-- Two completed combinations (one literal each): route 1 and route 2. -/
def comboA : Combo := [(inA, Excl.empty)]
def comboB : Combo := [(inB, Excl.empty)]

/-- The two real vulnerabilities of the witness. -/
def vulns : List (List Loc) := [[locA], [locB]]

theorem refine_all : refine [litX] (capOf [comboA, comboB]) =
    [(0, inA, Excl.empty), (0, inB, Excl.empty)] := by decide

theorem refine_selected : refine [litX] (capOf [comboA]) = [(0, inA, Excl.empty)] := by decide

theorem litX_covers_locB : litX.covers locB := ⟨rfl, ⟨[4], rfl, trivial⟩, rfl⟩

theorem not_inA_locB : ¬ coversX inA Excl.empty locB := by
  rintro ⟨_, ⟨σ, hp, _⟩, _⟩
  simp [inA, locB] at hp

/-- The capture of BOTH completed combinations satisfies `CombosCover`, so `ForwardCaptured`. -/
theorem all_combos_cover : CombosCover [litX] vulns [comboA, comboB] := by
  unfold CombosCover
  intro ls hls
  simp only [vulns, List.mem_cons, List.not_mem_nil, or_false] at hls
  rcases hls with rfl | rfl
  · refine ⟨fun j l hl => ?_, comboA, by simp, fun j l hl => ?_⟩
    · cases j with
      | zero =>
        simp at hl
        subst hl
        exact ⟨litX, rfl, rfl, ⟨[3], rfl, trivial⟩, rfl⟩
      | succ k => simp at hl
    · cases j with
      | zero =>
        simp at hl
        subst hl
        exact ⟨(inA, Excl.empty), rfl, rfl, ⟨[], rfl, rfl, rfl⟩, rfl⟩
      | succ k => simp at hl
  · refine ⟨fun j l hl => ?_, comboB, by simp, fun j l hl => ?_⟩
    · cases j with
      | zero =>
        simp at hl
        subst hl
        exact ⟨litX, rfl, litX_covers_locB⟩
      | succ k => simp at hl
    · cases j with
      | zero =>
        simp at hl
        subst hl
        exact ⟨(inB, Excl.empty), rfl, rfl, ⟨[], rfl, rfl, rfl⟩, rfl⟩
      | succ k => simp at hl

/-- With both combinations captured, the real location `x.b` is covered by a refined seed. -/
theorem all_covers_locB :
    ∃ p pex, (0, p, pex) ∈ refine [litX] (capOf [comboA, comboB]) ∧ coversX p pex locB := by
  refine refine_sound_strict (j := 0) (l := locB) ?_ (forwardCaptured_of_combos all_combos_cover)
    ⟨[locB], by decide, rfl⟩
  intro e he
  rw [show capOf [comboA, comboB] = [(0, inA, Excl.empty), (0, inB, Excl.empty)] by decide] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact ⟨7, rfl⟩
  · exact ⟨7, rfl⟩

/-- THEOREM 7 (`cex_selected_only`). Two routes reach the ND sink: the completed combinations give
    the inputs `x.a $` and `x.b $` of the literal `x.[any]`. If only the SELECTED proof's input
    (route 1) is captured, the real location `x.b` of route 2 (a location of the literal, the
    location of a real vulnerability) is covered by NO refined seed. So `ForwardCaptured` needs the
    inputs of ALL completed combinations. -/
theorem cex_selected_only :
    RealOf vulns 0 locB ∧ litX.covers locB ∧
    (∀ s, s ∈ refine [litX] (capOf [comboA]) → ¬ coversX s.2.1 s.2.2 locB) ∧
    ¬ ForwardCaptured [litX] (capOf [comboA]) (RealOf vulns) ∧
    (∃ p pex, (0, p, pex) ∈ refine [litX] (capOf [comboA, comboB]) ∧ coversX p pex locB) := by
  have hno : ∀ s, s ∈ refine [litX] (capOf [comboA]) → ¬ coversX s.2.1 s.2.2 locB := by
    intro s hs
    rw [refine_selected] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    exact not_inA_locB
  refine ⟨⟨[locB], by decide, rfl⟩, litX_covers_locB, hno, ?_, all_covers_locB⟩
  intro hfc
  have hcc : CapConc (capOf [comboA]) := by
    intro e he
    rw [show capOf [comboA] = [(0, inA, Excl.empty)] by decide] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    subst he
    exact ⟨7, rfl⟩
  obtain ⟨p, pex, hm, hc⟩ := refine_sound_strict (j := 0) (l := locB) hcc hfc
    ⟨[locB], by decide, rfl⟩
  exact hno _ hm hc

#print axioms cex_selected_only

/-- An input with the mark `*`: `x.[any] (*)`. -/
def inStar : PFact := ⟨1, [], .any, .star⟩
def locX : Loc := ⟨1, [], 7⟩

/-- `cex_abstract_mark`. A captured input with the abstract mark `*` covers a location of the
    literal, but its meet is empty (`emitX` needs the concrete mark of the pattern), and the
    literal has an entry, so it gets NO seed at all (not even the fallback). The capture must store
    the concrete mark that the sink check matched (`CapConc`). -/
theorem cex_abstract_mark :
    litX.covers locX ∧ inStar.covers locX ∧ meetLit litX inStar Excl.empty = none ∧
    refine [litX] [(0, inStar, Excl.empty)] = [] :=
  ⟨⟨rfl, ⟨[], rfl, trivial⟩, rfl⟩, ⟨rfl, ⟨[], rfl, trivial⟩, trivial⟩, by decide, by decide⟩

#print axioms cex_abstract_mark

/-- An input with a `*/{a}` tail and a concrete mark. -/
def inStarTail : PFact := ⟨1, [], .star (.set [3]), .conc 7⟩

/-- `cex_star_capture`. A captured input with a `*/E` tail gives a seed with a `*` tail and a
    concrete mark: not a legal `DB` seed. The capture must store it as `[any]` with the exclusion
    `E` (the same location set as a premise): then the seed is `x.[any]/{a}` with a legal tail. -/
theorem cex_star_capture :
    refine [litX] [(0, inStarTail, Excl.empty)] = [(0, inStarTail, Excl.empty)] ∧
    refine [litX] [(0, ⟨1, [], .any, .conc 7⟩, .set [3])] = [(0, litX, .set [3])] := by
  constructor <;> decide

#print axioms cex_star_capture

/-- `cex_mono_fallback`. A literal that LOSES all its captured inputs (`cap' = []`; every input of
    `cap'` trivially lies inside one of `cap`) falls back to the full pattern: the location `x.b`
    is covered by a seed of `cap'` and by no seed of `cap`. So `refine_mono` needs "no new
    fallback". -/
theorem cex_mono_fallback :
    (∀ j a' aex', (j, a', aex') ∈ ([] : Cap) →
      ∃ a aex, (j, a, aex) ∈ capOf [comboA] ∧ ∀ l, coversX a' aex' l → coversX a aex l) ∧
    (0, litX, Excl.empty) ∈ refine [litX] [] ∧ coversX litX Excl.empty locB ∧
    (∀ s, s ∈ refine [litX] (capOf [comboA]) → ¬ coversX s.2.1 s.2.2 locB) := by
  refine ⟨fun _ _ _ h => absurd h List.not_mem_nil, by decide,
    covers_coversX litX_covers_locB, ?_⟩
  exact cex_selected_only.2.2.1

#print axioms cex_mono_fallback

/-- A vector of the meet rows: the literal `x.[any]` with `x.a $` (below: the input), with the
    `[any-taint]/{a}` input at `x` (at: the meet keeps the exclusion), the literal `x.a.[any]`
    with the input `x.[any-taint]/{b}` (above: the literal chain, no exclusion), and with the
    input `x.[any-taint]/{a}` (above, the step down excluded: empty). -/
theorem meet_rows :
    meetLit litX inA Excl.empty = some (inA, Excl.empty) ∧
    meetLit litX ⟨1, [], .any, .conc 7⟩ (.set [3]) = some (litX, .set [3]) ∧
    meetLit ⟨1, [3], .any, .conc 7⟩ ⟨1, [], .any, .conc 7⟩ (.set [4]) =
      some (⟨1, [3], .any, .conc 7⟩, Excl.empty) ∧
    meetLit ⟨1, [3], .any, .conc 7⟩ ⟨1, [], .any, .conc 7⟩ (.set [3]) = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

#print axioms meet_rows
#print axioms refine_all
#print axioms refine_selected
#print axioms all_combos_cover

end Vec

/-! ## 9. Stretch: the base backward contract with refined seeds

`Backward.B_general` (and `B_fragment_rep`) read the seeds only through `demanded_gen`
(`demanded_fragment`): for the witness location `l` of a reported sink they need ONE seed
`(M, n, s')` with a concrete mark, the tail `$`/`[any]` and `s'.covers l`. The sink pattern itself
is not needed. `SeedsCover` is this contract; the old hypothesis "every reported sink is seeded"
gives it (`seedsCover_full`), and so does the refined seeding (`seedsCover_refined`). -/

section Stretch
open ApSpec.Backward ApSpec.Reverse

/-- The seeding contract that `demanded_gen` / `demanded_fragment` read: every location `l` of a
    reported sink `s` with a witness `W M n l` is covered by a seed at `(M, n)` with a concrete
    mark and the tail `$` or `[any]`. -/
def SeedsCover (W : MethodId → Node → Loc → Prop) (Rk : Obj → Prop)
    (sinks seeds : List (MethodId × Node × PFact)) : Prop :=
  ∀ M n s T b l, Rk (.vuln M n s b) → (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l →
    W M n l →
    ∃ s', (M, n, s') ∈ seeds ∧ s'.covers l ∧ (∃ T', s'.mark = .conc T') ∧
      (s'.kind = .exact ∨ s'.kind = .any)

/-- The old seeding (every reported sink seeded with its pattern) satisfies `SeedsCover`. -/
theorem seedsCover_full {W : MethodId → Node → Loc → Prop} {Rk : Obj → Prop}
    {sinks seeds : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (hseeds : ∀ M n s b, Rk (.vuln M n s b) → (M, n, s) ∈ seeds) :
    SeedsCover W Rk sinks seeds :=
  fun M n s T b _ hv hs hT hsc _ => ⟨s, hseeds M n s b hv, hsc, ⟨T, hT⟩, hk M n s hs⟩

#print axioms seedsCover_full

/-- CONTRACT B IN THE GENERAL CASE WITH ANY COVERING SEEDING: `Backward.B_general` with
    `SeedsCover` in place of "every reported sink is seeded" (and no hypothesis on the tails of
    the sinks: the seeds carry it). -/
theorem B_general_cov {P : Program} (hW : P.WF) (hT : BindTargetsStar P) (hmr : StmtsMarkRev P)
    (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId} (hX : ExitReach P roots)
    {sinks : List (MethodId × Node × PFact)}
    {Rk : Obj → Prop} {seeds : List (MethodId × Node × PFact)}
    (hseeds : SeedsCover (ReachRD P Rk roots) Rk sinks seeds)
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)} :
    BackwardContractD P roots sinks Rk (demOf (Program.rev P)
      (DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB roots seeds true)) := by
  intro M n l s T hs hT' hsc hRR hv
  obtain ⟨b, hv⟩ := hv
  obtain ⟨s', hs', hc', ⟨T', hT''⟩, hk'⟩ := hseeds M n s T b l hv hs hT' hsc hRR
  exact demanded_gen hW hT hmr hNZB hZ hX rfl (fun _ h => h) hdemB hRR hs' hT'' hk' hc'

#print axioms B_general_cov

/-- THE FRAGMENT FORM: `Backward.B_fragment_rep` with `SeedsCover`. -/
theorem B_fragment_rep_cov {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hnb : NoBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    {Rk : Obj → Prop} {seeds : List (MethodId × Node × PFact)}
    (hseeds : SeedsCover (fun M n l => ReachR P (summaryDemand P Rk) roots M n l) Rk sinks seeds)
    {counted : Acc → Bool} {L : Nat} {demand : MethodId → DemandEdge → Prop}
    {emit : PFact → PFact → Option PFact} {sat : PFact → PFact → Bool}
    {restrict : PFact → AFact → DemandEdge → Option AFact}
    {recs : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)} :
    BackwardContractRep P roots sinks Rk (demOf (Program.rev P)
      (DB (Program.rev P) counted L demand emit sat restrict recs sinksB roots seeds true)) := by
  intro M n l s T hs hT' hsc hRR hv
  obtain ⟨b, hv⟩ := hv
  obtain ⟨s', hs', hc', ⟨T', hT''⟩, hk'⟩ := hseeds M n s T b l hv hs hT' hsc hRR
  exact demanded_fragment hW hT hmr hnb hZ hX rfl (fun _ h => h) (RCov.reachR_reach hRR) hs' hT''
    hk' hc'

#print axioms B_fragment_rep_cov

/-- The seeds of the refined seeding of one witness at `(M, n)` in the base backward run: the seed
    patterns with the exclusion FORGOTTEN (a `DB` seed has none; the backward run has no
    `[any-taint]`, I14). -/
def seedsAt (M : MethodId) (n : Node) (lits : List PFact) (cap : Cap) :
    List (MethodId × Node × PFact) :=
  (refine lits cap).map (fun s => (M, n, s.2.1))

/-- THE REFINED SEEDING: every reported sink pattern `s` at `(M, n)` is the literal `j` of a
    literal list `lits` whose capture `cap` is well formed and covers every witness location of
    that literal (`ForwardCapturedF` for `W`, read on the literal `j`), and the refined seeds of
    `(lits, cap)` are seeded. -/
def RefinedSeeding (W : MethodId → Node → Loc → Prop) (Rk : Obj → Prop)
    (sinks seeds : List (MethodId × Node × PFact)) : Prop :=
  ∀ M n s b, Rk (.vuln M n s b) → (M, n, s) ∈ sinks →
    ∃ (lits : List PFact) (cap : Cap) (j : Nat), lits[j]? = some s ∧ CapWF cap ∧
      ForwardCapturedF lits cap (fun j' l => j' = j ∧ s.covers l ∧ W M n l) ∧
      ∀ x, x ∈ seedsAt M n lits cap → x ∈ seeds

/-- THE REFINED SEEDING SATISFIES `SeedsCover` (for sinks with the tail `$`/`[any]`). -/
theorem seedsCover_refined {W : MethodId → Node → Loc → Prop} {Rk : Obj → Prop}
    {sinks seeds : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    (h : RefinedSeeding W Rk sinks seeds) : SeedsCover W Rk sinks seeds := by
  intro M n s T b l hv hs hT hsc hWl
  obtain ⟨lits, cap, j, hj, hwf, hfc, hsub⟩ := h M n s b hv hs
  obtain ⟨p, pex, hm, hcov⟩ := refine_sound (capWF_conc hwf) hfc ⟨rfl, hsc, hWl⟩
  have hin : (M, n, p) ∈ seedsAt M n lits cap := List.mem_map.mpr ⟨(j, p, pex), hm, rfl⟩
  obtain ⟨hpk, hpm⟩ := refine_legal hwf hj (hk M n s hs) ⟨T, hT⟩ hm
  exact ⟨p, hsub _ hin, coversX_covers hcov, hpm, hpk⟩

#print axioms seedsCover_refined

/-- CONTRACT B IN THE GENERAL CASE WITH THE REFINED SEEDS (rule B3). -/
theorem B_general_refined {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {Rk : Obj → Prop} {seeds : List (MethodId × Node × PFact)}
    (hseeds : RefinedSeeding (ReachRD P Rk roots) Rk sinks seeds)
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)} :
    BackwardContractD P roots sinks Rk (demOf (Program.rev P)
      (DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB roots seeds true)) :=
  B_general_cov hW hT hmr hNZB hZ hX (seedsCover_refined hk hseeds) hdemB

#print axioms B_general_refined

/-- THE GENERAL ITERATION THEOREM WITH THE REFINED SEEDS: `Backward.iteration_general` with the
    refined seeding of every forward run in place of "the seeds contain the reported sinks". -/
theorem iteration_general_refined {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    (hk : ∀ M n s, (M, n, s) ∈ sinks → s.kind = .exact ∨ s.kind = .any)
    {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, revSummaryDemand P
      (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k, RefinedSeeding
      (ReachRD P (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k) roots)
      (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k) sinks (seeds k))
    (hdem : ∀ k m d, demOf (Program.rev P) (DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k
      (.vuln M n s b) :=
  iteration_sound_M_D hW (fun k M' n' l' s' T' hs' hT'' hc' hr' hv' =>
    RCov.reachR_mono (hdem k)
      (B_general_refined hW hT hmr hNZB hZ hX hk (hseeds k) (hdemB k) M' n' l' s' T' hs' hT''
        hc' hr' hv'))
    hRe hs hT' hsc

#print axioms iteration_general_refined

end Stretch

end ApSpec.BackND
