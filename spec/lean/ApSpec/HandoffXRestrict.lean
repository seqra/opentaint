/-
  ApSpec.HandoffXRestrict — the restriction as an INTERSECTION (decision F70) on the spec closures
  with the `[any-taint]` tail and its exclusion (decision F69).

  `restrictX` (`AnyTaintExDefs.lean`) keeps the premise whole if it OVERLAPS `D-c`, and keeps the
  whole conclusion at the path of `D-p`. `restrictIX` is the intersection:
    * the premise `(j, jex)` must lie INSIDE `D-c` (`insideXB`: `insideLocXB` on the locations,
      the premise exclusion read, and the marks, F71; an emitted premise of a concrete added fact
      lies inside its entry pattern, `emitX_inside`, `emitX_insideXB`);
    * the conclusion mark must meet the mark of `D-p` (`concMarkB`, F71);
    * at the path of `D-p` the conclusion tail is met with the tail of `D-p` (`meetConcK` for the
      tail, `meetExX` for the exclusion):
        `[any]` (demand) ∩ `$` = `$`,           `[any-taint]/E` ∩ `$` = `$`,
        `[any-taint]/E` ∩ `*/E2` = `[any-taint]/(E ∪ E2)`,   `[any-taint]/E` ∩ `[any]` = `[any-taint]/E`,
        `[any]` ∩ `*/E2` = `[any]` (W2: a demand `[any]` has no exclusion; an exception),
        `$` stays, `*` stays (a restricted run has no `*` conclusion; no `*/Universe`, S8);
    * below `D-p`: the conclusion with its exclusion, if the tail of `D-p` admits the step
      (`restrictConcX`);
    * above `D-p` (`D-p.path = g.path ++ r`): the chain of `D-p` if the exclusion of `g` admits `r`
      (`restrictConcX`), with the tail `$` for a `$` exit pattern, else `.any`, and WITH THE
      EXCLUSION `E2` of a `*/E2` exit pattern on an `[any-taint]` conclusion (`chainExX`; CHANGED
      against the brief: `restrictConcX` gives `[any-taint]/{}` there, which is not the
      intersection; `[any-taint]/E2` is, and it is sound and in normal form).
  The layer stays.

  Results (constructive; see the `#print axioms` lines):
    X1 `restrictIX_ok`        `AnyTaintExExact.RestrictOKX restrictIX`: a conclusion in normal form
                              gives a conclusion in normal form, in the same layer, with fewer pairs.
                              `restrictIX_sub_base`: the base facts only lose pairs (no normal form
                              needed), the hypothesis `hpubSub` of the backward contract.
                              `restrictConcIX_fact`, `restrictIX_restrictI`: the fact part is the base
                              intersection `restrictConcI` / `restrictI` of `HandoffDefs.lean`.
    X2 `restrictIX_contract`  C5 for a premise inside `D-c`, with `denX`, for EVERY conclusion (also
                              `*`). `restrictIX_contract_base`: the same from `insideLocB`.
                              `restrictIX_not_RestrictContractX`: the overlap form of C5 is false.
    X3 `emitX_inside`         an emitted premise lies inside its entry pattern (`insideLocXB` and
                              `insideLocB`). `insideLocXB_sound`: the location form.
    X4 `restrictIX_inter`     every pair of a result has its entry in `D-c` and its exit in `D-p`,
                              except the cells of `RExcX`: a NON-CARRYING `.any` conclusion (a demand
                              `[any]`) at or above a `*/E2` exit pattern, and a `*` conclusion.
                              `restrictConcIX_inside`, `restrictIX_narrow`: the pattern form (the
                              result with its exclusion lies inside `D-p`, the premise with its
                              exclusion inside `D-c`). `pubRX`, `handF_narrowX`: the narrowing of
                              the forward hand-off read on the forgotten view.
    MARK-AWARE (F71, the user, 2026-10-10): `restrictIX` has the SAME mark tests as
    `Handoff.restrictI`: the premise inside `D-c` in its marks too (`insideXB` = `insideLocXB`
    and `markSubB`), the conclusion mark meets the mark of `D-p` (`concMarkB`). So
    `restrictIX_contract` takes `insideXB` and `p.covers l2` (the location form is false,
    `XVec.restrictIX_contract_loc_false`); `emitX_insideXB` (a concrete added fact);
    `restrictIX_interM`, `restrictIX_inter_conc`, `restrictIX_narrowM`, `handF_narrowXM`,
    `handF_narrowX_DRXM` (the marks narrow too); the location forms stay; vectors `XVec.vM_*`.
    X5 vectors (`decide`, namespace `XVec`): the §6.4 example in X form, the cell
                              `[any-taint]/E ∩ */E2`, the cell above a `*/E2` exit pattern (and the
                              old cell of `restrictConcX` there is not the intersection,
                              `v_old_above_not_inter`), a premise that only overlaps `D-c`, a premise
                              inside `D-c` only with its exclusion, each exception of `RExcX` (a real
                              pair outside `D-p`).
-/
import ApSpec.HandoffRestrict
import ApSpec.AnyTaintExCov
import ApSpec.AnyTaintExExact

namespace ApSpec.HandoffX
open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx ApSpec.Handoff

/-! ## 1. The definitions -/

/-- The premise `j` with its exclusion `jex` lies INSIDE the pattern `d` (locations, marks
    ignored). The form of `insideLocB` (`coversB` on the locations) with the premise exclusion read
    at the path of `d`: there `d` must exclude at most what `j` with `jex` excludes. Strictly below
    the path of `d` the step must pass the tail of `d` (the exclusion of `j` does not matter: the
    location at the path of `j` is in `j`). Above or apart: never (the location at the path of `j`
    is not in `d`). With `jex = {}` it accepts what `insideLocB` accepts (`insideLocXB_of_base`). -/
def insideLocXB (j : PFact) (jex : Excl) (d : PFact) : Bool :=
  Nat.beq d.base j.base &&
  match dropPrefix d.path j.path with
  | some []       => (tailExcl d.kind).subB ((tailExcl j.kind).union jex)
  | some (x :: r) => admitsTailB d.kind (x :: r)
  | none          => false

/-- The exclusion of the meet at the path of `D-p`: an `.any` conclusion against a `*/E2` exit
    pattern gets `E ∪ E2` (the normal form keeps it only on `[any-taint]`); every other cell keeps
    the exclusion of the conclusion. -/
def meetExX (k : Kind) (ex : Excl) (dk : Kind) : Excl :=
  match k, dk with
  | .any, .star e2 => ex.union e2
  | _,    _        => ex

/-- The exclusion of the chain of `D-p` (a conclusion above `D-p`): the exclusion `E2` of a
    `*/E2` exit pattern, else none. -/
def chainExX : Kind → Excl
  | .star e2 => e2
  | _        => Excl.empty

/-- THE RESTRICTED CONCLUSION AS AN INTERSECTION, WITH THE EXCLUSION. The fact is
    `restrictConcI` (`HandoffDefs.lean`); the exclusion: at `D-p` the meet `meetExX`; below `D-p`
    the exclusion of the conclusion; above `D-p` (`D-p.path = g.path ++ r`) the result exists only
    if the exclusion of the conclusion admits `r`, and it gets `chainExX`. Then the normal form
    `normX`. -/
def restrictConcIX (sc : XFact) (dout : PFact) : Option XFact :=
  match restrictConcI sc.af dout with
  | none    => none
  | some g' =>
    match relate dout.path sc.af.fact.path with
    | .below []       => some (normX ⟨g', meetExX sc.af.fact.kind sc.ex dout.kind⟩)
    | .below (_ :: _) => some (normX ⟨g', sc.ex⟩)
    | .above r        => if sc.ex.admits r then some (normX ⟨g', chainExX dout.kind⟩) else none
    | .apart          => none

/-- The premise `(j, jex)` lies INSIDE the pattern `d` in its locations (with its exclusion,
    `insideLocXB`) AND in its marks (`markSubB d.mark j.mark`): the X form of
    `Handoff.insideB` (decision F71, the mark-aware restriction). -/
def insideXB (j : PFact) (jex : Excl) (d : PFact) : Bool :=
  insideLocXB j jex d && markSubB d.mark j.mark

/-- THE RESTRICTION OF `ap.md` §6.4 AS AN INTERSECTION, WITH THE EXCLUSION, MARK-AWARE (F71). No
    `D-p`: no result. The premise `(sp, spex)` must lie INSIDE `D-c` in its locations and marks
    (`insideXB`), and the conclusion mark must meet the mark of `D-p` (`concMarkB`): the SAME mark
    tests as `Handoff.restrictI`. The conclusion is `restrictConcIX`. The layer stays. -/
def restrictIX (sp : PFact) (spex : Excl) (sc : XFact) (d : DemandEdge) : Option XFact :=
  match d.dout with
  | none   => none
  | some p =>
    if insideXB sp spex d.din && concMarkB p.mark sc.af.fact.mark then restrictConcIX sc p
    else none

/-! ## 2. Small lemmas -/

namespace XAux

theorem empty_subB (e : Excl) : Excl.empty.subB e = true := by
  cases e <;> rfl

/-- A union on the right keeps a sub-exclusion. -/
theorem subB_union_right {e1 e2 : Excl} (h : e1.subB e2 = true) (e3 : Excl) :
    e1.subB (e2.union e3) = true := by
  cases e2 with
  | univ => exact Invariant.subB_univ e1
  | set ys =>
    cases e3 with
    | univ => exact Invariant.subB_univ e1
    | set zs =>
      cases e1 with
      | univ => exact absurd h (fun h' => Bool.noConfusion h')
      | set xs =>
        have h' : xs.all (fun a => memB a ys) = true := h
        show xs.all (fun a => memB a (ys ++ zs)) = true
        refine List.all_eq_true.mpr (fun a ha => ?_)
        rw [CoreAux.memB_append, List.all_eq_true.mp h' a ha, Bool.true_or]

/-- A union on the left keeps a sub-exclusion. -/
theorem subB_union_left {e1 e3 : Excl} (h : e1.subB e3 = true) (e2 : Excl) :
    e1.subB (e2.union e3) = true := by
  cases e2 with
  | univ => exact Invariant.subB_univ e1
  | set ys =>
    cases e3 with
    | univ => exact Invariant.subB_univ e1
    | set zs =>
      cases e1 with
      | univ => exact absurd h (fun h' => Bool.noConfusion h')
      | set xs =>
        have h' : xs.all (fun a => memB a zs) = true := h
        show xs.all (fun a => memB a (ys ++ zs)) = true
        refine List.all_eq_true.mpr (fun a ha => ?_)
        rw [CoreAux.memB_append, List.all_eq_true.mp h' a ha, Bool.or_true]

/-- The tail inclusion test of `coversB` gives the exclusion inclusion of `insideLocXB`. -/
theorem tailSubB_subB {a b : Kind} (h : tailSubB a b = true) (jex : Excl) :
    (tailExcl a).subB ((tailExcl b).union jex) = true := by
  cases a with
  | star ei =>
    cases b with
    | star ec => exact subB_union_right h jex
    | exact => exact Invariant.subB_univ _
    | any =>
      cases ei with
      | univ => exact absurd h (fun h' => Bool.noConfusion h')
      | set xs =>
        cases xs with
        | nil => exact empty_subB _
        | cons _ _ => exact absurd h (fun h' => Bool.noConfusion h')
  | any => exact empty_subB _
  | exact =>
    cases b with
    | exact => rfl
    | star ec =>
      cases ec with
      | univ => rfl
      | set _ => exact absurd h (fun h' => Bool.noConfusion h')
    | any => exact absurd h (fun h' => Bool.noConfusion h')

/-- The normal form keeps the pair (it only drops an exclusion). -/
theorem denX_normX {j : PFact} {jex : Excl} {x : XFact} {l1 l2 : Loc}
    (h : denX j jex x.af.fact x.ex l1 l2) :
    denX j jex (normX x).af.fact (normX x).ex l1 l2 := by
  rw [normX_fact]
  rcases AnyTaintExCov.normX_ex_cases x with he | he
  · rw [he]; exact h
  · rw [he]; exact AnyTaintExCov.denX_drop h

/-- The meet exclusion admits a continuation that the exclusion of the conclusion and the tail of
    `D-p` admit. -/
theorem meetExX_admits {k dk : Kind} {ex : Excl} {τ : List Acc} (h1 : ex.admits τ = true)
    (h2 : tailI dk τ) : (meetExX k ex dk).admits τ = true := by
  cases k with
  | any =>
    cases dk with
    | star e2 =>
      show (ex.union e2).admits τ = true
      rw [CoreAux.Excl.admits_union, h1, Bool.true_and]
      exact h2
    | any => exact h1
    | exact => exact h1
  | star e => cases dk <;> exact h1
  | exact => cases dk <;> exact h1

/-- A continuation that the meet exclusion admits is admitted by the exclusion of the
    conclusion. -/
theorem meetExX_sub {k dk : Kind} {ex : Excl} {τ : List Acc}
    (h : (meetExX k ex dk).admits τ = true) : ex.admits τ = true := by
  cases k with
  | any =>
    cases dk with
    | star e2 =>
      have h' : (ex.union e2).admits τ = true := h
      rw [CoreAux.Excl.admits_union, Bool.and_eq_true] at h'
      exact h'.1
    | any => exact h
    | exact => exact h
  | star e => cases dk <;> exact h
  | exact => cases dk <;> exact h

/-- The chain exclusion admits every continuation that the tail of `D-p` admits. -/
theorem chainExX_admits {dk : Kind} {τ : List Acc} (h : tailI dk τ) :
    (chainExX dk).admits τ = true := by
  cases dk with
  | star e2 => exact h
  | any => exact CoreAux.empty_admits τ
  | exact => exact CoreAux.empty_admits τ

/-- A star fact never carries an exclusion: its normal form drops it. -/
theorem normX_star {f : AFact} {e ex : Excl} (hk : f.fact.kind = .star e) :
    normX ⟨f, ex⟩ = ⟨f, Excl.empty⟩ := by
  apply normX_of_not
  show (f.fact.kind.isAny && !f.demand && concB f.fact.mark) = false
  rw [hk]
  rfl

theorem tailF_outKind {k : Kind} {σ τ : List Acc} (h : tailI k τ) :
    tailF (RCore.outKind k) σ τ := by
  cases k with
  | exact => exact h
  | any => trivial
  | star e => trivial

#print axioms empty_subB
#print axioms subB_union_right
#print axioms subB_union_left
#print axioms tailSubB_subB
#print axioms denX_normX
#print axioms meetExX_admits
#print axioms meetExX_sub
#print axioms chainExX_admits
#print axioms normX_star
#print axioms tailF_outKind

end XAux
open XAux

/-! ## 3. The inside test -/

/-- The location form of `insideLocXB`: every admitted location of the premise (with its
    exclusion) is a location of `d`. -/
theorem insideLocXB_sound {j d : PFact} {jex : Excl} {l : Loc} (h : insideLocXB j jex d = true)
    (hj : AnyTaintExCov.CovLocX j jex l) : d.coversLoc l := by
  obtain ⟨hbj, σ, hpj, htj, hej⟩ := hj
  unfold insideLocXB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hb, hm⟩ := h
  have hb' : d.base = j.base := CoreAux.beq_iff.mp hb
  cases hdp : dropPrefix d.path j.path with
  | none => rw [hdp] at hm; exact absurd hm (fun h' => Bool.noConfusion h')
  | some r =>
    have hq : j.path = d.path ++ r := CoreAux.dropPrefix_some.mp hdp
    rw [hdp] at hm
    cases r with
    | nil =>
      dsimp only at hm
      refine ⟨by rw [hbj, hb'], σ, by rw [hpj, hq, List.append_nil], ?_⟩
      have hu : ((tailExcl j.kind).union jex).admits σ = true := by
        rw [CoreAux.Excl.admits_union, (tailExcl_admits_iff j.kind σ).mpr htj, hej]
        rfl
      exact (tailExcl_admits_iff d.kind σ).mp (CoreAux.Excl.subB_sound hm hu)
    | cons x r =>
      dsimp only at hm
      refine ⟨by rw [hbj, hb'], x :: r ++ σ, by rw [hpj, hq, List.append_assoc], ?_⟩
      exact CoreAux.tailI_cons_append hm

/-- `insideLocB` (no exclusion read) implies `insideLocXB` for every premise exclusion. -/
theorem insideLocXB_of_base {j d : PFact} (jex : Excl) (h : insideLocB j d = true) :
    insideLocXB j jex d = true := by
  unfold insideLocB coversB at h
  unfold insideLocXB
  dsimp only at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hb, _⟩, hm⟩ := h
  rw [hb, Bool.true_and]
  cases hdp : dropPrefix d.path j.path with
  | none => rw [hdp] at hm; exact hm
  | some r =>
    rw [hdp] at hm
    cases r with
    | nil => exact tailSubB_subB hm jex
    | cons x r => exact hm

/-- The two parts of `insideXB`: the locations and the marks. -/
theorem insideXB_loc {j d : PFact} {jex : Excl} (h : insideXB j jex d = true) :
    insideLocXB j jex d = true := by
  unfold insideXB at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem insideXB_mark {j d : PFact} {jex : Excl} (h : insideXB j jex d = true) :
    markSubB d.mark j.mark = true := by
  unfold insideXB at h
  rw [Bool.and_eq_true] at h
  exact h.2

theorem insideXB_intro {j d : PFact} {jex : Excl} (h1 : insideLocXB j jex d = true)
    (h2 : markSubB d.mark j.mark = true) : insideXB j jex d = true := by
  unfold insideXB
  rw [h1, h2]
  rfl

/-- `insideB` (no exclusion read) implies `insideXB` for every premise exclusion. -/
theorem insideXB_of_base {j d : PFact} (jex : Excl) (h : insideB j d = true) :
    insideXB j jex d = true :=
  insideXB_intro (insideLocXB_of_base jex (insideB_loc h)) (insideB_mark h)

/-- The location-and-mark form of `insideXB`: every admitted location of the premise (with its
    exclusion) that has a mark of the premise is a location of `d` with a mark of `d`. -/
theorem insideXB_sound {j d : PFact} {jex : Excl} {l : Loc} (h : insideXB j jex d = true)
    (hj : AnyTaintExCov.CovLocX j jex l) (hm : j.mark.admits l.mark) : d.covers l := by
  have hd := insideLocXB_sound (insideXB_loc h) hj
  exact ⟨hd.1, hd.2, CoreAux.markSubB_sound (insideXB_mark h) hm⟩

#print axioms insideLocXB_sound
#print axioms insideLocXB_of_base
#print axioms insideXB_loc
#print axioms insideXB_mark
#print axioms insideXB_intro
#print axioms insideXB_of_base
#print axioms insideXB_sound

/-! ## 4. X3: an emitted premise lies inside its entry pattern -/

theorem emitX_emitM {d a j : PFact} {aex jex : Excl} (h : emitX d a aex = some (j, jex)) :
    emitM d a = some j := by
  unfold emitX at h
  cases he : emitM d a with
  | none => rw [he] at h; cases h
  | some j0 =>
    rw [he] at h
    dsimp only at h
    cases hr : relate d.path a.path with
    | above r =>
      rw [hr] at h
      dsimp only at h
      cases ha : aex.admits r with
      | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
      | true => rw [ha, if_pos rfl] at h; cases h; rfl
    | below r => rw [hr] at h; cases h; rfl
    | apart => rw [hr] at h; cases h; rfl

/-- X3, base form: the premise that `emitX` emits lies inside its entry pattern (as `emitM`). -/
theorem emitX_inside_base {d a j : PFact} {aex jex : Excl} (h : emitX d a aex = some (j, jex)) :
    insideLocB j d = true :=
  emitM_inside (emitX_emitM h)

/-- X3. AN EMITTED PREMISE LIES INSIDE ITS ENTRY PATTERN, with its exclusion. -/
theorem emitX_inside {d a j : PFact} {aex jex : Excl} (h : emitX d a aex = some (j, jex)) :
    insideLocXB j jex d = true :=
  insideLocXB_of_base jex (emitX_inside_base h)

/-- X3, MARK-AWARE (F71): the premise that `emitX` emits from a CONCRETE added fact lies inside its
    entry pattern in its locations (with its exclusion) AND its marks. -/
theorem emitX_insideXB {d a j : PFact} {aex jex : Excl} {t : Mark}
    (h : emitX d a aex = some (j, jex)) (ha : a.mark = .conc t) : insideXB j jex d = true :=
  insideXB_of_base jex (emitM_insideB (emitX_emitM h) ha).1

#print axioms emitX_emitM
#print axioms emitX_inside_base
#print axioms emitX_inside
#print axioms emitX_insideXB

/-! ## 5. The cells of `restrictConcIX` and `restrictIX` -/

/-- The four cells of `restrictConcIX` that give a result: AT `D-p` (the meet), BELOW `D-p` (the
    conclusion, if the tail of `D-p` admits the step), ABOVE `D-p` with an `.any` conclusion (the
    chain of `D-p` with `chainExX`), ABOVE `D-p` with a `*` conclusion (the conclusion). Each one in
    normal form. -/
theorem restrictConcIX_cases {sc g' : XFact} {p : PFact} (h : restrictConcIX sc p = some g') :
    sc.af.fact.base = p.base ∧
    ((sc.af.fact.path = p.path ∧
        g' = normX ⟨⟨⟨sc.af.fact.base, sc.af.fact.path, meetConcK sc.af.fact.kind p.kind,
          sc.af.fact.mark⟩, sc.af.demand⟩, meetExX sc.af.fact.kind sc.ex p.kind⟩) ∨
     (∃ x r, sc.af.fact.path = p.path ++ x :: r ∧ admitsTailB p.kind (x :: r) = true ∧
        g' = normX ⟨sc.af, sc.ex⟩) ∨
     (∃ r, p.path = sc.af.fact.path ++ r ∧ r ≠ [] ∧ sc.af.fact.kind = .any ∧
        sc.ex.admits r = true ∧
        g' = normX ⟨⟨⟨sc.af.fact.base, p.path, RCore.outKind p.kind, sc.af.fact.mark⟩,
          sc.af.demand⟩, chainExX p.kind⟩) ∨
     (∃ r e, p.path = sc.af.fact.path ++ r ∧ r ≠ [] ∧ sc.af.fact.kind = .star e ∧
        e.admits r = true ∧ sc.ex.admits r = true ∧ g' = normX ⟨sc.af, chainExX p.kind⟩)) := by
  unfold restrictConcIX restrictConcI at h
  cases hb : Nat.beq sc.af.fact.base p.base with
  | false => rw [hb, if_neg Bool.false_ne_true] at h; cases h
  | true =>
    rw [hb, if_pos rfl] at h
    refine ⟨CoreAux.beq_iff.mp hb, ?_⟩
    cases hr : relate p.path sc.af.fact.path with
    | apart => rw [hr] at h; cases h
    | below r =>
      have hq := CoreAux.relate_below_inv hr
      rw [hr] at h
      cases r with
      | nil =>
        exact Or.inl ⟨by rw [hq, List.append_nil], (Option.some.inj h).symm⟩
      | cons x r =>
        dsimp only at h
        cases ha : admitsTailB p.kind (x :: r) with
        | false => rw [ha, if_neg Bool.false_ne_true] at h; cases h
        | true =>
          rw [ha, if_pos rfl] at h
          exact Or.inr (Or.inl ⟨x, r, hq, ha, (Option.some.inj h).symm⟩)
    | above r =>
      obtain ⟨hP, hr0⟩ := CoreAux.relate_above_inv hr
      rw [hr] at h
      dsimp only at h
      cases hk : sc.af.fact.kind with
      | exact => rw [hk] at h; cases h
      | any =>
        rw [hk] at h
        dsimp only at h
        cases he : sc.ex.admits r with
        | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
        | true =>
          rw [he, if_pos rfl] at h
          refine Or.inr (Or.inr (Or.inl ⟨r, hP, hr0, rfl, he, ?_⟩))
          rw [← Option.some.inj h]
          cases p.kind <;> rfl
      | star e =>
        rw [hk] at h
        dsimp only at h
        cases he : e.admits r with
        | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
        | true =>
          rw [he, if_pos rfl] at h
          dsimp only at h
          cases hx : sc.ex.admits r with
          | false => rw [hx, if_neg Bool.false_ne_true] at h; cases h
          | true =>
            rw [hx, if_pos rfl] at h
            exact Or.inr (Or.inr (Or.inr ⟨r, e, hP, hr0, rfl, he, hx, (Option.some.inj h).symm⟩))

/-- A result of `restrictIX`, MARK-AWARE (F71): the demand edge has an exit pattern, the premise
    lies inside the entry pattern in its locations and its marks, the conclusion mark passes the
    mark test of `D-p`, and the conclusion is the result of `restrictConcIX`. -/
theorem restrictIX_someM {j : PFact} {jex : Excl} {g g' : XFact} {d : DemandEdge}
    (h : restrictIX j jex g d = some g') :
    ∃ p, d.dout = some p ∧ insideXB j jex d.din = true ∧
      concMarkB p.mark g.af.fact.mark = true ∧ restrictConcIX g p = some g' := by
  unfold restrictIX at h
  cases hd : d.dout with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    dsimp only at h
    cases hi : insideXB j jex d.din with
    | false => rw [hi, Bool.false_and, if_neg Bool.false_ne_true] at h; cases h
    | true =>
      cases hc : concMarkB p.mark g.af.fact.mark with
      | false => rw [hi, hc, Bool.true_and, if_neg Bool.false_ne_true] at h; cases h
      | true => rw [hi, hc, Bool.true_and, if_pos rfl] at h; exact ⟨p, rfl, rfl, hc, h⟩

/-- A result of `restrictIX`, the location form: the demand edge has an exit pattern, the premise
    lies inside the entry pattern (locations, with its exclusion), and the conclusion is the result
    of `restrictConcIX`. -/
theorem restrictIX_some {j : PFact} {jex : Excl} {g g' : XFact} {d : DemandEdge}
    (h : restrictIX j jex g d = some g') :
    ∃ p, d.dout = some p ∧ insideLocXB j jex d.din = true ∧ restrictConcIX g p = some g' := by
  obtain ⟨p, hd, hi, _, hc⟩ := restrictIX_someM h
  exact ⟨p, hd, insideXB_loc hi, hc⟩

/-- With an exit pattern, a premise inside `D-c` (locations and marks) and a conclusion mark that
    passes the mark test, `restrictIX` is `restrictConcIX`. -/
theorem restrictIX_of {j : PFact} {jex : Excl} {g : XFact} {d : DemandEdge} {p : PFact}
    (hd : d.dout = some p) (hi : insideXB j jex d.din = true)
    (hm : concMarkB p.mark g.af.fact.mark = true) :
    restrictIX j jex g d = restrictConcIX g p := by
  unfold restrictIX
  rw [hd]
  dsimp only
  rw [hi, hm]
  rfl

#print axioms restrictConcIX_cases
#print axioms restrictIX_someM
#print axioms restrictIX_some
#print axioms restrictIX_of

/-- The fact part of `restrictConcIX` is `restrictConcI` (`HandoffDefs.lean`): the exclusions only
    decide the exclusion of the result and, above `D-p`, if there is a result. -/
theorem restrictConcIX_fact {sc g' : XFact} {p : PFact} (h : restrictConcIX sc p = some g') :
    restrictConcI sc.af p = some g'.af := by
  unfold restrictConcIX at h
  cases hI : restrictConcI sc.af p with
  | none => rw [hI] at h; cases h
  | some g0 =>
    rw [hI] at h
    dsimp only at h
    cases hr : relate p.path sc.af.fact.path with
    | apart => rw [hr] at h; cases h
    | below r =>
      rw [hr] at h
      cases r with
      | nil => dsimp only at h; cases h; rw [normX_af]
      | cons x r => dsimp only at h; cases h; rw [normX_af]
    | above r =>
      rw [hr] at h
      dsimp only at h
      cases he : sc.ex.admits r with
      | false => rw [he, if_neg Bool.false_ne_true] at h; cases h
      | true => rw [he, if_pos rfl] at h; cases h; rw [normX_af]

/-- On the forgotten view, `restrictIX` is the base intersection `restrictI` of `HandoffDefs.lean`
    for a premise that lies inside `D-c` with no exclusion read (`insideLocB`; e.g. every premise
    with `jex = {}`): the same result fact, in the same layer. Both restrictions have the same mark
    tests (F71), so the marks of a result of `restrictIX` pass the tests of `restrictI`. -/
theorem restrictIX_restrictI {j : PFact} {jex : Excl} {g g' : XFact} {d : DemandEdge}
    (hin : insideLocB j d.din = true) (h : restrictIX j jex g d = some g') :
    restrictI j g.af d = some g'.af := by
  obtain ⟨p, hdo, hix, hcm, hc⟩ := restrictIX_someM h
  rw [restrictI_of hdo (insideB_intro hin (insideXB_mark hix)) hcm]
  exact restrictConcIX_fact hc

/-- `restrictConcIX` keeps the mark of the conclusion. -/
theorem restrictConcIX_mark {sc g' : XFact} {p : PFact} (h : restrictConcIX sc p = some g') :
    g'.af.fact.mark = sc.af.fact.mark :=
  restrictConcI_mark (restrictConcIX_fact h)

#print axioms restrictConcIX_fact
#print axioms restrictIX_restrictI
#print axioms restrictConcIX_mark

/-! ## 6. X1: the restriction only removes pairs, in normal form -/

/-- The base facts of a result of `restrictConcIX` only lose pairs, and the layer stays (no normal
    form needed: the exclusions are not read). -/
theorem restrictConcIX_sub_base {sc g' : XFact} {p : PFact} (h : restrictConcIX sc p = some g') :
    g'.af.demand = sc.af.demand ∧
    ∀ (j : PFact) l1 l2, den j g'.af.fact l1 l2 → den j sc.af.fact l1 l2 := by
  obtain ⟨_, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨r, hP, _, hk, _, h3⟩ | ⟨_, _, _, _, _, _, _, h4⟩⟩ :=
    restrictConcIX_cases h
  · subst h1
    rw [normX_af]
    refine ⟨rfl, fun j l1 l2 hd => ?_⟩
    obtain ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, htf⟩ := hd
    exact ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, RAux.meetConcK_tailF htf⟩
  · subst h2
    rw [normX_af]
    exact ⟨rfl, fun _ _ _ hd => hd⟩
  · subst h3
    rw [normX_af]
    refine ⟨rfl, fun j l1 l2 hd => ?_⟩
    obtain ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, _⟩ := hd
    refine ⟨hb1, hb2, hm1, hm2, hps, σ, r ++ τ, hp1, ?_, hti, ?_⟩
    · rw [hp2]
      show p.path ++ τ = sc.af.fact.path ++ (r ++ τ)
      rw [hP, List.append_assoc]
    · rw [hk]
      trivial
  · subst h4
    rw [normX_af]
    exact ⟨rfl, fun _ _ _ hd => hd⟩

/-- The base form of X1: the facts of a result of `restrictIX` only lose pairs, and the layer
    stays. -/
theorem restrictIX_sub_base {j : PFact} {jex : Excl} {g g' : XFact} {d : DemandEdge}
    (h : restrictIX j jex g d = some g') :
    g'.af.demand = g.af.demand ∧ ∀ l1 l2, den j g'.af.fact l1 l2 → den j g.af.fact l1 l2 := by
  obtain ⟨p, _, _, hc⟩ := restrictIX_some h
  obtain ⟨hd, hs⟩ := restrictConcIX_sub_base hc
  exact ⟨hd, fun l1 l2 h' => hs j l1 l2 h'⟩

/-- Every result of `restrictConcIX` is in normal form. -/
theorem restrictConcIX_wf {sc g' : XFact} {p : PFact} (h : restrictConcIX sc p = some g') :
    WFX g' := by
  obtain ⟨_, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨_, _, _, _, _, h3⟩ | ⟨_, _, _, _, _, _, _, h4⟩⟩ :=
    restrictConcIX_cases h
  · rw [h1]; exact normX_wf _
  · rw [h2]; exact normX_wf _
  · rw [h3]; exact normX_wf _
  · rw [h4]; exact normX_wf _

/-- The pairs of a result of `restrictConcIX` (exclusions read) are pairs of a conclusion in
    normal form. -/
theorem restrictConcIX_pairs {sc g' : XFact} {p : PFact} (hw : WFX sc)
    (h : restrictConcIX sc p = some g') {j : PFact} {jex : Excl} {l1 l2 : Loc}
    (hd : denX j jex g'.af.fact g'.ex l1 l2) : denX j jex sc.af.fact sc.ex l1 l2 := by
  obtain ⟨_, ⟨_, h1⟩ | ⟨_, _, _, _, h2⟩ | ⟨r, hP, hr0, hk, hadm, h3⟩ |
    ⟨_, e, _, _, hk, _, _, h4⟩⟩ := restrictConcIX_cases h
  · -- at `D-p`: the meet
    subst h1
    rw [normX_fact] at hd
    obtain ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, htf, hjex, hgex⟩ := hd
    refine ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, RAux.meetConcK_tailF htf, hjex, ?_⟩
    cases hgx : sc.ex.admits τ with
    | true => rfl
    | false =>
      exfalso
      obtain ⟨hk, hdm, t, hmk⟩ := carriesB_parts (carriesB_of_ex hw hgx)
      rw [hk] at htf hgex
      cases hpk : p.kind with
      | exact =>
        rw [hpk] at htf
        have hτ : τ = [] := htf
        rw [hτ, CoreAux.admits_nil] at hgx
        exact Bool.noConfusion hgx
      | any =>
        rw [hpk] at hgex
        have hx : carriesB (⟨⟨sc.af.fact.base, sc.af.fact.path, meetConcK .any .any,
            sc.af.fact.mark⟩, sc.af.demand⟩ : AFact) = true := by
          unfold carriesB; rw [hdm, hmk]; rfl
        rw [normX_of_carries (x := ⟨⟨⟨sc.af.fact.base, sc.af.fact.path, meetConcK .any .any,
            sc.af.fact.mark⟩, sc.af.demand⟩, meetExX .any sc.ex .any⟩) hx] at hgex
        have h' : sc.ex.admits τ = true := meetExX_sub (k := .any) (dk := .any) hgex
        rw [hgx] at h'
        exact Bool.noConfusion h'
      | star e2 =>
        rw [hpk] at hgex
        have hx : carriesB (⟨⟨sc.af.fact.base, sc.af.fact.path, meetConcK .any (.star e2),
            sc.af.fact.mark⟩, sc.af.demand⟩ : AFact) = true := by
          unfold carriesB; rw [hdm, hmk]; rfl
        rw [normX_of_carries (x := ⟨⟨⟨sc.af.fact.base, sc.af.fact.path, meetConcK .any (.star e2),
            sc.af.fact.mark⟩, sc.af.demand⟩, meetExX .any sc.ex (.star e2)⟩) hx] at hgex
        have h' : sc.ex.admits τ = true := meetExX_sub (k := .any) (dk := .star e2) hgex
        rw [hgx] at h'
        exact Bool.noConfusion h'
  · -- below `D-p`: the conclusion itself
    subst h2
    rw [show (⟨sc.af, sc.ex⟩ : XFact) = sc from rfl, normX_of_wf hw] at hd
    exact hd
  · -- above `D-p`, an `.any` conclusion: the chain of `D-p`
    subst h3
    rw [normX_fact] at hd
    obtain ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, _, hjex, _⟩ := hd
    refine ⟨hb1, hb2, hm1, hm2, hps, σ, r ++ τ, hp1, ?_, hti, by rw [hk]; trivial, hjex, ?_⟩
    · rw [hp2]
      show p.path ++ τ = sc.af.fact.path ++ (r ++ τ)
      rw [hP, List.append_assoc]
    · cases r with
      | nil => exact absurd rfl hr0
      | cons x r' => exact Exact.admits_cons_append τ hadm
  · -- above `D-p`, a `*` conclusion: the conclusion with no exclusion
    subst h4
    rw [normX_star hk] at hd
    have hex : sc.ex = Excl.empty := hw (by
      show (sc.af.fact.kind.isAny && !sc.af.demand && concB sc.af.fact.mark) = false
      rw [hk]; rfl)
    rw [hex]
    exact hd

/-- X1. THE RESTRICTION HAS THE NORMAL-FORM CONTRACT `RestrictOKX` (`AnyTaintExExact`): a
    conclusion in normal form gives a conclusion in normal form, in the same layer, with fewer
    pairs (exclusions read). -/
theorem restrictIX_ok : AnyTaintExExact.RestrictOKX restrictIX := by
  intro j jex g d g' hgw h
  obtain ⟨p, _, _, hc⟩ := restrictIX_some h
  exact ⟨restrictConcIX_wf hc, (restrictConcIX_sub_base hc).1,
    fun l1 l2 hd => restrictConcIX_pairs hgw hc hd⟩

#print axioms restrictConcIX_sub_base
#print axioms restrictIX_sub_base
#print axioms restrictConcIX_wf
#print axioms restrictConcIX_pairs
#print axioms restrictIX_ok

/-! ## 7. X2: the contract C5 for a premise inside `D-c` -/

/-- C5 of the conclusion part: a pair of the edge (exclusions read) whose exit location is in
    `D-p` stays, in the same layer. Every cell, also a `*` conclusion: at `D-p` the meet keeps the
    pair (the `D-p` tail admits the exit continuation, so `E ∪ E2` admits it too); below `D-p` the
    conclusion stays; above `D-p` an `.any` conclusion gives the chain (its exclusion admits the
    step, and `E2` admits the rest), a `*` conclusion stays (correlated: its exclusion and the
    conclusion exclusion admit the step), a `$` conclusion has no pair there. -/
theorem restrictConcIX_contract {j : PFact} {jex : Excl} {g : XFact} {p : PFact} {l1 l2 : Loc}
    (hden : denX j jex g.af.fact g.ex l1 l2) (hp : p.coversLoc l2) :
    ∃ g', restrictConcIX g p = some g' ∧ denX j jex g'.af.fact g'.ex l1 l2 ∧
      g'.af.demand = g.af.demand := by
  have hden0 := hden
  obtain ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, htf, hjex, hgex⟩ := hden
  obtain ⟨hbp, σ', hpp, htp⟩ := hp
  have hb : Nat.beq g.af.fact.base p.base = true := by rw [← hb2, ← hbp]; exact Nat.beq_refl _
  have hpath : p.path ++ σ' = g.af.fact.path ++ τ := by rw [← hpp, ← hp2]
  unfold restrictConcIX restrictConcI
  rw [if_pos hb]
  rcases CoreAux.relate_common hpath with ⟨r, hrel, _, hσ⟩ | ⟨r, hrel, _, hr, hτ⟩
  · rw [hrel]
    cases r with
    | nil =>
      -- at the path of `D-p`: the meet
      have hτp : tailI p.kind τ := by rw [hσ] at htp; exact htp
      dsimp only
      refine ⟨_, rfl, denX_normX ?_, by rw [normX_af]⟩
      exact ⟨hb1, hb2, hm1, hm2, hps, σ, τ, hp1, hp2, hti, RAux.meetConcK_tailF_of htf hτp, hjex,
        meetExX_admits hgex hτp⟩
    | cons x r =>
      -- below `D-p`: the conclusion stays
      have ha : admitsTailB p.kind (x :: r) = true := by
        rw [hσ] at htp
        exact CoreAux.tailI_append_admits htp
      dsimp only
      rw [if_pos ha]
      exact ⟨_, rfl, denX_normX hden0, by rw [normX_af]⟩
  · -- above `D-p`
    rw [hrel]
    dsimp only
    have hgr : g.ex.admits r = true := by
      rw [hτ] at hgex
      exact AnyTaintExCov.admits_prefix hgex
    cases hk : g.af.fact.kind with
    | star e =>
      -- correlated: the continuation is the initial one, so `e` admits the step
      rw [hk] at htf
      obtain ⟨hτσ, he⟩ := htf
      have her : e.admits r = true := by
        rw [← hτσ, hτ] at he
        exact AnyTaintExCov.admits_prefix he
      dsimp only
      rw [if_pos her]
      dsimp only
      rw [if_pos hgr]
      refine ⟨_, rfl, ?_, by rw [normX_af]⟩
      rw [normX_star hk]
      exact AnyTaintExCov.denX_drop hden0
    | any =>
      -- uncorrelated: the chain of `D-p` with the exclusion of `D-p`
      dsimp only
      rw [if_pos hgr]
      refine ⟨_, rfl, denX_normX ?_, by rw [normX_af]⟩
      have htF : tailF (RCore.outKind p.kind) σ σ' := tailF_outKind htp
      refine ⟨hb1, hb2, hm1, hm2, hps, σ, σ', hp1, hpp, hti, ?_, hjex, chainExX_admits htp⟩
      revert htF
      cases p.kind <;> exact id
    | exact =>
      exfalso
      rw [hk] at htf
      have hτ0 : τ = [] := htf
      rw [hτ0] at hτ
      cases r with
      | nil => exact hr rfl
      | cons x r' => exact List.cons_ne_nil x (r' ++ σ') hτ.symm

/-- X2. THE CONTRACT C5 OF THE INTERSECTION WITH THE EXCLUSION, MARK-AWARE (F71): if the premise
    (with its exclusion) lies inside `D-c` in its locations and marks (`insideXB`), every pair of
    the edge (exclusions read) whose exit location (with its mark) `D-p` covers stays, in the same
    layer. For EVERY conclusion (also `*`); the mark test by `concMarkB_of_den`. -/
theorem restrictIX_contract {j : PFact} {jex : Excl} {g : XFact} {d : DemandEdge} {p : PFact}
    {l1 l2 : Loc} (hin : insideXB j jex d.din = true) (hden : denX j jex g.af.fact g.ex l1 l2)
    (hdout : d.dout = some p) (hp : p.covers l2) :
    ∃ g', restrictIX j jex g d = some g' ∧ denX j jex g'.af.fact g'.ex l1 l2 ∧
      g'.af.demand = g.af.demand := by
  rw [restrictIX_of hdout hin (RAux.concMarkB_of_den (denX_den hden) hp.2.2)]
  exact restrictConcIX_contract hden (RCore.covers_coversLoc hp)

/-- X2 from the base inside test (`insideB`, the form of `emitM_insideB`). -/
theorem restrictIX_contract_base {j : PFact} {jex : Excl} {g : XFact} {d : DemandEdge}
    {p : PFact} {l1 l2 : Loc} (hin : insideB j d.din = true)
    (hden : denX j jex g.af.fact g.ex l1 l2) (hdout : d.dout = some p) (hp : p.covers l2) :
    ∃ g', restrictIX j jex g d = some g' ∧ denX j jex g'.af.fact g'.ex l1 l2 ∧
      g'.af.demand = g.af.demand :=
  restrictIX_contract (insideXB_of_base jex hin) hden hdout hp

#print axioms restrictConcIX_contract
#print axioms restrictIX_contract
#print axioms restrictIX_contract_base

/-- CEGAR: the OVERLAP form of C5 (`RestrictContractX` of `AnyTaintExDefs.lean`: the entry
    location in `D-c`, the premise only overlapping `D-c`) is FALSE for `restrictIX`: the premise
    `1.*` (it covers the entry location `1.[5]` of `D-c = 1.[5].$`) does not lie inside `D-c`, so
    the intersection gives nothing. The coverage proof needs `emitX_inside`. -/
theorem restrictIX_not_RestrictContractX : ¬ RestrictContractX restrictIX := by
  intro h
  let j : PFact := ⟨1, [], .star Excl.empty, .star⟩
  let g : XFact := ⟨⟨⟨1, [], .star Excl.empty, .star⟩, false⟩, Excl.empty⟩
  let p : PFact := ⟨1, [5], .exact, .star⟩
  let d : DemandEdge := ⟨p, some p⟩
  have hd : denX j Excl.empty g.af.fact g.ex ⟨1, [5], 3⟩ ⟨1, [5], 3⟩ :=
    ⟨rfl, rfl, trivial, rfl, trivial, [5], [5], rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩
  have hc : p.coversLoc ⟨1, [5], 3⟩ := ⟨rfl, [], rfl, rfl⟩
  obtain ⟨g', hg', _, _⟩ := h j Excl.empty g d p ⟨1, [5], 3⟩ ⟨1, [5], 3⟩ hd hc rfl hc
  have hnone : restrictIX j Excl.empty g d = none := by decide
  rw [hnone] at hg'
  cases hg'

#print axioms restrictIX_not_RestrictContractX

/-! ## 8. X4: the intersection property, with its exact exceptions -/

/-- THE TWO EXCEPTIONS of the intersection with the exclusion (the cells that keep more than the
    intersection), for the conclusion `g`, the exit pattern `p` and the result `g'`:
    * (a) an `.any` conclusion that does NOT carry an exclusion (`carriesB` false: a demand
      `[any]`; in a concrete run every other `.any` conclusion is `[any-taint]`) at or above a
      `*/E` exit pattern: the result is the chain of `D-p` with the tail `.any` and no exclusion
      (W2: a concrete mark has no `*` tail; DESIGN A2: a demand `[any]` has no exclusion);
    * (b) a `*` conclusion: the result is the conclusion itself, with no exclusion (a cut to `$`
      adds pairs; the exact meet would be `*/Universe`, which S8 forbids). -/
def RExcX (g : XFact) (p : PFact) (g' : XFact) : Prop :=
  (g.af.fact.kind = .any ∧ carriesB g.af = false ∧ (∃ E, p.kind = .star E) ∧
    g'.af.fact = ⟨g.af.fact.base, p.path, .any, g.af.fact.mark⟩ ∧ g'.af.demand = g.af.demand ∧
    g'.ex = Excl.empty) ∨
  ((∃ e, g.af.fact.kind = .star e) ∧ g'.af = g.af ∧ g'.ex = Excl.empty)

/-- `carriesB` reads only the tail, the layer and the mark. -/
theorem carriesB_any_eq {f : AFact} (hk : f.fact.kind = .any) (b : Base) (q : List Acc) :
    carriesB ⟨⟨b, q, .any, f.fact.mark⟩, f.demand⟩ = carriesB f := by
  unfold carriesB
  rw [hk]

/-- The `.any` result of a meet or of a chain: in normal form it keeps the exclusion iff the
    conclusion carries one. -/
theorem normX_any_cases {f : AFact} (hk : f.fact.kind = .any) (b : Base) (q : List Acc) (ex : Excl) :
    (carriesB f = true ∧
      normX ⟨⟨⟨b, q, .any, f.fact.mark⟩, f.demand⟩, ex⟩ = ⟨⟨⟨b, q, .any, f.fact.mark⟩, f.demand⟩, ex⟩) ∨
    (carriesB f = false ∧
      normX ⟨⟨⟨b, q, .any, f.fact.mark⟩, f.demand⟩, ex⟩ =
        ⟨⟨⟨b, q, .any, f.fact.mark⟩, f.demand⟩, Excl.empty⟩) := by
  cases hc : carriesB f with
  | true =>
    left
    refine ⟨rfl, normX_of_carries ?_⟩
    show carriesB ⟨⟨b, q, .any, f.fact.mark⟩, f.demand⟩ = true
    rw [carriesB_any_eq hk, hc]
  | false =>
    right
    refine ⟨rfl, normX_of_not ?_⟩
    show carriesB ⟨⟨b, q, .any, f.fact.mark⟩, f.demand⟩ = false
    rw [carriesB_any_eq hk, hc]

#print axioms carriesB_any_eq
#print axioms normX_any_cases

/-- The exit part of X4 for the conclusion restriction: every pair of a result has its exit
    location in `D-p`, except the cells of `RExcX`. -/
theorem restrictConcIX_exit {sc g' : XFact} {p : PFact} (h : restrictConcIX sc p = some g')
    {j : PFact} {jex : Excl} {l1 l2 : Loc} (hd : denX j jex g'.af.fact g'.ex l1 l2) :
    p.coversLoc l2 ∨ RExcX sc p g' := by
  obtain ⟨hbp, ⟨hq, h1⟩ | ⟨x, r, hq, ha, h2⟩ | ⟨r, _, _, hk, _, h3⟩ | ⟨r, e, _, _, hk, _, _, h4⟩⟩ :=
    restrictConcIX_cases h
  · -- at `D-p`: the meet
    subst h1
    obtain ⟨⟨⟨b, q, k, m⟩, dm⟩, ex⟩ := sc
    obtain ⟨pb, pq, pk, pm⟩ := p
    dsimp only at hbp hq hd ⊢
    subst hbp hq
    cases k with
    | exact =>
      rw [normX_fact] at hd
      obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, htf, _, _⟩ := hd
      have hτ : τ = [] := by cases pk <;> exact htf
      left
      exact ⟨hb2, [], by rw [hp2, hτ], RAux.tailI_nil pk⟩
    | star e =>
      right; right
      refine ⟨⟨e, rfl⟩, ?_, ?_⟩
      · rw [normX_af]; cases pk <;> rfl
      · exact congrArg XFact.ex (normX_star rfl)
    | any =>
      cases pk with
      | exact =>
        rw [normX_fact] at hd
        obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, htf, _, _⟩ := hd
        have hτ : τ = [] := htf
        left
        exact ⟨hb2, [], by rw [hp2, hτ], rfl⟩
      | any =>
        rw [normX_fact] at hd
        obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, _, _, _⟩ := hd
        left
        exact ⟨hb2, τ, hp2, trivial⟩
      | star E =>
        rcases normX_any_cases (f := ⟨⟨b, q, .any, m⟩, dm⟩) rfl b q (ex.union E) with
          ⟨_, hn⟩ | ⟨hc, hn⟩
        · left
          have hn' : normX ⟨⟨⟨b, q, meetConcK .any (.star E), m⟩, dm⟩, meetExX .any ex (.star E)⟩ =
              ⟨⟨⟨b, q, .any, m⟩, dm⟩, ex.union E⟩ := hn
          rw [hn'] at hd
          obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, _, _, hgex⟩ := hd
          have hgex' : (ex.union E).admits τ = true := hgex
          rw [CoreAux.Excl.admits_union, Bool.and_eq_true] at hgex'
          exact ⟨hb2, τ, hp2, hgex'.2⟩
        · right; left
          have hn' : normX ⟨⟨⟨b, q, meetConcK .any (.star E), m⟩, dm⟩, meetExX .any ex (.star E)⟩ =
              ⟨⟨⟨b, q, .any, m⟩, dm⟩, Excl.empty⟩ := hn
          rw [hn']
          exact ⟨rfl, hc, ⟨E, rfl⟩, rfl, rfl, rfl⟩
  · -- below `D-p`: the tail of `D-p` admits the step
    subst h2
    rw [normX_fact] at hd
    obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, _, _, _⟩ := hd
    left
    refine ⟨by rw [hb2]; exact hbp, x :: r ++ τ, ?_, CoreAux.tailI_cons_append ha⟩
    rw [hp2, hq, List.append_assoc]
  · -- above `D-p`, an `.any` conclusion: the chain of `D-p`
    subst h3
    obtain ⟨⟨⟨b, q, k, m⟩, dm⟩, ex⟩ := sc
    obtain ⟨pb, pq, pk, pm⟩ := p
    dsimp only at hbp hk hd ⊢
    subst hbp hk
    cases pk with
    | exact =>
      rw [normX_fact] at hd
      obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, htf, _, _⟩ := hd
      have hτ : τ = [] := htf
      left
      exact ⟨hb2, [], by rw [hp2, hτ], rfl⟩
    | any =>
      rw [normX_fact] at hd
      obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, _, _, _⟩ := hd
      left
      exact ⟨hb2, τ, hp2, trivial⟩
    | star E =>
      rcases normX_any_cases (f := ⟨⟨b, q, .any, m⟩, dm⟩) rfl b pq E with ⟨_, hn⟩ | ⟨hc, hn⟩
      · left
        have hn' : normX ⟨⟨⟨b, pq, RCore.outKind (.star E), m⟩, dm⟩, chainExX (.star E)⟩ =
            ⟨⟨⟨b, pq, .any, m⟩, dm⟩, E⟩ := hn
        rw [hn'] at hd
        obtain ⟨_, hb2, _, _, _, σ, τ, _, hp2, _, _, _, hgex⟩ := hd
        exact ⟨hb2, τ, hp2, hgex⟩
      · right; left
        have hn' : normX ⟨⟨⟨b, pq, RCore.outKind (.star E), m⟩, dm⟩, chainExX (.star E)⟩ =
            ⟨⟨⟨b, pq, .any, m⟩, dm⟩, Excl.empty⟩ := hn
        rw [hn']
        exact ⟨rfl, hc, ⟨E, rfl⟩, rfl, rfl, rfl⟩
  · -- above `D-p`, a `*` conclusion: the conclusion itself
    subst h4
    right; right
    exact ⟨⟨e, hk⟩, by rw [normX_af], congrArg XFact.ex (normX_star hk)⟩

/-- X4. THE INTERSECTION PROPERTY WITH THE EXCLUSION. Every pair of a result of `restrictIX`
    (exclusions read) has its entry location in `D-c` (the premise with its exclusion lies inside
    `D-c`) and its exit location in `D-p`, except in the two cells of `RExcX`. -/
theorem restrictIX_inter {j : PFact} {jex : Excl} {g g' : XFact} {d : DemandEdge}
    (h : restrictIX j jex g d = some g') {l1 l2 : Loc} (hd : denX j jex g'.af.fact g'.ex l1 l2) :
    d.din.coversLoc l1 ∧ ∃ p, d.dout = some p ∧ (p.coversLoc l2 ∨ RExcX g p g') := by
  obtain ⟨p, hdo, hin, hc⟩ := restrictIX_some h
  have hd0 := hd
  obtain ⟨hb1, _, _, _, _, σ, _, hp1, _, hti, _, hjex, _⟩ := hd0
  exact ⟨insideLocXB_sound hin ⟨hb1, σ, hp1, hti, hjex⟩, p, hdo, restrictConcIX_exit hc hd⟩

/-- X4, MARK-AWARE (F71). Every pair of a result of `restrictIX` (exclusions read) has its entry
    location WITH its mark in `D-c`, and its exit location in `D-p` (except `RExcX`) with a mark of
    `D-p` (except an abstract conclusion mark). -/
theorem restrictIX_interM {j : PFact} {jex : Excl} {g g' : XFact} {d : DemandEdge}
    (h : restrictIX j jex g d = some g') {l1 l2 : Loc} (hd : denX j jex g'.af.fact g'.ex l1 l2) :
    d.din.covers l1 ∧ ∃ p, d.dout = some p ∧ (p.coversLoc l2 ∨ RExcX g p g') ∧
      (p.mark.admits l2.mark ∨ Invariant.AbsMark g.af.fact.mark) := by
  obtain ⟨p, hdo, hin, hm, hc⟩ := restrictIX_someM h
  have hd0 := hd
  obtain ⟨hb1, _, hm1, _, _, σ, _, hp1, _, hti, _, hjex, _⟩ := hd0
  exact ⟨insideXB_sound hin ⟨hb1, σ, hp1, hti, hjex⟩ hm1, p, hdo, restrictConcIX_exit hc hd,
    restrictI_exit_mark hm (restrictConcIX_fact hc) (denX_den hd)⟩

/-- X4 for a CONCRETE conclusion mark (every exit edge of a restricted run): the exit location has
    its mark in `D-p`, also in the cells of `RExcX`. -/
theorem restrictIX_inter_conc {j : PFact} {jex : Excl} {g g' : XFact} {d : DemandEdge} {t : Mark}
    (h : restrictIX j jex g d = some g') (ht : g.af.fact.mark = .conc t) {l1 l2 : Loc}
    (hd : denX j jex g'.af.fact g'.ex l1 l2) :
    d.din.covers l1 ∧ ∃ p, d.dout = some p ∧
      (p.covers l2 ∨ (RExcX g p g' ∧ p.mark.admits l2.mark)) := by
  obtain ⟨hin, p, hdo, hloc, hmk⟩ := restrictIX_interM h hd
  have hmk' : p.mark.admits l2.mark := by
    rcases hmk with hmk | hab
    · exact hmk
    · exact absurd ht (Invariant.AbsMark.not_conc hab t)
  refine ⟨hin, p, hdo, ?_⟩
  rcases hloc with hl | hr
  · exact Or.inl ⟨hl.1, hl.2, hmk'⟩
  · exact Or.inr ⟨hr, hmk'⟩

#print axioms restrictConcIX_exit
#print axioms restrictIX_inter
#print axioms restrictIX_interM
#print axioms restrictIX_inter_conc

/-! ### The pattern form: the result lies inside `D-p` -/

theorem insideLocXB_at {f p : PFact} {ex : Excl} (hb : f.base = p.base) (hq : f.path = p.path)
    (hs : (tailExcl p.kind).subB ((tailExcl f.kind).union ex) = true) :
    insideLocXB f ex p = true := by
  unfold insideLocXB
  rw [hb, hq, Nat.beq_refl, RAux.dropPrefix_self']
  exact hs

theorem insideLocXB_below {f p : PFact} {ex : Excl} {x : Acc} {r : List Acc}
    (hb : f.base = p.base) (hq : f.path = p.path ++ x :: r)
    (ha : admitsTailB p.kind (x :: r) = true) : insideLocXB f ex p = true := by
  unfold insideLocXB
  rw [hb, hq, Nat.beq_refl, Store.dropPrefix_append]
  exact ha

#print axioms insideLocXB_at
#print axioms insideLocXB_below

/-- The conclusion part of the narrowing: the result of `restrictConcIX`, read as a pattern WITH
    ITS EXCLUSION, lies inside `D-p`, except in the two cells of `RExcX`. -/
theorem restrictConcIX_inside {sc g' : XFact} {p : PFact} (h : restrictConcIX sc p = some g') :
    insideLocXB g'.af.fact g'.ex p = true ∨ RExcX sc p g' := by
  obtain ⟨hbp, ⟨hq, h1⟩ | ⟨x, r, hq, ha, h2⟩ | ⟨r, _, _, hk, _, h3⟩ | ⟨r, e, _, _, hk, _, _, h4⟩⟩ :=
    restrictConcIX_cases h
  · -- at `D-p`: the meet
    subst h1
    obtain ⟨⟨⟨b, q, k, m⟩, dm⟩, ex⟩ := sc
    obtain ⟨pb, pq, pk, pm⟩ := p
    dsimp only at hbp hq ⊢
    subst hbp hq
    cases k with
    | exact =>
      left
      refine insideLocXB_at (by rw [normX_fact]) (by rw [normX_fact]) ?_
      rw [normX_fact]
      exact Invariant.subB_univ _
    | star e =>
      right; right
      refine ⟨⟨e, rfl⟩, ?_, ?_⟩
      · rw [normX_af]; cases pk <;> rfl
      · exact congrArg XFact.ex (normX_star rfl)
    | any =>
      cases pk with
      | exact =>
        left
        refine insideLocXB_at (by rw [normX_fact]) (by rw [normX_fact]) ?_
        rw [normX_fact]
        exact Invariant.subB_univ _
      | any =>
        left
        exact insideLocXB_at (by rw [normX_fact]) (by rw [normX_fact]) (empty_subB _)
      | star E =>
        rcases normX_any_cases (f := ⟨⟨b, q, .any, m⟩, dm⟩) rfl b q (ex.union E) with
          ⟨_, hn⟩ | ⟨hc, hn⟩
        · left
          have hn' : normX ⟨⟨⟨b, q, meetConcK .any (.star E), m⟩, dm⟩, meetExX .any ex (.star E)⟩ =
              ⟨⟨⟨b, q, .any, m⟩, dm⟩, ex.union E⟩ := hn
          rw [hn']
          exact insideLocXB_at rfl rfl
            (subB_union_left (subB_union_left (subB_refl E) ex) Excl.empty)
        · right; left
          have hn' : normX ⟨⟨⟨b, q, meetConcK .any (.star E), m⟩, dm⟩, meetExX .any ex (.star E)⟩ =
              ⟨⟨⟨b, q, .any, m⟩, dm⟩, Excl.empty⟩ := hn
          rw [hn']
          exact ⟨rfl, hc, ⟨E, rfl⟩, rfl, rfl, rfl⟩
  · -- below `D-p`: the tail of `D-p` admits the step
    subst h2
    left
    exact insideLocXB_below (by rw [normX_fact]; exact hbp) (by rw [normX_fact]; exact hq) ha
  · -- above `D-p`, an `.any` conclusion: the chain of `D-p`
    subst h3
    obtain ⟨⟨⟨b, q, k, m⟩, dm⟩, ex⟩ := sc
    obtain ⟨pb, pq, pk, pm⟩ := p
    dsimp only at hbp hk ⊢
    subst hbp hk
    cases pk with
    | exact =>
      left
      refine insideLocXB_at (by rw [normX_fact]) (by rw [normX_fact]) ?_
      rw [normX_fact]
      exact Invariant.subB_univ _
    | any =>
      left
      exact insideLocXB_at (by rw [normX_fact]) (by rw [normX_fact]) (empty_subB _)
    | star E =>
      rcases normX_any_cases (f := ⟨⟨b, q, .any, m⟩, dm⟩) rfl b pq E with ⟨_, hn⟩ | ⟨hc, hn⟩
      · left
        have hn' : normX ⟨⟨⟨b, pq, RCore.outKind (.star E), m⟩, dm⟩, chainExX (.star E)⟩ =
            ⟨⟨⟨b, pq, .any, m⟩, dm⟩, E⟩ := hn
        rw [hn']
        exact insideLocXB_at rfl rfl (subB_union_left (subB_refl E) Excl.empty)
      · right; left
        have hn' : normX ⟨⟨⟨b, pq, RCore.outKind (.star E), m⟩, dm⟩, chainExX (.star E)⟩ =
            ⟨⟨⟨b, pq, .any, m⟩, dm⟩, Excl.empty⟩ := hn
        rw [hn']
        exact ⟨rfl, hc, ⟨E, rfl⟩, rfl, rfl, rfl⟩
  · -- above `D-p`, a `*` conclusion: the conclusion itself
    subst h4
    right; right
    exact ⟨⟨e, hk⟩, by rw [normX_af], congrArg XFact.ex (normX_star hk)⟩

/-- X4, THE PATTERN FORM (THE NARROWING OF ONE RESTRICTION): a result of `restrictIX` comes from
    the exit pattern `p` of the demand edge; the premise with its exclusion lies inside `D-c`, and
    the result with its exclusion lies inside `D-p` (except `RExcX`). -/
theorem restrictIX_narrow {j : PFact} {jex : Excl} {g g' : XFact} {d : DemandEdge}
    (h : restrictIX j jex g d = some g') :
    ∃ p, d.dout = some p ∧ insideLocXB j jex d.din = true ∧
      (insideLocXB g'.af.fact g'.ex p = true ∨ RExcX g p g') := by
  obtain ⟨p, hdo, hin, hc⟩ := restrictIX_some h
  exact ⟨p, hdo, hin, restrictConcIX_inside hc⟩

/-- X4, THE PATTERN FORM, MARK-AWARE (F71): the premise lies inside `D-c` with its exclusion AND
    its marks; the result lies inside `D-p` with its exclusion (except `RExcX`) and its marks
    (except an abstract conclusion mark). -/
theorem restrictIX_narrowM {j : PFact} {jex : Excl} {g g' : XFact} {d : DemandEdge}
    (h : restrictIX j jex g d = some g') :
    ∃ p, d.dout = some p ∧ insideXB j jex d.din = true ∧
      (insideLocXB g'.af.fact g'.ex p = true ∨ RExcX g p g') ∧
      (markSubB p.mark g'.af.fact.mark = true ∨ Invariant.AbsMark g.af.fact.mark) := by
  obtain ⟨p, hdo, hin, hm, hc⟩ := restrictIX_someM h
  refine ⟨p, hdo, hin, restrictConcIX_inside hc, ?_⟩
  rcases RAux.mark_conc_or_abs g.af.fact.mark with ⟨t, ht⟩ | habs
  · left
    rw [restrictConcIX_mark hc, ht, ← RAux.concMarkB_conc, ← ht]
    exact hm
  · exact Or.inr habs

#print axioms restrictConcIX_inside
#print axioms restrictIX_narrow
#print axioms restrictIX_narrowM

/-! ### The narrowing of the forward hand-off, read on the forgotten view -/

/-- The publication of a restricted forward run `R` with the exclusion, for a given restriction,
    read WITHOUT THE EXCLUSIONS (the hand-off may drop `E`, DESIGN A2): the exit edge `j → g` of
    `R` (base facts) is published as `j → g'` if `R` has the annotated exit edge
    `(j, mj, jex) → (g, gex)` and a demand edge `d` restricts it to `(g', gex')`. -/
def pubRXw (P : Program) (R : XObj → Prop)
    (restrict : PFact → Excl → XFact → DemandEdge → Option XFact)
    (dem : MethodId → DemandEdge → Prop) : Pub :=
  fun m j g g' => ∃ mj jex gex gex' d, R (.edge m j mj jex (P.exit m) ⟨g, gex⟩) ∧ dem m d ∧
    restrict j jex ⟨g, gex⟩ d = some ⟨g', gex'⟩

/-- THE PUBLICATION OF THE SPEC RESTRICTION `restrictIX`, read on the forgotten view (the
    forgotten image of the `restrictIX` pieces of the exit edges of `R`). -/
abbrev pubRX (P : Program) (R : XObj → Prop) (dem : MethodId → DemandEdge → Prop) : Pub :=
  pubRXw P R restrictIX dem

/-- THE HYPOTHESIS `hpubSub` FOR `pubRX`: a published piece has only pairs of its edge (base facts,
    exclusions dropped). -/
theorem pubRX_sub (P : Program) (R : XObj → Prop) (dem : MethodId → DemandEdge → Prop) :
    ∀ m j g g', pubRX P R dem m j g g' → ∀ l1 l2, den j g'.fact l1 l2 → den j g.fact l1 l2 :=
  fun _ _ _ _ ⟨_, _, _, _, _, _, _, hr⟩ l1 l2 hd => (restrictIX_sub_base hr).2 l1 l2 hd

#print axioms pubRX_sub

/-- X4, THE NARROWING OF THE FORWARD HAND-OFF. Every demand edge `d'` that `handF` gives for a
    restricted run `R` read on the forgotten view, with the publication `pubRX`, is
    `⟨g', some j⟩` for an annotated exit edge `(j, mj, jex) → gx` of `R` and a demand edge `d`
    that restricts it to `(g', gex')`: the premise `j` WITH ITS EXCLUSION `jex` lies inside `D-c`
    of `d`, and the piece `g'` WITH ITS EXCLUSION `gex'` lies inside `D-p` of `d` (except
    `RExcX`). The forgotten view drops `jex` and `gex'`: the base patterns `j` and `g'` can lie
    outside `D-c`, `D-p` only at the excluded first accessors (`XVec.v_inside_only_with_excl`). -/
theorem handF_narrowX {P : Program} {R : XObj → Prop} {dem : MethodId → DemandEdge → Prop}
    {m : MethodId} {d' : DemandEdge}
    (h : handF P (AnyTaintExCov.forgetX R) (pubRX P R dem) m d') :
    ∃ j mj jex gx g' gex' d p, R (.edge m j mj jex (P.exit m) gx) ∧ dem m d ∧
      d.dout = some p ∧ restrictIX j jex gx d = some ⟨g', gex'⟩ ∧ d' = ⟨g'.fact, some j⟩ ∧
      insideLocXB j jex d.din = true ∧
      (insideLocXB g'.fact gex' p = true ∨ RExcX gx p ⟨g', gex'⟩) := by
  obtain ⟨j, g, g'', _, _, _, ⟨mj, jex, gex, gex', d, hR, hdem, hres⟩, hd'⟩ := h
  obtain ⟨p, hdo, hin, hcon⟩ := restrictIX_narrow hres
  exact ⟨j, mj, jex, ⟨g, gex⟩, g'', gex', d, p, hR, hdem, hdo, hres, hd', hin, hcon⟩

/-- The narrowing for a restricted run with the exclusion (`DRX` with `restrictIX` and a
    mark-copying emission): the run has no `*` conclusion and every conclusion has a concrete mark
    (`AnyTaintExCov.concX_all`), so the only exception is the cell (a) of `RExcX` on a DEMAND-LAYER
    `[any]` piece. -/
theorem handF_narrowX_DRX {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Excl → Option (PFact × Excl)}
    {sat : PFact → Excl → PFact → Excl → Bool}
    {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hem : EmitCopiesMarkX emit) {m : MethodId} {d' : DemandEdge}
    (h : handF P (AnyTaintExCov.forgetX
        (DRX P taint counted L dem emit sat restrictIX recs sinks roots))
      (pubRX P (DRX P taint counted L dem emit sat restrictIX recs sinks roots) dem) m d') :
    ∃ j jex gx g' gex' d p, dem m d ∧ d.dout = some p ∧
      restrictIX j jex gx d = some ⟨g', gex'⟩ ∧ d' = ⟨g'.fact, some j⟩ ∧
      insideLocXB j jex d.din = true ∧
      (insideLocXB g'.fact gex' p = true ∨ (gx.af.demand = true ∧ RExcX gx p ⟨g', gex'⟩)) := by
  obtain ⟨j, mj, jex, gx, g', gex', d, p, hR, hdem, hdo, hres, hd', hin, hcon⟩ := handF_narrowX h
  refine ⟨j, jex, gx, g', gex', d, p, hdem, hdo, hres, hd', hin, ?_⟩
  obtain ⟨_, ⟨t, ht⟩, hns, _⟩ :=
    AnyTaintExCov.concX_all P taint counted L dem emit sat restrictIX recs sinks roots hem hR
  rcases hcon with hc | hc
  · exact Or.inl hc
  · refine Or.inr ⟨?_, hc⟩
    rcases hc with ⟨hk, hcar, _⟩ | ⟨⟨e, hk⟩, _⟩
    · unfold carriesB at hcar
      rw [hk, ht] at hcar
      cases hdm : gx.af.demand with
      | true => rfl
      | false => rw [hdm] at hcar; exact absurd hcar (fun h' => Bool.noConfusion h')
    · rw [hk] at hns
      exact absurd hns (fun h' => Bool.noConfusion h')

/-- X4, THE NARROWING OF THE FORWARD HAND-OFF, MARK-AWARE (F71): as `handF_narrowX`, with the
    marks: the premise lies inside `D-c` with its exclusion and its marks (`insideXB`), the piece
    lies inside `D-p` with its exclusion (except `RExcX`) and its marks (except an abstract
    conclusion mark). -/
theorem handF_narrowXM {P : Program} {R : XObj → Prop} {dem : MethodId → DemandEdge → Prop}
    {m : MethodId} {d' : DemandEdge}
    (h : handF P (AnyTaintExCov.forgetX R) (pubRX P R dem) m d') :
    ∃ j mj jex gx g' gex' d p, R (.edge m j mj jex (P.exit m) gx) ∧ dem m d ∧
      d.dout = some p ∧ restrictIX j jex gx d = some ⟨g', gex'⟩ ∧ d' = ⟨g'.fact, some j⟩ ∧
      insideXB j jex d.din = true ∧
      (insideLocXB g'.fact gex' p = true ∨ RExcX gx p ⟨g', gex'⟩) ∧
      (markSubB p.mark g'.fact.mark = true ∨ Invariant.AbsMark gx.af.fact.mark) := by
  obtain ⟨j, g, g'', _, _, _, ⟨mj, jex, gex, gex', d, hR, hdem, hres⟩, hd'⟩ := h
  obtain ⟨p, hdo, hin, hcon, hmk⟩ := restrictIX_narrowM hres
  exact ⟨j, mj, jex, ⟨g, gex⟩, g'', gex', d, p, hR, hdem, hdo, hres, hd', hin, hcon, hmk⟩

/-- The narrowing for a restricted run with the exclusion, MARK-AWARE (F71): every conclusion has a
    concrete mark (`AnyTaintExCov.concX_all`), so the abstract-mark exception does not occur; the
    premise and the piece lie inside `D-c` and `D-p` with their marks (`insideXB`), except the cell
    (a) of `RExcX` on a DEMAND-LAYER `[any]` piece, where the mark of the piece is still a mark of
    `D-p`. -/
theorem handF_narrowX_DRXM {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {emit : PFact → PFact → Excl → Option (PFact × Excl)}
    {sat : PFact → Excl → PFact → Excl → Bool}
    {recs : MethodId → PFact × Bool × Excl × XFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (hem : EmitCopiesMarkX emit) {m : MethodId} {d' : DemandEdge}
    (h : handF P (AnyTaintExCov.forgetX
        (DRX P taint counted L dem emit sat restrictIX recs sinks roots))
      (pubRX P (DRX P taint counted L dem emit sat restrictIX recs sinks roots) dem) m d') :
    ∃ j jex gx g' gex' d p, dem m d ∧ d.dout = some p ∧
      restrictIX j jex gx d = some ⟨g', gex'⟩ ∧ d' = ⟨g'.fact, some j⟩ ∧
      insideXB j jex d.din = true ∧
      (insideXB g'.fact gex' p = true ∨
        (gx.af.demand = true ∧ RExcX gx p ⟨g', gex'⟩ ∧ markSubB p.mark g'.fact.mark = true)) := by
  obtain ⟨j, mj, jex, gx, g', gex', d, p, hR, hdem, hdo, hres, hd', hin, hcon, hmk⟩ :=
    handF_narrowXM h
  refine ⟨j, jex, gx, g', gex', d, p, hdem, hdo, hres, hd', hin, ?_⟩
  obtain ⟨_, ⟨t, ht⟩, hns, _⟩ :=
    AnyTaintExCov.concX_all P taint counted L dem emit sat restrictIX recs sinks roots hem hR
  have hmk' : markSubB p.mark g'.fact.mark = true := by
    rcases hmk with hmk | hab
    · exact hmk
    · exact absurd ht (Invariant.AbsMark.not_conc hab t)
  rcases hcon with hc | hc
  · exact Or.inl (insideXB_intro hc hmk')
  · refine Or.inr ⟨?_, hc, hmk'⟩
    rcases hc with ⟨hk, hcar, _⟩ | ⟨⟨e, hk⟩, _⟩
    · unfold carriesB at hcar
      rw [hk, ht] at hcar
      cases hdm : gx.af.demand with
      | true => rfl
      | false => rw [hdm] at hcar; exact absurd hcar (fun h' => Bool.noConfusion h')
    · rw [hk] at hns
      exact absurd hns (fun h' => Bool.noConfusion h')

#print axioms handF_narrowX
#print axioms handF_narrowX_DRX
#print axioms handF_narrowXM
#print axioms handF_narrowX_DRXM

/-! ## 9. X5: vectors (`decide`) -/

namespace XVec

/-- The premise `1.$` (mark `1`) and the entry pattern `1.$`. -/
def j1 : PFact := ⟨1, [], .exact, .conc 1⟩
def dc1 : PFact := ⟨1, [], .exact, .star⟩
/-- A demand `[any]` conclusion `2.[any]` (mark `1`). -/
def gDem : XFact := ⟨⟨⟨2, [], .any, .conc 1⟩, true⟩, Excl.empty⟩
/-- An `[any-taint]/{4}` conclusion `2.[any-taint]/{4}` (mark `1`). -/
def gTaint : XFact := ⟨⟨⟨2, [], .any, .conc 1⟩, false⟩, .set [4]⟩
/-- A `$` conclusion. -/
def gExact : XFact := ⟨⟨⟨2, [], .exact, .conc 1⟩, false⟩, Excl.empty⟩
/-- Exit patterns at `2`: `$`, `[any]`, `*/{5}`. -/
def pE : PFact := ⟨2, [], .exact, .star⟩
def pA : PFact := ⟨2, [], .any, .star⟩
def pS : PFact := ⟨2, [], .star (.set [5]), .star⟩

/-- THE §6.4 EXAMPLE IN X FORM: a demand `[any]` conclusion against `D-p = $` gives `$`
    (`restrictIX`), `restrictX` keeps `[any]`; an `[any-taint]/{4}` conclusion against `$` gives
    `$` with no exclusion. -/
theorem v64_demand :
    restrictIX j1 Excl.empty gDem ⟨dc1, some pE⟩ =
      some ⟨⟨⟨2, [], .exact, .conc 1⟩, true⟩, Excl.empty⟩ ∧
    restrictX j1 Excl.empty gDem ⟨dc1, some pE⟩ = some gDem := by decide

theorem v64_taint :
    restrictIX j1 Excl.empty gTaint ⟨dc1, some pE⟩ =
      some ⟨⟨⟨2, [], .exact, .conc 1⟩, false⟩, Excl.empty⟩ ∧
    restrictX j1 Excl.empty gTaint ⟨dc1, some pE⟩ = some gTaint := by decide

/-- THE CELL `[any-taint]/E ∩ */E2 = [any-taint]/(E ∪ E2)`: `{4} ∪ {5}`; `restrictX` keeps `{4}`. -/
theorem v_taint_star :
    restrictIX j1 Excl.empty gTaint ⟨dc1, some pS⟩ =
      some ⟨⟨⟨2, [], .any, .conc 1⟩, false⟩, .set [4, 5]⟩ ∧
    restrictX j1 Excl.empty gTaint ⟨dc1, some pS⟩ = some gTaint := by decide

/-- The other cells at `D-p`: `[any-taint]/E ∩ [any] = [any-taint]/E`; `[any] ∩ [any] = [any]`;
    `[any] ∩ */E2 = [any]` (the exception (a)); `$` stays against every tail. -/
theorem v_at_rows :
    restrictIX j1 Excl.empty gTaint ⟨dc1, some pA⟩ = some gTaint ∧
    restrictIX j1 Excl.empty gDem ⟨dc1, some pA⟩ = some gDem ∧
    restrictIX j1 Excl.empty gDem ⟨dc1, some pS⟩ = some gDem ∧
    restrictIX j1 Excl.empty gExact ⟨dc1, some pE⟩ = some gExact ∧
    restrictIX j1 Excl.empty gExact ⟨dc1, some pA⟩ = some gExact ∧
    restrictIX j1 Excl.empty gExact ⟨dc1, some pS⟩ = some gExact := by decide

/-- THE CELL ABOVE A `*/E2` EXIT PATTERN (changed against `restrictConcX`): the conclusion
    `2.[any-taint]/{4}` above `D-p = 2.[7].*/{5}` gives the chain `2.[7].[any-taint]/{5}` (the
    intersection); `restrictX` gives `2.[7].[any-taint]/{}`. If the exclusion of the conclusion
    excludes the step (`{7}`), nothing. Against `2.[7].$`: `2.[7].$`. -/
theorem v_above_rows :
    restrictIX j1 Excl.empty gTaint ⟨dc1, some ⟨2, [7], .star (.set [5]), .star⟩⟩ =
      some ⟨⟨⟨2, [7], .any, .conc 1⟩, false⟩, .set [5]⟩ ∧
    restrictX j1 Excl.empty gTaint ⟨dc1, some ⟨2, [7], .star (.set [5]), .star⟩⟩ =
      some ⟨⟨⟨2, [7], .any, .conc 1⟩, false⟩, Excl.empty⟩ ∧
    restrictIX j1 Excl.empty ⟨⟨⟨2, [], .any, .conc 1⟩, false⟩, .set [7]⟩
      ⟨dc1, some ⟨2, [7], .star (.set [5]), .star⟩⟩ = none ∧
    restrictIX j1 Excl.empty gTaint ⟨dc1, some ⟨2, [7], .exact, .star⟩⟩ =
      some ⟨⟨⟨2, [7], .exact, .conc 1⟩, false⟩, Excl.empty⟩ ∧
    restrictIX j1 Excl.empty gDem ⟨dc1, some ⟨2, [7], .star (.set [5]), .star⟩⟩ =
      some ⟨⟨⟨2, [7], .any, .conc 1⟩, true⟩, Excl.empty⟩ ∧
    restrictIX j1 Excl.empty gExact ⟨dc1, some ⟨2, [7], .any, .star⟩⟩ = none := by decide

/-- The cells below `D-p`: the conclusion `2.[7].[any-taint]/{4}` below `D-p = 2.*/{5}` stays with
    its exclusion; below `2.*/{7}` nothing (the step is excluded); below `2.$` nothing. -/
theorem v_below_rows :
    restrictIX j1 Excl.empty ⟨⟨⟨2, [7], .any, .conc 1⟩, false⟩, .set [4]⟩ ⟨dc1, some pS⟩ =
      some ⟨⟨⟨2, [7], .any, .conc 1⟩, false⟩, .set [4]⟩ ∧
    restrictIX j1 Excl.empty ⟨⟨⟨2, [7], .any, .conc 1⟩, false⟩, .set [4]⟩
      ⟨dc1, some ⟨2, [], .star (.set [7]), .star⟩⟩ = none ∧
    restrictIX j1 Excl.empty ⟨⟨⟨2, [7], .any, .conc 1⟩, false⟩, .set [4]⟩ ⟨dc1, some pE⟩ =
      none := by decide

/-- A PREMISE THAT ONLY OVERLAPS `D-c`: `1.*/{}` against `D-c = 1.[5].$`. `restrictIX` gives
    nothing (the premise is not inside), `restrictX` gives a result (it overlaps). No `D-p`:
    nothing. -/
theorem v_overlap :
    insideLocXB ⟨1, [], .star Excl.empty, .conc 1⟩ Excl.empty ⟨1, [5], .exact, .star⟩ = false ∧
    restrictIX ⟨1, [], .star Excl.empty, .conc 1⟩ Excl.empty gTaint
      ⟨⟨1, [5], .exact, .star⟩, some pA⟩ = none ∧
    restrictX ⟨1, [], .star Excl.empty, .conc 1⟩ Excl.empty gTaint
      ⟨⟨1, [5], .exact, .star⟩, some pA⟩ = some gTaint ∧
    restrictIX j1 Excl.empty gTaint ⟨dc1, none⟩ = none := by decide

/-- A PREMISE INSIDE `D-c` ONLY WITH ITS EXCLUSION: `1.*/{}` with the premise exclusion `{4}` lies
    inside `D-c = 1.*/{4}` (`insideLocXB`), the base pattern `1.*/{}` does not (`insideLocB`). So
    the restriction gives a result, and the forgotten view (the hand-off drops the exclusion) has
    the base pattern `1.*/{}`, which covers the location `1.[4]` outside `D-c`. -/
theorem v_inside_only_with_excl :
    insideLocXB ⟨1, [], .star Excl.empty, .conc 1⟩ (.set [4]) ⟨1, [], .star (.set [4]), .star⟩ =
      true ∧
    insideLocB ⟨1, [], .star Excl.empty, .conc 1⟩ ⟨1, [], .star (.set [4]), .star⟩ = false ∧
    restrictIX ⟨1, [], .star Excl.empty, .conc 1⟩ (.set [4]) gTaint
      ⟨⟨1, [], .star (.set [4]), .star⟩, some pA⟩ = some gTaint := by decide

theorem v_inside_only_with_excl_loc :
    (⟨1, [], .star Excl.empty, .conc 1⟩ : PFact).coversLoc ⟨1, [4], 1⟩ ∧
    ¬ (⟨1, [], .star (.set [4]), .star⟩ : PFact).coversLoc ⟨1, [4], 1⟩ := by
  refine ⟨⟨rfl, [4], rfl, rfl⟩, ?_⟩
  intro ⟨_, σ, hp, ht⟩
  have hσ : σ = [4] := by
    have h' : [4] = [] ++ σ := hp
    rw [List.nil_append] at h'
    exact h'.symm
  rw [hσ] at ht
  exact Bool.noConfusion ht

/-- THE EXCEPTION (a) IS REAL: the demand `[any]` conclusion against `D-p = 2.*/{5}` stays
    `2.[any]`; the pair `1 → 2.[5]` is in the result, but not in `D-p`. -/
theorem inter_exc_any :
    restrictIX j1 Excl.empty gDem ⟨dc1, some pS⟩ = some gDem ∧
    denX j1 Excl.empty gDem.af.fact gDem.ex ⟨1, [], 1⟩ ⟨2, [5], 1⟩ ∧
    ¬ pS.coversLoc ⟨2, [5], 1⟩ := by
  refine ⟨by decide, ⟨rfl, rfl, rfl, rfl, trivial, [], [5], rfl, rfl, rfl, trivial, rfl, rfl⟩, ?_⟩
  intro ⟨_, σ, hp, ht⟩
  have hσ : σ = [5] := by
    have h' : [5] = [] ++ σ := hp
    rw [List.nil_append] at h'
    exact h'.symm
  rw [hσ] at ht
  exact Bool.noConfusion ht

/-- THE EXCEPTION (b) IS REAL: the `*` conclusion `2.*` (correlated, mark `*`) against
    `D-p = 2.[5].$` stays; the pair `1.[] → 2.[]` is in the result, but not in `D-p`. -/
theorem inter_exc_star :
    restrictIX ⟨1, [], .star Excl.empty, .star⟩ Excl.empty
        ⟨⟨⟨2, [], .star Excl.empty, .star⟩, false⟩, Excl.empty⟩
        ⟨⟨1, [], .star Excl.empty, .star⟩, some ⟨2, [5], .exact, .star⟩⟩ =
      some ⟨⟨⟨2, [], .star Excl.empty, .star⟩, false⟩, Excl.empty⟩ ∧
    denX ⟨1, [], .star Excl.empty, .star⟩ Excl.empty ⟨2, [], .star Excl.empty, .star⟩ Excl.empty
      ⟨1, [], 3⟩ ⟨2, [], 3⟩ ∧
    ¬ (⟨2, [5], .exact, .star⟩ : PFact).coversLoc ⟨2, [], 3⟩ := by
  refine ⟨by decide, ⟨rfl, rfl, trivial, rfl, trivial, [], [], rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩,
    ?_⟩
  intro ⟨_, σ, hp, _⟩
  have h' : ([] : List Acc) = [5] ++ σ := hp
  exact List.cons_ne_nil 5 σ h'.symm

/-- The OLD CELL above a `*/E2` exit pattern (`restrictConcX`: the chain `[any-taint]/{}`) is not
    the intersection: the pair `1 → 2.[7, 5]` is in its result, but `D-p = 2.[7].*/{5}` does not
    cover `2.[7, 5]`. The new cell `[any-taint]/{5}` does not have this pair. -/
theorem v_old_above_not_inter :
    denX j1 Excl.empty ⟨2, [7], .any, .conc 1⟩ Excl.empty ⟨1, [], 1⟩ ⟨2, [7, 5], 1⟩ ∧
    ¬ denX j1 Excl.empty ⟨2, [7], .any, .conc 1⟩ (.set [5]) ⟨1, [], 1⟩ ⟨2, [7, 5], 1⟩ ∧
    ¬ (⟨2, [7], .star (.set [5]), .star⟩ : PFact).coversLoc ⟨2, [7, 5], 1⟩ := by
  refine ⟨⟨rfl, rfl, rfl, rfl, trivial, [], [5], rfl, rfl, rfl, trivial, rfl, rfl⟩, ?_, ?_⟩
  · intro ⟨_, _, _, _, _, σ, τ, _, hp2, _, _, _, hex⟩
    have hτ : τ = [5] := by
      have h' : [7, 5] = [7] ++ τ := hp2
      exact (List.append_cancel_left (h'.symm.trans (rfl : [7, 5] = [7] ++ [5]))).trans rfl
    rw [hτ] at hex
    exact Bool.noConfusion hex
  · intro ⟨_, σ, hp, ht⟩
    have hσ : σ = [5] := by
      have h' : [7, 5] = [7] ++ σ := hp
      exact (List.append_cancel_left (h'.symm.trans (rfl : [7, 5] = [7] ++ [5]))).trans rfl
    rw [hσ] at ht
    exact Bool.noConfusion ht

/-! ### The mark tests (F71), in X form

  Bases: `x = 1`, `ret = 4`; the accessor `f = 4`; the marks `T = 1`, `U = 2`. -/

def mJ : PFact := ⟨1, [], .exact, .conc 1⟩
def mJU : PFact := ⟨1, [], .exact, .conc 2⟩
def mGx : XFact := ⟨⟨⟨4, [4], .exact, .conc 1⟩, false⟩, Excl.empty⟩
def mD : DemandEdge := ⟨⟨1, [], .exact, .conc 1⟩, some ⟨4, [4], .exact, .conc 2⟩⟩

/-- THE USER'S EXAMPLE IN X FORM: the edge `(x,.,$,T) → (ret,.f,$,T)` and the demand edge with
    `D-c = (x,.,$,T)`, `D-p = (ret,.f,$,U)`: `restrictIX` gives nothing, `restrictX` keeps the edge;
    with `D-p = (ret,.f,$,T)` the edge is kept. -/
theorem vM_user :
    restrictIX mJ Excl.empty mGx mD = none ∧ restrictX mJ Excl.empty mGx mD = some mGx ∧
    restrictIX mJ Excl.empty mGx ⟨mD.din, some ⟨4, [4], .exact, .conc 1⟩⟩ = some mGx := by
  decide

/-- A premise mark that `D-c` does not admit: `D-c = (x,.,$,U)` and the premise `(x,.,$,T)`. The
    premise lies inside `D-c` in its locations, not in its marks: nothing. -/
theorem vM_prem :
    insideLocXB mJ Excl.empty ⟨1, [], .exact, .conc 2⟩ = true ∧
    insideXB mJ Excl.empty ⟨1, [], .exact, .conc 2⟩ = false ∧
    restrictIX mJ Excl.empty mGx ⟨⟨1, [], .exact, .conc 2⟩, some ⟨4, [4], .exact, .conc 1⟩⟩ =
      none := by decide

/-- THE `*∖x` CELLS, entry side: `D-c = (x,.,$,*∖[T])`. A premise with the mark `T`: nothing; a
    premise with the mark `U`: kept. -/
theorem vM_inStarEx :
    restrictIX mJ Excl.empty mGx ⟨⟨1, [], .exact, .starEx [1]⟩, some ⟨4, [4], .exact, .star⟩⟩ =
      none ∧
    restrictIX mJU Excl.empty ⟨⟨⟨4, [4], .exact, .conc 2⟩, false⟩, Excl.empty⟩
      ⟨⟨1, [], .exact, .starEx [1]⟩, some ⟨4, [4], .exact, .star⟩⟩ =
      some ⟨⟨⟨4, [4], .exact, .conc 2⟩, false⟩, Excl.empty⟩ := by decide

/-- THE `*∖x` CELLS, exit side: an `[any-taint]/{4}` conclusion with the mark `T` against
    `D-p = (ret,.,$,*∖[T])`: nothing; the same conclusion with the mark `U`: the meet `$`. -/
theorem vM_outStarEx :
    restrictIX mJ Excl.empty ⟨⟨⟨4, [], .any, .conc 1⟩, false⟩, .set [4]⟩
      ⟨⟨1, [], .exact, .star⟩, some ⟨4, [], .exact, .starEx [1]⟩⟩ = none ∧
    restrictIX mJU Excl.empty ⟨⟨⟨4, [], .any, .conc 2⟩, false⟩, .set [4]⟩
      ⟨⟨1, [], .exact, .star⟩, some ⟨4, [], .exact, .starEx [1]⟩⟩ =
      some ⟨⟨⟨4, [], .exact, .conc 2⟩, false⟩, Excl.empty⟩ := by decide

/-- THE EMISSION VECTOR IN X FORM: the entry pattern `(x,.,$,*∖[T])`: an added fact with the mark
    `T` gives nothing (before F71: the premise `(x,.,$,T)`, `Handoff.RVec.vEmit_starEx_T_pre70`);
    an added fact with the mark `U` gives the premise `(x,.,$,U)` with no exclusion, inside the
    entry pattern with its mark. -/
theorem vM_emit :
    emitX ⟨1, [], .exact, .starEx [1]⟩ mJ Excl.empty = none ∧
    emitX ⟨1, [], .exact, .starEx [1]⟩ mJU Excl.empty = some (mJU, Excl.empty) ∧
    insideXB mJU Excl.empty ⟨1, [], .exact, .starEx [1]⟩ = true := by decide

/-- CEGAR (F71): the location form of the contract X2 (the premise inside `D-c` in its locations,
    the exit location in the locations of `D-p`) is FALSE for the mark-aware `restrictIX` (the
    user's example). -/
theorem restrictIX_contract_loc_false :
    ¬ (∀ (j : PFact) (jex : Excl) (g : XFact) (d : DemandEdge) (p : PFact) (l1 l2 : Loc),
        insideLocXB j jex d.din = true → denX j jex g.af.fact g.ex l1 l2 → d.dout = some p →
        p.coversLoc l2 →
        ∃ g', restrictIX j jex g d = some g' ∧ denX j jex g'.af.fact g'.ex l1 l2 ∧
          g'.af.demand = g.af.demand) := by
  intro h
  have hden : denX mJ Excl.empty mGx.af.fact mGx.ex ⟨1, [], 1⟩ ⟨4, [4], 1⟩ :=
    ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hp : (⟨4, [4], .exact, .conc 2⟩ : PFact).coversLoc ⟨4, [4], 1⟩ := ⟨rfl, [], rfl, rfl⟩
  have hin : insideLocXB mJ Excl.empty mD.din = true := by decide
  obtain ⟨g', hg', _, _⟩ := h mJ Excl.empty mGx mD _ _ _ hin hden rfl hp
  rw [vM_user.1] at hg'
  cases hg'

#print axioms vM_user
#print axioms vM_prem
#print axioms vM_inStarEx
#print axioms vM_outStarEx
#print axioms vM_emit
#print axioms restrictIX_contract_loc_false
#print axioms v_old_above_not_inter
#print axioms v64_demand
#print axioms v64_taint
#print axioms v_taint_star
#print axioms v_at_rows
#print axioms v_above_rows
#print axioms v_below_rows
#print axioms v_overlap
#print axioms v_inside_only_with_excl
#print axioms v_inside_only_with_excl_loc
#print axioms inter_exc_any
#print axioms inter_exc_star

end XVec

end ApSpec.HandoffX
