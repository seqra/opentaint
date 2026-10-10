/-
  ApSpec.AbsDefs — abstract marks in restricted runs (decision F72), the definitions and the
  small facts.

  Historical cleaner boundary: these closures and FlowMA use the pre-F75 spatial
  cleaner and F73 mode. BaseCleaner and ReviewBaseCleaner model the corrected
  selected-mark operation and base-model closures. General coverage, exactness
  and iteration must migrate separately; old definitions remain for comparison.

  The user's decision (2026-10-10): a restricted run (forward or backward) analyses with the
  abstract mark `*` where the demand has the mark `*`. It analyses with a concrete mark only where
  the demand has a concrete mark. The rules (ABS-DESIGN.md §1):
    R1 `normDem`, `handFA`, `demOfNA`: the two hand-offs change every demand mark `*∖X` to `*`
       (a larger demand).
    R2 `emitW`: for a `*` pattern the initial fact is the FLOW FORM of the pattern (`flowForm`):
       one initial fact for every added fact under the pattern (sharing). For a concrete pattern
       the initial fact is `emitM` (the part of the added fact inside the pattern, with the mark of
       the added fact). A `*` added fact under a concrete pattern gives nothing (the user: the
       added fact cannot satisfy the demand).
    R3 `satW`: a summary applies by `satI` (the premise lies inside the fact), or, for a `*`
       premise, also by `applicable` (the premise covers the fact).
    R4 `DRA`, `DBA`: the restricted closures with NO request rule (`reqStmt`, `reqSink`, `answer`,
       `reqUp`, `reqClean`).
    R5 the restriction is `Handoff.restrictI`: a flow form lies inside its own `*` pattern
       (`flowForm_inside`) and inside no concrete pattern (`flowForm_not_inside_conc`).

  The witnesses with MODES (§7): at each call that returns, an ABSTRACT call (a `*` pattern
  demands it, its inner flow is MARK-AGNOSTIC: `FlowMA`), a CONCRETE call (a pattern with a mark
  that is not `*` demands it, its inner flow is a moded flow again), or a RECORDED call. The input
  witness of a forward run is `FlowRRA` / `ReachRRA`, the output witness is `FlowRDNA` / `ReachRDNA`.
  The contracts are `CoversNA` and `BackwardContractNA`.

  Small facts (proved here):
    * `flowForm_covers`, `flowForm_insideLoc`, `flowForm_inside`, `flowForm_not_inside_conc`: the
      FLOW form has the locations of its pattern, it lies inside a `*` pattern, inside no concrete
      pattern;
    * `normDem_enlarges`, `handFA_of_handF`, `demOfNA_of_demOfN`: R1 only enlarges the demand;
    * `satW_markSub`, `satW_gate`, `satW_step`: a satisfied premise gives no request;
    * L6 `emitW_contract_star`, `emitW_contract_conc`, `emitW_contract`: the emission contract. For a
      `*` pattern it needs a pattern tail that is `$`, `[any]` or `*` with the Empty exclusion
      (`PatTailB`); `emitW_needs_patTail` shows that a `*/E` pattern with a non-empty `E` breaks it
      for an abstract added fact. The hand-off never gives such a pattern: a normal edge with a `*`
      conclusion and a crossable premise is crossable (`cross_of_star_concl`), and every normal
      backward edge with a `*` conclusion is crossed by its reversal (`crossB_of_star_concl`);
    * `DRA_sub_DR`, `DBA_sub_DB`, `DRA_no_req`, `DBA_no_req`: the closures without requests;
    * `flowMA_flowRR`, `flowRRA_flowRR`, `reachRRA_reachRR`, `flowMA_flowRDN`, `flowRDNA_flowRDN`,
      `reachRDNA_reachRDN`: a moded witness is a witness of `HandoffDefs` (the modes add only
      information).

  All proofs are constructive (`propext`, `Quot.sound` only).
-/
import ApSpec.HandoffRestrict

namespace ApSpec.Abs
open ApSpec ApSpec.Reverse ApSpec.Handoff

/-! ## 1. R1: the hand-off normalization -/

/-- The demand mark: `*∖X` becomes `*`. The other marks stay. -/
def markNorm : MarkA → MarkA
  | .star     => .star
  | .conc t   => .conc t
  | .starEx _ => .star

/-- A pattern with its mark normalized. -/
def normFact (f : PFact) : PFact := ⟨f.base, f.path, f.kind, markNorm f.mark⟩

/-- A demand edge with both marks normalized. -/
def normDem (d : DemandEdge) : DemandEdge := ⟨normFact d.din, d.dout.map normFact⟩

/-- R1. FORWARD TO BACKWARD: `Handoff.handF` with the normalized marks. -/
def handFA (P : Program) (R : Obj → Prop) (pub : Pub) (m : MethodId) (d : DemandEdge) : Prop :=
  ∃ d0, handF P R pub m d0 ∧ d = normDem d0

/-- R1. BACKWARD TO FORWARD: `Handoff.demOfN` with the normalized marks. -/
def demOfNA (Pb : Program) (R : Obj → Prop) (pub : Pub) (M : MethodId) (d : DemandEdge) : Prop :=
  ∃ d0, demOfN Pb R pub M d0 ∧ d = normDem d0

theorem markNorm_admits {m : MarkA} {x : Mark} (h : m.admits x) : (markNorm m).admits x := by
  cases m with
  | star => trivial
  | conc t => exact h
  | starEx _ => trivial

#print axioms markNorm_admits

theorem markNorm_not_starEx (m : MarkA) (x : List Mark) : markNorm m ≠ .starEx x := by
  cases m <;> intro h <;> cases h

#print axioms markNorm_not_starEx

/-- A concrete pattern does not change. -/
theorem normFact_conc {f : PFact} {t : Mark} (h : f.mark = .conc t) : normFact f = f := by
  obtain ⟨b, p, k, m⟩ := f
  cases h
  rfl

#print axioms normFact_conc

theorem normFact_mark_star {f : PFact} (h : f.mark = .star) : (normFact f).mark = .star := by
  show markNorm f.mark = .star
  rw [h]
  rfl

#print axioms normFact_mark_star

/-- A normalized pattern covers every location that the pattern covers. -/
theorem normFact_covers {f : PFact} {l : Loc} (h : f.covers l) : (normFact f).covers l :=
  ⟨h.1, h.2.1, markNorm_admits h.2.2⟩

#print axioms normFact_covers

theorem normFact_coversLoc {f : PFact} {l : Loc} : (normFact f).coversLoc l ↔ f.coversLoc l :=
  Iff.rfl

#print axioms normFact_coversLoc

theorem normDem_din {d : DemandEdge} {l : Loc} (h : d.din.covers l) : (normDem d).din.covers l :=
  normFact_covers h

#print axioms normDem_din

theorem normDem_dout {d : DemandEdge} {p : PFact} (h : d.dout = some p) :
    (normDem d).dout = some (normFact p) := by
  show d.dout.map normFact = some (normFact p)
  rw [h]
  rfl

#print axioms normDem_dout

theorem normDem_dout_none {d : DemandEdge} (h : d.dout = none) : (normDem d).dout = none := by
  show d.dout.map normFact = none
  rw [h]
  rfl

#print axioms normDem_dout_none

/-- R1 ONLY ENLARGES THE DEMAND: the normalized entry pattern covers every location (with its
    mark) of the entry pattern, and the normalized exit pattern every location of the exit
    pattern. -/
theorem normDem_enlarges (d : DemandEdge) :
    (∀ l, d.din.covers l → (normDem d).din.covers l) ∧
    (∀ p, d.dout = some p → ∃ p', (normDem d).dout = some p' ∧ ∀ l, p.covers l → p'.covers l) :=
  ⟨fun _ h => normDem_din h,
   fun p h => ⟨normFact p, normDem_dout h, fun _ hl => normFact_covers hl⟩⟩

#print axioms normDem_enlarges

theorem handFA_of_handF {P : Program} {R : Obj → Prop} {pub : Pub} {m : MethodId}
    {d0 : DemandEdge} (h : handF P R pub m d0) : handFA P R pub m (normDem d0) :=
  ⟨d0, h, rfl⟩

#print axioms handFA_of_handF

theorem demOfNA_of_demOfN {Pb : Program} {R : Obj → Prop} {pub : Pub} {m : MethodId}
    {d0 : DemandEdge} (h : demOfN Pb R pub m d0) : demOfNA Pb R pub m (normDem d0) :=
  ⟨d0, h, rfl⟩

#print axioms demOfNA_of_demOfN

/-! ## 2. R2: the flow form and the emission -/

/-- The tail of the FLOW form: a `*` tail stays, `[any]` becomes `*` with the Empty exclusion (the
    same locations; a `*` tail is legal for the mark `*`, W2), `$` stays. -/
def flowK : Kind → Kind
  | .star e => .star e
  | .any    => .star Excl.empty
  | .exact  => .exact

/-- THE FLOW FORM of a pattern: its locations, with the mark `*`. It is the weakest premise inside
    a `*` pattern. -/
def flowForm (d : PFact) : PFact := ⟨d.base, d.path, flowK d.kind, .star⟩

/-- R2. THE EMISSION OF F72. A `*` pattern: the flow form of the pattern, for every added fact that
    `emitM` serves (the common part is not empty). Another pattern: `emitM` (the part of the added
    fact inside the pattern, with the mark of the added fact). -/
def emitW (d a : PFact) : Option PFact :=
  match emitM d a with
  | none   => none
  | some j => if d.mark = .star then some (flowForm d) else some j

theorem flowK_tailI (k : Kind) (σ : List Acc) : tailI (flowK k) σ ↔ tailI k σ := by
  cases k with
  | star e => exact Iff.rfl
  | any => exact ⟨fun _ => trivial, fun _ => CoreAux.empty_admits σ⟩
  | exact => exact Iff.rfl

#print axioms flowK_tailI

theorem flowK_not_any (k : Kind) : (flowK k).isAny = false := by
  cases k <;> rfl

#print axioms flowK_not_any

theorem tailSubB_flowK (k : Kind) : tailSubB k (flowK k) = true := by
  cases k with
  | star e => exact subB_refl e
  | any => rfl
  | exact => rfl

#print axioms tailSubB_flowK

theorem flowForm_mark (d : PFact) : (flowForm d).mark = .star := rfl

#print axioms flowForm_mark

/-- The flow form covers exactly the locations of its pattern, with every mark. -/
theorem flowForm_covers {d : PFact} {l : Loc} : (flowForm d).covers l ↔ d.coversLoc l := by
  constructor
  · rintro ⟨hb, ⟨σ, hp, ht⟩, _⟩
    exact ⟨hb, σ, hp, (flowK_tailI d.kind σ).mp ht⟩
  · rintro ⟨hb, σ, hp, ht⟩
    exact ⟨hb, ⟨σ, hp, (flowK_tailI d.kind σ).mpr ht⟩, trivial⟩

#print axioms flowForm_covers

theorem flowForm_covers_of {d : PFact} {l : Loc} (h : d.covers l) : (flowForm d).covers l :=
  flowForm_covers.mpr (RCore.covers_coversLoc h)

#print axioms flowForm_covers_of

/-- The flow form lies inside its pattern, in its locations. -/
theorem flowForm_insideLoc (d : PFact) : insideLocB (flowForm d) d = true := by
  unfold insideLocB coversB flowForm
  dsimp only
  rw [Nat.beq_refl, RAux.dropPrefix_self']
  show (true && true && tailSubB d.kind (flowK d.kind)) = true
  rw [tailSubB_flowK]
  rfl

#print axioms flowForm_insideLoc

/-- R5. THE FLOW FORM LIES INSIDE ITS `*` PATTERN, in its locations and its marks. -/
theorem flowForm_inside {d : PFact} (h : d.mark = .star) : insideB (flowForm d) d = true := by
  refine insideB_intro (flowForm_insideLoc d) ?_
  rw [h]
  rfl

#print axioms flowForm_inside

/-- R5. A flow form lies inside NO concrete pattern (the mark `*` is not inside `T`). -/
theorem flowForm_not_inside_conc {d : PFact} {t : Mark} (h : d.mark = .conc t) :
    insideB (flowForm d) d = false := by
  unfold insideB
  rw [h]
  show (insideLocB (flowForm d) d && false) = false
  rw [Bool.and_false]

#print axioms flowForm_not_inside_conc

/-- `emitW` serves an added fact if and only if `emitM` serves it. -/
theorem emitW_eq_none {d a : PFact} : emitW d a = none ↔ emitM d a = none := by
  cases he : emitM d a with
  | none =>
    rw [emitW, he]
  | some j =>
    rw [emitW, he]
    dsimp only
    refine ⟨fun h => ?_, fun h => by cases h⟩
    cases hm : d.mark with
    | star => rw [hm, if_pos rfl] at h; cases h
    | conc t =>
      rw [hm, if_neg (fun h0 => MarkA.noConfusion h0)] at h; cases h
    | starEx x =>
      rw [hm, if_neg (fun h0 => MarkA.noConfusion h0)] at h; cases h

#print axioms emitW_eq_none

/-- A `*` pattern: the emitted fact is the flow form, and `emitM` serves the added fact. -/
theorem emitW_star {d a j : PFact} (hm : d.mark = .star) (h : emitW d a = some j) :
    j = flowForm d ∧ ∃ j0, emitM d a = some j0 := by
  cases he : emitM d a with
  | none =>
    rw [emitW, he] at h
    cases h
  | some j0 =>
    rw [emitW, he] at h
    dsimp only at h
    rw [if_pos hm] at h
    exact ⟨(Option.some.inj h).symm, j0, rfl⟩

#print axioms emitW_star

/-- A pattern whose mark is not `*`: `emitW` is `emitM`. -/
theorem emitW_nonstar {d a : PFact} (hm : d.mark ≠ .star) : emitW d a = emitM d a := by
  cases he : emitM d a with
  | none => rw [emitW, he]
  | some j =>
    rw [emitW, he]
    dsimp only
    rw [if_neg hm]

#print axioms emitW_nonstar

/-- A `*` pattern emits its flow form when `emitM` serves the added fact. -/
theorem emitW_of_emitM_star {d a j0 : PFact} (hm : d.mark = .star) (he : emitM d a = some j0) :
    emitW d a = some (flowForm d) := by
  rw [emitW, he]
  dsimp only
  rw [if_pos hm]

#print axioms emitW_of_emitM_star

/-- Every emitted premise lies inside its pattern, in its locations. -/
theorem emitW_insideLoc {d a j : PFact} (h : emitW d a = some j) : insideLocB j d = true := by
  cases hm : d.mark with
  | star =>
    obtain ⟨rfl, _⟩ := emitW_star hm h
    exact flowForm_insideLoc d
  | conc t =>
    rw [emitW_nonstar (by rw [hm]; exact fun h0 => MarkA.noConfusion h0)] at h
    exact emitM_inside h
  | starEx x =>
    rw [emitW_nonstar (by rw [hm]; exact fun h0 => MarkA.noConfusion h0)] at h
    exact emitM_inside h

#print axioms emitW_insideLoc

/-- A `*` pattern: the emitted premise lies inside the pattern, in its locations and marks. -/
theorem emitW_insideB_star {d a j : PFact} (hm : d.mark = .star) (h : emitW d a = some j) :
    insideB j d = true := by
  obtain ⟨rfl, _⟩ := emitW_star hm h
  exact flowForm_inside hm

#print axioms emitW_insideB_star

/-- Another pattern and a concrete added fact: the emitted premise lies inside the pattern with
    its marks, and it has the mark of the added fact. -/
theorem emitW_insideB_conc {d a j : PFact} {t : Mark} (hm : d.mark ≠ .star) (ha : a.mark = .conc t)
    (h : emitW d a = some j) : insideB j d = true ∧ j.mark = a.mark := by
  rw [emitW_nonstar hm] at h
  exact emitM_insideB h ha

#print axioms emitW_insideB_conc

/-- The mark of an emitted premise: `*` for a `*` pattern, the mark of the added fact otherwise. -/
theorem emitW_mark {d a j : PFact} (h : emitW d a = some j) :
    (d.mark = .star ∧ j.mark = .star) ∨ (d.mark ≠ .star ∧ j.mark = a.mark) := by
  cases hm : d.mark with
  | star =>
    obtain ⟨rfl, _⟩ := emitW_star hm h
    exact Or.inl ⟨rfl, rfl⟩
  | conc t =>
    have hne : d.mark ≠ .star := by rw [hm]; exact fun h0 => MarkA.noConfusion h0
    rw [emitW_nonstar hne] at h
    exact Or.inr ⟨fun h0 => MarkA.noConfusion h0, RCore.emitM_mark h⟩
  | starEx x =>
    have hne : d.mark ≠ .star := by rw [hm]; exact fun h0 => MarkA.noConfusion h0
    rw [emitW_nonstar hne] at h
    exact Or.inr ⟨fun h0 => MarkA.noConfusion h0, RCore.emitM_mark h⟩

#print axioms emitW_mark

/-- The user's decision on the cell `*` added fact, concrete pattern: nothing is emitted. -/
theorem emitW_conc_star {d a : PFact} {t : Mark} (hm : d.mark = .conc t) (ha : a.mark = .star) :
    emitW d a = none := by
  rw [emitW_eq_none]
  unfold emitM
  rw [hm, ha]
  show (if (Nat.beq d.base a.base && false) = true then _ else none) = none
  rw [Bool.and_false, if_neg Bool.false_ne_true]

#print axioms emitW_conc_star

/-! ## 3. R3: the satisfaction -/

/-- The mark `*` (a FLOW premise). -/
def isStarB : MarkA → Bool
  | .star => true
  | _     => false

/-- R3. THE SATISFACTION OF F72: the premise lies inside the fact (`satI`), or the premise is a
    FLOW premise (the mark `*`) that covers the fact (`applicable`, as run 1 and the records). -/
def satW (j a : PFact) : Bool := satI j a || (isStarB j.mark && applicable j a)

theorem isStarB_iff {m : MarkA} : isStarB m = true ↔ m = .star := by
  cases m with
  | star => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | conc t => exact ⟨fun h => Bool.noConfusion h, fun h => MarkA.noConfusion h⟩
  | starEx x => exact ⟨fun h => Bool.noConfusion h, fun h => MarkA.noConfusion h⟩

#print axioms isStarB_iff

theorem satW_of_satI {j a : PFact} (h : satI j a = true) : satW j a = true := by
  unfold satW
  rw [h]
  rfl

#print axioms satW_of_satI

theorem satW_of_applicable {j a : PFact} (hj : j.mark = .star) (h : applicable j a = true) :
    satW j a = true := by
  unfold satW
  rw [hj, h]
  cases satI j a <;> rfl

#print axioms satW_of_applicable

theorem satW_cases {j a : PFact} (h : satW j a = true) :
    satI j a = true ∨ (j.mark = .star ∧ applicable j a = true) := by
  unfold satW at h
  rw [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨isStarB_iff.mp h1, h2⟩

#print axioms satW_cases

/-- A satisfied premise admits the mark of the fact. -/
theorem satW_markSub {j a : PFact} (h : satW j a = true) : markSubB j.mark a.mark = true := by
  rcases satW_cases h with h | ⟨_, h⟩
  · exact RCore.satI_contract.1 j a h
  · exact RCore.applicable_markSub h

#print axioms satW_markSub

/-- A SATISFIED PREMISE GIVES NO REQUEST: the mark gate of its mark against the fact mark is not a
    request. -/
theorem satW_gate {j a : PFact} (h : satW j a = true) (t : Mark) :
    markGate j.mark a.mark ≠ .req t := by
  have hm := satW_markSub h
  intro hg
  cases hj : j.mark with
  | star => rw [hj] at hg; exact Gate.noConfusion hg
  | starEx _ => rw [hj] at hg; exact Gate.noConfusion hg
  | conc u =>
    rw [hj] at hm hg
    cases ha : a.mark with
    | star => rw [ha] at hm; exact Bool.noConfusion hm
    | starEx _ => rw [ha] at hm; exact Bool.noConfusion hm
    | conc u' =>
      rw [ha] at hg
      have hg' : (if Nat.beq u u' = true then Gate.ok else Gate.no) = Gate.req t := hg
      cases hq : Nat.beq u u' with
      | true => rw [hq, if_pos rfl] at hg'; exact Gate.noConfusion hg'
      | false => rw [hq, if_neg Bool.false_ne_true] at hg'; exact Gate.noConfusion hg'

#print axioms satW_gate

/-- The application of a summary whose premise the fact satisfies covers the composed pair (no
    request). -/
theorem satW_step {i j : PFact} {a g : AFact} {l0 l1 l2 : Loc}
    (hs : satW j a.fact = true) (hda : den i a.fact l0 l1) (hdg : den j g.fact l1 l2) :
    ∃ r, r ∈ (applySummary a j g).facts ∧ den i r.fact l0 l2 := by
  rcases applySummary_sound hda hdg with h | ⟨_, hq⟩
  · exact h
  · exfalso
    have hreq : (applySummary a j g).reqs = (applyEdge a j g.fact).reqs := rfl
    have h0 : (applyEdge a j g.fact).reqs = [] :=
      CoreAux.reqs_of_gate (fun t => satW_gate hs t)
    rw [hreq, h0] at hq
    cases hq

#print axioms satW_step

/-! ## 4. L6: the emission contract -/

/-- The tails of a pattern that the flow form serves for every added fact: `$`, `[any]`, and `*`
    with the Empty exclusion. The hand-off gives only such patterns (`cross_of_star_concl`,
    `crossB_of_star_concl`: an edge with a `*` conclusion is a record, not a demand edge). -/
def PatTailB : Kind → Bool
  | .exact  => true
  | .any    => true
  | .star e => e.isEmptyB

/-- `satI` from the relative position: the fact is at the path of the premise. -/
theorem satI_of_drop0 {j a : PFact} (hb : Nat.beq a.base j.base = true)
    (hd : dropPrefix a.path j.path = some []) (ht : tailSubB a.kind j.kind = true)
    (hm : markSubB j.mark a.mark = true) : satI j a = true := by
  unfold satI coversB
  dsimp only
  rw [hb, hd, hm]
  show (true && true && tailSubB a.kind j.kind && true) = true
  rw [ht]
  rfl

#print axioms satI_of_drop0

/-- `satI` from the relative position: the fact is strictly above the premise. -/
theorem satI_of_drop1 {j a : PFact} {x : Acc} {r : List Acc} (hb : Nat.beq a.base j.base = true)
    (hd : dropPrefix a.path j.path = some (x :: r)) (ht : admitsTailB a.kind (x :: r) = true)
    (hm : markSubB j.mark a.mark = true) : satI j a = true := by
  unfold satI coversB
  dsimp only
  rw [hb, hd, hm]
  show (true && true && admitsTailB a.kind (x :: r) && true) = true
  rw [ht]
  rfl

#print axioms satI_of_drop1

/-- `applicable` from the relative position: the fact is at the path of the premise. -/
theorem applicable_of_drop0 {j a : PFact} (hb : Nat.beq j.base a.base = true)
    (hm : markSubB j.mark a.mark = true) (hd : dropPrefix j.path a.path = some [])
    (ht : tailSubB j.kind a.kind = true) (hk : j.kind.isAny = false) : applicable j a = true := by
  unfold applicable coversB
  rw [hb, hm, hd, hk]
  show (true && true && tailSubB j.kind a.kind && (!false || a.kind.isAny)) = true
  rw [ht]
  rfl

#print axioms applicable_of_drop0

/-- `applicable` from the relative position: the fact is strictly below the premise. -/
theorem applicable_of_drop1 {j a : PFact} {x : Acc} {r : List Acc}
    (hb : Nat.beq j.base a.base = true) (hm : markSubB j.mark a.mark = true)
    (hd : dropPrefix j.path a.path = some (x :: r)) (ht : admitsTailB j.kind (x :: r) = true)
    (hk : j.kind.isAny = false) : applicable j a = true := by
  unfold applicable coversB
  rw [hb, hm, hd, hk]
  show (true && true && admitsTailB j.kind (x :: r) && (!false || a.kind.isAny)) = true
  rw [ht]
  rfl

#print axioms applicable_of_drop1

/-- L6 FOR A `*` PATTERN. For a `*` pattern with a tail of `PatTailB` and an added fact (ANY mark:
    concrete, `*` or `*∖x`) that both cover the location `l`: the emission gives the flow form of
    the pattern, which covers `l` and which the added fact satisfies (`satW`). -/
theorem emitW_contract_star {d a : PFact} {l : Loc} (hm : d.mark = .star)
    (hk : PatTailB d.kind = true) (hd : d.covers l) (ha : a.covers l) :
    emitW d a = some (flowForm d) ∧ (flowForm d).covers l ∧ satW (flowForm d) a = true := by
  have hmm : markMatchB d.mark a.mark = true := by rw [hm]; rfl
  obtain ⟨j0, he⟩ := RCore.emitM_complete hmm ha (RCore.covers_coversLoc hd)
  refine ⟨emitW_of_emitM_star hm he, flowForm_covers_of hd, ?_⟩
  obtain ⟨hbd, ⟨σ, hpd, htd⟩, _⟩ := hd
  obtain ⟨hba, ⟨τ, hpa, hta⟩, _⟩ := ha
  have hb1 : Nat.beq a.base (flowForm d).base = true := by
    show Nat.beq a.base d.base = true
    rw [← hba, ← hbd]; exact Nat.beq_refl _
  have hb2 : Nat.beq (flowForm d).base a.base = true := by
    show Nat.beq d.base a.base = true
    rw [← hba, ← hbd]; exact Nat.beq_refl _
  have hms1 : markSubB (flowForm d).mark a.mark = true := rfl
  have hpath : d.path ++ σ = a.path ++ τ := by rw [← hpd, ← hpa]
  rcases CoreAux.relate_common hpath with ⟨r, _, hq, hσ⟩ | ⟨r, _, hP, hr, hτ⟩
  · -- the added fact is at or below the pattern
    cases r with
    | nil =>
      have hq' : a.path = d.path := by rw [hq, List.append_nil]
      cases hdk : d.kind with
      | exact =>
        -- the flow form is `$` at the path of `a`: it lies inside `a`
        apply satW_of_satI
        apply satI_of_drop0 hb1 (by show dropPrefix a.path d.path = some []; rw [hq']; exact RAux.dropPrefix_self' _) _ hms1
        show tailSubB a.kind (flowK d.kind) = true
        rw [hdk]
        cases a.kind <;> rfl
      | any =>
        -- the flow form is `*` with the Empty exclusion at the path of `a`: it covers `a`
        apply satW_of_applicable rfl
        apply applicable_of_drop0 hb2 hms1 (by show dropPrefix d.path a.path = some []; rw [hq']; exact RAux.dropPrefix_self' _)
        · show tailSubB (flowK d.kind) a.kind = true
          rw [hdk]
          exact RCore.tailSubB_starEmpty a.kind
        · show (flowK d.kind).isAny = false
          exact flowK_not_any _
      | star e =>
        rw [hdk] at hk
        have he0 : e = Excl.empty := by
          cases e with
          | univ => exact Bool.noConfusion hk
          | set xs => cases xs with
            | nil => rfl
            | cons _ _ => exact Bool.noConfusion hk
        apply satW_of_applicable rfl
        apply applicable_of_drop0 hb2 hms1 (by show dropPrefix d.path a.path = some []; rw [hq']; exact RAux.dropPrefix_self' _)
        · show tailSubB (flowK d.kind) a.kind = true
          rw [hdk, he0]
          exact RCore.tailSubB_starEmpty a.kind
        · show (flowK d.kind).isAny = false
          exact flowK_not_any _
    | cons x r' =>
      -- the added fact is strictly below the pattern: the flow form covers it
      have hadm : admitsTailB d.kind (x :: r') = true := by
        rw [hσ] at htd
        exact CoreAux.tailI_append_admits htd
      have hadm' : admitsTailB (flowK d.kind) (x :: r') = true := by
        cases hdk : d.kind with
        | exact => rw [hdk] at hadm; exact Bool.noConfusion hadm
        | any =>
          show Excl.empty.admits (x :: r') = true
          exact CoreAux.empty_admits _
        | star e => rw [hdk] at hadm; exact hadm
      apply satW_of_applicable rfl
      exact applicable_of_drop1 hb2 hms1 (CoreAux.dropPrefix_some.mpr hq) hadm' (flowK_not_any _)
  · -- the added fact is strictly above the pattern: the flow form lies inside it
    cases r with
    | nil => exact absurd rfl hr
    | cons x r' =>
      apply satW_of_satI
      apply satI_of_drop1 hb1 (CoreAux.dropPrefix_some.mpr hP) _ hms1
      rw [hτ] at hta
      exact CoreAux.tailI_append_admits hta

#print axioms emitW_contract_star

/-- L6 FOR ANOTHER PATTERN. For a pattern whose mark is not `*` and a CONCRETE added fact that both
    cover `l`: the emission is `emitM` (today's rule); it covers `l`, the added fact satisfies it, it
    has the mark of the added fact and it lies inside the pattern with its marks. -/
theorem emitW_contract_conc {d a : PFact} {l : Loc} {t : Mark} (hm : d.mark ≠ .star)
    (ha0 : a.mark = .conc t) (hd : d.covers l) (ha : a.covers l) :
    ∃ j, emitW d a = some j ∧ j.covers l ∧ satW j a = true ∧ j.mark = a.mark ∧
      insideB j d = true := by
  obtain ⟨j, he, hjc, hsat⟩ := RCore.emitM_contract_I d a l t ha0 hd ha
  refine ⟨j, by rw [emitW_nonstar hm]; exact he, hjc, satW_of_satI hsat, RCore.emitM_mark he,
    (emitM_insideB he ha0).1⟩

#print axioms emitW_contract_conc

/-- L6, THE EMISSION CONTRACT OF F72: for every pattern `d` and added fact `a` that both cover `l`
    (with its mark), the emission gives a premise `j` that covers `l` and that `a` satisfies; for a
    `*` pattern with a tail of `PatTailB` (every added fact), and for another pattern with a concrete
    added fact. -/
theorem emitW_contract {d a : PFact} {l : Loc}
    (hk : d.mark = .star → PatTailB d.kind = true)
    (hc : d.mark ≠ .star → ∃ t, a.mark = .conc t) (hd : d.covers l) (ha : a.covers l) :
    ∃ j, emitW d a = some j ∧ j.covers l ∧ satW j a = true := by
  cases hdm : d.mark with
  | star =>
    obtain ⟨h1, h2, h3⟩ := emitW_contract_star hdm (hk hdm) hd ha
    exact ⟨_, h1, h2, h3⟩
  | conc u =>
    have hne : d.mark ≠ .star := by rw [hdm]; exact fun h0 => MarkA.noConfusion h0
    obtain ⟨t, ht⟩ := hc hne
    obtain ⟨j, h1, h2, h3, _⟩ := emitW_contract_conc hne ht hd ha
    exact ⟨j, h1, h2, h3⟩
  | starEx x =>
    have hne : d.mark ≠ .star := by rw [hdm]; exact fun h0 => MarkA.noConfusion h0
    obtain ⟨t, ht⟩ := hc hne
    obtain ⟨j, h1, h2, h3, _⟩ := emitW_contract_conc hne ht hd ha
    exact ⟨j, h1, h2, h3⟩

#print axioms emitW_contract

/-- The vectors of the CEGAR of L6: a `*/{2}` pattern and an abstract `*/{1}` added fact at the same
    path, with the common location `(3,.4.5,7)`. -/
def vD : PFact := ⟨3, [4], .star (.set [2]), .star⟩
def vA : PFact := ⟨3, [4], .star (.set [1]), .star⟩
def vL : Loc := ⟨3, [4, 5], 7⟩

/-- The flow form of `vD` is emitted, but `vA` does not satisfy it: the flow form is not inside
    `vA` (it admits `.1`), and it does not cover `vA` (`vA` admits `.2`). `emitM` would give the
    intersection `*/{1,2}`, which lies inside `vA`. -/
theorem vec_emitW_starE : emitW vD vA = some (flowForm vD) ∧ satW (flowForm vD) vA = false ∧
    emitM vD vA = some ⟨3, [4], .star (.set [1, 2]), .star⟩ ∧
    satW ⟨3, [4], .star (.set [1, 2]), .star⟩ vA = true := by
  decide

#print axioms vec_emitW_starE

/-- THE `PatTailB` CONDITION OF L6 IS NECESSARY: without it the contract is false for a `*` pattern
    and an abstract added fact. -/
theorem emitW_needs_patTail :
    ¬ (∀ d a l, d.mark = .star → d.covers l → a.covers l →
        ∃ j, emitW d a = some j ∧ j.covers l ∧ satW j a = true) := by
  intro h
  have hd : vD.covers vL := ⟨rfl, ⟨[5], rfl, rfl⟩, trivial⟩
  have ha : vA.covers vL := ⟨rfl, ⟨[5], rfl, rfl⟩, trivial⟩
  obtain ⟨j, hj, _, hs⟩ := h vD vA vL rfl hd ha
  rw [vec_emitW_starE.1] at hj
  cases hj
  rw [vec_emitW_starE.2.1] at hs
  exact Bool.noConfusion hs

#print axioms emitW_needs_patTail

/-! ## 5. Why the hand-off gives no `*/E` pattern: a `*` conclusion is a record -/

/-- A NORMAL edge with a `*`-tail conclusion with an abstract mark and a crossable premise is
    crossable (`Cross`). So `handF` never hands it off: every backward entry pattern has the tail
    `$` or `[any]` (a conclusion with a concrete mark has no `*` tail, W2). -/
theorem cross_of_star_concl {j : PFact} {g : AFact} {e : Excl} (hd : g.demand = false)
    (hj : CrossK j.kind) (hk : g.fact.kind = .star e)
    (hm : g.fact.mark = .star ∨ ∃ x, g.fact.mark = .starEx x) : Cross j g := by
  refine ⟨hd, hj, Or.inl hm, ?_⟩
  show CrossK (revKinds j.kind g.fact.kind).1
  rw [hk]
  cases hjk : j.kind with
  | star ei => exact (rfl : Excl.empty = Excl.empty)
  | any => rw [hjk] at hj; exact hj.elim
  | exact => trivial

#print axioms cross_of_star_concl

/-- EVERY NORMAL backward edge with a `*`-tail conclusion with an abstract mark is crossed by its
    reversal (`CrossB`), for every premise. So `demOfN` never hands it off: every forward entry
    pattern of a non-zero backward premise has the tail `$` or `[any]`. -/
theorem crossB_of_star_concl {jb : PFact} {gb : AFact} {e : Excl} (hd : gb.demand = false)
    (hk : gb.fact.kind = .star e)
    (hm : gb.fact.mark = .star ∨ ∃ x, gb.fact.mark = .starEx x) : CrossB jb gb := by
  refine ⟨hd, rfl, ?_, ?_, ?_⟩
  · show CrossK (revKinds jb.kind gb.fact.kind).1
    rw [hk]
    cases jb.kind with
    | star ei => exact (rfl : Excl.empty = Excl.empty)
    | any => exact (rfl : Excl.empty = Excl.empty)
    | exact => trivial
  · -- the reversed conclusion has the mark `*` or `*∖x`
    apply Or.inl
    obtain ⟨⟨gbb, gbp, gbk, gbm⟩, gbd⟩ := gb
    dsimp only at hm
    rcases hm with h | ⟨x, h⟩
    · subst h; exact Or.inl rfl
    · subst h; exact Or.inr ⟨x, rfl⟩
  · show CrossK (revKinds (revKinds jb.kind gb.fact.kind).1 (revKinds jb.kind gb.fact.kind).2).1
    rw [hk]
    cases jb.kind with
    | star ei => exact (rfl : Excl.empty = Excl.empty)
    | any => exact (rfl : Excl.empty = Excl.empty)
    | exact => trivial

#print axioms crossB_of_star_concl

/-! ## 6. R4: the restricted closures with no request rule -/

section ClosureRA
variable (P : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- THE FORWARD RESTRICTED RUN OF F72: the rules of `Restricted.DR` with NO request rule. On a `*`
    fact an operation that needs a concrete mark gives nothing: the mark gate of a micro edge with a
    concrete premise mark, the sink check, the cleaned part of a cleaner (it continues as `*∖{t}`,
    with no request). -/
inductive DRA : Obj → Prop where
  | root {M} : M ∈ roots → DRA (.init M zeroFact)
  | start {M i} : DRA (.init M i) → DRA (.edge M i (P.entry M) (startFact i))
  | step {M i n f n' s f'} :
      DRA (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transfer counted L s f).facts → DRA (.edge M i n' f')
  | pass {M i n f n' c} :
      DRA (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.fact.base c.touched = false → DRA (.edge M i n' f)
  | added {M i n f n' c e a} :
      DRA (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      DRA (.added c.callee a.fact)
  | initR {m a d j} :
      DRA (.added m a) → demand m d → emit d.din a = some j → DRA (.init m j)
  | ret {M i n f n' c e1 a j g d g' r e2 r'} :
      DRA (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DRA (.init c.callee j) →
      DRA (.edge c.callee j (P.exit c.callee) g) →
      demand c.callee d → restrict j g d = some g' →
      sat j a.fact = true →
      r ∈ (applySummary a j g').facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DRA (.edge M i n' (limitF counted L r'))
  | retRec {M i n f n' c e1 a j g r e2 r'} :
      DRA (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      recs c.callee (j, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DRA (.edge M i n' (limitF counted L r'))
  | vuln {M i n f s} :
      DRA (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      DRA (.vuln M n s f.demand)
  | clean {M i n f n' cl f'} :
      DRA (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanRes cl f).facts → DRA (.edge M i n' f')
  | filt {M i n f n' b may} :
      DRA (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.fact.base = b → may f.fact.path = true) → DRA (.edge M i n' f)

/-- Every object of `DRA` is an object of `DR` with the same parameters (the rules are a part of the
    rules of `DR`). -/
theorem DRA_sub_DR {o : Obj} (h : DRA P counted L demand emit sat restrict recs sinks roots o) :
    DR P counted L demand emit sat restrict recs sinks roots o := by
  induction h with
  | root hM => exact DR.root hM
  | start _ ih => exact DR.start ih
  | step _ he hf ih => exact DR.step ih he hf
  | pass _ he hm ih => exact DR.pass ih he hm
  | added _ he he1 ha ih => exact DR.added ih he he1 ha
  | initR _ hd he ih => exact DR.initR ih hd he
  | ret _ he he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    exact DR.ret ihf he he1 ha ihj ihg hd hres hsat hr he2 hr'
  | retRec _ he he1 ha hrec hsat hr he2 hr' ih =>
    exact DR.retRec ih he he1 ha hrec hsat hr he2 hr'
  | vuln _ hs hc ih => exact DR.vuln ih hs hc
  | clean _ he hf ih => exact DR.clean ih he hf
  | filt _ he hl ih => exact DR.filt ih he hl

/-- `DRA` has no request. -/
theorem DRA_no_req {M : MethodId} {i : PFact} {t : Mark} :
    ¬ DRA P counted L demand emit sat restrict recs sinks roots (.req M i t) := by
  intro h
  cases h

end ClosureRA

#print axioms DRA_sub_DR
#print axioms DRA_no_req

section ClosureBA
variable (Pb : Program) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Option PFact)
  (sat : PFact → PFact → Bool)
  (restrict : PFact → AFact → DemandEdge → Option AFact)
  (recs : MethodId → (PFact × AFact) → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)
  (seeds : List (MethodId × Node × PFact))
  (zbind : Bool)

/-- THE BACKWARD RESTRICTED RUN OF F72: the rules of `Backward.DB` with NO request rule. -/
inductive DBA : Obj → Prop where
  | root {M} : M ∈ roots → DBA (.init M zeroFact)
  | start {M i} : DBA (.init M i) → DBA (.edge M i (Pb.entry M) (startFact i))
  | step {M i n f n' s f'} :
      DBA (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ Pb.edges →
      f' ∈ (transfer counted L s f).facts → DBA (.edge M i n' f')
  | pass {M i n f n' c} :
      DBA (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      memB f.fact.base c.touched = false → DBA (.edge M i n' f)
  | added {M i n f n' c e a} :
      DBA (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e ∈ c.toCallee → a ∈ (applyEdge f e.1 e.2).facts →
      DBA (.added c.callee a.fact)
  | initR {m a d j} :
      DBA (.added m a) → demand m d → emit d.din a = some j → DBA (.init m j)
  | ret {M i n f n' c e1 a j g d g' r e2 r'} :
      DBA (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      DBA (.init c.callee j) →
      DBA (.edge c.callee j (Pb.exit c.callee) g) →
      demand c.callee d → restrict j g d = some g' →
      sat j a.fact = true →
      r ∈ (applySummary a j g').facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DBA (.edge M i n' (limitF counted L r'))
  | retRec {M i n f n' c e1 a j g r e2 r'} :
      DBA (.edge M i n f) → (M, n, Instr.call c, n') ∈ Pb.edges →
      e1 ∈ c.toCallee → a ∈ (applyEdge f e1.1 e1.2).facts →
      recs c.callee (j, g) → (sat j a.fact = true ∨ applicable j a.fact = true) →
      r ∈ (applySummary a j g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DBA (.edge M i n' (limitF counted L r'))
  | vuln {M i n f s} :
      DBA (.edge M i n f) → (M, n, s) ∈ sinks → check i f s = .triggered →
      DBA (.vuln M n s f.demand)
  | clean {M i n f n' cl f'} :
      DBA (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ Pb.edges →
      f' ∈ (cleanRes cl f).facts → DBA (.edge M i n' f')
  | filt {M i n f n' b may} :
      DBA (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ Pb.edges →
      (f.fact.base = b → may f.fact.path = true) → DBA (.edge M i n' f)
  | zpass {M n n' c} :
      DBA (.edge M zeroFact n Backward.zeroAF) → (M, n, Instr.call c, n') ∈ Pb.edges →
      DBA (.edge M zeroFact n' Backward.zeroAF)
  | zin {M n n' c} : zbind = true →
      DBA (.edge M zeroFact n Backward.zeroAF) → (M, n, Instr.call c, n') ∈ Pb.edges →
      DBA (.init c.callee zeroFact)
  | seed {M n s} : (M, n, s) ∈ seeds → DBA (.edge M zeroFact n Backward.zeroAF) →
      DBA (.edge M zeroFact n (limitF counted L ⟨s, false⟩))
  | zret {M n n' c g r e2 r'} : zbind = true →
      DBA (.edge M zeroFact n Backward.zeroAF) → (M, n, Instr.call c, n') ∈ Pb.edges →
      DBA (.edge c.callee zeroFact (Pb.exit c.callee) g) →
      r ∈ (applySummary Backward.zeroAF zeroFact g).facts →
      e2 ∈ c.fromCallee → r' ∈ (applyEdge r e2.1 e2.2).facts →
      DBA (.edge M zeroFact n' (limitF counted L r'))

/-- Every object of `DBA` is an object of `DB` with the same parameters. -/
theorem DBA_sub_DB {o : Obj}
    (h : DBA Pb counted L demand emit sat restrict recs sinks roots seeds zbind o) :
    Backward.DB Pb counted L demand emit sat restrict recs sinks roots seeds zbind o := by
  induction h with
  | root hM => exact Backward.DB.root hM
  | start _ ih => exact Backward.DB.start ih
  | step _ he hf ih => exact Backward.DB.step ih he hf
  | pass _ he hm ih => exact Backward.DB.pass ih he hm
  | added _ he he1 ha ih => exact Backward.DB.added ih he he1 ha
  | initR _ hd he ih => exact Backward.DB.initR ih hd he
  | ret _ he he1 ha _ _ hd hres hsat hr he2 hr' ihf ihj ihg =>
    exact Backward.DB.ret ihf he he1 ha ihj ihg hd hres hsat hr he2 hr'
  | retRec _ he he1 ha hrec hsat hr he2 hr' ih =>
    exact Backward.DB.retRec ih he he1 ha hrec hsat hr he2 hr'
  | vuln _ hs hc ih => exact Backward.DB.vuln ih hs hc
  | clean _ he hf ih => exact Backward.DB.clean ih he hf
  | filt _ he hl ih => exact Backward.DB.filt ih he hl
  | zpass _ he ih => exact Backward.DB.zpass ih he
  | zin hz _ he ih => exact Backward.DB.zin hz ih he
  | seed hs _ ih => exact Backward.DB.seed hs ih
  | zret hz _ he _ hr he2 hr' ih ihg => exact Backward.DB.zret hz ih he ihg hr he2 hr'

/-- `DBA` has no request. -/
theorem DBA_no_req {M : MethodId} {i : PFact} {t : Mark} :
    ¬ DBA Pb counted L demand emit sat restrict recs sinks roots seeds zbind (.req M i t) := by
  intro h
  cases h

end ClosureBA

#print axioms DBA_sub_DB
#print axioms DBA_no_req

/-- The forward run of F72: `DRA` with `emitW`, `satW` and the restriction `restrictI`. -/
abbrev DRW (P : Program) (counted : Acc → Bool) (L : Nat) (dem : MethodId → DemandEdge → Prop)
    (rc : Recs) (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Obj → Prop :=
  DRA P counted L dem emitW satW restrictI rc sinks roots

/-- The backward run of F72: `DBA` on the reversed program with `emitW`, `satW`, `restrictI`, no
    forward sink, the zero binding of the user's design. -/
abbrev DBW (Pb : Program) (counted : Acc → Bool) (L : Nat) (dem : MethodId → DemandEdge → Prop)
    (recs : Recs) (roots : List MethodId) (seeds : List (MethodId × Node × PFact)) :
    Obj → Prop :=
  DBA Pb counted L dem emitW satW restrictI recs [] roots seeds true

/-! ## 7. Mark-agnostic flows and the witnesses with modes -/

/-- A statement step that needs no concrete mark: the location is not touched, or a micro edge
    with the premise mark `*` relates the two locations. -/
def StepMA (s : Stmt) (l l' : Loc) : Prop :=
  (memB l.base s.touched = false ∧ l' = l) ∨ (∃ e, e ∈ s.edges ∧ e.1.mark = .star ∧ den e.1 e.2 l l')

/-- A cleaner step needs no concrete mark when it is spatially disjoint from the
    actual propagated fact, cleans all marks, or cleans another mark. -/
def cleanMAB (cl : Cleaner) (f : AFact) (l : Loc) : Bool :=
  match cleanPos cl f.fact with
  | .disjoint => true
  | _ => match cl.mark with
    | none => true
    | some t => !(Nat.beq l.mark t)

theorem stepMA_step {s : Stmt} {l l' : Loc} (h : StepMA s l l') : s.step l l' := by
  rcases h with h | ⟨e, he, _, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, he, hd⟩

#print axioms stepMA_step

/-- Call justification fixes the actual binding input, initial premise, exit
    fact, published/restricted fact and concrete pair. -/
abbrev AbstractOK := MethodId → AFact → PFact → AFact → AFact → Loc → Loc → Prop

/-- An executable certificate for an abstract flow. Its initial premise and every
    intermediate fact are fixed in the indices. Constructors use actual AP
    operations, including field limits; denotation certificates select the same
    concrete pair throughout. No fact may be replaced just to pass a cleaner. -/
inductive FlowMA (P : Program) (counted : Acc → Bool) (L : Nat) (ok : AbstractOK) (rc : Recs) :
    MethodId → PFact → Loc → Node → AFact → Loc → Type where
  | start (M : MethodId) (j : PFact) (l0 : Loc) :
      j.mark = .star → j.covers l0 →
      FlowMA P counted L ok rc M j l0 (P.entry M) (startFact j) l0
  | step {M j l0 n f l n' f' l' s} :
      FlowMA P counted L ok rc M j l0 n f l → (M, n, Instr.stmt s, n') ∈ P.edges →
      StepMA s l l' → f' ∈ (transfer counted L s f).facts → den j f'.fact l0 l' →
      FlowMA P counted L ok rc M j l0 n' f' l'
  | pass {M j l0 n f l n' c} :
      FlowMA P counted L ok rc M j l0 n f l → (M, n, Instr.call c, n') ∈ P.edges →
      memB l.base c.touched = false → memB f.fact.base c.touched = false →
      FlowMA P counted L ok rc M j l0 n' f l
  | call {M j l0 n f l n' c e1 a jc g g' r e2 r' l1 l2 l3} :
      FlowMA P counted L ok rc M j l0 n f l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 → a ∈ (applyEdge f e1.1 e1.2).facts →
      den j a.fact l0 l1 →
      FlowMA P counted L ok rc c.callee jc l1 (P.exit c.callee) g l2 →
      ok c.callee a jc g g' l1 l2 → satW jc a.fact = true → den jc g'.fact l1 l2 →
      r ∈ (applySummary a jc g').facts → den j r.fact l0 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 → r' ∈ (applyEdge r e2.1 e2.2).facts →
      den j r'.fact l0 l3 → den j (limitF counted L r').fact l0 l3 →
      FlowMA P counted L ok rc M j l0 n' (limitF counted L r') l3
  | rcall {M j l0 n f l n' c e1 a jc g r e2 r' l1 l2 l3} :
      FlowMA P counted L ok rc M j l0 n f l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 → a ∈ (applyEdge f e1.1 e1.2).facts →
      den j a.fact l0 l1 →
      rc c.callee (jc, g) → Cross jc g → jc.mark = .star → jc.covers l1 → den jc g.fact l1 l2 →
      (satW jc a.fact = true ∨ applicable jc a.fact = true) →
      r ∈ (applySummary a jc g).facts → den j r.fact l0 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 → r' ∈ (applyEdge r e2.1 e2.2).facts →
      den j r'.fact l0 l3 → den j (limitF counted L r').fact l0 l3 →
      FlowMA P counted L ok rc M j l0 n' (limitF counted L r') l3
  | clean {M j l0 n f l n' cl f'} :
      FlowMA P counted L ok rc M j l0 n f l → (M, n, Instr.clean cl, n') ∈ P.edges →
      cl.cleansB l = false → cleanMAB cl f l = true →
      f' ∈ (cleanRes cl f).facts → den j f'.fact l0 l →
      FlowMA P counted L ok rc M j l0 n' f' l
  | filt {M j l0 n f l n' b may} :
      FlowMA P counted L ok rc M j l0 n f l → (M, n, Instr.filt b may, n') ∈ P.edges →
      (l.base = b → may l.path = true) → (f.fact.base = b → may f.fact.path = true) →
      FlowMA P counted L ok rc M j l0 n' f l

/-- The input mode fixes the emitted FLOW premise and restricted conclusion of
    the selected demand, using the actual binding input. -/
def starOK (dem : MethodId → DemandEdge → Prop) : AbstractOK := fun m a j g g' l1 l2 =>
  ∃ d p, dem m d ∧ d.din.mark = .star ∧ d.din.covers l1 ∧ d.dout = some p ∧ p.covers l2 ∧
    emitW d.din a.fact = some j ∧ j = flowForm d.din ∧
    restrictI j g d = some g' ∧ satW j a.fact = true

/-- The output mode uses exactly the published FLOW premise and exit fact. -/
def starJ (P : Program) (R : Obj → Prop) (pub : Pub) : AbstractOK := fun m _ j g g' l1 l2 =>
  R (.init m j) ∧ R (.edge m j (P.exit m) g) ∧ pub m j g g' ∧ j.mark = .star ∧
    j.covers l1 ∧ den j g'.fact l1 l2

/-- THE INPUT WITNESS OF A FORWARD RUN, WITH MODES. Every call that returns is an ABSTRACT call (a
    `*` pattern demands it and its inner flow is mark-agnostic), a CONCRETE call (a pattern whose
    mark is not `*` demands it, its inner flow is a moded flow), or a RECORDED call. -/
inductive FlowRRA (P : Program) (counted : Acc → Bool) (L : Nat) (dem : MethodId → DemandEdge → Prop) (rc : Recs) :
    MethodId → Loc → Node → Loc → Prop where
  | start (M : MethodId) (l0 : Loc) : FlowRRA P counted L dem rc M l0 (P.entry M) l0
  | step {M l0 n l n' l' s} :
      FlowRRA P counted L dem rc M l0 n l → (M, n, Instr.stmt s, n') ∈ P.edges → s.step l l' →
      FlowRRA P counted L dem rc M l0 n' l'
  | pass {M l0 n l n' c} :
      FlowRRA P counted L dem rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      memB l.base c.touched = false → FlowRRA P counted L dem rc M l0 n' l
  | acall {M l0 n l n' c e1 e2 l1 l2 l3 d p g} :
      FlowRRA P counted L dem rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowMA P counted L (starOK dem) rc c.callee (flowForm d.din) l1 (P.exit c.callee) g l2 →
      dem c.callee d → d.din.mark = .star → d.din.covers l1 → d.dout = some p → p.covers l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRRA P counted L dem rc M l0 n' l3
  | ccall {M l0 n l n' c e1 e2 l1 l2 l3 d p} :
      FlowRRA P counted L dem rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowRRA P counted L dem rc c.callee l1 (P.exit c.callee) l2 →
      dem c.callee d → d.din.mark ≠ .star → d.din.covers l1 → d.dout = some p → p.covers l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRRA P counted L dem rc M l0 n' l3
  | rcall {M l0 n l n' c e1 e2 l1 l2 l3 j g} :
      FlowRRA P counted L dem rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      rc c.callee (j, g) → Cross j g → j.covers l1 → den j g.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRRA P counted L dem rc M l0 n' l3
  | clean {M l0 n l n' cl} :
      FlowRRA P counted L dem rc M l0 n l → (M, n, Instr.clean cl, n') ∈ P.edges →
      cl.cleansB l = false → FlowRRA P counted L dem rc M l0 n' l
  | filt {M l0 n l n' b may} :
      FlowRRA P counted L dem rc M l0 n l → (M, n, Instr.filt b may, n') ∈ P.edges →
      (l.base = b → may l.path = true) → FlowRRA P counted L dem rc M l0 n' l

/-- The input vulnerability witness with modes: every call down enters a CONCRETE pattern (the sink
    check needs a concrete mark), every flow is `FlowRRA`. -/
inductive ReachRRA (P : Program) (counted : Acc → Bool) (L : Nat) (dem : MethodId → DemandEdge → Prop) (rc : Recs)
    (roots : List MethodId) : MethodId → Node → Loc → Prop where
  | root {M n l} : M ∈ roots → FlowRRA P counted L dem rc M zeroLoc n l → ReachRRA P counted L dem rc roots M n l
  | down {M n l n' c e l1 n2 l2 d} :
      ReachRRA P counted L dem rc roots M n l → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → den e.1 e.2 l l1 →
      dem c.callee d → d.din.mark ≠ .star → d.din.covers l1 →
      FlowRRA P counted L dem rc c.callee l1 n2 l2 → ReachRRA P counted L dem rc roots c.callee n2 l2

/-- THE OUTPUT WITNESS OF A RUN, WITH MODES. Every call that returns is an ABSTRACT call (a published
    piece of a FLOW premise has the pair, the inner flow is mark-agnostic and justified), a CONCRETE
    call (a published piece of a concrete premise has the pair), or a RECORDED call. -/
inductive FlowRDNA (P : Program) (counted : Acc → Bool) (L : Nat) (R : Obj → Prop) (pub : Pub) (rc : Recs) :
    MethodId → Loc → Node → Loc → Prop where
  | start (M : MethodId) (l0 : Loc) : FlowRDNA P counted L R pub rc M l0 (P.entry M) l0
  | step {M l0 n l n' l' s} :
      FlowRDNA P counted L R pub rc M l0 n l → (M, n, Instr.stmt s, n') ∈ P.edges → s.step l l' →
      FlowRDNA P counted L R pub rc M l0 n' l'
  | pass {M l0 n l n' c} :
      FlowRDNA P counted L R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      memB l.base c.touched = false → FlowRDNA P counted L R pub rc M l0 n' l
  | acall {M l0 n l n' c e1 e2 l1 l2 l3 j g g'} :
      FlowRDNA P counted L R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowMA P counted L (starJ P R pub) rc c.callee j l1 (P.exit c.callee) g l2 →
      R (.init c.callee j) → R (.edge c.callee j (P.exit c.callee) g) → pub c.callee j g g' →
      j.mark = .star → j.covers l1 → den j g'.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRDNA P counted L R pub rc M l0 n' l3
  | ccall {M l0 n l n' c e1 e2 l1 l2 l3 j g g' t} :
      FlowRDNA P counted L R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      FlowRDNA P counted L R pub rc c.callee l1 (P.exit c.callee) l2 →
      R (.init c.callee j) → R (.edge c.callee j (P.exit c.callee) g) → pub c.callee j g g' →
      j.mark = .conc t → j.covers l1 → den j g'.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRDNA P counted L R pub rc M l0 n' l3
  | rcall {M l0 n l n' c e1 e2 l1 l2 l3 j g} :
      FlowRDNA P counted L R pub rc M l0 n l → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → den e1.1 e1.2 l l1 →
      rc c.callee (j, g) → Cross j g → j.covers l1 → den j g.fact l1 l2 →
      e2 ∈ c.fromCallee → den e2.1 e2.2 l2 l3 →
      FlowRDNA P counted L R pub rc M l0 n' l3
  | clean {M l0 n l n' cl} :
      FlowRDNA P counted L R pub rc M l0 n l → (M, n, Instr.clean cl, n') ∈ P.edges →
      cl.cleansB l = false → FlowRDNA P counted L R pub rc M l0 n' l
  | filt {M l0 n l n' b may} :
      FlowRDNA P counted L R pub rc M l0 n l → (M, n, Instr.filt b may, n') ∈ P.edges →
      (l.base = b → may l.path = true) → FlowRDNA P counted L R pub rc M l0 n' l

/-- The output vulnerability witness with modes: its calls down enter an initial fact of `R` that
    covers the entry location, its flows are `FlowRDNA`. -/
inductive ReachRDNA (P : Program) (counted : Acc → Bool) (L : Nat) (R : Obj → Prop) (pub : Pub) (rc : Recs) (roots : List MethodId) :
    MethodId → Node → Loc → Prop where
  | root {M n l} : M ∈ roots → FlowRDNA P counted L R pub rc M zeroLoc n l → ReachRDNA P counted L R pub rc roots M n l
  | down {M n l n' c e l1 n2 l2 j} :
      ReachRDNA P counted L R pub rc roots M n l → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → den e.1 e.2 l l1 →
      R (.init c.callee j) → j.covers l1 →
      FlowRDNA P counted L R pub rc c.callee l1 n2 l2 → ReachRDNA P counted L R pub rc roots c.callee n2 l2

/-! ## 8. The contracts with modes -/

/-- THE FORWARD CONTRACT WITH MODES: every moded input witness of a sink pattern with a concrete
    mark is justified by `R` with modes, and `R` reports its vulnerability. -/
def CoversNA (P : Program) (counted : Acc → Bool) (L : Nat) (roots : List MethodId) (sinks : List (MethodId × Node × PFact))
    (dem : MethodId → DemandEdge → Prop) (rc : Recs) (R : Obj → Prop) (pub : Pub) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l →
    ReachRRA P counted L dem rc roots M n l →
    ReachRDNA P counted L R pub rc roots M n l ∧ ∃ b, R (.vuln M n s b)

/-- THE BACKWARD CONTRACT WITH MODES: every witness that forward run `Rk` justifies with modes, of a
    seeded sink, is a moded input witness of the next forward run (its demand `dnext`, its records
    `rcnext`): an abstract call stays abstract (a `*` pattern), a concrete call gets a concrete
    pattern or a record. -/
def BackwardContractNA (P : Program) (counted : Acc → Bool) (L : Nat) (roots : List MethodId)
    (sinks : List (MethodId × Node × PFact)) (seeds : List (MethodId × Node × PFact))
    (Rk : Obj → Prop) (pub : Pub) (rc : Recs)
    (dnext : MethodId → DemandEdge → Prop) (rcnext : Recs) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l →
    ReachRDNA P counted L Rk pub rc roots M n l → (M, n, s) ∈ seeds →
    ReachRRA P counted L dnext rcnext roots M n l

/-- THE RUN-1 CONTRACT WITH MODES (L2): run 1 justifies every real witness with modes and reports
    its vulnerability. -/
def Run1ContractA (P : Program) (counted : Acc → Bool) (L : Nat) (roots : List MethodId) (sinks : List (MethodId × Node × PFact))
    (R1 : Obj → Prop) : Prop :=
  ∀ M n l s T, (M, n, s) ∈ sinks → s.mark = .conc T → s.covers l → Reach P roots M n l →
    ReachRDNA P counted L R1 pubD (fun _ _ => False) roots M n l ∧ ∃ b, R1 (.vuln M n s b)

/-! ## 9. A moded witness is a witness of `HandoffDefs` -/

theorem flowMA_flowRR {P : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {rc : Recs}
    {M : MethodId} {j : PFact} {f : AFact} {l0 : Loc} {n : Node} {l : Loc}
    (h : FlowMA P counted L (starOK dem) rc M j l0 n f l) : FlowRR P dem rc M l0 n l := by
  induction h with
  | start M j l0 _ _ => exact FlowRR.start M l0
  | step _ he hs _ _ ih => exact FlowRR.step ih he (stepMA_step hs)
  | pass _ he hm _ ih => exact FlowRR.pass ih he hm
  | call _ he he1 hd1 _ _ _ hok _ _ _ _ he2 hd2 _ _ _ ih ihc =>
    obtain ⟨d, p, hdem, _, hdin, hdout, hp, _⟩ := hok
    exact FlowRR.call ih he he1 hd1 ihc hdem hdin hdout hp he2 hd2
  | rcall _ he he1 hd1 _ _ hrc hcr _ hjc hdg _ _ _ he2 hd2 _ _ _ ih =>
    exact FlowRR.rcall ih he he1 hd1 hrc hcr hjc hdg he2 hd2
  | clean _ he hcl _ _ _ ih => exact FlowRR.clean ih he hcl
  | filt _ he hl _ ih => exact FlowRR.filt ih he hl

#print axioms flowMA_flowRR

theorem flowRRA_flowRR {P : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {rc : Recs}
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : FlowRRA P counted L dem rc M l0 n l) : FlowRR P dem rc M l0 n l := by
  induction h with
  | start M l0 => exact FlowRR.start M l0
  | step _ he hs ih => exact FlowRR.step ih he hs
  | pass _ he hm ih => exact FlowRR.pass ih he hm
  | acall _ he he1 hd1 hma hdem _ hdin hdout hp he2 hd2 ih =>
    exact FlowRR.call ih he he1 hd1 (flowMA_flowRR hma) hdem hdin hdout hp he2 hd2
  | ccall _ he he1 hd1 _ hdem _ hdin hdout hp he2 hd2 ih ihc =>
    exact FlowRR.call ih he he1 hd1 ihc hdem hdin hdout hp he2 hd2
  | rcall _ he he1 hd1 hrc hcr hjc hdg he2 hd2 ih =>
    exact FlowRR.rcall ih he he1 hd1 hrc hcr hjc hdg he2 hd2
  | clean _ he hcl ih => exact FlowRR.clean ih he hcl
  | filt _ he hl ih => exact FlowRR.filt ih he hl

#print axioms flowRRA_flowRR

theorem reachRRA_reachRR {P : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {rc : Recs}
    {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ReachRRA P counted L dem rc roots M n l) : ReachRR P dem rc roots M n l := by
  induction h with
  | root hM hfl => exact ReachRR.root hM (flowRRA_flowRR hfl)
  | down _ he he1 hd1 hdem _ hdin hfc ih =>
    exact ReachRR.down ih he he1 hd1 hdem hdin (flowRRA_flowRR hfc)

#print axioms reachRRA_reachRR

theorem flowMA_flowRDN {P : Program} {counted : Acc → Bool} {L : Nat}
    {R : Obj → Prop} {pub : Pub} {rc : Recs}
    {M : MethodId} {j : PFact} {f : AFact} {l0 : Loc} {n : Node} {l : Loc}
    (h : FlowMA P counted L (starJ P R pub) rc M j l0 n f l) : FlowRDN P R pub rc M l0 n l := by
  induction h with
  | start M j l0 _ _ => exact FlowRDN.start M l0
  | step _ he hs _ _ ih => exact FlowRDN.step ih he (stepMA_step hs)
  | pass _ he hm _ ih => exact FlowRDN.pass ih he hm
  | call _ he he1 hd1 _ _ _ hok _ _ _ _ he2 hd2 _ _ _ ih ihc =>
    obtain ⟨hj, hg, hpub, _, hjc, hden⟩ := hok
    exact FlowRDN.call ih he he1 hd1 ihc hj hg hpub hjc hden he2 hd2
  | rcall _ he he1 hd1 _ _ hrc hcr _ hjc hdg _ _ _ he2 hd2 _ _ _ ih =>
    exact FlowRDN.rcall ih he he1 hd1 hrc hcr hjc hdg he2 hd2
  | clean _ he hcl _ _ _ ih => exact FlowRDN.clean ih he hcl
  | filt _ he hl _ ih => exact FlowRDN.filt ih he hl

#print axioms flowMA_flowRDN

theorem flowRDNA_flowRDN {P : Program} {counted : Acc → Bool} {L : Nat}
    {R : Obj → Prop} {pub : Pub} {rc : Recs}
    {M : MethodId} {l0 : Loc} {n : Node} {l : Loc}
    (h : FlowRDNA P counted L R pub rc M l0 n l) : FlowRDN P R pub rc M l0 n l := by
  induction h with
  | start M l0 => exact FlowRDN.start M l0
  | step _ he hs ih => exact FlowRDN.step ih he hs
  | pass _ he hm ih => exact FlowRDN.pass ih he hm
  | acall _ he he1 hd1 hma hj hg hpub _ hjc hden he2 hd2 ih =>
    exact FlowRDN.call ih he he1 hd1 (flowMA_flowRDN hma) hj hg hpub hjc hden he2 hd2
  | ccall _ he he1 hd1 _ hj hg hpub _ hjc hden he2 hd2 ih ihc =>
    exact FlowRDN.call ih he he1 hd1 ihc hj hg hpub hjc hden he2 hd2
  | rcall _ he he1 hd1 hrc hcr hjc hdg he2 hd2 ih =>
    exact FlowRDN.rcall ih he he1 hd1 hrc hcr hjc hdg he2 hd2
  | clean _ he hcl ih => exact FlowRDN.clean ih he hcl
  | filt _ he hl ih => exact FlowRDN.filt ih he hl

#print axioms flowRDNA_flowRDN

theorem reachRDNA_reachRDN {P : Program} {counted : Acc → Bool} {L : Nat}
    {R : Obj → Prop} {pub : Pub} {rc : Recs}
    {roots : List MethodId} {M : MethodId} {n : Node} {l : Loc}
    (h : ReachRDNA P counted L R pub rc roots M n l) : ReachRDN P R pub rc roots M n l := by
  induction h with
  | root hM hfl => exact ReachRDN.root hM (flowRDNA_flowRDN hfl)
  | down _ he he1 hd1 hj hjc hfc ih =>
    exact ReachRDN.down ih he he1 hd1 hj hjc (flowRDNA_flowRDN hfc)

#print axioms reachRDNA_reachRDN

/-- The moded forward contract gives the contract of `HandoffDefs` on moded inputs (the output
    forgets the modes). -/
theorem coversNA_reach {P : Program} {counted : Acc → Bool} {L : Nat} {roots : List MethodId}
    {sinks : List (MethodId × Node × PFact)} {dem : MethodId → DemandEdge → Prop} {rc : Recs}
    {R : Obj → Prop} {pub : Pub} (h : CoversNA P counted L roots sinks dem rc R pub)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hs : (M, n, s) ∈ sinks) (hT : s.mark = .conc T) (hsc : s.covers l)
    (hRe : ReachRRA P counted L dem rc roots M n l) :
    ReachRDN P R pub rc roots M n l ∧ ∃ b, R (.vuln M n s b) :=
  match h M n l s T hs hT hsc hRe with
  | ⟨hRD, hv⟩ => ⟨reachRDNA_reachRDN hRD, hv⟩

#print axioms coversNA_reach

end ApSpec.Abs
