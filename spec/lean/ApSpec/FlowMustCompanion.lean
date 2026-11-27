/-
  ApSpec.FlowMustCompanion — rule F1 of docs/design/owasp-cycle-stirling-split-20261126.md:
  "the C5 companion clause accepts a FLOW MUST member as it accepts a FLOW STAR member".

  Production C5 (`ap/RestrictedInitialPolicy.kt`, `canStoreInitial`) keeps a summary conclusion only
  under a demand row whose entry accepts the summary premise member. A member is accepted when it is
  a legal C2 start under the entry (`primaryImage`). CURRENT has one more clause, the companion
  clause: an abstract-mark (FLOW) STAR member is accepted under a concrete-mark entry when its
  concrete instance (the same member with the entry mark) is a legal start. A FLOW MUST member does
  not get this clause. NEW (F1): the companion clause takes the tails STAR and MUST.

  This file proves:
  1. SCOPE. F1 only adds acceptance (`new_of_cur`). The two rules differ only on the F1 row: an
     abstract-mark MUST member under a concrete-mark entry (`new_eq_cur_off`). On that row CURRENT
     rejects (`cur_row_false`) and F1 accepts exactly when the concrete instance is a legal start
     (`new_row`). An abstract-mark entry is unchanged (`new_eq_cur_abs_entry`).
  2. ONE LAW FOR BOTH TAILS. With F1 the companion clause is the same for STAR and MUST
     (`uniform`): a FLOW member is accepted under a concrete entry when the member or its concrete
     instance is a legal start.
  3. WITHOUT M1 ONLY THE EQUAL PATH CHANGES. When the MUST start below the entry is not legal (M1 off),
     every member that F1 adds sits at the entry path (`native_equal_path`).
  4. THE RELATIVE CAP STAYS. A member that F1 adds below the entry has exactly one counted accessor
     more than the entry (`cap_stays`): F1 never accepts a member deeper than `FL(Dc)+1`.
  5. C5 KEEPS EVERY CURRENT CONCLUSION. The admitted pieces of a premise are monotone in the
     acceptance test (`admitted_mono`), so F1 keeps every piece that CURRENT keeps (`f1_keeps`).

  Model versus production (each difference is listed in the design document, §8):
  * Empty exclusions everywhere (production checks `exclusion == Empty` on the STAR and EXACT rows and
    `excluded.isEmpty` on the FLOW mark; F1 keeps both checks unchanged).
  * No mark groups (`boundMark`, `isGroup`), no field limit K (`fitsBudget`), no STATIC rules, no
    run-2 STAR row, no `insideDemand` (it is a prefix-and-exclusion test; with empty exclusions it is
    the prefix test that `canEmit` already has).
  * Forward direction only (production `legalInitial` rejects a MUST start in the backward run, so
    neither the primary nor the F1 companion accepts a MUST member there).
  * The cost effect (a depth-0 piece that subsumes the depth-1 pieces in the store) is MEASURED, not
    proved (design §6.7).

  All proofs are constructive (only `propext`, `Quot.sound`; see the `#print axioms` lines).
-/
import ApSpec.MustStartFit

namespace ApSpec.FlowMustCompanion
open ApSpec ApSpec.MustStartFit

/-! ## 1. Patterns and the production tests -/

inductive Tl where
  | exact | star | may | must
  deriving DecidableEq, Repr

inductive Mk where
  | conc (t : Nat) | abs
  deriving DecidableEq, Repr

def Mk.isConc : Mk → Bool
  | .conc _ => true
  | .abs => false

/-- A demand entry or a premise member: base, path, tail, mark. -/
structure Pat where
  base : Nat
  path : List Acc
  tail : Tl
  mark : Mk
  deriving DecidableEq, Repr

/-- Production `renderedMark` without mark groups. -/
def rendered : Mk → Mk → Bool
  | .abs, .abs => true
  | .conc t, .conc u => t == u
  | _, _ => false

/-- Production `canEmitInitial` (forward, empty exclusions). `m1` is the M1 row (`MUST_PROBE`): a
    concrete MUST start below the entry that fits the relative cap. -/
def canEmit (m1 : Bool) (cnt : Acc → Bool) (d s : Pat) : Bool :=
  s.tail != .may && d.base == s.base && rendered d.mark s.mark &&
  (if s.path == d.path then
     (match s.tail with
      | .exact => d.tail != .must
      | .may => false
      | .must => d.tail == .may
      | .star => d.tail == .may)
   else
     d.tail == .may && d.path.isPrefixOf s.path && fitsB cnt (s.path.drop d.path.length) &&
     (s.tail == .star || s.tail == .exact && s.mark.isConc || m1 && s.tail == .must && s.mark.isConc))

/-- Production `primaryImage`: the member, or the EXACT form of a FLOW STAR member, is a legal start. -/
def primary (m1 : Bool) (cnt : Acc → Bool) (d s : Pat) : Bool :=
  canEmit m1 cnt d s || (s.mark == .abs && s.tail == .star && canEmit m1 cnt d { s with tail := .exact })

/-- The concrete instance of a member: the same member with the entry mark. -/
def inst (s : Pat) (m : Mk) : Pat := { s with mark := m }

/-- CURRENT `canStoreInitial`: the companion clause takes a FLOW STAR member only. -/
def storeCur (m1 : Bool) (cnt : Acc → Bool) (d s : Pat) : Bool :=
  primary m1 cnt d s ||
    (s.mark == .abs && s.tail == .star && d.mark.isConc && primary m1 cnt d (inst s d.mark))

/-- NEW `canStoreInitial` (F1): the companion clause takes a FLOW STAR or a FLOW MUST member. -/
def storeNew (m1 : Bool) (cnt : Acc → Bool) (d s : Pat) : Bool :=
  primary m1 cnt d s ||
    (s.mark == .abs && (s.tail == .star || s.tail == .must) && d.mark.isConc &&
      primary m1 cnt d (inst s d.mark))

/-! ## 2. Scope -/

/-- F1 only adds acceptance. -/
theorem new_of_cur (m1 : Bool) (cnt : Acc → Bool) (d s : Pat) (h : storeCur m1 cnt d s = true) :
    storeNew m1 cnt d s = true := by
  unfold storeCur at h
  unfold storeNew
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  rcases h with h | ⟨⟨⟨ha, hs⟩, hc⟩, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨⟨ha, Or.inl hs⟩, hc⟩, hp⟩

/-- Off the F1 row (an abstract-mark MUST member) the two rules are equal. -/
theorem new_eq_cur_off (m1 : Bool) (cnt : Acc → Bool) (d s : Pat)
    (h : ¬ (s.mark = .abs ∧ s.tail = .must)) : storeNew m1 cnt d s = storeCur m1 cnt d s := by
  unfold storeNew storeCur
  cases hm : s.mark <;> cases ht : s.tail <;> first | rfl | exact absurd ⟨hm, ht⟩ h

/-- Under an abstract-mark entry the two rules are equal (the companion clause needs a concrete entry). -/
theorem new_eq_cur_abs_entry (m1 : Bool) (cnt : Acc → Bool) (d s : Pat) (hd : d.mark = .abs) :
    storeNew m1 cnt d s = storeCur m1 cnt d s := by
  unfold storeNew storeCur
  simp [hd, Mk.isConc]

/-- A FLOW member is never a primary start under a concrete-mark entry. -/
theorem primary_abs_conc (m1 : Bool) (cnt : Acc → Bool) (d s : Pat) (t : Nat)
    (hm : s.mark = .abs) (hd : d.mark = .conc t) : primary m1 cnt d s = false := by
  unfold primary canEmit
  simp [hm, hd, rendered]

/-- On the F1 row CURRENT rejects the member. -/
theorem cur_row_false (m1 : Bool) (cnt : Acc → Bool) (d s : Pat) (t : Nat)
    (hm : s.mark = .abs) (ht : s.tail = .must) (hd : d.mark = .conc t) :
    storeCur m1 cnt d s = false := by
  unfold storeCur
  rw [primary_abs_conc m1 cnt d s t hm hd]
  simp [ht]

/-- On the F1 row F1 accepts the member exactly when its concrete instance is a legal start. -/
theorem new_row (m1 : Bool) (cnt : Acc → Bool) (d s : Pat) (t : Nat)
    (hm : s.mark = .abs) (ht : s.tail = .must) (hd : d.mark = .conc t) :
    storeNew m1 cnt d s = canEmit m1 cnt d (inst s (.conc t)) := by
  unfold storeNew
  rw [primary_abs_conc m1 cnt d s t hm hd, hm, ht, hd]
  simp [Mk.isConc, primary, inst, ht]

/-! ## 3. One law for both tails -/

/-- With F1 the companion clause is the same for STAR and MUST. -/
theorem uniform (m1 : Bool) (cnt : Acc → Bool) (d s : Pat) (t : Nat)
    (hm : s.mark = .abs) (ht : s.tail = .star ∨ s.tail = .must) (hd : d.mark = .conc t) :
    storeNew m1 cnt d s = (primary m1 cnt d s || primary m1 cnt d (inst s (.conc t))) := by
  unfold storeNew
  rcases ht with ht | ht <;> simp [hm, ht, hd, Mk.isConc]

/-! ## 4. Without M1 only the equal path changes -/

theorem native_equal_path (cnt : Acc → Bool) (d s : Pat)
    (hn : storeNew false cnt d s = true) (hc : storeCur false cnt d s = false) : s.path = d.path := by
  by_cases hrow : s.mark = .abs ∧ s.tail = .must
  · obtain ⟨hm, ht⟩ := hrow
    cases hd : d.mark with
    | abs =>
      rw [new_eq_cur_abs_entry false cnt d s hd, hc] at hn
      exact absurd hn Bool.false_ne_true
    | conc t =>
      rw [new_row false cnt d s t hm ht hd] at hn
      unfold canEmit at hn
      simp only [inst, ht, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
      by_cases hp : s.path = d.path
      · exact hp
      · simp [hp, Mk.isConc] at hn
  · rw [new_eq_cur_off false cnt d s hrow, hc] at hn
    exact absurd hn Bool.false_ne_true

/-! ## 5. The relative cap stays -/

theorem cap_stays (m1 : Bool) (cnt : Acc → Bool) (d s : Pat)
    (hn : storeNew m1 cnt d s = true) (hc : storeCur m1 cnt d s = false) (hp : s.path ≠ d.path) :
    fl cnt s.path = fl cnt d.path + 1 := by
  by_cases hrow : s.mark = .abs ∧ s.tail = .must
  · obtain ⟨hm, ht⟩ := hrow
    cases hd : d.mark with
    | abs =>
      rw [new_eq_cur_abs_entry m1 cnt d s hd, hc] at hn
      exact absurd hn Bool.false_ne_true
    | conc t =>
      rw [new_row m1 cnt d s t hm ht hd] at hn
      unfold canEmit at hn
      simp only [inst, Bool.and_eq_true] at hn
      obtain ⟨_, hrest⟩ := hn
      simp only [beq_iff_eq, hp, if_false, Bool.and_eq_true] at hrest
      obtain ⟨⟨⟨_, hpre⟩, hfit⟩, _⟩ := hrest
      obtain ⟨r, hr⟩ := (List.isPrefixOf_iff_prefix.mp hpre)
      rw [← hr] at hfit ⊢
      simp only [List.drop_left] at hfit
      rw [fl_append, fits_fl cnt r hfit]
  · rw [new_eq_cur_off m1 cnt d s hrow, hc] at hn
    exact absurd hn Bool.false_ne_true

/-! ## 6. C5 keeps every CURRENT conclusion -/

/-- The admitted pieces of a premise member: each row whose entry accepts the member restricts the
    raw conclusion at its exit (production `offerDataPair`, `ExactDemandResults`). -/
def admitted {β : Type} (acc : Pat → Pat → Bool) (rows : List (Pat × Pat)) (s : Pat)
    (piece : Pat → List β) : List β :=
  (rows.filter (fun r => acc r.1 s)).flatMap (fun r => piece r.2)

theorem admitted_mono {β : Type} (a b : Pat → Pat → Bool) (rows : List (Pat × Pat)) (s : Pat)
    (piece : Pat → List β) (h : ∀ d, a d s = true → b d s = true) :
    ∀ x, x ∈ admitted a rows s piece → x ∈ admitted b rows s piece := by
  intro x hx
  simp only [admitted, List.mem_flatMap, List.mem_filter] at hx ⊢
  obtain ⟨r, ⟨hr, ha⟩, hx⟩ := hx
  exact ⟨r, ⟨hr, h r.1 ha⟩, hx⟩

/-- F1 keeps every piece that CURRENT keeps: no route that CURRENT serves is lost. -/
theorem f1_keeps {β : Type} (m1 : Bool) (cnt : Acc → Bool) (rows : List (Pat × Pat)) (s : Pat)
    (piece : Pat → List β) :
    ∀ x, x ∈ admitted (storeCur m1 cnt) rows s piece → x ∈ admitted (storeNew m1 cnt) rows s piece :=
  admitted_mono _ _ rows s piece (fun d h => new_of_cur m1 cnt d s h)

/-! ## 7. Vectors: the Conductor loop block (checked by `decide`) -/

namespace Vec
def cnt : Acc → Bool := MustStartFit.Vec.cnt
/-- Entry `var(3).MAY/T` of a concrete demand row of `ParametersUtils#replace`, block B2. -/
def d : Pat := ⟨3, [], .may, .conc 1⟩
/-- Member `var(3).HeaderIterator#headers.MUST/FLOW` (one counted field below the entry). -/
def sM : Pat := ⟨3, [5], .must, .abs⟩
/-- Member `var(3).HeaderIterator#headers.*/FLOW`. -/
def sS : Pat := ⟨3, [5], .star, .abs⟩
/-- Member `var(3).MUST/FLOW` (at the entry path). -/
def s0 : Pat := ⟨3, [], .must, .abs⟩
/-- Member `var(3).X.Y.MUST/FLOW` (two counted fields below the entry: beyond the cap). -/
def sM2 : Pat := ⟨3, [5, 7], .must, .abs⟩
/-- An abstract-mark entry `var(3).MAY/FLOW`. -/
def dA : Pat := ⟨3, [], .may, .abs⟩

/-- CURRENT: the FLOW STAR member meets the concrete row; the FLOW MUST member does not. -/
example : storeCur true cnt d sS = true := by decide
example : storeCur true cnt d sM = false := by decide
/-- F1 with M1: the FLOW MUST member meets the concrete row as its STAR twin does. -/
example : storeNew true cnt d sM = true := by decide
/-- F1 without M1: the member below the entry is not added (its concrete MUST start is not legal). -/
example : storeNew false cnt d sM = false := by decide
/-- F1 without M1 adds the equal-path member. -/
example : storeCur false cnt d s0 = false := by decide
example : storeNew false cnt d s0 = true := by decide
/-- The cap: a member two counted fields below the entry is not added. -/
example : storeNew true cnt d sM2 = false := by decide
/-- An abstract-mark entry is unchanged. -/
example : storeNew true cnt dA sM = storeCur true cnt dA sM := by decide
end Vec

end ApSpec.FlowMustCompanion

#print axioms ApSpec.FlowMustCompanion.new_of_cur
#print axioms ApSpec.FlowMustCompanion.new_eq_cur_off
#print axioms ApSpec.FlowMustCompanion.new_eq_cur_abs_entry
#print axioms ApSpec.FlowMustCompanion.cur_row_false
#print axioms ApSpec.FlowMustCompanion.new_row
#print axioms ApSpec.FlowMustCompanion.uniform
#print axioms ApSpec.FlowMustCompanion.native_equal_path
#print axioms ApSpec.FlowMustCompanion.cap_stays
#print axioms ApSpec.FlowMustCompanion.admitted_mono
#print axioms ApSpec.FlowMustCompanion.f1_keeps
