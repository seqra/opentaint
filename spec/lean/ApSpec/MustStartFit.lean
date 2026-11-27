/-
  ApSpec.MustStartFit — rule M1 of docs/design/owasp-cycle-stirling-split-20261126.md:
  "C2 starts a MUST actual that fits the relative cap as itself".

  STATUS: M1 alone is not WI (design document §11: it fails the gate on Conductor). M1 v5 together
  with rule F1 (`ApSpec.FlowMustCompanion`) is the OWASP fix (design §3.8, §11). Sections 1-5 model
  the v4 form; section 6 adds the v5 layer guard (a NORMAL actual only) on top of it.

  Production C2 (`ap/RestrictedInitialPolicy.kt`, `emit`, ANY entry, actual strictly below the
  entry) cuts the actual at its first counted accessor below the entry (the relative cap
  `FL(Dc)+1`). CURRENT: when the actual fits the cap (no accessor after that first counted one), an
  EXACT actual with a concrete mark keeps its `$` tail; every other actual becomes a STAR start at
  its own path. A STAR start with a concrete mark is DEMAND by itself (ap.md §6.5, `startFact`).
  NEW (M1 v4, forward restricted runs, concrete entry mark): a MUST (`[any-taint]`) actual that fits
  the cap starts as itself, with its exclusion, as a must-premise. An abstract-mark entry keeps the
  CURRENT start (the start table of ap.md §6.5 has no FLOW must row).

  This file proves:
  1. SCOPE. `c2New` and `c2Cur` differ only on the M1 rows (`new_eq_cur_off`); on these rows CURRENT
     gives the STAR start (`cur_on_rows`).
  2. THE M1 ROW IS THE SPEC EMISSION. On the M1 rows `c2New` equals the spec emission with the must
     flag `emitTX emitX` (`new_eq_spec`). So the proved C2 contract with exclusions
     (`AnyTaintExCov.emitX_contract`) holds on these rows (`new_contract`): every demanded location
     that the admitted part of the actual carries is covered by the M1 premise, and the actual
     satisfies the premise.
  3. LAYERS. The CURRENT start of an M1 row with a concrete mark is DEMAND (`cur_start_demand`); the
     M1 start is NORMAL (`new_start_normal`) and is the actual itself (`new_start_is_actual`).
  4. THE RELATIVE CAP STAYS. The M1 premise has exactly one counted accessor more than the entry
     (`new_depth`): M1 never relaxes the cap `FL(Dc)+1`; it only stops the tail abstraction of an
     actual that already fits the cap.
  5. DIRECTION. The model is the forward restricted run. Production checks `direction == FORWARD`
     and falls back to the CURRENT STAR start when the MUST start is not legal (`legalInitial`). The
     model has no backward branch; see the proof scope in the design document.

  Model versus production (each difference is listed in the design document, §8):
  * `fitsB` is production `end == q.size` with `end = firstFieldEnd(base, p, q)`; the STATIC anchor
    rule of `firstFieldEnd` is not modelled (M1 has no STATIC case on the measured projects).
  * The model has no field limit K: production also checks `fitsBudget`, the same for both rules.
  * The M1 rows have a concrete entry mark (v4 guard `mark is MarkSlot.Concrete`), so the abstract-mark
    case of `normX` does not occur on them. Production uses the bound mark (`boundMark`: the entry mark,
    or the actual mark for a group entry); the model uses the actual's mark.
  * Companion starts (`emitAdmissions`) are not modelled: M1 adds none and removes the FLOW
    companion of the CURRENT STAR start (measured, design §5).

  All proofs are constructive (only `propext`, `Quot.sound`; see the `#print axioms` lines).
-/
import ApSpec.AnyTaintExDefs
import ApSpec.AnyTaintExCov

namespace ApSpec.MustStartFit
open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx

/-! ## 1. The cap test and the two production rules -/

/-- The continuation `r` below the entry FITS the relative cap: its last accessor is counted and no
    accessor before it is counted (production `end == q.size`). -/
def fitsB (cnt : Acc → Bool) : List Acc → Bool
  | []          => false
  | [f]         => cnt f
  | a :: b :: r => !cnt a && fitsB cnt (b :: r)

/-- The number of counted accessors of a path (`FL`). -/
def fl (cnt : Acc → Bool) (p : List Acc) : Nat := (p.filter cnt).length

/-- The first counted end of `r`: the length of the shortest prefix that ends with a counted
    accessor (production `firstFieldEnd`, relative to the entry). -/
def firstEnd (cnt : Acc → Bool) : List Acc → Option Nat
  | []     => none
  | a :: r => if cnt a then some 1 else (firstEnd cnt r).map (· + 1)

/-- The M1 condition on one C2 query (v4): the actual is MUST, the entry has a concrete mark (the
    start-table row `(x, p, [any-taint], E, T)`), and the actual fits the cap below the entry. -/
def m1RowB (cnt : Acc → Bool) (d : PFact) (r : List Acc) (am : Bool) (a : PFact) : Bool :=
  am && a.kind.isAny && concB d.mark && fitsB cnt r

/-- CURRENT production C2 for an ANY entry and an actual strictly below it by `r`
    (premise, must flag, premise exclusion). -/
def c2Cur (cnt : Acc → Bool) (d a : PFact) (r : List Acc) : Option (PFact × Bool × Excl) :=
  match firstEnd cnt r with
  | none   => none
  | some e =>
    if e == r.length && a.kind == .exact && concB a.mark then some (a, false, Excl.empty)
    else some (⟨a.base, d.path ++ r.take e, .star Excl.empty, a.mark⟩, false, Excl.empty)

/-- NEW production C2 (rule M1): a MUST actual that fits the cap starts as itself. -/
def c2New (cnt : Acc → Bool) (d a : PFact) (r : List Acc) (am : Bool) (aex : Excl) :
    Option (PFact × Bool × Excl) :=
  if m1RowB cnt d r am a then some (a, true, normJ a aex) else c2Cur cnt d a r

/-! ## 2. Scope: the only changed row -/

/-- Off the M1 rows the two rules are equal. -/
theorem new_eq_cur_off (cnt : Acc → Bool) (d a : PFact) (r : List Acc) (am : Bool) (aex : Excl)
    (h : m1RowB cnt d r am a = false) : c2New cnt d a r am aex = c2Cur cnt d a r := by
  simp [c2New, h]

/-- A fitting continuation is not empty, and its first counted end is its length. -/
theorem fits_firstEnd (cnt : Acc → Bool) : ∀ r : List Acc, fitsB cnt r = true →
    firstEnd cnt r = some r.length
  | [], h => by simp [fitsB] at h
  | [f], h => by simp [fitsB] at h; simp [firstEnd, h]
  | a :: b :: r, h => by
    simp only [fitsB, Bool.and_eq_true, Bool.not_eq_true'] at h
    have ih := fits_firstEnd cnt (b :: r) h.2
    show (if cnt a then some 1 else (firstEnd cnt (b :: r)).map (· + 1)) = some (a :: b :: r).length
    rw [if_neg (by simp [h.1]), ih]
    simp

/-- On an M1 row with a concrete mark CURRENT gives the STAR start at the actual's own path. -/
theorem cur_on_rows (cnt : Acc → Bool) (d a : PFact) (r : List Acc) (am : Bool)
    (hrow : m1RowB cnt d r am a = true) (hpath : a.path = d.path ++ r) :
    c2Cur cnt d a r = some (⟨a.base, a.path, .star Excl.empty, a.mark⟩, false, Excl.empty) := by
  simp only [m1RowB, Bool.and_eq_true] at hrow
  obtain ⟨⟨⟨_, hany⟩, _⟩, hfit⟩ := hrow
  have hk : a.kind = .any := by
    cases hk : a.kind with
    | any => rfl
    | exact => rw [hk] at hany; exact absurd hany Bool.false_ne_true
    | star e => rw [hk] at hany; exact absurd hany Bool.false_ne_true
  have hne : (a.kind == Kind.exact) = false := by rw [hk]; rfl
  unfold c2Cur
  rw [fits_firstEnd cnt r hfit, hne]
  show (if (r.length == r.length && false && concB a.mark) = true then some (a, false, Excl.empty)
    else some (⟨a.base, d.path ++ r.take r.length, .star Excl.empty, a.mark⟩, false, Excl.empty)) = _
  rw [Bool.and_false, Bool.false_and, if_neg Bool.false_ne_true, List.take_length, ← hpath]

/-! ## 3. The M1 row is the spec emission -/

/-- A nonempty continuation from `dropPrefix`: `relate` gives `.below r` with `r ≠ []` for an actual
    strictly below the entry. -/
theorem new_eq_spec (cnt : Acc → Bool) (d a : PFact) (r : List Acc) (am : Bool) (aex : Excl)
    (hbase : Nat.beq d.base a.base = true) (hmark : markMatchB d.mark a.mark = true)
    (hany : d.kind = .any) (hrel : relate d.path a.path = .below r)
    (hrow : m1RowB cnt d r am a = true) :
    c2New cnt d a r am aex = emitTX emitX d a am aex := by
  have hrow' := hrow
  simp only [m1RowB, Bool.and_eq_true] at hrow'
  obtain ⟨⟨⟨ham, hka⟩, _⟩, hfit⟩ := hrow'
  obtain ⟨x, r', rfl⟩ : ∃ x r', r = x :: r' := by
    cases r with
    | nil => simp [fitsB] at hfit
    | cons x r' => exact ⟨x, r', rfl⟩
  have hm : emitM d a = some a := by
    unfold emitM
    rw [hbase, hmark, hrel]
    simp [hany, admitsTailB]
  have hx : emitX d a aex = some (a, normJ a aex) := by
    unfold emitX
    rw [hm, hrel]
  unfold c2New
  rw [if_pos hrow]
  simp [emitTX, hx, ham, hka]

/-- THE CONTRACT ON THE M1 ROWS (from `AnyTaintExCov.emitX_contract`): for a concrete mark, every
    demanded location that the admitted part of the actual carries is covered by the M1 premise with
    its exclusion, and the actual satisfies that premise. -/
theorem new_contract (cnt : Acc → Bool) (d a : PFact) (r : List Acc) (am : Bool) (aex : Excl)
    (hbase : Nat.beq d.base a.base = true) (hmark : markMatchB d.mark a.mark = true)
    (hany : d.kind = .any) (hrel : relate d.path a.path = .below r)
    (hrow : m1RowB cnt d r am a = true) (l : Loc) (t : Mark) (ht : a.mark = .conc t)
    (hd : d.covers l) (ha : coversX a aex l) :
    ∃ j must jex, c2New cnt d a r am aex = some (j, must, jex) ∧ coversX j jex l ∧
      satX j jex a aex = true := by
  obtain ⟨j, jex, hj, hcov, hsat⟩ := ApSpec.AnyTaintExCov.emitX_contract d a aex l t ht hd ha
  refine ⟨j, am && j.kind.isAny, jex, ?_, hcov, hsat⟩
  rw [new_eq_spec cnt d a r am aex hbase hmark hany hrel hrow]
  simp [emitTX, hj]

/-! ## 4. Layers -/

/-- The CURRENT start of an M1 row with a concrete mark is DEMAND by itself (ap.md §6.5). -/
theorem cur_start_demand (a : PFact) (t : Mark) (ht : a.mark = .conc t) :
    (startX ⟨a.base, a.path, .star Excl.empty, a.mark⟩ false Excl.empty).af.demand = true := by
  simp [startX, startFact, ht]

/-- The M1 start is NORMAL. -/
theorem new_start_normal (a : PFact) (aex : Excl) :
    (startX a true (normJ a aex)).af.demand = false := by
  simp only [startX, ite_true, normX]
  split <;> rfl

/-- The M1 start is the actual itself (same path, tail and mark). -/
theorem new_start_is_actual (a : PFact) (aex : Excl) :
    (startX a true (normJ a aex)).af.fact = a := by
  simp only [startX, ite_true, normX]
  split <;> rfl

/-- For a concrete mark the M1 start keeps the actual's exclusion (a MUST actual has kind `.any`,
    so `normJ` keeps it): it covers exactly the admitted locations of the actual. -/
theorem new_start_covers_iff (a : PFact) (aex : Excl) (t : Mark) (ht : a.mark = .conc t)
    (hka : a.kind = .any) (l : Loc) :
    coversX (startX a true (normJ a aex)).af.fact (startX a true (normJ a aex)).ex l ↔
      coversX a aex l := by
  have hj : normJ a aex = aex := by simp [normJ, hka]
  have hc : carriesB ⟨a, false⟩ = true := by simp [carriesB, hka, Kind.isAny, concB, ht]
  simp [startX, normX, hj, hc]

/-! ## 5. The relative cap stays -/

theorem fl_append (cnt : Acc → Bool) (p q : List Acc) : fl cnt (p ++ q) = fl cnt p + fl cnt q := by
  simp [fl, List.filter_append]

/-- A fitting continuation has exactly one counted accessor. -/
theorem fits_fl (cnt : Acc → Bool) : ∀ r : List Acc, fitsB cnt r = true → fl cnt r = 1
  | [], h => by simp [fitsB] at h
  | [f], h => by simp [fitsB] at h; simp [fl, h]
  | a :: b :: r, h => by
    simp only [fitsB, Bool.and_eq_true, Bool.not_eq_true'] at h
    have ih := fits_fl cnt (b :: r) h.2
    simp only [fl] at ih ⊢
    rw [List.filter_cons, if_neg (by simp [h.1])]
    exact ih

/-- THE CAP: the M1 premise has exactly `FL(entry) + 1` counted accessors. -/
theorem new_depth (cnt : Acc → Bool) (d a : PFact) (r : List Acc) (am : Bool)
    (hrow : m1RowB cnt d r am a = true) (hpath : a.path = d.path ++ r) :
    fl cnt a.path = fl cnt d.path + 1 := by
  simp only [m1RowB, Bool.and_eq_true] at hrow
  rw [hpath, fl_append, fits_fl cnt r hrow.2]

/-! ## 6. v5: the layer guard -/

/-- The M1 condition of v5: the v4 condition and a NORMAL actual (`actualLayer == NORMAL`). -/
def m1RowV5 (cnt : Acc → Bool) (d : PFact) (r : List Acc) (am : Bool) (a : PFact) (normal : Bool) : Bool :=
  normal && m1RowB cnt d r am a

/-- NEW production C2 of v5. -/
def c2NewV5 (cnt : Acc → Bool) (d a : PFact) (r : List Acc) (am : Bool) (aex : Excl) (normal : Bool) :
    Option (PFact × Bool × Excl) :=
  if m1RowV5 cnt d r am a normal then some (a, true, normJ a aex) else c2Cur cnt d a r

/-- v5 on a NORMAL actual is v4: every theorem of sections 2 to 5 holds for it. -/
theorem v5_normal_eq_v4 (cnt : Acc → Bool) (d a : PFact) (r : List Acc) (am : Bool) (aex : Excl) :
    c2NewV5 cnt d a r am aex true = c2New cnt d a r am aex := by
  simp [c2NewV5, c2New, m1RowV5]

/-- v5 on a DEMAND actual is CURRENT (row M1.2b of the design): a DEMAND actual gets a DEMAND start
    in both forms. -/
theorem v5_demand_eq_cur (cnt : Acc → Bool) (d a : PFact) (r : List Acc) (am : Bool) (aex : Excl) :
    c2NewV5 cnt d a r am aex false = c2Cur cnt d a r := by
  simp [c2NewV5, m1RowV5]

/-! ## 7. Vectors (checked by `decide`) -/

namespace Vec
/-- Every accessor below 100 counts; 100 and above do not (an element accessor, say). -/
def cnt : Acc → Bool := fun a => a < 100
/-- Entry `var.MAY/T` (OWASP `var(27).MAY`). -/
def d : PFact := ⟨27, [], .any, .conc 1⟩
/-- Actual `var.SB.MUST/T` (one counted field below the entry). -/
def a : PFact := ⟨27, [5], .any, .conc 1⟩
/-- Actual `var.SB.CT.MUST/T` (two counted fields below: the cap cuts). -/
def a2 : PFact := ⟨27, [5, 7], .any, .conc 1⟩
/-- Actual `var.SB.$/T` (EXACT, fits). -/
def ae : PFact := ⟨27, [5], .exact, .conc 1⟩

example : c2Cur cnt d a [5] = some (⟨27, [5], .star Excl.empty, .conc 1⟩, false, Excl.empty) := by decide
example : c2New cnt d a [5] true Excl.empty = some (a, true, Excl.empty) := by decide
/-- The cut row is unchanged: the cap cuts at the first counted field, STAR, DEMAND. -/
example : c2New cnt d a2 [5, 7] true Excl.empty = c2Cur cnt d a2 [5, 7] := by decide
example : c2New cnt d a2 [5, 7] true Excl.empty =
    some (⟨27, [5], .star Excl.empty, .conc 1⟩, false, Excl.empty) := by decide
/-- The EXACT row is unchanged. -/
example : c2New cnt d ae [5] false Excl.empty = some (ae, false, Excl.empty) := by decide
/-- A non-MUST `.any` actual (MAY) is unchanged: STAR start. -/
example : c2New cnt d a [5] false Excl.empty = c2Cur cnt d a [5] := by decide
/-- An abstract-mark entry (`*`, FLOW) is unchanged (v4): CURRENT STAR start. -/
def dS : PFact := ⟨27, [], .any, .star⟩
example : c2New cnt dS ⟨27, [5], .any, .star⟩ [5] true Excl.empty =
    c2Cur cnt dS ⟨27, [5], .any, .star⟩ [5] := by decide
/-- An uncounted accessor after the counted one: no fit, unchanged. -/
example : c2New cnt d ⟨27, [5, 100], .any, .conc 1⟩ [5, 100] true Excl.empty =
    some (⟨27, [5], .star Excl.empty, .conc 1⟩, false, Excl.empty) := by decide
/-- v5: a DEMAND MUST actual that fits the cap keeps the CURRENT STAR start. -/
example : c2NewV5 cnt d a [5] true Excl.empty false =
    some (⟨27, [5], .star Excl.empty, .conc 1⟩, false, Excl.empty) := by decide
example : c2NewV5 cnt d a [5] true Excl.empty true = some (a, true, Excl.empty) := by decide
end Vec

end ApSpec.MustStartFit

#print axioms ApSpec.MustStartFit.new_eq_cur_off
#print axioms ApSpec.MustStartFit.cur_on_rows
#print axioms ApSpec.MustStartFit.new_eq_spec
#print axioms ApSpec.MustStartFit.new_contract
#print axioms ApSpec.MustStartFit.cur_start_demand
#print axioms ApSpec.MustStartFit.new_start_normal
#print axioms ApSpec.MustStartFit.new_start_is_actual
#print axioms ApSpec.MustStartFit.new_start_covers_iff
#print axioms ApSpec.MustStartFit.new_depth
#print axioms ApSpec.MustStartFit.v5_normal_eq_v4
#print axioms ApSpec.MustStartFit.v5_demand_eq_cur
