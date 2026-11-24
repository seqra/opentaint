/-!
# G6 drop form (acyclic proposal §5.1)

Standalone constructive model for `spec/acyclic-group-a-implementation.md` §3.
Lean 4.36.0, core library only, no `Classical`, no `sorry`, no custom axiom.

A position below the base of a TAINT fact is a path of accessors. Its spine
level is the number of leading element accessors. The type filter's mark policy
reads the static type of each spine level (`JIRTypeFilters.make`):
`prim k` (primitive or boxed), `boxed k` (a class that unboxes to a primitive)
and the primitive-tracking test `pt` of a mark. One mark `t` at a time: the
policy is a per-mark decision, and the filter applies it to every mark of a leaf
the same way (exact and any marks, both layers).
-/
namespace G6DropForm

inductive Acc where
  | elem
  | field (n : Nat)
deriving DecidableEq, Repr

abbrev Path := List Acc

/-- The spine level of a position: the number of leading element accessors. -/
def spineLen : Path → Nat
  | .elem :: r => spineLen r + 1
  | _ => 0

/-- The position is a spine node (only element accessors). -/
def onSpine : Path → Bool
  | [] => true
  | .elem :: r => onSpine r
  | .field _ :: _ => false

/-- `LevelMarkPolicy` (prototype `ap/Primitives.kt`). -/
structure Policy where
  prim  : Nat → Bool
  boxed : Nat → Bool
  pt    : Nat → Bool
  boxedPrim : ∀ k, boxed k = true → prim k = true

namespace Policy
/-- `MarkPolicy.keeps`, the native per-level decision. -/
def keeps (P : Policy) (t k : Nat) : Bool := !P.prim k || P.pt t
/-- `MarkPolicy.dropsValue`. -/
def dropsValue (P : Policy) (t k : Nat) : Bool := P.boxed k && !P.keeps t k
/-- `∃ k ≤ j, dropsValue t k`, accumulated as `droppedAt` in `ap/Filter.kt`. -/
def dropsUpTo (P : Policy) (t : Nat) : Nat → Bool
  | 0 => P.dropsValue t 0
  | j + 1 => P.dropsUpTo t j || P.dropsValue t (j + 1)
end Policy

/-- Native `markPolicyOnElements`: only spine leaves are filtered. -/
def removedNative (P : Policy) (t : Nat) (p : Path) : Bool :=
  onSpine p && !P.keeps t (spineLen p)

/-- Drop form: in addition, a mark that a boxed level `k ≤ spineLen p` drops is
    removed from every position at or below that level. -/
def removedDrop (P : Policy) (t : Nat) (p : Path) : Bool :=
  P.dropsUpTo t (spineLen p) || removedNative P t p

/-- A spine node at a true primitive level (primitive, not boxed). -/
def TruePrimLeaf (P : Policy) (q : Path) : Bool :=
  onSpine q && P.prim (spineLen q) && !P.boxed (spineLen q)

/-! ## Basic lemmas -/

theorem dropsUpTo_of (P : Policy) (t : Nat) {k : Nat} :
    ∀ {j : Nat}, k ≤ j → P.dropsValue t k = true → P.dropsUpTo t j = true
  | 0, hk, h => by
    have : k = 0 := Nat.le_zero.mp hk
    subst this; exact h
  | j + 1, hk, h => by
    unfold Policy.dropsUpTo
    cases Nat.lt_or_eq_of_le hk with
    | inl hlt => rw [dropsUpTo_of P t (Nat.le_of_lt_succ hlt) h]; rfl
    | inr heq => subst heq; rw [h, Bool.or_true]

theorem dropsUpTo_exists (P : Policy) (t : Nat) :
    ∀ {j : Nat}, P.dropsUpTo t j = true → ∃ k, k ≤ j ∧ P.dropsValue t k = true
  | 0, h => ⟨0, Nat.le_refl 0, h⟩
  | j + 1, h => by
    unfold Policy.dropsUpTo at h
    cases hd : P.dropsUpTo t j
    · rw [hd, Bool.false_or] at h; exact ⟨j + 1, Nat.le_refl _, h⟩
    · obtain ⟨k, hk, hv⟩ := dropsUpTo_exists P t hd
      exact ⟨k, Nat.le_succ_of_le hk, hv⟩

theorem dropsUpTo_mono (P : Policy) (t : Nat) {j j' : Nat} (hj : j ≤ j')
    (h : P.dropsUpTo t j = true) : P.dropsUpTo t j' = true := by
  obtain ⟨k, hk, hv⟩ := dropsUpTo_exists P t h
  exact dropsUpTo_of P t (Nat.le_trans hk hj) hv

theorem boxed_of_dropsValue (P : Policy) {t k : Nat} (h : P.dropsValue t k = true) :
    P.boxed k = true := by
  unfold Policy.dropsValue at h
  cases hb : P.boxed k
  · rw [hb, Bool.false_and] at h; exact h
  · rfl

theorem spineLen_append (q s : Path) : spineLen q ≤ spineLen (q ++ s) := by
  induction q with
  | nil => exact Nat.zero_le _
  | cons a r ih =>
    cases a with
    | elem => exact Nat.succ_le_succ ih
    | field n => exact Nat.le_refl 0

theorem spineLen_prefix {q p : Path} (h : q <+: p) : spineLen q ≤ spineLen p := by
  obtain ⟨s, hs⟩ := h
  rw [← hs]; exact spineLen_append q s

theorem length_of_onSpine : ∀ {p : Path}, onSpine p = true → p.length = spineLen p
  | [], _ => rfl
  | .elem :: r, h => by
    show r.length + 1 = spineLen r + 1
    rw [length_of_onSpine (p := r) h]
  | .field _ :: _, h => by cases h

/-! ## D1: the drop form extends native and acts only at or below a boxed level -/

theorem drop_extends_native (P : Policy) (t : Nat) (p : Path)
    (h : removedNative P t p = true) : removedDrop P t p = true := by
  unfold removedDrop; rw [h, Bool.or_true]

theorem native_without_boxed_level (P : Policy) (t : Nat) (p : Path)
    (h : ∀ k, k ≤ spineLen p → P.boxed k = false) :
    removedDrop P t p = removedNative P t p := by
  unfold removedDrop
  cases hd : P.dropsUpTo t (spineLen p)
  · rw [Bool.false_or]
  · obtain ⟨k, hk, hv⟩ := dropsUpTo_exists P t hd
    have := boxed_of_dropsValue P hv
    rw [h k hk] at this; cases this

/-- A primitive-tracking mark is never removed, natively or by the drop form. -/
theorem tracking_never_removed (P : Policy) (t : Nat) (p : Path) (h : P.pt t = true) :
    removedDrop P t p = false ∧ removedNative P t p = false := by
  have hk : ∀ k, P.keeps t k = true := by
    intro k; unfold Policy.keeps; rw [h, Bool.or_true]
  have hn : removedNative P t p = false := by
    unfold removedNative; rw [hk, Bool.not_true, Bool.and_false]
  have hv : ∀ k, P.dropsValue t k = false := by
    intro k; unfold Policy.dropsValue; rw [hk, Bool.not_true, Bool.and_false]
  have hd : P.dropsUpTo t (spineLen p) = false := by
    cases hx : P.dropsUpTo t (spineLen p)
    · rfl
    · obtain ⟨k, _, hv'⟩ := dropsUpTo_exists P t hx
      rw [hv k] at hv'; cases hv'
  refine ⟨?_, hn⟩
  unfold removedDrop; rw [hd, hn]; rfl

/-! ## D2: region exactness, prefix closure and monotonicity in K -/

/-- D2. If the drop form removes `t` at `q`, it removes `t` at every position of
    the region below `q` (`q` is a prefix of `p`). The only exception is a spine
    node at a true primitive level, which has no fields and no elements. -/
theorem removed_on_region (P : Policy) (t : Nat) (q p : Path)
    (hq : removedDrop P t q = true) (hpre : q <+: p)
    (hwf : p = q ∨ TruePrimLeaf P q = false) : removedDrop P t p = true := by
  unfold removedDrop at hq ⊢
  cases hd : P.dropsUpTo t (spineLen q)
  · rw [hd, Bool.false_or] at hq
    -- removed natively at q: a spine node with a primitive level and an ordinary mark
    unfold removedNative at hq
    have hs : onSpine q = true := (Bool.and_eq_true_iff.mp hq).1
    have hk : P.keeps t (spineLen q) = false := by
      have := (Bool.and_eq_true_iff.mp hq).2
      cases hx : P.keeps t (spineLen q)
      · rfl
      · rw [hx] at this; cases this
    cases hb : P.boxed (spineLen q)
    · -- a true primitive level: by `hwf` the position is `q` itself
      have htp : TruePrimLeaf P q = true := by
        unfold TruePrimLeaf
        have hp : P.prim (spineLen q) = true := by
          unfold Policy.keeps at hk
          cases hx : P.prim (spineLen q)
          · rw [hx] at hk; cases hk
          · rfl
        rw [hs, hp, hb]; rfl
      cases hwf with
      | inl e => subst e; unfold removedNative; rw [hd, hs, hk]; rfl
      | inr e => rw [htp] at e; cases e
    · -- a boxed level: dropsUpTo holds at q, against `hd`
      have hv : P.dropsValue t (spineLen q) = true := by
        unfold Policy.dropsValue; rw [hb, hk]; rfl
      rw [dropsUpTo_of P t (Nat.le_refl _) hv] at hd; cases hd
  · rw [dropsUpTo_mono P t (spineLen_prefix hpre) hd, Bool.true_or]

/-- D3 (prefix closure, ap.md S5 for the mark policy). If the drop form keeps `t`
    on the exact fact at `p`, it keeps `t` on every cut form `q.MAY` of it. -/
theorem kept_exact_keeps_cut (P : Policy) (t : Nat) (q p : Path)
    (hkept : removedDrop P t p = false) (hpre : q <+: p)
    (hwf : p = q ∨ TruePrimLeaf P q = false) : removedDrop P t q = false := by
  cases hq : removedDrop P t q
  · rfl
  · rw [removed_on_region P t q p hq hpre hwf] at hkept; cases hkept

/-- D4 (monotone in K). The cut at `K` keeps the fact's path to `K` accessors.
    If the drop form keeps `t` at the cut of a larger `K'`, it keeps `t` at the
    cut of every smaller `K`. So a larger field limit can only remove marks. -/
theorem monotone_in_K (P : Policy) (t : Nat) (p : Path) {K K' : Nat} (hK : K ≤ K')
    (hkept : removedDrop P t (p.take K') = false)
    (hwf : p.take K' = p.take K ∨ TruePrimLeaf P (p.take K) = false) :
    removedDrop P t (p.take K) = false := by
  have hpre : p.take K <+: p.take K' := by
    have e : p.take K = (p.take K').take K := by
      rw [List.take_take, Nat.min_eq_left hK]
    rw [e]; exact List.take_prefix K (p.take K')
  exact kept_exact_keeps_cut P t _ _ hkept hpre hwf

/-! ## D3', D4': no side condition for an admitted fact -/

/-- The path filter admits `p` (code fact C-A2, `JIRFactTypeChecker`): no
    accessor follows a true primitive value, so no strict prefix of an
    admitted path is a spine node at a true primitive level. -/
def Admitted (P : Policy) (p : Path) : Prop :=
  ∀ q, q <+: p → q ≠ p → TruePrimLeaf P q = false

theorem side_condition_of_admitted (P : Policy) {q p : Path} (hadm : Admitted P p)
    (hpre : q <+: p) : p = q ∨ TruePrimLeaf P q = false :=
  if h : q = p then Or.inl h.symm else Or.inr (hadm q hpre h)

/-- D3' (prefix closure for every admitted fact). -/
theorem kept_exact_keeps_cut_admitted (P : Policy) (t : Nat) (q p : Path)
    (hadm : Admitted P p) (hkept : removedDrop P t p = false) (hpre : q <+: p) :
    removedDrop P t q = false :=
  kept_exact_keeps_cut P t q p hkept hpre (side_condition_of_admitted P hadm hpre)

/-- D4' (monotone in K for every admitted fact). -/
theorem monotone_in_K_admitted (P : Policy) (t : Nat) (p : Path) {K K' : Nat} (hK : K ≤ K')
    (hadm : Admitted P (p.take K')) (hkept : removedDrop P t (p.take K') = false) :
    removedDrop P t (p.take K) = false := by
  have hpre : p.take K <+: p.take K' := by
    have e : p.take K = (p.take K').take K := by
      rw [List.take_take, Nat.min_eq_left hK]
    rw [e]; exact List.take_prefix K (p.take K')
  exact kept_exact_keeps_cut_admitted P t _ _ hadm hkept hpre

/-! ## D5: the native filter is not prefix closed (fixture M4) -/

/-- `Integer[]`: level 0 is an array (no policy), level 1 is `Integer` (boxed). -/
def m4 : Policy where
  prim k := k == 1
  boxed k := k == 1
  pt _ := false
  boxedPrim _ h := h

def m4Exact : Path := [.elem, .field 0]   -- x.[].value.$
def m4Cut : Path := [.elem]               -- x.[].MAY (the cut at K = 1)

theorem m4_native_breaks :
    removedNative m4 0 m4Exact = false ∧ removedNative m4 0 m4Cut = true := ⟨rfl, rfl⟩

theorem m4_drop_form :
    removedDrop m4 0 m4Exact = true ∧ removedDrop m4 0 m4Cut = true ∧ removedDrop m4 0 [] = false :=
  ⟨rfl, rfl, rfl⟩

theorem native_not_prefix_closed :
    ¬ (∀ (P : Policy) (t : Nat) (q p : Path), removedNative P t p = false → q <+: p →
        (p = q ∨ TruePrimLeaf P q = false) → removedNative P t q = false) := by
  intro h
  have := h m4 0 m4Cut m4Exact rfl ⟨[.field 0], rfl⟩ (Or.inr rfl)
  cases this

/-! ## D6: the conjunction of two policies (`TypeFilter.and`) is a level policy -/

def Policy.conj (A B : Policy) (_h : A.pt = B.pt) : Policy where
  prim k := A.prim k || B.prim k
  boxed k := A.boxed k || B.boxed k
  pt := A.pt
  boxedPrim k hk := by
    cases ha : A.boxed k
    · rw [ha, Bool.false_or] at hk; rw [B.boxedPrim k hk, Bool.or_true]
    · rw [A.boxedPrim k ha, Bool.true_or]

theorem conj_keeps (A B : Policy) (h : A.pt = B.pt) (t k : Nat) :
    (A.conj B h).keeps t k = (A.keeps t k && B.keeps t k) := by
  show (!(A.prim k || B.prim k) || A.pt t) = ((!A.prim k || A.pt t) && (!B.prim k || B.pt t))
  rw [← h]
  cases A.prim k <;> cases B.prim k <;> cases A.pt t <;> rfl

theorem conj_dropsValue (A B : Policy) (h : A.pt = B.pt) (t k : Nat) :
    (A.conj B h).dropsValue t k = (A.dropsValue t k || B.dropsValue t k) := by
  show ((A.boxed k || B.boxed k) && !(A.conj B h).keeps t k) =
    ((A.boxed k && !A.keeps t k) || (B.boxed k && !B.keeps t k))
  rw [conj_keeps]
  unfold Policy.keeps; rw [← h]
  cases hpa : A.prim k <;> cases hpb : B.prim k <;> cases hba : A.boxed k <;> cases hbb : B.boxed k <;>
    cases A.pt t <;>
    first
    | rfl
    | (have := A.boxedPrim k hba; rw [hpa] at this; cases this)
    | (have := B.boxedPrim k hbb; rw [hpb] at this; cases this)

/-! ## D7: the production algorithm and the reference compute the predicate -/

/-- `droppedAt` of `markPolicyDropForm`: the candidate marks (the marks of the
    subtree at the first boxed spine level `first`) that a boxed level `k ≤ j`
    drops. -/
def droppedAt (P : Policy) (cands : List Nat) (first : Nat) : Nat → List Nat
  | 0 => if decide (first ≤ 0) && P.boxed 0 then cands.filter (fun t => P.dropsValue t 0) else []
  | j + 1 =>
    let d := droppedAt P cands first j
    if decide (first ≤ j + 1) && P.boxed (j + 1) then
      d ++ cands.filter (fun t => !d.contains t && P.dropsValue t (j + 1))
    else d

/-- Production: the spine leaf gets the native policy and loses `droppedAt j`;
    every field subtree of level `j` loses `droppedAt j`. -/
def removedImpl (P : Policy) (cands : List Nat) (first t : Nat) (p : Path) : Bool :=
  (droppedAt P cands first (spineLen p)).contains t || removedNative P t p

/-- Constructive `LawfulBEq Nat` (the library instance goes through `Classical`). -/
local instance (priority := high) natReflBEq : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
local instance (priority := high) natLawfulBEq : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

theorem contains_filter (l : List Nat) (f : Nat → Bool) (t : Nat) (ht : t ∈ l) :
    (l.filter f).contains t = f t := by
  cases hf : f t
  · apply Bool.eq_false_iff.mpr; intro hc
    have := (List.mem_filter.mp (List.contains_iff_mem.mp hc)).2
    rw [hf] at this; cases this
  · exact List.contains_iff_mem.mpr (List.mem_filter.mpr ⟨ht, hf⟩)

theorem droppedAt_contains (P : Policy) (cands : List Nat) (first t : Nat) (ht : t ∈ cands)
    (hfirst : ∀ k, k < first → P.boxed k = false) :
    ∀ j, (droppedAt P cands first j).contains t = P.dropsUpTo t j
  | 0 => by
    unfold droppedAt Policy.dropsUpTo
    cases hc : (decide (first ≤ 0) && P.boxed 0)
    · show ([] : List Nat).contains t = P.dropsValue t 0
      unfold Policy.dropsValue
      cases hb : P.boxed 0
      · rfl
      · have hf : first ≤ 0 → False := by
          intro hle; rw [decide_eq_true hle, hb] at hc; cases hc
        have : 0 < first := Nat.lt_of_not_le hf
        rw [hfirst 0 this] at hb; cases hb
    · exact contains_filter cands _ t ht
  | j + 1 => by
    have ih := droppedAt_contains P cands first t ht hfirst j
    unfold droppedAt Policy.dropsUpTo
    cases hc : (decide (first ≤ j + 1) && P.boxed (j + 1))
    · show (droppedAt P cands first j).contains t = _
      rw [ih]
      have hv : P.dropsValue t (j + 1) = false := by
        unfold Policy.dropsValue
        cases hb : P.boxed (j + 1)
        · rfl
        · have hf : first ≤ j + 1 → False := by
            intro hle; rw [decide_eq_true hle, hb] at hc; cases hc
          rw [hfirst (j + 1) (Nat.lt_of_not_le hf)] at hb; cases hb
      rw [hv, Bool.or_false]
    · show (droppedAt P cands first j ++ _).contains t = _
      rw [List.contains_append, contains_filter cands _ t ht, ih]
      cases P.dropsUpTo t j <;> rfl

theorem droppedAt_sub (P : Policy) (cands : List Nat) (first : Nat) :
    ∀ j, ∀ x ∈ droppedAt P cands first j, x ∈ cands
  | 0, x, hx => by
    unfold droppedAt at hx
    split at hx
    · exact (List.mem_filter.mp hx).1
    · cases hx
  | j + 1, x, hx => by
    unfold droppedAt at hx
    split at hx
    · cases List.mem_append.mp hx with
      | inl h => exact droppedAt_sub P cands first j x h
      | inr h => exact (List.mem_filter.mp h).1
    · exact droppedAt_sub P cands first j x hx

/-- D7a. For every candidate mark, production equals the drop-form predicate. -/
theorem impl_is_drop_form (P : Policy) (cands : List Nat) (first t : Nat) (p : Path)
    (ht : t ∈ cands) (hfirst : ∀ k, k < first → P.boxed k = false) :
    removedImpl P cands first t p = removedDrop P t p := by
  unfold removedImpl removedDrop
  rw [droppedAt_contains P cands first t ht hfirst]

/-- D7b. Production never removes a mark that is not a candidate beyond native. -/
theorem impl_non_candidate (P : Policy) (cands : List Nat) (first t : Nat) (p : Path)
    (ht : t ∉ cands) : removedImpl P cands first t p = removedNative P t p := by
  unfold removedImpl
  have : (droppedAt P cands first (spineLen p)).contains t = false := by
    apply Bool.eq_false_iff.mpr; intro hc
    exact ht (droppedAt_sub P cands first _ t (List.contains_iff_mem.mp hc))
  rw [this, Bool.false_or]

/-- D7c. Above the first boxed level, the drop form is native, whatever the marks. -/
theorem drop_form_above_first (P : Policy) (first t : Nat) (p : Path)
    (hfirst : ∀ k, k < first → P.boxed k = false) (hp : spineLen p < first) :
    removedDrop P t p = removedNative P t p :=
  native_without_boxed_level P t p (fun k hk => hfirst k (Nat.lt_of_le_of_lt hk hp))

/-- Reference `ReferenceAlgebra.passes` with the drop form (prototype
    `interp/FormsReference.kt`): `for (k in 0..spine) if (dropsValue) false`;
    a path with a non-element accessor passes; else `keeps(mark, path.size)`. -/
def passesRef (P : Policy) (t : Nat) (p : Path) : Bool :=
  if (List.range (spineLen p + 1)).any (fun k => P.dropsValue t k) then false
  else if !onSpine p then true
  else P.keeps t p.length

theorem range_any (P : Policy) (t : Nat) :
    ∀ j, (List.range (j + 1)).any (fun k => P.dropsValue t k) = P.dropsUpTo t j
  | 0 => by show (P.dropsValue t 0 || false) = P.dropsValue t 0; rw [Bool.or_false]
  | j + 1 => by
    rw [List.range_succ, List.any_append, range_any P t j]
    show (P.dropsUpTo t j || (P.dropsValue t (j + 1) || false)) = _
    rw [Bool.or_false]; rfl

/-- D7d. The reference decision is the negation of the drop-form predicate. -/
theorem reference_is_drop_form (P : Policy) (t : Nat) (p : Path) :
    passesRef P t p = !removedDrop P t p := by
  unfold passesRef removedDrop removedNative
  rw [range_any P t (spineLen p)]
  cases hd : P.dropsUpTo t (spineLen p)
  · cases hs : onSpine p
    · rfl
    · rw [length_of_onSpine hs]
      cases P.keeps t (spineLen p) <;> rfl
  · rfl

end G6DropForm

#print axioms G6DropForm.drop_extends_native
#print axioms G6DropForm.native_without_boxed_level
#print axioms G6DropForm.tracking_never_removed
#print axioms G6DropForm.removed_on_region
#print axioms G6DropForm.kept_exact_keeps_cut
#print axioms G6DropForm.monotone_in_K
#print axioms G6DropForm.kept_exact_keeps_cut_admitted
#print axioms G6DropForm.monotone_in_K_admitted
#print axioms G6DropForm.m4_native_breaks
#print axioms G6DropForm.m4_drop_form
#print axioms G6DropForm.native_not_prefix_closed
#print axioms G6DropForm.conj_keeps
#print axioms G6DropForm.conj_dropsValue
#print axioms G6DropForm.impl_is_drop_form
#print axioms G6DropForm.impl_non_candidate
#print axioms G6DropForm.drop_form_above_first
#print axioms G6DropForm.reference_is_drop_form
