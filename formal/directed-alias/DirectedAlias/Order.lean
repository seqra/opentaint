import DirectedAlias.Concept
import DirectedAlias.Examples
import DirectedAlias.Opt.Table

/-!
# The directed relation as an order

Today's DSU keeps a congruence: a symmetric, transitive relation that is closed under fields.
The directed design keeps an order: `p ⊒ q` ("p may hold each object that q may hold", the
edge `p → q`). This file proves that the order is reflexive, transitive, antisymmetric on the
canonical nodes of the optimization, and congruent (closed under fields). May-alias is not the
order itself. It is derived from it: two paths may alias if they have a common origin below
them. So the order is transitive, and may-alias is not.
-/

namespace DirectedAlias.Order

open DirectedAlias

/-- `Above S T`: the set `S` holds each origin of `T` (`S ⊒ T`). -/
def Above (S T : List Origin) : Prop := ∀ o, o ∈ T → o ∈ S

/-- Decidable form of `Above`. -/
def aboveB (S T : List Origin) : Bool := subB T S

/-- `aboveB` decides `Above`. -/
theorem aboveB_iff {S T : List Origin} : aboveB S T = true ↔ Above S T :=
  subB_iff

/-- The order is reflexive. -/
theorem above_refl (S : List Origin) : Above S S := fun _ h => h

/-- The order is transitive. -/
theorem above_trans {S T V : List Origin} (h1 : Above S T) (h2 : Above T V) : Above S V :=
  fun o h => h1 o (h2 o h)

/-- The order is antisymmetric on the nodes of a good table: two node ids that are above each
other are the same id. -/
theorem node_antisymm {U : List Origin} {T : Opt.Tbl} (g : T.Good U) {i j : Nat}
    (hi : i < T.size) (hj : j < T.size) (h1 : Above (T.mem i) (T.mem j))
    (h2 : Above (T.mem j) (T.mem i)) : i = j :=
  Opt.Tbl.id_inj g hi hj (fun o => ⟨h2 o, h1 o⟩)

/-- Congruence for one field: if `S ⊒ T`, then `S.c ⊒ T.c`. -/
theorem aread_mono (X : AState) {S T : List Origin} (c : ACell) (h : Above S T) :
    Above (aread X S c) (aread X T c) := by
  intro o ho
  obtain ⟨o', ho', hc⟩ := mem_aread.mp ho
  exact mem_aread.mpr ⟨o', h o' ho', hc⟩

/-- Congruence for a path: if `S ⊒ T`, then `S.p ⊒ T.p` for each path `p`. -/
theorem aevalFrom_mono (X : AState) :
    ∀ (p : List ACell) {S T : List Origin}, Above S T →
      Above (aevalFrom X S p) (aevalFrom X T p)
  | [], _, _, h => h
  | c :: cs, _, _, h => aevalFrom_mono X cs (aread_mono X c h)

/-- Congruence for variables: if `x ⊒ y`, then `x.p ⊒ y.p`. -/
theorem path_mono (X : AState) {x y : Var} (p : List ACell)
    (h : Above (X.env x) (X.env y)) : Above (aevalPath X x p) (aevalPath X y p) :=
  aevalFrom_mono X p h

/-- May-alias is derived from the order: two paths may alias if and only if one origin is
below both of them. -/
theorem may_iff_common_lower {X : AState} {x y : Var} {px py : List ACell} :
    may X x px y py = true ↔
      ∃ o, Above (aevalPath X x px) [o] ∧ Above (aevalPath X y py) [o] := by
  rw [may_iff]
  constructor
  · rintro ⟨o, h1, h2⟩
    refine ⟨o, ?_, ?_⟩ <;> intro o' h' <;> simp at h' <;> subst h' <;> assumption
  · rintro ⟨o, h1, h2⟩
    exact ⟨o, h1 o (by simp), h2 o (by simp)⟩

/-- A path that is above another path may alias it, if the lower path holds an origin. -/
theorem may_of_above {X : AState} {x y : Var} {px py : List ACell} {o : Origin}
    (h : Above (aevalPath X x px) (aevalPath X y py)) (ho : o ∈ aevalPath X y py) :
    may X x px y py = true :=
  may_iff.mpr ⟨o, h o ho, ho⟩

/-- A weak store adds `S` to cell `c` of each origin in `os`. -/
theorem weak_cell (X : AState) {os : List Origin} {o : Origin} (c : ACell) (S : List Origin)
    (h : o ∈ os) : (X.weakStore os c S).heap o c = uni S (X.heap o c) := by
  show (if c = c ∧ o ∈ os then uni S (X.heap o c) else X.heap o c) = _
  exact if_pos ⟨rfl, h⟩

/-- A strong store sets cell `c` of origin `o` to `S`. -/
theorem strong_cell (X : AState) (o : Origin) (c : ACell) (S : List Origin) :
    (X.setCell o c S).heap o c = S :=
  fupd2_same X.heap o c S

/-- A store writes down the order: after `x.c := S`, each set `T` below `x` that holds an
origin reads at least `S` in cell `c`. This holds for the strong and for the weak store. -/
theorem store_down (once : Site → Bool) (eu : Bool) (X : AState) (x : Var) (c : ACell)
    (S : List Origin) {T : List Origin} {o0 : Origin} (hT : Above (X.env x) T) (h0 : o0 ∈ T) :
    Above (aread (X.store once x c S eu) T c) S := by
  intro o hS
  apply mem_aread.mpr
  refine ⟨o0, h0, ?_⟩
  unfold AState.store
  split
  · rename_i o1 hs
    have h01 : o0 = o1 := (single?_spec hs).2 o0 (hT o0 h0)
    split
    · rw [h01, strong_cell]; exact hS
    · rw [weak_cell X c S (hT o0 h0)]; exact mem_uni.mpr (Or.inl hS)
  · rw [weak_cell X c S (hT o0 h0)]; exact mem_uni.mpr (Or.inl hS)

/-- Each symmetric relation that is also antisymmetric relates only equal elements. So a
symmetric relation (a DSU class) cannot hold `a ⊒ x` without merging `a` and `x`. -/
theorem symm_antisymm_eq {α : Type} (R : α → α → Prop) (hs : ∀ a b, R a b → R b a)
    (ha : ∀ a b, R a b → R b a → a = b) {a b : α} (h : R a b) : a = b :=
  ha a b h (hs a b h)

open DirectedAlias.Examples

/-- The analysis state after the task example `if (*) a = x else a = y`. -/
def sJoin : AState := analyzeProg 1 fr pJoin []

/-- Task example: `a ⊒ x` and `a ⊒ y`, but `x` and `y` are not ordered, and `x` is not above
`a`. The order holds the direction that a DSU loses. -/
theorem join_order :
    aboveB (sJoin.env va) (sJoin.env vx) = true ∧ aboveB (sJoin.env va) (sJoin.env vy) = true ∧
    aboveB (sJoin.env vx) (sJoin.env vy) = false ∧ aboveB (sJoin.env vy) (sJoin.env vx) = false ∧
    aboveB (sJoin.env vx) (sJoin.env va) = false := by
  decide

/-- The analysis state after the field example: the join, `a.f = z`, then `a = w`. -/
def sField : AState := analyzeProg 1 fr pField []

/-- Field example: after `a.f = z` and `a = w`, both `x.f ⊒ z` and `y.f ⊒ z` hold, `a` is no
longer above `x` or `y`, and `x`, `y` stay unordered. -/
theorem field_order :
    aboveB (aevalPath sField vx [.fld ff]) (sField.env vz) = true ∧
    aboveB (aevalPath sField vy [.fld ff]) (sField.env vz) = true ∧
    aboveB (sField.env va) (sField.env vx) = false ∧
    aboveB (sField.env va) (sField.env vy) = false ∧
    aboveB (sField.env vx) (sField.env vy) = false ∧
    aboveB (sField.env vy) (sField.env vx) = false := by
  decide

end DirectedAlias.Order
