import DirectedAlias.Opt.ValueSem

/-!
# The engine state: written entries, default content by rule (brief B, obligations 1 and 2)

The Kotlin engine stores a state as two finite maps:

* `env`: variable to origin set. An absent key is an unassigned variable (no origin). The two
  reserved keys `xe` (`Etree`) and `xv` (`Eval`) are keys of this map.
* `heap`: (origin, cell) to origin set. An absent key has the DEFAULT CONTENT BY RULE:
  `adefaultV` (the cell name `childCN`).

Here a finite map is an association list (`look`: the first entry wins). The denotation
`den K E` is a total model state (`AState`). The NORMAL FORM `NF` says that no visible entry is
its absent value: no env entry is empty, and no heap entry is set-equal to its default content.

Results:
* `nf_mapEq_iff`: for NF states, MAP EQUALITY (same key sets, set-equal values) is equivalent to
  equality of the denotations (set-equal at each variable and cell). `nf_mapEq_iff_on`: the same
  on the universe, for states whose keys are universe keys. `mapEqB_iff`: the test is decidable.
* The engine operations (`putV`, `weakE`, `storeE`, `joinE`, `retireE`) commute with `den` up
  to set equality (`den_*`), and keep NF (`NF_*`).
* `store_shortcut`: if `H(o, f) ⊆ pts(y)`, the strong and the weak store give the same state, so
  the engine skips the uniqueness test.
* RETIRE. The naive rule (`retireNaive`: merge only the written cells of `new(s)`) differs from
  the model `retireV` (`retireNaive_ne`: a concrete NF state). The corrected rule (`retireE`:
  iterate the written cells of `old(s)` AND of `new(s)`) commutes with `den` (`den_retireE`).
  The bug is latent: each state of the model analysis has the cell name in each cell of each
  `old(s)` (`OldDflt`, `oldDflt_analyzeVS`), and on such states the naive rule is correct too
  (`den_retireNaive_of_oldDflt`).
-/

namespace DirectedAlias.Impl.Engine

open DirectedAlias DirectedAlias.Opt DirectedAlias.Opt.Rec
open DirectedAlias.Sound.Recency DirectedAlias.Sound.HavocRecency DirectedAlias.Sound.CellNamed
open DirectedAlias.Sound.BlockOnly DirectedAlias.Sound.ValueSem

/-! ## Association lists -/

section alist

variable {κ : Type} [DecidableEq κ]

/-- The value of key `k` in the association list `l`; the first entry wins. -/
def look : List (κ × List Origin) → κ → Option (List Origin)
  | [], _ => none
  | p :: rest, k => if k = p.1 then some p.2 else look rest k

/-- Remove each entry with key `k`. -/
def eraseK : List (κ × List Origin) → κ → List (κ × List Origin)
  | [], _ => []
  | p :: rest, k => if p.1 = k then eraseK rest k else p :: eraseK rest k

/-- Set key `k` to `S`; if `drop k S` holds (the absent value), remove the key. -/
def put (drop : κ → List Origin → Bool) (l : List (κ × List Origin)) (k : κ) (S : List Origin) :
    List (κ × List Origin) :=
  cond (drop k S) (eraseK l k) ((k, S) :: eraseK l k)

/-- The map with keys `ks` and values `f`, without the entries that `drop` removes. -/
def mkMap (drop : κ → List Origin → Bool) (f : κ → List Origin) :
    List κ → List (κ × List Origin)
  | [] => []
  | k :: ks => cond (drop k (f k)) (mkMap drop f ks) ((k, f k) :: mkMap drop f ks)

/-- The keys of an association list. -/
def keys (l : List (κ × List Origin)) : List κ := l.map Prod.fst

/-- A visible entry is an entry of the list. -/
theorem look_mem : ∀ {l : List (κ × List Origin)} {k : κ} {S : List Origin},
    look l k = some S → (k, S) ∈ l
  | [], _, _, h => by cases h
  | p :: rest, k, S, h => by
    unfold look at h
    by_cases e : k = p.1
    · rw [ite_eq_left e] at h
      cases h
      subst e
      exact List.mem_cons_self
    · rw [ite_eq_right e] at h
      exact List.mem_cons_of_mem _ (look_mem h)

/-- A key is visible if and only if it is a key of the list. -/
theorem look_isSome_iff : ∀ {l : List (κ × List Origin)} {k : κ},
    (look l k).isSome = true ↔ k ∈ keys l
  | [], k => by simp [look, keys]
  | p :: rest, k => by
    unfold look
    by_cases e : k = p.1
    · rw [ite_eq_left e]
      subst e
      simp [keys]
    · rw [ite_eq_right e, look_isSome_iff]
      simp only [keys, List.map_cons, List.mem_cons]
      constructor
      · intro h; exact Or.inr h
      · rintro (h | h)
        · exact absurd h e
        · exact h

/-- A key is absent if and only if it is not a key of the list. -/
theorem look_none_iff {l : List (κ × List Origin)} {k : κ} :
    look l k = none ↔ k ∉ keys l := by
  rw [← look_isSome_iff]
  cases look l k <;> simp

/-- An absent key: the lookup gives none. -/
theorem look_none_of {l : List (κ × List Origin)} {k : κ} (h : k ∉ keys l) : look l k = none :=
  look_none_iff.mpr h

/-- A key of the list has a value. -/
theorem look_some_of {l : List (κ × List Origin)} {k : κ} (h : k ∈ keys l) :
    ∃ S, look l k = some S := by
  have := look_isSome_iff.mpr h
  cases e : look l k with
  | none => rw [e] at this; cases this
  | some S => exact ⟨S, rfl⟩

/-- The removed key is absent. -/
theorem look_eraseK_same : ∀ (l : List (κ × List Origin)) (k : κ), look (eraseK l k) k = none
  | [], _ => rfl
  | p :: rest, k => by
    unfold eraseK
    by_cases e : p.1 = k
    · rw [ite_eq_left e]; exact look_eraseK_same rest k
    · rw [ite_eq_right e]
      unfold look
      rw [ite_eq_right (fun h => e h.symm)]
      exact look_eraseK_same rest k

/-- The removal of a key does not change another key. -/
theorem look_eraseK_ne : ∀ (l : List (κ × List Origin)) {k k' : κ}, k' ≠ k →
    look (eraseK l k) k' = look l k'
  | [], _, _, _ => rfl
  | p :: rest, k, k', h => by
    unfold eraseK
    by_cases e : p.1 = k
    · rw [ite_eq_left e, look_eraseK_ne rest h]
      show look rest k' = (if k' = p.1 then some p.2 else look rest k')
      rw [ite_eq_right (fun h' => h (h'.trans e))]
    · rw [ite_eq_right e]
      unfold look
      by_cases e2 : k' = p.1
      · rw [ite_eq_left e2, ite_eq_left e2]
      · rw [ite_eq_right e2, ite_eq_right e2, look_eraseK_ne rest h]

/-- The removal of a key does not make the list longer. -/
theorem length_eraseK_le : ∀ (l : List (κ × List Origin)) (k : κ), (eraseK l k).length ≤ l.length
  | [], _ => Nat.le_refl _
  | p :: rest, k => by
    unfold eraseK
    have := length_eraseK_le rest k
    by_cases e : p.1 = k
    · rw [ite_eq_left e]; simp only [List.length_cons]; omega
    · rw [ite_eq_right e]; simp only [List.length_cons]; omega

/-- `put` at the key: the value, or absent if `drop` removes it. -/
theorem look_put_same (drop : κ → List Origin → Bool) (l : List (κ × List Origin)) (k : κ)
    (S : List Origin) : look (put drop l k S) k = cond (drop k S) none (some S) := by
  unfold put
  cases drop k S with
  | true => exact look_eraseK_same l k
  | false =>
    show (if k = k then some S else _) = some S
    rw [ite_eq_left rfl]

/-- `put` does not change another key. -/
theorem look_put_ne (drop : κ → List Origin → Bool) (l : List (κ × List Origin)) {k k' : κ}
    (S : List Origin) (h : k' ≠ k) : look (put drop l k S) k' = look l k' := by
  unfold put
  cases drop k S with
  | true => exact look_eraseK_ne l h
  | false =>
    show (if k' = k then some S else look (eraseK l k) k') = look l k'
    rw [ite_eq_right h, look_eraseK_ne l h]

/-- The value of a key in `mkMap`: the value of `f` if the key is in `ks` and `drop` keeps it,
else absent. -/
theorem look_mkMap_some (drop : κ → List Origin → Bool) (f : κ → List Origin) :
    ∀ (ks : List κ) {k : κ} {S : List Origin},
      look (mkMap drop f ks) k = some S ↔ k ∈ ks ∧ drop k (f k) = false ∧ f k = S
  | [], k, S => by simp [mkMap, look]
  | k0 :: ks, k, S => by
    unfold mkMap
    cases hd : drop k0 (f k0) with
    | true =>
      show look (mkMap drop f ks) k = some S ↔ _
      rw [look_mkMap_some drop f ks]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨List.mem_cons_of_mem _ h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        rcases List.mem_cons.mp h1 with e | e
        · subst e; rw [hd] at h2; cases h2
        · exact ⟨e, h2, h3⟩
    | false =>
      show (if k = k0 then some (f k0) else look (mkMap drop f ks) k) = some S ↔ _
      by_cases e : k = k0
      · rw [ite_eq_left e]
        subst e
        constructor
        · intro h; cases h; exact ⟨List.mem_cons_self, hd, rfl⟩
        · rintro ⟨_, _, h3⟩; rw [h3]
      · rw [ite_eq_right e, look_mkMap_some drop f ks]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨List.mem_cons_of_mem _ h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩
          rcases List.mem_cons.mp h1 with e' | e'
          · exact absurd e' e
          · exact ⟨e', h2, h3⟩

/-- A key that is not in `ks` is absent in `mkMap`. -/
theorem look_mkMap_nk (drop : κ → List Origin → Bool) (f : κ → List Origin) {ks : List κ}
    {k : κ} (h : k ∉ ks) : look (mkMap drop f ks) k = none := by
  cases e : look (mkMap drop f ks) k with
  | none => rfl
  | some S => exact absurd ((look_mkMap_some drop f ks).mp e).1 h

/-- The value of a key of `ks` in `mkMap`, with the absent value `d`: set-equal to `f k`, if
each value that `drop` removes is set-equal to `d`. -/
theorem getD_mkMap (drop : κ → List Origin → Bool) (f : κ → List Origin) {ks : List κ} {k : κ}
    (d : List Origin) (hd : drop k (f k) = true → SetEq (f k) d) (hk : k ∈ ks) :
    SetEq ((look (mkMap drop f ks) k).getD d) (f k) := by
  cases h : drop k (f k) with
  | false =>
    rw [(look_mkMap_some drop f ks).mpr ⟨hk, h, rfl⟩]
    exact SetEq.refl _
  | true =>
    cases e : look (mkMap drop f ks) k with
    | none => exact (hd h).symm
    | some S =>
      obtain ⟨_, h2, _⟩ := (look_mkMap_some drop f ks).mp e
      rw [h] at h2; cases h2

/-- Each visible entry of `mkMap` is kept by `drop`. -/
theorem drop_mkMap (drop : κ → List Origin → Bool) (f : κ → List Origin) (ks : List κ)
    {k : κ} {S : List Origin} (h : look (mkMap drop f ks) k = some S) : drop k S = false := by
  obtain ⟨_, h2, h3⟩ := (look_mkMap_some drop f ks).mp h
  rw [← h3]; exact h2

/-- `mkMap` has at most one entry for each key of `ks`. -/
theorem length_mkMap_le (drop : κ → List Origin → Bool) (f : κ → List Origin) :
    ∀ ks : List κ, (mkMap drop f ks).length ≤ ks.length
  | [] => Nat.le_refl _
  | k :: ks => by
    have := length_mkMap_le drop f ks
    unfold mkMap
    cases drop k (f k) with
    | true => show (mkMap drop f ks).length ≤ _; simp only [List.length_cons]; omega
    | false => show (mkMap drop f ks).length + 1 ≤ _; simp only [List.length_cons]; omega

end alist

/-! ## Set equality as a Boolean test -/

/-- Boolean set equality of two lists. -/
def setEqB (l m : List Origin) : Bool := subB l m && subB m l

/-- `setEqB` is set equality. -/
theorem setEqB_iff {l m : List Origin} : setEqB l m = true ↔ SetEq l m := by
  unfold setEqB
  rw [Bool.and_eq_true, subB_iff, subB_iff]
  constructor
  · rintro ⟨h1, h2⟩ a; exact ⟨h1 a, h2 a⟩
  · intro h; exact ⟨fun a => (h a).mp, fun a => (h a).mpr⟩

/-- Set-equal origin sets of states agree pointwise. -/
def DEq (X Y : AState) : Prop :=
  (∀ x, SetEq (X.env x) (Y.env x)) ∧ ∀ o c, SetEq (X.heap o c) (Y.heap o c)

/-- `DEq` is reflexive. -/
theorem DEq.refl (X : AState) : DEq X X := ⟨fun _ => SetEq.refl _, fun _ _ => SetEq.refl _⟩

/-- `DEq` is symmetric. -/
theorem DEq.symm {X Y : AState} (h : DEq X Y) : DEq Y X :=
  ⟨fun x => (h.1 x).symm, fun o c => (h.2 o c).symm⟩

/-- `DEq` is transitive. -/
theorem DEq.trans {X Y Z : AState} (h1 : DEq X Y) (h2 : DEq Y Z) : DEq X Z :=
  ⟨fun x => (h1.1 x).trans (h2.1 x), fun o c => (h1.2 o c).trans (h2.2 o c)⟩

/-! ## The engine state and its denotation -/

/-- The engine state: the written variables and the written heap cells. The reserved keys
`xe` and `xv` are keys of `env`. -/
structure EState where
  env : List (Var × List Origin)
  heap : List ((Origin × ACell) × List Origin)

/-- An env entry is absent if it is empty (an unassigned variable has no origin). -/
def dropV (_ : Var) (S : List Origin) : Bool := S.isEmpty

/-- A heap entry is absent if it is set-equal to the default content of its cell. -/
def dropH (K : Nat) (k : Origin × ACell) (S : List Origin) : Bool :=
  setEqB S (adefaultV K k.1 k.2)

/-- The origins of variable `x`: the entry, or none. -/
def getE (E : EState) (x : Var) : List Origin := (look E.env x).getD []

/-- The origins of cell `k`: the entry, or the default content by rule. -/
def getH (K : Nat) (E : EState) (k : Origin × ACell) : List Origin :=
  (look E.heap k).getD (adefaultV K k.1 k.2)

/-- The denotation of an engine state: a total model state. -/
def den (K : Nat) (E : EState) : AState where
  env := getE E
  heap := fun o c => getH K E (o, c)

/-- Normal form: no visible env entry is empty, and no visible heap entry is set-equal to the
default content of its cell. -/
def NF (K : Nat) (E : EState) : Prop :=
  (∀ x S, look E.env x = some S → S ≠ []) ∧
  ∀ k S, look E.heap k = some S → ¬ SetEq S (adefaultV K k.1 k.2)

/-- An entry that `dropV` keeps is not empty. -/
theorem dropV_false {x : Var} {S : List Origin} (h : dropV x S = false) : S ≠ [] := by
  intro e; subst e; cases h

/-- An entry that `dropH` keeps is not the default content. -/
theorem dropH_false {K : Nat} {k : Origin × ACell} {S : List Origin} (h : dropH K k S = false) :
    ¬ SetEq S (adefaultV K k.1 k.2) := by
  intro e; unfold dropH at h; rw [setEqB_iff.mpr e] at h; cases h

/-- A value that `dropV` removes is the absent value. -/
theorem dropV_true {x : Var} {S : List Origin} (h : dropV x S = true) : SetEq S [] := by
  cases S with
  | nil => exact SetEq.refl _
  | cons _ _ => cases h

/-- A value that `dropH` removes is set-equal to the default content. -/
theorem dropH_true {K : Nat} {k : Origin × ACell} {S : List Origin} (h : dropH K k S = true) :
    SetEq S (adefaultV K k.1 k.2) :=
  setEqB_iff.mp h

/-! ## Map equality and normal form (obligation 1) -/

/-- Map equality: the same keys, and set-equal values at each key. -/
def MapEq (E1 E2 : EState) : Prop :=
  (∀ x, (look E1.env x).isSome = (look E2.env x).isSome) ∧
  (∀ x S1 S2, look E1.env x = some S1 → look E2.env x = some S2 → SetEq S1 S2) ∧
  (∀ k, (look E1.heap k).isSome = (look E2.heap k).isSome) ∧
  (∀ k S1 S2, look E1.heap k = some S1 → look E2.heap k = some S2 → SetEq S1 S2)

/-- Map equality of one map, with absent value `d` and normal form `nf`, is equality of the
total functions. -/
theorem map_iff_fun {κ : Type} [DecidableEq κ] {l1 l2 : List (κ × List Origin)}
    (d : κ → List Origin) (n1 : ∀ k S, look l1 k = some S → ¬ SetEq S (d k))
    (n2 : ∀ k S, look l2 k = some S → ¬ SetEq S (d k)) :
    ((∀ k, (look l1 k).isSome = (look l2 k).isSome) ∧
      (∀ k S1 S2, look l1 k = some S1 → look l2 k = some S2 → SetEq S1 S2)) ↔
      ∀ k, SetEq ((look l1 k).getD (d k)) ((look l2 k).getD (d k)) := by
  constructor
  · rintro ⟨h1, h2⟩ k
    have hk := h1 k
    cases e1 : look l1 k with
    | none =>
      cases e2 : look l2 k with
      | none => exact SetEq.refl _
      | some S2 => rw [e1, e2] at hk; cases hk
    | some S1 =>
      cases e2 : look l2 k with
      | none => rw [e1, e2] at hk; cases hk
      | some S2 => exact h2 k S1 S2 e1 e2
  · intro h
    refine ⟨fun k => ?_, fun k S1 S2 e1 e2 => ?_⟩
    · have hk := h k
      cases e1 : look l1 k with
      | none =>
        cases e2 : look l2 k with
        | none => rfl
        | some S2 =>
          rw [e1, e2] at hk
          exact absurd hk.symm (n2 k S2 e2)
      | some S1 =>
        cases e2 : look l2 k with
        | none =>
          rw [e1, e2] at hk
          exact absurd hk (n1 k S1 e1)
        | some S2 => rfl
    · have hk := h k
      rw [e1, e2] at hk
      exact hk

/-- NORMAL FORM GIVES MAP EQUALITY: for NF states, the maps are equal (same keys, set-equal
values) if and only if the denotations are set-equal at each variable and each cell. -/
theorem nf_mapEq_iff {K : Nat} {E1 E2 : EState} (h1 : NF K E1) (h2 : NF K E2) :
    MapEq E1 E2 ↔ DEq (den K E1) (den K E2) := by
  have hv := map_iff_fun (l1 := E1.env) (l2 := E2.env) (fun _ => [])
    (fun k S e h => h1.1 k S e ((Opt.BlockOnly.setEq_nil h).mpr rfl))
    (fun k S e h => h2.1 k S e ((Opt.BlockOnly.setEq_nil h).mpr rfl))
  have hh := map_iff_fun (l1 := E1.heap) (l2 := E2.heap) (fun k => adefaultV K k.1 k.2)
    h1.2 h2.2
  constructor
  · rintro ⟨a, b, c, d⟩
    exact ⟨fun x => hv.mp ⟨a, b⟩ x, fun o c' => hh.mp ⟨c, d⟩ (o, c')⟩
  · rintro ⟨a, b⟩
    obtain ⟨a1, a2⟩ := hv.mpr a
    obtain ⟨b1, b2⟩ := hh.mpr (fun k => b k.1 k.2)
    exact ⟨a1, a2, b1, b2⟩

/-- The keys of an engine state are universe keys. -/
def KeysU (ctx : Ctx) (E : EState) : Prop :=
  (∀ x ∈ keys E.env, x ∈ ctx.vars) ∧ ∀ k ∈ keys E.heap, k.1 ∈ ctx.origins ∧ k.2 ∈ ctx.cells

/-- Set equality of two states on the universe. -/
def DEqOn (ctx : Ctx) (X Y : AState) : Prop :=
  (∀ x ∈ ctx.vars, SetEq (X.env x) (Y.env x)) ∧
  ∀ o ∈ ctx.origins, ∀ c ∈ ctx.cells, SetEq (X.heap o c) (Y.heap o c)

/-- On universe keys, equality on the universe is equality everywhere: outside the universe both
states hold the absent values. -/
theorem deq_of_on {ctx : Ctx} {K : Nat} {E1 E2 : EState} (k1 : KeysU ctx E1) (k2 : KeysU ctx E2)
    (h : DEqOn ctx (den K E1) (den K E2)) : DEq (den K E1) (den K E2) := by
  refine ⟨fun x => ?_, fun o c => ?_⟩
  · by_cases hx : x ∈ ctx.vars
    · exact h.1 x hx
    · show SetEq (getE E1 x) (getE E2 x)
      unfold getE
      rw [look_none_of (fun m => hx (k1.1 x m)), look_none_of (fun m => hx (k2.1 x m))]
      exact SetEq.refl _
  · by_cases hu : o ∈ ctx.origins ∧ c ∈ ctx.cells
    · exact h.2 o hu.1 c hu.2
    · show SetEq (getH K E1 (o, c)) (getH K E2 (o, c))
      unfold getH
      rw [look_none_of (fun m => hu (k1.2 _ m)), look_none_of (fun m => hu (k2.2 _ m))]
      exact SetEq.refl _

/-- NORMAL FORM GIVES MAP EQUALITY ON THE UNIVERSE: for NF states with universe keys, the maps
are equal if and only if the denotations are set-equal on the universe. -/
theorem nf_mapEq_iff_on {ctx : Ctx} {E1 E2 : EState} (h1 : NF ctx.K E1) (h2 : NF ctx.K E2)
    (k1 : KeysU ctx E1) (k2 : KeysU ctx E2) :
    MapEq E1 E2 ↔ DEqOn ctx (den ctx.K E1) (den ctx.K E2) := by
  rw [nf_mapEq_iff h1 h2]
  constructor
  · intro h; exact ⟨fun x _ => h.1 x, fun o _ c _ => h.2 o c⟩
  · exact deq_of_on k1 k2

/-! ## The decidable change test -/

/-- Map equality test of one map: each key of `l1` has a set-equal value in `l2`, and each key
of `l2` is a key of `l1`. -/
def entEqB {κ : Type} [DecidableEq κ] (l1 l2 : List (κ × List Origin)) : Bool :=
  l1.all (fun p => match look l1 p.1, look l2 p.1 with
    | some S1, some S2 => setEqB S1 S2
    | _, _ => false) &&
  l2.all (fun p => (look l1 p.1).isSome)

/-- The map equality test of two engine states. -/
def mapEqB (E1 E2 : EState) : Bool := entEqB E1.env E2.env && entEqB E1.heap E2.heap

/-- The test of one map is map equality of that map. -/
theorem entEqB_iff {κ : Type} [DecidableEq κ] {l1 l2 : List (κ × List Origin)} :
    entEqB l1 l2 = true ↔
      (∀ k, (look l1 k).isSome = (look l2 k).isSome) ∧
      (∀ k S1 S2, look l1 k = some S1 → look l2 k = some S2 → SetEq S1 S2) := by
  unfold entEqB
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    have hk1 : ∀ k S1, look l1 k = some S1 → ∃ S2, look l2 k = some S2 ∧ SetEq S1 S2 := by
      intro k S1 e1
      have hm := look_mem e1
      have := h1 _ hm
      simp only at this
      rw [e1] at this
      cases e2 : look l2 k with
      | none => rw [e2] at this; cases this
      | some S2 => rw [e2] at this; exact ⟨S2, rfl, setEqB_iff.mp this⟩
    refine ⟨fun k => ?_, fun k S1 S2 e1 e2 => ?_⟩
    · cases e1 : look l1 k with
      | some S1 =>
        obtain ⟨S2, e2, _⟩ := hk1 k S1 e1
        rw [e2]; rfl
      | none =>
        cases e2 : look l2 k with
        | none => rfl
        | some S2 =>
          have := h2 _ (look_mem e2)
          simp only at this
          rw [e1] at this; cases this
    · obtain ⟨S2', e2', h⟩ := hk1 k S1 e1
      rw [e2] at e2'; cases e2'; exact h
  · rintro ⟨h1, h2⟩
    constructor
    · intro p hp
      have hk : p.1 ∈ keys l1 := List.mem_map.mpr ⟨p, hp, rfl⟩
      obtain ⟨S1, e1⟩ := look_some_of hk
      have hs := h1 p.1
      rw [e1] at hs
      cases e2 : look l2 p.1 with
      | none => rw [e2] at hs; cases hs
      | some S2 =>
        rw [e1]
        exact setEqB_iff.mpr (h2 p.1 S1 S2 e1 e2)
    · intro p hp
      have hk : p.1 ∈ keys l2 := List.mem_map.mpr ⟨p, hp, rfl⟩
      rw [h1 p.1]
      exact look_isSome_iff.mpr hk

/-- THE CHANGE TEST IS DECIDABLE: `mapEqB` is map equality. -/
theorem mapEqB_iff {E1 E2 : EState} : mapEqB E1 E2 = true ↔ MapEq E1 E2 := by
  unfold mapEqB MapEq
  rw [Bool.and_eq_true, entEqB_iff, entEqB_iff]
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨a, b, c, d⟩
  · rintro ⟨a, b, c, d⟩; exact ⟨⟨a, b⟩, c, d⟩

/-- Map equality is decidable. -/
instance (E1 E2 : EState) : Decidable (MapEq E1 E2) :=
  decidable_of_iff _ mapEqB_iff

/-- THE FIXPOINT CHANGE TEST: for NF states, `mapEqB` decides the set equality of the
denotations. -/
theorem mapEqB_iff_den {K : Nat} {E1 E2 : EState} (h1 : NF K E1) (h2 : NF K E2) :
    mapEqB E1 E2 = true ↔ DEq (den K E1) (den K E2) :=
  mapEqB_iff.trans (nf_mapEq_iff h1 h2)

/-! ## Variable and cell updates -/

/-- Set variable `x` to `S` (remove the key if `S` is empty). -/
def putV (E : EState) (x : Var) (S : List Origin) : EState :=
  { E with env := put dropV E.env x S }

/-- Set cell `k` to `S` (remove the key if `S` is the default content). -/
def putH (K : Nat) (E : EState) (k : Origin × ACell) (S : List Origin) : EState :=
  { E with heap := put (dropH K) E.heap k S }

/-- `putV` sets the variable. -/
theorem getE_putV_same (E : EState) (x : Var) (S : List Origin) : getE (putV E x S) x = S := by
  unfold getE putV
  simp only
  rw [look_put_same]
  cases h : dropV x S with
  | true => cases S with
    | nil => rfl
    | cons _ _ => cases h
  | false => rfl

/-- `putV` keeps the other variables. -/
theorem getE_putV_ne (E : EState) {x y : Var} (S : List Origin) (h : y ≠ x) :
    getE (putV E x S) y = getE E y := by
  unfold getE putV
  simp only
  rw [look_put_ne _ _ _ h]

/-- `putV` keeps the heap. -/
theorem getH_putV (K : Nat) (E : EState) (x : Var) (S : List Origin) (k : Origin × ACell) :
    getH K (putV E x S) k = getH K E k := rfl

/-- `putH` sets the cell, up to set equality. -/
theorem getH_putH_same (K : Nat) (E : EState) (k : Origin × ACell) (S : List Origin) :
    SetEq (getH K (putH K E k S) k) S := by
  unfold getH putH
  simp only
  rw [look_put_same]
  cases h : dropH K k S with
  | true => exact (dropH_true h).symm
  | false => exact SetEq.refl _

/-- `putH` keeps the other cells. -/
theorem getH_putH_ne (K : Nat) (E : EState) {k k' : Origin × ACell} (S : List Origin)
    (h : k' ≠ k) : getH K (putH K E k S) k' = getH K E k' := by
  unfold getH putH
  simp only
  rw [look_put_ne _ _ _ h]

/-- `putH` keeps the variables. -/
theorem getE_putH (K : Nat) (E : EState) (k : Origin × ACell) (S : List Origin) (x : Var) :
    getE (putH K E k S) x = getE E x := rfl

/-- `putV` keeps the normal form. -/
theorem NF_putV {K : Nat} {E : EState} (h : NF K E) (x : Var) (S : List Origin) :
    NF K (putV E x S) := by
  refine ⟨fun y T e => ?_, h.2⟩
  by_cases hy : y = x
  · subst hy
    change look (put dropV E.env y S) y = some T at e
    rw [look_put_same] at e
    cases hd : dropV y S with
    | true => rw [hd] at e; cases e
    | false => rw [hd] at e; cases e; exact dropV_false hd
  · change look (put dropV E.env x S) y = some T at e
    rw [look_put_ne _ _ _ hy] at e
    exact h.1 y T e

/-- `putH` keeps the normal form. -/
theorem NF_putH {K : Nat} {E : EState} (h : NF K E) (k : Origin × ACell) (S : List Origin) :
    NF K (putH K E k S) := by
  refine ⟨h.1, fun k' T e => ?_⟩
  by_cases hk : k' = k
  · subst hk
    change look (put (dropH K) E.heap k' S) k' = some T at e
    rw [look_put_same] at e
    cases hd : dropH K k' S with
    | true => rw [hd] at e; cases e
    | false => rw [hd] at e; cases e; exact dropH_false hd
  · change look (put (dropH K) E.heap k S) k' = some T at e
    rw [look_put_ne _ _ _ hk] at e
    exact h.2 k' T e

/-- `putV` commutes with the denotation. -/
theorem den_putV (K : Nat) (E : EState) (x : Var) (S : List Origin) :
    DEq (den K (putV E x S)) ((den K E).setVar x S) := by
  refine ⟨fun y => ?_, fun o c => SetEq.refl _⟩
  show SetEq (getE (putV E x S) y) (fupd (getE E) x S y)
  by_cases hy : y = x
  · subst hy; rw [getE_putV_same, fupd_same]; exact SetEq.refl _
  · rw [getE_putV_ne _ _ hy, fupd_ne _ _ hy]; exact SetEq.refl _

/-- `putH` commutes with the denotation. -/
theorem den_putH (K : Nat) (E : EState) (o : Origin) (c : ACell) (S : List Origin) :
    DEq (den K (putH K E (o, c) S)) ((den K E).setCell o c S) := by
  refine ⟨fun y => SetEq.refl _, fun o' c' => ?_⟩
  show SetEq (getH K (putH K E (o, c) S) (o', c')) (fupd2 (fun o c => getH K E (o, c)) o c S o' c')
  by_cases e : o' = o ∧ c' = c
  · obtain ⟨rfl, rfl⟩ := e
    rw [fupd2_same]
    exact getH_putH_same K E _ S
  · rw [fupd2_ne _ _ e]
    have : (o', c') ≠ (o, c) := fun h => e ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    rw [getH_putH_ne K E S this]
    exact SetEq.refl _

/-- Setting the optional result variable. -/
def setRetE (E : EState) : Option Var → List Origin → EState
  | none, _ => E
  | some x, S => putV E x S

/-- `setRetE` commutes with the denotation. -/
theorem den_setRetE (K : Nat) (E : EState) (r : Option Var) (S : List Origin) :
    DEq (den K (setRetE E r S)) ((den K E).setRet r S) := by
  cases r with
  | none => exact DEq.refl _
  | some x => exact den_putV K E x S

/-- `setRetE` keeps the normal form. -/
theorem NF_setRetE {K : Nat} {E : EState} (h : NF K E) (r : Option Var) (S : List Origin) :
    NF K (setRetE E r S) := by
  cases r with
  | none => exact h
  | some x => exact NF_putV h x S

/-! ## Model-side congruences -/

/-- `setVar` keeps `DEq`. -/
theorem DEq.setVar {X Y : AState} (h : DEq X Y) (x : Var) {S S' : List Origin}
    (hS : SetEq S S') : DEq (X.setVar x S) (Y.setVar x S') := by
  refine ⟨fun y => ?_, h.2⟩
  show SetEq (fupd X.env x S y) (fupd Y.env x S' y)
  by_cases hy : y = x
  · subst hy; rw [fupd_same, fupd_same]; exact hS
  · rw [fupd_ne _ _ hy, fupd_ne _ _ hy]; exact h.1 y

/-- `setRet` keeps `DEq`. -/
theorem DEq.setRet {X Y : AState} (h : DEq X Y) (r : Option Var) (S : List Origin) :
    DEq (X.setRet r S) (Y.setRet r S) := by
  cases r with
  | none => exact h
  | some x => exact h.setVar x (SetEq.refl S)

/-- `setCell` keeps `DEq`. -/
theorem DEq.setCell {X Y : AState} (h : DEq X Y) (o : Origin) (c : ACell) {S S' : List Origin}
    (hS : SetEq S S') : DEq (X.setCell o c S) (Y.setCell o c S') := by
  refine ⟨h.1, fun o' c' => ?_⟩
  show SetEq (fupd2 X.heap o c S o' c') (fupd2 Y.heap o c S' o' c')
  by_cases e : o' = o ∧ c' = c
  · obtain ⟨rfl, rfl⟩ := e; rw [fupd2_same, fupd2_same]; exact hS
  · rw [fupd2_ne _ _ e, fupd2_ne _ _ e]; exact h.2 o' c'

/-- `weakStore` keeps `DEq`. -/
theorem DEq.weakStore {X Y : AState} (h : DEq X Y) {os os' : List Origin} (ho : SetEq os os')
    (c : ACell) {S S' : List Origin} (hS : SetEq S S') :
    DEq (X.weakStore os c S) (Y.weakStore os' c S') := by
  refine ⟨h.1, fun o' c' => ?_⟩
  show SetEq (if c' = c ∧ o' ∈ os then uni S (X.heap o' c') else X.heap o' c')
    (if c' = c ∧ o' ∈ os' then uni S' (Y.heap o' c') else Y.heap o' c')
  by_cases e : c' = c ∧ o' ∈ os
  · rw [ite_eq_left e, ite_eq_left ⟨e.1, (ho o').mp e.2⟩]
    exact SetEq.uni hS (h.2 o' c')
  · have e' : ¬ (c' = c ∧ o' ∈ os') := fun h' => e ⟨h'.1, (ho o').mpr h'.2⟩
    rw [ite_eq_right e, ite_eq_right e']
    exact h.2 o' c'

/-- `aread` gives set-equal results on `DEq` states and set-equal sets. -/
theorem DEq.aread {X Y : AState} (h : DEq X Y) {S S' : List Origin} (hS : SetEq S S')
    (c : ACell) : SetEq (DirectedAlias.aread X S c) (DirectedAlias.aread Y S' c) := by
  intro a
  rw [mem_aread, mem_aread]
  constructor
  · rintro ⟨o, ho, ha⟩; exact ⟨o, (hS o).mp ho, (h.2 o c a).mp ha⟩
  · rintro ⟨o, ho, ha⟩; exact ⟨o, (hS o).mpr ho, (h.2 o c a).mpr ha⟩

/-! ## Load, weak store, store (obligation 2) -/

/-- The engine read: `⋃ H(o, c)` over `o ∈ S`, reading an absent key by rule. -/
def readE (K : Nat) (E : EState) (S : List Origin) (c : ACell) : List Origin :=
  uniMap (fun o => getH K E (o, c)) S

/-- The engine read is the model read of the denotation. -/
theorem readE_eq (K : Nat) (E : EState) (S : List Origin) (c : ACell) :
    readE K E S c = DirectedAlias.aread (den K E) S c := rfl

/-- The engine weak store: add `S` to cell `c` of each origin of the list. -/
def weakE (K : Nat) (c : ACell) (S : List Origin) : EState → List Origin → EState
  | E, [] => E
  | E, o :: os => weakE K c S (putH K E (o, c) (uni S (getH K E (o, c)))) os

/-- The engine weak store keeps the normal form. -/
theorem NF_weakE {K : Nat} (c : ACell) (S : List Origin) :
    ∀ {E : EState} (os : List Origin), NF K E → NF K (weakE K c S E os)
  | _, [], h => h
  | _, _ :: os, h => NF_weakE c S os (NF_putH h _ _)

/-- The engine weak store keeps the variables. -/
theorem getE_weakE (K : Nat) (c : ACell) (S : List Origin) :
    ∀ (E : EState) (os : List Origin) (x : Var), getE (weakE K c S E os) x = getE E x
  | _, [], _ => rfl
  | E, _ :: os, x => (getE_weakE K c S _ os x).trans (getE_putH K E _ _ x)

/-- The engine weak store commutes with the denotation. -/
theorem den_weakE (K : Nat) (c : ACell) (S : List Origin) :
    ∀ (E : EState) (os : List Origin), DEq (den K (weakE K c S E os)) ((den K E).weakStore os c S)
  | E, [] => by
    refine ⟨fun x => SetEq.refl _, fun o' c' => ?_⟩
    show SetEq (getH K E (o', c')) (if c' = c ∧ o' ∈ ([] : List Origin) then _ else getH K E (o', c'))
    rw [ite_eq_right (fun h => by cases h.2)]
    exact SetEq.refl _
  | E, o :: os => by
    have ih := den_weakE K c S (putH K E (o, c) (uni S (getH K E (o, c)))) os
    refine ih.trans ⟨fun x => SetEq.refl _, fun o' c' => ?_⟩
    show SetEq (if c' = c ∧ o' ∈ os then uni S (getH K (putH K E (o, c) _) (o', c'))
        else getH K (putH K E (o, c) _) (o', c'))
      (if c' = c ∧ o' ∈ o :: os then uni S (getH K E (o', c')) else getH K E (o', c'))
    by_cases e : o' = o ∧ c' = c
    · obtain ⟨rfl, rfl⟩ := e
      have h1 := getH_putH_same K E (o', c') (uni S (getH K E (o', c')))
      rw [ite_eq_left (show c' = c' ∧ o' ∈ o' :: os from ⟨rfl, List.mem_cons_self⟩)]
      by_cases hm : o' ∈ os
      · rw [ite_eq_left ⟨rfl, hm⟩]
        intro a
        rw [mem_uni, h1 a, mem_uni]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact h
        · intro h; exact Or.inr h
      · rw [ite_eq_right (fun h => hm h.2)]
        exact h1
    · have hne : (o', c') ≠ (o, c) := fun h => e ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      rw [getH_putH_ne K E _ hne]
      by_cases hc : c' = c
      · subst hc
        have ho : o' ≠ o := fun h => e ⟨h, rfl⟩
        have hiff : o' ∈ os ↔ o' ∈ o :: os := by
          rw [List.mem_cons]
          constructor
          · exact Or.inr
          · rintro (h | h)
            · exact absurd h ho
            · exact h
        by_cases hm : o' ∈ os
        · rw [ite_eq_left ⟨rfl, hm⟩, ite_eq_left ⟨rfl, hiff.mp hm⟩]; exact SetEq.refl _
        · rw [ite_eq_right (fun h => hm h.2), ite_eq_right (fun h => hm (hiff.mpr h.2))]
          exact SetEq.refl _
      · rw [ite_eq_right (fun h => hc h.1), ite_eq_right (fun h => hc h.1)]
        exact SetEq.refl _

/-- THE STORE SHORTCUT: if the target has one origin `o` and `H(o, c) ⊆ S`, the strong store and
the weak store give set-equal states. So the uniqueness test can be skipped. -/
theorem store_shortcut {X : AState} {x : Var} {o : Origin} {c : ACell} {S : List Origin}
    (hx : single? (X.env x) = some o) (hsub : X.heap o c ⊆ S) :
    DEq (X.setCell o c S) (X.weakStore (X.env x) c S) := by
  have hall := single?_spec hx
  refine ⟨fun y => SetEq.refl _, fun o' c' => ?_⟩
  show SetEq (fupd2 X.heap o c S o' c')
    (if c' = c ∧ o' ∈ X.env x then uni S (X.heap o' c') else X.heap o' c')
  by_cases e : o' = o ∧ c' = c
  · obtain ⟨rfl, rfl⟩ := e
    rw [fupd2_same, ite_eq_left ⟨rfl, hall.1⟩]
    intro a
    rw [mem_uni]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exact hsub h
  · rw [fupd2_ne _ _ e]
    have : ¬ (c' = c ∧ o' ∈ X.env x) := fun h => e ⟨hall.2 o' h.2, h.1⟩
    rw [ite_eq_right this]
    exact SetEq.refl _

/-- The engine store of design VS: strong if the target has one origin `o` and either
`H(o, c) ⊆ S` (the shortcut: the test is skipped) or `o` is unique for `Etree` and `Eval`;
else weak. -/
def storeE (cb : CtxB) (E : EState) (x : Var) (c : ACell) (S : List Origin) : EState :=
  match single? (getE E x) with
  | some o =>
    if subB (getH cb.cn.ctx.K E (o, c)) S = true then putH cb.cn.ctx.K E (o, c) S
    else if uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (getE E cb.cn.xe) (getE E cb.xv) o = true
      then putH cb.cn.ctx.K E (o, c) S
      else weakE cb.cn.ctx.K c S E (getE E x)
  | none => weakE cb.cn.ctx.K c S E (getE E x)

/-- The engine store commutes with the denotation: it is the store of design VS. -/
theorem den_storeE (cb : CtxB) (E : EState) (x : Var) (c : ACell) (S : List Origin) :
    DEq (den cb.cn.ctx.K (storeE cb E x c S)) (storeBO cb (den cb.cn.ctx.K E) x c S) := by
  unfold storeE storeBO
  show DEq _ (match single? (getE E x) with
    | some o => if uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (getE E cb.cn.xe)
        (getE E cb.xv) o = true then (den cb.cn.ctx.K E).setCell o c S
        else (den cb.cn.ctx.K E).weakStore (getE E x) c S
    | none => (den cb.cn.ctx.K E).weakStore (getE E x) c S)
  cases hs : single? (getE E x) with
  | none => exact den_weakE _ c S E _
  | some o =>
    simp only
    by_cases hsub : subB (getH cb.cn.ctx.K E (o, c)) S = true
    · rw [ite_eq_left hsub]
      have h1 := den_putH cb.cn.ctx.K E o c S
      by_cases hu : uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (getE E cb.cn.xe)
          (getE E cb.xv) o = true
      · rw [ite_eq_left hu]; exact h1
      · rw [ite_eq_right hu]
        exact h1.trans (store_shortcut (X := den cb.cn.ctx.K E) hs (subB_iff.mp hsub))
    · rw [ite_eq_right hsub]
      by_cases hu : uniqueBO cb.cn.ctx.once cb.cn.ctx.entryUnique (getE E cb.cn.xe)
          (getE E cb.xv) o = true
      · rw [ite_eq_left hu, ite_eq_left hu]; exact den_putH cb.cn.ctx.K E o c S
      · rw [ite_eq_right hu, ite_eq_right hu]; exact den_weakE _ c S E _

/-- The engine store keeps the normal form. -/
theorem NF_storeE (cb : CtxB) {E : EState} (h : NF cb.cn.ctx.K E) (x : Var) (c : ACell)
    (S : List Origin) : NF cb.cn.ctx.K (storeE cb E x c S) := by
  unfold storeE
  cases single? (getE E x) with
  | none => exact NF_weakE c S _ h
  | some o =>
    simp only
    split
    · exact NF_putH h _ _
    · split
      · exact NF_putH h _ _
      · exact NF_weakE c S _ h

/-! ## Join (obligation 2) -/

/-- The engine join: the keys of either map; an absent key on one side gives its absent value;
the result is normalized. -/
def joinE (K : Nat) (E1 E2 : EState) : EState where
  env := mkMap dropV (fun x => uni (getE E1 x) (getE E2 x)) (keys E1.env ++ keys E2.env)
  heap := mkMap (dropH K) (fun k => uni (getH K E1 k) (getH K E2 k)) (keys E1.heap ++ keys E2.heap)

/-- The engine join keeps (makes) the normal form. -/
theorem NF_joinE (K : Nat) (E1 E2 : EState) : NF K (joinE K E1 E2) :=
  ⟨fun _ _ e => dropV_false (drop_mkMap _ _ _ e), fun _ _ e => dropH_false (drop_mkMap _ _ _ e)⟩

/-- The engine join commutes with the denotation: it is the pointwise union. -/
theorem den_joinE (K : Nat) (E1 E2 : EState) :
    DEq (den K (joinE K E1 E2)) (join (den K E1) (den K E2)) := by
  refine ⟨fun x => ?_, fun o c => ?_⟩
  · show SetEq ((look (mkMap dropV _ (keys E1.env ++ keys E2.env)) x).getD [])
      (uni (getE E1 x) (getE E2 x))
    by_cases hk : x ∈ keys E1.env ++ keys E2.env
    · exact getD_mkMap _ _ [] (fun h => dropV_true h) hk
    · rw [look_mkMap_nk _ _ hk]
      have h1 : x ∉ keys E1.env := fun h => hk (List.mem_append_left _ h)
      have h2 : x ∉ keys E2.env := fun h => hk (List.mem_append_right _ h)
      unfold getE
      rw [look_none_of h1, look_none_of h2]
      intro a; simp [uni]
  · show SetEq ((look (mkMap (dropH K) _ (keys E1.heap ++ keys E2.heap)) (o, c)).getD
        (adefaultV K o c)) (uni (getH K E1 (o, c)) (getH K E2 (o, c)))
    by_cases hk : (o, c) ∈ keys E1.heap ++ keys E2.heap
    · exact getD_mkMap _ _ _ (fun h => dropH_true h) hk
    · rw [look_mkMap_nk _ _ hk]
      have h1 : (o, c) ∉ keys E1.heap := fun h => hk (List.mem_append_left _ h)
      have h2 : (o, c) ∉ keys E2.heap := fun h => hk (List.mem_append_right _ h)
      unfold getH
      rw [look_none_of h1, look_none_of h2]
      exact (uni_self_set _).symm

/-! ## Retire (obligation 2): the suspected design bug -/

/-- The renamed key of `retire`: a cell of `new(s)` becomes the cell of `old(s)`. -/
def rkey (s : Site) (k : Origin × ACell) : Origin × ACell := (renameO s k.1, k.2)

/-- The value of a renamed key after the corrected retire: the cell of `old(s)` gets the union
of the two cells (each read by rule); each other cell is renamed. -/
def retireF (K : Nat) (s : Site) (E : EState) (k : Origin × ACell) : List Origin :=
  if k.1 = rOld s then renameL s (uni (getH K E (rNew s, k.2)) (getH K E (rOld s, k.2)))
  else renameL s (getH K E k)

/-- THE CORRECTED RETIRE: rename `new(s)` to `old(s)` in each node (the reserved keys included);
iterate the union of the written cells of `old(s)` and of `new(s)`; remove the cells of
`new(s)`. -/
def retireE (K : Nat) (s : Site) (E : EState) : EState where
  env := E.env.map (fun p => (p.1, renameL s p.2))
  heap := mkMap (dropH K) (retireF K s E) ((keys E.heap).map (rkey s))

/-- The value of the cell of `old(s)` in the naive rule: the union only if the cell of `new(s)`
is written. -/
def retireNaiveF (K : Nat) (s : Site) (E : EState) (k : Origin × ACell) : List Origin :=
  if k.1 = rOld s ∧ (rNew s, k.2) ∈ keys E.heap then
    renameL s (uni (getH K E (rNew s, k.2)) (getH K E (rOld s, k.2)))
  else renameL s (getH K E k)

/-- THE NAIVE RETIRE of the earlier design text: for each written cell `c` of `new(s)`,
`heap[old(s), c] := H(old, c) ∪ H(new, c)` and remove `(new(s), c)`; rename each node. -/
def retireNaive (K : Nat) (s : Site) (E : EState) : EState where
  env := E.env.map (fun p => (p.1, renameL s p.2))
  heap := mkMap (dropH K) (retireNaiveF K s E) ((keys E.heap).map (rkey s))

/-- The renamed env: the lookup of a renamed map. -/
theorem look_map_rename (s : Site) :
    ∀ (l : List (Var × List Origin)) (x : Var),
      look (l.map (fun p => (p.1, renameL s p.2))) x = (look l x).map (renameL s)
  | [], _ => rfl
  | p :: rest, x => by
    show (if x = p.1 then some (renameL s p.2) else _) = (if x = p.1 then some p.2 else _).map _
    by_cases e : x = p.1
    · rw [ite_eq_left e, ite_eq_left e]; rfl
    · rw [ite_eq_right e, ite_eq_right e]; exact look_map_rename s rest x

/-- The env of both retire rules is the renamed env. -/
theorem getE_retire_env (s : Site) (l : List (Var × List Origin)) (x : Var) :
    (look (l.map (fun p => (p.1, renameL s p.2))) x).getD [] = renameL s ((look l x).getD []) := by
  rw [look_map_rename]
  cases look l x <;> rfl

/-- A key is a renamed key if and only if it comes from a written key. -/
theorem mem_rkeys {s : Site} {l : List (Origin × ACell)} {o : Origin} {c : ACell} :
    (o, c) ∈ l.map (rkey s) ↔ ∃ o', (o', c) ∈ l ∧ renameO s o' = o := by
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨o', c'⟩, h, e⟩
    cases e
    exact ⟨o', h, rfl⟩
  · rintro ⟨o', h, rfl⟩
    exact ⟨(o', c), h, rfl⟩

/-- A cell name is not changed by the retire renaming. -/
theorem renameL_child (K : Nat) (s : Site) (o : Origin) (c : ACell) :
    renameL s [childCN K o c] = [childCN K o c] := by
  show [renameO s (childCN K o c)] = _
  rw [renameO_of_ne_alloc s (childCN_ne_alloc K o c)]

/-- The env part of both retire rules commutes with the denotation. -/
theorem retire_env_eq (K : Nat) (s : Site) (E : EState) (x : Var) :
    (look (E.env.map (fun p => (p.1, renameL s p.2))) x).getD [] =
      (retireV K s (den K E)).env x :=
  getE_retire_env s E.env x

/-- RETIRE RENAMES THE RESERVED KEYS TOO: the `Etree` and `Eval` sets of the engine retire are
the renamed sets. -/
theorem retireE_env (K : Nat) (s : Site) (E : EState) (x : Var) :
    getE (retireE K s E) x = renameL s (getE E x) :=
  getE_retire_env s E.env x

/-- A renamed env keeps the normal form of the env. -/
theorem NF_env_rename {E : EState} (h : ∀ x S, look E.env x = some S → S ≠ []) (s : Site) :
    ∀ x S, look (E.env.map (fun p => (p.1, renameL s p.2))) x = some S → S ≠ [] := by
  intro x S e
  rw [look_map_rename] at e
  cases e2 : look E.env x with
  | none => rw [e2] at e; cases e
  | some T =>
    rw [e2] at e
    cases e
    intro h0
    have := congrArg List.length h0
    rw [length_renameL] at this
    exact h x T e2 (List.eq_nil_of_length_eq_zero this)

/-- The corrected retire keeps the normal form. -/
theorem NF_retireE {K : Nat} {E : EState} (h : NF K E) (s : Site) : NF K (retireE K s E) :=
  ⟨NF_env_rename h.1 s, fun _ _ e => dropH_false (drop_mkMap _ _ _ e)⟩

/-- THE CORRECTED RETIRE COMMUTES WITH THE DENOTATION: it is `retireV` of design VS. -/
theorem den_retireE (K : Nat) (s : Site) (E : EState) :
    DEq (den K (retireE K s E)) (retireV K s (den K E)) := by
  refine ⟨fun x => ?_, fun o c => ?_⟩
  · show SetEq ((look (E.env.map (fun p => (p.1, renameL s p.2))) x).getD []) _
    rw [retire_env_eq]; exact SetEq.refl _
  · show SetEq ((look (mkMap (dropH K) (retireF K s E) ((keys E.heap).map (rkey s))) (o, c)).getD
        (adefaultV K o c))
      (if o = rNew s then [childCN K (rNew s) c] else (retire s (den K E)).heap o c)
    by_cases hn : o = rNew s
    · subst hn
      rw [ite_eq_left rfl]
      have : (rNew s, c) ∉ (keys E.heap).map (rkey s) := by
        intro h
        obtain ⟨o', _, e⟩ := mem_rkeys.mp h
        exact renameO_ne_new s o' e
      rw [look_mkMap_nk _ _ this]
      exact SetEq.refl _
    · rw [ite_eq_right hn]
      show SetEq _ (if o = rNew s then [] else if o = rOld s then
        renameL s (uni (getH K E (rNew s, c)) (getH K E (rOld s, c)))
        else renameL s (getH K E (o, c)))
      rw [ite_eq_right hn]
      by_cases hk : (o, c) ∈ (keys E.heap).map (rkey s)
      · have := getD_mkMap (dropH K) (retireF K s E) (adefaultV K o c) (fun h => dropH_true h) hk
        refine this.trans ?_
        unfold retireF
        by_cases ho : o = rOld s
        · rw [ite_eq_left ho]; exact SetEq.refl _
        · rw [ite_eq_right ho]; exact SetEq.refl _
      · rw [look_mkMap_nk _ _ hk]
        by_cases ho : o = rOld s
        · subst ho
          rw [ite_eq_left rfl]
          have h1 : (rNew s, c) ∉ keys E.heap := fun h =>
            hk (mem_rkeys.mpr ⟨rNew s, h, by unfold renameO; rw [ite_eq_left rfl]⟩)
          have h2 : (rOld s, c) ∉ keys E.heap := fun h =>
            hk (mem_rkeys.mpr ⟨rOld s, h, by
              unfold renameO; rw [ite_eq_right (fun e => rNew_ne_rOld s e.symm)]⟩)
          unfold getH
          rw [look_none_of h1, look_none_of h2]
          show SetEq [childCN K (rOld s) c]
            (renameL s (uni [childCN K (rNew s) c] [childCN K (rOld s) c]))
          rw [← childCN_rOld K s c]
          have hu : uni [childCN K (rOld s) c] [childCN K (rOld s) c] = [childCN K (rOld s) c] := by
            simp [uni]
          rw [hu, renameL_child]
          exact SetEq.refl _
        · rw [ite_eq_right ho]
          have h1 : (o, c) ∉ keys E.heap := fun h => hk (mem_rkeys.mpr ⟨o, h, by
            unfold renameO; rw [ite_eq_right hn]⟩)
          unfold getH
          rw [look_none_of h1]
          show SetEq [childCN K o c] (renameL s [childCN K o c])
          rw [renameL_child]
          exact SetEq.refl _

/-- THE NAIVE RETIRE IS WRONG AS A STATE FUNCTION: an NF state with a written cell of `old(0)`
and no written cell of `new(0)`; the naive rule leaves out the default `⟨@0.f⟩` of the new
object, which `retireV` merges into the old object. -/
theorem retireNaive_ne :
    let E : EState := ⟨[], [((rOld 0, .fld 0), [rOld 0])]⟩
    NF 0 E ∧ childCN 0 (rOld 0) (.fld 0) ∈ (retireV 0 0 (den 0 E)).heap (rOld 0) (.fld 0) ∧
      childCN 0 (rOld 0) (.fld 0) ∉ (den 0 (retireNaive 0 0 E)).heap (rOld 0) (.fld 0) ∧
      ¬ DEq (den 0 (retireNaive 0 0 E)) (retireV 0 0 (den 0 E)) := by
  intro E
  have hNF : NF 0 E := by
    refine ⟨fun x S e => (by cases e), fun k S e => ?_⟩
    have hm := look_mem e
    simp only [E, List.mem_cons, List.not_mem_nil, or_false] at hm
    cases hm
    intro h
    have := (h (rOld 0)).mp List.mem_cons_self
    simp [adefaultV, childCN, rOld] at this
  have h1 : childCN 0 (rOld 0) (.fld 0) ∈ (retireV 0 0 (den 0 E)).heap (rOld 0) (.fld 0) := by
    decide
  have h2 : childCN 0 (rOld 0) (.fld 0) ∉ (den 0 (retireNaive 0 0 E)).heap (rOld 0) (.fld 0) := by
    decide
  exact ⟨hNF, h1, h2, fun h => h2 ((h.2 _ _ _).mpr h1)⟩

/-- Each cell of each `old(s)` holds its cell name (true in each state of the model analysis:
`oldDflt_analyzeVS`). -/
def OldDflt (K : Nat) (X : AState) : Prop := ∀ s c, childCN K (rOld s) c ∈ X.heap (rOld s) c

/-- THE NAIVE RETIRE IS CORRECT ON STATES WITH `OldDflt`: the bug is latent. -/
theorem den_retireNaive_of_oldDflt {K : Nat} {s : Site} {E : EState} (h : OldDflt K (den K E)) :
    DEq (den K (retireNaive K s E)) (den K (retireE K s E)) := by
  refine ⟨fun x => SetEq.refl _, fun o c => ?_⟩
  show SetEq ((look (mkMap (dropH K) (retireNaiveF K s E) ((keys E.heap).map (rkey s))) (o, c)).getD
      (adefaultV K o c))
    ((look (mkMap (dropH K) (retireF K s E) ((keys E.heap).map (rkey s))) (o, c)).getD
      (adefaultV K o c))
  have hf : SetEq (retireNaiveF K s E (o, c)) (retireF K s E (o, c)) := by
    unfold retireNaiveF retireF
    by_cases ho : o = rOld s
    · subst ho
      rw [ite_eq_left rfl]
      by_cases hw : (rNew s, c) ∈ keys E.heap
      · rw [ite_eq_left ⟨rfl, hw⟩]; exact SetEq.refl _
      · rw [ite_eq_right (fun h' => hw h'.2)]
        have hn : getH K E (rNew s, c) = [childCN K (rOld s) c] := by
          unfold getH; rw [look_none_of hw, childCN_rOld]; rfl
        rw [hn]
        apply renameL_congr
        intro a
        rw [mem_uni, List.mem_singleton]
        constructor
        · intro ha; exact Or.inr ha
        · rintro (e | e)
          · subst e; exact h s c
          · exact e
    · rw [ite_eq_right (fun h' => ho h'.1), ite_eq_right ho]
      exact SetEq.refl _
  by_cases hk : (o, c) ∈ (keys E.heap).map (rkey s)
  · have a1 := getD_mkMap (dropH K) (retireNaiveF K s E) (adefaultV K o c)
      (fun h' => dropH_true h') hk
    have a2 := getD_mkMap (dropH K) (retireF K s E) (adefaultV K o c)
      (fun h' => dropH_true h') hk
    exact a1.trans (hf.trans a2.symm)
  · rw [look_mkMap_nk _ _ hk, look_mkMap_nk _ _ hk]
    exact SetEq.refl _

/-! ## `OldDflt` holds in each state of the model analysis -/

/-- `old(s)` is never unique. -/
theorem uniqueBO_rOld (once : Site → Bool) (eu : Bool) (E V : List Origin) (s : Site) :
    uniqueBO once eu E V (rOld s) = false := by
  have h : @Eq Nat ((2 * s + 1) % 2) 1 := by omega
  show ((((2 * s + 1) % 2 == 0) && !expB E (rOld s)) && !decide (rOld s ∈ V)) = false
  rw [h]
  rfl

/-- `OldDflt` is closed upward. -/
theorem OldDflt.mono {K : Nat} {X Y : AState} (h : OldDflt K X) (hs : X.Sub Y) : OldDflt K Y :=
  fun s c => hs.2 _ _ (h s c)

/-- `retireV` keeps `OldDflt`. -/
theorem OldDflt.retireV {K : Nat} {X : AState} (h : OldDflt K X) (s : Site) :
    OldDflt K (retireV K s X) := by
  intro s' c
  show childCN K (rOld s') c ∈ (if rOld s' = rNew s then _ else (retire s X).heap (rOld s') c)
  have hne : rOld s' ≠ rNew s := by
    intro e
    have : @Eq Nat (2 * s' + 1) (2 * s) := Origin.alloc.inj e
    omega
  rw [ite_eq_right hne]
  show _ ∈ (if rOld s' = rNew s then [] else if rOld s' = rOld s then
    renameL s (uni (X.heap (rNew s) c) (X.heap (rOld s) c)) else renameL s (X.heap (rOld s') c))
  rw [ite_eq_right hne]
  have hr : renameO s (childCN K (rOld s') c) = childCN K (rOld s') c :=
    renameO_of_ne_alloc s (childCN_ne_alloc K _ c)
  by_cases e : rOld s' = rOld s
  · rw [ite_eq_left e]
    exact mem_renameL.mpr ⟨_, mem_uni.mpr (Or.inr (e ▸ h s' c)), hr⟩
  · rw [ite_eq_right e]
    exact mem_renameL.mpr ⟨_, h s' c, hr⟩

/-- `storeBO` keeps `OldDflt`: a strong store never writes a cell of `old(s)`. -/
theorem OldDflt.storeBO {K : Nat} (cb : CtxB) {X : AState} (h : OldDflt K X) (x : Var)
    (c : ACell) (S : List Origin) : OldDflt K (storeBO cb X x c S) := by
  have hw : ∀ os, OldDflt K (X.weakStore os c S) := fun os =>
    h.mono ⟨fun _ _ h => h, fun o c' a ha => by
      show a ∈ (if c' = c ∧ o ∈ os then uni S (X.heap o c') else X.heap o c')
      split
      · exact mem_uni.mpr (Or.inr ha)
      · exact ha⟩
  unfold DirectedAlias.Sound.BlockOnly.storeBO
  cases hs : single? (X.env x) with
  | none => exact hw _
  | some o =>
    simp only
    split
    · rename_i hu
      intro s' c'
      show childCN K (rOld s') c' ∈ fupd2 X.heap o c S (rOld s') c'
      have : ¬ (rOld s' = o ∧ c' = c) := by
        rintro ⟨e, _⟩
        subst e
        rw [uniqueBO_rOld] at hu
        cases hu
      rw [fupd2_ne _ _ this]
      exact h s' c'
    · exact hw _

/-- One statement of design VS keeps `OldDflt`. -/
theorem OldDflt.astepVS (cb : CtxB) (i : Nat) {X : AState} (h : OldDflt cb.cn.ctx.K X) :
    ∀ st : Stmt, OldDflt cb.cn.ctx.K (DirectedAlias.Sound.ValueSem.astepVS cb i st X)
  | .new x s => (h.retireV s : OldDflt _ _)
  | .null x => h
  | .copy x y => h
  | .load x y f => h
  | .store x f y => h.storeBO cb x _ _
  | .aload x y => h
  | .astore x y => h.mono ⟨fun _ _ h => h, fun o c a ha => by
      show a ∈ (if c = .elem ∧ o ∈ X.env x then uni (X.env y) (X.heap o c) else X.heap o c)
      split
      · exact mem_uni.mpr (Or.inr ha)
      · exact ha⟩
  | .unknown x s => (h.retireV s : OldDflt _ _)
  | .call ret s args => by
    have hc : OldDflt cb.cn.ctx.K (callVS cb X args) := by
      intro s' c
      rw [callVS_heap]
      exact h s' c
    show OldDflt _ ((DirectedAlias.Sound.ValueSem.retireV cb.cn.ctx.K s (callVS cb X args)).setRet
      ret _)
    cases ret with
    | none => exact hc.retireV s
    | some x => exact hc.retireV s

/-- The loop iteration keeps `OldDflt` (the result includes the loop entry state). -/
theorem OldDflt.loopIter {K : Nat} (ctx : Ctx) (f : AState → AState) :
    ∀ (n : Nat) {Y : AState}, OldDflt K Y → OldDflt K (DirectedAlias.loopIter ctx f n Y) := by
  intro n
  induction n with
  | zero => intro Y h; exact h.mono (sub_top ctx Y)
  | succ n ih =>
    intro Y h
    show OldDflt K (if leOn ctx (f Y) Y then Y else DirectedAlias.loopIter ctx f n (join Y (f Y)))
    split
    · exact h
    · exact ih (h.mono (sub_join_left _ _))

/-- THE MODEL ANALYSIS KEEPS `OldDflt`: so the naive retire is correct on each of its states. -/
theorem oldDflt_analyzeVS (cb : CtxB) :
    ∀ (p : Prog) (i : Nat) {X : AState}, OldDflt cb.cn.ctx.K X →
      OldDflt cb.cn.ctx.K (analyzeVS cb i p X)
  | .skip, _, _, h => h
  | .stmt st, i, _, h => h.astepVS cb i st
  | .seq p q, i, _, h => oldDflt_analyzeVS cb q _ (oldDflt_analyzeVS cb p i h)
  | .choice p q, i, _, h => (oldDflt_analyzeVS cb p i h).mono (sub_join_left _ _)
  | .loop _, _, _, h => OldDflt.loopIter _ _ _ h

/-- The entry state of design VS has `OldDflt`. -/
theorem oldDflt_ainitV (K : Nat) (fr : Frame) : OldDflt K (ainitV K fr) :=
  fun _ _ => List.mem_singleton_self _

/-! ## The entry state -/

/-- The engine entry state of a frame: the bound variables hold their roots; no heap entry. -/
def initE (fr : Frame) : EState :=
  ⟨mkMap dropV (fun x => (ainit 0 fr).env x) fr.vars, []⟩

/-- The engine entry state is NF. -/
theorem NF_initE (K : Nat) (fr : Frame) : NF K (initE fr) :=
  ⟨fun _ _ e => dropV_false (drop_mkMap _ _ _ e), fun _ _ e => by cases e⟩

/-- The engine entry state denotes the entry state of design VS. -/
theorem den_initE (K : Nat) (fr : Frame) : DEq (den K (initE fr)) (ainitV K fr) := by
  refine ⟨fun x => ?_, fun o c => SetEq.refl _⟩
  show SetEq ((look (mkMap dropV (fun x => (ainit 0 fr).env x) fr.vars) x).getD [])
    ((ainit K fr).env x)
  have he : (ainit K fr).env x = (ainit 0 fr).env x := rfl
  rw [he]
  by_cases hx : x ∈ fr.vars
  · exact getD_mkMap _ _ [] (fun h => dropV_true h) hx
  · rw [look_mkMap_nk _ _ hx]
    show SetEq [] (match fr.root? x with | some r => [Origin.sym (.root r) []] | none => [])
    rw [show fr.root? x = none from lookup_none_of_not_mem fr.binds x hx]
    exact SetEq.refl _

end DirectedAlias.Impl.Engine
