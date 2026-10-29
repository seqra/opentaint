import DirectedAlias.Opt.Support

/-!
# Optimization O, part 3: the state map and the primitive operations

An O state is a finite map from keys to node ids (an association list). A key that the map does
not hold has its default content: a variable is null, and a cell holds `adefault`.
The value of a key is the member set of its node, or the default content.

Each primitive operation threads the node table. Each specification says: the table stays good,
the table only grows, the ids in the state stay valid, and the value of each key changes as the
specification states.
-/

namespace DirectedAlias.Opt

open DirectedAlias

/-- An O state: a finite map from keys to node ids. -/
abbrev OState := List (Key × Nat)

/-- The node id of a key, if the map has the key. -/
def oget : OState → Key → Option Nat
  | [], _ => none
  | (k', i) :: r, k => if k' = k then some i else oget r k

/-- Set key `k` to node `i`. The map keeps one entry for each key. -/
def oset (m : OState) (k : Key) (i : Nat) : OState :=
  (k, i) :: m.filter (fun p => decide (p.1 ≠ k))

/-- Remove key `k`: it gets its default content again. -/
def oerase (m : OState) (k : Key) : OState :=
  m.filter (fun p => decide (p.1 ≠ k))

/-- The default content of a key: null for a variable, `adefault` for a cell. -/
def dflt (K : Nat) : Key → List Origin
  | .v _ => []
  | .h o c => adefault K o c

/-- The value of a key in an O state: the members of its node, or the default content. -/
def val (K : Nat) (T : Tbl) (st : OState) (k : Key) : List Origin :=
  match oget st k with
  | some i => T.mem i
  | none => dflt K k

/-- The denotation of an O state: the C state that it represents. -/
def den (K : Nat) (T : Tbl) (st : OState) : AState where
  env := fun x => val K T st (.v x)
  heap := fun o c => val K T st (.h o c)

/-- Each entry of the map has a valid node id and a universe key, and the map has one entry
for each key. -/
structure EntOK (ctx : Ctx) (T : Tbl) (st : OState) : Prop where
  ent : ∀ p ∈ st, p.2 < T.size ∧ InU ctx p.1
  nodup : (st.map Prod.fst).Nodup

/-- The O state and the C state have set-equal values on each universe key. -/
def Agree (ctx : Ctx) (T : Tbl) (st : OState) (X : AState) : Prop :=
  ∀ k, InU ctx k → SetEq (val ctx.K T st k) (cval X k)

/-- The simulation relation between an O state (with its table) and a C state. -/
structure Rel (ctx : Ctx) (T : Tbl) (st : OState) (X : AState) : Prop where
  ent : EntOK ctx T st
  agree : Agree ctx T st X
  supp : Supp ctx X

/-! ## Map lemmas -/

/-- A map hit is an entry of the map. -/
theorem oget_mem : ∀ {m : OState} {k : Key} {i : Nat}, oget m k = some i → (k, i) ∈ m
  | [], _, _, h => by simp [oget] at h
  | (k', j) :: r, k, i, h => by
    simp only [oget] at h
    split at h
    · rename_i he; cases h; subst he; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (oget_mem h)

/-- A lookup in the filtered map. -/
theorem oget_filter (m : OState) (k k' : Key) :
    oget (m.filter (fun p => decide (p.1 ≠ k))) k' = if k' = k then none else oget m k' := by
  induction m with
  | nil => simp [oget]
  | cons p r ih =>
    obtain ⟨k1, i1⟩ := p
    rw [List.filter_cons]
    by_cases h1 : k1 = k
    · subst h1
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, ih, oget]
      by_cases h2 : k' = k1
      · simp [h2]
      · have : ¬ k1 = k' := fun h => h2 h.symm
        simp [h2, this]
    · simp only [ne_eq, h1, not_false_eq_true, decide_true, ite_true, oget, ih]
      by_cases h2 : k' = k
      · subst h2; simp [h1]
      · simp [h2]

/-- A lookup after `oset`. -/
theorem oget_oset (m : OState) (k k' : Key) (i : Nat) :
    oget (oset m k i) k' = if k' = k then some i else oget m k' := by
  unfold oset
  simp only [oget]
  rw [oget_filter]
  by_cases h : k' = k
  · subst h; simp
  · have : ¬ k = k' := fun h' => h h'.symm
    simp [this, h]

/-- A lookup after `oerase`. -/
theorem oget_oerase (m : OState) (k k' : Key) :
    oget (oerase m k) k' = if k' = k then none else oget m k' :=
  oget_filter m k k'

/-- The value after `oset`. -/
theorem val_oset (K : Nat) (T : Tbl) (m : OState) (k k' : Key) (i : Nat) :
    val K T (oset m k i) k' = if k' = k then T.mem i else val K T m k' := by
  by_cases h : k' = k <;> simp [val, oget_oset, h]

/-- The value after `oerase`. -/
theorem val_oerase (K : Nat) (T : Tbl) (m : OState) (k k' : Key) :
    val K T (oerase m k) k' = if k' = k then dflt K k else val K T m k' := by
  by_cases h : k' = k
  · subst h; simp [val, oget_oerase]
  · simp [val, oget_oerase, h]

/-- The value of a key in the empty map is its default content. -/
theorem val_nil (K : Nat) (T : Tbl) (k : Key) : val K T [] k = dflt K k := rfl

/-- The denotation gives the values of the keys. -/
theorem cval_den (K : Nat) (T : Tbl) (st : OState) (k : Key) :
    cval (den K T st) k = val K T st k := by
  cases k <;> rfl

/-- A table extension keeps the value of each key. -/
theorem val_ext {ctx : Ctx} {T T' : Tbl} {st : OState} (h : EntOK ctx T st) (e : T.Ext T')
    (k : Key) : val ctx.K T' st k = val ctx.K T st k := by
  unfold val
  cases ho : oget st k with
  | none => rfl
  | some i => exact e.mem_eq (h.ent _ (oget_mem ho)).1

/-- The default content of a universe key holds only universe origins. -/
theorem dflt_sub {ctx : Ctx} (cc : CtxClosed ctx) {k : Key} (hk : InU ctx k) :
    dflt ctx.K k ⊆ ctx.origins := by
  cases k with
  | v x => intro _ h; cases h
  | h o c => exact cc.dflt o hk.1 c hk.2

/-- The value of a universe key holds only universe origins. -/
theorem val_sub {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    (st : OState) {k : Key} (hk : InU ctx k) : val ctx.K T st k ⊆ ctx.origins := by
  unfold val
  split
  · exact g.mem_sub _
  · exact dflt_sub cc hk

/-- The keys of a filtered map are a sublist of the keys of the map. -/
theorem keys_filter_sublist (st : OState) (k : Key) :
    ((st.filter (fun p => decide (p.1 ≠ k))).map Prod.fst).Sublist (st.map Prod.fst) :=
  (List.filter_sublist).map _

/-- The empty map is valid. -/
theorem EntOK.nil (ctx : Ctx) (T : Tbl) : EntOK ctx T [] :=
  ⟨fun p hp => (by cases hp), List.nodup_nil⟩

/-- `oset` with a valid id and a universe key keeps the map valid. -/
theorem EntOK.oset {ctx : Ctx} {T : Tbl} {st : OState} (h : EntOK ctx T st) {k : Key} {i : Nat}
    (hi : i < T.size) (hk : InU ctx k) : EntOK ctx T (Opt.oset st k i) := by
  constructor
  · intro p hp
    simp only [Opt.oset, List.mem_cons, List.mem_filter] at hp
    rcases hp with rfl | ⟨hp, _⟩
    · exact ⟨hi, hk⟩
    · exact h.ent p hp
  · simp only [Opt.oset, List.map_cons]
    rw [List.nodup_cons]
    refine ⟨?_, h.nodup.sublist (keys_filter_sublist st k)⟩
    intro hm
    obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hm
    have := (List.mem_filter.mp hp).2
    simp only [ne_eq, decide_eq_true_eq] at this
    exact this hpk

/-- `oerase` keeps the map valid. -/
theorem EntOK.oerase {ctx : Ctx} {T : Tbl} {st : OState} (h : EntOK ctx T st) (k : Key) :
    EntOK ctx T (Opt.oerase st k) := by
  constructor
  · intro p hp
    simp only [Opt.oerase, List.mem_filter] at hp
    exact h.ent p hp.1
  · exact h.nodup.sublist (keys_filter_sublist st k)

/-- A table extension keeps the map valid. -/
theorem EntOK.ext {ctx : Ctx} {T T' : Tbl} {st : OState} (h : EntOK ctx T st) (e : T.Ext T') :
    EntOK ctx T' st :=
  ⟨fun p hp => ⟨Nat.lt_of_lt_of_le (h.ent p hp).1 e.size_le, (h.ent p hp).2⟩, h.nodup⟩

/-- A valid map has at most one entry for each universe key: its size is at most the number of
universe keys. -/
theorem EntOK.length_le {ctx : Ctx} {T : Tbl} {st : OState} (h : EntOK ctx T st) :
    st.length ≤ (ukeys ctx).length := by
  have : (st.map Prod.fst).length ≤ (ukeys ctx).length :=
    nodup_length_le h.nodup (fun k hk => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      exact mem_ukeys.mpr (h.ent p hp).2)
  rw [List.length_map] at this
  exact this

/-- A table extension keeps the simulation relation. -/
theorem Rel.ext {ctx : Ctx} {T T' : Tbl} {st : OState} {X : AState} (h : Rel ctx T st X)
    (e : T.Ext T') : Rel ctx T' st X where
  ent := h.ent.ext e
  agree := fun k hk => by rw [val_ext h.ent e]; exact h.agree k hk
  supp := h.supp

/-! ## Primitive operations -/

/-- Intern a set with no children. -/
theorem Tbl.intern_none_spec {U : List Origin} {T : Tbl} (g : T.Good U) {S : List Origin}
    (hS : S ⊆ U) :
    (T.intern U S none).2.Good U ∧ T.Ext (T.intern U S none).2 ∧
      (T.intern U S none).1 < (T.intern U S none).2.size ∧
      SetEq ((T.intern U S none).2.mem (T.intern U S none).1) S := by
  obtain ⟨g1, e1, i1, m1, _⟩ := T.intern_spec g S none (by intro a b h; cases h)
  exact ⟨g1, e1, i1, by rw [m1]; exact canon_setEq hS⟩

/-- The node id of key `k`. If the map does not hold `k`, intern its default content. -/
def getId (ctx : Ctx) (T : Tbl) (st : OState) (k : Key) : Nat × Tbl :=
  match oget st k with
  | some i => (i, T)
  | none => T.intern ctx.origins (dflt ctx.K k) none

/-- `getId` gives a valid id whose members are the value of the key. -/
theorem getId_spec {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} (h : EntOK ctx T st) {k : Key} (hk : InU ctx k) :
    (getId ctx T st k).2.Good ctx.origins ∧ T.Ext (getId ctx T st k).2 ∧
      (getId ctx T st k).1 < (getId ctx T st k).2.size ∧
      SetEq ((getId ctx T st k).2.mem (getId ctx T st k).1) (val ctx.K T st k) := by
  unfold getId val
  cases ho : oget st k with
  | some i => exact ⟨g, Tbl.Ext.refl T, (h.ent _ (oget_mem ho)).1, SetEq.refl _⟩
  | none => exact Tbl.intern_none_spec g (dflt_sub cc hk)

/-- Set key `k` to the node of the set `S`. -/
def setKey (ctx : Ctx) (T : Tbl) (st : OState) (k : Key) (S : List Origin) : Tbl × OState :=
  let r := T.intern ctx.origins S none
  (r.2, oset st k r.1)

/-- `setKey` sets the value of `k` to `S` and keeps the other values. -/
theorem setKey_spec {ctx : Ctx} {T : Tbl} (g : T.Good ctx.origins) {st : OState}
    (h : EntOK ctx T st) {k : Key} (hk : InU ctx k) {S : List Origin} (hS : S ⊆ ctx.origins) :
    (setKey ctx T st k S).1.Good ctx.origins ∧ T.Ext (setKey ctx T st k S).1 ∧
      EntOK ctx (setKey ctx T st k S).1 (setKey ctx T st k S).2 ∧
      ∀ k', SetEq (val ctx.K (setKey ctx T st k S).1 (setKey ctx T st k S).2 k')
        (if k' = k then S else val ctx.K T st k') := by
  obtain ⟨g1, e1, i1, m1⟩ := Tbl.intern_none_spec g hS
  unfold setKey
  refine ⟨g1, e1, (h.ext e1).oset i1 hk, ?_⟩
  intro k'
  rw [val_oset]
  split
  · exact m1
  · rw [val_ext h e1]; exact SetEq.refl _

/-- Add the members of node `n` to key `k`: a memoized union. -/
def addKey (ctx : Ctx) (T : Tbl) (st : OState) (k : Key) (n : Nat) : Tbl × OState :=
  let r := getId ctx T st k
  let u := r.2.union ctx.origins r.1 n
  (u.2, oset st k u.1)

/-- `addKey` adds the members of `n` to the value of `k` and keeps the other values. -/
theorem addKey_spec {ctx : Ctx} (cc : CtxClosed ctx) {T : Tbl} (g : T.Good ctx.origins)
    {st : OState} (h : EntOK ctx T st) {k : Key} (hk : InU ctx k) {n : Nat} (hn : n < T.size) :
    (addKey ctx T st k n).1.Good ctx.origins ∧ T.Ext (addKey ctx T st k n).1 ∧
      EntOK ctx (addKey ctx T st k n).1 (addKey ctx T st k n).2 ∧
      ∀ k', SetEq (val ctx.K (addKey ctx T st k n).1 (addKey ctx T st k n).2 k')
        (if k' = k then uni (val ctx.K T st k) (T.mem n) else val ctx.K T st k') := by
  obtain ⟨g1, e1, i1, m1⟩ := getId_spec cc g h hk
  unfold addKey
  simp only
  generalize getId ctx T st k = r at g1 e1 i1 m1
  have hn1 : n < r.2.size := Nat.lt_of_lt_of_le hn e1.size_le
  obtain ⟨g2, e2, i2, m2⟩ := Tbl.union_spec g1 i1 hn1
  generalize r.2.union ctx.origins r.1 n = u at g2 e2 i2 m2
  have e12 := e1.trans e2
  refine ⟨g2, e12, (h.ext e12).oset i2 hk, ?_⟩
  intro k'
  rw [val_oset]
  split
  · rename_i hkk
    subst hkk
    rw [e1.mem_eq hn] at m2
    exact m2.trans (SetEq.uni m1 (SetEq.refl _))
  · rw [val_ext h e12]; exact SetEq.refl _

/-- Add the members of node `n` to each key of `ks`. -/
def addAll (ctx : Ctx) : Tbl → OState → List Key → Nat → Tbl × OState
  | T, st, [], _ => (T, st)
  | T, st, k :: ks, n =>
    let r := addKey ctx T st k n
    addAll ctx r.1 r.2 ks n

/-- `addAll` adds the members of `n` to the value of each key of `ks`. -/
theorem addAll_spec {ctx : Ctx} (cc : CtxClosed ctx) :
    ∀ (ks : List Key) {T : Tbl} {st : OState} {n : Nat}, T.Good ctx.origins → EntOK ctx T st →
      (∀ k ∈ ks, InU ctx k) → n < T.size →
      (addAll ctx T st ks n).1.Good ctx.origins ∧ T.Ext (addAll ctx T st ks n).1 ∧
      EntOK ctx (addAll ctx T st ks n).1 (addAll ctx T st ks n).2 ∧
      ∀ k', SetEq (val ctx.K (addAll ctx T st ks n).1 (addAll ctx T st ks n).2 k')
        (if k' ∈ ks then uni (val ctx.K T st k') (T.mem n) else val ctx.K T st k')
  | [], T, st, n, g, h, _, _ => by
    refine ⟨g, Tbl.Ext.refl T, h, ?_⟩
    intro k'; simp only [addAll, List.not_mem_nil, ite_false]; exact SetEq.refl _
  | k :: ks, T, st, n, g, h, hks, hn => by
    obtain ⟨g1, e1, h1, m1⟩ := addKey_spec cc g h (hks k List.mem_cons_self) hn
    simp only [addAll]
    generalize addKey ctx T st k n = r at g1 e1 h1 m1
    have hn1 : n < r.1.size := Nat.lt_of_lt_of_le hn e1.size_le
    obtain ⟨g2, e2, h2, m2⟩ :=
      addAll_spec cc ks g1 h1 (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) hn1
    refine ⟨g2, e1.trans e2, h2, ?_⟩
    intro k'
    rw [e1.mem_eq hn] at m2
    refine (m2 k').trans ?_
    have m1k := m1 k'
    by_cases hk1 : k' = k
    · subst hk1
      simp only [List.mem_cons_self, ite_true] at m1k ⊢
      split
      · intro a
        rw [mem_uni, m1k a, mem_uni]
        constructor
        · rintro ((h | h) | h) <;> simp [h]
        · rintro (h | h) <;> simp [h]
      · exact m1k
    · simp only [hk1, ite_false] at m1k
      have : (k' ∈ k :: ks) ↔ k' ∈ ks := by simp [hk1]
      simp only [this]
      split
      · exact SetEq.uni m1k (SetEq.refl _)
      · exact m1k

/-- Union of node `acc` with the cell `c` of each origin of `os`. -/
def readUnion (ctx : Ctx) (st : OState) (c : ACell) : Tbl → List Origin → Nat → Nat × Tbl
  | T, [], acc => (acc, T)
  | T, o :: os, acc =>
    let r := getId ctx T st (.h o c)
    let u := r.2.union ctx.origins acc r.1
    readUnion ctx st c u.2 os u.1

/-- `readUnion` gives the node of the union of `acc` and the cells `c` of the origins `os`. -/
theorem readUnion_spec {ctx : Ctx} (cc : CtxClosed ctx) {st : OState} {c : ACell}
    (hc : c ∈ ctx.cells) :
    ∀ (os : List Origin) {T : Tbl} {acc : Nat}, T.Good ctx.origins → EntOK ctx T st →
      os ⊆ ctx.origins → acc < T.size →
      (readUnion ctx st c T os acc).2.Good ctx.origins ∧ T.Ext (readUnion ctx st c T os acc).2 ∧
      (readUnion ctx st c T os acc).1 < (readUnion ctx st c T os acc).2.size ∧
      ∀ o', o' ∈ (readUnion ctx st c T os acc).2.mem (readUnion ctx st c T os acc).1 ↔
        o' ∈ T.mem acc ∨ ∃ o ∈ os, o' ∈ val ctx.K T st (.h o c)
  | [], T, acc, g, _, _, ha => by
    refine ⟨g, Tbl.Ext.refl T, ha, ?_⟩
    intro o'; simp [readUnion]
  | o :: os, T, acc, g, h, hos, ha => by
    have hk : InU ctx (.h o c) := ⟨hos List.mem_cons_self, hc⟩
    obtain ⟨g1, e1, i1, m1⟩ := getId_spec cc g h hk
    simp only [readUnion]
    generalize getId ctx T st (.h o c) = r at g1 e1 i1 m1
    have ha1 : acc < r.2.size := Nat.lt_of_lt_of_le ha e1.size_le
    obtain ⟨g2, e2, i2, m2⟩ := Tbl.union_spec g1 ha1 i1
    generalize r.2.union ctx.origins acc r.1 = u at g2 e2 i2 m2
    have h2 : EntOK ctx u.2 st := h.ext (e1.trans e2)
    obtain ⟨g3, e3, i3, m3⟩ :=
      readUnion_spec cc hc os g2 h2 (fun a ha' => hos (List.mem_cons_of_mem _ ha')) i2
    refine ⟨g3, e1.trans (e2.trans e3), i3, ?_⟩
    intro o'
    rw [m3 o', m2 o', mem_uni, e1.mem_eq ha, m1 o']
    simp only [val_ext h (e1.trans e2), List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h1 | h1) | h1) <;> simp_all
    · rintro (h1 | h1 | h1) <;> simp_all

end DirectedAlias.Opt
