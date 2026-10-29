import DirectedAlias.Concept

/-!
# Optimization O, part 1: the hash-consed node table

A node is a canonical origin set. The canonical form of a set `S` over the universe `U` is
`U.filter (· ∈ S)`: the members of `S` in the order of `U`. Two sets with the same members on `U`
have the same canonical form (`canon_eq_of_setEq`). The node table interns canonical sets:
a node id is an index into the table, and the table has no duplicate sets. Thus two ids with the
same members are the same id (`Tbl.id_inj`). The fixpoint test can then compare ids.

A union memo maps an id pair to the id of the union. A node that a union makes keeps its two
children. This gives the DAG view: the members of a node are the members of the leaves below it
(`Tbl.mem_iff_leaf`).
-/

namespace DirectedAlias.Opt

open DirectedAlias

/-! ## Set equality and canonical form -/

/-- Two lists have the same members. -/
def SetEq {α : Type} (l m : List α) : Prop := ∀ a, a ∈ l ↔ a ∈ m

/-- Set equality is reflexive. -/
theorem SetEq.refl {α : Type} (l : List α) : SetEq l l := fun _ => Iff.rfl

/-- Set equality is symmetric. -/
theorem SetEq.symm {α : Type} {l m : List α} (h : SetEq l m) : SetEq m l :=
  fun a => (h a).symm

/-- Set equality is transitive. -/
theorem SetEq.trans {α : Type} {l m n : List α} (h1 : SetEq l m) (h2 : SetEq m n) : SetEq l n :=
  fun a => (h1 a).trans (h2 a)

/-- Union keeps set equality on both sides. -/
theorem SetEq.uni {α : Type} [DecidableEq α] {l l' m m' : List α}
    (h1 : SetEq l l') (h2 : SetEq m m') : SetEq (uni l m) (uni l' m') := by
  intro a; rw [mem_uni, mem_uni, h1 a, h2 a]

/-- Union is commutative as a set. -/
theorem uni_comm_set {α : Type} [DecidableEq α] (l m : List α) : SetEq (uni l m) (uni m l) := by
  intro a; rw [mem_uni, mem_uni]; exact Or.comm

/-- Union with itself is the same set. -/
theorem uni_self_set {α : Type} [DecidableEq α] (l : List α) : SetEq (uni l l) l := by
  intro a; rw [mem_uni]; exact or_self_iff

/-- The canonical form of the set `S` over the universe `U`. -/
def canon {α : Type} [DecidableEq α] (U S : List α) : List α :=
  U.filter (fun o => decide (o ∈ S))

/-- An element is in the canonical form if and only if it is in the universe and in the set. -/
theorem mem_canon {α : Type} [DecidableEq α] {U S : List α} {o : α} :
    o ∈ canon U S ↔ o ∈ U ∧ o ∈ S := by
  simp [canon, List.mem_filter]

/-- Two sets with the same members on the universe have the same canonical form. -/
theorem canon_congr {α : Type} [DecidableEq α] {U S S' : List α}
    (h : ∀ o ∈ U, o ∈ S ↔ o ∈ S') : canon U S = canon U S' := by
  unfold canon
  apply List.filter_congr
  intro o ho
  simp [h o ho]

/-- Set-equal sets give equal nodes: the canonical forms are equal. -/
theorem canon_eq_of_setEq {α : Type} [DecidableEq α] {U S S' : List α} (h : SetEq S S') :
    canon U S = canon U S' :=
  canon_congr (fun o _ => h o)

/-- The canonical form of a subset of the universe has the same members. -/
theorem canon_setEq {α : Type} [DecidableEq α] {U S : List α} (h : S ⊆ U) :
    SetEq (canon U S) S := by
  intro o; rw [mem_canon]; exact ⟨fun h' => h'.2, fun h' => ⟨h h', h'⟩⟩

/-- The canonical form is a subset of the universe. -/
theorem canon_sub {α : Type} [DecidableEq α] {U S : List α} : canon U S ⊆ U :=
  fun _ h => (mem_canon.mp h).1

/-- The canonical form does not change a canonical form. -/
theorem canon_idem {α : Type} [DecidableEq α] (U S : List α) :
    canon U (canon U S) = canon U S :=
  canon_congr (fun o ho => by rw [mem_canon]; exact ⟨fun h => h.2, fun h => ⟨ho, h⟩⟩)

/-- The canonical form of the empty set is empty. -/
theorem canon_nil {α : Type} [DecidableEq α] : ∀ (U : List α), canon U [] = []
  | [] => rfl
  | a :: l => by
    simp only [canon, List.filter_cons, List.not_mem_nil, decide_false, Bool.false_eq_true,
      ite_false]
    exact canon_nil l

/-! ## Indexed lists -/

/-- Two equal elements at two positions of a list with no duplicates have the same position. -/
theorem nodup_idx_inj {α : Type} :
    ∀ {l : List α} {i j : Nat} {x : α}, l.Nodup → l[i]? = some x → l[j]? = some x → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | a :: l, i, j, x, hn, hi, hj => by
    rw [List.nodup_cons] at hn
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq,
          List.getElem?_cons_succ] at hi hj
        subst hi
        exact absurd (List.mem_of_getElem? hj) hn.1
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq,
          List.getElem?_cons_succ] at hi hj
        subst hj
        exact absurd (List.mem_of_getElem? hi) hn.1
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        rw [nodup_idx_inj hn.2 hi hj]

/-- A filter that removes an element of the list makes the list shorter. -/
theorem length_filter_lt {α : Type} {p : α → Bool} :
    ∀ {l : List α} {x : α}, x ∈ l → p x = false → (l.filter p).length < l.length
  | [], _, h, _ => by cases h
  | y :: l, x, h, hp => by
    rw [List.filter_cons]
    cases hy : p y with
    | true =>
      simp only [ite_true, List.length_cons]
      cases List.mem_cons.mp h with
      | inl h1 => subst h1; rw [hp] at hy; cases hy
      | inr h1 => exact Nat.succ_lt_succ (length_filter_lt h1 hp)
    | false =>
      simp only [Bool.false_eq_true, ite_false, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le p l)

/-- A list with no duplicates that is a subset of a second list is not longer than the second
list. This is a constructive form of `List.Nodup.length_le_of_subset`. -/
theorem nodup_length_le {α : Type} [DecidableEq α] :
    ∀ {l m : List α}, l.Nodup → (∀ a ∈ l, a ∈ m) → l.length ≤ m.length
  | [], _, _, _ => Nat.zero_le _
  | x :: l, m, hn, hs => by
    rw [List.nodup_cons] at hn
    have hx : x ∈ m := hs x List.mem_cons_self
    have hsub : ∀ a ∈ l, a ∈ m.filter (fun y => decide (y ≠ x)) := by
      intro a ha
      refine List.mem_filter.mpr ⟨hs a (List.mem_cons_of_mem _ ha), ?_⟩
      have : a ≠ x := fun h => hn.1 (h ▸ ha)
      simp [this]
    have h1 := nodup_length_le hn.2 hsub
    have h2 := length_filter_lt (p := fun y => decide (y ≠ x)) hx (by simp)
    simp only [List.length_cons]
    omega

/-! ## The node table -/

/-- A node: its canonical set, and its two children if a union made it. -/
structure Node where
  set : List Origin
  kids : Option (Nat × Nat)
  deriving DecidableEq, Repr

/-- The node table: the interned nodes (the id is the index), the union memo, and a work
counter for the cost model. -/
structure Tbl where
  nodes : List Node
  memo : List ((Nat × Nat) × Nat)
  work : Nat
  deriving DecidableEq, Repr

/-- The empty table. -/
def Tbl.empty : Tbl := ⟨[], [], 0⟩

/-- Add `n` units to the work counter. -/
def Tbl.tick (T : Tbl) (n : Nat) : Tbl := { T with work := T.work + n }

/-- The number of nodes. -/
def Tbl.size (T : Tbl) : Nat := T.nodes.length

/-- The members of node `i`. An invalid id has no members. -/
def Tbl.mem (T : Tbl) (i : Nat) : List Origin :=
  match T.nodes[i]? with
  | some n => n.set
  | none => []

/-- The position of the node with set `S`, if the table has it. -/
def findSet : List Node → List Origin → Option Nat
  | [], _ => none
  | n :: ns, S => if n.set = S then some 0 else (findSet ns S).map (· + 1)

/-- A position that `findSet` gives holds a node with the searched set. -/
theorem findSet_some : ∀ {ns : List Node} {S : List Origin} {i : Nat},
    findSet ns S = some i → ∃ n, ns[i]? = some n ∧ n.set = S
  | [], _, _, h => by simp [findSet] at h
  | n :: ns, S, i, h => by
    simp only [findSet] at h
    split at h
    · rename_i he; cases h; exact ⟨n, rfl, he⟩
    · cases hf : findSet ns S with
      | none => rw [hf] at h; cases h
      | some j =>
        rw [hf] at h; cases h
        obtain ⟨m, hm, hs⟩ := findSet_some hf
        exact ⟨m, by simpa using hm, hs⟩

/-- If `findSet` fails, no node has the searched set. -/
theorem findSet_none : ∀ {ns : List Node} {S : List Origin},
    findSet ns S = none → ∀ n ∈ ns, n.set ≠ S
  | [], _, _, n, hn => by simp at hn
  | m :: ns, S, h, n, hn => by
    simp only [findSet] at h
    split at h
    · cases h
    · rename_i he
      cases hf : findSet ns S with
      | some j => rw [hf] at h; cases h
      | none =>
        cases List.mem_cons.mp hn with
        | inl h1 => subst h1; exact he
        | inr h1 => exact findSet_none hf n h1

/-- Look up an id pair in the memo. -/
def mlook : List ((Nat × Nat) × Nat) → Nat × Nat → Option Nat
  | [], _ => none
  | (k, v) :: r, q => if k = q then some v else mlook r q

/-- A memo hit is an entry of the memo. -/
theorem mlook_mem : ∀ {m : List ((Nat × Nat) × Nat)} {q : Nat × Nat} {c : Nat},
    mlook m q = some c → (q, c) ∈ m
  | [], _, _, h => by simp [mlook] at h
  | (k, v) :: r, q, c, h => by
    simp only [mlook] at h
    split at h
    · rename_i he; cases h; subst he; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mlook_mem h)

/-- The memo key of an id pair. The smaller id comes first, so the key is symmetric. -/
def mkey (a b : Nat) : Nat × Nat := if a ≤ b then (a, b) else (b, a)

/-- Intern the canonical form of `S`. Give the id of the node with this set. Add a node with the
children `kids` if the table has no such node. -/
def Tbl.put (U : List Origin) (T : Tbl) (S : List Origin) (kids : Option (Nat × Nat)) :
    Nat × Tbl :=
  let C := canon U S
  match findSet T.nodes C with
  | some i => (i, T)
  | none => (T.nodes.length, { T with nodes := T.nodes ++ [⟨C, kids⟩] })

/-- Intern with cost: one unit plus the size of the set (the hash of the canonical form). -/
def Tbl.intern (U : List Origin) (T : Tbl) (S : List Origin) (kids : Option (Nat × Nat)) :
    Nat × Tbl :=
  (T.tick (S.length + 1)).put U S kids

/-- Memoized union of nodes `a` and `b`. A shortcut or a memo hit costs one unit. A miss costs
one unit plus the two sizes (the merge), plus the intern of the result. -/
def Tbl.union (U : List Origin) (T : Tbl) (a b : Nat) : Nat × Tbl :=
  if a = b then (a, T.tick 1) else
  match mlook T.memo (mkey a b) with
  | some c => (c, T.tick 1)
  | none =>
    let r := (T.tick (1 + (T.mem a).length + (T.mem b).length)).intern U
      (uni (T.mem a) (T.mem b)) (some (a, b))
    (r.1, { r.2 with memo := (mkey a b, r.1) :: r.2.memo })

/-! ## Table invariant -/

/-- The table invariant over the universe `U`. Each set is canonical. No two nodes have the same
set. Each child id is smaller than its parent, and the parent set is the union of the child sets.
Each memo entry is the union of its key nodes. -/
structure Tbl.Good (U : List Origin) (T : Tbl) : Prop where
  canon : ∀ n ∈ T.nodes, canon U n.set = n.set
  nodup : (T.nodes.map Node.set).Nodup
  kids : ∀ i n a b, T.nodes[i]? = some n → n.kids = some (a, b) →
    a < i ∧ b < i ∧ SetEq n.set (uni (T.mem a) (T.mem b))
  memo : ∀ a b c, ((a, b), c) ∈ T.memo →
    a < T.size ∧ b < T.size ∧ c < T.size ∧ SetEq (T.mem c) (uni (T.mem a) (T.mem b))

/-- Table `T'` extends table `T`: it keeps all old nodes at their ids, and all old memo
entries. -/
def Tbl.Ext (T T' : Tbl) : Prop := (∃ l, T'.nodes = T.nodes ++ l) ∧ ∃ l, T'.memo = l ++ T.memo

/-- Extension is reflexive. -/
theorem Tbl.Ext.refl (T : Tbl) : T.Ext T := ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

/-- Extension is transitive. -/
theorem Tbl.Ext.trans {T1 T2 T3 : Tbl} (h1 : T1.Ext T2) (h2 : T2.Ext T3) : T1.Ext T3 := by
  obtain ⟨⟨l1, h1⟩, ⟨m1, k1⟩⟩ := h1; obtain ⟨⟨l2, h2⟩, ⟨m2, k2⟩⟩ := h2
  exact ⟨⟨l1 ++ l2, by rw [h2, h1, List.append_assoc]⟩,
    ⟨m2 ++ m1, by rw [k2, k1, List.append_assoc]⟩⟩

/-- An extension does not make the table smaller. -/
theorem Tbl.Ext.size_le {T T' : Tbl} (h : T.Ext T') : T.size ≤ T'.size := by
  obtain ⟨⟨l, h⟩, _⟩ := h; simp [Tbl.size, h]

/-- An extension keeps the members of each old node. -/
theorem Tbl.Ext.mem_eq {T T' : Tbl} (h : T.Ext T') {i : Nat} (hi : i < T.size) :
    T'.mem i = T.mem i := by
  obtain ⟨⟨l, h⟩, _⟩ := h
  simp only [Tbl.mem, h, List.getElem?_append_left (show i < T.nodes.length from hi)]

/-- An extension keeps each old memo entry. -/
theorem Tbl.Ext.memo_mem {T T' : Tbl} (h : T.Ext T') {e : (Nat × Nat) × Nat}
    (he : e ∈ T.memo) : e ∈ T'.memo := by
  obtain ⟨_, ⟨l, h⟩⟩ := h
  rw [h]; exact List.mem_append_right _ he

/-- The work counter does not change the nodes or the memo. -/
theorem Tbl.Ext.tick (T : Tbl) (n : Nat) : T.Ext (T.tick n) := Tbl.Ext.refl T

/-- The members of a node of a good table are in the universe. -/
theorem Tbl.Good.mem_sub {U : List Origin} {T : Tbl} (g : T.Good U) (i : Nat) : T.mem i ⊆ U := by
  unfold Tbl.mem
  split
  · rename_i n hn
    rw [← g.canon n (List.mem_of_getElem? hn)]
    exact canon_sub
  · intro _ h; cases h

/-- The members of a node of a good table are canonical. -/
theorem Tbl.Good.mem_canonical {U : List Origin} {T : Tbl} (g : T.Good U) (i : Nat) :
    Opt.canon U (T.mem i) = T.mem i := by
  unfold Tbl.mem
  split
  · rename_i n hn; exact g.canon n (List.mem_of_getElem? hn)
  · exact canon_nil U

/-- In a good table, two valid ids with the same members are the same id. -/
theorem Tbl.id_inj {U : List Origin} {T : Tbl} (g : T.Good U) {i j : Nat} (hi : i < T.size)
    (hj : j < T.size) (h : SetEq (T.mem i) (T.mem j)) : i = j := by
  have he : T.mem i = T.mem j := by
    rw [← g.mem_canonical i, ← g.mem_canonical j]; exact canon_eq_of_setEq h
  have hsi : (T.nodes.map Node.set)[i]? = some (T.mem i) := by
    rw [List.getElem?_map]; unfold Tbl.mem
    cases hn : T.nodes[i]? with
    | none => rw [List.getElem?_eq_none_iff] at hn; unfold Tbl.size at hi; omega
    | some n => rfl
  have hsj : (T.nodes.map Node.set)[j]? = some (T.mem i) := by
    rw [List.getElem?_map, he]; unfold Tbl.mem
    cases hn : T.nodes[j]? with
    | none => rw [List.getElem?_eq_none_iff] at hn; unfold Tbl.size at hj; omega
    | some n => rfl
  exact nodup_idx_inj g.nodup hsi hsj

/-- In a good table, two valid ids are equal if and only if their members are set-equal. -/
theorem Tbl.id_eq_iff {U : List Origin} {T : Tbl} (g : T.Good U) {i j : Nat} (hi : i < T.size)
    (hj : j < T.size) : i = j ↔ SetEq (T.mem i) (T.mem j) :=
  ⟨fun h => h ▸ SetEq.refl _, Tbl.id_inj g hi hj⟩

/-- The work counter does not change the table invariant. -/
theorem Tbl.Good.tick {U : List Origin} {T : Tbl} (g : T.Good U) (n : Nat) :
    (T.tick n).Good U :=
  ⟨g.canon, g.nodup, g.kids, g.memo⟩

/-- The empty table is good. -/
theorem Tbl.good_empty (U : List Origin) : Tbl.empty.Good U where
  canon := by simp [Tbl.empty]
  nodup := by simp [Tbl.empty]
  kids := by simp [Tbl.empty]
  memo := by simp [Tbl.empty]

/-! ## Specifications of intern and union -/

/-- The result of `put`: the table stays good and grows, the id is valid, the members are the
canonical form, and the memo does not change. -/
theorem Tbl.put_spec {U : List Origin} {T : Tbl} (g : T.Good U) (S : List Origin)
    (kids : Option (Nat × Nat))
    (hk : ∀ a b, kids = some (a, b) →
      a < T.size ∧ b < T.size ∧ SetEq (canon U S) (uni (T.mem a) (T.mem b))) :
    (T.put U S kids).2.Good U ∧ T.Ext (T.put U S kids).2 ∧
      (T.put U S kids).1 < (T.put U S kids).2.size ∧
      (T.put U S kids).2.mem (T.put U S kids).1 = canon U S ∧
      (T.put U S kids).2.memo = T.memo := by
  unfold Tbl.put
  cases hf : findSet T.nodes (canon U S) with
  | some i =>
    obtain ⟨n, hn, hs⟩ := findSet_some hf
    simp only [hf]
    refine ⟨g, Tbl.Ext.refl T, ?_, ?_, trivial⟩
    · exact (List.getElem?_eq_some_iff.mp hn).1
    · simp [Tbl.mem, hn, hs]
  | none =>
    simp only [hf]
    have hnot := findSet_none hf
    have hext : T.Ext { T with nodes := T.nodes ++ [⟨canon U S, kids⟩] } :=
      ⟨⟨_, rfl⟩, ⟨[], by simp⟩⟩
    have hmem : ∀ i, i < T.size →
        Tbl.mem { T with nodes := T.nodes ++ [⟨canon U S, kids⟩] } i = T.mem i :=
      fun i hi => hext.mem_eq hi
    refine ⟨?_, hext, by simp [Tbl.size], ?_, trivial⟩
    · constructor
      · intro n hn
        cases List.mem_append.mp hn with
        | inl h => exact g.canon n h
        | inr h => simp at h; subst h; exact canon_idem U S
      · rw [List.map_append, List.nodup_append]
        refine ⟨g.nodup, by simp, ?_⟩
        intro a ha b hb
        simp at hb; subst hb
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
        exact hnot n hn
      · intro i n a b hi hka
        by_cases hlt : i < T.nodes.length
        · rw [List.getElem?_append_left hlt] at hi
          obtain ⟨h1, h2, h3⟩ := g.kids i n a b hi hka
          refine ⟨h1, h2, ?_⟩
          rw [hmem a (by unfold Tbl.size; omega), hmem b (by unfold Tbl.size; omega)]
          exact h3
        · rw [List.getElem?_append_right (by omega)] at hi
          have hi0 : i - T.nodes.length = 0 := by
            cases h : i - T.nodes.length with
            | zero => rfl
            | succ k => rw [h] at hi; simp at hi
          rw [hi0] at hi; simp at hi; subst hi
          obtain ⟨h1, h2, h3⟩ := hk a b hka
          have hi' : i = T.nodes.length := by
            have : T.nodes.length ≤ i := by omega
            omega
          subst hi'
          refine ⟨h1, h2, ?_⟩
          rw [hmem a h1, hmem b h2]; exact h3
      · intro a b c hm
        obtain ⟨h1, h2, h3, h4⟩ := g.memo a b c hm
        have hs : T.size ≤ Tbl.size { T with nodes := T.nodes ++ [⟨canon U S, kids⟩] } :=
          hext.size_le
        refine ⟨by omega, by omega, by omega, ?_⟩
        rw [hmem c h3, hmem a h1, hmem b h2]; exact h4
    · simp [Tbl.mem]

/-- The result of `intern`: the table stays good and grows, the id is valid, the members are the
canonical form, and the memo does not change. -/
theorem Tbl.intern_spec {U : List Origin} {T : Tbl} (g : T.Good U) (S : List Origin)
    (kids : Option (Nat × Nat))
    (hk : ∀ a b, kids = some (a, b) →
      a < T.size ∧ b < T.size ∧ SetEq (canon U S) (uni (T.mem a) (T.mem b))) :
    (T.intern U S kids).2.Good U ∧ T.Ext (T.intern U S kids).2 ∧
      (T.intern U S kids).1 < (T.intern U S kids).2.size ∧
      (T.intern U S kids).2.mem (T.intern U S kids).1 = canon U S ∧
      (T.intern U S kids).2.memo = T.memo := by
  have g0 : (T.tick (S.length + 1)).Good U := g.tick _
  obtain ⟨g1, e1, i1, m1, k1⟩ := Tbl.put_spec g0 S kids hk
  exact ⟨g1, (Tbl.Ext.tick T _).trans e1, i1, m1, k1⟩

/-- The members of the memo key nodes are the members of the two nodes, as a union. -/
theorem mkey_uni (T : Tbl) (a b : Nat) :
    SetEq (uni (T.mem (mkey a b).1) (T.mem (mkey a b).2)) (uni (T.mem a) (T.mem b)) := by
  unfold mkey
  split
  · exact SetEq.refl _
  · exact uni_comm_set _ _

/-- The result of `union`: the table stays good and grows, the id is valid, and its members are
the union of the members of the two nodes. -/
theorem Tbl.union_spec {U : List Origin} {T : Tbl} (g : T.Good U) {a b : Nat}
    (ha : a < T.size) (hb : b < T.size) :
    (T.union U a b).2.Good U ∧ T.Ext (T.union U a b).2 ∧
      (T.union U a b).1 < (T.union U a b).2.size ∧
      SetEq ((T.union U a b).2.mem (T.union U a b).1) (uni (T.mem a) (T.mem b)) := by
  unfold Tbl.union
  split
  · rename_i hab; subst hab
    exact ⟨g.tick 1, Tbl.Ext.tick T 1, ha, (uni_self_set _).symm⟩
  · cases hl : mlook T.memo (mkey a b) with
    | some c =>
      simp only
      have hm := mlook_mem hl
      have hk : mkey a b = ((mkey a b).1, (mkey a b).2) := rfl
      rw [hk] at hm
      obtain ⟨_, _, h3, h4⟩ := g.memo _ _ c hm
      exact ⟨g.tick 1, Tbl.Ext.tick T 1, h3, h4.trans (mkey_uni T a b)⟩
    | none =>
      simp only
      have hsub : uni (T.mem a) (T.mem b) ⊆ U := by
        intro o ho
        cases mem_uni.mp ho with
        | inl h => exact g.mem_sub a h
        | inr h => exact g.mem_sub b h
      have g0 : (T.tick (1 + (T.mem a).length + (T.mem b).length)).Good U := g.tick _
      obtain ⟨g1, e1, i1, m1, k1⟩ := Tbl.intern_spec g0 (uni (T.mem a) (T.mem b)) (some (a, b))
        (by
          intro a' b' h; cases h
          exact ⟨ha, hb, canon_setEq hsub⟩)
      have e1 : T.Ext _ := (Tbl.Ext.tick T _).trans e1
      have hsz := e1.size_le
      generalize Tbl.intern U (T.tick (1 + (T.mem a).length + (T.mem b).length))
        (uni (T.mem a) (T.mem b)) (some (a, b)) = r at g1 e1 i1 m1 k1 hsz
      have hmem : SetEq (r.2.mem r.1) (uni (T.mem a) (T.mem b)) := by
        rw [m1]; exact canon_setEq hsub
      have e1' : T.Ext { r.2 with memo := (mkey a b, r.1) :: r.2.memo } :=
        ⟨e1.1, ⟨[(mkey a b, r.1)], by simp only [List.singleton_append]; rw [k1]; rfl⟩⟩
      refine ⟨?_, e1', i1, hmem⟩
      constructor
      · exact g1.canon
      · exact g1.nodup
      · exact g1.kids
      · intro a' b' c hm
        cases List.mem_cons.mp hm with
        | inl h =>
          simp only [Prod.mk.injEq] at h
          obtain ⟨hkk, hc⟩ := h
          have hka : (mkey a b).1 = a' := by rw [← hkk]
          have hkb : (mkey a b).2 = b' := by rw [← hkk]
          subst hc
          have hk1 : a' < T.size := by
            rw [← hka]; unfold mkey; split <;> assumption
          have hk2 : b' < T.size := by
            rw [← hkb]; unfold mkey; split <;> assumption
          refine ⟨by simp only [Tbl.size] at *; omega, by simp only [Tbl.size] at *; omega, i1, ?_⟩
          have hm' : ∀ (R : Tbl) (m : List ((Nat × Nat) × Nat)) (w i : Nat),
              Tbl.mem { nodes := R.nodes, memo := m, work := w } i = R.mem i :=
            fun _ _ _ _ => rfl
          simp only [hm']
          rw [e1.mem_eq hk1, e1.mem_eq hk2, ← hka, ← hkb]
          exact hmem.trans (mkey_uni T a b).symm
        | inr h => exact g1.memo a' b' c h

/-! ## Memo hits -/

/-- If the memo has an entry for a key, the memo lookup finds an entry for the key. -/
theorem mlook_some_of_mem : ∀ {m : List ((Nat × Nat) × Nat)} {q : Nat × Nat} {c : Nat},
    (q, c) ∈ m → ∃ c', mlook m q = some c'
  | [], _, _, h => by cases h
  | (k, v) :: r, q, c, h => by
    simp only [mlook]
    split
    · exact ⟨v, rfl⟩
    · rename_i hne
      cases List.mem_cons.mp h with
      | inl h1 => cases h1; exact absurd rfl hne
      | inr h1 => exact mlook_some_of_mem h1

/-- The memo key of a pair with itself is the pair. -/
theorem mkey_self (a : Nat) : mkey a a = (a, a) := by simp [mkey]

/-- After a union of two different nodes, the memo has the result for their key. -/
theorem Tbl.union_memo_mem (U : List Origin) (T : Tbl) {a b : Nat} (hab : a ≠ b) :
    (mkey a b, (T.union U a b).1) ∈ (T.union U a b).2.memo := by
  unfold Tbl.union
  rw [ite_eq_right hab]
  cases hl : mlook T.memo (mkey a b) with
  | some c => exact mlook_mem hl
  | none => exact List.mem_cons_self

/-- A memo hit: if the memo has the result `c` for the key, the union gives `c`, adds no node,
and costs one unit. -/
theorem Tbl.union_hit {U : List Origin} {T : Tbl} (g : T.Good U) {a b c : Nat}
    (hm : (mkey a b, c) ∈ T.memo) : (T.union U a b).1 = c ∧ (T.union U a b).2 = T.tick 1 := by
  have hk : mkey a b = ((mkey a b).1, (mkey a b).2) := rfl
  have hm2 := hm
  rw [hk] at hm2
  obtain ⟨_, _, hc, hcm⟩ := g.memo _ _ c hm2
  unfold Tbl.union
  split
  · rename_i hab
    subst hab
    refine ⟨?_, rfl⟩
    have ha : a < T.size := by
      have := (g.memo _ _ c hm2).1; rw [mkey_self] at this; exact this
    apply Tbl.id_inj g ha hc
    rw [mkey_self] at hcm
    exact (hcm.trans (uni_self_set _)).symm
  · obtain ⟨c', hc'⟩ := mlook_some_of_mem hm
    rw [hc']
    refine ⟨?_, rfl⟩
    have hm3 := mlook_mem hc'
    rw [hk] at hm3
    obtain ⟨_, _, hc2, hcm2⟩ := g.memo _ _ c' hm3
    exact Tbl.id_inj g hc2 hc (hcm2.trans hcm.symm)

/-- A repeated union is a hit: after a union of `a` and `b`, each later good table of the same
analysis gives the same id for the same pair, adds no node, and costs one unit. -/
theorem Tbl.union_again {U : List Origin} {T T' : Tbl} {a b : Nat} (g' : T'.Good U)
    (e : (T.union U a b).2.Ext T') :
    (T'.union U a b).1 = (T.union U a b).1 ∧ (T'.union U a b).2 = T'.tick 1 := by
  by_cases hab : a = b
  · subst hab
    simp [Tbl.union]
  · exact Tbl.union_hit g' (e.memo_mem (Tbl.union_memo_mem U T hab))

/-! ## The DAG view -/

/-- Node `j` is below node `i` in the DAG: a chain of child edges goes from `i` to `j`. -/
inductive Tbl.Below (T : Tbl) : Nat → Nat → Prop
  | refl (i : Nat) : T.Below i i
  | left {i a b j : Nat} {n : Node} : T.nodes[i]? = some n → n.kids = some (a, b) →
      T.Below a j → T.Below i j
  | right {i a b j : Nat} {n : Node} : T.nodes[i]? = some n → n.kids = some (a, b) →
      T.Below b j → T.Below i j

/-- Node `l` is a leaf: an `intern` made it, not a union. -/
def Tbl.Leaf (T : Tbl) (l : Nat) : Prop := ∃ n, T.nodes[l]? = some n ∧ n.kids = none

/-- In a good table, a union node has the union of the members of its two children. -/
theorem Tbl.kids_den {U : List Origin} {T : Tbl} (g : T.Good U) {i a b : Nat} {n : Node}
    (hn : T.nodes[i]? = some n) (hk : n.kids = some (a, b)) :
    SetEq (T.mem i) (uni (T.mem a) (T.mem b)) := by
  have := (g.kids i n a b hn hk).2.2
  simpa [Tbl.mem, hn] using this

/-- In a good table, a node below another node has fewer or equal members. -/
theorem Tbl.Below.mem_sub {U : List Origin} {T : Tbl} (g : T.Good U) {i j : Nat}
    (h : T.Below i j) : T.mem j ⊆ T.mem i := by
  induction h with
  | refl => exact fun _ h => h
  | left hn hk _ ih =>
    intro o ho
    exact ((Tbl.kids_den g hn hk) o).mpr (mem_uni.mpr (Or.inl (ih ho)))
  | right hn hk _ ih =>
    intro o ho
    exact ((Tbl.kids_den g hn hk) o).mpr (mem_uni.mpr (Or.inr (ih ho)))

/-- In a good table, an origin is in node `i` if and only if it is in a leaf below `i`. -/
theorem Tbl.mem_iff_leaf {U : List Origin} {T : Tbl} (g : T.Good U) {i : Nat} {o : Origin} :
    o ∈ T.mem i ↔ ∃ l, T.Below i l ∧ T.Leaf l ∧ o ∈ T.mem l := by
  constructor
  · intro ho
    suffices H : ∀ k i, i < k → o ∈ T.mem i → ∃ l, T.Below i l ∧ T.Leaf l ∧ o ∈ T.mem l from
      H (i + 1) i (Nat.lt_succ_self i) ho
    intro k
    induction k with
    | zero => intro i h; exact absurd h (Nat.not_lt_zero i)
    | succ k ih =>
      intro i hik hoi
      cases hn : T.nodes[i]? with
      | none => unfold Tbl.mem at hoi; rw [hn] at hoi; cases hoi
      | some n =>
        cases hk : n.kids with
        | none => exact ⟨i, .refl i, ⟨n, hn, hk⟩, hoi⟩
        | some ab =>
          obtain ⟨a, b⟩ := ab
          obtain ⟨h1, h2, _⟩ := g.kids i n a b hn hk
          cases mem_uni.mp (((Tbl.kids_den g hn hk) o).mp hoi) with
          | inl h =>
            obtain ⟨l, hb, hl, hol⟩ := ih a (Nat.lt_of_lt_of_le h1 (Nat.le_of_lt_succ hik)) h
            exact ⟨l, .left hn hk hb, hl, hol⟩
          | inr h =>
            obtain ⟨l, hb, hl, hol⟩ := ih b (Nat.lt_of_lt_of_le h2 (Nat.le_of_lt_succ hik)) h
            exact ⟨l, .right hn hk hb, hl, hol⟩
  · rintro ⟨l, hb, _, hol⟩
    exact hb.mem_sub g hol

end DirectedAlias.Opt
