/-
  ApSpec.Tree — the edge tree (storage design v2) as an optimization of the
  CONCEPT of a final fact (a list of path facts with one base).

  Storage design (spec §7.2): ONE TREE per (premise, layer,
  exclusion E, mark exclusion X). A `*` leaf is a flag: the exclusion `E` belongs
  to the whole tree, and the layer (the demand bit) is part of the key. `[any]`
  and `$` leaves carry no exclusion (W1).
  Version 5 (cleaners): the abstract mark of the tree is `*∖X` (`starM X`; `*` if
  `X` is empty). The mark exclusion `X` belongs to the whole tree, as `E` does: the
  trie stores the abstract mark as the flag `*`, and `toAFacts` reads it as
  `starM X` on every leaf with the abstract mark (`*`, `[any]` and `$` leaves).
  Concrete marks `conc t` do not change. With `X = []` the representation is the
  representation of version 4.
    * Merge rule 1: same premise, layer, E and X  → the union of the trees.
    * Merge rule 2: same premise, layer, X and tree, E1 and E2 → E1 ∩ E2.
    * Merge rule 2 for marks (`rule2_mark`): same premise, layer, E and tree,
      X1 and X2 → X1 ∩ X2.
    * A union of exclusions is FORBIDDEN (counterexamples in section 9).

  The module:
    (a) defines the trie, the edge tree and its path facts (`toAFacts`);
    (b) proves each operation equal to the operation on the list of path facts
        (insert, merge rules 1 and 2, prepend, and `applyTreeE`, the tree form
        of `applyEdge`, on whole `AFact`s: fact AND demand bit);
    (c) proves closed-form cost bounds (size, fan, prepend, walk).

  All proofs are constructive: only `propext` and `Quot.sound` occur.
-/
import ApSpec.Basic

namespace ApSpec.Tree
open ApSpec

/-! ## 1. Relative path facts and their meaning -/

/-- A path fact without a base. The tree stores these facts. The base is a
    parameter of `toFacts`, thus a base change costs nothing. -/
structure RFact where
  path : List Acc
  kind : Kind
  mark : MarkA
deriving DecidableEq, Repr

/-- Put the path `p` before the path of the fact. -/
def RFact.pre (p : List Acc) (x : RFact) : RFact := ⟨p ++ x.path, x.kind, x.mark⟩

/-- Put the accessor `a` before the path of the fact. -/
def RFact.cons (a : Acc) (x : RFact) : RFact := ⟨a :: x.path, x.kind, x.mark⟩

/-- The path fact on base `b`. -/
def RFact.toP (b : Base) (x : RFact) : PFact := ⟨b, x.path, x.kind, x.mark⟩

/-- The relative fact of a path fact (the base is removed). -/
def ofP (f : PFact) : RFact := ⟨f.path, f.kind, f.mark⟩

/-- The abstract mark of a tree with the mark exclusion `X`: `*` if `X` is empty,
    else `*∖X`. -/
def starM : List Mark → MarkA
  | []     => .star
  | t :: x => .starEx (t :: x)

/-- Read a stored mark in a tree with the mark exclusion `X`: the stored abstract
    mark `*` becomes `starM X`; other marks do not change. -/
def mxMark (X : List Mark) : MarkA → MarkA
  | .star => starM X
  | m     => m

/-- Read a stored relative fact in a tree with the mark exclusion `X`. -/
def markX (X : List Mark) (x : RFact) : RFact := ⟨x.path, x.kind, mxMark X x.mark⟩

/-- The stored form of a mark: every abstract mark becomes the flag `*`. -/
def stripM : MarkA → MarkA
  | .starEx _ => .star
  | m         => m

/-- The stored form of a path fact. -/
def stripF (f : PFact) : PFact := ⟨f.base, f.path, f.kind, stripM f.mark⟩

/-- The intersection of two mark exclusions. -/
def mxInter (x1 x2 : List Mark) : List Mark := x1.filter (fun t => memB t x2)

/-- The final part of `den`: with the initial continuation `σ` and the initial
    mark `m0`, the fact reaches the final path `q` with the final mark `m1`. -/
def RFact.sem (x : RFact) (σ : List Acc) (m0 : Mark) (q : List Acc) (m1 : Mark) : Prop :=
  m1 = x.mark.out m0 ∧ x.mark.passes m0 ∧ ∃ τ, q = x.path ++ τ ∧ tailF x.kind σ τ

/-- The meaning of a list of relative facts. -/
def semL (L : List RFact) (σ : List Acc) (m0 : Mark) (q : List Acc) (m1 : Mark) : Prop :=
  ∃ x, x ∈ L ∧ x.sem σ m0 q m1

/-- Two lists of relative facts have the same meaning. -/
def Eqv (L1 L2 : List RFact) : Prop :=
  ∀ σ m0 q m1, semL L1 σ m0 q m1 ↔ semL L2 σ m0 q m1

/-- The denotation of a list of final facts under the initial fact `i`. -/
def denL (i : PFact) (fs : List PFact) (l0 l1 : Loc) : Prop :=
  ∃ f, f ∈ fs ∧ den i f l0 l1

theorem den_toP {i : PFact} {b : Base} {x : RFact} {l0 l1 : Loc} :
    den i (x.toP b) l0 l1 ↔
      (l0.base = i.base ∧ l1.base = b ∧ i.mark.admits l0.mark ∧
        ∃ σ, l0.path = i.path ++ σ ∧ tailI i.kind σ ∧ x.sem σ l0.mark l1.path l1.mark) := by
  constructor
  · rintro ⟨h1, h2, h3, h4, hp, σ, τ, h5, h6, h7, h8⟩
    exact ⟨h1, h2, h3, σ, h5, h7, h4, hp, τ, h6, h8⟩
  · rintro ⟨h1, h2, h3, σ, h5, h7, h4, hp, τ, h6, h8⟩
    exact ⟨h1, h2, h3, h4, hp, σ, τ, h5, h6, h7, h8⟩

theorem denL_map {i : PFact} {b : Base} {L : List RFact} {l0 l1 : Loc} :
    denL i (L.map (RFact.toP b)) l0 l1 ↔
      (l0.base = i.base ∧ l1.base = b ∧ i.mark.admits l0.mark ∧
        ∃ σ, l0.path = i.path ++ σ ∧ tailI i.kind σ ∧ semL L σ l0.mark l1.path l1.mark) := by
  constructor
  · rintro ⟨f, hf, hd⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
    obtain ⟨h1, h2, h3, σ, h5, h7, h8⟩ := den_toP.mp hd
    exact ⟨h1, h2, h3, σ, h5, h7, x, hx, h8⟩
  · rintro ⟨h1, h2, h3, σ, h5, h7, x, hx, h8⟩
    exact ⟨x.toP b, List.mem_map.mpr ⟨x, hx, rfl⟩, den_toP.mpr ⟨h1, h2, h3, σ, h5, h7, h8⟩⟩

/-- Equal meaning gives equal denotation, for each base and each initial fact. -/
theorem Eqv.den {L1 L2 : List RFact} (h : Eqv L1 L2) {i : PFact} {b : Base} {l0 l1 : Loc} :
    denL i (L1.map (RFact.toP b)) l0 l1 ↔ denL i (L2.map (RFact.toP b)) l0 l1 := by
  rw [denL_map, denL_map]
  constructor
  · rintro ⟨h1, h2, h3, σ, h5, h7, h8⟩
    exact ⟨h1, h2, h3, σ, h5, h7, (h σ _ _ _).mp h8⟩
  · rintro ⟨h1, h2, h3, σ, h5, h7, h8⟩
    exact ⟨h1, h2, h3, σ, h5, h7, (h σ _ _ _).mpr h8⟩

theorem Eqv.refl (L : List RFact) : Eqv L L := fun _ _ _ _ => Iff.rfl

theorem Eqv.symm {L1 L2 : List RFact} (h : Eqv L1 L2) : Eqv L2 L1 :=
  fun σ m0 q m1 => (h σ m0 q m1).symm

theorem Eqv.trans {L1 L2 L3 : List RFact} (h1 : Eqv L1 L2) (h2 : Eqv L2 L3) : Eqv L1 L3 :=
  fun σ m0 q m1 => (h1 σ m0 q m1).trans (h2 σ m0 q m1)

theorem Eqv.of_mem {L1 L2 : List RFact} (h : ∀ x, x ∈ L1 ↔ x ∈ L2) : Eqv L1 L2 := by
  intro σ m0 q m1
  constructor
  · rintro ⟨x, hx, hs⟩; exact ⟨x, (h x).mp hx, hs⟩
  · rintro ⟨x, hx, hs⟩; exact ⟨x, (h x).mpr hx, hs⟩

theorem semL_append {A B : List RFact} {σ m0 q m1} :
    semL (A ++ B) σ m0 q m1 ↔ semL A σ m0 q m1 ∨ semL B σ m0 q m1 := by
  constructor
  · rintro ⟨x, hx, hs⟩
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl ⟨x, h, hs⟩
    · exact Or.inr ⟨x, h, hs⟩
  · rintro (⟨x, hx, hs⟩ | ⟨x, hx, hs⟩)
    · exact ⟨x, List.mem_append.mpr (Or.inl hx), hs⟩
    · exact ⟨x, List.mem_append.mpr (Or.inr hx), hs⟩

theorem Eqv.append {A A' B B' : List RFact} (h1 : Eqv A A') (h2 : Eqv B B') :
    Eqv (A ++ B) (A' ++ B') := by
  intro σ m0 q m1
  rw [semL_append, semL_append, h1 σ m0 q m1, h2 σ m0 q m1]

theorem Eqv.append_comm (A B : List RFact) : Eqv (A ++ B) (B ++ A) := by
  intro σ m0 q m1
  rw [semL_append, semL_append]
  exact Or.comm

theorem Eqv.nil_append (A : List RFact) : Eqv ([] ++ A) A := fun _ _ _ _ => Iff.rfl

theorem RFact.sem_cons {a : Acc} {x : RFact} {σ m0 q m1} :
    (x.cons a).sem σ m0 q m1 ↔ ∃ q', q = a :: q' ∧ x.sem σ m0 q' m1 := by
  constructor
  · rintro ⟨hm, hp, τ, hq, ht⟩
    exact ⟨x.path ++ τ, hq, hm, hp, τ, rfl, ht⟩
  · rintro ⟨q', rfl, hm, hp, τ, rfl, ht⟩
    exact ⟨hm, hp, τ, rfl, ht⟩

theorem semL_map_cons {a : Acc} {A : List RFact} {σ m0 q m1} :
    semL (A.map (RFact.cons a)) σ m0 q m1 ↔ ∃ q', q = a :: q' ∧ semL A σ m0 q' m1 := by
  constructor
  · rintro ⟨y, hy, hs⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨q', hq, hs'⟩ := RFact.sem_cons.mp hs
    exact ⟨q', hq, x, hx, hs'⟩
  · rintro ⟨q', hq, x, hx, hs⟩
    exact ⟨x.cons a, List.mem_map.mpr ⟨x, hx, rfl⟩, RFact.sem_cons.mpr ⟨q', hq, hs⟩⟩

theorem Eqv.map_cons {a : Acc} {A B : List RFact} (h : Eqv A B) :
    Eqv (A.map (RFact.cons a)) (B.map (RFact.cons a)) := by
  intro σ m0 q m1
  rw [semL_map_cons, semL_map_cons]
  constructor
  · rintro ⟨q', hq, hs⟩; exact ⟨q', hq, (h σ m0 q' m1).mp hs⟩
  · rintro ⟨q', hq, hs⟩; exact ⟨q', hq, (h σ m0 q' m1).mpr hs⟩

theorem denL_append' {i : PFact} {A B : List PFact} {l0 l1 : Loc} :
    denL i (A ++ B) l0 l1 ↔ denL i A l0 l1 ∨ denL i B l0 l1 := by
  constructor
  · rintro ⟨f, hf, hd⟩
    rcases List.mem_append.mp hf with h | h
    · exact Or.inl ⟨f, h, hd⟩
    · exact Or.inr ⟨f, h, hd⟩
  · rintro (⟨f, hf, hd⟩ | ⟨f, hf, hd⟩)
    · exact ⟨f, List.mem_append.mpr (Or.inl hf), hd⟩
    · exact ⟨f, List.mem_append.mpr (Or.inr hf), hd⟩

/-! ### The memberships of two lists are equal -/

/-- Two lists of relative facts have the same members. -/
def MemEq (A B : List RFact) : Prop := ∀ y, y ∈ A ↔ y ∈ B

theorem MemEq.refl (A : List RFact) : MemEq A A := fun _ => Iff.rfl

theorem MemEq.trans {A B C : List RFact} (h1 : MemEq A B) (h2 : MemEq B C) : MemEq A C :=
  fun y => (h1 y).trans (h2 y)

theorem MemEq.append {A A' B B' : List RFact} (h1 : MemEq A A') (h2 : MemEq B B') :
    MemEq (A ++ B) (A' ++ B') := by
  intro y; rw [List.mem_append, List.mem_append, h1 y, h2 y]

theorem MemEq.append_comm (A B : List RFact) : MemEq (A ++ B) (B ++ A) := by
  intro y; rw [List.mem_append, List.mem_append]; exact Or.comm

theorem MemEq.map_cons {a : Acc} {A B : List RFact} (h : MemEq A B) :
    MemEq (A.map (RFact.cons a)) (B.map (RFact.cons a)) := by
  intro y
  rw [List.mem_map, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, (h x).mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, (h x).mpr hx, rfl⟩

theorem MemEq.eqv {A B : List RFact} (h : MemEq A B) : Eqv A B := Eqv.of_mem h

/-! ### The denotation of a list of final facts with their layer -/

/-- The pairs of the facts of the layer `d`. -/
def denA (i : PFact) (as : List AFact) (d : Bool) (l0 l1 : Loc) : Prop :=
  ∃ a, a ∈ as ∧ a.demand = d ∧ den i a.fact l0 l1

theorem denA_append {i : PFact} {A B : List AFact} {d : Bool} {l0 l1 : Loc} :
    denA i (A ++ B) d l0 l1 ↔ denA i A d l0 l1 ∨ denA i B d l0 l1 := by
  constructor
  · rintro ⟨a, ha, hd, hden⟩
    rcases List.mem_append.mp ha with h | h
    · exact Or.inl ⟨a, h, hd, hden⟩
    · exact Or.inr ⟨a, h, hd, hden⟩
  · rintro (⟨a, ha, hd, hden⟩ | ⟨a, ha, hd, hden⟩)
    · exact ⟨a, List.mem_append.mpr (Or.inl ha), hd, hden⟩
    · exact ⟨a, List.mem_append.mpr (Or.inr ha), hd, hden⟩

/-! ### A decision procedure for `den` (for the decide-checked examples) -/

theorem dropPrefix_spec (p q r : List Acc) : dropPrefix p q = some r ↔ q = p ++ r := by
  induction p generalizing q with
  | nil =>
    show some q = some r ↔ q = r
    exact ⟨fun h => by cases h; rfl, fun h => by rw [h]⟩
  | cons a p ih =>
    cases q with
    | nil =>
      exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    | cons c q =>
      show (if Nat.beq a c = true then dropPrefix p q else none) = some r ↔ c :: q = a :: (p ++ r)
      rcases Bool.eq_false_or_eq_true (Nat.beq a c) with h | h
      · have hac : a = c := Nat.eq_of_beq_eq_true h
        subst hac
        simp only [h, ↓reduceIte, ih]
        constructor
        · intro h'; rw [h']
        · intro h'; cases h'; rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        constructor
        · intro h'; exact nomatch h'
        · intro h'
          cases h'
          rw [Nat.beq_refl] at h
          exact nomatch h

def tailFB : Kind → List Acc → List Acc → Bool
  | .star e, σ, τ => decide (τ = σ) && e.admits σ
  | .any,    _, _ => true
  | .exact,  _, τ => τ.isEmpty

def markAdmB : MarkA → Mark → Bool
  | .star,     _ => true
  | .conc t,   m => Nat.beq m t
  | .starEx x, m => !memB m x

/-- `MarkA.passes` as a Boolean function. -/
def passesB : MarkA → Mark → Bool
  | .starEx x, m => !memB m x
  | _,         _ => true

/-- `den` as a Boolean function. -/
def denB (i f : PFact) (l0 l1 : Loc) : Bool :=
  Nat.beq l0.base i.base && Nat.beq l1.base f.base && markAdmB i.mark l0.mark &&
    Nat.beq l1.mark (f.mark.out l0.mark) && passesB f.mark l0.mark &&
    (match dropPrefix i.path l0.path, dropPrefix f.path l1.path with
     | some σ, some τ => admitsTailB i.kind σ && tailFB f.kind σ τ
     | _,      _      => false)

theorem beq_iff {a b : Nat} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h]; exact Nat.beq_refl b⟩

theorem tailI_iff (k : Kind) (σ : List Acc) : tailI k σ ↔ admitsTailB k σ = true := by
  cases k with
  | star e => exact Iff.rfl
  | any => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | exact =>
    cases σ with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons a r => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem tailF_iff (k : Kind) (σ τ : List Acc) : tailF k σ τ ↔ tailFB k σ τ = true := by
  cases k with
  | star e =>
    show (τ = σ ∧ e.admits σ = true) ↔ (decide (τ = σ) && e.admits σ) = true
    rw [Bool.and_eq_true, decide_eq_true_iff]
  | any => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | exact =>
    show τ = [] ↔ τ.isEmpty = true
    cases τ with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons a r => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem markAdm_iff (m : MarkA) (t : Mark) : m.admits t ↔ markAdmB m t = true := by
  cases m with
  | star => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | conc c => exact beq_iff.symm
  | starEx x =>
    show memB t x = false ↔ (!memB t x) = true
    rw [Bool.not_eq_true']

theorem passes_iff (m : MarkA) (t : Mark) : m.passes t ↔ passesB m t = true := by
  cases m with
  | star => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | conc c => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | starEx x =>
    show memB t x = false ↔ (!memB t x) = true
    rw [Bool.not_eq_true']

theorem den_iff_denB (i f : PFact) (l0 l1 : Loc) : den i f l0 l1 ↔ denB i f l0 l1 = true := by
  unfold den denB
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    beq_iff, beq_iff, beq_iff, ← markAdm_iff, ← passes_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, hp, σ, τ, h5, h6, h7, h8⟩
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hp⟩, ?_⟩
    rw [(dropPrefix_spec _ _ σ).mpr h5, (dropPrefix_spec _ _ τ).mpr h6]
    show (admitsTailB i.kind σ && tailFB f.kind σ τ) = true
    rw [Bool.and_eq_true, ← tailI_iff, ← tailF_iff]
    exact ⟨h7, h8⟩
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hp⟩, h5⟩
    refine ⟨h1, h2, h3, h4, hp, ?_⟩
    cases hσ : dropPrefix i.path l0.path with
    | none => rw [hσ] at h5; exact nomatch h5
    | some σ =>
      cases hτ : dropPrefix f.path l1.path with
      | none => rw [hσ, hτ] at h5; exact nomatch h5
      | some τ =>
        rw [hσ, hτ] at h5
        have h5' : (admitsTailB i.kind σ && tailFB f.kind σ τ) = true := h5
        rw [Bool.and_eq_true, ← tailI_iff, ← tailF_iff] at h5'
        exact ⟨σ, τ, (dropPrefix_spec _ _ _).mp hσ, (dropPrefix_spec _ _ _).mp hτ, h5'.1, h5'.2⟩

/-- `denA` as a Boolean function. -/
def denAB (i : PFact) (as : List AFact) (d : Bool) (l0 l1 : Loc) : Bool :=
  match as with
  | []      => false
  | a :: as => (decide (a.demand = d) && denB i a.fact l0 l1) || denAB i as d l0 l1

theorem denA_iff_denAB (i : PFact) (as : List AFact) (d : Bool) (l0 l1 : Loc) :
    denA i as d l0 l1 ↔ denAB i as d l0 l1 = true := by
  induction as with
  | nil => exact ⟨fun ⟨_, h, _⟩ => (nomatch h), fun h => (nomatch h)⟩
  | cons a as ih =>
    show _ ↔ ((decide (a.demand = d) && denB i a.fact l0 l1) || denAB i as d l0 l1) = true
    rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, ← den_iff_denB, ← ih]
    constructor
    · rintro ⟨x, hx, hd, hden⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl ⟨hd, hden⟩
      · exact Or.inr ⟨x, hx, hd, hden⟩
    · rintro (⟨hd, hden⟩ | ⟨x, hx, hd, hden⟩)
      · exact ⟨a, List.mem_cons_self .., hd, hden⟩
      · exact ⟨x, List.mem_cons_of_mem _ hx, hd, hden⟩

/-! ## 2. The payload of a node -/

/-- A set of marks: `star` is the abstract mark (the flag `*`; in an edge tree
    with the mark exclusion `X` it means `starM X`), `conc` the concrete marks. -/
structure MarkSet where
  star : Bool
  conc : List Mark
deriving DecidableEq, Repr

def MarkSet.empty : MarkSet := ⟨false, []⟩

/-- Union of two mark sets. -/
def MarkSet.union (m1 m2 : MarkSet) : MarkSet := ⟨m1.star || m2.star, m1.conc ++ m2.conc⟩

/-- Add one mark (no duplicate concrete mark). Every abstract mark sets the flag
    `*` (the mark exclusion belongs to the tree, as the exclusion `E` does). -/
def MarkSet.add : MarkA → MarkSet → MarkSet
  | .star,     ms => ⟨true, ms.conc⟩
  | .conc t,   ms => if memB t ms.conc then ms else ⟨ms.star, t :: ms.conc⟩
  | .starEx _, ms => ⟨true, ms.conc⟩

/-- The mark set contains the mark (in the stored form: `*∖x` is never stored). -/
def MarkSet.Has (ms : MarkSet) : MarkA → Prop
  | .star     => ms.star = true
  | .conc t   => t ∈ ms.conc
  | .starEx _ => False

/-- The payload of the node at path `p` of a tree with exclusion `E`:
    * `star = true` — the abstract leaf `p.*/E` (stored mark `*`; `E` and the mark
                      exclusion are the tree's),
    * `anyM`        — the leaves `p.[any]` with these marks (no exclusion, W1),
    * `exactM`      — the leaves `p.$` with these marks. -/
structure Payload where
  star   : Bool
  anyM   : MarkSet
  exactM : MarkSet
deriving DecidableEq, Repr

def Payload.empty : Payload := ⟨false, MarkSet.empty, MarkSet.empty⟩

/-- Merge rule 1 at one node: `*` flags by OR, mark sets by union. -/
def Payload.union (p1 p2 : Payload) : Payload :=
  ⟨p1.star || p2.star, p1.anyM.union p2.anyM, p1.exactM.union p2.exactM⟩

/-- A path fact in the stored form FITS a tree with exclusion `E`: a `*` tail has
    the exclusion `E` and the mark `*`; the mark `*∖x` is not a stored mark. -/
def fitsB (E : Excl) (k : Kind) (m : MarkA) : Bool :=
  match k, m with
  | .star e, .star     => decide (e = E)
  | _,       .starEx _ => false
  | .star _, .conc _   => false
  | _,       _         => true

/-- The mark `m` is a mark of a tree with the mark exclusion `X`: a concrete mark,
    or the abstract mark `starM X` of the tree. -/
def markFitsB (X : List Mark) : MarkA → Bool
  | .conc _ => true
  | m       => decide (m = starM X)

/-- A path fact FITS an edge tree with the exclusion `E` and the mark exclusion
    `X`: its stored form fits `E`, and its mark is a mark of the tree. -/
def fitsX (E : Excl) (X : List Mark) (k : Kind) (m : MarkA) : Bool :=
  fitsB E k (stripM m) && markFitsB X m

/-- Add one leaf to a payload (the `*` exclusion must be the tree's). -/
def Payload.add (k : Kind) (m : MarkA) (pl : Payload) : Payload :=
  match k with
  | .star _ => ⟨true, pl.anyM, pl.exactM⟩
  | .any    => ⟨pl.star, pl.anyM.add m, pl.exactM⟩
  | .exact  => ⟨pl.star, pl.anyM, pl.exactM.add m⟩

def starRF (E : Excl) (s : Bool) : List RFact :=
  if s then [⟨[], .star E, .star⟩] else []

def msRF (k : Kind) (ms : MarkSet) : List RFact :=
  (if ms.star then [⟨[], k, .star⟩] else []) ++ ms.conc.map (fun t => ⟨[], k, .conc t⟩)

/-- The facts of a payload in a tree with exclusion `E` (all paths are empty). -/
def payRF (E : Excl) (pl : Payload) : List RFact :=
  starRF E pl.star ++ msRF .any pl.anyM ++ msRF .exact pl.exactM

/-! ### Lemmas on exclusions and marks -/

theorem memB_iff {a : Acc} {l : List Acc} : memB a l = true ↔ a ∈ l := by
  induction l with
  | nil => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | cons b bs ih =>
    show (Nat.beq a b || memB a bs) = true ↔ a ∈ b :: bs
    rw [Bool.or_eq_true, List.mem_cons, ih]
    constructor
    · rintro (h | h)
      · exact Or.inl (Nat.eq_of_beq_eq_true h)
      · exact Or.inr h
    · rintro (h | h)
      · subst h; exact Or.inl (Nat.beq_refl a)
      · exact Or.inr h

theorem memB_filter {a : Acc} {xs ys : List Acc} :
    memB a (xs.filter (fun b => memB b ys)) = (memB a xs && memB a ys) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.filter_cons]
    cases hb : memB b ys with
    | true =>
      simp only [↓reduceIte]
      show (Nat.beq a b || memB a (List.filter (fun b => memB b ys) bs)) =
        ((Nat.beq a b || memB a bs) && memB a ys)
      rw [ih]
      cases hab : Nat.beq a b with
      | true =>
        have hab' : a = b := Nat.eq_of_beq_eq_true hab
        subst hab'
        rw [hb]; rfl
      | false => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      show (memB a bs && memB a ys) = ((Nat.beq a b || memB a bs) && memB a ys)
      cases hab : Nat.beq a b with
      | true =>
        have hab' : a = b := Nat.eq_of_beq_eq_true hab
        subst hab'
        rw [hb]; simp only [Bool.and_false]
      | false => rfl

/-- WHY intersection is the exact join of two `*` leaves: the intersection
    admits a continuation iff one of the two exclusions admits it. -/
theorem admits_inter (e1 e2 : Excl) (σ : List Acc) :
    (Excl.inter e1 e2).admits σ = (e1.admits σ || e2.admits σ) := by
  cases σ with
  | nil => cases e1 <;> cases e2 <;> rfl
  | cons a r =>
    cases e1 with
    | univ => cases e2 <;> rfl
    | set xs =>
      cases e2 with
      | univ => show (!memB a xs) = ((!memB a xs) || false); rw [Bool.or_false]
      | set ys =>
        show (!memB a (xs.filter (fun b => memB b ys))) = ((!memB a xs) || !memB a ys)
        rw [memB_filter, Bool.not_and]

/-- The admits test of a non-empty continuation reads only its first accessor. -/
theorem admits_cons (e : Excl) (a : Acc) (r : List Acc) :
    e.admits (a :: r) = e.admits [a] := by
  cases e <;> rfl

theorem Excl.admits_nil (e : Excl) : e.admits [] = true := by
  cases e <;> rfl

theorem has_union {m1 m2 : MarkSet} {m : MarkA} :
    (m1.union m2).Has m ↔ m1.Has m ∨ m2.Has m := by
  cases m with
  | star =>
    show (m1.star || m2.star) = true ↔ m1.star = true ∨ m2.star = true
    rw [Bool.or_eq_true]
  | conc t => exact List.mem_append
  | starEx x => exact ⟨fun h => h.elim, fun h => h.elim id id⟩

theorem has_empty {m : MarkA} : ¬ MarkSet.empty.Has m := by
  cases m with
  | star => exact fun h => nomatch h
  | conc t => exact fun h => nomatch h
  | starEx x => exact fun h => h

/-- Adding a mark adds its stored form (version 5: `stripM m`; for `*` and `conc t`
    it is `m`). -/
theorem has_add {ms : MarkSet} {m m' : MarkA} :
    (ms.add m).Has m' ↔ m' = stripM m ∨ ms.Has m' := by
  have hstar : ∀ ms' : MarkSet, (⟨true, ms'.conc⟩ : MarkSet).Has m' ↔ m' = .star ∨ ms'.Has m' := by
    intro ms'
    cases m' with
    | star => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
    | conc t' =>
      constructor
      · intro h; exact Or.inr h
      · rintro (h | h)
        · exact nomatch h
        · exact h
    | starEx x' =>
      constructor
      · intro h; exact h.elim
      · rintro (h | h)
        · exact nomatch h
        · exact h
  cases m with
  | star => exact hstar ms
  | starEx x => exact hstar ms
  | conc t =>
    show _ ↔ m' = .conc t ∨ ms.Has m'
    cases hm : memB t ms.conc with
    | true =>
      have hmem : t ∈ ms.conc := memB_iff.mp hm
      have hadd : ms.add (.conc t) = ms := by simp only [MarkSet.add, hm, ↓reduceIte]
      rw [hadd]
      constructor
      · intro h; exact Or.inr h
      · rintro (h | h)
        · subst h; exact hmem
        · exact h
    | false =>
      have hadd : ms.add (.conc t) = ⟨ms.star, t :: ms.conc⟩ := by
        simp only [MarkSet.add, hm, Bool.false_eq_true, ↓reduceIte]
      rw [hadd]
      cases m' with
      | star =>
        constructor
        · intro h; exact Or.inr h
        · rintro (h | h)
          · exact nomatch h
          · exact h
      | conc t' =>
        show t' ∈ t :: ms.conc ↔ _
        rw [List.mem_cons]
        constructor
        · rintro (h | h)
          · subst h; exact Or.inl rfl
          · exact Or.inr h
        · rintro (h | h)
          · cases h; exact Or.inl rfl
          · exact Or.inr h
      | starEx x' =>
        constructor
        · intro h; exact h.elim
        · rintro (h | h)
          · exact nomatch h
          · exact h

theorem mem_starRF {E : Excl} {s : Bool} {y : RFact} :
    y ∈ starRF E s ↔ s = true ∧ y = ⟨[], .star E, .star⟩ := by
  cases s with
  | false => exact ⟨fun h => (nomatch h), fun ⟨h, _⟩ => (nomatch h)⟩
  | true =>
    show y ∈ [_] ↔ _
    rw [List.mem_singleton]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

theorem mem_msRF {k : Kind} {ms : MarkSet} {y : RFact} :
    y ∈ msRF k ms ↔ ∃ m, ms.Has m ∧ y = ⟨[], k, m⟩ := by
  unfold msRF
  rw [List.mem_append]
  constructor
  · rintro (h | h)
    · cases hs : ms.star with
      | true =>
        rw [hs] at h
        exact ⟨.star, hs, List.mem_singleton.mp h⟩
      | false =>
        rw [hs] at h
        exact nomatch h
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
      exact ⟨.conc t, ht, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    cases m with
    | star =>
      left
      have hs : ms.star = true := hm
      rw [hs]
      exact List.mem_singleton.mpr rfl
    | conc t =>
      right
      exact List.mem_map.mpr ⟨t, hm, rfl⟩
    | starEx x => exact hm.elim

theorem mem_payRF {E : Excl} {pl : Payload} {y : RFact} :
    y ∈ payRF E pl ↔
      (pl.star = true ∧ y = ⟨[], .star E, .star⟩) ∨
      (∃ m, pl.anyM.Has m ∧ y = ⟨[], .any, m⟩) ∨
      (∃ m, pl.exactM.Has m ∧ y = ⟨[], .exact, m⟩) := by
  unfold payRF
  rw [List.mem_append, List.mem_append, mem_starRF, mem_msRF, mem_msRF, or_assoc]

theorem sem_star_inter {e1 e2 : Excl} {σ m0 q m1} :
    RFact.sem ⟨[], .star (Excl.inter e1 e2), .star⟩ σ m0 q m1 ↔
      RFact.sem ⟨[], .star e1, .star⟩ σ m0 q m1 ∨ RFact.sem ⟨[], .star e2, .star⟩ σ m0 q m1 := by
  constructor
  · rintro ⟨hm, hp, τ, hq, hτ, ha⟩
    have ha' : (e1.admits σ || e2.admits σ) = true := by rw [← admits_inter]; exact ha
    cases h1 : e1.admits σ with
    | true => exact Or.inl ⟨hm, hp, τ, hq, hτ, h1⟩
    | false =>
      rw [h1, Bool.false_or] at ha'
      exact Or.inr ⟨hm, hp, τ, hq, hτ, ha'⟩
  · rintro (⟨hm, hp, τ, hq, hτ, ha⟩ | ⟨hm, hp, τ, hq, hτ, ha⟩)
    · refine ⟨hm, hp, τ, hq, hτ, ?_⟩
      show (Excl.inter e1 e2).admits σ = true
      rw [admits_inter, ha, Bool.true_or]
    · refine ⟨hm, hp, τ, hq, hτ, ?_⟩
      show (Excl.inter e1 e2).admits σ = true
      rw [admits_inter, ha, Bool.or_true]

theorem msRF_union_mem {k : Kind} {m1 m2 : MarkSet} {y : RFact} :
    y ∈ msRF k (m1.union m2) ↔ y ∈ msRF k m1 ++ msRF k m2 := by
  rw [List.mem_append, mem_msRF, mem_msRF, mem_msRF]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rcases has_union.mp hm with h | h
    · exact Or.inl ⟨m, h, rfl⟩
    · exact Or.inr ⟨m, h, rfl⟩
  · rintro (⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    · exact ⟨m, has_union.mpr (Or.inl hm), rfl⟩
    · exact ⟨m, has_union.mpr (Or.inr hm), rfl⟩

theorem Payload.union_mem (E : Excl) (p1 p2 : Payload) :
    MemEq (payRF E (p1.union p2)) (payRF E p1 ++ payRF E p2) := by
  intro y
  rw [List.mem_append, mem_payRF, mem_payRF, mem_payRF]
  constructor
  · rintro (⟨hs, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
    · have hs' : (p1.star || p2.star) = true := hs
      rw [Bool.or_eq_true] at hs'
      rcases hs' with h | h
      · exact Or.inl (Or.inl ⟨h, rfl⟩)
      · exact Or.inr (Or.inl ⟨h, rfl⟩)
    · rcases has_union.mp hm with h | h
      · exact Or.inl (Or.inr (Or.inl ⟨m, h, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨m, h, rfl⟩))
    · rcases has_union.mp hm with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨m, h, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨m, h, rfl⟩))
  · rintro ((⟨hs, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩) | (⟨hs, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩))
    · exact Or.inl ⟨by show (p1.star || p2.star) = true; rw [hs]; rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨m, has_union.mpr (Or.inl hm), rfl⟩)
    · exact Or.inr (Or.inr ⟨m, has_union.mpr (Or.inl hm), rfl⟩)
    · exact Or.inl ⟨by show (p1.star || p2.star) = true; rw [hs, Bool.or_true], rfl⟩
    · exact Or.inr (Or.inl ⟨m, has_union.mpr (Or.inr hm), rfl⟩)
    · exact Or.inr (Or.inr ⟨m, has_union.mpr (Or.inr hm), rfl⟩)

/-- A fitting mark is in the stored form. -/
theorem fitsB_strip {E : Excl} {k : Kind} {m : MarkA} (hf : fitsB E k m = true) : stripM m = m := by
  cases k <;> cases m <;> first | rfl | exact nomatch hf

/-- Adding a fitting leaf to a payload adds exactly that leaf. -/
theorem Payload.add_mem (E : Excl) {k : Kind} {m : MarkA} (pl : Payload) (hf : fitsB E k m = true) :
    MemEq (payRF E (pl.add k m)) (payRF E pl ++ [⟨[], k, m⟩]) := by
  intro y
  rw [List.mem_append, List.mem_singleton]
  have hs := fitsB_strip hf
  cases k with
  | star e =>
    cases m with
    | conc t => exact nomatch hf
    | starEx x => exact nomatch hf
    | star =>
      have he : e = E := of_decide_eq_true hf
      subst he
      show y ∈ payRF e ⟨true, pl.anyM, pl.exactM⟩ ↔ _
      rw [mem_payRF, mem_payRF]
      constructor
      · rintro (⟨_, rfl⟩ | h | h)
        · exact Or.inr rfl
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inl (Or.inr (Or.inr h))
      · rintro ((⟨_, rfl⟩ | h | h) | rfl)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl ⟨rfl, rfl⟩
  | any =>
    show y ∈ payRF E ⟨pl.star, pl.anyM.add m, pl.exactM⟩ ↔ _
    rw [mem_payRF, mem_payRF]
    constructor
    · rintro (h | ⟨m', hm', rfl⟩ | h)
      · exact Or.inl (Or.inl h)
      · rcases has_add.mp hm' with h | h
        · rw [h, hs]; exact Or.inr rfl
        · exact Or.inl (Or.inr (Or.inl ⟨m', h, rfl⟩))
      · exact Or.inl (Or.inr (Or.inr h))
    · rintro ((h | ⟨m', hm', rfl⟩ | h) | rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨m', has_add.mpr (Or.inr hm'), rfl⟩)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl ⟨m, has_add.mpr (Or.inl hs.symm), rfl⟩)
  | exact =>
    show y ∈ payRF E ⟨pl.star, pl.anyM, pl.exactM.add m⟩ ↔ _
    rw [mem_payRF, mem_payRF]
    constructor
    · rintro (h | h | ⟨m', hm', rfl⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · rcases has_add.mp hm' with h | h
        · rw [h, hs]; exact Or.inr rfl
        · exact Or.inl (Or.inr (Or.inr ⟨m', h, rfl⟩))
    · rintro ((h | h | ⟨m', hm', rfl⟩) | rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨m', has_add.mpr (Or.inr hm'), rfl⟩)
      · exact Or.inr (Or.inr ⟨m, has_add.mpr (Or.inl hs.symm), rfl⟩)

/-! ## 3. The trie and the edge tree -/

/-- The children of a node, as a left-child / right-sibling list:
    `cons a here below next` is the child with accessor `a`, its payload `here`,
    its own children `below`, and the next sibling `next`. -/
inductive Trie where
  | nil
  | cons (a : Acc) (here : Payload) (below : Trie) (next : Trie)
deriving DecidableEq, Repr

structure Tree where
  root : Payload
  kids : Trie
deriving DecidableEq, Repr

def emptyTree : Tree := ⟨Payload.empty, .nil⟩

/-- The relative facts of the children, in a tree with exclusion `E`. -/
def trieRF (E : Excl) : Trie → List RFact
  | .nil => []
  | .cons a h bl nx => (payRF E h ++ trieRF E bl).map (RFact.cons a) ++ trieRF E nx

/-- The relative facts of a tree with exclusion `E`. -/
def treeRF (E : Excl) (t : Tree) : List RFact := payRF E t.root ++ trieRF E t.kids

/-- The edge tree: ONE tree per (premise, layer, exclusion, mark exclusion). The
    premise is the initial fact of the edge; it is outside this structure. The mark
    exclusion `mx` gives the abstract mark `starM mx` of the tree. -/
structure EdgeTree where
  excl   : Excl
  mx     : List Mark
  demand : Bool
  tree   : Tree
deriving DecidableEq, Repr

/-- The final path facts of an edge tree on base `b`: the CONCEPT it encodes. -/
def toAFacts (b : Base) (t : EdgeTree) : List AFact :=
  (treeRF t.excl t.tree).map (fun x => ⟨(markX t.mx x).toP b, t.demand⟩)

theorem trieRF_cons {E : Excl} {a : Acc} {h : Payload} {bl nx : Trie} :
    trieRF E (.cons a h bl nx) = (treeRF E ⟨h, bl⟩).map (RFact.cons a) ++ trieRF E nx := rfl

theorem treeRF_empty (E : Excl) : treeRF E emptyTree = [] := rfl

theorem map_pre_nil (X : List RFact) : X.map (RFact.pre []) = X := by
  have h : RFact.pre [] = id := funext (fun _ => rfl)
  rw [h, List.map_id]

theorem map_cons_pre (a : Acc) (p : List Acc) (X : List RFact) :
    (X.map (RFact.pre p)).map (RFact.cons a) = X.map (RFact.pre (a :: p)) := by
  rw [List.map_map]; rfl

theorem mem_toAFacts (b : Base) (t : EdgeTree) (a : AFact) :
    a ∈ toAFacts b t ↔ ∃ x, x ∈ treeRF t.excl t.tree ∧ a = ⟨(markX t.mx x).toP b, t.demand⟩ := by
  unfold toAFacts
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem denA_toAFacts {i : PFact} {b : Base} {t : EdgeTree} {d : Bool} {l0 l1 : Loc} :
    denA i (toAFacts b t) d l0 l1 ↔
      t.demand = d ∧ denL i (((treeRF t.excl t.tree).map (markX t.mx)).map (RFact.toP b)) l0 l1 := by
  constructor
  · rintro ⟨a, ha, hd, hden⟩
    obtain ⟨x, hx, rfl⟩ := (mem_toAFacts b t a).mp ha
    exact ⟨hd, (markX t.mx x).toP b,
      List.mem_map.mpr ⟨markX t.mx x, List.mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩, hden⟩
  · rintro ⟨hd, f, hf, hden⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact ⟨⟨(markX t.mx x).toP b, t.demand⟩, (mem_toAFacts b t _).mpr ⟨x, hx, rfl⟩, hd, hden⟩

/-! ### The walk that changes the subtree at a path -/

/-- Change the child with accessor `a` by `g` (make it if it is absent). -/
def insK (a : Acc) (g : Tree → Tree) : Trie → Trie
  | .nil => .cons a (g emptyTree).root (g emptyTree).kids .nil
  | .cons c h bl nx =>
    if Nat.beq a c then .cons c (g ⟨h, bl⟩).root (g ⟨h, bl⟩).kids nx
    else .cons c h bl (insK a g nx)

/-- Change the subtree at path `p` by `g` (make the path if it is absent). -/
def atPath : List Acc → (Tree → Tree) → Tree → Tree
  | [],     g, t => g t
  | a :: p, g, t => ⟨t.root, insK a (atPath p g) t.kids⟩

theorem insK_mem {E : Excl} {a : Acc} {G : Tree → Tree} {Y : List RFact}
    (hG : ∀ s, MemEq (treeRF E (G s)) (treeRF E s ++ Y)) (k : Trie) :
    MemEq (trieRF E (insK a G k)) (trieRF E k ++ Y.map (RFact.cons a)) := by
  induction k with
  | nil =>
    show MemEq ((treeRF E (G emptyTree)).map (RFact.cons a) ++ []) ([] ++ Y.map (RFact.cons a))
    rw [List.append_nil]
    exact MemEq.map_cons (hG emptyTree)
  | cons c h bl nx _ ihn =>
    show MemEq (trieRF E (if Nat.beq a c then _ else _)) _
    rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
    · have hac' : a = c := Nat.eq_of_beq_eq_true hac
      subst hac'
      simp only [hac, ↓reduceIte]
      show MemEq ((treeRF E (G ⟨h, bl⟩)).map (RFact.cons a) ++ trieRF E nx)
        (((treeRF E ⟨h, bl⟩).map (RFact.cons a) ++ trieRF E nx) ++ Y.map (RFact.cons a))
      have h1 := MemEq.append (MemEq.map_cons (a := a) (hG ⟨h, bl⟩)) (MemEq.refl (trieRF E nx))
      refine MemEq.trans h1 ?_
      rw [List.map_append, List.append_assoc, List.append_assoc]
      exact MemEq.append (MemEq.refl _) (MemEq.append_comm _ _)
    · simp only [hac, Bool.false_eq_true, ↓reduceIte]
      show MemEq ((treeRF E ⟨h, bl⟩).map (RFact.cons c) ++ trieRF E (insK a G nx))
        (((treeRF E ⟨h, bl⟩).map (RFact.cons c) ++ trieRF E nx) ++ Y.map (RFact.cons a))
      rw [List.append_assoc]
      exact MemEq.append (MemEq.refl _) ihn

/-- `atPath p g` adds to the tree what `g` adds to the subtree, moved to `p`. -/
theorem atPath_mem {E : Excl} {g : Tree → Tree} {X : List RFact}
    (hg : ∀ s, MemEq (treeRF E (g s)) (treeRF E s ++ X)) (p : List Acc) (t : Tree) :
    MemEq (treeRF E (atPath p g t)) (treeRF E t ++ X.map (RFact.pre p)) := by
  induction p generalizing t with
  | nil => rw [map_pre_nil]; exact hg t
  | cons a p ih =>
    show MemEq (payRF E t.root ++ trieRF E (insK a (atPath p g) t.kids))
      ((payRF E t.root ++ trieRF E t.kids) ++ X.map (RFact.pre (a :: p)))
    rw [← map_cons_pre, List.append_assoc]
    exact MemEq.append (MemEq.refl _) (insK_mem ih t.kids)

/-! ## 4. Insert -/

/-- Insert one path fact (merge it into the trie). -/
def insert (f : PFact) (t : Tree) : Tree :=
  atPath f.path (fun s => ⟨s.root.add f.kind f.mark, s.kids⟩) t

theorem insert_memEq {E : Excl} {f : PFact} (hf : fitsB E f.kind f.mark = true) (t : Tree) :
    MemEq (treeRF E (insert f t)) (treeRF E t ++ [ofP f]) := by
  have hg : ∀ s : Tree, MemEq (treeRF E ⟨s.root.add f.kind f.mark, s.kids⟩)
      (treeRF E s ++ [⟨[], f.kind, f.mark⟩]) := by
    intro s
    show MemEq (payRF E (s.root.add f.kind f.mark) ++ trieRF E s.kids)
      ((payRF E s.root ++ trieRF E s.kids) ++ [⟨[], f.kind, f.mark⟩])
    refine MemEq.trans (MemEq.append (Payload.add_mem E s.root hf) (MemEq.refl _)) ?_
    rw [List.append_assoc, List.append_assoc]
    exact MemEq.append (MemEq.refl _) (MemEq.append_comm _ _)
  have h := atPath_mem hg f.path t
  have hx : [(⟨[], f.kind, f.mark⟩ : RFact)].map (RFact.pre f.path) = [ofP f] := by
    show [(⟨f.path ++ [], f.kind, f.mark⟩ : RFact)] = [⟨f.path, f.kind, f.mark⟩]
    rw [List.append_nil]
  rw [hx] at h
  exact h

theorem toP_ofP {f : PFact} {b : Base} (hb : f.base = b) : (ofP f).toP b = f := by
  cases f; cases hb; rfl

/-- The tree stores the abstract mark of a fact as the flag `*`: inserting a fact
    and inserting its stored form give the same tree. -/
theorem insert_stripF (f : PFact) (t : Tree) : insert f t = insert (stripF f) t := by
  have hp : ∀ k : Kind, ∀ pl : Payload, pl.add k f.mark = pl.add k (stripM f.mark) := by
    intro k pl
    rcases f with ⟨fb, fp, fk, fm⟩
    cases k <;> cases fm <;> rfl
  unfold insert
  show atPath f.path (fun s => ⟨s.root.add f.kind f.mark, s.kids⟩) t =
    atPath f.path (fun s => ⟨s.root.add f.kind (stripM f.mark), s.kids⟩) t
  have hg : (fun s : Tree => (⟨s.root.add f.kind f.mark, s.kids⟩ : Tree)) =
      (fun s : Tree => (⟨s.root.add f.kind (stripM f.mark), s.kids⟩ : Tree)) :=
    funext (fun s => by rw [hp f.kind s.root])
  rw [hg]

/-- A mark of the tree comes back from its stored form. -/
theorem mxMark_stripM {X : List Mark} {m : MarkA} (hm : markFitsB X m = true) :
    mxMark X (stripM m) = m := by
  cases m with
  | star => exact (of_decide_eq_true hm).symm
  | conc t => rfl
  | starEx x => exact (of_decide_eq_true hm).symm

theorem markX_ofP_stripF {X : List Mark} {f : PFact} (hm : markFitsB X f.mark = true) :
    markX X (ofP (stripF f)) = ofP f := by
  show (⟨f.path, f.kind, mxMark X (stripM f.mark)⟩ : RFact) = ⟨f.path, f.kind, f.mark⟩
  rw [mxMark_stripM hm]

theorem fitsX_parts {E : Excl} {X : List Mark} {k : Kind} {m : MarkA}
    (hf : fitsX E X k m = true) : fitsB E k (stripM m) = true ∧ markFitsB X m = true :=
  Bool.and_eq_true _ _ ▸ hf

/-- Insert into an edge tree. -/
def EdgeTree.insert (f : PFact) (t : EdgeTree) : EdgeTree :=
  ⟨t.excl, t.mx, t.demand, Tree.insert f t.tree⟩

/-- MAIN 1. Insert is exact (membership) for a fact that fits the tree.
    (Version 5: the fact fits the exclusion AND the mark exclusion, `fitsX`.) -/
theorem insert_mem {b : Base} (t : EdgeTree) (f : PFact) (hb : f.base = b)
    (hf : fitsX t.excl t.mx f.kind f.mark = true) (a : AFact) :
    a ∈ toAFacts b (t.insert f) ↔ a = ⟨f, t.demand⟩ ∨ a ∈ toAFacts b t := by
  obtain ⟨hf1, hf2⟩ := fitsX_parts hf
  rw [mem_toAFacts, mem_toAFacts]
  have h := insert_memEq (f := stripF f) hf1 t.tree
  show (∃ x, x ∈ treeRF t.excl (Tree.insert f t.tree) ∧ a = ⟨(markX t.mx x).toP b, t.demand⟩) ↔ _
  rw [insert_stripF]
  have hb' : (ofP f).toP b = f := toP_ofP hb
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases List.mem_append.mp ((h x).mp hx) with hx | hx
    · exact Or.inr ⟨x, hx, rfl⟩
    · rw [List.mem_singleton.mp hx, markX_ofP_stripF hf2, hb']; exact Or.inl rfl
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact ⟨ofP (stripF f), (h _).mpr (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))),
        by rw [markX_ofP_stripF hf2, hb']⟩
    · exact ⟨x, (h x).mpr (List.mem_append.mpr (Or.inl hx)), rfl⟩

/-! ## 5. The merge rules -/

/-- Merge the children `k2` into the children `k1`. -/
def mergeT : Trie → Trie → Trie
  | k1, .nil => k1
  | k1, .cons a h bl nx => mergeT (insK a (fun s => ⟨s.root.union h, mergeT s.kids bl⟩) k1) nx

/-- The union of two trees. -/
def merge (t1 t2 : Tree) : Tree := ⟨t1.root.union t2.root, mergeT t1.kids t2.kids⟩

theorem mergeT_mem (E : Excl) (k2 : Trie) :
    ∀ k1, MemEq (trieRF E (mergeT k1 k2)) (trieRF E k1 ++ trieRF E k2) := by
  induction k2 with
  | nil =>
    intro k1; show MemEq (trieRF E k1) (trieRF E k1 ++ []); rw [List.append_nil]
    exact MemEq.refl _
  | cons a h bl nx ihb ihn =>
    intro k1
    show MemEq (trieRF E (mergeT (insK a (fun s => ⟨s.root.union h, mergeT s.kids bl⟩) k1) nx))
      (trieRF E k1 ++ ((treeRF E ⟨h, bl⟩).map (RFact.cons a) ++ trieRF E nx))
    have hG : ∀ s : Tree, MemEq (treeRF E ⟨s.root.union h, mergeT s.kids bl⟩)
        (treeRF E s ++ treeRF E ⟨h, bl⟩) := by
      intro s y
      have h1 := Payload.union_mem E s.root h y
      have h2 := ihb s.kids y
      show y ∈ payRF E (s.root.union h) ++ trieRF E (mergeT s.kids bl) ↔
        y ∈ (payRF E s.root ++ trieRF E s.kids) ++ (payRF E h ++ trieRF E bl)
      simp only [List.mem_append] at h1 h2 ⊢
      rw [h1, h2]
      simp only [or_assoc, or_left_comm]
    refine MemEq.trans (ihn _) ?_
    rw [← List.append_assoc]
    exact MemEq.append (insK_mem hG k1) (MemEq.refl _)

theorem merge_memEq (E : Excl) (t1 t2 : Tree) :
    MemEq (treeRF E (merge t1 t2)) (treeRF E t1 ++ treeRF E t2) := by
  intro y
  have h1 := Payload.union_mem E t1.root t2.root y
  have h2 := mergeT_mem E t2.kids t1.kids y
  show y ∈ payRF E (t1.root.union t2.root) ++ trieRF E (mergeT t1.kids t2.kids) ↔
    y ∈ (payRF E t1.root ++ trieRF E t1.kids) ++ (payRF E t2.root ++ trieRF E t2.kids)
  simp only [List.mem_append] at h1 h2 ⊢
  rw [h1, h2]
  simp only [or_assoc, or_left_comm]

/-- Merge rule 1: two edge trees with the same key (premise, layer, E, X). -/
def EdgeTree.merge1 (t1 t2 : EdgeTree) : EdgeTree :=
  ⟨t1.excl, t1.mx, t1.demand, merge t1.tree t2.tree⟩

/-- MAIN 2a. Merge rule 1 is the union of the path facts (membership).
    (Version 5: the key has the mark exclusion, `hX`.) -/
theorem rule1_mem (b : Base) (t1 t2 : EdgeTree) (hE : t1.excl = t2.excl) (hX : t1.mx = t2.mx)
    (hd : t1.demand = t2.demand) (a : AFact) :
    a ∈ toAFacts b (t1.merge1 t2) ↔ a ∈ toAFacts b t1 ∨ a ∈ toAFacts b t2 := by
  rcases t1 with ⟨E, X, d, T1⟩
  rcases t2 with ⟨E2, X2, d2, T2⟩
  dsimp only at hE hX hd
  subst hE hX hd
  rw [mem_toAFacts, mem_toAFacts, mem_toAFacts]
  have h := merge_memEq E T1 T2
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases List.mem_append.mp ((h x).mp hx) with hx | hx
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, (h x).mpr (List.mem_append.mpr (Or.inl hx)), rfl⟩
    · exact ⟨x, (h x).mpr (List.mem_append.mpr (Or.inr hx)), rfl⟩

theorem rule1_den (b : Base) (t1 t2 : EdgeTree) (hE : t1.excl = t2.excl) (hX : t1.mx = t2.mx)
    (hd : t1.demand = t2.demand) {i : PFact} {d : Bool} {l0 l1 : Loc} :
    denA i (toAFacts b (t1.merge1 t2)) d l0 l1 ↔ denA i (toAFacts b t1 ++ toAFacts b t2) d l0 l1 := by
  constructor
  · rintro ⟨a, ha, hdd, hden⟩
    exact ⟨a, List.mem_append.mpr ((rule1_mem b t1 t2 hE hX hd a).mp ha), hdd, hden⟩
  · rintro ⟨a, ha, hdd, hden⟩
    exact ⟨a, (rule1_mem b t1 t2 hE hX hd a).mpr (List.mem_append.mp ha), hdd, hden⟩

/-! ### Merge rule 2: the same tree with two exclusions -/

/-- Give a `*` fact the exclusion `E`. -/
def setExcl (E : Excl) (x : RFact) : RFact :=
  match x.kind with
  | .star _ => ⟨x.path, .star E, x.mark⟩
  | _       => x

theorem setExcl_cons (E : Excl) (a : Acc) (x : RFact) :
    setExcl E (x.cons a) = (setExcl E x).cons a := by
  rcases x with ⟨p, k, m⟩; cases k <;> rfl

theorem map_setExcl_nonstar (E : Excl) (L : List RFact) (hL : ∀ x, x ∈ L → x.kind.isStar = false) :
    L.map (setExcl E) = L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.map_cons, ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))]
    have hx := hL x (List.mem_cons_self ..)
    rcases x with ⟨p, k, m⟩
    cases k with
    | star e => exact nomatch hx
    | any => rfl
    | exact => rfl

theorem msRF_kind {k : Kind} {ms : MarkSet} {x : RFact} (hx : x ∈ msRF k ms) : x.kind = k := by
  obtain ⟨_, _, rfl⟩ := mem_msRF.mp hx; rfl

theorem payRF_setExcl (E E0 : Excl) (pl : Payload) : payRF E pl = (payRF E0 pl).map (setExcl E) := by
  unfold payRF
  rw [List.map_append, List.map_append,
    map_setExcl_nonstar E (msRF .any pl.anyM) (fun x hx => by rw [msRF_kind hx]; rfl),
    map_setExcl_nonstar E (msRF .exact pl.exactM) (fun x hx => by rw [msRF_kind hx]; rfl)]
  cases pl.star <;> rfl

theorem trieRF_setExcl (E E0 : Excl) (k : Trie) : trieRF E k = (trieRF E0 k).map (setExcl E) := by
  induction k with
  | nil => rfl
  | cons a h bl nx ihb ihn =>
    show (payRF E h ++ trieRF E bl).map (RFact.cons a) ++ trieRF E nx =
      ((payRF E0 h ++ trieRF E0 bl).map (RFact.cons a) ++ trieRF E0 nx).map (setExcl E)
    have hf : (setExcl E ∘ RFact.cons a) = (RFact.cons a ∘ setExcl E) :=
      funext (fun x => setExcl_cons E a x)
    have key : ((payRF E0 h ++ trieRF E0 bl).map (RFact.cons a) ++ trieRF E0 nx).map (setExcl E) =
        (payRF E h ++ trieRF E bl).map (RFact.cons a) ++ trieRF E nx := by
      rw [List.map_append (f := setExcl E), List.map_map, hf, ← List.map_map,
        List.map_append (f := setExcl E) (l₁ := payRF E0 h), ← payRF_setExcl E E0 h, ← ihb, ← ihn]
    exact key.symm

theorem treeRF_setExcl (E E0 : Excl) (t : Tree) : treeRF E t = (treeRF E0 t).map (setExcl E) := by
  unfold treeRF
  rw [List.map_append, ← payRF_setExcl, ← trieRF_setExcl]

theorem sem_star_inter' {p : List Acc} {m : MarkA} {e1 e2 : Excl} {σ m0 q m1} :
    RFact.sem ⟨p, .star (Excl.inter e1 e2), m⟩ σ m0 q m1 ↔
      RFact.sem ⟨p, .star e1, m⟩ σ m0 q m1 ∨ RFact.sem ⟨p, .star e2, m⟩ σ m0 q m1 := by
  constructor
  · rintro ⟨hm, hp, τ, hq, hτ, ha⟩
    have ha' : (e1.admits σ || e2.admits σ) = true := by rw [← admits_inter]; exact ha
    cases h1 : e1.admits σ with
    | true => exact Or.inl ⟨hm, hp, τ, hq, hτ, h1⟩
    | false =>
      rw [h1, Bool.false_or] at ha'
      exact Or.inr ⟨hm, hp, τ, hq, hτ, ha'⟩
  · rintro (⟨hm, hp, τ, hq, hτ, ha⟩ | ⟨hm, hp, τ, hq, hτ, ha⟩)
    · refine ⟨hm, hp, τ, hq, hτ, ?_⟩
      show (Excl.inter e1 e2).admits σ = true
      rw [admits_inter, ha, Bool.true_or]
    · refine ⟨hm, hp, τ, hq, hτ, ?_⟩
      show (Excl.inter e1 e2).admits σ = true
      rw [admits_inter, ha, Bool.or_true]

theorem sem_setExcl_inter (E1 E2 : Excl) (x : RFact) {σ m0 q m1} :
    (setExcl (E1.inter E2) x).sem σ m0 q m1 ↔
      (setExcl E1 x).sem σ m0 q m1 ∨ (setExcl E2 x).sem σ m0 q m1 := by
  rcases x with ⟨p, k, m⟩
  cases k with
  | star e => exact sem_star_inter'
  | any => exact or_self_iff.symm
  | exact => exact or_self_iff.symm

theorem semL_map {f : RFact → RFact} {L : List RFact} {σ m0 q m1} :
    semL (L.map f) σ m0 q m1 ↔ ∃ x, x ∈ L ∧ (f x).sem σ m0 q m1 := by
  constructor
  · rintro ⟨y, hy, hs⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact ⟨x, hx, hs⟩
  · rintro ⟨x, hx, hs⟩
    exact ⟨f x, List.mem_map.mpr ⟨x, hx, rfl⟩, hs⟩

/-- WHY rule 2 is exact: the same tree under `E1 ∩ E2` means the same pairs as
    the tree under `E1` together with the tree under `E2`. -/
theorem rule2_eqv (E1 E2 : Excl) (T : Tree) :
    Eqv (treeRF (E1.inter E2) T) (treeRF E1 T ++ treeRF E2 T) := by
  rw [treeRF_setExcl (E1.inter E2) Excl.empty T, treeRF_setExcl E1 Excl.empty T,
    treeRF_setExcl E2 Excl.empty T]
  intro σ m0 q m1
  rw [semL_append, semL_map, semL_map, semL_map]
  constructor
  · rintro ⟨x, hx, hs⟩
    rcases (sem_setExcl_inter E1 E2 x).mp hs with h | h
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨x, hx, hs⟩ | ⟨x, hx, hs⟩)
    · exact ⟨x, hx, (sem_setExcl_inter E1 E2 x).mpr (Or.inl hs)⟩
    · exact ⟨x, hx, (sem_setExcl_inter E1 E2 x).mpr (Or.inr hs)⟩

/-- The mark exclusion of a tree and the exclusion of its `*` leaves are
    independent. -/
theorem markX_setExcl (X : List Mark) (E : Excl) (x : RFact) :
    markX X (setExcl E x) = setExcl E (markX X x) := by
  rcases x with ⟨p, k, m⟩; cases k <;> rfl

/-- `rule2_eqv` for the facts of a tree with the mark exclusion `X`. -/
theorem rule2_eqvX (X : List Mark) (E1 E2 : Excl) (T : Tree) :
    Eqv ((treeRF (E1.inter E2) T).map (markX X))
      ((treeRF E1 T).map (markX X) ++ (treeRF E2 T).map (markX X)) := by
  rw [treeRF_setExcl (E1.inter E2) Excl.empty T, treeRF_setExcl E1 Excl.empty T,
    treeRF_setExcl E2 Excl.empty T, List.map_map, List.map_map, List.map_map]
  intro σ m0 q m1
  rw [semL_append, semL_map, semL_map, semL_map]
  have key : ∀ x : RFact, ((markX X ∘ setExcl (E1.inter E2)) x).sem σ m0 q m1 ↔
      ((markX X ∘ setExcl E1) x).sem σ m0 q m1 ∨ ((markX X ∘ setExcl E2) x).sem σ m0 q m1 := by
    intro x
    show (markX X (setExcl (E1.inter E2) x)).sem σ m0 q m1 ↔
      (markX X (setExcl E1 x)).sem σ m0 q m1 ∨ (markX X (setExcl E2 x)).sem σ m0 q m1
    rw [markX_setExcl, markX_setExcl, markX_setExcl]
    exact sem_setExcl_inter E1 E2 (markX X x)
  constructor
  · rintro ⟨x, hx, hs⟩
    rcases (key x).mp hs with h | h
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨x, hx, hs⟩ | ⟨x, hx, hs⟩)
    · exact ⟨x, hx, (key x).mpr (Or.inl hs)⟩
    · exact ⟨x, hx, (key x).mpr (Or.inr hs)⟩

/-- Merge rule 2: the same tree (and layer, and mark exclusion) with two exclusions. -/
def EdgeTree.merge2 (t1 t2 : EdgeTree) : EdgeTree :=
  ⟨t1.excl.inter t2.excl, t1.mx, t1.demand, t1.tree⟩

/-- MAIN 2b. Merge rule 2 is exact: it means the pairs of both edge trees.
    (Version 5: the two trees have the same mark exclusion, `hX`.) -/
theorem rule2_den (b : Base) (t1 t2 : EdgeTree) (hT : t1.tree = t2.tree) (hX : t1.mx = t2.mx)
    (hd : t1.demand = t2.demand) {i : PFact} {d : Bool} {l0 l1 : Loc} :
    denA i (toAFacts b (t1.merge2 t2)) d l0 l1 ↔ denA i (toAFacts b t1 ++ toAFacts b t2) d l0 l1 := by
  rcases t1 with ⟨E1, X, d1, T⟩
  rcases t2 with ⟨E2, X2, d2, T2⟩
  dsimp only at hT hX hd
  subst hT hX hd
  rw [denA_append, denA_toAFacts, denA_toAFacts, denA_toAFacts]
  show (d1 = d ∧ denL i (((treeRF (E1.inter E2) T).map (markX X)).map (RFact.toP b)) l0 l1) ↔ _
  rw [(rule2_eqvX X E1 E2 T).den, List.map_append, denL_append']
  constructor
  · rintro ⟨hd, h | h⟩
    · exact Or.inl ⟨hd, h⟩
    · exact Or.inr ⟨hd, h⟩
  · rintro (⟨hd, h⟩ | ⟨hd, h⟩)
    · exact ⟨hd, Or.inl h⟩
    · exact ⟨hd, Or.inr h⟩

/-! ### Merge rule 2 for marks: the same tree with two mark exclusions -/

theorem out_starM (X : List Mark) (m : Mark) : (starM X).out m = m := by
  cases X <;> rfl

theorem passes_starM (X : List Mark) (m : Mark) : (starM X).passes m ↔ memB m X = false := by
  cases X with
  | nil => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | cons t x => exact Iff.rfl

/-- WHY intersection is the exact join of two mark exclusions: the abstract mark
    `starM (X1 ∩ X2)` lets a mark through iff `starM X1` or `starM X2` does. -/
theorem passes_mxInter (X1 X2 : List Mark) (m : Mark) :
    (starM (mxInter X1 X2)).passes m ↔ (starM X1).passes m ∨ (starM X2).passes m := by
  rw [passes_starM, passes_starM, passes_starM]
  show memB m (X1.filter (fun t => memB t X2)) = false ↔ _
  rw [memB_filter, Bool.and_eq_false_iff]

theorem sem_markX_inter (X1 X2 : List Mark) (x : RFact) {σ m0 q m1} :
    (markX (mxInter X1 X2) x).sem σ m0 q m1 ↔
      (markX X1 x).sem σ m0 q m1 ∨ (markX X2 x).sem σ m0 q m1 := by
  rcases x with ⟨p, k, m⟩
  cases m with
  | star =>
    show (m1 = (starM (mxInter X1 X2)).out m0 ∧ (starM (mxInter X1 X2)).passes m0 ∧ _) ↔
      (m1 = (starM X1).out m0 ∧ (starM X1).passes m0 ∧ _) ∨
      (m1 = (starM X2).out m0 ∧ (starM X2).passes m0 ∧ _)
    rw [out_starM, out_starM, out_starM, passes_mxInter]
    constructor
    · rintro ⟨hm, hp | hp, ht⟩
      · exact Or.inl ⟨hm, hp, ht⟩
      · exact Or.inr ⟨hm, hp, ht⟩
    · rintro (⟨hm, hp, ht⟩ | ⟨hm, hp, ht⟩)
      · exact ⟨hm, Or.inl hp, ht⟩
      · exact ⟨hm, Or.inr hp, ht⟩
  | conc t => exact or_self_iff.symm
  | starEx y => exact or_self_iff.symm

/-- WHY rule 2 for marks is exact: the same tree under `X1 ∩ X2` means the same
    pairs as the tree under `X1` together with the tree under `X2`. -/
theorem rule2_mark_eqv (X1 X2 : List Mark) (E : Excl) (T : Tree) :
    Eqv ((treeRF E T).map (markX (mxInter X1 X2)))
      ((treeRF E T).map (markX X1) ++ (treeRF E T).map (markX X2)) := by
  intro σ m0 q m1
  rw [semL_append, semL_map, semL_map, semL_map]
  constructor
  · rintro ⟨x, hx, hs⟩
    rcases (sem_markX_inter X1 X2 x).mp hs with h | h
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨x, hx, hs⟩ | ⟨x, hx, hs⟩)
    · exact ⟨x, hx, (sem_markX_inter X1 X2 x).mpr (Or.inl hs)⟩
    · exact ⟨x, hx, (sem_markX_inter X1 X2 x).mpr (Or.inr hs)⟩

/-- Merge rule 2 for marks: the same tree (and layer, and exclusion) with two mark
    exclusions. -/
def EdgeTree.merge2m (t1 t2 : EdgeTree) : EdgeTree :=
  ⟨t1.excl, mxInter t1.mx t2.mx, t1.demand, t1.tree⟩

/-- MAIN 2c. Merge rule 2 for marks is exact: the tree with the intersection of the
    two mark exclusions means the union of the pairs of both edge trees. -/
theorem rule2_mark (b : Base) (t1 t2 : EdgeTree) (hE : t1.excl = t2.excl) (hT : t1.tree = t2.tree)
    (hd : t1.demand = t2.demand) {i : PFact} {d : Bool} {l0 l1 : Loc} :
    denA i (toAFacts b (t1.merge2m t2)) d l0 l1 ↔ denA i (toAFacts b t1 ++ toAFacts b t2) d l0 l1 := by
  rcases t1 with ⟨E, X1, d1, T⟩
  rcases t2 with ⟨E2, X2, d2, T2⟩
  dsimp only at hE hT hd
  subst hE hT hd
  rw [denA_append, denA_toAFacts, denA_toAFacts, denA_toAFacts]
  show (d1 = d ∧ denL i (((treeRF E T).map (markX (mxInter X1 X2))).map (RFact.toP b)) l0 l1) ↔ _
  rw [(rule2_mark_eqv X1 X2 E T).den, List.map_append, denL_append']
  constructor
  · rintro ⟨hd, h | h⟩
    · exact Or.inl ⟨hd, h⟩
    · exact Or.inr ⟨hd, h⟩
  · rintro (⟨hd, h⟩ | ⟨hd, h⟩)
    · exact ⟨hd, Or.inl h⟩
    · exact ⟨hd, Or.inr h⟩

/-! ## 6. Prepend (store into a field) -/

/-- Put the accessor `a` before every path: one new root, the old tree is shared. -/
def prepend (a : Acc) (t : Tree) : Tree := ⟨Payload.empty, .cons a t.root t.kids .nil⟩

def prependF (a : Acc) (f : PFact) : PFact := ⟨f.base, a :: f.path, f.kind, f.mark⟩

theorem treeRF_prepend (E : Excl) (a : Acc) (t : Tree) :
    treeRF E (prepend a t) = (treeRF E t).map (RFact.cons a) := by
  show [] ++ ((payRF E t.root ++ trieRF E t.kids).map (RFact.cons a) ++ []) = _
  rw [List.append_nil]; rfl

/-- MAIN 3. Prepend is `map (prepend a)` on the path facts (list equality). -/
theorem toAFacts_prepend (b : Base) (a : Acc) (t : EdgeTree) :
    toAFacts b ⟨t.excl, t.mx, t.demand, prepend a t.tree⟩ =
      (toAFacts b t).map (fun c => ⟨prependF a c.fact, c.demand⟩) := by
  unfold toAFacts
  rw [treeRF_prepend, List.map_map, List.map_map]; rfl

/-- Put the path `p` before every path. -/
def prependPath : List Acc → Tree → Tree
  | [],     t => t
  | a :: p, t => prepend a (prependPath p t)

theorem treeRF_prependPath (E : Excl) (p : List Acc) (t : Tree) :
    treeRF E (prependPath p t) = (treeRF E t).map (RFact.pre p) := by
  induction p with
  | nil => rw [map_pre_nil]; rfl
  | cons a p ih =>
    show treeRF E (prepend a (prependPath p t)) = _
    rw [treeRF_prepend, ih, map_cons_pre]


/-! ## 7. The tree form of `applyEdge` -/

/-- The child with accessor `a` (the first one). -/
def childAt (a : Acc) : Trie → Option Tree
  | .nil => none
  | .cons c h bl nx => if Nat.beq a c then some ⟨h, bl⟩ else childAt a nx

/-- The subtree at path `q`. -/
def subtreeAt : List Acc → Tree → Option Tree
  | [],     t => some t
  | a :: q, t =>
    match childAt a t.kids with
    | none   => none
    | some s => subtreeAt q s

/-! ### Legal facts -/

/-- A legal final fact: a `*` tail has an abstract mark (`*` or `*∖x`, W2). -/
def legalB (k : Kind) (m : MarkA) : Bool :=
  match k, m with
  | .star _, .conc _ => false
  | _,       _       => true

theorem payRF_legal {E : Excl} {pl : Payload} {x : RFact} (hx : x ∈ payRF E pl) :
    legalB x.kind x.mark = true := by
  rcases mem_payRF.mp hx with ⟨_, rfl⟩ | ⟨m, _, rfl⟩ | ⟨m, _, rfl⟩
  · rfl
  · cases m <;> rfl
  · cases m <;> rfl

theorem trieRF_legal (E : Excl) (k : Trie) : ∀ x, x ∈ trieRF E k → legalB x.kind x.mark = true := by
  induction k with
  | nil => intro x hx; exact nomatch hx
  | cons a h bl nx ihb ihn =>
    intro x hx
    rw [trieRF_cons] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
      rcases List.mem_append.mp hx' with hx' | hx'
      · exact payRF_legal (x := x') hx'
      · exact ihb x' hx'
    · exact ihn x hx

/-- Every fact of an edge tree is legal: a `*` leaf has the abstract mark. -/
theorem treeRF_legal (E : Excl) (t : Tree) (x : RFact) (hx : x ∈ treeRF E t) :
    legalB x.kind x.mark = true := by
  rcases List.mem_append.mp hx with hx | hx
  · exact payRF_legal hx
  · exact trieRF_legal E t.kids x hx

/-- `AFact.norm` (design decision F9) does not change a legal fact with `demand = false`.
    (Version 5: a `*` tail with the mark `*∖x` is legal, W2.) -/
theorem norm_legal (b : Base) (p : List Acc) (k : Kind) (m : MarkA) (hl : legalB k m = true) :
    AFact.norm ⟨⟨b, p, k, m⟩, false⟩ = ⟨⟨b, p, k, m⟩, false⟩ := by
  cases k with
  | star e => cases m with
    | star => rfl
    | conc t => exact nomatch hl
    | starEx x => rfl
  | any => rfl
  | exact => rfl

/-- `AFact.norm` does not change a fact that is not `*`-tailed. -/
theorem norm_nonstar (b : Base) (p : List Acc) (k : Kind) (m : MarkA) (ap : Bool)
    (hk : k.isStar = false) : AFact.norm ⟨⟨b, p, k, m⟩, ap⟩ = ⟨⟨b, p, k, m⟩, ap⟩ := by
  cases k with
  | star e => exact nomatch hk
  | any => rfl
  | exact => rfl

/-! ### The per-path concept with the step bit -/

theorem relate_nil (p : List Acc) : relate [] p = .below p := rfl

theorem relate_cons_nil (a : Acc) (q : List Acc) : relate (a :: q) [] = .above (a :: q) := rfl

theorem beq_symm_false {a c : Nat} (h : Nat.beq a c = false) : Nat.beq c a = false := by
  rcases Bool.eq_false_or_eq_true (Nat.beq c a) with h' | h'
  · have hca : c = a := Nat.eq_of_beq_eq_true h'
    subst hca
    rw [Nat.beq_refl] at h
    exact nomatch h
  · exact h'

theorem relate_cons_cons (a c : Acc) (q p : List Acc) :
    relate (a :: q) (c :: p) = if Nat.beq a c then relate q p else .apart := by
  rcases Bool.eq_false_or_eq_true (Nat.beq a c) with h | h
  · have hac : a = c := Nat.eq_of_beq_eq_true h
    subst hac
    simp only [relate, dropPrefix, Nat.beq_refl, ↓reduceIte]
  · simp only [relate, dropPrefix, h, beq_symm_false h, Bool.false_eq_true, ↓reduceIte]

def belowNilS (ex : Excl) (ck : Kind) (m : MarkA) : List (RFact × Bool) :=
  match ck, ex with
  | .exact,   _     => [(⟨[], .exact, m⟩, false)]
  | .star ec, _     => [(⟨[], .star (ec.union ex), m⟩, false)]
  | .any,     .univ => [(⟨[], .exact, m⟩, false)]
  | .any,     _     => [(⟨[], .any, m⟩, !ex.isEmptyB)]

def belowS (e e' : Excl) (ck : Kind) (m : MarkA) : List Acc → List (RFact × Bool)
  | []     => belowNilS (e.union e') ck m
  | a :: r => if e.admits (a :: r) && e'.admits (a :: r) then [(⟨a :: r, ck, m⟩, false)] else []

def aboveS (ex : Excl) (ck : Kind) (m : MarkA) (r : List Acc) : List (RFact × Bool) :=
  if admitsTailB ck r then [(⟨[], .any, m⟩, !(ck.isAny && ex.isEmptyB))] else []

/-- `applyEdge` on one relative fact: each result with its step bit. -/
def stepR (e e' : Excl) (fp : List Acc) (x : RFact) : List (RFact × Bool) :=
  match relate fp x.path with
  | .below r => belowS e e' x.kind x.mark r
  | .above r => aboveS (e.union e') x.kind x.mark r
  | .apart   => []

/-- `applyEdge` with the demand bit, on one legal fact. A demand fact (`ap0 = true`)
    is not `*`-tailed (the invariant). Then `AFact.norm` is the identity and the
    demand bit of each result is `ap0 || step bit`. -/
theorem applyEdge_eq2 (fb tb : Base) (fp tp : List Acc) (e e' : Excl) (x : RFact) (ap0 : Bool)
    (hl : legalB x.kind x.mark = true) (hd : ap0 = true → x.kind.isStar = false) :
    (applyEdge ⟨x.toP fb, ap0⟩ ⟨fb, fp, .star e, .star⟩ ⟨tb, tp, .star e', .star⟩).facts
      = (stepR e e' fp x).map (fun p => ⟨(p.1.pre tp).toP tb, ap0 || p.2⟩) := by
  rcases x with ⟨xp, xk, xm⟩
  dsimp only at hl hd
  unfold applyEdge stepR
  simp only [RFact.toP, Nat.beq_refl, ↓reduceIte]
  cases xk with
  | star ec =>
    cases ap0 with
    | true => exact nomatch hd rfl
    | false =>
    cases xm with
    | conc t => exact nomatch hl
    | star =>
      cases relate fp xp with
      | below r =>
        cases r with
        | nil =>
          simp only [belowCase, admitsTailB, Excl.admits_nil, ↓reduceIte, tailExcl, belowS,
            belowNilS, markGate, markComp, Bool.or_false, norm_legal _ _ (.star _) .star rfl,
            List.map, RFact.pre, List.append_nil]
        | cons a r =>
          simp only [belowCase, admitsTailB, belowS]
          rcases Bool.eq_false_or_eq_true (e.admits (a :: r)) with h1 | h1 <;>
          rcases Bool.eq_false_or_eq_true (e'.admits (a :: r)) with h2 | h2 <;>
            simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true,
              markGate, markComp, Bool.or_false, norm_legal _ _ (.star _) .star rfl, List.map,
              RFact.pre, Res.none]
      | above r =>
        simp only [aboveCase, aboveS]
        rcases Bool.eq_false_or_eq_true (admitsTailB (.star ec) r) with h1 | h1 <;>
          simp only [h1, Bool.false_eq_true, ↓reduceIte, markGate, markComp, tailExcl,
            norm_nonstar _ _ .any _ _ rfl, List.map, RFact.pre, Res.none, List.append_nil]
      | apart => rfl
    | starEx y =>
      cases relate fp xp with
      | below r =>
        cases r with
        | nil =>
          simp only [belowCase, admitsTailB, Excl.admits_nil, ↓reduceIte, tailExcl, belowS,
            belowNilS, markGate, markComp, Bool.or_false, norm_legal _ _ (.star _) (.starEx y) rfl,
            List.map, RFact.pre, List.append_nil]
        | cons a r =>
          simp only [belowCase, admitsTailB, belowS]
          rcases Bool.eq_false_or_eq_true (e.admits (a :: r)) with h1 | h1 <;>
          rcases Bool.eq_false_or_eq_true (e'.admits (a :: r)) with h2 | h2 <;>
            simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true,
              markGate, markComp, Bool.or_false, norm_legal _ _ (.star _) (.starEx y) rfl, List.map,
              RFact.pre, Res.none]
      | above r =>
        simp only [aboveCase, aboveS]
        rcases Bool.eq_false_or_eq_true (admitsTailB (.star ec) r) with h1 | h1 <;>
          simp only [h1, Bool.false_eq_true, ↓reduceIte, markGate, markComp, tailExcl,
            norm_nonstar _ _ .any _ _ rfl, List.map, RFact.pre, Res.none, List.append_nil]
      | apart => rfl
  | any =>
    cases relate fp xp with
    | below r =>
      cases r with
      | nil =>
        simp only [belowCase, admitsTailB, Excl.admits_nil, ↓reduceIte, tailExcl, belowS,
          belowNilS]
        cases e.union e' <;>
          simp only [markGate, markComp, norm_nonstar _ _ .exact _ _ rfl,
            norm_nonstar _ _ .any _ _ rfl, List.map, RFact.pre, List.append_nil]
      | cons a r =>
        simp only [belowCase, admitsTailB, belowS]
        rcases Bool.eq_false_or_eq_true (e.admits (a :: r)) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (e'.admits (a :: r)) with h2 | h2 <;>
          simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true,
            markGate, markComp, norm_nonstar _ _ .any _ _ rfl, List.map, RFact.pre, Res.none]
    | above r =>
      simp only [aboveCase, aboveS, admitsTailB, ↓reduceIte, markGate, markComp, tailExcl,
        norm_nonstar _ _ .any _ _ rfl, List.map, RFact.pre, List.append_nil]
    | apart => rfl
  | exact =>
    cases relate fp xp with
    | below r =>
      cases r with
      | nil =>
        simp only [belowCase, admitsTailB, Excl.admits_nil, ↓reduceIte, belowS,
          belowNilS, markGate, markComp, norm_nonstar _ _ .exact _ _ rfl, List.map, RFact.pre,
          List.append_nil]
      | cons a r =>
        simp only [belowCase, admitsTailB, belowS]
        rcases Bool.eq_false_or_eq_true (e.admits (a :: r)) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (e'.admits (a :: r)) with h2 | h2 <;>
          simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.and_true,
            markGate, markComp, norm_nonstar _ _ .exact _ _ rfl, List.map, RFact.pre, Res.none]
    | above r =>
      cases r with
      | nil =>
        simp only [aboveCase, aboveS, admitsTailB, ↓reduceIte, markGate, markComp, tailExcl,
          norm_nonstar _ _ .any _ _ rfl, List.map, RFact.pre, List.append_nil]
      | cons a r =>
        simp only [aboveCase, admitsTailB, Bool.false_eq_true, ↓reduceIte, aboveS, List.map]
        rfl
    | apart => rfl
/-! ### The mark exclusion of the tree passes through the micro edge -/

theorem legal_markX (X : List Mark) {x : RFact} (hl : legalB x.kind x.mark = true) :
    legalB (markX X x).kind (markX X x).mark = true := by
  rcases x with ⟨p, k, m⟩
  cases k <;> cases m <;> (try cases X) <;> first | rfl | exact hl

theorem belowNilS_markX (X : List Mark) (ex : Excl) (ck : Kind) (m : MarkA) :
    belowNilS ex ck (mxMark X m) = (belowNilS ex ck m).map (fun p => (markX X p.1, p.2)) := by
  cases ck <;> cases ex <;> rfl

theorem belowS_markX (X : List Mark) (e e' : Excl) (ck : Kind) (m : MarkA) (r : List Acc) :
    belowS e e' ck (mxMark X m) r = (belowS e e' ck m r).map (fun p => (markX X p.1, p.2)) := by
  cases r with
  | nil => exact belowNilS_markX X _ ck m
  | cons a r =>
    show (if (e.admits (a :: r) && e'.admits (a :: r)) = true then _ else _) =
      List.map _ (if (e.admits (a :: r) && e'.admits (a :: r)) = true then _ else _)
    cases (e.admits (a :: r) && e'.admits (a :: r)) <;> rfl

theorem aboveS_markX (X : List Mark) (ex : Excl) (ck : Kind) (m : MarkA) (r : List Acc) :
    aboveS ex ck (mxMark X m) r = (aboveS ex ck m r).map (fun p => (markX X p.1, p.2)) := by
  unfold aboveS
  cases admitsTailB ck r <;> rfl

/-- `stepR` only passes the mark through: it commutes with the reading of the mark
    exclusion. -/
theorem stepR_markX (X : List Mark) (e e' : Excl) (fp : List Acc) (x : RFact) :
    stepR e e' fp (markX X x) = (stepR e e' fp x).map (fun p => (markX X p.1, p.2)) := by
  rcases x with ⟨p, k, m⟩
  show stepR e e' fp ⟨p, k, mxMark X m⟩ = _
  unfold stepR
  dsimp only
  cases relate fp p with
  | below r => exact belowS_markX X e e' k m r
  | above r => exact aboveS_markX X (e.union e') k m r
  | apart => rfl

/-- `applyEdge_eq2` for a fact of a tree with the mark exclusion `X`. -/
theorem applyEdge_eqX (fb tb : Base) (fp tp : List Acc) (e e' : Excl) (X : List Mark) (x : RFact)
    (ap0 : Bool) (hl : legalB x.kind x.mark = true) (hd : ap0 = true → x.kind.isStar = false) :
    (applyEdge ⟨(markX X x).toP fb, ap0⟩ ⟨fb, fp, .star e, .star⟩ ⟨tb, tp, .star e', .star⟩).facts
      = (stepR e e' fp x).map (fun p => ⟨(markX X (p.1.pre tp)).toP tb, ap0 || p.2⟩) := by
  rw [applyEdge_eq2 fb tb fp tp e e' (markX X x) ap0 (legal_markX X hl) hd, stepR_markX,
    List.map_map]
  rfl

theorem pair_mem_singleton {y z : RFact} {b c : Bool} : (y, b) ∈ [(z, c)] ↔ y = z ∧ b = c := by
  rw [List.mem_singleton]
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! ### Routing of the result root (Case below, empty rest) -/

/-- The non-`*` part of the result root that stays in the layer of the input
    (no exclusion, W1). The `*` leaf of the root goes to the tree with the
    exclusion `E ∪ ex` (`rootF`). -/
def payBelowN (ex : Excl) (pl : Payload) : Payload :=
  match ex with
  | .univ         => ⟨false, MarkSet.empty, pl.exactM.union pl.anyM⟩
  | .set []       => ⟨false, pl.anyM, pl.exactM⟩
  | .set (_ :: _) => ⟨false, MarkSet.empty, pl.exactM⟩

/-- The `[any]` marks of the result root that move to the demand layer: an
    `[any]` leaf at `fr.path` under a non-empty exclusion `ex` (step bit `true`). -/
def movedBelow (ex : Excl) (pl : Payload) : MarkSet :=
  match ex with
  | .set (_ :: _) => pl.anyM
  | _             => MarkSet.empty

/-- The results with step bit `false` of the root payload at `fr.path`. -/
def rootF (E ex : Excl) (pl : Payload) : List RFact :=
  starRF (E.union ex) pl.star ++ payRF E (payBelowN ex pl)

theorem mem_rootF (E ex : Excl) (pl : Payload) (y : RFact) :
    y ∈ rootF E ex pl ↔ ∃ x, x ∈ payRF E pl ∧ (y, false) ∈ belowNilS ex x.kind x.mark := by
  unfold rootF
  rw [List.mem_append, mem_starRF, mem_payRF]
  cases ex with
  | univ =>
    constructor
    · rintro (⟨hs, rfl⟩ | ⟨hs, _⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
      · exact ⟨⟨[], .star E, .star⟩, mem_payRF.mpr (Or.inl ⟨hs, rfl⟩),
          pair_mem_singleton.mpr ⟨rfl, rfl⟩⟩
      · exact nomatch hs
      · exact absurd hm has_empty
      · rcases has_union.mp hm with h | h
        · exact ⟨⟨[], .exact, m⟩, mem_payRF.mpr (Or.inr (Or.inr ⟨m, h, rfl⟩)),
            pair_mem_singleton.mpr ⟨rfl, rfl⟩⟩
        · exact ⟨⟨[], .any, m⟩, mem_payRF.mpr (Or.inr (Or.inl ⟨m, h, rfl⟩)),
            pair_mem_singleton.mpr ⟨rfl, rfl⟩⟩
    · rintro ⟨x, hx, hy⟩
      rcases mem_payRF.mp hx with ⟨hs, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
      · exact Or.inl ⟨hs, (pair_mem_singleton.mp hy).1⟩
      · exact Or.inr (Or.inr (Or.inr ⟨m, has_union.mpr (Or.inr hm), (pair_mem_singleton.mp hy).1⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨m, has_union.mpr (Or.inl hm), (pair_mem_singleton.mp hy).1⟩))
  | set l =>
    cases l with
    | nil =>
      constructor
      · rintro (⟨hs, rfl⟩ | ⟨hs, _⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
        · exact ⟨⟨[], .star E, .star⟩, mem_payRF.mpr (Or.inl ⟨hs, rfl⟩),
            pair_mem_singleton.mpr ⟨rfl, rfl⟩⟩
        · exact nomatch hs
        · exact ⟨⟨[], .any, m⟩, mem_payRF.mpr (Or.inr (Or.inl ⟨m, hm, rfl⟩)),
            pair_mem_singleton.mpr ⟨rfl, rfl⟩⟩
        · exact ⟨⟨[], .exact, m⟩, mem_payRF.mpr (Or.inr (Or.inr ⟨m, hm, rfl⟩)),
            pair_mem_singleton.mpr ⟨rfl, rfl⟩⟩
      · rintro ⟨x, hx, hy⟩
        rcases mem_payRF.mp hx with ⟨hs, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
        · exact Or.inl ⟨hs, (pair_mem_singleton.mp hy).1⟩
        · exact Or.inr (Or.inr (Or.inl ⟨m, hm, (pair_mem_singleton.mp hy).1⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨m, hm, (pair_mem_singleton.mp hy).1⟩))
    | cons c l =>
      constructor
      · rintro (⟨hs, rfl⟩ | ⟨hs, _⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩)
        · exact ⟨⟨[], .star E, .star⟩, mem_payRF.mpr (Or.inl ⟨hs, rfl⟩),
            pair_mem_singleton.mpr ⟨rfl, rfl⟩⟩
        · exact nomatch hs
        · exact absurd hm has_empty
        · exact ⟨⟨[], .exact, m⟩, mem_payRF.mpr (Or.inr (Or.inr ⟨m, hm, rfl⟩)),
            pair_mem_singleton.mpr ⟨rfl, rfl⟩⟩
      · rintro ⟨x, hx, hy⟩
        rcases mem_payRF.mp hx with ⟨hs, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
        · exact Or.inl ⟨hs, (pair_mem_singleton.mp hy).1⟩
        · exact nomatch (pair_mem_singleton.mp hy).2
        · exact Or.inr (Or.inr (Or.inr ⟨m, hm, (pair_mem_singleton.mp hy).1⟩))

theorem mem_movedBelow (E ex : Excl) (pl : Payload) (y : RFact) :
    y ∈ msRF .any (movedBelow ex pl) ↔
      ∃ x, x ∈ payRF E pl ∧ (y, true) ∈ belowNilS ex x.kind x.mark := by
  have hE : ∀ y : RFact, y ∈ msRF .any MarkSet.empty ↔ False :=
    fun y => ⟨fun h => by rw [mem_msRF] at h; obtain ⟨m, hm, _⟩ := h; exact has_empty hm,
      fun h => h.elim⟩
  have hno : ∀ ex' : Excl, ex'.isEmptyB = true ∨ ex' = .univ →
      ∀ x, x ∈ payRF E pl → (y, true) ∉ belowNilS ex' x.kind x.mark := by
    intro ex' hex x hx hy
    rcases mem_payRF.mp hx with ⟨_, rfl⟩ | ⟨m, _, rfl⟩ | ⟨m, _, rfl⟩
    · exact nomatch (pair_mem_singleton.mp hy).2
    · rcases hex with hex | hex
      · cases ex' with
        | univ => exact nomatch hex
        | set l =>
          cases l with
          | nil => exact nomatch (pair_mem_singleton.mp hy).2
          | cons _ _ => exact nomatch hex
      · subst hex; exact nomatch (pair_mem_singleton.mp hy).2
    · exact nomatch (pair_mem_singleton.mp hy).2
  cases ex with
  | univ =>
    rw [show movedBelow .univ pl = MarkSet.empty from rfl, hE]
    exact ⟨fun h => h.elim, fun ⟨x, hx, hy⟩ => hno .univ (Or.inr rfl) x hx hy⟩
  | set l =>
    cases l with
    | nil =>
      rw [show movedBelow (.set []) pl = MarkSet.empty from rfl, hE]
      exact ⟨fun h => h.elim, fun ⟨x, hx, hy⟩ => hno (.set []) (Or.inl rfl) x hx hy⟩
    | cons a l =>
      show y ∈ msRF .any pl.anyM ↔ _
      rw [mem_msRF]
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨[], .any, m⟩, mem_payRF.mpr (Or.inr (Or.inl ⟨m, hm, rfl⟩)),
          pair_mem_singleton.mpr ⟨rfl, rfl⟩⟩
      · rintro ⟨x, hx, hy⟩
        rcases mem_payRF.mp hx with ⟨_, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, _, rfl⟩
        · exact nomatch (pair_mem_singleton.mp hy).2
        · exact ⟨m, hm, (pair_mem_singleton.mp hy).1⟩
        · exact nomatch (pair_mem_singleton.mp hy).2

/-! ### Routing of the kept children (step bit `false`) -/

/-- Case below, non-empty rest: the child `a` stays if both exclusions admit it. -/
def passB (e e' : Excl) (a : Acc) : Bool := e.admits [a] && e'.admits [a]

def filterKids (e e' : Excl) : Trie → Trie
  | .nil => .nil
  | .cons a h bl nx =>
    if passB e e' a then .cons a h bl (filterKids e e' nx) else filterKids e e' nx

theorem belowS_cons (e e' : Excl) (k : Kind) (m : MarkA) (a : Acc) (r : List Acc) :
    belowS e e' k m (a :: r) = if passB e e' a then [(⟨a :: r, k, m⟩, false)] else [] := by
  show (if (e.admits (a :: r) && e'.admits (a :: r)) = true then _ else _) = _
  rw [admits_cons e, admits_cons e']; rfl

theorem mem_kidsS (E e e' : Excl) (k : Trie) (y : RFact) (b0 : Bool) :
    (∃ x, x ∈ trieRF E k ∧ (y, b0) ∈ belowS e e' x.kind x.mark x.path) ↔
      b0 = false ∧ y ∈ trieRF E (filterKids e e' k) := by
  induction k with
  | nil => exact ⟨fun ⟨_, h, _⟩ => (nomatch h), fun ⟨_, h⟩ => (nomatch h)⟩
  | cons a h bl nx _ ihn =>
    rw [trieRF_cons]
    have hmap : ∀ x' : RFact, (y, b0) ∈ belowS e e' (x'.cons a).kind (x'.cons a).mark (x'.cons a).path ↔
        passB e e' a = true ∧ b0 = false ∧ y = x'.cons a := by
      intro x'
      show (y, b0) ∈ belowS e e' x'.kind x'.mark (a :: x'.path) ↔ _
      rw [belowS_cons]
      rcases Bool.eq_false_or_eq_true (passB e e' a) with hp | hp
      · simp only [hp, ↓reduceIte]
        rw [pair_mem_singleton]
        exact ⟨fun ⟨h1, h2⟩ => ⟨trivial, h2, h1⟩, fun ⟨_, h2, h1⟩ => ⟨h1, h2⟩⟩
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
        exact ⟨fun h => (nomatch h), fun ⟨h, _⟩ => (nomatch h)⟩
    rcases Bool.eq_false_or_eq_true (passB e e' a) with hp | hp
    · have hf : filterKids e e' (.cons a h bl nx) = .cons a h bl (filterKids e e' nx) := by
        simp only [filterKids, hp, ↓reduceIte]
      rw [hf, trieRF_cons, List.mem_append]
      constructor
      · rintro ⟨x, hx, hy⟩
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
          obtain ⟨_, hb, rfl⟩ := (hmap x').mp hy
          exact ⟨hb, Or.inl (List.mem_map.mpr ⟨x', hx', rfl⟩)⟩
        · obtain ⟨hb, hy'⟩ := ihn.mp ⟨x, hx, hy⟩
          exact ⟨hb, Or.inr hy'⟩
      · rintro ⟨hb, hy | hy⟩
        · obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hy
          exact ⟨x'.cons a, List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x', hx', rfl⟩)),
            (hmap x').mpr ⟨hp, hb, rfl⟩⟩
        · obtain ⟨x, hx, hy'⟩ := ihn.mpr ⟨hb, hy⟩
          exact ⟨x, List.mem_append.mpr (Or.inr hx), hy'⟩
    · have hf : filterKids e e' (.cons a h bl nx) = filterKids e e' nx := by
        simp only [filterKids, hp, Bool.false_eq_true, ↓reduceIte]
      rw [hf, ← ihn]
      constructor
      · rintro ⟨x, hx, hy⟩
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
          rw [(hmap x').mp hy |>.1] at hp
          exact nomatch hp
        · exact ⟨x, hx, hy⟩
      · rintro ⟨x, hx, hy⟩
        exact ⟨x, List.mem_append.mpr (Or.inr hx), hy⟩

/-! ### Routing of the payloads on the proper prefixes (Case above) -/

/-- The `[any]` mark that the `*` leaf at a proper prefix gives (step bit `true`):
    the leaf `*/E` admits the rest `r` of `fr.path`. -/
def cS (E : Excl) (r : List Acc) (pl : Payload) : MarkSet := ⟨pl.star && E.admits r, []⟩

/-- The `[any]` marks with step bit `b0` that the payload at a proper prefix gives:
    `*` leaves give bit `true`; `[any]` leaves give bit `!ex.isEmptyB`. -/
def contribB (E ex : Excl) (b0 : Bool) (r : List Acc) (pl : Payload) : MarkSet :=
  (if b0 = true then cS E r pl else MarkSet.empty).union
    (if (!ex.isEmptyB) = b0 then pl.anyM else MarkSet.empty)

theorem mem_contribB (E ex : Excl) (b0 : Bool) (a : Acc) (q : List Acc) (pl : Payload) (y : RFact) :
    y ∈ msRF .any (contribB E ex b0 (a :: q) pl) ↔
      ∃ x, x ∈ payRF E pl ∧ (y, b0) ∈ aboveS ex x.kind x.mark (a :: q) := by
  have hE : ∀ y : RFact, y ∈ msRF .any MarkSet.empty ↔ False :=
    fun y => ⟨fun h => by rw [mem_msRF] at h; obtain ⟨m, hm, _⟩ := h; exact has_empty hm,
      fun h => h.elim⟩
  unfold contribB
  rw [msRF_union_mem, List.mem_append]
  constructor
  · rintro (hy | hy)
    · cases b0 with
      | false => simp only [Bool.false_eq_true, ↓reduceIte] at hy; exact ((hE y).mp hy).elim
      | true =>
        simp only [↓reduceIte] at hy
        rw [mem_msRF] at hy
        obtain ⟨m, hm, rfl⟩ := hy
        cases m with
        | conc t => exact nomatch hm
        | starEx x => exact hm.elim
        | star =>
          have hm' : (pl.star && E.admits (a :: q)) = true := hm
          rw [Bool.and_eq_true] at hm'
          refine ⟨⟨[], .star E, .star⟩, mem_payRF.mpr (Or.inl ⟨hm'.1, rfl⟩), ?_⟩
          show _ ∈ (if E.admits (a :: q) = true then _ else _)
          rw [hm'.2]
          exact pair_mem_singleton.mpr ⟨rfl, rfl⟩
    · by_cases hb' : (!ex.isEmptyB) = b0
      · rw [if_pos hb', mem_msRF] at hy
        obtain ⟨m, hm, rfl⟩ := hy
        refine ⟨⟨[], .any, m⟩, mem_payRF.mpr (Or.inr (Or.inl ⟨m, hm, rfl⟩)), ?_⟩
        show _ ∈ [((⟨[], .any, m⟩ : RFact), !(true && ex.isEmptyB))]
        rw [Bool.true_and]
        exact pair_mem_singleton.mpr ⟨rfl, hb'.symm⟩
      · rw [if_neg hb'] at hy
        exact ((hE y).mp hy).elim
  · rintro ⟨x, hx, hy⟩
    rcases mem_payRF.mp hx with ⟨hs, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, _, rfl⟩
    · have hy' : (y, b0) ∈ (if E.admits (a :: q) = true then
          [((⟨[], .any, .star⟩ : RFact), !(false && ex.isEmptyB))] else []) := hy
      rcases Bool.eq_false_or_eq_true (E.admits (a :: q)) with h | h
      · rw [h] at hy'
        simp only [↓reduceIte] at hy'
        obtain ⟨rfl, hb⟩ := pair_mem_singleton.mp hy'
        rw [Bool.false_and, Bool.not_false] at hb
        subst hb
        left
        simp only [↓reduceIte]
        rw [mem_msRF]
        refine ⟨.star, ?_, rfl⟩
        show (pl.star && E.admits (a :: q)) = true
        rw [hs, h]; rfl
      · rw [h] at hy'
        exact nomatch hy'
    · have hy' : (y, b0) ∈ [((⟨[], .any, m⟩ : RFact), !(true && ex.isEmptyB))] := hy
      obtain ⟨rfl, hb⟩ := pair_mem_singleton.mp hy'
      rw [Bool.true_and] at hb
      right
      rw [if_pos hb.symm, mem_msRF]
      exact ⟨m, hm, rfl⟩
    · exact nomatch hy

/-! ### Well-formed tries: sibling accessors are distinct -/

def labels : Trie → List Acc
  | .nil => []
  | .cons a _ _ nx => a :: labels nx

def wfT : Trie → Bool
  | .nil => true
  | .cons a _ bl nx => !memB a (labels nx) && wfT bl && wfT nx

/-- The trie invariant (as in a map from accessor to child). -/
def Tree.wf (t : Tree) : Bool := wfT t.kids

theorem wfT_cons {a : Acc} {h : Payload} {bl nx : Trie} :
    wfT (.cons a h bl nx) = true ↔
      memB a (labels nx) = false ∧ wfT bl = true ∧ wfT nx = true := by
  show ((!memB a (labels nx) && wfT bl) && wfT nx) = true ↔ _
  rcases Bool.eq_false_or_eq_true (memB a (labels nx)) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (wfT bl) with h2 | h2 <;>
  rcases Bool.eq_false_or_eq_true (wfT nx) with h3 | h3 <;>
  simp only [h1, h2, h3] <;> decide

theorem childAt_wf {a : Acc} {s : Tree} (k : Trie) (hk : wfT k = true) (hs : childAt a k = some s) :
    s.wf = true := by
  induction k with
  | nil => exact nomatch hs
  | cons c h bl nx _ ihn =>
    obtain ⟨_, hbl, hnx⟩ := wfT_cons.mp hk
    rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
    · simp only [childAt, hac, ↓reduceIte] at hs
      cases hs
      exact hbl
    · simp only [childAt, hac, Bool.false_eq_true, ↓reduceIte] at hs
      exact ihn hnx hs

/-! ### The walk -/

theorem stepR_above {e e' : Excl} {a : Acc} {q : List Acc} {x : RFact} (hx : x.path = []) :
    stepR e e' (a :: q) x = aboveS (e.union e') x.kind x.mark (a :: q) := by
  unfold stepR; rw [hx]; rfl

theorem stepR_cons (e e' : Excl) (a c : Acc) (q : List Acc) (x : RFact) :
    stepR e e' (a :: q) (x.cons c) = if Nat.beq a c then stepR e e' q x else [] := by
  unfold stepR
  show (match relate (a :: q) (c :: x.path) with
    | .below r => belowS e e' x.kind x.mark r
    | .above r => aboveS (e.union e') x.kind x.mark r
    | .apart   => []) = _
  rw [relate_cons_cons]
  rcases Bool.eq_false_or_eq_true (Nat.beq a c) with h | h <;>
    simp only [h, Bool.false_eq_true, ↓reduceIte]

/-- `kids_step` for any per-fact function that follows the accessor of a child. -/
theorem kids_stepG {β : Type} {E : Excl} (F : List Acc → RFact → List β)
    (hF : ∀ (a : Acc) (q : List Acc) (c : Acc) (x : RFact),
      F (a :: q) (x.cons c) = if Nat.beq a c then F q x else [])
    {a : Acc} {q : List Acc} (k : Trie) (hk : wfT k = true) (z : β) :
    (∃ x, x ∈ trieRF E k ∧ z ∈ F (a :: q) x) ↔
      ∃ s, childAt a k = some s ∧ ∃ x, x ∈ treeRF E s ∧ z ∈ F q x := by
  have noLab : ∀ k' : Trie, memB a (labels k') = false → ∀ x, x ∈ trieRF E k' → F (a :: q) x = [] := by
    intro k'
    induction k' with
    | nil => intro _ x hx; exact nomatch hx
    | cons c h bl nx _ ihn =>
      intro hk' x hx
      have hk'' : (Nat.beq a c || memB a (labels nx)) = false := hk'
      rw [Bool.or_eq_false_iff] at hk''
      rw [trieRF_cons] at hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
        rw [hF, hk''.1]
        rfl
      · exact ihn hk''.2 x hx
  induction k with
  | nil => exact ⟨fun ⟨_, h, _⟩ => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | cons c h bl nx _ ihn =>
    obtain ⟨hl, _, hnx⟩ := wfT_cons.mp hk
    rw [trieRF_cons]
    rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
    · have hc : childAt a (.cons c h bl nx) = some ⟨h, bl⟩ := by
        simp only [childAt, hac, ↓reduceIte]
      have hac' : a = c := Nat.eq_of_beq_eq_true hac
      subst hac'
      rw [hc]
      constructor
      · rintro ⟨x, hx, hy⟩
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
          rw [hF, hac] at hy
          exact ⟨_, rfl, x', hx', hy⟩
        · rw [noLab nx hl x hx] at hy
          exact nomatch hy
      · rintro ⟨s, hs, x, hx, hy⟩
        cases hs
        refine ⟨x.cons a, List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x, hx, rfl⟩)), ?_⟩
        rw [hF, hac]
        exact hy
    · have hc : childAt a (.cons c h bl nx) = childAt a nx := by
        simp only [childAt, hac, Bool.false_eq_true, ↓reduceIte]
      rw [hc]
      refine Iff.trans ?_ (ihn hnx)
      constructor
      · rintro ⟨x, hx, hy⟩
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
          rw [hF, hac] at hy
          exact nomatch hy
        · exact ⟨x, hx, hy⟩
      · rintro ⟨x, hx, hy⟩
        exact ⟨x, List.mem_append.mpr (Or.inr hx), hy⟩

/-- The walk along `fr.path` with a contribution function for the proper prefixes. -/
def walkG (cf : List Acc → Payload → MarkSet) : List Acc → Tree → Option Tree × MarkSet
  | [],     t => (some t, MarkSet.empty)
  | a :: q, t =>
    match childAt a t.kids with
    | none   => (none, cf (a :: q) t.root)
    | some s => ((walkG cf q s).1, (cf (a :: q) t.root).union (walkG cf q s).2)

theorem walkG_cons_none {cf : List Acc → Payload → MarkSet} {a : Acc} {q : List Acc} {t : Tree}
    (h : childAt a t.kids = none) : walkG cf (a :: q) t = (none, cf (a :: q) t.root) := by
  simp only [walkG, h]

theorem walkG_cons_some {cf : List Acc → Payload → MarkSet} {a : Acc} {q : List Acc} {t s : Tree}
    (h : childAt a t.kids = some s) :
    walkG cf (a :: q) t = ((walkG cf q s).1, (cf (a :: q) t.root).union (walkG cf q s).2) := by
  simp only [walkG, h]

/-- Every walk ends at `subtreeAt`. -/
theorem walkG_fst (cf : List Acc → Payload → MarkSet) (q : List Acc) (t : Tree) :
    (walkG cf q t).1 = subtreeAt q t := by
  induction q generalizing t with
  | nil => rfl
  | cons a q ih =>
    cases h : childAt a t.kids with
    | none => rw [walkG_cons_none h]; simp only [subtreeAt, h]
    | some s => rw [walkG_cons_some h, ih]; simp only [subtreeAt, h]

theorem walkG_wf (cf : List Acc → Payload → MarkSet) (q : List Acc) (t : Tree) (ht : t.wf = true) :
    ((walkG cf q t).1.getD emptyTree).wf = true := by
  induction q generalizing t with
  | nil => exact ht
  | cons a q ih =>
    cases h : childAt a t.kids with
    | none => rw [walkG_cons_none h]; rfl
    | some s => rw [walkG_cons_some h]; exact ih s (childAt_wf t.kids ht h)



/-! ### The routed result of one tree -/

def bPart (b0 : Bool) (E ex : Excl) (pl : Payload) : List RFact :=
  if b0 = true then msRF .any (movedBelow ex pl) else rootF E ex pl

def kPart (b0 : Bool) (E e e' : Excl) (k : Trie) : List RFact :=
  if b0 = true then [] else trieRF E (filterKids e e' k)

/-- The results with step bit `b0` of one tree with exclusion `E`, relative to `to.path`. -/
def resL (b0 : Bool) (E e e' : Excl) (q : List Acc) (t : Tree) : List RFact :=
  bPart b0 E (e.union e') ((walkG (contribB E (e.union e') b0) q t).1.getD emptyTree).root ++
    msRF .any (walkG (contribB E (e.union e') b0) q t).2 ++
    kPart b0 E e e' ((walkG (contribB E (e.union e') b0) q t).1.getD emptyTree).kids

theorem mem_bPart (b0 : Bool) (E ex : Excl) (pl : Payload) (y : RFact) :
    y ∈ bPart b0 E ex pl ↔ ∃ x, x ∈ payRF E pl ∧ (y, b0) ∈ belowNilS ex x.kind x.mark := by
  cases b0 with
  | false => exact mem_rootF E ex pl y
  | true => exact mem_movedBelow E ex pl y

theorem mem_kPart (b0 : Bool) (E e e' : Excl) (k : Trie) (y : RFact) :
    y ∈ kPart b0 E e e' k ↔ ∃ x, x ∈ trieRF E k ∧ (y, b0) ∈ belowS e e' x.kind x.mark x.path := by
  rw [mem_kidsS]
  cases b0 with
  | false => exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  | true => exact ⟨fun h => (nomatch h), fun h => nomatch h.1⟩

theorem bPart_empty (b0 : Bool) (E ex : Excl) : bPart b0 E ex Payload.empty = [] := by
  cases b0 with
  | false =>
    cases ex with
    | univ => rfl
    | set l => cases l <;> rfl
  | true =>
    cases ex with
    | univ => rfl
    | set l => cases l <;> rfl

theorem mem_msRF_empty (k : Kind) (y : RFact) : y ∈ msRF k MarkSet.empty ↔ False :=
  ⟨fun h => by rw [mem_msRF] at h; obtain ⟨m, hm, _⟩ := h; exact has_empty hm, fun h => h.elim⟩

/-- The routed relative form: the results with step bit `b0` of one layer. -/
theorem resL_spec (b0 : Bool) (E e e' : Excl) (q : List Acc) (t : Tree) (ht : t.wf = true)
    (y : RFact) :
    y ∈ resL b0 E e e' q t ↔ ∃ x, x ∈ treeRF E t ∧ (y, b0) ∈ stepR e e' q x := by
  induction q generalizing t with
  | nil =>
    show y ∈ bPart b0 E (e.union e') t.root ++ msRF .any MarkSet.empty ++ kPart b0 E e e' t.kids ↔ _
    rw [List.mem_append, List.mem_append, mem_msRF_empty, or_false, mem_bPart, mem_kPart]
    constructor
    · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
      · refine ⟨x, List.mem_append.mpr (Or.inl hx), ?_⟩
        rcases mem_payRF.mp hx with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact hy
      · exact ⟨x, List.mem_append.mpr (Or.inr hx), hy⟩
    · rintro ⟨x, hx, hy⟩
      rcases List.mem_append.mp hx with hx | hx
      · left
        refine ⟨x, hx, ?_⟩
        rcases mem_payRF.mp hx with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact hy
      · exact Or.inr ⟨x, hx, hy⟩
  | cons a q ih =>
    have hroot : (∃ x, x ∈ payRF E t.root ∧ (y, b0) ∈ stepR e e' (a :: q) x) ↔
        y ∈ msRF .any (contribB E (e.union e') b0 (a :: q) t.root) := by
      rw [mem_contribB]
      constructor
      · rintro ⟨x, hx, hy⟩
        have hp : x.path = [] := by
          rcases mem_payRF.mp hx with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
        rw [stepR_above hp] at hy
        exact ⟨x, hx, hy⟩
      · rintro ⟨x, hx, hy⟩
        have hp : x.path = [] := by
          rcases mem_payRF.mp hx with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
        exact ⟨x, hx, by rw [stepR_above hp]; exact hy⟩
    have hsplit : (∃ x, x ∈ treeRF E t ∧ (y, b0) ∈ stepR e e' (a :: q) x) ↔
        (∃ x, x ∈ payRF E t.root ∧ (y, b0) ∈ stepR e e' (a :: q) x) ∨
        (∃ x, x ∈ trieRF E t.kids ∧ (y, b0) ∈ stepR e e' (a :: q) x) := by
      constructor
      · rintro ⟨x, hx, hy⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact Or.inl ⟨x, hx, hy⟩
        · exact Or.inr ⟨x, hx, hy⟩
      · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
        · exact ⟨x, List.mem_append.mpr (Or.inl hx), hy⟩
        · exact ⟨x, List.mem_append.mpr (Or.inr hx), hy⟩
    rw [hsplit, hroot, kids_stepG (E := E) (stepR e e') (fun a q c x => stepR_cons e e' a c q x) t.kids ht]
    unfold resL
    cases h : childAt a t.kids with
    | none =>
      rw [walkG_cons_none h]
      show y ∈ bPart b0 E (e.union e') Payload.empty ++ _ ++ kPart b0 E e e' Trie.nil ↔ _
      rw [bPart_empty]
      have hk : kPart b0 E e e' Trie.nil = [] := by cases b0 <;> rfl
      rw [hk, List.nil_append, List.append_nil]
      constructor
      · intro hy; exact Or.inl hy
      · rintro (hy | ⟨_, hs, _⟩)
        · exact hy
        · exact nomatch hs
    | some s =>
      rw [walkG_cons_some h]
      have hs := ih s (childAt_wf t.kids ht h)
      unfold resL at hs
      rw [List.mem_append, List.mem_append] at hs
      show y ∈ bPart b0 E (e.union e') ((walkG (contribB E (e.union e') b0) q s).1.getD emptyTree).root
        ++ msRF .any ((contribB E (e.union e') b0 (a :: q) t.root).union
          (walkG (contribB E (e.union e') b0) q s).2)
        ++ kPart b0 E e e' ((walkG (contribB E (e.union e') b0) q s).1.getD emptyTree).kids ↔ _
      rw [List.mem_append, List.mem_append, msRF_union_mem, List.mem_append]
      have hex : (∃ s', some s = some s' ∧ ∃ x, x ∈ treeRF E s' ∧ (y, b0) ∈ stepR e e' q x) ↔
          ∃ x, x ∈ treeRF E s ∧ (y, b0) ∈ stepR e e' q x :=
        ⟨fun ⟨s', hs', hx⟩ => by cases hs'; exact hx, fun hx => ⟨s, rfl, hx⟩⟩
      rw [hex, ← hs]
      constructor
      · rintro ((hP | hC | hW) | hK)
        · exact Or.inr (Or.inl (Or.inl hP))
        · exact Or.inl hC
        · exact Or.inr (Or.inl (Or.inr hW))
        · exact Or.inr (Or.inr hK)
      · rintro (hC | (hP | hW) | hK)
        · exact Or.inl (Or.inr (Or.inl hC))
        · exact Or.inl (Or.inl hP)
        · exact Or.inl (Or.inr (Or.inr hW))
        · exact Or.inr hK


/-! ### The output trees -/

def addAny (pl : Payload) (ms : MarkSet) : Payload := ⟨pl.star, pl.anyM.union ms, pl.exactM⟩

theorem mem_addAny (E : Excl) (pl : Payload) (ms : MarkSet) (y : RFact) :
    y ∈ payRF E (addAny pl ms) ↔ y ∈ payRF E pl ∨ y ∈ msRF .any ms := by
  rw [mem_payRF, mem_payRF, mem_msRF]
  constructor
  · rintro (h | ⟨m, hm, rfl⟩ | h)
    · exact Or.inl (Or.inl h)
    · rcases has_union.mp hm with h | h
      · exact Or.inl (Or.inr (Or.inl ⟨m, h, rfl⟩))
      · exact Or.inr ⟨m, h, rfl⟩
    · exact Or.inl (Or.inr (Or.inr h))
  · rintro ((h | ⟨m, hm, rfl⟩ | h) | ⟨m, hm, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨m, has_union.mpr (Or.inl hm), rfl⟩)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl ⟨m, has_union.mpr (Or.inr hm), rfl⟩)

/-- The results with step bit `false`, except the root `*` leaf: one tree with
    the exclusion `E` of the input (relative to `to.path`). The children below
    the kept children are SHARED with the input tree. -/
def resA (E e e' : Excl) (q : List Acc) (t : Tree) : Tree :=
  let w := walkG (contribB E (e.union e') false) q t
  let S := w.1.getD emptyTree
  ⟨addAny (payBelowN (e.union e') S.root) w.2, filterKids e e' S.kids⟩

/-- The root `*` leaf at `fr.path`: it moves to `to.path` with the exclusion
    `E ∪ (e ∪ e')` (the strong update changes the exclusion of this leaf only). -/
def resStar (E e e' : Excl) (q : List Acc) (t : Tree) : Bool :=
  ((walkG (contribB E (e.union e') false) q t).1.getD emptyTree).root.star

/-- The results with step bit `true`: `[any]` marks at `to.path`. -/
def resM (E e e' : Excl) (q : List Acc) (t : Tree) : MarkSet :=
  let w := walkG (contribB E (e.union e') true) q t
  let S := w.1.getD emptyTree
  (movedBelow (e.union e') S.root).union w.2

theorem mem_resA (E e e' : Excl) (q : List Acc) (t : Tree) (y : RFact) :
    y ∈ resL false E e e' q t ↔
      y ∈ treeRF E (resA E e e' q t) ∨
      (resStar E e e' q t = true ∧ y = ⟨[], .star (E.union (e.union e')), .star⟩) := by
  show y ∈ (starRF (E.union (e.union e'))
      ((walkG (contribB E (e.union e') false) q t).1.getD emptyTree).root.star ++
      payRF E (payBelowN (e.union e') ((walkG (contribB E (e.union e') false) q t).1.getD emptyTree).root))
      ++ msRF .any (walkG (contribB E (e.union e') false) q t).2
      ++ trieRF E (filterKids e e' ((walkG (contribB E (e.union e') false) q t).1.getD emptyTree).kids) ↔
    y ∈ payRF E (addAny (payBelowN (e.union e')
        ((walkG (contribB E (e.union e') false) q t).1.getD emptyTree).root)
        (walkG (contribB E (e.union e') false) q t).2)
      ++ trieRF E (filterKids e e' ((walkG (contribB E (e.union e') false) q t).1.getD emptyTree).kids) ∨
    (((walkG (contribB E (e.union e') false) q t).1.getD emptyTree).root.star = true ∧
      y = ⟨[], .star (E.union (e.union e')), .star⟩)
  simp only [List.mem_append, mem_addAny, mem_starRF, or_assoc, or_comm, or_left_comm]

theorem mem_resM (E e e' : Excl) (q : List Acc) (t : Tree) (y : RFact) :
    y ∈ msRF .any (resM E e e' q t) ↔ y ∈ resL true E e e' q t := by
  unfold resM
  rw [msRF_union_mem]
  show _ ↔ y ∈ msRF .any _ ++ msRF .any _ ++ []
  rw [List.append_nil]

/-- A tree with the root `*` leaf only. -/
def starTree : Tree := ⟨⟨true, MarkSet.empty, MarkSet.empty⟩, .nil⟩

/-- A tree with root `[any]` leaves only. -/
def anyTree (M : MarkSet) : Tree := ⟨⟨false, M, MarkSet.empty⟩, .nil⟩

/-- The tree form of `applyEdge` for a micro edge `fr → to` with `*` tails and
    abstract marks, on ONE edge tree (premise, layer, E, X). Every output tree keeps
    the mark exclusion `X` of the input: the target mark `*` passes the mark
    `starM X` of a fact through (`markComp .star m = some m`). The results are grouped
    by (exclusion, layer):
    * the results with step bit `false` stay in the layer of the input, in a tree
      with the exclusion `E`; the root `*` leaf goes to a tree with the exclusion
      `E ∪ (e ∪ e')` (merged into the first tree if the two exclusions are equal);
    * the results with step bit `true` go to the demand layer (`[any]` leaves, no
      exclusion; the tree key uses `{}`);
    * a demand input gives all its results to one demand tree.
    The input tree is on base `b`; the results are on base `to.base`. -/
def applyTreeE (b : Base) (t : EdgeTree) (fr to : PFact) : List EdgeTree :=
  if Nat.beq b fr.base then
    let e  := tailExcl fr.kind
    let e' := tailExcl to.kind
    let A  := resA t.excl e e' fr.path t.tree
    let st := resStar t.excl e e' fr.path t.tree
    let M  := resM t.excl e e' fr.path t.tree
    let E2 := t.excl.union (e.union e')
    if t.demand then
      [⟨t.excl, t.mx, true, prependPath to.path ⟨addAny A.root M, A.kids⟩⟩]
    else
      (if st then
        (if E2 = t.excl then
          [⟨t.excl, t.mx, false, prependPath to.path ⟨⟨true, A.root.anyM, A.root.exactM⟩, A.kids⟩⟩]
        else
          [⟨t.excl, t.mx, false, prependPath to.path A⟩, ⟨E2, t.mx, false, prependPath to.path starTree⟩])
      else [⟨t.excl, t.mx, false, prependPath to.path A⟩]) ++
      [⟨Excl.empty, t.mx, true, prependPath to.path (anyTree M)⟩]
  else []

/-! ### No `*` leaf (the invariant of the demand layer) -/

def noStarT : Trie → Bool
  | .nil => true
  | .cons _ h bl nx => !h.star && noStarT bl && noStarT nx

def Tree.noStar (t : Tree) : Bool := !t.root.star && noStarT t.kids

theorem noStarT_cons {a : Acc} {h : Payload} {bl nx : Trie} :
    noStarT (.cons a h bl nx) = true ↔ h.star = false ∧ noStarT bl = true ∧ noStarT nx = true := by
  show ((!h.star && noStarT bl) && noStarT nx) = true ↔ _
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', and_assoc]

theorem noStar_iff {t : Tree} : t.noStar = true ↔ t.root.star = false ∧ noStarT t.kids = true := by
  show (!t.root.star && noStarT t.kids) = true ↔ _
  rw [Bool.and_eq_true, Bool.not_eq_true']

theorem payRF_noStar {E : Excl} {pl : Payload} (hp : pl.star = false) {x : RFact}
    (hx : x ∈ payRF E pl) : x.kind.isStar = false := by
  rcases mem_payRF.mp hx with ⟨hs, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · rw [hp] at hs; exact nomatch hs
  · rfl
  · rfl

theorem trieRF_noStar (E : Excl) (k : Trie) (hk : noStarT k = true) :
    ∀ x, x ∈ trieRF E k → x.kind.isStar = false := by
  induction k with
  | nil => intro x hx; exact nomatch hx
  | cons a h bl nx ihb ihn =>
    intro x hx
    obtain ⟨hh, hbl, hnx⟩ := noStarT_cons.mp hk
    rw [trieRF_cons] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
      rcases List.mem_append.mp hx' with hx' | hx'
      · exact payRF_noStar (x := x') hh hx'
      · exact ihb hbl x' hx'
    · exact ihn hnx x hx

/-- A tree without `*` leaves holds no `*` fact. -/
theorem treeRF_noStar (E : Excl) (t : Tree) (ht : t.noStar = true) (x : RFact)
    (hx : x ∈ treeRF E t) : x.kind.isStar = false := by
  have ht' := noStar_iff.mp ht
  rcases List.mem_append.mp hx with hx | hx
  · exact payRF_noStar ht'.1 hx
  · exact trieRF_noStar E t.kids ht'.2 x hx

theorem childAt_noStar {a : Acc} {s : Tree} (k : Trie) (hk : noStarT k = true)
    (hs : childAt a k = some s) : s.noStar = true := by
  induction k with
  | nil => exact nomatch hs
  | cons c h bl nx _ ihn =>
    obtain ⟨hh, hbl, hnx⟩ := noStarT_cons.mp hk
    rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
    · simp only [childAt, hac, ↓reduceIte] at hs
      cases hs
      exact noStar_iff.mpr ⟨hh, hbl⟩
    · simp only [childAt, hac, Bool.false_eq_true, ↓reduceIte] at hs
      exact ihn hnx hs

theorem walkG_noStar (cf : List Acc → Payload → MarkSet) (q : List Acc) (t : Tree)
    (ht : t.noStar = true) : ((walkG cf q t).1.getD emptyTree).noStar = true := by
  induction q generalizing t with
  | nil => exact ht
  | cons a q ih =>
    cases h : childAt a t.kids with
    | none => rw [walkG_cons_none h]; rfl
    | some s =>
      rw [walkG_cons_some h]
      exact ih s (childAt_noStar t.kids (noStar_iff.mp ht).2 h)

theorem filterKids_noStar (e e' : Excl) (k : Trie) (hk : noStarT k = true) :
    noStarT (filterKids e e' k) = true := by
  induction k with
  | nil => rfl
  | cons a h bl nx _ ihn =>
    obtain ⟨hh, hbl, hnx⟩ := noStarT_cons.mp hk
    rcases Bool.eq_false_or_eq_true (passB e e' a) with hp | hp
    · simp only [filterKids, hp, ↓reduceIte]
      exact noStarT_cons.mpr ⟨hh, hbl, ihn hnx⟩
    · simp only [filterKids, hp, Bool.false_eq_true, ↓reduceIte]
      exact ihn hnx

theorem prependPath_noStar (p : List Acc) (t : Tree) (ht : t.noStar = true) :
    (prependPath p t).noStar = true := by
  induction p with
  | nil => exact ht
  | cons a p ih =>
    have ih' := noStar_iff.mp ih
    exact noStar_iff.mpr ⟨rfl, noStarT_cons.mpr ⟨ih'.1, ih'.2, rfl⟩⟩

theorem resStar_noStar (E e e' : Excl) (q : List Acc) (t : Tree) (ht : t.noStar = true) :
    resStar E e e' q t = false :=
  (noStar_iff.mp (walkG_noStar _ q t ht)).1

theorem mem_toAFacts_pp (tb : Base) (tp : List Acc) (E : Excl) (X : List Mark) (d : Bool) (T : Tree)
    (a : AFact) :
    a ∈ toAFacts tb ⟨E, X, d, prependPath tp T⟩ ↔
      ∃ y, y ∈ treeRF E T ∧ a = ⟨(markX X (y.pre tp)).toP tb, d⟩ := by
  rw [mem_toAFacts]
  show (∃ x, x ∈ treeRF E (prependPath tp T) ∧ _) ↔ _
  rw [treeRF_prependPath]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.pre tp, List.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩

/-- MAIN 4. `applyTreeE` is exact on whole `AFact`s (fact AND demand bit): an
    `AFact` is in the output trees iff `applyEdge` gives it for some `AFact` of
    the input tree. -/
theorem applyTreeE_mem (b : Base) (t : EdgeTree) (hwf : t.tree.wf = true)
    (hinv : t.demand = true → t.tree.noStar = true) (fr to : PFact) {e e' : Excl}
    (hfk : fr.kind = .star e) (htk : to.kind = .star e') (hfm : fr.mark = .star)
    (htm : to.mark = .star) (a : AFact) :
    a ∈ (applyTreeE b t fr to).flatMap (toAFacts to.base) ↔
      ∃ c, c ∈ toAFacts b t ∧ a ∈ (applyEdge c fr to).facts := by
  rcases t with ⟨E, X, d, T⟩
  rcases fr with ⟨fb, fp, fk, fm⟩
  rcases to with ⟨tb, tp, tk, tm⟩
  dsimp only at hfk htk hfm htm hwf hinv
  subst hfk htk hfm htm
  unfold applyTreeE
  dsimp only
  rcases Bool.eq_false_or_eq_true (Nat.beq b fb) with hb | hb
  · have hb' : b = fb := Nat.eq_of_beq_eq_true hb
    subst hb'
    have hR : (∃ c, c ∈ toAFacts b ⟨E, X, d, T⟩ ∧
        a ∈ (applyEdge c ⟨b, fp, .star e, .star⟩ ⟨tb, tp, .star e', .star⟩).facts) ↔
        ∃ y s, y ∈ resL s E e e' fp T ∧ a = ⟨(markX X (y.pre tp)).toP tb, d || s⟩ := by
      constructor
      · rintro ⟨c, hc, ha⟩
        obtain ⟨x, hx, rfl⟩ := (mem_toAFacts b _ c).mp hc
        rw [applyEdge_eqX b tb fp tp e e' X x d (treeRF_legal E T x hx)
          (fun h => treeRF_noStar E T (hinv h) x hx), List.mem_map] at ha
        obtain ⟨⟨y, s⟩, hp, rfl⟩ := ha
        exact ⟨y, s, (resL_spec s E e e' fp T hwf y).mpr ⟨x, hx, hp⟩, rfl⟩
      · rintro ⟨y, s, hy, rfl⟩
        obtain ⟨x, hx, hp⟩ := (resL_spec s E e e' fp T hwf y).mp hy
        refine ⟨⟨(markX X x).toP b, d⟩, (mem_toAFacts b _ _).mpr ⟨x, hx, rfl⟩, ?_⟩
        rw [applyEdge_eqX b tb fp tp e e' X x d (treeRF_legal E T x hx)
          (fun h => treeRF_noStar E T (hinv h) x hx), List.mem_map]
        exact ⟨(y, s), hp, rfl⟩
    rw [hR]
    dsimp only [tailExcl]
    simp only [hb, ↓reduceIte]
    have hA := mem_resA E e e' fp T
    have hM := mem_resM E e e' fp T
    cases d with
    | true =>
      have hst := resStar_noStar E e e' fp T (hinv rfl)
      simp only [↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [mem_toAFacts_pp]
      have hmem : ∀ y, y ∈ treeRF E ⟨addAny (resA E e e' fp T).root (resM E e e' fp T),
          (resA E e e' fp T).kids⟩ ↔
          y ∈ treeRF E (resA E e e' fp T) ∨ y ∈ msRF .any (resM E e e' fp T) := by
        intro y
        show y ∈ payRF E (addAny _ _) ++ trieRF E _ ↔ y ∈ payRF E _ ++ trieRF E _ ∨ _
        rw [List.mem_append, mem_addAny, List.mem_append]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
          · exact Or.inl (Or.inr h)
        · rintro ((h | h) | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
          · exact Or.inl (Or.inr h)
      constructor
      · rintro ⟨y, hy, rfl⟩
        rcases (hmem y).mp hy with h | h
        · exact ⟨y, false, (hA y).mpr (Or.inl h), rfl⟩
        · exact ⟨y, true, (hM y).mp h, rfl⟩
      · rintro ⟨y, s, hy, rfl⟩
        refine ⟨y, (hmem y).mpr ?_, by rw [Bool.true_or]⟩
        cases s with
        | false =>
          rcases (hA y).mp hy with h | ⟨h, _⟩
          · exact Or.inl h
          · rw [hst] at h; exact nomatch h
        | true => exact Or.inr ((hM y).mpr hy)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [List.flatMap_append, List.mem_append]
      have hC : a ∈ [(⟨Excl.empty, X, true, prependPath tp (anyTree (resM E e e' fp T))⟩ : EdgeTree)].flatMap
          (toAFacts tb) ↔ ∃ y, y ∈ msRF .any (resM E e e' fp T) ∧ a = ⟨(markX X (y.pre tp)).toP tb, true⟩ := by
        rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, mem_toAFacts_pp]
        constructor
        · rintro ⟨y, hy, rfl⟩
          refine ⟨y, ?_, rfl⟩
          have hy' : y ∈ payRF Excl.empty ⟨false, resM E e e' fp T, MarkSet.empty⟩ ++ [] := hy
          rw [List.append_nil, mem_payRF] at hy'
          rcases hy' with ⟨h, _⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, _⟩
          · exact nomatch h
          · exact mem_msRF.mpr ⟨m, hm, rfl⟩
          · exact absurd hm has_empty
        · rintro ⟨y, hy, rfl⟩
          refine ⟨y, ?_, rfl⟩
          show y ∈ payRF Excl.empty ⟨false, resM E e e' fp T, MarkSet.empty⟩ ++ []
          rw [List.append_nil, mem_payRF]
          obtain ⟨m, hm, rfl⟩ := mem_msRF.mp hy
          exact Or.inr (Or.inl ⟨m, hm, rfl⟩)
      have hX : a ∈ (if resStar E e e' fp T = true then
            (if E.union (e.union e') = E then
              [(⟨E, X, false, prependPath tp ⟨⟨true, (resA E e e' fp T).root.anyM,
                (resA E e e' fp T).root.exactM⟩, (resA E e e' fp T).kids⟩⟩ : EdgeTree)]
            else [⟨E, X, false, prependPath tp (resA E e e' fp T)⟩,
              ⟨E.union (e.union e'), X, false, prependPath tp starTree⟩])
          else [⟨E, X, false, prependPath tp (resA E e e' fp T)⟩]).flatMap (toAFacts tb) ↔
          ∃ y, y ∈ resL false E e e' fp T ∧ a = ⟨(markX X (y.pre tp)).toP tb, false⟩ := by
        have hAstar : (resA E e e' fp T).root.star = false := by
          show (payBelowN (e.union e') _).star = false
          cases e.union e' with
          | univ => rfl
          | set l => cases l <;> rfl
        cases hst : resStar E e e' fp T with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, List.flatMap_cons, List.flatMap_nil,
            List.append_nil]
          rw [mem_toAFacts_pp]
          constructor
          · rintro ⟨y, hy, rfl⟩; exact ⟨y, (hA y).mpr (Or.inl hy), rfl⟩
          · rintro ⟨y, hy, rfl⟩
            rcases (hA y).mp hy with h | ⟨h, _⟩
            · exact ⟨y, h, rfl⟩
            · rw [hst] at h; exact nomatch h
        | true =>
          simp only [↓reduceIte]
          by_cases hE2 : E.union (e.union e') = E
          · rw [if_pos hE2]
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            rw [mem_toAFacts_pp]
            have hmem : ∀ y, y ∈ treeRF E ⟨⟨true, (resA E e e' fp T).root.anyM,
                (resA E e e' fp T).root.exactM⟩, (resA E e e' fp T).kids⟩ ↔
                y ∈ treeRF E (resA E e e' fp T) ∨ y = ⟨[], .star E, .star⟩ := by
              intro y
              show y ∈ payRF E _ ++ trieRF E _ ↔ y ∈ payRF E _ ++ trieRF E _ ∨ _
              rw [List.mem_append, List.mem_append, mem_payRF, mem_payRF, hAstar]
              constructor
              · rintro ((⟨_, rfl⟩ | h | h) | h)
                · exact Or.inr rfl
                · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
                · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
                · exact Or.inl (Or.inr h)
              · rintro (((⟨h, _⟩ | h | h) | h) | rfl)
                · exact nomatch h
                · exact Or.inl (Or.inr (Or.inl h))
                · exact Or.inl (Or.inr (Or.inr h))
                · exact Or.inr h
                · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
            constructor
            · rintro ⟨y, hy, rfl⟩
              refine ⟨y, (hA y).mpr ?_, rfl⟩
              rcases (hmem y).mp hy with h | rfl
              · exact Or.inl h
              · exact Or.inr ⟨hst, by rw [hE2]⟩
            · rintro ⟨y, hy, rfl⟩
              refine ⟨y, (hmem y).mpr ?_, rfl⟩
              rcases (hA y).mp hy with h | ⟨_, rfl⟩
              · exact Or.inl h
              · exact Or.inr (by rw [hE2])
          · rw [if_neg hE2]
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
            rw [List.mem_append, mem_toAFacts_pp, mem_toAFacts_pp]
            have hS : ∀ y, y ∈ treeRF (E.union (e.union e')) starTree ↔
                y = ⟨[], .star (E.union (e.union e')), .star⟩ := by
              intro y
              show y ∈ payRF _ _ ++ [] ↔ _
              rw [List.append_nil, mem_payRF]
              constructor
              · rintro (⟨_, rfl⟩ | ⟨m, hm, _⟩ | ⟨m, hm, _⟩)
                · rfl
                · exact absurd hm has_empty
                · exact absurd hm has_empty
              · rintro rfl; exact Or.inl ⟨rfl, rfl⟩
            constructor
            · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
              · exact ⟨y, (hA y).mpr (Or.inl hy), rfl⟩
              · exact ⟨y, (hA y).mpr (Or.inr ⟨hst, (hS y).mp hy⟩), rfl⟩
            · rintro ⟨y, hy, rfl⟩
              rcases (hA y).mp hy with h | ⟨_, h⟩
              · exact Or.inl ⟨y, h, rfl⟩
              · exact Or.inr ⟨y, (hS y).mpr h, rfl⟩
      refine (or_congr hX hC).trans ?_
      constructor
      · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
        · exact ⟨y, false, hy, rfl⟩
        · exact ⟨y, true, (hM y).mp hy, rfl⟩
      · rintro ⟨y, s, hy, rfl⟩
        cases s with
        | false => exact Or.inl ⟨y, hy, rfl⟩
        | true => exact Or.inr ⟨y, (hM y).mpr hy, rfl⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, List.flatMap_nil]
    constructor
    · intro h; exact nomatch h
    · rintro ⟨c, hc, ha⟩
      obtain ⟨x, _, rfl⟩ := (mem_toAFacts b _ c).mp hc
      have hnil : (applyEdge ⟨(markX X x).toP b, d⟩ ⟨fb, fp, .star e, .star⟩
          ⟨tb, tp, .star e', .star⟩).facts = [] := by
        unfold applyEdge
        simp only [RFact.toP, hb, Bool.false_eq_true, ↓reduceIte]
        rfl
      rw [hnil] at ha
      exact nomatch ha


/-- The demand-layer corollary: the pairs of the output trees of the layer `d`
    are the pairs of the `applyEdge` results of the layer `d`. -/
theorem applyTreeE_den (b : Base) (t : EdgeTree) (hwf : t.tree.wf = true)
    (hinv : t.demand = true → t.tree.noStar = true) (fr to : PFact) {e e' : Excl}
    (hfk : fr.kind = .star e) (htk : to.kind = .star e') (hfm : fr.mark = .star)
    (htm : to.mark = .star) {i : PFact} {d : Bool} {l0 l1 : Loc} :
    denA i ((applyTreeE b t fr to).flatMap (toAFacts to.base)) d l0 l1 ↔
      ∃ c ∈ toAFacts b t, ∃ r ∈ (applyEdge c fr to).facts, r.demand = d ∧ den i r.fact l0 l1 := by
  constructor
  · rintro ⟨a, ha, hd, hden⟩
    obtain ⟨c, hc, hr⟩ := (applyTreeE_mem b t hwf hinv fr to hfk htk hfm htm a).mp ha
    exact ⟨c, hc, a, hr, hd, hden⟩
  · rintro ⟨c, hc, r, hr, hd, hden⟩
    exact ⟨r, (applyTreeE_mem b t hwf hinv fr to hfk htk hfm htm r).mpr ⟨c, hc, hr⟩, hd, hden⟩

/-! ### Every operation keeps the trie invariant -/

theorem insK_labels {a c : Acc} {G : Tree → Tree} (k : Trie) :
    memB c (labels (insK a G k)) = true → memB c (labels k) = true ∨ c = a := by
  induction k with
  | nil =>
    intro h
    have h' : (Nat.beq c a || memB c []) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact Or.inr (Nat.eq_of_beq_eq_true h')
    · exact nomatch h'
  | cons d hp bl nx _ ihn =>
    rcases Bool.eq_false_or_eq_true (Nat.beq a d) with hac | hac
    · simp only [insK, hac, ↓reduceIte]
      intro h; exact Or.inl h
    · simp only [insK, hac, Bool.false_eq_true, ↓reduceIte]
      intro h
      have h' : (Nat.beq c d || memB c (labels (insK a G nx))) = true := h
      rw [Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · left; show (Nat.beq c d || memB c (labels nx)) = true; rw [h']; rfl
      · rcases ihn h' with h'' | h''
        · left; show (Nat.beq c d || memB c (labels nx)) = true; rw [h'', Bool.or_true]
        · exact Or.inr h''

theorem wfT_insK {a : Acc} {G : Tree → Tree} (hG : ∀ s : Tree, s.wf = true → (G s).wf = true)
    (k : Trie) (hk : wfT k = true) : wfT (insK a G k) = true := by
  induction k with
  | nil =>
    show wfT (.cons a (G emptyTree).root (G emptyTree).kids .nil) = true
    exact wfT_cons.mpr ⟨rfl, hG emptyTree rfl, rfl⟩
  | cons c h bl nx _ ihn =>
    obtain ⟨hl, hbl, hnx⟩ := wfT_cons.mp hk
    rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
    · simp only [insK, hac, ↓reduceIte]
      exact wfT_cons.mpr ⟨hl, hG ⟨h, bl⟩ hbl, hnx⟩
    · simp only [insK, hac, Bool.false_eq_true, ↓reduceIte]
      refine wfT_cons.mpr ⟨?_, hbl, ihn hnx⟩
      rcases Bool.eq_false_or_eq_true (memB c (labels (insK a G nx))) with h1 | h1
      · rcases insK_labels nx h1 with h2 | h2
        · rw [hl] at h2; exact nomatch h2
        · subst h2; rw [Nat.beq_refl] at hac; exact nomatch hac
      · exact h1

theorem atPath_wf {g : Tree → Tree} (hg : ∀ s : Tree, s.wf = true → (g s).wf = true)
    (p : List Acc) (t : Tree) (ht : t.wf = true) : (atPath p g t).wf = true := by
  induction p generalizing t with
  | nil => exact hg t ht
  | cons a p ih => exact wfT_insK (fun s hs => ih s hs) t.kids ht

theorem insert_wf (f : PFact) (t : Tree) (ht : t.wf = true) : (insert f t).wf = true :=
  atPath_wf (g := fun s => ⟨s.root.add f.kind f.mark, s.kids⟩) (fun _ hs => hs) f.path t ht

theorem mergeT_wf (k2 : Trie) (hk2 : wfT k2 = true) :
    ∀ k1, wfT k1 = true → wfT (mergeT k1 k2) = true := by
  induction k2 with
  | nil => intro k1 hk1; exact hk1
  | cons a h bl nx ihb ihn =>
    obtain ⟨_, hbl, hnx⟩ := wfT_cons.mp hk2
    intro k1 hk1
    exact ihn hnx _ (wfT_insK (G := fun s => ⟨s.root.union h, mergeT s.kids bl⟩)
      (fun s hs => ihb hbl s.kids hs) k1 hk1)

theorem merge_wf (t1 t2 : Tree) (h1 : t1.wf = true) (h2 : t2.wf = true) :
    (merge t1 t2).wf = true :=
  mergeT_wf t2.kids h2 t1.kids h1

theorem filterKids_labels {e e' : Excl} {c : Acc} (k : Trie) :
    memB c (labels (filterKids e e' k)) = true → memB c (labels k) = true := by
  induction k with
  | nil => exact id
  | cons a h bl nx _ ihn =>
    intro hc
    show (Nat.beq c a || memB c (labels nx)) = true
    rcases Bool.eq_false_or_eq_true (passB e e' a) with hp | hp
    · simp only [filterKids, hp, ↓reduceIte] at hc
      have hc' : (Nat.beq c a || memB c (labels (filterKids e e' nx))) = true := hc
      rw [Bool.or_eq_true] at hc'
      rcases hc' with h1 | h1
      · rw [h1]; rfl
      · rw [ihn h1, Bool.or_true]
    · simp only [filterKids, hp, Bool.false_eq_true, ↓reduceIte] at hc
      rw [ihn hc, Bool.or_true]

theorem wfT_filterKids (e e' : Excl) (k : Trie) (hk : wfT k = true) :
    wfT (filterKids e e' k) = true := by
  induction k with
  | nil => rfl
  | cons a h bl nx _ ihn =>
    obtain ⟨hl, hbl, hnx⟩ := wfT_cons.mp hk
    rcases Bool.eq_false_or_eq_true (passB e e' a) with hp | hp
    · simp only [filterKids, hp, ↓reduceIte]
      refine wfT_cons.mpr ⟨?_, hbl, ihn hnx⟩
      rcases Bool.eq_false_or_eq_true (memB a (labels (filterKids e e' nx))) with h1 | h1
      · rw [filterKids_labels nx h1] at hl; exact nomatch hl
      · exact h1
    · simp only [filterKids, hp, Bool.false_eq_true, ↓reduceIte]
      exact ihn hnx

theorem prependPath_wf (p : List Acc) (t : Tree) (ht : t.wf = true) :
    (prependPath p t).wf = true := by
  induction p with
  | nil => exact ht
  | cons a p ih => exact wfT_cons.mpr ⟨rfl, ih, rfl⟩

theorem resA_wf (E e e' : Excl) (q : List Acc) (t : Tree) (ht : t.wf = true) :
    (resA E e e' q t).wf = true :=
  wfT_filterKids _ _ _ (walkG_wf _ q t ht)

theorem resA_noStar (E e e' : Excl) (q : List Acc) (t : Tree) (ht : t.noStar = true) :
    (resA E e e' q t).noStar = true := by
  refine noStar_iff.mpr ⟨?_, filterKids_noStar _ _ _ (noStar_iff.mp (walkG_noStar _ q t ht)).2⟩
  show (payBelowN (e.union e') _).star = false
  cases e.union e' with
  | univ => rfl
  | set l => cases l <;> rfl

/-- MAIN 5. Every output tree is well formed, and every output tree of the
    demand layer has no `*` leaf (all `*` results are in the normal layer). -/
theorem applyTreeE_inv (b : Base) (t : EdgeTree) (hwf : t.tree.wf = true)
    (hinv : t.demand = true → t.tree.noStar = true) (fr to : PFact) :
    ∀ t', t' ∈ applyTreeE b t fr to →
      t'.tree.wf = true ∧ (t'.demand = true → t'.tree.noStar = true) := by
  rcases t with ⟨E, X, d, T⟩
  dsimp only at hwf hinv
  intro t' ht'
  unfold applyTreeE at ht'
  dsimp only at ht'
  have hAw := resA_wf E (tailExcl fr.kind) (tailExcl to.kind) fr.path T hwf
  rcases Bool.eq_false_or_eq_true (Nat.beq b fr.base) with hb | hb
  · simp only [hb, ↓reduceIte] at ht'
    cases d with
    | true =>
      simp only [↓reduceIte, List.mem_singleton] at ht'
      subst ht'
      refine ⟨prependPath_wf _ _ hAw, fun _ => prependPath_noStar _ _ ?_⟩
      have hA := noStar_iff.mp (resA_noStar E (tailExcl fr.kind) (tailExcl to.kind) fr.path T
        (hinv rfl))
      exact noStar_iff.mpr ⟨hA.1, hA.2⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at ht'
      rcases List.mem_append.mp ht' with ht' | ht'
      · cases hst : resStar E (tailExcl fr.kind) (tailExcl to.kind) fr.path T with
        | false =>
          simp only [hst, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at ht'
          subst ht'
          exact ⟨prependPath_wf _ _ hAw, fun h => nomatch h⟩
        | true =>
          simp only [hst, ↓reduceIte] at ht'
          by_cases hE2 : E.union ((tailExcl fr.kind).union (tailExcl to.kind)) = E
          · rw [if_pos hE2, List.mem_singleton] at ht'
            subst ht'
            exact ⟨prependPath_wf _ _ hAw, fun h => nomatch h⟩
          · rw [if_neg hE2] at ht'
            rcases List.mem_cons.mp ht' with rfl | ht'
            · exact ⟨prependPath_wf _ _ hAw, fun h => nomatch h⟩
            · rw [List.mem_singleton] at ht'
              subst ht'
              exact ⟨prependPath_wf _ _ rfl, fun h => nomatch h⟩
      · rw [List.mem_singleton] at ht'
        subst ht'
        exact ⟨prependPath_wf _ _ rfl, fun _ => prependPath_noStar _ _ rfl⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ht'
    exact nomatch ht'

/-- Every `*` fact of an edge tree list with the invariant is in the normal layer. -/
theorem star_normal (b : Base) (ts : List EdgeTree)
    (hinv : ∀ t, t ∈ ts → t.demand = true → t.tree.noStar = true) (a : AFact)
    (ha : a ∈ ts.flatMap (toAFacts b)) (hs : a.fact.kind.isStar = true) : a.demand = false := by
  obtain ⟨t, ht, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨x, hx, rfl⟩ := (mem_toAFacts b t a).mp ha
  cases hd : t.demand with
  | false => rfl
  | true =>
    have h := treeRF_noStar t.excl t.tree (hinv t ht hd) x hx
    have hs' : x.kind.isStar = true := hs
    rw [h] at hs'
    exact nomatch hs'

/-- MAIN 5 (fact form): every `*` result of `applyTreeE` is in the normal layer. -/
theorem applyTreeE_star_normal (b : Base) (t : EdgeTree) (hwf : t.tree.wf = true)
    (hinv : t.demand = true → t.tree.noStar = true) (fr to : PFact) (a : AFact)
    (ha : a ∈ (applyTreeE b t fr to).flatMap (toAFacts to.base))
    (hs : a.fact.kind.isStar = true) : a.demand = false :=
  star_normal to.base _ (fun t' ht' => (applyTreeE_inv b t hwf hinv fr to t' ht').2) a ha hs

/-- MAIN 6. The output trees are GROUPED: no two output trees have the same key
    (exclusion, layer). -/
theorem applyTreeE_grouped (b : Base) (t : EdgeTree) (fr to : PFact) :
    ((applyTreeE b t fr to).map (fun t' => (t'.excl, t'.demand))).Nodup := by
  rcases t with ⟨E, X, d, T⟩
  unfold applyTreeE
  dsimp only
  have hne : ∀ (E1 E2 : Excl), (E1, false) ≠ (E2, true) := fun _ _ h => nomatch congrArg Prod.snd h
  rcases Bool.eq_false_or_eq_true (Nat.beq b fr.base) with hb | hb
  · simp only [hb, ↓reduceIte]
    cases d with
    | true => exact List.nodup_cons.mpr ⟨fun h => (nomatch h), List.nodup_nil⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases resStar E (tailExcl fr.kind) (tailExcl to.kind) fr.path T with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.singleton_append, List.map_cons,
          List.map_nil]
        refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨fun h => (nomatch h), List.nodup_nil⟩⟩
        intro h
        rcases List.mem_singleton.mp h with h
        exact hne _ _ h
      | true =>
        simp only [↓reduceIte]
        by_cases hE2 : E.union ((tailExcl fr.kind).union (tailExcl to.kind)) = E
        · rw [if_pos hE2]
          simp only [List.singleton_append, List.map_cons, List.map_nil]
          refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨fun h => (nomatch h), List.nodup_nil⟩⟩
          intro h
          exact hne _ _ (List.mem_singleton.mp h)
        · rw [if_neg hE2]
          simp only [List.cons_append, List.map_cons]
          refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
            List.nodup_cons.mpr ⟨fun h => (nomatch h), List.nodup_nil⟩⟩⟩
          · intro h
            rcases List.mem_cons.mp h with h | h
            · exact hE2 (congrArg Prod.fst h).symm
            · exact hne _ _ (List.mem_singleton.mp h)
          · intro h
            exact hne _ _ (List.mem_singleton.mp h)
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, List.map_nil]
    exact List.nodup_nil

/-- MAIN 6b. `applyTreeE` keeps the mark exclusion: every output tree has the mark
    exclusion of the input tree. -/
theorem applyTreeE_mx (b : Base) (t : EdgeTree) (fr to : PFact) :
    ∀ t', t' ∈ applyTreeE b t fr to → t'.mx = t.mx := by
  intro t' ht'
  unfold applyTreeE at ht'
  dsimp only at ht'
  rcases Bool.eq_false_or_eq_true (Nat.beq b fr.base) with hb | hb
  · simp only [hb, ↓reduceIte] at ht'
    cases hd : t.demand with
    | true =>
      simp only [hd, ↓reduceIte, List.mem_singleton] at ht'
      subst ht'; rfl
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at ht'
      rcases List.mem_append.mp ht' with ht' | ht'
      · cases hst : resStar t.excl (tailExcl fr.kind) (tailExcl to.kind) fr.path t.tree with
        | false =>
          simp only [hst, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at ht'
          subst ht'; rfl
        | true =>
          simp only [hst, ↓reduceIte] at ht'
          by_cases hE2 : t.excl.union ((tailExcl fr.kind).union (tailExcl to.kind)) = t.excl
          · rw [if_pos hE2, List.mem_singleton] at ht'
            subst ht'; rfl
          · rw [if_neg hE2] at ht'
            rcases List.mem_cons.mp ht' with rfl | ht'
            · rfl
            · rw [List.mem_singleton] at ht'
              subst ht'; rfl
      · rw [List.mem_singleton] at ht'
        subst ht'; rfl
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at ht'
    exact nomatch ht'

/-- MAIN 6c. The output trees are grouped by the whole key (exclusion, mark
    exclusion, layer). -/
theorem applyTreeE_grouped_key (b : Base) (t : EdgeTree) (fr to : PFact) :
    ((applyTreeE b t fr to).map (fun t' => (t'.excl, t'.mx, t'.demand))).Nodup := by
  have h : List.Pairwise (fun u v : Excl × Bool => u ≠ v)
      (((applyTreeE b t fr to).map (fun t' => (t'.excl, t'.mx, t'.demand))).map
        (fun k : Excl × List Mark × Bool => (k.1, k.2.2))) := by
    rw [List.map_map]
    exact applyTreeE_grouped b t fr to
  exact List.Pairwise.of_map (R := fun u v => u ≠ v) (S := fun u v => u ≠ v) _
    (fun _ _ hne heq => hne (by rw [heq])) h

/-! ## 8. Build a tree from a list -/

def fromList (fs : List PFact) : Tree := fs.foldr Tree.insert emptyTree

theorem fromList_wf (fs : List PFact) : (fromList fs).wf = true := by
  induction fs with
  | nil => rfl
  | cons f fs ih => exact insert_wf f _ ih

theorem fromList_memEq (E : Excl) (fs : List PFact)
    (hf : ∀ f, f ∈ fs → fitsB E f.kind f.mark = true) :
    MemEq (treeRF E (fromList fs)) (fs.map ofP) := by
  induction fs with
  | nil => exact MemEq.refl _
  | cons f fs ih =>
    have ih' := ih (fun g hg => hf g (List.mem_cons_of_mem _ hg))
    refine MemEq.trans (insert_memEq (hf f (List.mem_cons_self ..)) _) ?_
    refine MemEq.trans (MemEq.append ih' (MemEq.refl _)) ?_
    exact MemEq.append_comm _ _

theorem fromList_stripF (fs : List PFact) : fromList fs = fromList (fs.map stripF) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    show insert f (fromList fs) = insert (stripF f) (fromList (fs.map stripF))
    rw [← ih, insert_stripF]

/-- The edge tree built from a list of facts that fit `E` and `X`, on base `b`,
    holds exactly these facts in the layer `d`. (Version 5: the key has the mark
    exclusion `X`, and the facts fit it, `fitsX`.) -/
theorem fromList_mem (b : Base) (E : Excl) (X : List Mark) (d : Bool) (fs : List PFact)
    (hb : ∀ f, f ∈ fs → f.base = b) (hf : ∀ f, f ∈ fs → fitsX E X f.kind f.mark = true)
    (a : AFact) : a ∈ toAFacts b ⟨E, X, d, fromList fs⟩ ↔ ∃ f, f ∈ fs ∧ a = ⟨f, d⟩ := by
  rw [mem_toAFacts]
  show (∃ x, x ∈ treeRF E (fromList fs) ∧ a = ⟨(markX X x).toP b, d⟩) ↔ _
  rw [fromList_stripF]
  have h := fromList_memEq E (fs.map stripF) (fun g hg => by
    obtain ⟨f, hfm, rfl⟩ := List.mem_map.mp hg
    exact (fitsX_parts (hf f hfm)).1)
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ((h x).mp hx)
    obtain ⟨f, hfm, rfl⟩ := List.mem_map.mp hg
    exact ⟨f, hfm, by rw [markX_ofP_stripF (fitsX_parts (hf f hfm)).2, toP_ofP (hb f hfm)]⟩
  · rintro ⟨f, hfm, rfl⟩
    exact ⟨ofP (stripF f), (h _).mpr (List.mem_map.mpr ⟨stripF f, List.mem_map.mpr ⟨f, hfm, rfl⟩, rfl⟩),
      by rw [markX_ofP_stripF (fitsX_parts (hf f hfm)).2, toP_ofP (hb f hfm)]⟩

/-! ## 9. Complexity -/

/-- The number of child nodes. -/
def trieSize : Trie → Nat
  | .nil => 0
  | .cons _ _ bl nx => 1 + trieSize bl + trieSize nx

/-- The number of nodes (the root counts). -/
def size (t : Tree) : Nat := 1 + trieSize t.kids

/-- The list storage: the total number of accessors in the paths. -/
def pathSum : List PFact → Nat
  | []      => 0
  | f :: fs => f.path.length + pathSum fs

theorem insK_size {a : Acc} {G : Tree → Tree} {n : Nat} (hG : ∀ s, size (G s) ≤ size s + n)
    (k : Trie) : trieSize (insK a G k) ≤ trieSize k + n + 1 := by
  induction k with
  | nil =>
    have h1 : 1 + trieSize (G emptyTree).kids ≤ 1 + 0 + n := hG emptyTree
    show 1 + trieSize (G emptyTree).kids + 0 ≤ 0 + n + 1
    omega
  | cons c h bl nx _ ihn =>
    rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
    · simp only [insK, hac, ↓reduceIte]
      have h1 : 1 + trieSize (G ⟨h, bl⟩).kids ≤ 1 + trieSize bl + n := hG ⟨h, bl⟩
      show 1 + trieSize (G ⟨h, bl⟩).kids + trieSize nx ≤ 1 + trieSize bl + trieSize nx + n + 1
      omega
    · simp only [insK, hac, Bool.false_eq_true, ↓reduceIte]
      show 1 + trieSize bl + trieSize (insK a G nx) ≤ 1 + trieSize bl + trieSize nx + n + 1
      omega

theorem insK_size_found {a : Acc} {G : Tree → Tree} {n : Nat} {s : Tree}
    (hG : size (G s) ≤ size s + n) (k : Trie) (hk : childAt a k = some s) :
    trieSize (insK a G k) ≤ trieSize k + n := by
  induction k with
  | nil => exact nomatch hk
  | cons c h bl nx _ ihn =>
    rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
    · simp only [childAt, hac, ↓reduceIte] at hk
      cases hk
      simp only [insK, hac, ↓reduceIte]
      have h1 : 1 + trieSize (G ⟨h, bl⟩).kids ≤ 1 + trieSize bl + n := hG
      show 1 + trieSize (G ⟨h, bl⟩).kids + trieSize nx ≤ 1 + trieSize bl + trieSize nx + n
      omega
    · simp only [childAt, hac, Bool.false_eq_true, ↓reduceIte] at hk
      simp only [insK, hac, Bool.false_eq_true, ↓reduceIte]
      have h1 := ihn hk
      show 1 + trieSize bl + trieSize (insK a G nx) ≤ 1 + trieSize bl + trieSize nx + n
      omega

theorem atPath_size {g : Tree → Tree} (hg : ∀ s, size (g s) ≤ size s) (p : List Acc) (t : Tree) :
    size (atPath p g t) ≤ size t + p.length := by
  induction p generalizing t with
  | nil => exact hg t
  | cons a p ih =>
    have h1 := insK_size (a := a) (fun s => ih s) t.kids
    show 1 + trieSize (insK a (atPath p g) t.kids) ≤ 1 + trieSize t.kids + (p.length + 1)
    omega

/-- Insert makes at most `|f.path|` new nodes. -/
theorem insert_size (f : PFact) (t : Tree) : size (insert f t) ≤ size t + f.path.length :=
  atPath_size (g := fun s => ⟨s.root.add f.kind f.mark, s.kids⟩) (fun _ => Nat.le_refl _) f.path t

/-- COMPLEXITY 1. The trie of a list has at most `1 + Σ |f.path|` nodes. -/
theorem fromList_size (fs : List PFact) : size (fromList fs) ≤ 1 + pathSum fs := by
  induction fs with
  | nil => exact Nat.le_refl _
  | cons f fs ih =>
    have h1 := insert_size f (fromList fs)
    show size (insert f (fromList fs)) ≤ 1 + (f.path.length + pathSum fs)
    omega

/-- The path `P` exists in the tree. -/
def hasPath : List Acc → Tree → Bool
  | [],     _ => true
  | a :: p, t =>
    match childAt a t.kids with
    | none   => false
    | some s => hasPath p s

theorem childAt_insK_self (a : Acc) (G : Tree → Tree) (k : Trie) :
    childAt a (insK a G k) = some (G ((childAt a k).getD emptyTree)) := by
  induction k with
  | nil => simp only [insK, childAt, Nat.beq_refl, ↓reduceIte]; rfl
  | cons c h bl nx _ ihn =>
    rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
    · simp only [insK, childAt, hac, ↓reduceIte]; rfl
    · simp only [insK, childAt, hac, Bool.false_eq_true, ↓reduceIte]
      exact ihn

theorem hasPath_atPath (P q : List Acc) (g : Tree → Tree) (t : Tree) :
    hasPath P (atPath (P ++ q) g t) = true := by
  induction P generalizing t with
  | nil => rfl
  | cons a P ih =>
    show (match childAt a (insK a (atPath (P ++ q) g) t.kids) with
      | none => false
      | some s => hasPath P s) = true
    rw [childAt_insK_self]
    exact ih _

theorem atPath_size_has {g : Tree → Tree} (hg : ∀ s, size (g s) ≤ size s) (P q : List Acc)
    (t : Tree) (ht : hasPath P t = true) : size (atPath (P ++ q) g t) ≤ size t + q.length := by
  induction P generalizing t with
  | nil => exact atPath_size hg q t
  | cons a P ih =>
    cases hc : childAt a t.kids with
    | none =>
      have ht' : (match childAt a t.kids with
        | none => false
        | some s => hasPath P s) = true := ht
      rw [hc] at ht'
      exact nomatch ht'
    | some s =>
      have ht' : (match childAt a t.kids with
        | none => false
        | some s => hasPath P s) = true := ht
      rw [hc] at ht'
      have h1 := insK_size_found (G := atPath (P ++ q) g) (ih s ht') t.kids hc
      show 1 + trieSize (insK a (atPath (P ++ q) g) t.kids) ≤ 1 + trieSize t.kids + q.length
      omega

/-- `k` paths that share the prefix `P` and then differ in one accessor. -/
def fan (b : Base) (P : List Acc) (k : Kind) (m : MarkA) (as : List Acc) : List PFact :=
  as.map (fun a => ⟨b, P ++ [a], k, m⟩)

/-- COMPLEXITY 2a. List storage of the fan: a PRODUCT `k * (p + 1)`. -/
theorem fan_list (b : Base) (P : List Acc) (k : Kind) (m : MarkA) (as : List Acc) :
    pathSum (fan b P k m as) = as.length * (P.length + 1) := by
  induction as with
  | nil => simp only [fan, List.map_nil, pathSum, List.length_nil, Nat.zero_mul]
  | cons a as ih =>
    show (P ++ [a]).length + pathSum (fan b P k m as) = (as.length + 1) * (P.length + 1)
    rw [ih, List.length_append, Nat.succ_mul]
    show P.length + 1 + as.length * (P.length + 1) = as.length * (P.length + 1) + (P.length + 1)
    omega

theorem fan_tree_aux (b : Base) (P : List Acc) (k : Kind) (m : MarkA) (as : List Acc) :
    size (fromList (fan b P k m as)) ≤ P.length + as.length + 1 ∧
      (as = [] ∨ hasPath P (fromList (fan b P k m as)) = true) := by
  induction as with
  | nil => exact ⟨by show 1 ≤ P.length + 0 + 1; omega, Or.inl rfl⟩
  | cons a as ih =>
    have hg : ∀ s : Tree, size ((fun s : Tree => (⟨s.root.add k m, s.kids⟩ : Tree)) s) ≤ size s :=
      fun _ => Nat.le_refl _
    refine ⟨?_, Or.inr (hasPath_atPath P [a] _ _)⟩
    show size (atPath (P ++ [a]) (fun s => ⟨s.root.add k m, s.kids⟩) (fromList (fan b P k m as)))
      ≤ P.length + (as.length + 1) + 1
    rcases ih.2 with h | h
    · subst h
      have h1 := atPath_size hg (P ++ [a]) emptyTree
      rw [List.length_append] at h1
      exact Nat.le_trans h1 (by show 1 + (P.length + 1) ≤ _; omega)
    · have h1 := atPath_size_has hg P [a] _ h
      have h2 := ih.1
      show _ ≤ _
      exact Nat.le_trans h1 (by show size (fromList (fan b P k m as)) + 1 ≤ _; omega)

/-- COMPLEXITY 2b. Trie storage of the fan: a SUM `p + k + 1`. -/
theorem fan_tree (b : Base) (P : List Acc) (k : Kind) (m : MarkA) (as : List Acc) :
    size (fromList (fan b P k m as)) ≤ P.length + as.length + 1 :=
  (fan_tree_aux b P k m as).1

/-- COMPLEXITY 3a. Prepend shares the old tree: the only new node is the root. -/
theorem prepend_shares (a : Acc) (t : Tree) : (prepend a t).kids = .cons a t.root t.kids .nil := rfl

theorem prepend_size (a : Acc) (t : Tree) : size (prepend a t) = size t + 1 := by
  show 1 + (1 + trieSize t.kids + 0) = 1 + trieSize t.kids + 1
  omega

/-- COMPLEXITY 3b. In the list form, prepend rewrites every one of the `|fs|`
    facts, and the storage grows by `|fs|`. -/
theorem prependF_ne (a : Acc) (f : PFact) : prependF a f ≠ f := by
  intro h
  have h1 : (prependF a f).path.length = f.path.length := by rw [h]
  have h2 : (a :: f.path).length = f.path.length := h1
  rw [List.length_cons] at h2
  omega

theorem prepend_list_cost (a : Acc) (fs : List PFact) :
    (fs.map (prependF a)).length = fs.length ∧
      pathSum (fs.map (prependF a)) = pathSum fs + fs.length := by
  refine ⟨List.length_map .., ?_⟩
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    show (a :: f.path).length + pathSum (fs.map (prependF a)) = f.path.length + pathSum fs +
      (fs.length + 1)
    rw [ih, List.length_cons]
    omega

/-- The number of trie levels that `walk` visits. -/
def walkSteps : List Acc → Tree → Nat
  | [],     _ => 1
  | a :: q, t =>
    match childAt a t.kids with
    | none   => 1
    | some s => 1 + walkSteps q s

/-- COMPLEXITY 4a. The walk to `fr.path` visits at most `|fr.path| + 1` levels. -/
theorem walkSteps_le (q : List Acc) (t : Tree) : walkSteps q t ≤ q.length + 1 := by
  induction q generalizing t with
  | nil => exact Nat.le_refl _
  | cons a q ih =>
    cases hc : childAt a t.kids with
    | none => simp only [walkSteps, hc, List.length_cons]; omega
    | some s =>
      have h1 := ih s
      simp only [walkSteps, hc, List.length_cons]
      omega

/-- The number of sibling cells that `childAt` compares. -/
def scanCost (a : Acc) : Trie → Nat
  | .nil => 0
  | .cons c _ _ nx => 1 + (if Nat.beq a c then 0 else scanCost a nx)

/-- The number of accessor comparisons of the walk. -/
def walkCmp : List Acc → Tree → Nat
  | [],     _ => 0
  | a :: q, t =>
    scanCost a t.kids +
      (match childAt a t.kids with
       | none   => 0
       | some s => walkCmp q s)

theorem scanCost_le (a : Acc) (k : Trie) : scanCost a k ≤ trieSize k := by
  induction k with
  | nil => exact Nat.le_refl _
  | cons c h bl nx _ ihn =>
    rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
    · simp only [scanCost, trieSize, hac, ↓reduceIte]; omega
    · simp only [scanCost, trieSize, hac, Bool.false_eq_true, ↓reduceIte]; omega

theorem scanCost_found (a : Acc) (k : Trie) (s : Tree) (hk : childAt a k = some s) :
    scanCost a k + trieSize s.kids ≤ trieSize k := by
  induction k with
  | nil => exact nomatch hk
  | cons c h bl nx _ ihn =>
    rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
    · simp only [childAt, hac, ↓reduceIte] at hk
      cases hk
      simp only [scanCost, trieSize, hac, ↓reduceIte]
      show 1 + 0 + trieSize bl ≤ 1 + trieSize bl + trieSize nx
      omega
    · simp only [childAt, hac, Bool.false_eq_true, ↓reduceIte] at hk
      have h1 := ihn hk
      simp only [scanCost, trieSize, hac, Bool.false_eq_true, ↓reduceIte]
      omega

/-- COMPLEXITY 4b. The walk compares each trie cell at most once: its cost is
    bounded by the tree size, never by the number of path facts times the
    path length. -/
theorem walkCmp_le (q : List Acc) (t : Tree) : walkCmp q t ≤ trieSize t.kids := by
  induction q generalizing t with
  | nil => exact Nat.zero_le _
  | cons a q ih =>
    cases hc : childAt a t.kids with
    | none =>
      have h1 := scanCost_le a t.kids
      simp only [walkCmp, hc]
      omega
    | some s =>
      have h1 := scanCost_found a t.kids s hc
      have h2 := ih s
      simp only [walkCmp, hc]
      omega

/-- The list form with a step counter: one `applyEdge` call per path fact. -/
def applyListC (fr to : PFact) : List AFact → List AFact × Nat
  | []      => ([], 0)
  | c :: fs =>
    let r := applyListC fr to fs
    ((applyEdge c fr to).facts ++ r.1, 1 + r.2)

/-- The list form of the operation: apply the edge to every path fact. -/
def applyList (fs : List AFact) (fr to : PFact) : List AFact :=
  fs.flatMap (fun c => (applyEdge c fr to).facts)

/-- COMPLEXITY 4c. The list form scans all `|fs|` facts, and it computes `applyList`. -/
theorem applyListC_spec (fr to : PFact) (fs : List AFact) :
    (applyListC fr to fs).1 = applyList fs fr to ∧ (applyListC fr to fs).2 = fs.length := by
  induction fs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c fs ih =>
    refine ⟨?_, ?_⟩
    · show _ ++ (applyListC fr to fs).1 = applyList (c :: fs) fr to
      rw [ih.1]
      unfold applyList
      rw [List.flatMap_cons]
    · show 1 + (applyListC fr to fs).2 = fs.length + 1
      rw [ih.2]
      omega

/-- The tree form walks `fr.path` once per output layer; each walk visits at
    most `|fr.path| + 1` levels (`walkSteps_le`) and the walk of `applyTreeE`
    ends at `subtreeAt` (`walkG_fst`). -/
theorem applyTreeE_walk (q : List Acc) (t : Tree) : walkSteps q t ≤ q.length + 1 :=
  walkSteps_le q t


/-! ## 9. Examples (the test vectors of `ApSpec.Cases`) -/

namespace Ex

def f : Acc := 1
def g : Acc := 2
def h : Acc := 3
def x : Base := 10
def a : Base := 11
def b : Base := 12
def T : Mark := 5
def E1 : Excl := .set [h]

/-- The final facts on base `b` with the exclusion `E1`, normal layer. -/
def factsE1 : List PFact :=
  [ ⟨b, [f], .star E1, .star⟩,
    ⟨b, [], .star E1, .star⟩,
    ⟨b, [], .any, .star⟩,
    ⟨b, [], .exact, .star⟩,
    ⟨b, [h], .any, .conc T⟩,
    ⟨b, [f, g], .exact, .conc T⟩,
    ⟨b, [f, g], .star E1, .star⟩ ]

/-- One edge tree per (layer, exclusion): `E1`, `{f}`, and the demand layer. -/
def tE1 : EdgeTree := ⟨E1, [], false, fromList factsE1⟩
def tF : EdgeTree := ⟨.set [f], [], false, fromList [⟨b, [], .star (.set [f]), .star⟩]⟩
def tD : EdgeTree := ⟨Excl.empty, [], true, fromList [⟨b, [], .any, .conc T⟩, ⟨b, [f], .exact, .star⟩,
  ⟨b, [f, h], .any, .star⟩, ⟨b, [g], .any, .star⟩]⟩
def treesB : List EdgeTree := [tE1, tF, tD]

#eval tE1
#eval toAFacts b tE1
-- nodes: root, .f, .f.g, .h (4) against 6 stored accessors in the list
example : (size tE1.tree, pathSum factsE1) = (4, 6) := by decide
example : (tE1.tree.wf && tF.tree.wf && tD.tree.wf && tD.tree.noStar) = true := by decide

/-- `a = b.f` (the micro edges of `loadF`). -/
def loadEdges : List (PFact × PFact) :=
  [ (⟨b, [], .star (.set [f]), .star⟩, ⟨b, [], .star Excl.empty, .star⟩),
    (⟨b, [f], .star Excl.empty, .star⟩, ⟨b, [f], .star Excl.empty, .star⟩),
    (⟨b, [f], .star Excl.empty, .star⟩, ⟨a, [], .star Excl.empty, .star⟩) ]

/-- `a.f = b` (the micro edges of `storeF`). -/
def storeEdges : List (PFact × PFact) :=
  [ (⟨a, [], .star (.set [f]), .star⟩, ⟨a, [], .star Excl.empty, .star⟩),
    (⟨b, [], .star Excl.empty, .star⟩, ⟨b, [], .star Excl.empty, .star⟩),
    (⟨b, [], .star Excl.empty, .star⟩, ⟨a, [f], .star Excl.empty, .star⟩) ]

def sameSetA (l1 l2 : List AFact) : Bool :=
  l1.all (fun p => l2.contains p) && l2.all (fun p => l1.contains p)

-- tree form = list form on whole `AFact`s, for every tree and every micro edge
example : treesB.all (fun t => loadEdges.all (fun e =>
    sameSetA ((applyTreeE b t e.1 e.2).flatMap (toAFacts e.2.base))
      (applyList (toAFacts b t) e.1 e.2))) = true := by decide
example : treesB.all (fun t => storeEdges.all (fun e =>
    sameSetA ((applyTreeE b t e.1 e.2).flatMap (toAFacts e.2.base))
      (applyList (toAFacts b t) e.1 e.2))) = true := by decide

-- the load `a = b.f` on the `E1` tree
#eval applyTreeE b tE1 (⟨b, [f], .star Excl.empty, .star⟩) (⟨a, [], .star Excl.empty, .star⟩)

/-- A tree on base `a` for the strong update `a.f = b`. -/
def tA : EdgeTree := ⟨E1, [], false, fromList [⟨a, [], .star E1, .star⟩, ⟨a, [f], .star E1, .star⟩,
  ⟨a, [g], .exact, .conc T⟩]⟩

-- the strong update keeps `.g`, drops `.f`, and moves the root `*` leaf to a NEW
-- tree with the exclusion `E1 ∪ {f}`: one input tree gives several output trees
#eval applyTreeE a tA (⟨a, [], .star (.set [f]), .star⟩) (⟨a, [], .star Excl.empty, .star⟩)
example : (applyTreeE a tA (⟨a, [], .star (.set [f]), .star⟩)
    (⟨a, [], .star Excl.empty, .star⟩)).map (fun t => (t.excl, t.demand))
    = [(E1, false), (E1.union ((Excl.set [f]).union Excl.empty), false), (Excl.empty, true)] := by
  decide
example : sameSetA ((applyTreeE a tA (⟨a, [], .star (.set [f]), .star⟩)
    (⟨a, [], .star Excl.empty, .star⟩)).flatMap (toAFacts a))
    (applyList (toAFacts a tA) (⟨a, [], .star (.set [f]), .star⟩)
      (⟨a, [], .star Excl.empty, .star⟩)) = true := by decide

/-! ### Merge rules and the forbidden union of exclusions -/

def t1 : EdgeTree := ⟨Excl.empty, [], false, fromList [⟨b, [], .star Excl.empty, .star⟩]⟩
def t2 : EdgeTree := ⟨.set [h], [], false, fromList [⟨b, [f], .star (.set [h]), .star⟩]⟩
def i0 : PFact := ⟨b, [], .star Excl.empty, .star⟩
def l0 : Loc := ⟨b, [h], 0⟩

-- rule 1 on two trees with the same key: the union of the facts
example : sameSetA (toAFacts b (t1.merge1 ⟨Excl.empty, [], false, fromList [⟨b, [g], .exact, .star⟩]⟩))
    (toAFacts b t1 ++ [⟨⟨b, [g], .exact, .star⟩, false⟩]) = true := by decide

-- rule 2 on the same tree: `{h} ∩ {f} = {}`; the continuation `.h` comes back
def tSameH : EdgeTree := ⟨.set [h], [], false, fromList [⟨b, [], .star (.set [h]), .star⟩]⟩
def tSameF : EdgeTree := ⟨.set [f], [], false, fromList [⟨b, [], .star (.set [f]), .star⟩]⟩
example : (denAB i0 (toAFacts b (tSameH.merge2 tSameF)) false l0 l0,
    denAB i0 (toAFacts b tSameH ++ toAFacts b tSameF) false l0 l0) = (true, true) := by decide

/-- FORBIDDEN: a union of exclusions across two DIFFERENT trees. -/
def tUnion : EdgeTree := ⟨t1.excl.union t2.excl, [], false, merge t1.tree t2.tree⟩

-- it LOSES a pair: (b.h ↦ b.h) is a pair of `t1`, not of the merged tree
example : denA i0 (toAFacts b t1 ++ toAFacts b t2) false l0 l0 ∧
    ¬ denA i0 (toAFacts b tUnion) false l0 l0 := by
  rw [denA_iff_denAB, denA_iff_denAB]
  decide

/-- An intersection across two different trees is not exact either: it ADDS a pair. -/
def tInter : EdgeTree := ⟨t1.excl.inter t2.excl, [], false, merge t1.tree t2.tree⟩
def l1' : Loc := ⟨b, [f, h], 0⟩

example : denA i0 (toAFacts b tInter) false l0 l1' ∧
    ¬ denA i0 (toAFacts b t1 ++ toAFacts b t2) false l0 l1' := by
  rw [denA_iff_denAB, denA_iff_denAB]
  decide

/-! ### Trees with a mark exclusion (version 5, cleaners) -/

def U : Mark := 6

/-- A tree behind a cleaner of the mark `T`: its abstract mark is `*∖{T}`. -/
def tX : EdgeTree := ⟨E1, [T], false, fromList [⟨b, [f], .star E1, .starEx [T]⟩,
  ⟨b, [], .star E1, .starEx [T]⟩, ⟨b, [], .any, .starEx [T]⟩, ⟨b, [h], .any, .conc U⟩,
  ⟨b, [f, g], .exact, .starEx [T]⟩]⟩
def tXD : EdgeTree := ⟨Excl.empty, [T], true, fromList [⟨b, [f], .exact, .starEx [T]⟩,
  ⟨b, [g], .any, .starEx [T]⟩, ⟨b, [], .any, .conc T⟩]⟩

-- the trie stores the flag `*`; `toAFacts` reads it as `*∖{T}`
#eval toAFacts b tX
example : sameSetA (toAFacts b tXD) [⟨⟨b, [f], .exact, .starEx [T]⟩, true⟩,
    ⟨⟨b, [g], .any, .starEx [T]⟩, true⟩, ⟨⟨b, [], .any, .conc T⟩, true⟩] = true := by decide

-- tree form = list form on whole `AFact`s, for trees with a mark exclusion
example : [tX, tXD].all (fun t => loadEdges.all (fun e =>
    sameSetA ((applyTreeE b t e.1 e.2).flatMap (toAFacts e.2.base))
      (applyList (toAFacts b t) e.1 e.2))) = true := by decide
example : [tX, tXD].all (fun t => storeEdges.all (fun e =>
    sameSetA ((applyTreeE b t e.1 e.2).flatMap (toAFacts e.2.base))
      (applyList (toAFacts b t) e.1 e.2))) = true := by decide

/-- The strong update `a.f = b` on a tree with the mark exclusion `{T}`. -/
def tAX : EdgeTree := ⟨E1, [T], false, fromList [⟨a, [], .star E1, .starEx [T]⟩,
  ⟨a, [f], .star E1, .starEx [T]⟩, ⟨a, [g], .exact, .conc T⟩]⟩

-- every output tree keeps the mark exclusion `{T}`
example : (applyTreeE a tAX (⟨a, [], .star (.set [f]), .star⟩)
    (⟨a, [], .star Excl.empty, .star⟩)).map (fun t => (t.excl, t.mx, t.demand))
    = [(E1, [T], false), (E1.union ((Excl.set [f]).union Excl.empty), [T], false),
       (Excl.empty, [T], true)] := by
  decide
example : sameSetA ((applyTreeE a tAX (⟨a, [], .star (.set [f]), .star⟩)
    (⟨a, [], .star Excl.empty, .star⟩)).flatMap (toAFacts a))
    (applyList (toAFacts a tAX) (⟨a, [], .star (.set [f]), .star⟩)
      (⟨a, [], .star Excl.empty, .star⟩)) = true := by decide

/-! ### Merge rule 2 for marks and the forbidden union of mark exclusions -/

def lT : Loc := ⟨b, [h], T⟩
def lU : Loc := ⟨b, [h], U⟩
def tMT : EdgeTree := ⟨Excl.empty, [T], false, fromList [⟨b, [], .star Excl.empty, .starEx [T]⟩]⟩
def tMU : EdgeTree := ⟨Excl.empty, [U], false, fromList [⟨b, [], .star Excl.empty, .starEx [U]⟩]⟩

-- rule 2 for marks: `{T} ∩ {U} = {}`; the mark `T` comes back (from `tMU`), and the
-- mark `U` too (from `tMT`)
example : (denAB i0 (toAFacts b (tMT.merge2m tMU)) false lT lT,
    denAB i0 (toAFacts b tMT ++ toAFacts b tMU) false lT lT,
    denAB i0 (toAFacts b tMT) false lT lT,
    denAB i0 (toAFacts b (tMT.merge2m tMU)) false lU lU,
    denAB i0 (toAFacts b tMT ++ toAFacts b tMU) false lU lU) = (true, true, false, true, true) := by
  decide

/-- FORBIDDEN: a union of mark exclusions. -/
def tUnionM : EdgeTree := ⟨Excl.empty, tMT.mx ++ tMU.mx, false, tMT.tree⟩

-- it LOSES a pair: (b.h ↦ b.h) with the mark `T` is a pair of `tMU`, not of the merged tree
example : denA i0 (toAFacts b tMT ++ toAFacts b tMU) false lT lT ∧
    ¬ denA i0 (toAFacts b tUnionM) false lT lT := by
  rw [denA_iff_denAB, denA_iff_denAB]
  decide

/-! ### Cost -/

-- the fan: k = 4 paths with a shared prefix of length p = 3
example : pathSum (fan b [1, 2, 3] .exact .star [4, 5, 6, 7]) = 16 := by decide
example : size (fromList (fan b [1, 2, 3] .exact .star [4, 5, 6, 7])) = 8 := by decide
-- the walk to .f.g visits 3 levels and compares 2 cells
example : (walkSteps [f, g] tE1.tree, walkCmp [f, g] tE1.tree) = (3, 2) := by decide

end Ex

/-! ## 10. Axiom audit -/

#print axioms admits_inter
#print axioms den_iff_denB
#print axioms denA_iff_denAB
#print axioms insert_mem
#print axioms rule1_mem
#print axioms rule1_den
#print axioms rule2_eqv
#print axioms rule2_den
#print axioms rule2_eqvX
#print axioms rule2_mark_eqv
#print axioms rule2_mark
#print axioms insert_stripF
#print axioms stepR_markX
#print axioms applyEdge_eqX
#print axioms toAFacts_prepend
#print axioms applyEdge_eq2
#print axioms resL_spec
#print axioms applyTreeE_mem
#print axioms applyTreeE_den
#print axioms applyTreeE_inv
#print axioms applyTreeE_star_normal
#print axioms applyTreeE_grouped
#print axioms applyTreeE_mx
#print axioms applyTreeE_grouped_key
#print axioms walkG_fst
#print axioms insert_wf
#print axioms merge_wf
#print axioms fromList_mem
#print axioms fromList_size
#print axioms fan_list
#print axioms fan_tree
#print axioms prepend_size
#print axioms prepend_list_cost
#print axioms prependF_ne
#print axioms walkSteps_le
#print axioms walkCmp_le
#print axioms applyListC_spec

end ApSpec.Tree
