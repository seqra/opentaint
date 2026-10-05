/-
  ApSpec.Store — the stores of the analysis: the concept and the index.

  The CONCEPT of each store is a list of records and a filter query.
  The OPTIMIZATION is an index: a path trie (`PathMap`) or an exact-key map
  (`KMap`). This file proves that the index query and the list filter give the
  same records, and it compares the cost of the two queries.

  Parts:
    1. `PathMap`: a generic path trie, its laws, and its cost.
    2. The summary store: the indexes `byEntry` and `byExit`.
    3. The split of the summary store by provenance (complete / demand).
    4. The demand store.
    5. The exact-key maps: the request store and the subscription store.
    6. Examples (`#eval`).

  All proofs are constructive. Each main theorem has a `#print axioms` audit.

  Design notes (each has a theorem or a checked example):
    N1. The forward query `applicable` needs only `lookupPrefixes`. A record
        from the extension half passes the filter only at the exact key, and
        that record is also in the prefix half (`extension_half_redundant`).
        `lookupPrefixes ++ lookupExtensions` returns the exact-key records twice.
    N2. A key without the base mixes the bases. A root fact (`path = []`) then
        gets every record of the method. The key `base :: path` keeps the
        completeness (`applicable_mem_candidatesB`, `demand_completeB`).
    N3. The standing request match (spec §8.3) is an overlap query, not an
        exact-key query. The exact-key request store cannot answer it; a path
        index on `method :: base :: path` answers it (`standing_complete`).
    N4. The cost bound `|q| + 1` counts key-path nodes. In a left-child /
        right-sibling trie the sibling scan adds a factor `fan`
        (`prefCells_le`); the bound needs a hashed child map.
-/
import ApSpec.Basic

namespace ApSpec.Store
open ApSpec

/-! ## 0. Path helpers -/

theorem dropPrefix_some : ∀ {p q r : List Acc}, dropPrefix p q = some r → q = p ++ r
  | [], q, r, h => by
      have h' : q = r := Option.some.inj h
      rw [h', List.nil_append]
  | _ :: _, [], r, h => by cases h
  | a :: p, b :: q, r, h => by
      unfold dropPrefix at h
      cases hab : Nat.beq a b
      · rw [hab] at h; cases h
      · rw [hab] at h
        rw [dropPrefix_some h, Nat.eq_of_beq_eq_true hab, List.cons_append]

theorem dropPrefix_append : ∀ (p r : List Acc), dropPrefix p (p ++ r) = some r
  | [], _ => rfl
  | a :: p, r => by
      show (if Nat.beq a a = true then dropPrefix p (p ++ r) else none) = some r
      rw [Nat.beq_refl a]
      exact dropPrefix_append p r

/-- The prefix test of `Basic` (`dropPrefix`) decides the prefix relation. -/
theorem dropPrefix_isSome_iff {p q : List Acc} :
    (dropPrefix p q).isSome = true ↔ ∃ r, q = p ++ r := by
  constructor
  · intro h
    cases hd : dropPrefix p q with
    | none => rw [hd] at h; cases h
    | some r => exact ⟨r, dropPrefix_some hd⟩
  · intro ⟨r, e⟩
    rw [e, dropPrefix_append]
    rfl

#print axioms dropPrefix_isSome_iff

theorem pre_cons_cons {a b : Acc} {p q : List Acc} :
    (∃ r, b :: q = (a :: p) ++ r) ↔ a = b ∧ ∃ r, q = p ++ r := by
  constructor
  · intro ⟨r, h⟩
    rw [List.cons_append] at h
    injection h with h1 h2
    exact ⟨h1.symm, r, h2⟩
  · intro ⟨hab, r, h⟩
    exact ⟨r, by rw [h, hab, List.cons_append]⟩

theorem pre_nil_cons {a : Acc} {p : List Acc} :
    (∃ r, ([] : List Acc) = (a :: p) ++ r) ↔ False := by
  constructor
  · intro ⟨r, h⟩
    rw [List.cons_append] at h
    cases h
  · intro h; exact h.elim

theorem swap3 {a b : Acc} {P Q : Prop} : (a = b ∧ P ∧ Q) ↔ ((b = a ∧ P) ∧ Q) :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1.symm, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1.symm, h2, h3⟩⟩

theorem pre_nil {q : List Acc} : (∃ r, q = [] ++ r) ↔ True :=
  ⟨fun _ => trivial, fun _ => ⟨q, (List.nil_append q).symm⟩⟩

/-! ## 1. The path trie `PathMap`

The trie uses the left-child / right-sibling encoding. A `Forest` is a list of
sibling nodes. Each node has an accessor `a`, the values `vals` at its key, the
forest `kids` of its children, and the forest `rest` of its next siblings.
This encoding is not nested, so the structural recursion is simple. -/

inductive Forest (β : Type) where
  | nil
  | cons (a : Acc) (vals : List β) (kids : Forest β) (rest : Forest β)
deriving Repr

/-- A path trie. `vals` are the values at the empty key `[]`. -/
structure PathMap (β : Type) where
  vals : List β
  kids : Forest β
deriving Repr

namespace Forest
variable {β : Type}

/-- The forest that holds only the value `v` at the key `a :: p`. -/
def single (a : Acc) : List Acc → β → Forest β
  | [],     v => .cons a [v] .nil .nil
  | c :: p, v => .cons a [] (single c p v) .nil

/-- Insert the value `v` at the key `a :: p`. -/
def ins : Forest β → Acc → List Acc → β → Forest β
  | .nil, a, p, v => single a p v
  | .cons b vs k r, a, p, v =>
    if a = b then
      match p with
      | []      => .cons b (v :: vs) k r
      | c :: p' => .cons b vs (k.ins c p' v) r
    else .cons b vs k (r.ins a p v)

/-- The values at the key `a :: q`. -/
def exact : Forest β → Acc → List Acc → List β
  | .nil, _, _ => []
  | .cons b vs k r, a, q =>
    if a = b then
      match q with
      | []      => vs
      | c :: q' => k.exact c q'
    else r.exact a q

/-- The values at every non-empty key that is a prefix of `a :: q`. -/
def prefixes : Forest β → Acc → List Acc → List β
  | .nil, _, _ => []
  | .cons b vs k r, a, q =>
    if a = b then
      match q with
      | []      => vs
      | c :: q' => vs ++ k.prefixes c q'
    else r.prefixes a q

/-- All the values of the forest. -/
def all : Forest β → List β
  | .nil => []
  | .cons _ vs k r => vs ++ k.all ++ r.all

/-- The values at every key that has `a :: q` as a prefix. -/
def extensions : Forest β → Acc → List Acc → List β
  | .nil, _, _ => []
  | .cons b vs k r, a, q =>
    if a = b then
      match q with
      | []      => vs ++ k.all
      | c :: q' => k.extensions c q'
    else r.extensions a q

/-! ### 1.1 Laws of `ins` -/

theorem exact_single {x v : β} : ∀ {p : List Acc} {a b : Acc} {q : List Acc},
    x ∈ (single a p v).exact b q ↔ a = b ∧ p = q ∧ x = v
  | [], a, b, q => by
    by_cases h : b = a
    · subst h; cases q <;> simp [single, exact]
    · simp [single, exact, h, Ne.symm h]
  | c :: p, a, b, q => by
    by_cases h : b = a
    · subst h
      cases q with
      | nil => simp [single, exact]
      | cons d q' =>
        simp only [single, exact, ↓reduceIte]
        rw [exact_single]; simp [and_assoc]
    · simp [single, exact, h, Ne.symm h]

theorem exact_ins {x v : β} : ∀ {f : Forest β} {a b : Acc} {p q : List Acc},
    x ∈ (f.ins a p v).exact b q ↔ (a = b ∧ p = q ∧ x = v) ∨ x ∈ f.exact b q
  | .nil, a, b, p, q => by
    simp only [ins, exact_single]; simp [exact]
  | .cons c vs k r, a, b, p, q => by
    by_cases hac : a = c
    · subst hac
      cases p with
      | nil =>
        by_cases hba : b = a
        · subst hba
          cases q with
          | nil => simp [ins, exact]
          | cons d q' => simp [ins, exact]
        · simp [ins, exact, hba, Ne.symm hba]
      | cons e p' =>
        by_cases hba : b = a
        · subst hba
          cases q with
          | nil => simp [ins, exact]
          | cons d q' =>
            simp only [ins, exact, ↓reduceIte]
            rw [exact_ins]; simp [and_assoc]
        · simp [ins, exact, hba, Ne.symm hba]
    · by_cases hbc : b = c
      · subst hbc
        simp only [ins, exact, hac, ↓reduceIte]
        cases q <;> simp
      · simp only [ins, exact, hac, hbc, ↓reduceIte]
        exact exact_ins

theorem prefixes_single {x v : β} : ∀ {p : List Acc} {a b : Acc} {q : List Acc},
    x ∈ (single a p v).prefixes b q ↔ a = b ∧ (∃ r, q = p ++ r) ∧ x = v
  | [], a, b, q => by
    by_cases h : b = a
    · subst h; cases q <;> simp [single, prefixes]
    · simp [single, prefixes, h, Ne.symm h]
  | c :: p, a, b, q => by
    by_cases h : b = a
    · subst h
      cases q with
      | nil =>
        simp only [single, prefixes, ↓reduceIte, pre_nil_cons]; simp
      | cons d q' =>
        simp only [single, prefixes, ↓reduceIte]
        rw [List.nil_append, prefixes_single, pre_cons_cons]; simp [and_assoc]
    · simp [single, prefixes, h, Ne.symm h]

theorem prefixes_ins {x v : β} : ∀ {f : Forest β} {a b : Acc} {p q : List Acc},
    x ∈ (f.ins a p v).prefixes b q ↔
      (a = b ∧ (∃ r, q = p ++ r) ∧ x = v) ∨ x ∈ f.prefixes b q
  | .nil, a, b, p, q => by
    simp only [ins, prefixes_single]; simp [prefixes]
  | .cons c vs k r, a, b, p, q => by
    by_cases hac : a = c
    · subst hac
      cases p with
      | nil =>
        by_cases hba : b = a
        · subst hba
          cases q with
          | nil => simp [ins, prefixes]
          | cons d q' => simp [ins, prefixes]
        · simp [ins, prefixes, hba, Ne.symm hba]
      | cons e p' =>
        by_cases hba : b = a
        · subst hba
          cases q with
          | nil => simp only [ins, prefixes, ↓reduceIte, pre_nil_cons]; simp
          | cons d q' =>
            simp only [ins, prefixes, ↓reduceIte]
            rw [List.mem_append, List.mem_append, prefixes_ins, pre_cons_cons]
            simp only [true_and]
            constructor
            · intro h
              rcases h with h | h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inl ⟨⟨h.1, h.2.1⟩, h.2.2⟩
              · exact Or.inr (Or.inr h)
            · intro h
              rcases h with ⟨⟨h1, h2⟩, h3⟩ | h | h
              · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr (Or.inr h)
        · simp [ins, prefixes, hba, Ne.symm hba]
    · by_cases hbc : b = c
      · subst hbc
        simp only [ins, prefixes, hac, ↓reduceIte]
        cases q <;> simp
      · simp only [ins, prefixes, hac, hbc, ↓reduceIte]
        exact prefixes_ins

theorem all_single {x v : β} : ∀ {p : List Acc} {a : Acc}, x ∈ (single a p v).all ↔ x = v
  | [], a => by simp [single, all]
  | c :: p, a => by
    simp only [single, all, List.nil_append, List.append_nil]
    exact all_single

theorem all_ins {x v : β} : ∀ {f : Forest β} {a : Acc} {p : List Acc},
    x ∈ (f.ins a p v).all ↔ x = v ∨ x ∈ f.all
  | .nil, a, p => by simp only [ins, all_single]; simp [all]
  | .cons c vs k r, a, p => by
    by_cases hac : a = c
    · subst hac
      cases p with
      | nil => simp [ins, all]
      | cons e p' =>
        simp only [ins, all, ↓reduceIte, List.mem_append]
        rw [all_ins]
        constructor
        · intro h
          rcases h with (h | h | h) | h
          · exact Or.inr (Or.inl (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (Or.inl (Or.inr h))
          · exact Or.inr (Or.inr h)
        · intro h
          rcases h with h | (h | h) | h
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inr h))
          · exact Or.inr h
    · simp only [ins, all, hac, ↓reduceIte, List.mem_append]
      rw [all_ins]
      constructor
      · intro h
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · intro h
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem extensions_single {x v : β} : ∀ {p : List Acc} {a b : Acc} {q : List Acc},
    x ∈ (single a p v).extensions b q ↔ a = b ∧ (∃ r, p = q ++ r) ∧ x = v
  | [], a, b, q => by
    by_cases h : b = a
    · subst h
      cases q with
      | nil => simp [single, extensions, all]
      | cons d q' =>
        simp only [single, extensions, ↓reduceIte, pre_nil_cons]; simp
    · simp [single, extensions, h, Ne.symm h]
  | c :: p, a, b, q => by
    by_cases h : b = a
    · subst h
      cases q with
      | nil =>
        simp only [single, extensions, ↓reduceIte, List.nil_append, all_single]; simp
      | cons d q' =>
        simp only [single, extensions, ↓reduceIte]
        rw [extensions_single, pre_cons_cons]; simp only [true_and]; exact swap3
    · simp [single, extensions, h, Ne.symm h]

theorem extensions_ins {x v : β} : ∀ {f : Forest β} {a b : Acc} {p q : List Acc},
    x ∈ (f.ins a p v).extensions b q ↔
      (a = b ∧ (∃ r, p = q ++ r) ∧ x = v) ∨ x ∈ f.extensions b q
  | .nil, a, b, p, q => by
    simp only [ins, extensions_single]; simp [extensions]
  | .cons c vs k r, a, b, p, q => by
    by_cases hac : a = c
    · subst hac
      cases p with
      | nil =>
        by_cases hba : b = a
        · subst hba
          cases q with
          | nil => simp [ins, extensions]
          | cons d q' => simp only [ins, extensions, ↓reduceIte, pre_nil_cons]; simp
        · simp [ins, extensions, hba, Ne.symm hba]
      | cons e p' =>
        by_cases hba : b = a
        · subst hba
          cases q with
          | nil =>
            simp only [ins, extensions, ↓reduceIte, List.mem_append]
            rw [all_ins]
            simp only [true_and, List.nil_append]
            constructor
            · intro h
              rcases h with h | h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inl ⟨⟨e :: p', rfl⟩, h⟩
              · exact Or.inr (Or.inr h)
            · intro h
              rcases h with ⟨_, h⟩ | h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inl h
              · exact Or.inr (Or.inr h)
          | cons d q' =>
            simp only [ins, extensions, ↓reduceIte]
            rw [extensions_ins, pre_cons_cons]; simp only [true_and]; rw [swap3]
        · simp [ins, extensions, hba, Ne.symm hba]
    · by_cases hbc : b = c
      · subst hbc
        simp only [ins, extensions, hac, ↓reduceIte]
        cases q <;> simp
      · simp only [ins, extensions, hac, hbc, ↓reduceIte]
        exact extensions_ins

end Forest

namespace PathMap
variable {β : Type}

def empty : PathMap β := ⟨[], .nil⟩

def insert (m : PathMap β) : List Acc → β → PathMap β
  | [],     v => ⟨v :: m.vals, m.kids⟩
  | a :: p, v => ⟨m.vals, m.kids.ins a p v⟩

def lookupExact (m : PathMap β) : List Acc → List β
  | []     => m.vals
  | a :: q => m.kids.exact a q

/-- The values at every key that is a prefix of `q`. -/
def lookupPrefixes (m : PathMap β) : List Acc → List β
  | []     => m.vals
  | a :: q => m.vals ++ m.kids.prefixes a q

def allVals (m : PathMap β) : List β := m.vals ++ m.kids.all

/-- The values at every key that has `q` as a prefix. -/
def lookupExtensions (m : PathMap β) : List Acc → List β
  | []     => m.allVals
  | a :: q => m.kids.extensions a q

/-- The index of a record list. -/
def fromList : List (List Acc × β) → PathMap β
  | []           => empty
  | (k, v) :: es => (fromList es).insert k v

/-! ### 1.2 Laws of `insert` -/

theorem lookupExact_insert {m : PathMap β} {k q : List Acc} {v x : β} :
    x ∈ (m.insert k v).lookupExact q ↔ (k = q ∧ x = v) ∨ x ∈ m.lookupExact q := by
  cases k with
  | nil => cases q <;> simp [insert, lookupExact]
  | cons a p =>
    cases q with
    | nil => simp [insert, lookupExact]
    | cons b q' =>
      simp only [insert, lookupExact]
      rw [Forest.exact_ins]; simp [and_assoc]

theorem lookupPrefixes_insert {m : PathMap β} {k q : List Acc} {v x : β} :
    x ∈ (m.insert k v).lookupPrefixes q ↔
      ((∃ r, q = k ++ r) ∧ x = v) ∨ x ∈ m.lookupPrefixes q := by
  cases k with
  | nil =>
    cases q with
    | nil => simp [insert, lookupPrefixes]
    | cons b q' =>
      simp only [insert, lookupPrefixes, pre_nil, true_and, List.mem_append, List.mem_cons]
      constructor
      · intro h; rcases h with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · intro h; rcases h with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | cons a p =>
    cases q with
    | nil => simp only [insert, lookupPrefixes, pre_nil_cons]; simp
    | cons b q' =>
      simp only [insert, lookupPrefixes, List.mem_append]
      rw [Forest.prefixes_ins, pre_cons_cons]
      constructor
      · intro h; rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl ⟨⟨h.1, h.2.1⟩, h.2.2⟩
        · exact Or.inr (Or.inr h)
      · intro h; rcases h with ⟨⟨h1, h2⟩, h3⟩ | h | h
        · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem lookupExtensions_insert {m : PathMap β} {k q : List Acc} {v x : β} :
    x ∈ (m.insert k v).lookupExtensions q ↔
      ((∃ r, k = q ++ r) ∧ x = v) ∨ x ∈ m.lookupExtensions q := by
  cases q with
  | nil =>
    cases k with
    | nil => simp [insert, lookupExtensions, allVals]
    | cons a p =>
      simp only [insert, lookupExtensions, allVals, pre_nil, true_and, List.mem_append]
      rw [Forest.all_ins]
      constructor
      · intro h; rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · intro h; rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
  | cons b q' =>
    cases k with
    | nil => simp only [insert, lookupExtensions, pre_nil_cons]; simp
    | cons a p =>
      simp only [insert, lookupExtensions]
      rw [Forest.extensions_ins, pre_cons_cons, swap3]

/-! ### 1.3 The index gives the records of the list concept -/

/-- The list concept of the exact query. -/
def listExact (es : List (List Acc × β)) (q : List Acc) : List β :=
  (es.filter (fun e => decide (e.1 = q))).map (·.2)

/-- The list concept of the prefix query (the test is `dropPrefix` of `Basic`). -/
def listPrefixes (es : List (List Acc × β)) (q : List Acc) : List β :=
  (es.filter (fun e => (dropPrefix e.1 q).isSome)).map (·.2)

/-- The list concept of the extension query. -/
def listExtensions (es : List (List Acc × β)) (q : List Acc) : List β :=
  (es.filter (fun e => (dropPrefix q e.1).isSome)).map (·.2)

theorem mem_lookupExact_fromList {es : List (List Acc × β)} {q : List Acc} {x : β} :
    x ∈ (fromList es).lookupExact q ↔ (q, x) ∈ es := by
  induction es with
  | nil => cases q <;> simp [fromList, empty, lookupExact, Forest.exact]
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    simp only [fromList]
    rw [lookupExact_insert, ih]
    simp [eq_comm]

#print axioms mem_lookupExact_fromList

theorem mem_lookupPrefixes_fromList {es : List (List Acc × β)} {q : List Acc} {x : β} :
    x ∈ (fromList es).lookupPrefixes q ↔ ∃ k, (k, x) ∈ es ∧ ∃ r, q = k ++ r := by
  induction es with
  | nil => cases q <;> simp [fromList, empty, lookupPrefixes, Forest.prefixes]
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    simp only [fromList]
    rw [lookupPrefixes_insert, ih]
    constructor
    · intro h; rcases h with ⟨h1, h2⟩ | ⟨k', h1, h2⟩
      · exact ⟨k, by rw [h2]; exact List.mem_cons_self, h1⟩
      · exact ⟨k', List.mem_cons_of_mem _ h1, h2⟩
    · intro ⟨k', h1, h2⟩
      rcases List.mem_cons.mp h1 with h | h
      · injection h with hk hx
        subst hk; subst hx
        exact Or.inl ⟨h2, rfl⟩
      · exact Or.inr ⟨k', h, h2⟩

#print axioms mem_lookupPrefixes_fromList

theorem mem_lookupExtensions_fromList {es : List (List Acc × β)} {q : List Acc} {x : β} :
    x ∈ (fromList es).lookupExtensions q ↔ ∃ k, (k, x) ∈ es ∧ ∃ r, k = q ++ r := by
  induction es with
  | nil => cases q <;> simp [fromList, empty, lookupExtensions, allVals, Forest.extensions, Forest.all]
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    simp only [fromList]
    rw [lookupExtensions_insert, ih]
    constructor
    · intro h; rcases h with ⟨h1, h2⟩ | ⟨k', h1, h2⟩
      · exact ⟨k, by rw [h2]; exact List.mem_cons_self, h1⟩
      · exact ⟨k', List.mem_cons_of_mem _ h1, h2⟩
    · intro ⟨k', h1, h2⟩
      rcases List.mem_cons.mp h1 with h | h
      · injection h with hk hx
        subst hk; subst hx
        exact Or.inl ⟨h2, rfl⟩
      · exact Or.inr ⟨k', h, h2⟩

#print axioms mem_lookupExtensions_fromList

/-- The prefix query in the form of the brief: `dropPrefix k q ≠ none`. -/
theorem mem_lookupPrefixes_fromList' {es : List (List Acc × β)} {q : List Acc} {x : β} :
    x ∈ (fromList es).lookupPrefixes q ↔ ∃ k, (k, x) ∈ es ∧ dropPrefix k q ≠ none := by
  rw [mem_lookupPrefixes_fromList]
  constructor
  · intro ⟨k, h1, r, h2⟩
    refine ⟨k, h1, ?_⟩
    rw [h2, dropPrefix_append]; exact fun h => by cases h
  · intro ⟨k, h1, h2⟩
    cases hd : dropPrefix k q with
    | none => exact absurd hd h2
    | some r => exact ⟨k, h1, r, dropPrefix_some hd⟩

#print axioms mem_lookupPrefixes_fromList'

/-- Index = concept, exact query. -/
theorem lookupExact_equiv {es : List (List Acc × β)} {q : List Acc} {x : β} :
    x ∈ (fromList es).lookupExact q ↔ x ∈ listExact es q := by
  rw [mem_lookupExact_fromList]
  simp only [listExact, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h; exact ⟨(q, x), ⟨h, rfl⟩, rfl⟩
  · intro ⟨⟨k, y⟩, ⟨h1, h2⟩, h3⟩
    simp only at h2 h3
    rw [← h2, ← h3]; exact h1

#print axioms lookupExact_equiv

/-- Index = concept, prefix query. -/
theorem lookupPrefixes_equiv {es : List (List Acc × β)} {q : List Acc} {x : β} :
    x ∈ (fromList es).lookupPrefixes q ↔ x ∈ listPrefixes es q := by
  rw [mem_lookupPrefixes_fromList]
  simp only [listPrefixes, List.mem_map, List.mem_filter, dropPrefix_isSome_iff]
  constructor
  · intro ⟨k, h1, h2⟩; exact ⟨(k, x), ⟨h1, h2⟩, rfl⟩
  · intro ⟨⟨k, y⟩, ⟨h1, h2⟩, h3⟩
    simp only at h2 h3
    subst h3; exact ⟨k, h1, h2⟩

#print axioms lookupPrefixes_equiv

/-- Index = concept, extension query. -/
theorem lookupExtensions_equiv {es : List (List Acc × β)} {q : List Acc} {x : β} :
    x ∈ (fromList es).lookupExtensions q ↔ x ∈ listExtensions es q := by
  rw [mem_lookupExtensions_fromList]
  simp only [listExtensions, List.mem_map, List.mem_filter, dropPrefix_isSome_iff]
  constructor
  · intro ⟨k, h1, h2⟩; exact ⟨(k, x), ⟨h1, h2⟩, rfl⟩
  · intro ⟨⟨k, y⟩, ⟨h1, h2⟩, h3⟩
    simp only at h2 h3
    subst h3; exact ⟨k, h1, h2⟩

#print axioms lookupExtensions_equiv

end PathMap

/-! ### 1.4 Cost

Two counters for the prefix query:
  * `prefHits` counts the trie nodes on the key path (the nodes whose key is a
    prefix of the query, plus the root). This is the cost when each node finds
    its child in one step (a hashed child map).
  * `prefCells` counts every forest cell that this encoding inspects (each
    sibling test is one cell).
The list concept tests every record: `|es|` tests. -/

namespace Forest
variable {β : Type}

def prefHits : Forest β → Acc → List Acc → Nat
  | .nil, _, _ => 0
  | .cons b _ k r, a, q =>
    if a = b then
      match q with
      | []      => 1
      | c :: q' => 1 + k.prefHits c q'
    else r.prefHits a q

def prefCells : Forest β → Acc → List Acc → Nat
  | .nil, _, _ => 0
  | .cons b _ k r, a, q =>
    if a = b then
      match q with
      | []      => 1
      | c :: q' => 1 + k.prefCells c q'
    else 1 + r.prefCells a q

/-- The number of nodes in the top sibling list. -/
def width : Forest β → Nat
  | .nil => 0
  | .cons _ _ _ r => r.width + 1

/-- The largest sibling list of the forest (the fan-out). -/
def fan : Forest β → Nat
  | .nil => 0
  | .cons _ _ k r => max (r.width + 1) (max k.fan r.fan)

theorem prefHits_le : ∀ {f : Forest β} {a : Acc} {q : List Acc},
    f.prefHits a q ≤ q.length + 1
  | .nil, _, _ => Nat.zero_le _
  | .cons b _ k r, a, q => by
    by_cases h : a = b
    · simp only [prefHits, h, ↓reduceIte]
      cases q with
      | nil => exact Nat.le_refl _
      | cons c q' =>
        have ih := prefHits_le (f := k) (a := c) (q := q')
        simp only [List.length_cons]; omega
    · simp only [prefHits, h, ↓reduceIte]; exact prefHits_le

theorem width_le_fan : ∀ {f : Forest β}, f.width ≤ f.fan
  | .nil => Nat.le_refl _
  | .cons _ _ _ _ => Nat.le_max_left _ _

theorem prefCells_le : ∀ {f : Forest β} {a : Acc} {q : List Acc},
    f.prefCells a q ≤ f.width + q.length * f.fan
  | .nil, _, _ => Nat.zero_le _
  | .cons b vs k r, a, q => by
    have hw : r.width + 1 ≤ (Forest.cons b vs k r).fan := Nat.le_max_left _ _
    have hk : k.fan ≤ (Forest.cons b vs k r).fan :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hr : r.fan ≤ (Forest.cons b vs k r).fan :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    have hkw : k.width ≤ k.fan := width_le_fan
    generalize (Forest.cons b vs k r).fan = F at hw hk hr ⊢
    by_cases h : a = b
    · simp only [prefCells, width, h, ↓reduceIte]
      cases q with
      | nil => simp only [List.length_nil, Nat.zero_mul]; omega
      | cons c q' =>
        have ih := prefCells_le (f := k) (a := c) (q := q')
        have m := Nat.mul_le_mul_left q'.length hk
        simp only [List.length_cons, Nat.succ_mul]
        omega
    · simp only [prefCells, width, h, ↓reduceIte]
      have ih := prefCells_le (f := r) (a := a) (q := q)
      have m := Nat.mul_le_mul_left q.length hr
      omega

end Forest

namespace PathMap
variable {β : Type}

def prefHits (m : PathMap β) : List Acc → Nat
  | []     => 1
  | a :: q => 1 + m.kids.prefHits a q

def prefCells (m : PathMap β) : List Acc → Nat
  | []     => 1
  | a :: q => 1 + m.kids.prefCells a q

/-- COST 1. The prefix query visits at most `|q| + 1` trie nodes on the key
    path, for every trie (so for every record list). -/
theorem prefHits_le {m : PathMap β} {q : List Acc} : m.prefHits q ≤ q.length + 1 := by
  cases q with
  | nil => exact Nat.le_refl _
  | cons a q' =>
    have := Forest.prefHits_le (f := m.kids) (a := a) (q := q')
    simp only [prefHits, List.length_cons]; omega

#print axioms prefHits_le

/-- COST 2. In the left-child / right-sibling encoding the prefix query
    inspects at most `1 + |q| * fan` cells. The fan-out is the largest sibling
    list, so the bound needs a small fan-out or a hashed child map. -/
theorem prefCells_le {m : PathMap β} {q : List Acc} :
    m.prefCells q ≤ 1 + q.length * m.kids.fan := by
  cases q with
  | nil => simp only [prefCells, List.length_nil, Nat.zero_mul]; omega
  | cons a q' =>
    have h1 := Forest.prefCells_le (f := m.kids) (a := a) (q := q')
    have h2 := Forest.width_le_fan (f := m.kids)
    simp only [prefCells, List.length_cons, Nat.succ_mul]
    omega

#print axioms prefCells_le

end PathMap

/-- A filter that counts its tests. -/
def filterCount {α : Type} (p : α → Bool) : List α → List α × Nat
  | []      => ([], 0)
  | x :: xs =>
    match filterCount p xs with
    | (ys, n) => (if p x = true then x :: ys else ys, n + 1)

theorem filterCount_eq {α : Type} {p : α → Bool} :
    ∀ {xs : List α}, filterCount p xs = (xs.filter p, xs.length)
  | [] => rfl
  | x :: xs => by
    simp only [filterCount]
    rw [filterCount_eq]
    cases h : p x <;> simp [List.filter, h]

theorem filterCount_fst {α : Type} {p : α → Bool} {xs : List α} :
    (filterCount p xs).1 = xs.filter p := by rw [filterCount_eq]

theorem filterCount_snd {α : Type} {p : α → Bool} {xs : List α} :
    (filterCount p xs).2 = xs.length := by rw [filterCount_eq]

/-- The list concept of the prefix query, with its test count. -/
def listPrefixesCounted {β : Type} (es : List (List Acc × β)) (q : List Acc) : List β × Nat :=
  let r := filterCount (fun e => (dropPrefix e.1 q).isSome) es
  (r.1.map (·.2), r.2)

theorem listPrefixesCounted_fst {β : Type} {es : List (List Acc × β)} {q : List Acc} :
    (listPrefixesCounted es q).1 = PathMap.listPrefixes es q := by
  simp only [listPrefixesCounted, PathMap.listPrefixes]; rw [filterCount_fst]

/-- COST 3. The list concept does `|es|` prefix tests, for every query. -/
theorem listPrefixesCounted_snd {β : Type} {es : List (List Acc × β)} {q : List Acc} :
    (listPrefixesCounted es q).2 = es.length := by
  simp only [listPrefixesCounted]; exact filterCount_snd

#print axioms listPrefixesCounted_snd

/-- COST, the comparison. On the index built from any record list `es`, the
    prefix query visits at most `|q| + 1` key-path nodes. The list concept does
    `|es|` tests. The two queries give the same records. -/
theorem prefix_query_cost {β : Type} (es : List (List Acc × β)) (q : List Acc) :
    (PathMap.fromList es).prefHits q ≤ q.length + 1 ∧
    (listPrefixesCounted es q).2 = es.length ∧
    (∀ x, x ∈ (PathMap.fromList es).lookupPrefixes q ↔ x ∈ (listPrefixesCounted es q).1) :=
  ⟨PathMap.prefHits_le, listPrefixesCounted_snd,
   fun _ => by rw [listPrefixesCounted_fst]; exact PathMap.lookupPrefixes_equiv⟩

#print axioms prefix_query_cost

/-! ## 2. The index of a record list, and the summary store -/

section Index
variable {ρ : Type}

/-- The path index of a record list, keyed by `key`. -/
def indexBy (key : ρ → List Acc) (rs : List ρ) : PathMap ρ :=
  PathMap.fromList (rs.map fun r => (key r, r))

/-- The records on the key path of `q` (prefixes) and below `q` (extensions). -/
def around (m : PathMap ρ) (q : List Acc) : List ρ :=
  m.lookupPrefixes q ++ m.lookupExtensions q

theorem mem_map_key {key : ρ → List Acc} {rs : List ρ} {k : List Acc} {x : ρ} :
    (k, x) ∈ rs.map (fun r => (key r, r)) ↔ x ∈ rs ∧ k = key x := by
  rw [List.mem_map]
  constructor
  · intro ⟨r, h1, h2⟩
    injection h2 with hk hx
    subst hx; exact ⟨h1, hk.symm⟩
  · intro ⟨h1, h2⟩; exact ⟨x, h1, by rw [h2]⟩

theorem mem_prefixes_indexBy {key : ρ → List Acc} {rs : List ρ} {q : List Acc} {x : ρ} :
    x ∈ (indexBy key rs).lookupPrefixes q ↔ x ∈ rs ∧ ∃ s, q = key x ++ s := by
  rw [indexBy, PathMap.mem_lookupPrefixes_fromList]
  constructor
  · intro ⟨k, h1, h2⟩
    have ⟨hx, hk⟩ := mem_map_key.mp h1
    subst hk; exact ⟨hx, h2⟩
  · intro ⟨hx, h2⟩; exact ⟨key x, mem_map_key.mpr ⟨hx, rfl⟩, h2⟩

theorem mem_extensions_indexBy {key : ρ → List Acc} {rs : List ρ} {q : List Acc} {x : ρ} :
    x ∈ (indexBy key rs).lookupExtensions q ↔ x ∈ rs ∧ ∃ s, key x = q ++ s := by
  rw [indexBy, PathMap.mem_lookupExtensions_fromList]
  constructor
  · intro ⟨k, h1, h2⟩
    have ⟨hx, hk⟩ := mem_map_key.mp h1
    subst hk; exact ⟨hx, h2⟩
  · intro ⟨hx, h2⟩; exact ⟨key x, mem_map_key.mpr ⟨hx, rfl⟩, h2⟩

/-- The index query `around` gives exactly the records whose key is a prefix of
    `q` or has `q` as a prefix. -/
theorem mem_around_indexBy {key : ρ → List Acc} {rs : List ρ} {q : List Acc} {x : ρ} :
    x ∈ around (indexBy key rs) q ↔
      x ∈ rs ∧ ((∃ s, q = key x ++ s) ∨ (∃ s, key x = q ++ s)) := by
  rw [around, List.mem_append, mem_prefixes_indexBy, mem_extensions_indexBy]
  constructor
  · intro h; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, Or.inl h2⟩
    · exact ⟨h1, Or.inr h2⟩
  · intro ⟨h1, h2⟩; rcases h2 with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩

#print axioms mem_around_indexBy

theorem around_sound {key : ρ → List Acc} {rs : List ρ} {q : List Acc} {x : ρ} :
    x ∈ around (indexBy key rs) q → x ∈ rs := fun h => (mem_around_indexBy.mp h).1

/-- If the record test implies the key relation, then the filter of the index
    query and the filter of the record list give the same records. -/
theorem around_filter_equiv {key : ρ → List Acc} {rs : List ρ} {q : List Acc}
    {test : ρ → Bool}
    (hrel : ∀ x, test x = true → (∃ s, q = key x ++ s) ∨ (∃ s, key x = q ++ s)) {x : ρ} :
    x ∈ (around (indexBy key rs) q).filter test ↔ x ∈ rs.filter test := by
  rw [List.mem_filter, List.mem_filter]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨around_sound h1, h2⟩
  · intro ⟨h1, h2⟩; exact ⟨mem_around_indexBy.mpr ⟨h1, hrel x h2⟩, h2⟩

theorem prefixes_filter_equiv {key : ρ → List Acc} {rs : List ρ} {q : List Acc}
    {test : ρ → Bool} (hrel : ∀ x, test x = true → ∃ s, q = key x ++ s) {x : ρ} :
    x ∈ ((indexBy key rs).lookupPrefixes q).filter test ↔ x ∈ rs.filter test := by
  rw [List.mem_filter, List.mem_filter]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨(mem_prefixes_indexBy.mp h1).1, h2⟩
  · intro ⟨h1, h2⟩; exact ⟨mem_prefixes_indexBy.mpr ⟨h1, hrel x h2⟩, h2⟩

end Index

/-! ### 2.1 The prefix relation of the fact tests -/

theorem coversB_parts {i c : PFact} (h : coversB i c = true) :
    i.base = c.base ∧ ∃ r, c.path = i.path ++ r := by
  unfold coversB at h
  have ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp h
  have hb := ((Bool.and_eq_true _ _).mp h12).1
  refine ⟨Nat.eq_of_beq_eq_true hb, ?_⟩
  cases hd : dropPrefix i.path c.path with
  | none => rw [hd] at h3; cases h3
  | some r => exact ⟨r, dropPrefix_some hd⟩

/-- `coversB i c` implies that `i.path` is a prefix of `c.path`. -/
theorem coversB_prefix {i c : PFact} (h : coversB i c = true) :
    ∃ r, c.path = i.path ++ r := (coversB_parts h).2

theorem applicable_parts {i c : PFact} (h : applicable i c = true) :
    i.base = c.base ∧ ∃ r, c.path = i.path ++ r := by
  unfold applicable at h
  exact coversB_parts ((Bool.and_eq_true _ _).mp h).1

theorem applicable_prefix {i c : PFact} (h : applicable i c = true) :
    ∃ r, c.path = i.path ++ r := (applicable_parts h).2

#print axioms applicable_prefix

theorem overlapB_parts {a b : PFact} (h : overlapB a b = true) :
    a.base = b.base ∧ ((∃ r, b.path = a.path ++ r) ∨ (∃ r, a.path = b.path ++ r)) := by
  unfold overlapB relate at h
  have ⟨hb, h2⟩ := (Bool.and_eq_true _ _).mp h
  refine ⟨Nat.eq_of_beq_eq_true hb, ?_⟩
  cases h1 : dropPrefix a.path b.path with
  | some r => exact Or.inl ⟨r, dropPrefix_some h1⟩
  | none =>
    cases h3 : dropPrefix b.path a.path with
    | some r => exact Or.inr ⟨r, dropPrefix_some h3⟩
    | none => rw [h1, h3] at h2; cases h2

/-- `overlapB a b` implies that one path is a prefix of the other. -/
theorem overlapB_prefix {a b : PFact} (h : overlapB a b = true) :
    (∃ r, b.path = a.path ++ r) ∨ (∃ r, a.path = b.path ++ r) := (overlapB_parts h).2

#print axioms overlapB_prefix

/-- The premise of a reversed record is at the exit path (v2 exact table too). -/
theorem revEdge_fst_path (i f : PFact) : (revEdge i f).1.path = f.path := rfl

theorem revEdge_fst_base (i f : PFact) : (revEdge i f).1.base = f.base := rfl

/-! ### 2.2 The summary store -/

/-- A summary record of one method: the premise (initial fact) and the exit
    (final fact at the method exit, with the layer of its edge). -/
structure SumRec where
  premise : PFact
  exit    : AFact
deriving DecidableEq, Repr

/-- The premise of the reversed record (backward application). -/
def SumRec.revPremise (r : SumRec) : PFact := (revEdge r.premise r.exit.fact).1

/-- Forward index: keyed by the premise path. -/
def byEntry (rs : List SumRec) : PathMap SumRec := indexBy (fun r => r.premise.path) rs

/-- Backward index: keyed by the exit path (the premise path of the reversed record). -/
def byExit (rs : List SumRec) : PathMap SumRec := indexBy (fun r => r.exit.fact.path) rs

def candidates (rs : List SumRec) (c : PFact) : List SumRec :=
  (byEntry rs).lookupPrefixes c.path ++ (byEntry rs).lookupExtensions c.path

def candidatesExit (rs : List SumRec) (c : PFact) : List SumRec :=
  (byExit rs).lookupPrefixes c.path ++ (byExit rs).lookupExtensions c.path

/-- The concept of the forward query. -/
def applicableRecs (rs : List SumRec) (c : PFact) : List SumRec :=
  rs.filter (fun r => applicable r.premise c)

theorem candidates_sound {rs : List SumRec} {c : PFact} {r : SumRec} :
    r ∈ candidates rs c → r ∈ rs := around_sound

/-- COMPLETENESS (forward, applicable). Every record whose premise is
    applicable to the caller fact `c` is among the candidates. The prefix half
    of the query is already complete. -/
theorem applicable_mem_prefixes {rs : List SumRec} {c : PFact} {r : SumRec}
    (hr : r ∈ rs) (ha : applicable r.premise c = true) :
    r ∈ (byEntry rs).lookupPrefixes c.path :=
  mem_prefixes_indexBy.mpr ⟨hr, applicable_prefix ha⟩

theorem applicable_mem_candidates {rs : List SumRec} {c : PFact} {r : SumRec}
    (hr : r ∈ rs) (ha : applicable r.premise c = true) : r ∈ candidates rs c :=
  List.mem_append_left _ (applicable_mem_prefixes hr ha)

#print axioms applicable_mem_candidates

/-- COMPLETENESS (forward, overlap). Every record whose premise overlaps `c`
    is among the candidates. -/
theorem overlap_mem_candidates {rs : List SumRec} {c : PFact} {r : SumRec}
    (hr : r ∈ rs) (ho : overlapB r.premise c = true) : r ∈ candidates rs c :=
  mem_around_indexBy.mpr ⟨hr, overlapB_prefix ho⟩

theorem overlap_mem_candidates' {rs : List SumRec} {c : PFact} {r : SumRec}
    (hr : r ∈ rs) (ho : overlapB c r.premise = true) : r ∈ candidates rs c := by
  refine mem_around_indexBy.mpr ⟨hr, ?_⟩
  rcases overlapB_prefix ho with h | h
  · exact Or.inr h
  · exact Or.inl h

#print axioms overlap_mem_candidates
#print axioms overlap_mem_candidates'

/-- Index = concept, forward query: the candidates filtered by `applicable`
    are the records filtered by `applicable`. -/
theorem forward_equiv {rs : List SumRec} {c : PFact} {r : SumRec} :
    r ∈ (candidates rs c).filter (fun x => applicable x.premise c) ↔ r ∈ applicableRecs rs c :=
  around_filter_equiv (fun _ h => Or.inl (applicable_prefix h))

/-- The prefix half alone gives the same forward answer. -/
theorem forward_equiv_prefixes {rs : List SumRec} {c : PFact} {r : SumRec} :
    r ∈ ((byEntry rs).lookupPrefixes c.path).filter (fun x => applicable x.premise c) ↔
      r ∈ applicableRecs rs c :=
  prefixes_filter_equiv (fun _ h => applicable_prefix h)

#print axioms forward_equiv
#print axioms forward_equiv_prefixes

theorem overlap_equiv {rs : List SumRec} {c : PFact} {r : SumRec} :
    r ∈ (candidates rs c).filter (fun x => overlapB x.premise c) ↔
      r ∈ rs.filter (fun x => overlapB x.premise c) :=
  around_filter_equiv (fun _ h => overlapB_prefix h)

#print axioms overlap_equiv

/-- The byExit key is the premise path of the reversed record. -/
theorem byExit_key (r : SumRec) : r.exit.fact.path = r.revPremise.path :=
  (revEdge_fst_path r.premise r.exit.fact).symm

/-- COMPLETENESS (backward, applicable). The reversed reading: the exit fact
    is the premise. -/
theorem rev_applicable_mem_candidatesExit {rs : List SumRec} {c : PFact} {r : SumRec}
    (hr : r ∈ rs) (ha : applicable r.revPremise c = true) : r ∈ candidatesExit rs c := by
  refine List.mem_append_left _ (mem_prefixes_indexBy.mpr ⟨hr, ?_⟩)
  rw [byExit_key]; exact applicable_prefix ha

/-- COMPLETENESS (backward, overlap). -/
theorem rev_overlap_mem_candidatesExit {rs : List SumRec} {c : PFact} {r : SumRec}
    (hr : r ∈ rs) (ho : overlapB r.revPremise c = true) : r ∈ candidatesExit rs c := by
  refine mem_around_indexBy.mpr ⟨hr, ?_⟩
  rw [byExit_key]; exact overlapB_prefix ho

theorem candidatesExit_sound {rs : List SumRec} {c : PFact} {r : SumRec} :
    r ∈ candidatesExit rs c → r ∈ rs := around_sound

theorem backward_equiv {rs : List SumRec} {c : PFact} {r : SumRec} :
    r ∈ (candidatesExit rs c).filter (fun x => applicable x.revPremise c) ↔
      r ∈ rs.filter (fun x => applicable x.revPremise c) :=
  around_filter_equiv (fun x h => by
    have := applicable_prefix h
    rw [← byExit_key] at this
    exact Or.inl this)

/-- The prefix half alone gives the same backward answer. -/
theorem backward_equiv_prefixes {rs : List SumRec} {c : PFact} {r : SumRec} :
    r ∈ ((byExit rs).lookupPrefixes c.path).filter (fun x => applicable x.revPremise c) ↔
      r ∈ rs.filter (fun x => applicable x.revPremise c) :=
  prefixes_filter_equiv (fun x h => by
    have := applicable_prefix h
    rw [← byExit_key] at this
    exact this)

#print axioms backward_equiv_prefixes
#print axioms rev_applicable_mem_candidatesExit
#print axioms rev_overlap_mem_candidatesExit
#print axioms backward_equiv

/-! ### 2.3 A finer key: the base in front of the path

The key `premise.path` does not hold the base. Thus a query for a fact at the
root path (`c.path = []`) enumerates ALL records of the method, for every base.
Both tests (`applicable`, `overlapB`) need equal bases. The key
`base :: path` keeps the completeness and removes the other bases. -/

def keyB (f : PFact) : List Acc := f.base :: f.path

def byEntryB (rs : List SumRec) : PathMap SumRec := indexBy (fun r => keyB r.premise) rs

def candidatesB (rs : List SumRec) (c : PFact) : List SumRec := around (byEntryB rs) (keyB c)

theorem applicable_mem_candidatesB {rs : List SumRec} {c : PFact} {r : SumRec}
    (hr : r ∈ rs) (ha : applicable r.premise c = true) : r ∈ candidatesB rs c := by
  have ⟨hb, s, hs⟩ := applicable_parts ha
  refine mem_around_indexBy.mpr ⟨hr, Or.inl ⟨s, ?_⟩⟩
  simp only [keyB, hb, hs, List.cons_append]

theorem overlap_mem_candidatesB {rs : List SumRec} {c : PFact} {r : SumRec}
    (hr : r ∈ rs) (ho : overlapB r.premise c = true) : r ∈ candidatesB rs c := by
  have ⟨hb, h⟩ := overlapB_parts ho
  refine mem_around_indexBy.mpr ⟨hr, ?_⟩
  rcases h with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inl ⟨s, by simp only [keyB, hb, hs, List.cons_append]⟩
  · exact Or.inr ⟨s, by simp only [keyB, hb, hs, List.cons_append]⟩

/-- The base-keyed index gives only records with the base of `c`. -/
theorem candidatesB_base {rs : List SumRec} {c : PFact} {r : SumRec}
    (h : r ∈ candidatesB rs c) : r.premise.base = c.base := by
  have ⟨_, h2⟩ := mem_around_indexBy.mp h
  rcases h2 with ⟨s, hs⟩ | ⟨s, hs⟩
  · simp only [keyB, List.cons_append] at hs; injection hs with h1; exact h1.symm
  · simp only [keyB, List.cons_append] at hs; injection hs

#print axioms applicable_mem_candidatesB
#print axioms overlap_mem_candidatesB
#print axioms candidatesB_base

/-! ### 2.4 The extension half is redundant for `applicable`

A record from the extension half passes the `applicable` filter only if its key
is equal to the query path. Such a record is also in the prefix half. So the
forward query (and the backward query) needs only `lookupPrefixes`. The
extension half is necessary only for the overlap tests (requests, demand). -/

theorem extension_half_redundant {rs : List SumRec} {c : PFact} {r : SumRec}
    (he : r ∈ (byEntry rs).lookupExtensions c.path) (ha : applicable r.premise c = true) :
    r.premise.path = c.path := by
  have ⟨_, s, hs⟩ := mem_extensions_indexBy.mp he
  have ⟨t, ht⟩ := applicable_prefix ha
  have hl := congrArg List.length hs
  have hl2 := congrArg List.length ht
  simp only [List.length_append] at hl hl2
  have h0 : t = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [ht, h0, List.append_nil]

#print axioms extension_half_redundant

/-! ## 3. The split by provenance

The classification of v2 is `AFact.complete` (normal layer AND no `[any]`
conclusion). `complete` records are persisted. The other records (the demand
layer, and the `[any]` conclusions) stay in the per-run store. -/

/-- `(complete, rest)`: the records with a complete exit, and the others. -/
def split (rs : List SumRec) : List SumRec × List SumRec :=
  (rs.filter (fun r => r.exit.complete), rs.filter (fun r => !r.exit.complete))

theorem mem_split_complete {rs : List SumRec} {r : SumRec} :
    r ∈ (split rs).1 ↔ r ∈ rs ∧ r.exit.complete = true := by
  simp only [split, List.mem_filter]

theorem mem_split_rest {rs : List SumRec} {r : SumRec} :
    r ∈ (split rs).2 ↔ r ∈ rs ∧ r.exit.complete = false := by
  simp only [split, List.mem_filter]
  cases r.exit.complete <;> simp

/-- A complete exit is in the normal layer. -/
theorem complete_not_demand {f : AFact} (h : f.complete = true) : f.demand = false := by
  unfold AFact.complete at h
  cases hd : f.demand
  · rfl
  · rw [hd] at h; cases h

/-- A demand exit is never complete. -/
theorem demand_not_complete {f : AFact} (h : f.demand = true) : f.complete = false := by
  unfold AFact.complete; rw [h]; rfl

/-- The union of the two parts is the original store. -/
theorem split_mem_iff {rs : List SumRec} {r : SumRec} :
    r ∈ rs ↔ r ∈ (split rs).1 ∨ r ∈ (split rs).2 := by
  rw [mem_split_complete, mem_split_rest]
  constructor
  · intro h
    cases hb : r.exit.complete
    · exact Or.inr ⟨h, rfl⟩
    · exact Or.inl ⟨h, rfl⟩
  · intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h

/-- Every record is in exactly one part. -/
theorem split_exactly_one {rs : List SumRec} {r : SumRec} (h : r ∈ rs) :
    (r ∈ (split rs).1 ∧ r ∉ (split rs).2) ∨ (r ∉ (split rs).1 ∧ r ∈ (split rs).2) := by
  rw [mem_split_complete, mem_split_rest]
  cases hb : r.exit.complete
  · exact Or.inr ⟨fun ⟨_, h2⟩ => Bool.noConfusion h2, ⟨h, rfl⟩⟩
  · exact Or.inl ⟨⟨h, rfl⟩, fun ⟨_, h2⟩ => Bool.noConfusion h2⟩

#print axioms split_exactly_one
#print axioms split_mem_iff

/-- The two parts are a permutation of the store (no record is lost or doubled). -/
theorem split_perm {rs : List SumRec} : ((split rs).1 ++ (split rs).2).Perm rs :=
  List.filter_append_perm (fun r : SumRec => r.exit.complete) rs

theorem split_length {rs : List SumRec} :
    (split rs).1.length + (split rs).2.length = rs.length := by
  rw [← List.length_append]; exact split_perm.length_eq

#print axioms split_perm
#print axioms split_length

/-- The stores of one run: the persisted part and the per-run part. -/
structure RunStore where
  persisted : List SumRec
  perRun    : List SumRec

/-- The records that the run reads. -/
def RunStore.view (s : RunStore) : List SumRec := s.persisted ++ s.perRun

/-- Persist the complete records. Keep the other records for this run only. -/
def RunStore.ofSplit (rs : List SumRec) : RunStore := ⟨(split rs).1, (split rs).2⟩

/-- What the next run receives as summaries: the persisted part only. -/
def RunStore.next (s : RunStore) : RunStore := ⟨s.persisted, []⟩

/-- Within the run, no record is lost. -/
theorem run_view_perm {rs : List SumRec} : (RunStore.ofSplit rs).view.Perm rs := split_perm

theorem run_view_iff {rs : List SumRec} {r : SumRec} :
    r ∈ (RunStore.ofSplit rs).view ↔ r ∈ rs := split_perm.mem_iff

/-- Every filter query on the run view gives the records of the original store. -/
theorem run_query_iff {rs : List SumRec} {test : SumRec → Bool} {r : SumRec} :
    r ∈ (RunStore.ofSplit rs).view.filter test ↔ r ∈ rs.filter test := by
  rw [List.mem_filter, List.mem_filter, run_view_iff]

/-- Two indexes (persisted and per-run) answer as the one index of the store. -/
theorem run_index_iff {key : SumRec → List Acc} {rs : List SumRec} {q : List Acc} {x : SumRec} :
    x ∈ around (indexBy key (split rs).1) q ++ around (indexBy key (split rs).2) q ↔
      x ∈ around (indexBy key rs) q := by
  rw [List.mem_append, mem_around_indexBy, mem_around_indexBy, mem_around_indexBy]
  constructor
  · intro h; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨split_mem_iff.mpr (Or.inl h1), h2⟩
    · exact ⟨split_mem_iff.mpr (Or.inr h1), h2⟩
  · intro ⟨h1, h2⟩
    rcases split_mem_iff.mp h1 with h | h
    · exact Or.inl ⟨h, h2⟩
    · exact Or.inr ⟨h, h2⟩

theorem candidates_eq_around (rs : List SumRec) (c : PFact) :
    candidates rs c = around (byEntry rs) c.path := rfl

theorem run_candidates_iff {rs : List SumRec} {c : PFact} {r : SumRec} :
    r ∈ candidates (split rs).1 c ++ candidates (split rs).2 c ↔ r ∈ candidates rs c :=
  run_index_iff

#print axioms run_query_iff
#print axioms run_candidates_iff

/-- Only complete records are persisted. -/
theorem persisted_complete {rs : List SumRec} {r : SumRec} :
    r ∈ (RunStore.ofSplit rs).persisted → r.exit.complete = true :=
  fun h => (mem_split_complete.mp h).2

/-- No demand record is persisted. -/
theorem persisted_not_demand {rs : List SumRec} {r : SumRec} :
    r ∈ (RunStore.ofSplit rs).persisted → r.exit.demand = false :=
  fun h => complete_not_demand (persisted_complete h)

/-- The next run loses exactly the records that are not complete. -/
theorem next_loses_only_demand {rs : List SumRec} {r : SumRec} (h : r ∈ rs) :
    r ∉ (RunStore.ofSplit rs).next.view ↔ r.exit.complete = false := by
  simp only [RunStore.next, RunStore.view, RunStore.ofSplit, List.append_nil]
  rw [mem_split_complete]
  constructor
  · intro hn
    cases hb : r.exit.complete
    · rfl
    · exact absurd ⟨h, hb⟩ hn
  · intro hb ⟨_, hf⟩; rw [hb] at hf; cases hf

#print axioms persisted_not_demand
#print axioms next_loses_only_demand

/-! ## 4. The demand store -/

/-- The demand match of an added fact `a` against a demand final `d`. -/
def demandMatch (d a : PFact) : Bool := overlapB d a

def demandIndex (ds : List PFact) : PathMap PFact := indexBy (fun d => d.path) ds

/-- The index query of the spec: `lookupPrefixes(a.path) ++ lookupExtensions(a.path)`. -/
def demandQuery (ds : List PFact) (a : PFact) : List PFact :=
  (demandIndex ds).lookupPrefixes a.path ++ (demandIndex ds).lookupExtensions a.path

/-- COMPLETENESS. The query gives every demand final that overlaps `a`. -/
theorem demand_complete {ds : List PFact} {a d : PFact} (hd : d ∈ ds)
    (hm : demandMatch d a = true) : d ∈ demandQuery ds a :=
  mem_around_indexBy.mpr ⟨hd, overlapB_prefix hm⟩

theorem demand_sound {ds : List PFact} {a d : PFact} :
    d ∈ demandQuery ds a → d ∈ ds := around_sound

/-- Index = concept: `matches(m, a)` computed on the index is the list filter. -/
theorem demand_equiv {ds : List PFact} {a d : PFact} :
    d ∈ (demandQuery ds a).filter (fun d => demandMatch d a) ↔
      d ∈ ds.filter (fun d => demandMatch d a) :=
  around_filter_equiv (fun _ h => overlapB_prefix h)

/-- The boolean query `matches(m, a) = ∃ d. overlap(d, a)`: index = concept. -/
theorem demand_any_equiv {ds : List PFact} {a : PFact} :
    (demandQuery ds a).any (fun d => demandMatch d a) = ds.any (fun d => demandMatch d a) := by
  cases h1 : (demandQuery ds a).any (fun d => demandMatch d a) <;>
    cases h2 : ds.any (fun d => demandMatch d a)
  · rfl
  · have ⟨d, hd, hm⟩ := List.any_eq_true.mp h2
    have := List.any_eq_false.mp h1 d (demand_complete hd hm)
    exact absurd hm this
  · have ⟨d, hd, hm⟩ := List.any_eq_true.mp h1
    have := List.any_eq_false.mp h2 d (demand_sound hd)
    exact absurd hm this
  · rfl

#print axioms demand_complete
#print axioms demand_equiv
#print axioms demand_any_equiv

/-- The base-keyed demand index (the same design note as §2.3). -/
def demandQueryB (ds : List PFact) (a : PFact) : List PFact :=
  around (indexBy keyB ds) (keyB a)

theorem demand_completeB {ds : List PFact} {a d : PFact} (hd : d ∈ ds)
    (hm : demandMatch d a = true) : d ∈ demandQueryB ds a := by
  have ⟨hb, h⟩ := overlapB_parts hm
  refine mem_around_indexBy.mpr ⟨hd, ?_⟩
  rcases h with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inl ⟨s, by simp only [keyB, hb, hs, List.cons_append]⟩
  · exact Or.inr ⟨s, by simp only [keyB, hb, hs, List.cons_append]⟩

#print axioms demand_completeB

/-! ## 5. Exact-key maps: the request store and the subscription store -/

/-- An association-list map: one bucket of values for each key. -/
abbrev KMap (κ β : Type) := List (κ × List β)

namespace KMap
variable {κ β : Type} [DecidableEq κ]

def empty : KMap κ β := []

def lookup : KMap κ β → κ → List β
  | [],            _ => []
  | (k', vs) :: m, k => if k' = k then vs else lookup m k

def insert : KMap κ β → κ → β → KMap κ β
  | [],            k, v => [(k, [v])]
  | (k', vs) :: m, k, v => if k' = k then (k', v :: vs) :: m else (k', vs) :: insert m k v

def fromList : List (κ × β) → KMap κ β
  | []           => []
  | (k, v) :: es => insert (fromList es) k v

/-- The list concept: the values of the records with the key `k`. -/
def listLookup (es : List (κ × β)) (k : κ) : List β :=
  (es.filter (fun e => decide (e.1 = k))).map (·.2)

theorem lookup_empty (k : κ) : lookup (empty : KMap κ β) k = [] := rfl

theorem lookup_insert_self : ∀ (m : KMap κ β) (k : κ) (v : β),
    lookup (insert m k v) k = v :: lookup m k
  | [], k, v => by simp [insert, lookup]
  | (k', vs) :: m, k, v => by
    by_cases h : k' = k
    · subst h; simp [insert, lookup]
    · simp only [insert, lookup, h, ↓reduceIte]; exact lookup_insert_self m k v

theorem lookup_insert_other : ∀ (m : KMap κ β) {k k' : κ} (v : β), k ≠ k' →
    lookup (insert m k v) k' = lookup m k'
  | [], k, k', v, h => by simp [insert, lookup, h]
  | (j, vs) :: m, k, k', v, h => by
    by_cases hj : j = k
    · subst hj; simp [insert, lookup, h]
    · simp only [insert, lookup, hj, ↓reduceIte]
      by_cases hj' : j = k'
      · simp [hj']
      · simp only [hj', ↓reduceIte]; exact lookup_insert_other m v h

#print axioms lookup_insert_self
#print axioms lookup_insert_other

/-- Index = concept, with the same order of the values. -/
theorem lookup_fromList : ∀ (es : List (κ × β)) (k : κ),
    lookup (fromList es) k = listLookup es k
  | [], _ => rfl
  | (k0, v0) :: es, k => by
    simp only [fromList]
    by_cases h : k0 = k
    · subst h
      rw [lookup_insert_self, lookup_fromList]
      simp [listLookup, List.filter]
    · rw [lookup_insert_other _ _ h, lookup_fromList]
      simp [listLookup, List.filter, h]

#print axioms lookup_fromList

theorem mem_lookup_fromList {es : List (κ × β)} {k : κ} {v : β} :
    v ∈ lookup (fromList es) k ↔ (k, v) ∈ es := by
  rw [lookup_fromList]
  simp only [listLookup, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro ⟨⟨k', v'⟩, ⟨h1, h2⟩, h3⟩
    simp only at h2 h3
    rw [← h2, ← h3]; exact h1
  · intro h; exact ⟨(k, v), ⟨h, rfl⟩, rfl⟩

#print axioms mem_lookup_fromList

end KMap

/-- The key of the request store and of the subscription store. -/
abbrev MKey := MethodId × PFact

/-! ### 5.1 The request store -/

/-- A request `(m, i, t)`: the method, its initial fact, the requested mark. -/
structure ReqRec where
  method  : MethodId
  initial : PFact
  mark    : Mark
deriving DecidableEq, Repr

def reqKey (r : ReqRec) : MKey := (r.method, r.initial)

/-- The request store: `(method, initial)` ↦ the requested marks. -/
def requestStore (rs : List ReqRec) : KMap MKey Mark :=
  KMap.fromList (rs.map fun r => (reqKey r, r.mark))

/-- Index = concept: the marks at the key `(m, i)` are the marks of the
    records `(m, i, t)`. This answers the duplicate test and the state lookup. -/
theorem requestStore_equiv {rs : List ReqRec} {m : MethodId} {i : PFact} {t : Mark} :
    t ∈ KMap.lookup (requestStore rs) (m, i) ↔ ⟨m, i, t⟩ ∈ rs := by
  rw [requestStore, KMap.mem_lookup_fromList, List.mem_map]
  constructor
  · intro ⟨r, h1, h2⟩
    simp only [reqKey, Prod.mk.injEq] at h2
    have ⟨⟨hm, hi⟩, ht⟩ := h2
    rw [← hm, ← hi, ← ht]; exact h1
  · intro h; exact ⟨⟨m, i, t⟩, h, rfl⟩

#print axioms requestStore_equiv

/-- The STANDING match of a request (spec §8.3), the concept: the requests of
    the method `M` whose initial fact overlaps the added fact `a`. -/
def standing (rs : List ReqRec) (M : MethodId) (a : PFact) : List ReqRec :=
  rs.filter (fun r => decide (r.method = M) && overlapB a r.initial)

/-- The standing match is NOT an exact-key query: the initial fact of the
    request and the added fact differ in general. A path index keyed by
    `method :: base :: path` of the initial fact answers it completely. -/
def reqPathKey (r : ReqRec) : List Acc := r.method :: keyB r.initial

def standingQuery (rs : List ReqRec) (M : MethodId) (a : PFact) : List ReqRec :=
  around (indexBy reqPathKey rs) (M :: keyB a)

theorem standing_complete {rs : List ReqRec} {M : MethodId} {a : PFact} {r : ReqRec}
    (h : r ∈ standing rs M a) : r ∈ standingQuery rs M a := by
  have ⟨hr, ht⟩ := List.mem_filter.mp h
  have ⟨hm, ho⟩ := (Bool.and_eq_true _ _).mp ht
  have hm := of_decide_eq_true hm
  have ⟨hb, hp⟩ := overlapB_parts ho
  refine mem_around_indexBy.mpr ⟨hr, ?_⟩
  rcases hp with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inr ⟨s, by simp only [reqPathKey, keyB, hm, hb, hs, List.cons_append]⟩
  · exact Or.inl ⟨s, by simp only [reqPathKey, keyB, hm, hb, hs, List.cons_append]⟩

theorem standing_equiv {rs : List ReqRec} {M : MethodId} {a : PFact} {r : ReqRec} :
    r ∈ (standingQuery rs M a).filter (fun r => decide (r.method = M) && overlapB a r.initial) ↔
      r ∈ standing rs M a := by
  rw [List.mem_filter, standing, List.mem_filter]
  constructor
  · intro ⟨h1, h2⟩; exact ⟨around_sound h1, h2⟩
  · intro ⟨h1, h2⟩
    exact ⟨standing_complete (List.mem_filter.mpr ⟨h1, h2⟩), h2⟩

#print axioms standing_complete
#print axioms standing_equiv

/-! ### 5.2 The subscription store -/

/-- A subscription: the caller record that waits for the summaries of the
    served initial fact `j` of the callee. -/
structure SubRec where
  callee     : MethodId
  served     : PFact
  caller     : MethodId
  callerInit : PFact
  node       : Node
  added      : PFact
deriving DecidableEq, Repr

def subKey (s : SubRec) : MKey := (s.callee, s.served)

def subscriptionStore (ss : List SubRec) : KMap MKey SubRec :=
  KMap.fromList (ss.map fun s => (subKey s, s))

/-- Index = concept: on a new summary edge of `(m, j)`, the lookup gives every
    subscription of `(m, j)`. The rule `ret` needs `serves m a j` exactly, so the
    exact key is complete for it. -/
theorem subscriptionStore_equiv {ss : List SubRec} {m : MethodId} {j : PFact} {s : SubRec} :
    s ∈ KMap.lookup (subscriptionStore ss) (m, j) ↔ s ∈ ss ∧ s.callee = m ∧ s.served = j := by
  rw [subscriptionStore, KMap.mem_lookup_fromList, List.mem_map]
  constructor
  · intro ⟨s', h1, h2⟩
    simp only [subKey, Prod.mk.injEq] at h2
    have ⟨⟨hm, hj⟩, hs⟩ := h2
    subst hs; exact ⟨h1, hm, hj⟩
  · intro ⟨h1, hm, hj⟩
    exact ⟨s, h1, by simp only [subKey, hm, hj]⟩

theorem subscriptionStore_lookup {ss : List SubRec} {m : MethodId} {j : PFact} :
    KMap.lookup (subscriptionStore ss) (m, j) =
      ss.filter (fun s => decide (subKey s = (m, j))) := by
  rw [subscriptionStore, KMap.lookup_fromList]
  simp only [KMap.listLookup]
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map, List.filter]
    cases decide (subKey s = (m, j)) with
    | false => exact ih
    | true => simp only [List.map]; rw [ih]

#print axioms subscriptionStore_equiv
#print axioms subscriptionStore_lookup

/-! ## 6. Examples -/

namespace Examples

-- accessors
def f : Acc := 1
def g : Acc := 2
def h : Acc := 3

/-! ### 6.1 The path trie -/

def es1 : List (List Acc × Nat) :=
  [([], 0), ([f], 1), ([f, g], 2), ([f, g, h], 3), ([f, h], 4), ([g], 5)]

def m1 : PathMap Nat := PathMap.fromList es1

#eval m1.lookupPrefixes [f, g, h]          -- keys [], [f], [f,g], [f,g,h]
#eval PathMap.listPrefixes es1 [f, g, h]
#eval m1.lookupExtensions [f]              -- keys [f], [f,g], [f,g,h], [f,h]
#eval PathMap.listExtensions es1 [f]
#eval m1.lookupExact [f, g]
#eval m1.lookupPrefixes [h]                -- only the root
#eval m1.lookupExtensions []               -- every value

#eval m1.prefHits [f, g, h]                -- 4 = |q| + 1
#eval (listPrefixesCounted es1 [f, g, h]).2   -- 6 = |es|

/-- 1000 keys of length 1: one wide sibling list. -/
def wide (n : Nat) : List (List Acc × Nat) := (List.range n).map fun i => ([i], i)
/-- 1000 keys on one chain: `[]`, `[7]`, `[7,7]`, ... -/
def deep (n : Nat) : List (List Acc × Nat) := (List.range n).map fun i => (List.replicate i 7, i)

#eval (PathMap.fromList (wide 1000)).prefHits [0]                -- 2
#eval (PathMap.fromList (wide 1000)).prefCells [0]               -- 1001: the sibling scan
#eval (PathMap.fromList (wide 1000)).kids.fan                     -- 1000
#eval (listPrefixesCounted (wide 1000) [0]).2                    -- 1000
#eval (PathMap.fromList (deep 1000)).prefHits (List.replicate 3 7)    -- 4
#eval (PathMap.fromList (deep 1000)).prefCells (List.replicate 3 7)   -- 4
#eval (listPrefixesCounted (deep 1000) (List.replicate 3 7)).2        -- 1000
#eval (PathMap.fromList (deep 1000)).lookupPrefixes (List.replicate 3 7)

/-! ### 6.2 The summary store -/

def st : Kind := .star Excl.empty
def pf (b : Base) (p : List Acc) (k : Kind) : PFact := ⟨b, p, k, .star⟩

def r1 : SumRec := ⟨pf 1 [f] st,        ⟨pf 2 [] st, false⟩⟩
def r2 : SumRec := ⟨pf 1 [] (.star (.set [f])), ⟨pf 2 [g] st, false⟩⟩
def r3 : SumRec := ⟨pf 1 [f, g] .exact, ⟨pf 2 [h] .exact, true⟩⟩
def r4 : SumRec := ⟨pf 3 [f] st,        ⟨pf 2 [f] st, false⟩⟩
def r5 : SumRec := ⟨pf 1 [g] st,        ⟨pf 2 [] st, true⟩⟩
def recs : List SumRec := [r1, r2, r3, r4, r5]

/-- The caller fact `(1, .f, *, {}, *)`. -/
def c1 : PFact := pf 1 [f] st

#eval (candidates recs c1).map (·.premise)
#eval ((candidates recs c1).filter (fun r => applicable r.premise c1)).map (·.premise)
#eval ((byEntry recs).lookupPrefixes c1.path).map (·.premise)
#eval (applicableRecs recs c1).map (·.premise)
#eval (candidatesB recs c1).map (·.premise)
#eval ((candidates recs c1).filter (fun r => overlapB r.premise c1)).map (·.premise)

/-- DESIGN NOTE 1. The record at the exact key comes twice (prefix half and
    extension half). The path key also returns the record of the base 3. -/
example : (candidates recs c1).length = 6 := by decide
example : (candidates recs c1).count r1 = 2 := by decide
example : r4 ∈ candidates recs c1 ∧ applicable r4.premise c1 = false := by decide
/-- The base key removes the base 3. -/
example : (candidatesB recs c1).length = 4 ∧ r4 ∉ candidatesB recs c1 := by decide

/-- DESIGN NOTE 2. A root fact `(1, ., *, {}, *)` gets every record from the
    path key (also the other bases); the base key gives only the base 1. -/
def c0 : PFact := pf 1 [] st
example : (candidates recs c0).length = 6 := by decide
example : (candidatesB recs c0).length = 5 := by decide

/-- The backward reading: a requirement at `(2, ., *, {}, *)`. -/
def q2 : PFact := pf 2 [] st
#eval (candidatesExit recs q2).map (·.exit.fact)
#eval ((candidatesExit recs q2).filter (fun r => applicable r.revPremise q2)).map (·.revPremise)

/-! ### 6.3 The split -/

#eval ((split recs).1.map (·.premise), (split recs).2.map (·.premise))
example : (split recs).1.length = 3 ∧ (split recs).2.length = 2 := by decide
example : (RunStore.ofSplit recs).next.view.length = 3 := by decide

/-! ### 6.4 The demand store -/

def ds : List PFact := [pf 1 [] .any, pf 1 [f, g] st, pf 1 [h] st, pf 4 [f] st]
/-- The added fact `(1, .f, *, {}, *)`. -/
def a1 : PFact := pf 1 [f] st

#eval demandQuery ds a1
#eval (demandQuery ds a1).filter (fun d => demandMatch d a1)
#eval ds.filter (fun d => demandMatch d a1)
#eval demandQueryB ds a1
example : (demandQuery ds a1).filter (fun d => demandMatch d a1) =
    ds.filter (fun d => demandMatch d a1) := by decide

/-! ### 6.5 The exact-key maps -/

def reqs : List ReqRec := [⟨1, pf 1 [] st, 5⟩, ⟨1, pf 1 [f] st, 6⟩, ⟨1, pf 1 [] st, 7⟩]

#eval KMap.lookup (requestStore reqs) (1, pf 1 [] st)       -- [5, 7]
#eval KMap.lookup (requestStore reqs) (1, pf 1 [f] st)      -- [6]
example : KMap.lookup (requestStore reqs) (1, pf 1 [] st) = [5, 7] := by decide

/-- DESIGN NOTE 3. The standing match (spec §8.3) of the added fact
    `(1, .f.g, *, {}, T)` overlaps all three requests, but its key is in no
    bucket: the exact-key map cannot answer the standing match. The path
    index `standingQuery` answers it. -/
def aT : PFact := ⟨1, [f, g], st, .conc 5⟩
example : KMap.lookup (requestStore reqs) (1, aT) = [] := by decide
example : (standing reqs 1 aT).length = 3 := by decide
example : (standing reqs 1 aT).all (fun r => (standingQuery reqs 1 aT).contains r) = true := by
  decide
#eval standingQuery reqs 1 aT |>.map (·.mark)

def subs : List SubRec :=
  [⟨2, pf 1 [] st, 9, pf 0 [] .exact, 40, pf 1 [f] st⟩,
   ⟨2, pf 1 [f] st, 9, pf 0 [] .exact, 41, pf 1 [f] st⟩,
   ⟨2, pf 1 [] st, 8, pf 0 [] .exact, 42, pf 1 [] st⟩]

#eval (KMap.lookup (subscriptionStore subs) (2, pf 1 [] st)).map (·.node)   -- [40, 42]

end Examples

end ApSpec.Store
