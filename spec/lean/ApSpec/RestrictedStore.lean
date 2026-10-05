/-
  ApSpec.RestrictedStore — the stores of a restricted run (`DR`, Restricted.lean).

  A restricted run needs two new lookups and one new tree operation:
    1. the emission lookup: the demand edges of the callee that can emit an initial
       fact for an added fact `a` (rule `initR`);
    2. the restriction lookup: the demand edges of the callee that can restrict a
       summary edge `(j, g)` (rule `ret`);
    3. the restriction of a whole edge tree of conclusions by `D-p` (`restrictConcS`
       on each conclusion, as one walk on the tree).

  For each one: the CONCEPT (a filter over a list, or the per-conclusion function),
  the INDEX form (on `Store.PathMap` or `Tree.EdgeTree`), the equivalence theorem,
  and a cost theorem.

  Kotlin-like sketch (it matches the Lean definitions below):

  ```kotlin
  // ---- 1 + 2. The demand store: one PathMap per method, keyed by din.path ----
  class DemandStore(edges: List<DemandEdge>) {
      val idx = PathMap<DemandEdge>().apply { edges.forEach { insert(it.din.path, it) } }

      // near(q) (Lean: `near`): the edges whose din.path is a prefix of q or extends q.
      // One walk: the key path of q (|q| + 1 nodes), then the subtree BELOW the node at q.
      fun near(q: List<Acc>): List<DemandEdge> {
          val out = ArrayList<DemandEdge>()
          var node: Node? = idx.root
          for (acc in q) {                             // prefix half: din.path <= q
              out += node!!.values
              node = node.child(acc) ?: return out     // no node at q: nothing below q
          }
          out += node!!.values                         // din.path == q (returned once)
          node.children.forEach { it.collectAll(out) } // extension half: din.path > q
          return out
      }

      // emission lookup (rule initR): the initial facts for the added fact a
      fun emit(a: PFact): List<PFact> = near(a.path).mapNotNull { d -> emitS(d.din, a) }

      // version 4 (emitM): an exact added fact is emitted only from chains at or above
      // its path, so the prefix walk alone is complete (Lean: `nearPre`, `emitPrefCands`)
      fun emitV4(a: PFact): List<PFact> =
          (if (a.kind == EXACT) nearPre(a.path) else near(a.path)).mapNotNull { d -> emitM(d.din, a) }

      // restriction lookup (rule ret), per summary conclusion ...
      fun restrict(j: PFact, g: AFact): List<AFact> =
          near(j.path).mapNotNull { d -> restrictS(j, g, d) }

      // ... or per edge tree of the premise j (one tree per layer, exclusion and mark exclusion)
      fun restrictTrees(b: Base, j: PFact, t: EdgeTree): List<EdgeTree> =
          near(j.path).mapNotNull { d -> restrictTreeE(true, b, j, t, d) }
  }

  // ---- 3. The restriction of an edge tree (premise j, layer, exclusion E, mark exclusion X) ----
  fun restrictTreeE(keep: Boolean, b: Base, j: PFact, t: EdgeTree, d: DemandEdge): EdgeTree? {
      val dout = d.dout ?: return null                 // no D-p: no summary
      if (!overlap(j, d.din)) return null              // R-p := S-p, or nothing
      if (b != dout.base) return EdgeTree(t.excl, t.mx, t.demand, Tree.EMPTY)
      return EdgeTree(t.excl, t.mx, t.demand,
          rTree(keep, t.excl, dout.kind, MarkSet.EMPTY, dout.path, t.tree))
  }

  // walk down q = the rest of dout.path; M = the [any] marks met above D-p
  fun rTree(keep: Boolean, E: Excl, dk: Kind, M: MarkSet, q: List<Acc>, t: Tree): Tree =
      if (q.isEmpty()) {
          // at D-p: keep the payload, add the moved [any] leaves (as `$` for an exact D-p),
          // keep each child whose accessor the tail of D-p admits (SHARED, not copied)
          Tree(addMarks(dk, t.root, M), t.kids.filter { (a, _) -> admitsTail(dk, listOf(a)) })
      } else {
          val a = q.first(); val rest = q.drop(1)
          val sub = rTree(keep, E, dk, M + t.root.anyM, rest, t.kids[a] ?: Tree.EMPTY)
          // above D-p: keep the `*` flag if E admits the rest of the chain (S rule; U: drop),
          // move the [any] marks down, drop the `$` marks and every other child
          Tree(Payload(star = keep && t.root.star && E.admits(q)), mapOf(a to sub))
      }
  ```

  Results (each has a theorem below and a `#print axioms` audit):
    * `emit_complete_S/U`, `restrict_complete_S/U` (and `..K` for the base-keyed index):
      the index query is complete.
    * `near_sound`, `emitCands_sound`, `restrictCands_sound`: every candidate is related
      (`relate ≠ .apart`).
    * `near_equiv`, `emit_lookup_equiv_S/U`, `restrict_lookup_equiv_S/U`,
      `initR_premise_equiv`, `ret_premise_equiv`: index = list concept.
    * `near_query_cost`: the cost of the query. The bound "walk + number returned" is
      FALSE for this (uncompressed) trie: `deep_chain_cost` is a checked counterexample.
    * `restrictTree_mem`, `restrictTreeE_mem_S/U`, `restrictTreeE_den_S`: the tree
      operation is EXACT (membership of whole `AFact`s, and the pairs of each layer).
    * `restrictTree_cost` (`rTree_shape`, `keepKids_children`, `newCells_eq`): the cost,
      and the sharing of the kept subtrees.
    * `restrictTreeE_inv`: the result keeps the trie invariants (well formed, no `*` leaf
      in the demand layer).
    * Version 5 (cleaners, mark exclusion `mx` of an edge tree): `restrictTree_mx`,
      `restrictTreeU_mx`, `restrictTreeW_mx`, `restrictTreeE_mx`: the result tree has the
      mark exclusion of the input tree (and its exclusion and layer). `rC_markX`: the walk
      does not read the marks, so it commutes with the read `markX mx` of the stored flag
      `*`; the exactness theorems above keep their statements (§4.2a, checked).
    * Version 4 (`emitM`, §2.5): `emitM_local`, `emit_complete_M`, `emit_completeK_M`,
      `emit_lookup_equiv_M`, `emit_lookup_equivK_M`, `initR_premise_equiv_M`: as for
      `emitS`/`emitU`. The cost note `emitM_exact_prefix`: an exact added fact is emitted only
      from a chain at or above its path, so the prefix walk alone is complete for it
      (`emit_complete_M_exact`, `emit_lookup_equiv_M_exact`, `initR_premise_equiv_M_exact`,
      `emitM_exact_cost`). The version-3 tables have the same property
      (`emitS_exact_prefix`, `emitU_exact_prefix`). A `*` or an `[any]` added fact needs the
      subtree half (§4.4, checked). The lookup equivalences are on membership: the index
      gives the facts in another order than the scan (§4.4, checked).

  All proofs are constructive (only `propext` and `Quot.sound`).
-/
import ApSpec.Restricted
import ApSpec.Store
import ApSpec.Tree

namespace ApSpec.RStore
open ApSpec

/-! ## 0. Related paths -/

/-- The path `p` is a prefix of `q`, or `q` is a prefix of `p`. -/
def nearB (p q : List Acc) : Bool := (dropPrefix p q).isSome || (dropPrefix q p).isSome

theorem nearB_iff {p q : List Acc} :
    nearB p q = true ↔ (∃ s, q = p ++ s) ∨ (∃ s, p = q ++ s) := by
  unfold nearB
  rw [Bool.or_eq_true, Store.dropPrefix_isSome_iff, Store.dropPrefix_isSome_iff]

/-- `relate` is not `.apart` exactly for the related paths. -/
theorem relate_ne_apart_iff {p q : List Acc} : relate p q ≠ .apart ↔ nearB p q = true := by
  unfold nearB relate
  cases h1 : dropPrefix p q with
  | some r => exact ⟨fun _ => rfl, fun _ h => nomatch h⟩
  | none =>
    cases h2 : dropPrefix q p with
    | some r => exact ⟨fun _ => rfl, fun _ h => nomatch h⟩
    | none => exact ⟨fun h => absurd rfl h, fun h => nomatch h⟩

#print axioms relate_ne_apart_iff

theorem relate_ne_apart_iff' {p q : List Acc} :
    relate p q ≠ .apart ↔ (∃ s, q = p ++ s) ∨ (∃ s, p = q ++ s) :=
  relate_ne_apart_iff.trans nearB_iff

/-! ## 1. The path trie: the node at a key, and the subtree below it

The query of a demand store walks the key path of `q` (the prefix half) and then lists the
subtree BELOW the node at `q` (the extension half). The helpers below give the node at a key
(`fTarget`, `mTarget`), its values (`tV`) and its children (`tK`), the entries of a trie
(`fEnts`, `mEnts`), and the node count (`fNodes`).

Cost model (as `Store.prefHits`): one unit per trie node that the query visits; a node finds
its child in one step (a hashed child map; design note N4 of Store.lean gives the sibling
scan of the left-child / right-sibling encoding). -/

section Trie
variable {β : Type}
open Store

/-- The number of nodes of a forest. -/
def fNodes : Forest β → Nat
  | .nil => 0
  | .cons _ _ k r => 1 + fNodes k + fNodes r

def fIsNil : Forest β → Bool
  | .nil => true
  | .cons _ _ _ _ => false

/-- Every node holds a value or has a child (no dead branch). `fromList` gives such tries. -/
def fPruned : Forest β → Bool
  | .nil => true
  | .cons _ vs k r => (!vs.isEmpty || !fIsNil k) && fPruned k && fPruned r

/-- The entries of a forest: (relative key, value). Every key starts with the accessor of
    a top node. -/
def fEnts : Forest β → List (List Acc × β)
  | .nil => []
  | .cons a vs k r =>
    vs.map (fun v => ([a], v)) ++ (fEnts k).map (fun e => (a :: e.1, e.2)) ++ fEnts r

/-- The sum of the key lengths. -/
def keySum : List (List Acc × β) → Nat
  | []      => 0
  | e :: es => e.1.length + keySum es

/-- The node at the key `a :: q`: its values and its children. -/
def fTarget : Forest β → Acc → List Acc → Option (List β × Forest β)
  | .nil, _, _ => none
  | .cons b vs k r, a, q =>
    if a = b then
      match q with
      | []      => some (vs, k)
      | c :: q' => fTarget k c q'
    else fTarget r a q

/-- The values of an optional target node. -/
def optV : Option (List β × Forest β) → List β
  | none => []
  | some (vs, _) => vs

/-- The children of an optional target node. -/
def optK : Option (List β × Forest β) → Forest β
  | none => .nil
  | some (_, k) => k

theorem fExt_target : ∀ {f : Forest β} {a : Acc} {q : List Acc},
    f.extensions a q = optV (fTarget f a q) ++ (optK (fTarget f a q)).all
  | .nil, _, _ => rfl
  | .cons b vs k r, a, q => by
    by_cases h : a = b
    · cases q with
      | nil => simp only [Forest.extensions, fTarget, h, ↓reduceIte, optV, optK]
      | cons c q' =>
        simp only [Forest.extensions, fTarget, h, ↓reduceIte]
        exact fExt_target
    · simp only [Forest.extensions, fTarget, h, ↓reduceIte]
      exact fExt_target

theorem fAll_ents : ∀ {f : Forest β}, f.all = (fEnts f).map (·.2)
  | .nil => rfl
  | .cons a vs k r => by
    show vs ++ k.all ++ r.all = _
    simp only [fEnts, List.map_append, List.map_map]
    rw [fAll_ents (f := k), fAll_ents (f := r)]
    have h1 : ((·.2) ∘ fun v => (([a] : List Acc), v)) = (id : β → β) := rfl
    have h2 : ((·.2) ∘ fun (e : List Acc × β) => (a :: e.1, e.2)) = (·.2) := rfl
    rw [h1, h2, List.map_id]

theorem fEnts_key_ne_nil : ∀ {f : Forest β} {e : List Acc × β}, e ∈ fEnts f → e.1 ≠ []
  | .nil, _, h => nomatch h
  | .cons a vs k r, e, h => by
    simp only [fEnts, List.mem_append, List.mem_map] at h
    rcases h with (⟨v, _, rfl⟩ | ⟨e', _, rfl⟩) | h
    · exact fun h => nomatch h
    · exact fun h => nomatch h
    · exact fEnts_key_ne_nil h

theorem keySum_append : ∀ {xs ys : List (List Acc × β)}, keySum (xs ++ ys) = keySum xs + keySum ys
  | [], _ => by simp only [List.nil_append, keySum]; omega
  | x :: xs, ys => by
    simp only [List.cons_append, keySum]
    rw [keySum_append]; omega

theorem keySum_single {a : Acc} : ∀ {vs : List β}, keySum (vs.map (fun v => ([a], v))) = vs.length
  | [] => rfl
  | v :: vs => by
    simp only [List.map_cons, keySum, List.length_cons, List.length_nil]
    rw [keySum_single]; omega

theorem keySum_cons {a : Acc} : ∀ {es : List (List Acc × β)},
    keySum (es.map (fun e => (a :: e.1, e.2))) = es.length + keySum es
  | [] => rfl
  | e :: es => by
    simp only [List.map_cons, keySum, List.length_cons]
    rw [keySum_cons]; omega

theorem fPruned_cons {a : Acc} {vs : List β} {k r : Forest β} :
    fPruned (.cons a vs k r) = true ↔
      (vs.isEmpty = false ∨ fIsNil k = false) ∧ fPruned k = true ∧ fPruned r = true := by
  show ((!vs.isEmpty || !fIsNil k) && fPruned k && fPruned r) = true ↔ _
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.not_eq_true',
    and_assoc]

/-- A pruned non-empty forest has an entry. -/
theorem fPruned_ents : ∀ {f : Forest β}, fPruned f = true → fIsNil f = false →
    1 ≤ (fEnts f).length
  | .nil, _, h => nomatch h
  | .cons a vs k r, hp, _ => by
    have ⟨h1, h2, _⟩ := fPruned_cons.mp hp
    simp only [fEnts, List.length_append, List.length_map]
    rcases h1 with h1 | h1
    · cases vs with
      | nil => exact nomatch h1
      | cons v vs => simp only [List.length_cons]; omega
    · have := fPruned_ents h2 h1
      omega

/-- In a pruned forest, the nodes are at most the sum of the key lengths of the entries:
    each node is one accessor of the key of an entry at or below it. -/
theorem fNodes_le : ∀ {f : Forest β}, fPruned f = true → fNodes f ≤ keySum (fEnts f)
  | .nil, _ => Nat.le_refl _
  | .cons a vs k r, hp => by
    have ⟨h1, h2, h3⟩ := fPruned_cons.mp hp
    have ik := fNodes_le h2
    have ir := fNodes_le h3
    have hone : 1 ≤ vs.length + (fEnts k).length := by
      rcases h1 with h1 | h1
      · cases vs with
        | nil => exact nomatch h1
        | cons v vs => simp only [List.length_cons]; omega
      · have := fPruned_ents h2 h1
        omega
    simp only [fNodes, fEnts, keySum_append, keySum_single, keySum_cons]
    omega

theorem fTarget_pruned : ∀ {f : Forest β} {a : Acc} {q : List Acc} {vs : List β} {k : Forest β},
    fPruned f = true → fTarget f a q = some (vs, k) → fPruned k = true
  | .nil, _, _, _, _, _, h => nomatch h
  | .cons b vs' k' r, a, q, vs, k, hp, h => by
    have ⟨_, h2, h3⟩ := fPruned_cons.mp hp
    by_cases hab : a = b
    · cases q with
      | nil =>
        simp only [fTarget, hab, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact h2
      | cons c q' =>
        simp only [fTarget, hab, ↓reduceIte] at h
        exact fTarget_pruned h2 h
    · simp only [fTarget, hab, ↓reduceIte] at h
      exact fTarget_pruned h3 h

/-- The entries of the target node are entries of the forest, below the key `a :: q`. -/
theorem fTarget_ents : ∀ {f : Forest β} {a : Acc} {q : List Acc} {vs : List β} {k : Forest β},
    fTarget f a q = some (vs, k) →
      (∀ v, v ∈ vs → (a :: q, v) ∈ fEnts f) ∧
      (∀ e, e ∈ fEnts k → (a :: (q ++ e.1), e.2) ∈ fEnts f)
  | .nil, _, _, _, _, h => nomatch h
  | .cons b vs' k' r, a, q, vs, k, h => by
    by_cases hab : a = b
    · subst hab
      cases q with
      | nil =>
        simp only [fTarget, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨fun v hv => ?_, fun e he => ?_⟩
        · simp only [fEnts, List.mem_append, List.mem_map]
          exact Or.inl (Or.inl ⟨v, hv, rfl⟩)
        · simp only [fEnts, List.mem_append, List.mem_map, List.nil_append]
          exact Or.inl (Or.inr ⟨e, he, rfl⟩)
      | cons c q' =>
        simp only [fTarget, ↓reduceIte] at h
        have ⟨i1, i2⟩ := fTarget_ents h
        refine ⟨fun v hv => ?_, fun e he => ?_⟩
        · simp only [fEnts, List.mem_append, List.mem_map]
          exact Or.inl (Or.inr ⟨_, i1 v hv, rfl⟩)
        · simp only [fEnts, List.mem_append, List.mem_map]
          exact Or.inl (Or.inr ⟨_, i2 e he, rfl⟩)
    · simp only [fTarget, hab, ↓reduceIte] at h
      have ⟨i1, i2⟩ := fTarget_ents h
      refine ⟨fun v hv => ?_, fun e he => ?_⟩
      · simp only [fEnts, List.mem_append]; exact Or.inr (i1 v hv)
      · simp only [fEnts, List.mem_append]; exact Or.inr (i2 e he)

/-! #### `fromList` gives a pruned trie, and its entries are the records -/

theorem fIsNil_single {a : Acc} {v : β} : ∀ {p : List Acc}, fIsNil (Forest.single a p v) = false
  | [] => rfl
  | _ :: _ => rfl

theorem fPruned_single {v : β} : ∀ {p : List Acc} {a : Acc}, fPruned (Forest.single a p v) = true
  | [], _ => rfl
  | c :: p, a => by
    show fPruned (Forest.cons a [] (Forest.single c p v) .nil) = true
    refine fPruned_cons.mpr ⟨Or.inr fIsNil_single, fPruned_single, rfl⟩

theorem fIsNil_ins {v : β} : ∀ {f : Forest β} {a : Acc} {p : List Acc}, fIsNil (f.ins a p v) = false
  | .nil, _, _ => fIsNil_single
  | .cons b vs k r, a, p => by
    by_cases h : a = b
    · cases p with
      | nil => simp only [Forest.ins, h, ↓reduceIte]; rfl
      | cons c p' => simp only [Forest.ins, h, ↓reduceIte]; rfl
    · simp only [Forest.ins, h, ↓reduceIte]; rfl

theorem fPruned_ins {v : β} : ∀ {f : Forest β} {a : Acc} {p : List Acc},
    fPruned f = true → fPruned (f.ins a p v) = true
  | .nil, _, _, _ => fPruned_single
  | .cons b vs k r, a, p, hp => by
    have ⟨h1, h2, h3⟩ := fPruned_cons.mp hp
    by_cases h : a = b
    · cases p with
      | nil =>
        simp only [Forest.ins, h, ↓reduceIte]
        exact fPruned_cons.mpr ⟨Or.inl rfl, h2, h3⟩
      | cons c p' =>
        simp only [Forest.ins, h, ↓reduceIte]
        exact fPruned_cons.mpr ⟨Or.inr fIsNil_ins, fPruned_ins h2, h3⟩
    · simp only [Forest.ins, h, ↓reduceIte]
      exact fPruned_cons.mpr ⟨h1, h2, fPruned_ins h3⟩

theorem fromList_pruned : ∀ (es : List (List Acc × β)), fPruned (PathMap.fromList es).kids = true
  | [] => rfl
  | (k, v) :: es => by
    show fPruned ((PathMap.fromList es).insert k v).kids = true
    cases k with
    | nil => exact fromList_pruned es
    | cons a p => exact fPruned_ins (fromList_pruned es)

theorem fEnts_single {v : β} : ∀ {p : List Acc} {a : Acc}, fEnts (Forest.single a p v) = [(a :: p, v)]
  | [], _ => rfl
  | c :: p, a => by
    show [] ++ (fEnts (Forest.single c p v)).map (fun e => (a :: e.1, e.2)) ++ [] = _
    rw [fEnts_single]; rfl

theorem mem_map_pair {a : Acc} {A B : List (List Acc × β)} {y : List Acc × β}
    (h : ∀ x, x ∈ A ↔ x = y ∨ x ∈ B) (z : List Acc × β) :
    z ∈ A.map (fun e => (a :: e.1, e.2)) ↔
      z = (a :: y.1, y.2) ∨ z ∈ B.map (fun e => (a :: e.1, e.2)) := by
  rw [List.mem_map, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (h x).mp hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact ⟨y, (h y).mpr (Or.inl rfl), rfl⟩
    · exact ⟨x, (h x).mpr (Or.inr hx), rfl⟩

theorem fEnts_ins {v : β} : ∀ {f : Forest β} {a : Acc} {p : List Acc} (e : List Acc × β),
    e ∈ fEnts (f.ins a p v) ↔ e = (a :: p, v) ∨ e ∈ fEnts f
  | .nil, a, p, e => by
    show e ∈ fEnts (Forest.single a p v) ↔ _
    rw [fEnts_single, List.mem_singleton]
    exact ⟨Or.inl, fun h => h.elim id (fun h => nomatch h)⟩
  | .cons b vs k r, a, p, e => by
    by_cases h : a = b
    · subst h
      cases p with
      | nil =>
        simp only [Forest.ins, ↓reduceIte, fEnts, List.map_cons, List.cons_append, List.mem_cons]
      | cons c p' =>
        simp only [Forest.ins, ↓reduceIte, fEnts, List.mem_append]
        rw [mem_map_pair (fEnts_ins (f := k) (a := c) (p := p'))]
        constructor
        · rintro ((h | h | h) | h)
          · exact Or.inr (Or.inl (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (Or.inl (Or.inr h))
          · exact Or.inr (Or.inr h)
        · rintro (h | (h | h) | h)
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr (Or.inr h))
          · exact Or.inr h
    · simp only [Forest.ins, h, ↓reduceIte, fEnts, List.mem_append]
      rw [fEnts_ins (f := r)]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- The entries of a path trie: (key, value). -/
def mEnts (m : PathMap β) : List (List Acc × β) := m.vals.map (fun v => ([], v)) ++ fEnts m.kids

theorem mEnts_fromList : ∀ {es : List (List Acc × β)} (e : List Acc × β),
    e ∈ mEnts (PathMap.fromList es) ↔ e ∈ es
  | [], e => by
    show e ∈ ([] : List (List Acc × β)) ↔ _
    exact Iff.rfl
  | (k, v) :: es, e => by
    show e ∈ mEnts ((PathMap.fromList es).insert k v) ↔ _
    rw [List.mem_cons]
    cases k with
    | nil =>
      show e ∈ (v :: (PathMap.fromList es).vals).map (fun v => ([], v)) ++
        fEnts (PathMap.fromList es).kids ↔ _
      rw [List.map_cons, List.cons_append, List.mem_cons]
      have ih := mEnts_fromList (es := es) e
      unfold mEnts at ih
      rw [ih]
    | cons a p =>
      show e ∈ (PathMap.fromList es).vals.map (fun v => ([], v)) ++
        fEnts ((PathMap.fromList es).kids.ins a p v) ↔ _
      have ih := mEnts_fromList (es := es) e
      unfold mEnts at ih
      rw [List.mem_append, fEnts_ins, ← ih, List.mem_append]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- The node at the key `q` of a path trie. -/
def mTarget (m : PathMap β) : List Acc → Option (List β × Forest β)
  | []     => some (m.vals, m.kids)
  | a :: q => fTarget m.kids a q

/-- The values at `q`, and the children of the node at `q` (empty if there is no node). -/
def tV (m : PathMap β) (q : List Acc) : List β := optV (mTarget m q)

def tK (m : PathMap β) (q : List Acc) : Forest β := optK (mTarget m q)

theorem mExt_eq (m : PathMap β) (q : List Acc) :
    m.lookupExtensions q = tV m q ++ (fEnts (tK m q)).map (·.2) := by
  rw [← fAll_ents]
  cases q with
  | nil => rfl
  | cons a q =>
    show m.kids.extensions a q = optV (fTarget m.kids a q) ++ (optK (fTarget m.kids a q)).all
    exact fExt_target

theorem tK_pruned (m : PathMap β) (hm : fPruned m.kids = true) (q : List Acc) :
    fPruned (tK m q) = true := by
  cases q with
  | nil => exact hm
  | cons a q =>
    show fPruned (optK (fTarget m.kids a q)) = true
    cases h : fTarget m.kids a q with
    | none => rfl
    | some p => obtain ⟨vs, k⟩ := p; exact fTarget_pruned hm h

theorem tK_ents (m : PathMap β) (q : List Acc) (e : List Acc × β) (he : e ∈ fEnts (tK m q)) :
    (q ++ e.1, e.2) ∈ mEnts m := by
  cases q with
  | nil => exact List.mem_append_right _ he
  | cons a q =>
    have he' : e ∈ fEnts (optK (fTarget m.kids a q)) := he
    revert he'
    cases h : fTarget m.kids a q with
    | none => intro he'; exact nomatch he'
    | some p =>
      obtain ⟨vs, k⟩ := p
      intro he'
      exact List.mem_append_right _ ((fTarget_ents h).2 e he')

theorem tV_ents (m : PathMap β) (q : List Acc) (v : β) (hv : v ∈ tV m q) : (q, v) ∈ mEnts m := by
  cases q with
  | nil => exact List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
  | cons a q =>
    have hv' : v ∈ optV (fTarget m.kids a q) := hv
    revert hv'
    cases h : fTarget m.kids a q with
    | none => intro hv'; exact nomatch hv'
    | some p =>
      obtain ⟨vs, k⟩ := p
      intro hv'
      exact List.mem_append_right _ ((fTarget_ents h).1 v hv')

end Trie

/-! ## 2. The demand store and the query `near` -/

/-- The demand index of one method: a path trie keyed by the entry chain `din.path`. -/
def demandIdx (ds : List DemandEdge) : Store.PathMap DemandEdge :=
  Store.indexBy (fun d => d.din.path) ds

/-- The query of a path index: the prefix walk of `q` (the records at `q` and above), and
    the subtree strictly below the node at `q`. Unlike `Store.around`, a record at `q` is
    not returned twice (design note N1 of Store.lean). -/
def nearBy {ρ : Type} (key : ρ → List Acc) (rs : List ρ) (q : List Acc) : List ρ :=
  (Store.indexBy key rs).lookupPrefixes q ++ (fEnts (tK (Store.indexBy key rs) q)).map (·.2)

/-- The INDEX query of the demand store. -/
def near (ds : List DemandEdge) (q : List Acc) : List DemandEdge :=
  nearBy (fun d => d.din.path) ds q

/-- The CONCEPT: the list filter. -/
def nearL (ds : List DemandEdge) (q : List Acc) : List DemandEdge :=
  ds.filter (fun d => nearB d.din.path q)

/-- The candidates of the emission lookup for the added fact `a`. -/
def emitCands (ds : List DemandEdge) (a : PFact) : List DemandEdge := near ds a.path

/-- The candidates of the restriction lookup for the summary premise `j`. -/
def restrictCands (ds : List DemandEdge) (j : PFact) : List DemandEdge := near ds j.path

/-- The values at the node `q` are on the prefix walk of `q`. -/
theorem tV_mem_prefixes {β : Type} {es : List (List Acc × β)} {q : List Acc} {v : β}
    (h : v ∈ tV (Store.PathMap.fromList es) q) : v ∈ (Store.PathMap.fromList es).lookupPrefixes q := by
  refine Store.PathMap.mem_lookupPrefixes_fromList.mpr ⟨q, ?_, [], (List.append_nil q).symm⟩
  exact (mEnts_fromList (q, v)).mp (tV_ents _ q v h)

/-- The query `nearBy` and the query `Store.around` give the same records. -/
theorem nearBy_iff_around {ρ : Type} {key : ρ → List Acc} {rs : List ρ} {q : List Acc} {x : ρ} :
    x ∈ nearBy key rs q ↔ x ∈ Store.around (Store.indexBy key rs) q := by
  unfold nearBy Store.around
  rw [mExt_eq, List.mem_append, List.mem_append, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inl (tV_mem_prefixes h)
    · exact Or.inr h

theorem mem_near {ds : List DemandEdge} {q : List Acc} {d : DemandEdge} :
    d ∈ near ds q ↔ d ∈ ds ∧ relate d.din.path q ≠ .apart := by
  unfold near
  rw [nearBy_iff_around, Store.mem_around_indexBy, relate_ne_apart_iff']

/-- SOUNDNESS. Every candidate is a demand edge of the method, and its entry chain is
    related to the query path (a prefix or an extension). -/
theorem near_sound {ds : List DemandEdge} {q : List Acc} {d : DemandEdge}
    (h : d ∈ near ds q) : d ∈ ds ∧ relate d.din.path q ≠ .apart :=
  mem_near.mp h

#print axioms near_sound

/-- Index = concept (membership). -/
theorem near_equiv {ds : List DemandEdge} {q : List Acc} {d : DemandEdge} :
    d ∈ near ds q ↔ d ∈ nearL ds q := by
  rw [mem_near, nearL, List.mem_filter, relate_ne_apart_iff]

#print axioms near_equiv

/-! ### 2.1 The emission lookup -/

/-- An emission that gives a fact only for a related chain on the same base. -/
def EmitLocal (emit : PFact → PFact → Option PFact) : Prop :=
  ∀ d a j, emit d a = some j → d.base = a.base ∧ relate d.path a.path ≠ .apart

theorem emitS_local : EmitLocal emitS := by
  intro d a j h
  unfold emitS at h
  cases hb : Nat.beq d.base a.base with
  | false => rw [hb] at h; exact nomatch h
  | true =>
    rw [hb, if_pos rfl] at h
    refine ⟨Nat.eq_of_beq_eq_true hb, ?_⟩
    intro hr
    rw [hr] at h
    exact nomatch h

theorem emitU_local : EmitLocal emitU := by
  intro d a j h
  unfold emitU at h
  cases hb : Nat.beq d.base a.base with
  | false => rw [hb] at h; exact nomatch h
  | true =>
    rw [hb, if_pos rfl] at h
    refine ⟨Nat.eq_of_beq_eq_true hb, ?_⟩
    intro hr
    rw [hr] at h
    exact nomatch h

#print axioms emitS_local
#print axioms emitU_local

/-- SOUNDNESS of the emission candidates. -/
theorem emitCands_sound {ds : List DemandEdge} {a : PFact} {d : DemandEdge}
    (h : d ∈ emitCands ds a) : d ∈ ds ∧ relate d.din.path a.path ≠ .apart :=
  mem_near.mp h

#print axioms emitCands_sound

/-- COMPLETENESS (generic). -/
theorem emit_complete {emit : PFact → PFact → Option PFact} (he : EmitLocal emit)
    {ds : List DemandEdge} {a j : PFact} {d : DemandEdge}
    (hd : d ∈ ds) (h : emit d.din a = some j) : d ∈ emitCands ds a :=
  mem_near.mpr ⟨hd, (he _ _ _ h).2⟩

/-- COMPLETENESS of the emission lookup, sound rules. -/
theorem emit_complete_S {ds : List DemandEdge} {a j : PFact} {d : DemandEdge}
    (hd : d ∈ ds) (h : emitS d.din a = some j) : d ∈ emitCands ds a :=
  emit_complete emitS_local hd h

/-- COMPLETENESS of the emission lookup, agreed rules. -/
theorem emit_complete_U {ds : List DemandEdge} {a j : PFact} {d : DemandEdge}
    (hd : d ∈ ds) (h : emitU d.din a = some j) : d ∈ emitCands ds a :=
  emit_complete emitU_local hd h

#print axioms emit_complete_S
#print axioms emit_complete_U

/-- Index = concept for the emitted facts (generic). -/
theorem emit_lookup_equiv {emit : PFact → PFact → Option PFact} (he : EmitLocal emit)
    {ds : List DemandEdge} {a j : PFact} :
    j ∈ (emitCands ds a).filterMap (fun d => emit d.din a) ↔
      j ∈ ds.filterMap (fun d => emit d.din a) := by
  rw [List.mem_filterMap, List.mem_filterMap]
  constructor
  · intro ⟨d, hd, h⟩; exact ⟨d, (mem_near.mp hd).1, h⟩
  · intro ⟨d, hd, h⟩; exact ⟨d, emit_complete he hd h, h⟩

/-- FUNCTIONAL EQUIVALENCE, emission, sound rules: the index gives the same initial facts
    as the scan of all demand edges of the method. -/
theorem emit_lookup_equiv_S {ds : List DemandEdge} {a j : PFact} :
    j ∈ (emitCands ds a).filterMap (fun d => emitS d.din a) ↔
      j ∈ ds.filterMap (fun d => emitS d.din a) :=
  emit_lookup_equiv emitS_local

theorem emit_lookup_equiv_U {ds : List DemandEdge} {a j : PFact} :
    j ∈ (emitCands ds a).filterMap (fun d => emitU d.din a) ↔
      j ∈ ds.filterMap (fun d => emitU d.din a) :=
  emit_lookup_equiv emitU_local

#print axioms emit_lookup_equiv_S
#print axioms emit_lookup_equiv_U

/-- The premise of rule `initR` (`demand m d ∧ emit d.din a = some j`), with the demand
    of the method stored as the list `ds`: the index answers it. -/
theorem initR_premise_equiv {emit : PFact → PFact → Option PFact} (he : EmitLocal emit)
    {ds : List DemandEdge} {a j : PFact} :
    (∃ d, d ∈ ds ∧ emit d.din a = some j) ↔ (∃ d, d ∈ emitCands ds a ∧ emit d.din a = some j) :=
  ⟨fun ⟨d, hd, h⟩ => ⟨d, emit_complete he hd h, h⟩,
   fun ⟨d, hd, h⟩ => ⟨d, (mem_near.mp hd).1, h⟩⟩

#print axioms initR_premise_equiv

/-! ### 2.2 The restriction lookup -/

theorem overlapB_near {j d : PFact} (h : overlapB j d = true) :
    j.base = d.base ∧ relate d.path j.path ≠ .apart := by
  have ⟨hb, hp⟩ := Store.overlapB_parts h
  refine ⟨hb, relate_ne_apart_iff'.mpr ?_⟩
  rcases hp with hp | hp
  · exact Or.inr hp
  · exact Or.inl hp

/-- A restriction gives an edge only if the demand edge has an exit pattern and its entry
    pattern overlaps the summary premise. -/
theorem restrictWith_some {rc : AFact → PFact → Option AFact} {j : PFact} {g g' : AFact}
    {d : DemandEdge} (h : restrictWith rc j g d = some g') :
    overlapB j d.din = true ∧ ∃ p, d.dout = some p ∧ rc g p = some g' := by
  unfold restrictWith at h
  cases hd : d.dout with
  | none => rw [hd] at h; exact nomatch h
  | some p =>
    have h' : (if overlapB j d.din = true then rc g p else none) = some g' := by
      rw [hd] at h; exact h
    cases ho : overlapB j d.din with
    | false => rw [ho] at h'; exact nomatch h'
    | true => rw [ho, if_pos rfl] at h'; exact ⟨rfl, p, rfl, h'⟩

#print axioms restrictWith_some

/-- SOUNDNESS of the restriction candidates. -/
theorem restrictCands_sound {ds : List DemandEdge} {j : PFact} {d : DemandEdge}
    (h : d ∈ restrictCands ds j) : d ∈ ds ∧ relate d.din.path j.path ≠ .apart :=
  mem_near.mp h

#print axioms restrictCands_sound

/-- COMPLETENESS (generic). -/
theorem restrict_complete {rc : AFact → PFact → Option AFact} {ds : List DemandEdge}
    {j : PFact} {g g' : AFact} {d : DemandEdge}
    (hd : d ∈ ds) (h : restrictWith rc j g d = some g') : d ∈ restrictCands ds j :=
  mem_near.mpr ⟨hd, (overlapB_near (restrictWith_some h).1).2⟩

/-- COMPLETENESS of the restriction lookup, sound rules. -/
theorem restrict_complete_S {ds : List DemandEdge} {j : PFact} {g g' : AFact} {d : DemandEdge}
    (hd : d ∈ ds) (h : restrictS j g d = some g') : d ∈ restrictCands ds j :=
  restrict_complete hd h

/-- COMPLETENESS of the restriction lookup, agreed rules. -/
theorem restrict_complete_U {ds : List DemandEdge} {j : PFact} {g g' : AFact} {d : DemandEdge}
    (hd : d ∈ ds) (h : restrictU j g d = some g') : d ∈ restrictCands ds j :=
  restrict_complete hd h

#print axioms restrict_complete_S
#print axioms restrict_complete_U

/-- Index = concept for the restricted edges (generic). -/
theorem restrict_lookup_equiv {rc : AFact → PFact → Option AFact} {ds : List DemandEdge}
    {j : PFact} {g g' : AFact} :
    g' ∈ (restrictCands ds j).filterMap (fun d => restrictWith rc j g d) ↔
      g' ∈ ds.filterMap (fun d => restrictWith rc j g d) := by
  rw [List.mem_filterMap, List.mem_filterMap]
  constructor
  · intro ⟨d, hd, h⟩; exact ⟨d, (mem_near.mp hd).1, h⟩
  · intro ⟨d, hd, h⟩; exact ⟨d, restrict_complete hd h, h⟩

/-- FUNCTIONAL EQUIVALENCE, restriction, sound rules. -/
theorem restrict_lookup_equiv_S {ds : List DemandEdge} {j : PFact} {g g' : AFact} :
    g' ∈ (restrictCands ds j).filterMap (fun d => restrictS j g d) ↔
      g' ∈ ds.filterMap (fun d => restrictS j g d) :=
  restrict_lookup_equiv

theorem restrict_lookup_equiv_U {ds : List DemandEdge} {j : PFact} {g g' : AFact} :
    g' ∈ (restrictCands ds j).filterMap (fun d => restrictU j g d) ↔
      g' ∈ ds.filterMap (fun d => restrictU j g d) :=
  restrict_lookup_equiv

#print axioms restrict_lookup_equiv_S
#print axioms restrict_lookup_equiv_U

/-- The premise of rule `ret` (`demand m d ∧ restrict j g d = some g'`): the index answers it. -/
theorem ret_premise_equiv {rc : AFact → PFact → Option AFact} {ds : List DemandEdge}
    {j : PFact} {g g' : AFact} :
    (∃ d, d ∈ ds ∧ restrictWith rc j g d = some g') ↔
      (∃ d, d ∈ restrictCands ds j ∧ restrictWith rc j g d = some g') :=
  ⟨fun ⟨d, hd, h⟩ => ⟨d, restrict_complete hd h, h⟩,
   fun ⟨d, hd, h⟩ => ⟨d, (mem_near.mp hd).1, h⟩⟩

#print axioms ret_premise_equiv

/-! ### 2.3 The base-keyed index (design note N2 of Store.lean)

With the key `din.path` alone, a root query (`q = []`) gets every demand edge of the
method in its extension half. The key `base :: path` keeps the completeness. -/

def nearK (ds : List DemandEdge) (f : PFact) : List DemandEdge :=
  nearBy (fun d => Store.keyB d.din) ds (Store.keyB f)

theorem nearK_of {ds : List DemandEdge} {f : PFact} {d : DemandEdge} (hd : d ∈ ds)
    (hb : d.din.base = f.base) (hr : relate d.din.path f.path ≠ .apart) : d ∈ nearK ds f := by
  unfold nearK
  refine nearBy_iff_around.mpr (Store.mem_around_indexBy.mpr ⟨hd, ?_⟩)
  rcases relate_ne_apart_iff'.mp hr with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inl ⟨s, by simp only [Store.keyB, hb, hs, List.cons_append]⟩
  · exact Or.inr ⟨s, by simp only [Store.keyB, hb, hs, List.cons_append]⟩

theorem emit_completeK {emit : PFact → PFact → Option PFact} (he : EmitLocal emit)
    {ds : List DemandEdge} {a j : PFact} {d : DemandEdge}
    (hd : d ∈ ds) (h : emit d.din a = some j) : d ∈ nearK ds a :=
  nearK_of hd (he _ _ _ h).1 (he _ _ _ h).2

theorem restrict_completeK {rc : AFact → PFact → Option AFact} {ds : List DemandEdge}
    {j : PFact} {g g' : AFact} {d : DemandEdge}
    (hd : d ∈ ds) (h : restrictWith rc j g d = some g') : d ∈ nearK ds j :=
  have ho := overlapB_near (restrictWith_some h).1
  nearK_of hd ho.1.symm ho.2

#print axioms emit_completeK
#print axioms restrict_completeK


/-! ### 2.4 The cost of the query -/

/-- The nodes that `near` visits: the key path of `q`, then every node of the subtree below
    the node at `q` (one walk; the prefix walk ends at that node). -/
def nearVisits (ds : List DemandEdge) (q : List Acc) : Nat :=
  (demandIdx ds).prefHits q + fNodes (tK (demandIdx ds) q)

/-- COST of the demand query `near ds q` (emission: `q = a.path`; restriction: `q = j.path`).
    (1) The prefix walk visits at most `|q| + 1` nodes.
    (2) The whole query visits at most `|q| + 1 + Σ |rel|` nodes. The sum runs over the
        edges that the query returns strictly below `q`: `din.path = q ++ rel`, `rel ≠ []`
        (3, 4). So it pays one node per accessor of a RETURNED chain below `q`, and no node
        for an edge that it does not return.
    (5) The list concept tests every demand edge of the method: `|ds|` tests.
    The bound is not `|q| + 1 + (number returned)`: a trie node holds ONE accessor, so a
    long chain below `q` costs its length (`deep_chain_cost`). A path-compressed (radix)
    trie would give that bound; the `PathMap` of Store.lean is not compressed. -/
theorem near_query_cost (ds : List DemandEdge) (q : List Acc) :
    (demandIdx ds).prefHits q ≤ q.length + 1 ∧
    nearVisits ds q ≤ q.length + 1 + keySum (fEnts (tK (demandIdx ds) q)) ∧
    near ds q = (demandIdx ds).lookupPrefixes q ++ (fEnts (tK (demandIdx ds) q)).map (·.2) ∧
    (∀ e, e ∈ fEnts (tK (demandIdx ds) q) → e.2 ∈ ds ∧ e.2.din.path = q ++ e.1 ∧ e.1 ≠ []) ∧
    (Store.filterCount (fun d => nearB d.din.path q) ds).2 = ds.length := by
  refine ⟨Store.PathMap.prefHits_le, ?_, rfl, ?_, Store.filterCount_snd⟩
  · have h1 := Store.PathMap.prefHits_le (m := demandIdx ds) (q := q)
    have h2 := fNodes_le (tK_pruned (demandIdx ds) (fromList_pruned _) q)
    unfold nearVisits
    omega
  · intro e he
    have h1 := tK_ents (demandIdx ds) q e he
    unfold demandIdx Store.indexBy at h1
    rw [mEnts_fromList] at h1
    have ⟨hx, hk⟩ := Store.mem_map_key.mp h1
    exact ⟨hx, hk.symm, fEnts_key_ne_nil he⟩

#print axioms near_query_cost

/-- The counterexample to the bound "walk + number returned": one demand edge with an entry
    chain of 8 accessors. The root query returns 1 edge and visits 9 nodes; the bound
    `|q| + 1 + 1` would be 2. The proved bound `|q| + 1 + Σ |rel|` is 9. -/
def deepEdge : DemandEdge := ⟨⟨1, [1, 2, 3, 4, 5, 6, 7, 8], .star Excl.empty, .star⟩, none⟩

theorem deep_chain_cost :
    (near [deepEdge] []).length = 1 ∧
    nearVisits [deepEdge] [] = 9 ∧
    keySum (fEnts (tK (demandIdx [deepEdge]) [])) = 8 := by decide

#print axioms deep_chain_cost

/-! ### 2.5 The emission of version 4 (`emitM`)

`emitM d a` (Restricted.lean §1b) gives a fact only for the same base, a matching mark
(`markMatchB`) and a related chain (`relate ≠ .apart`). So it is local (`emitM_local`), and the
query `near` is complete for it, as for `emitS` and `emitU`.

COST NOTE. For an exact (`$`) added fact, the lookup can skip the subtree half of `near`.
`emitM` emits from a chain BELOW the path of the fact (`relate d.path a.path = .above r`) only
if the tail of the fact admits the rest `r` of the chain. The tail `$` admits only the empty
rest. So only the chains AT or ABOVE the path of an exact fact emit (`emitM_exact_prefix`), and
the prefix walk alone (`nearPre`: at most `|a.path| + 1` nodes, no subtree) is complete
(`emit_complete_M_exact`, `emitM_exact_cost`). The version-3 tables have the same property
(`emitS_exact_prefix`, `emitU_exact_prefix`). A `*` or an `[any]` added fact needs the subtree
half (example in §4.4).

The equivalence of the lookups is on membership: the index and the scan give the same facts,
in a different order (example in §4.4). -/

/-- The path of a `.below` relation. -/
theorem relBelow_path {p q r : List Acc} (h : relate p q = .below r) : q = p ++ r := by
  unfold relate at h
  split at h
  next r' hr => cases h; exact Store.dropPrefix_some hr
  next => split at h <;> cases h

/-- The path of an `.above` relation. -/
theorem relAbove_path {p q r : List Acc} (h : relate p q = .above r) : p = q ++ r := by
  unfold relate at h
  split at h
  next => cases h
  next =>
    split at h
    next r' hr => cases h; exact Store.dropPrefix_some hr
    next => cases h

/-- The cases of a version-4 emission: the base and the mark match, and the chain of `d` is
    at the fact path (the meet of the tails), strictly above it (the whole fact), or strictly
    below it (the chain of `d`, with the mark of `a`). -/
theorem emitM_cases {d a j : PFact} (h : emitM d a = some j) :
    d.base = a.base ∧ markMatchB d.mark a.mark = true ∧
    ((relate d.path a.path = .below [] ∧ j = ⟨a.base, a.path, meetK a.kind d.kind, a.mark⟩) ∨
     (∃ x r, relate d.path a.path = .below (x :: r) ∧ admitsTailB d.kind (x :: r) = true ∧
        j = a) ∨
     (∃ r, relate d.path a.path = .above r ∧ admitsTailB a.kind r = true ∧
        j = ⟨d.base, d.path, d.kind, a.mark⟩)) := by
  unfold emitM at h
  cases hb : Nat.beq d.base a.base with
  | false => rw [hb, Bool.false_and] at h; exact nomatch h
  | true =>
    cases hm : markMatchB d.mark a.mark with
    | false => rw [hb, hm, Bool.true_and] at h; exact nomatch h
    | true =>
      rw [hb, hm, Bool.true_and, if_pos rfl] at h
      refine ⟨Nat.eq_of_beq_eq_true hb, rfl, ?_⟩
      cases hr : relate d.path a.path with
      | below r =>
        rw [hr] at h
        cases r with
        | nil => exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
        | cons x r =>
          have h' : (if admitsTailB d.kind (x :: r) = true then some a else none) = some j := h
          cases ht : admitsTailB d.kind (x :: r) with
          | false => rw [ht] at h'; exact nomatch h'
          | true =>
            rw [ht, if_pos rfl] at h'
            exact Or.inr (Or.inl ⟨x, r, rfl, ht, (Option.some.inj h').symm⟩)
      | above r =>
        rw [hr] at h
        have h' : (if admitsTailB a.kind r = true then
            some (⟨d.base, d.path, d.kind, a.mark⟩ : PFact) else none) = some j := h
        cases ht : admitsTailB a.kind r with
        | false => rw [ht] at h'; exact nomatch h'
        | true =>
          rw [ht, if_pos rfl] at h'
          exact Or.inr (Or.inr ⟨r, rfl, ht, (Option.some.inj h').symm⟩)
      | apart => rw [hr] at h; exact nomatch h

#print axioms emitM_cases

/-- `emitM` gives a fact only for a related chain on the same base. -/
theorem emitM_local : EmitLocal emitM := by
  intro d a j h
  have ⟨hb, _, hc⟩ := emitM_cases h
  refine ⟨hb, ?_⟩
  rcases hc with ⟨hr, _⟩ | ⟨x, r, hr, _⟩ | ⟨r, hr, _⟩ <;> rw [hr] <;> exact fun h => nomatch h

#print axioms emitM_local

/-- COMPLETENESS of the emission lookup, version 4: a demand edge of the store that emits for
    the added fact `a` is a candidate of the query. -/
theorem emit_complete_M {ds : List DemandEdge} {a j : PFact} {d : DemandEdge}
    (h : emitM d.din a = some j) (hd : d ∈ ds) : d ∈ emitCands ds a :=
  emit_complete emitM_local hd h

#print axioms emit_complete_M

/-- COMPLETENESS of the base-keyed emission lookup, version 4. -/
theorem emit_completeK_M {ds : List DemandEdge} {a j : PFact} {d : DemandEdge}
    (h : emitM d.din a = some j) (hd : d ∈ ds) : d ∈ nearK ds a :=
  emit_completeK emitM_local hd h

#print axioms emit_completeK_M

/-- SOUNDNESS of the base-keyed query: every candidate is a demand edge of the store, on the
    base of the query, with a related chain. -/
theorem nearK_sound {ds : List DemandEdge} {f : PFact} {d : DemandEdge} (h : d ∈ nearK ds f) :
    d ∈ ds ∧ d.din.base = f.base ∧ relate d.din.path f.path ≠ .apart := by
  unfold nearK at h
  have ⟨hd, hk⟩ := Store.mem_around_indexBy.mp (nearBy_iff_around.mp h)
  refine ⟨hd, ?_⟩
  simp only [Store.keyB, List.cons_append] at hk
  rcases hk with ⟨s, hs⟩ | ⟨s, hs⟩
  · injection hs with hb hp
    exact ⟨hb.symm, relate_ne_apart_iff'.mpr (Or.inl ⟨s, hp⟩)⟩
  · injection hs with hb hp
    exact ⟨hb, relate_ne_apart_iff'.mpr (Or.inr ⟨s, hp⟩)⟩

#print axioms nearK_sound

/-- FUNCTIONAL EQUIVALENCE, emission, version 4: the index gives the same initial facts as the
    scan of all demand edges of the method. -/
theorem emit_lookup_equiv_M {ds : List DemandEdge} {a j : PFact} :
    j ∈ (emitCands ds a).filterMap (fun d => emitM d.din a) ↔
      j ∈ ds.filterMap (fun d => emitM d.din a) :=
  emit_lookup_equiv emitM_local

#print axioms emit_lookup_equiv_M

/-- FUNCTIONAL EQUIVALENCE, emission, version 4, base-keyed index. -/
theorem emit_lookup_equivK_M {ds : List DemandEdge} {a j : PFact} :
    j ∈ (nearK ds a).filterMap (fun d => emitM d.din a) ↔
      j ∈ ds.filterMap (fun d => emitM d.din a) := by
  rw [List.mem_filterMap, List.mem_filterMap]
  constructor
  · intro ⟨d, hd, h⟩; exact ⟨d, (nearK_sound hd).1, h⟩
  · intro ⟨d, hd, h⟩; exact ⟨d, emit_completeK_M h hd, h⟩

#print axioms emit_lookup_equivK_M

/-- The premise of rule `initR` with `emitM`: the index answers it. -/
theorem initR_premise_equiv_M {ds : List DemandEdge} {a j : PFact} :
    (∃ d, d ∈ ds ∧ emitM d.din a = some j) ↔
      (∃ d, d ∈ emitCands ds a ∧ emitM d.din a = some j) :=
  initR_premise_equiv emitM_local

#print axioms initR_premise_equiv_M

/-! #### The cost of the emission for an exact added fact -/

/-- An emission that gives a fact for an exact added fact only from a chain AT or ABOVE the
    path of the fact. -/
def EmitExactPrefix (emit : PFact → PFact → Option PFact) : Prop :=
  ∀ d a j, a.kind = .exact → emit d a = some j → ∃ r, a.path = d.path ++ r

/-- A `$` tail admits only the empty rest. -/
theorem admitsTailB_exact {r : List Acc} (h : admitsTailB .exact r = true) : r = [] := by
  cases r with
  | nil => rfl
  | cons x r => exact nomatch h

/-- THE COST NOTE for `emitM`: an exact added fact is emitted only from a demand chain at or
    above its path. So the subtree half of `near` can be skipped for it. -/
theorem emitM_exact_prefix {d a j : PFact} (hk : a.kind = .exact) (h : emitM d a = some j) :
    ∃ r, a.path = d.path ++ r := by
  have ⟨_, _, hc⟩ := emitM_cases h
  rcases hc with ⟨hr, _⟩ | ⟨x, r, hr, _⟩ | ⟨r, hr, ht, _⟩
  · exact ⟨[], relBelow_path hr⟩
  · exact ⟨x :: r, relBelow_path hr⟩
  · rw [hk] at ht
    have h0 := admitsTailB_exact ht
    subst h0
    exact ⟨[], by rw [relAbove_path hr, List.append_nil, List.append_nil]⟩

#print axioms emitM_exact_prefix

theorem emitM_exactPrefix : EmitExactPrefix emitM :=
  fun _ _ _ hk h => emitM_exact_prefix hk h

/-- The version-3 table `emitS` has the same property. -/
theorem emitS_exact_prefix : EmitExactPrefix emitS := by
  intro d a j hk h
  unfold emitS at h
  cases hb : Nat.beq d.base a.base with
  | false => rw [hb] at h; exact nomatch h
  | true =>
    rw [hb, if_pos rfl, hk] at h
    cases hr : relate d.path a.path with
    | below r => exact ⟨r, relBelow_path hr⟩
    | above r => rw [hr] at h; exact nomatch h
    | apart => rw [hr] at h; exact nomatch h

/-- The version-3 table `emitU` has the same property. -/
theorem emitU_exact_prefix : EmitExactPrefix emitU := by
  intro d a j hk h
  unfold emitU at h
  cases hb : Nat.beq d.base a.base with
  | false => rw [hb] at h; exact nomatch h
  | true =>
    rw [hb, if_pos rfl, hk] at h
    cases hr : relate d.path a.path with
    | below r => exact ⟨r, relBelow_path hr⟩
    | above r => rw [hr] at h; exact nomatch h
    | apart => rw [hr] at h; exact nomatch h

#print axioms emitS_exact_prefix
#print axioms emitU_exact_prefix

/-- The prefix half of `near`: the demand edges whose entry chain is a prefix of `q` (the
    chains at or above `q`). The query walks the key path of `q` only. -/
def nearPre (ds : List DemandEdge) (q : List Acc) : List DemandEdge :=
  (demandIdx ds).lookupPrefixes q

theorem mem_nearPre {ds : List DemandEdge} {q : List Acc} {d : DemandEdge} :
    d ∈ nearPre ds q ↔ d ∈ ds ∧ ∃ s, q = d.din.path ++ s :=
  Store.mem_prefixes_indexBy

/-- The prefix half is a part of `near`. -/
theorem nearPre_sub {ds : List DemandEdge} {q : List Acc} {d : DemandEdge}
    (h : d ∈ nearPre ds q) : d ∈ near ds q :=
  List.mem_append_left _ h

/-- The emission candidates of an exact added fact: the prefix walk only. -/
def emitPrefCands (ds : List DemandEdge) (a : PFact) : List DemandEdge := nearPre ds a.path

/-- COMPLETENESS of the prefix walk for an exact added fact (generic). -/
theorem emit_complete_exact {emit : PFact → PFact → Option PFact} (he : EmitExactPrefix emit)
    {ds : List DemandEdge} {a j : PFact} {d : DemandEdge}
    (hk : a.kind = .exact) (h : emit d.din a = some j) (hd : d ∈ ds) :
    d ∈ emitPrefCands ds a :=
  mem_nearPre.mpr ⟨hd, he _ _ _ hk h⟩

/-- Index = concept for an exact added fact, with the prefix walk only (generic). -/
theorem emit_lookup_equiv_exact {emit : PFact → PFact → Option PFact} (he : EmitExactPrefix emit)
    {ds : List DemandEdge} {a j : PFact} (hk : a.kind = .exact) :
    j ∈ (emitPrefCands ds a).filterMap (fun d => emit d.din a) ↔
      j ∈ ds.filterMap (fun d => emit d.din a) := by
  rw [List.mem_filterMap, List.mem_filterMap]
  constructor
  · intro ⟨d, hd, h⟩; exact ⟨d, (mem_nearPre.mp hd).1, h⟩
  · intro ⟨d, hd, h⟩; exact ⟨d, emit_complete_exact he hk h hd, h⟩

/-- COMPLETENESS of the prefix walk for an exact added fact, version 4. -/
theorem emit_complete_M_exact {ds : List DemandEdge} {a j : PFact} {d : DemandEdge}
    (hk : a.kind = .exact) (h : emitM d.din a = some j) (hd : d ∈ ds) :
    d ∈ emitPrefCands ds a :=
  emit_complete_exact emitM_exactPrefix hk h hd

#print axioms emit_complete_M_exact

/-- FUNCTIONAL EQUIVALENCE for an exact added fact, version 4: the prefix walk alone gives the
    same initial facts as the scan of all demand edges. -/
theorem emit_lookup_equiv_M_exact {ds : List DemandEdge} {a j : PFact} (hk : a.kind = .exact) :
    j ∈ (emitPrefCands ds a).filterMap (fun d => emitM d.din a) ↔
      j ∈ ds.filterMap (fun d => emitM d.din a) :=
  emit_lookup_equiv_exact emitM_exactPrefix hk

#print axioms emit_lookup_equiv_M_exact

/-- The premise of rule `initR` with `emitM`, for an exact added fact: the prefix walk answers
    it. -/
theorem initR_premise_equiv_M_exact {ds : List DemandEdge} {a j : PFact} (hk : a.kind = .exact) :
    (∃ d, d ∈ ds ∧ emitM d.din a = some j) ↔
      (∃ d, d ∈ emitPrefCands ds a ∧ emitM d.din a = some j) :=
  ⟨fun ⟨d, hd, h⟩ => ⟨d, emit_complete_M_exact hk h hd, h⟩,
   fun ⟨d, hd, h⟩ => ⟨d, (mem_nearPre.mp hd).1, h⟩⟩

#print axioms initR_premise_equiv_M_exact

/-- COST of the emission lookup with `emitM` for an exact added fact `a`.
    (1) The prefix walk visits at most `|a.path| + 1` nodes.
    (2) The query `near` visits the prefix walk and the subtree below `a.path`; the lookup for
        an exact fact saves the `fNodes` of that subtree.
    (3) The prefix candidates are candidates of `near` (a part of the query).
    (4) The prefix walk is complete for `emitM`.
    (5) Every prefix candidate has its entry chain at or above `a.path`. -/
theorem emitM_exact_cost (ds : List DemandEdge) (a : PFact) (hk : a.kind = .exact) :
    (demandIdx ds).prefHits a.path ≤ a.path.length + 1 ∧
    nearVisits ds a.path = (demandIdx ds).prefHits a.path + fNodes (tK (demandIdx ds) a.path) ∧
    (∀ d, d ∈ emitPrefCands ds a → d ∈ emitCands ds a) ∧
    (∀ d j, d ∈ ds → emitM d.din a = some j → d ∈ emitPrefCands ds a) ∧
    (∀ d, d ∈ emitPrefCands ds a → d ∈ ds ∧ ∃ s, a.path = d.din.path ++ s) :=
  ⟨Store.PathMap.prefHits_le, rfl, fun _ h => nearPre_sub h,
   fun _ _ hd h => emit_complete_M_exact hk h hd, fun _ h => mem_nearPre.mp h⟩

#print axioms emitM_exact_cost

/-! ## 3. The restriction of an edge tree

A summary premise `j` has edge trees of conclusions: ONE tree per (layer, exclusion `E`,
mark exclusion `X`) (Tree.lean; version 5 adds `X`, and the abstract mark of the tree is
`starM X`). The restriction by a demand edge `d` (`restrictS j g d`, for every conclusion
`g` of the tree) is one walk down `D-p = dout.path`:
  * ABOVE `D-p` (a proper prefix): a `*` flag stays if `E` admits the rest of the chain
    (S rule; the U rule drops it); each `[any]` mark moves to `D-p` as one `[any]` leaf
    (a `$` leaf for an exact `D-p`); a `$` mark is dropped; every child off the path is
    dropped (`apart`).
  * AT `D-p`: the payload stays, and the moved marks are added.
  * BELOW `D-p`: a child stays if the tail of `D-p` admits its accessor. The tail test of
    a non-empty continuation reads only its first accessor (`admitsTailB_cons`), so a child
    is kept or dropped as a whole subtree, and the kept subtree is SHARED.

The result fits ONE tree with the same exclusion `E`, the same mark exclusion `X` and the
same layer: a kept `*` leaf keeps `E`, a moved leaf is `[any]` or `$` (no exclusion, W1),
`restrictConcS` keeps the layer bit, and it keeps the mark of each conclusion. The walk does
not read the marks, so the stored flag `*` stays the flag `*`, and the result tree reads it
with the same `X` (`rC_markX`, `restrictTreeE_mx`). So the equivalence is EXACT
(`restrictTreeE_mem_S`). -/

section TreeR
open ApSpec.Tree

/-- The kind of a moved `[any]` leaf at `D-p`. -/
def kd (dk : Kind) : Kind :=
  match dk with
  | .exact => .exact
  | _      => .any

/-- The relative concept: the restriction of ONE relative conclusion `x` by the rest `q` of
    the chain `D-p` (tail kind `dk`). `keep` selects the S rule (`true`) or the U rule. -/
def rC (keep : Bool) (dk : Kind) (q : List Acc) (x : RFact) : Option RFact :=
  match relate q x.path with
  | .below r => if admitsTailB dk r then some x else none
  | .above r =>
    match x.kind with
    | .star e => if (keep && e.admits r) then some x else none
    | .any    => some ⟨q, kd dk, x.mark⟩
    | .exact  => none
  | .apart => none

/-- `restrictConcS` on a conclusion of a tree on base `b` is `rC true` on its relative fact. -/
theorem conc_S (x : RFact) (δ : Bool) (b : Base) (dout : PFact) :
    restrictConcS ⟨x.toP b, δ⟩ dout =
      if Nat.beq b dout.base then (rC true dout.kind dout.path x).map (fun y => ⟨y.toP b, δ⟩)
      else none := by
  obtain ⟨xp, xk, xm⟩ := x
  obtain ⟨db, dp, dk, dm⟩ := dout
  show restrictConcS ⟨⟨b, xp, xk, xm⟩, δ⟩ ⟨db, dp, dk, dm⟩ =
    if Nat.beq b db then (rC true dk dp ⟨xp, xk, xm⟩).map (fun y => ⟨y.toP b, δ⟩) else none
  unfold restrictConcS rC
  dsimp only
  rcases Bool.eq_false_or_eq_true (Nat.beq b db) with h | h
  rotate_left
  · have hn : ¬ (Nat.beq b db = true) := by rw [h]; exact Bool.false_ne_true
    rw [if_neg hn, if_neg hn]
  · rw [if_pos h, if_pos h]
    cases relate dp xp with
    | below r =>
      dsimp only
      by_cases h2 : admitsTailB dk r = true
      · rw [if_pos h2, if_pos h2]; rfl
      · rw [if_neg h2, if_neg h2]; rfl
    | above r =>
      cases xk with
      | star e =>
        dsimp only
        rw [Bool.true_and]
        by_cases h3 : e.admits r = true
        · rw [if_pos h3, if_pos h3]; rfl
        · rw [if_neg h3, if_neg h3]; rfl
      | any => cases dk <;> rfl
      | exact => rfl
    | apart => rfl

/-- `restrictConcU` on a conclusion of a tree on base `b` is `rC false` on its relative fact. -/
theorem conc_U (x : RFact) (δ : Bool) (b : Base) (dout : PFact) :
    restrictConcU ⟨x.toP b, δ⟩ dout =
      if Nat.beq b dout.base then (rC false dout.kind dout.path x).map (fun y => ⟨y.toP b, δ⟩)
      else none := by
  obtain ⟨xp, xk, xm⟩ := x
  obtain ⟨db, dp, dk, dm⟩ := dout
  show restrictConcU ⟨⟨b, xp, xk, xm⟩, δ⟩ ⟨db, dp, dk, dm⟩ =
    if Nat.beq b db then (rC false dk dp ⟨xp, xk, xm⟩).map (fun y => ⟨y.toP b, δ⟩) else none
  unfold restrictConcU rC
  dsimp only
  rcases Bool.eq_false_or_eq_true (Nat.beq b db) with h | h
  rotate_left
  · have hn : ¬ (Nat.beq b db = true) := by rw [h]; exact Bool.false_ne_true
    rw [if_neg hn, if_neg hn]
  · rw [if_pos h, if_pos h]
    cases relate dp xp with
    | below r =>
      dsimp only
      by_cases h2 : admitsTailB dk r = true
      · rw [if_pos h2, if_pos h2]; rfl
      · rw [if_neg h2, if_neg h2]; rfl
    | above r =>
      cases xk with
      | star e => rfl
      | any => cases dk <;> rfl
      | exact => rfl
    | apart => rfl

#print axioms conc_S
#print axioms conc_U

theorem rC_cons (keep : Bool) (dk : Kind) (a c : Acc) (q : List Acc) (x : RFact) :
    rC keep dk (a :: q) (x.cons c) =
      if Nat.beq a c then (rC keep dk q x).map (RFact.cons a) else none := by
  obtain ⟨xp, xk, xm⟩ := x
  show (match relate (a :: q) (c :: xp) with
    | .below r => if admitsTailB dk r then some (⟨c :: xp, xk, xm⟩ : RFact) else none
    | .above r =>
      match xk with
      | .star e => if (keep && e.admits r) then some (⟨c :: xp, xk, xm⟩ : RFact) else none
      | .any    => some ⟨a :: q, kd dk, xm⟩
      | .exact  => none
    | .apart => none) = _
  rw [Tree.relate_cons_cons]
  rcases Bool.eq_false_or_eq_true (Nat.beq a c) with hac | hac
  · have h := Nat.eq_of_beq_eq_true hac
    subst h
    rw [if_pos hac, if_pos hac]
    unfold rC
    dsimp only
    cases relate q xp with
    | below r =>
      dsimp only
      by_cases h2 : admitsTailB dk r = true
      · rw [if_pos h2, if_pos h2]; rfl
      · rw [if_neg h2, if_neg h2]; rfl
    | above r =>
      cases xk with
      | star e =>
        dsimp only
        by_cases h3 : (keep && e.admits r) = true
        · rw [if_pos h3, if_pos h3]; rfl
        · rw [if_neg h3, if_neg h3]; rfl
      | any => rfl
      | exact => rfl
    | apart => rfl
  · have hn : ¬ (Nat.beq a c = true) := by rw [hac]; exact Bool.false_ne_true
    rw [if_neg hn, if_neg hn]

theorem rC_nil (keep : Bool) (dk : Kind) (x : RFact) :
    rC keep dk [] x = if admitsTailB dk x.path then some x else none := rfl

/-- Version 5. `rC` reads only the path and the kind of the conclusion, and the result keeps
    the mark of the conclusion. So `rC` and the read of the mark exclusion `X` of the tree
    (`markX X`) commute. -/
theorem rC_markX (keep : Bool) (dk : Kind) (q : List Acc) (X : List Mark) (x : RFact) :
    rC keep dk q (markX X x) = (rC keep dk q x).map (markX X) := by
  obtain ⟨xp, xk, xm⟩ := x
  show (match relate q xp with
    | .below r => if admitsTailB dk r then some (⟨xp, xk, mxMark X xm⟩ : RFact) else none
    | .above r =>
      match xk with
      | .star e => if (keep && e.admits r) then some (⟨xp, xk, mxMark X xm⟩ : RFact) else none
      | .any    => some ⟨q, kd dk, mxMark X xm⟩
      | .exact  => none
    | .apart => none) =
    (match relate q xp with
    | .below r => if admitsTailB dk r then some (⟨xp, xk, xm⟩ : RFact) else none
    | .above r =>
      match xk with
      | .star e => if (keep && e.admits r) then some (⟨xp, xk, xm⟩ : RFact) else none
      | .any    => some ⟨q, kd dk, xm⟩
      | .exact  => none
    | .apart => none).map (markX X)
  cases relate q xp with
  | below r =>
    dsimp only
    by_cases h2 : admitsTailB dk r = true
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]; rfl
  | above r =>
    cases xk with
    | star e =>
      dsimp only
      by_cases h3 : (keep && e.admits r) = true
      · rw [if_pos h3, if_pos h3]; rfl
      · rw [if_neg h3, if_neg h3]; rfl
    | any => rfl
    | exact => rfl
  | apart => rfl

theorem admitsTailB_nil (k : Kind) : admitsTailB k [] = true := by
  cases k with
  | star e => exact Excl.admits_nil e
  | any => rfl
  | exact => rfl

/-- The tail test of a non-empty continuation reads only its first accessor. -/
theorem admitsTailB_cons (k : Kind) (a : Acc) (r : List Acc) :
    admitsTailB k (a :: r) = admitsTailB k [a] := by
  cases k with
  | star e => exact admits_cons e a r
  | any => rfl
  | exact => rfl

theorem map_cons_some {o : Option RFact} {a : Acc} {y : RFact} :
    o.map (RFact.cons a) = some y ↔ ∃ y', o = some y' ∧ y = y'.cons a := by
  cases o with
  | none => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => nomatch h⟩
  | some z =>
    constructor
    · intro h
      exact ⟨z, rfl, (Option.some.inj h).symm⟩
    · rintro ⟨y', h, rfl⟩
      cases h
      rfl

theorem payRF_path {E : Excl} {pl : Payload} {x : RFact} (hx : x ∈ payRF E pl) : x.path = [] := by
  rcases mem_payRF.mp hx with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

/-! ### 3.1 The parts of the tree operation -/

/-- Add the moved marks `M` at `D-p` as leaves of kind `kd dk`. -/
def addMarks (dk : Kind) (pl : Payload) (M : MarkSet) : Payload :=
  match dk with
  | .exact => ⟨pl.star, pl.anyM, pl.exactM.union M⟩
  | _      => ⟨pl.star, pl.anyM.union M, pl.exactM⟩

theorem mem_addMarks (E : Excl) (dk : Kind) (pl : Payload) (M : MarkSet) (y : RFact) :
    y ∈ payRF E (addMarks dk pl M) ↔ y ∈ payRF E pl ∨ ∃ m, M.Has m ∧ y = ⟨[], kd dk, m⟩ := by
  cases dk with
  | star e => rw [← mem_msRF]; exact mem_addAny E pl M y
  | any => rw [← mem_msRF]; exact mem_addAny E pl M y
  | exact =>
    show y ∈ payRF E ⟨pl.star, pl.anyM, pl.exactM.union M⟩ ↔ _
    rw [mem_payRF, mem_payRF]
    constructor
    · rintro (h | h | ⟨m, hm, rfl⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · rcases has_union.mp hm with h | h
        · exact Or.inl (Or.inr (Or.inr ⟨m, h, rfl⟩))
        · exact Or.inr ⟨m, h, rfl⟩
    · rintro ((h | h | ⟨m, hm, rfl⟩) | ⟨m, hm, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨m, has_union.mpr (Or.inl hm), rfl⟩)
      · exact Or.inr (Or.inr ⟨m, has_union.mpr (Or.inr hm), rfl⟩)

/-- Keep the children whose accessor the tail of `D-p` admits. A kept child is taken AS IT
    IS (its payload and its subtrie are shared). -/
def keepKids (dk : Kind) : Trie → Trie
  | .nil => .nil
  | .cons a h bl nx => if admitsTailB dk [a] then .cons a h bl (keepKids dk nx) else keepKids dk nx

theorem mem_keepKids (E : Excl) (dk : Kind) (k : Trie) (y : RFact) :
    y ∈ trieRF E (keepKids dk k) ↔ y ∈ trieRF E k ∧ admitsTailB dk y.path = true := by
  induction k with
  | nil => exact ⟨fun h => (nomatch h), fun ⟨h, _⟩ => nomatch h⟩
  | cons a h bl nx _ ihn =>
    have hpath : ∀ z, z ∈ (treeRF E ⟨h, bl⟩).map (RFact.cons a) →
        admitsTailB dk z.path = admitsTailB dk [a] := by
      intro z hz
      obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
      exact admitsTailB_cons dk a z'.path
    rw [trieRF_cons]
    cases hA : admitsTailB dk [a] with
    | true =>
      simp only [keepKids, hA, ↓reduceIte]
      rw [trieRF_cons, List.mem_append, List.mem_append, ihn]
      constructor
      · rintro (hy | ⟨hy, hy'⟩)
        · exact ⟨Or.inl hy, by rw [hpath y hy, hA]⟩
        · exact ⟨Or.inr hy, hy'⟩
      · rintro ⟨hy | hy, hy'⟩
        · exact Or.inl hy
        · exact Or.inr ⟨hy, hy'⟩
    | false =>
      simp only [keepKids, hA, Bool.false_eq_true, ↓reduceIte]
      rw [ihn, List.mem_append]
      constructor
      · rintro ⟨hy, hy'⟩; exact ⟨Or.inr hy, hy'⟩
      · rintro ⟨hy | hy, hy'⟩
        · rw [hpath y hy, hA] at hy'; exact nomatch hy'
        · exact ⟨hy, hy'⟩

/-- The tree walk. `M` is the set of `[any]` marks met above; `q` is the rest of `D-p`. -/
def rTree (keep : Bool) (E : Excl) (dk : Kind) (M : MarkSet) : List Acc → Tree → Tree
  | [],     t => ⟨addMarks dk t.root M, keepKids dk t.kids⟩
  | a :: q, t =>
    let sub := rTree keep E dk (M.union t.root.anyM) q ((childAt a t.kids).getD emptyTree)
    ⟨⟨keep && t.root.star && E.admits (a :: q), MarkSet.empty, MarkSet.empty⟩,
      .cons a sub.root sub.kids .nil⟩

/-- The payload above `D-p`: the `*` leaf stays, the `[any]` leaves move, the `$` leaves go. -/
theorem root_rC (keep : Bool) (E : Excl) (dk : Kind) (pl : Payload) (a : Acc) (q : List Acc)
    (y : RFact) :
    (∃ x, x ∈ payRF E pl ∧ rC keep dk (a :: q) x = some y) ↔
      ((keep && pl.star && E.admits (a :: q)) = true ∧ y = ⟨[], .star E, .star⟩) ∨
      (∃ m, pl.anyM.Has m ∧ y = ⟨a :: q, kd dk, m⟩) := by
  have hS : rC keep dk (a :: q) ⟨[], .star E, .star⟩ =
      if (keep && E.admits (a :: q)) then some ⟨[], .star E, .star⟩ else none := rfl
  constructor
  · rintro ⟨x, hx, hy⟩
    rcases mem_payRF.mp hx with ⟨hs, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, _, rfl⟩
    · rw [hS] at hy
      cases hk : (keep && E.admits (a :: q)) with
      | false => rw [hk] at hy; exact nomatch hy
      | true =>
        rw [hk, if_pos rfl] at hy
        have ⟨hk1, hk2⟩ := (Bool.and_eq_true _ _).mp hk
        left
        refine ⟨?_, (Option.some.inj hy).symm⟩
        rw [hk1, hs, hk2]; rfl
    · exact Or.inr ⟨m, hm, (Option.some.inj hy).symm⟩
    · exact nomatch hy
  · rintro (⟨hst, rfl⟩ | ⟨m, hm, rfl⟩)
    · have ⟨h12, h3⟩ := (Bool.and_eq_true _ _).mp hst
      have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h12
      refine ⟨⟨[], .star E, .star⟩, mem_payRF.mpr (Or.inl ⟨h2, rfl⟩), ?_⟩
      rw [hS, h1, h3]; rfl
    · exact ⟨⟨[], .any, m⟩, mem_payRF.mpr (Or.inr (Or.inl ⟨m, hm, rfl⟩)), rfl⟩

/-- The children on the path: only the child `a` contributes, shifted by `a`. -/
theorem kids_rC (keep : Bool) (E : Excl) (dk : Kind) {a : Acc} {q : List Acc} (k : Trie)
    (hk : wfT k = true) (y : RFact) :
    (∃ x, x ∈ trieRF E k ∧ rC keep dk (a :: q) x = some y) ↔
      ∃ s, childAt a k = some s ∧
        ∃ x, x ∈ treeRF E s ∧ ∃ y', rC keep dk q x = some y' ∧ y = y'.cons a := by
  have noLab : ∀ k' : Trie, memB a (labels k') = false →
      ∀ x, x ∈ trieRF E k' → rC keep dk (a :: q) x = none := by
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
        rw [rC_cons, hk''.1]
        rfl
      · exact ihn hk''.2 x hx
  induction k with
  | nil => exact ⟨fun ⟨_, h, _⟩ => (nomatch h), fun ⟨_, h, _⟩ => nomatch h⟩
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
          rw [rC_cons, hac, if_pos rfl, map_cons_some] at hy
          exact ⟨_, rfl, x', hx', hy⟩
        · rw [noLab nx hl x hx] at hy
          exact nomatch hy
      · rintro ⟨s, hs, x, hx, y', hy', rfl⟩
        cases hs
        refine ⟨x.cons a, List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x, hx, rfl⟩)), ?_⟩
        rw [rC_cons, hac, if_pos rfl, hy']
        rfl
    · have hc : childAt a (.cons c h bl nx) = childAt a nx := by
        simp only [childAt, hac, Bool.false_eq_true, ↓reduceIte]
      rw [hc]
      refine Iff.trans ?_ (ihn hnx)
      constructor
      · rintro ⟨x, hx, hy⟩
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨x', _, rfl⟩ := List.mem_map.mp hx
          rw [rC_cons, hac] at hy
          exact nomatch hy
        · exact ⟨x, hx, hy⟩
      · rintro ⟨x, hx, hy⟩
        exact ⟨x, List.mem_append.mpr (Or.inr hx), hy⟩

theorem getD_wf (k : Trie) (hk : wfT k = true) (a : Acc) :
    ((childAt a k).getD emptyTree).wf = true := by
  cases h : childAt a k with
  | none => rfl
  | some s => exact childAt_wf k hk h

theorem kids_rC' (keep : Bool) (E : Excl) (dk : Kind) {a : Acc} {q : List Acc} (k : Trie)
    (hk : wfT k = true) (y : RFact) :
    (∃ x, x ∈ trieRF E k ∧ rC keep dk (a :: q) x = some y) ↔
      ∃ x, x ∈ treeRF E ((childAt a k).getD emptyTree) ∧
        ∃ y', rC keep dk q x = some y' ∧ y = y'.cons a := by
  rw [kids_rC keep E dk k hk y]
  cases h : childAt a k with
  | none =>
    constructor
    · rintro ⟨_, hs, _⟩; exact nomatch hs
    · rintro ⟨_, hx, _⟩; exact nomatch hx
  | some s =>
    exact ⟨fun ⟨s', hs', hx⟩ => by cases hs'; exact hx, fun hx => ⟨s, rfl, hx⟩⟩

/-- MAIN (relative form). The facts of the walked tree are the moved marks `M` at `q`, and
    the restrictions `rC` of the facts of the input tree. -/
theorem rTree_mem (keep : Bool) (E : Excl) (dk : Kind) (q : List Acc) :
    ∀ (M : MarkSet) (t : Tree), t.wf = true → ∀ y : RFact,
      y ∈ treeRF E (rTree keep E dk M q t) ↔
        (∃ m, M.Has m ∧ y = ⟨q, kd dk, m⟩) ∨ ∃ x, x ∈ treeRF E t ∧ rC keep dk q x = some y := by
  induction q with
  | nil =>
    intro M t _ y
    show y ∈ payRF E (addMarks dk t.root M) ++ trieRF E (keepKids dk t.kids) ↔ _
    rw [List.mem_append, mem_addMarks, mem_keepKids]
    constructor
    · rintro ((hy | hM) | ⟨hy, hA⟩)
      · refine Or.inr ⟨y, List.mem_append.mpr (Or.inl hy), ?_⟩
        rw [rC_nil, payRF_path hy, admitsTailB_nil, if_pos rfl]
      · exact Or.inl hM
      · exact Or.inr ⟨y, List.mem_append.mpr (Or.inr hy), by rw [rC_nil, hA, if_pos rfl]⟩
    · rintro (hM | ⟨x, hx, hy⟩)
      · exact Or.inl (Or.inr hM)
      · rw [rC_nil] at hy
        cases hA : admitsTailB dk x.path with
        | false => rw [hA] at hy; exact nomatch hy
        | true =>
          rw [hA, if_pos rfl] at hy
          cases hy
          rcases List.mem_append.mp hx with hx | hx
          · exact Or.inl (Or.inl hx)
          · exact Or.inr ⟨hx, hA⟩
  | cons a q ih =>
    intro M t ht y
    have hs := getD_wf t.kids ht a
    show y ∈ payRF E ⟨keep && t.root.star && E.admits (a :: q), MarkSet.empty, MarkSet.empty⟩ ++
      ((treeRF E (rTree keep E dk (M.union t.root.anyM) q ((childAt a t.kids).getD emptyTree))).map
        (RFact.cons a) ++ []) ↔ _
    rw [List.append_nil, List.mem_append, List.mem_map]
    have hsplit : (∃ x, x ∈ treeRF E t ∧ rC keep dk (a :: q) x = some y) ↔
        (∃ x, x ∈ payRF E t.root ∧ rC keep dk (a :: q) x = some y) ∨
        (∃ x, x ∈ trieRF E t.kids ∧ rC keep dk (a :: q) x = some y) := by
      constructor
      · rintro ⟨x, hx, hy⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact Or.inl ⟨x, hx, hy⟩
        · exact Or.inr ⟨x, hx, hy⟩
      · rintro (⟨x, hx, hy⟩ | ⟨x, hx, hy⟩)
        · exact ⟨x, List.mem_append.mpr (Or.inl hx), hy⟩
        · exact ⟨x, List.mem_append.mpr (Or.inr hx), hy⟩
    rw [hsplit, root_rC, kids_rC' keep E dk t.kids ht y]
    have hst : y ∈ payRF E ⟨keep && t.root.star && E.admits (a :: q), MarkSet.empty, MarkSet.empty⟩ ↔
        (keep && t.root.star && E.admits (a :: q)) = true ∧ y = ⟨[], .star E, .star⟩ := by
      rw [mem_payRF]
      constructor
      · rintro (h | ⟨m, hm, _⟩ | ⟨m, hm, _⟩)
        · exact h
        · exact absurd hm has_empty
        · exact absurd hm has_empty
      · intro h; exact Or.inl h
    rw [hst]
    constructor
    · rintro (hS | ⟨y', hy', rfl⟩)
      · exact Or.inr (Or.inl (Or.inl hS))
      · rcases (ih _ _ hs y').mp hy' with ⟨m, hm, rfl⟩ | ⟨x, hx, hx'⟩
        · rcases has_union.mp hm with hm | hm
          · exact Or.inl ⟨m, hm, rfl⟩
          · exact Or.inr (Or.inl (Or.inr ⟨m, hm, rfl⟩))
        · exact Or.inr (Or.inr ⟨x, hx, y', hx', rfl⟩)
    · rintro (⟨m, hm, rfl⟩ | (hS | ⟨m, hm, rfl⟩) | ⟨x, hx, y', hx', rfl⟩)
      · exact Or.inr ⟨⟨q, kd dk, m⟩, (ih _ _ hs _).mpr (Or.inl ⟨m, has_union.mpr (Or.inl hm), rfl⟩),
          rfl⟩
      · exact Or.inl hS
      · exact Or.inr ⟨⟨q, kd dk, m⟩, (ih _ _ hs _).mpr (Or.inl ⟨m, has_union.mpr (Or.inr hm), rfl⟩),
          rfl⟩
      · exact Or.inr ⟨y', (ih _ _ hs y').mpr (Or.inr ⟨x, hx, hx'⟩), rfl⟩

#print axioms rTree_mem

/-! ### 3.2 The edge tree: definition and exactness -/

/-- The restriction of the edge tree `t` (conclusions on base `b`) by the exit pattern
    `dout`. `keep = true`: the S rule (`restrictConcS`); `keep = false`: the U rule. -/
def restrictTreeW (keep : Bool) (b : Base) (t : EdgeTree) (dout : PFact) : EdgeTree :=
  if Nat.beq b dout.base then
    ⟨t.excl, t.mx, t.demand, rTree keep t.excl dout.kind MarkSet.empty dout.path t.tree⟩
  else ⟨t.excl, t.mx, t.demand, emptyTree⟩

/-- The restriction of a tree by `D-p`, S rule. -/
def restrictTree (b : Base) (t : EdgeTree) (dout : PFact) : EdgeTree := restrictTreeW true b t dout

/-- The restriction of a tree by `D-p`, U rule. -/
def restrictTreeU (b : Base) (t : EdgeTree) (dout : PFact) : EdgeTree := restrictTreeW false b t dout

/-- The restriction of the edge tree of the premise `j` by the demand edge `d` (`restrictWith`):
    no `D-p` gives nothing; a premise that does not overlap `D-c` gives nothing. -/
def restrictTreeE (keep : Bool) (b : Base) (j : PFact) (t : EdgeTree) (d : DemandEdge) :
    Option EdgeTree :=
  match d.dout with
  | none   => none
  | some p => if overlapB j d.din then some (restrictTreeW keep b t p) else none

/-- The conclusions of an optional tree. -/
def optFacts (b : Base) : Option EdgeTree → List AFact
  | none   => []
  | some t => toAFacts b t

/-- Generic exactness on one tree, for a conclusion restriction `rc` that is `rC keep`. -/
theorem restrictTreeW_mem (keep : Bool) (rc : AFact → PFact → Option AFact) (b : Base)
    (dout : PFact)
    (hrc : ∀ x δ, rc ⟨x.toP b, δ⟩ dout =
      if Nat.beq b dout.base then (rC keep dout.kind dout.path x).map (fun y => ⟨y.toP b, δ⟩)
      else none)
    (t : EdgeTree) (hwf : t.tree.wf = true) (a : AFact) :
    a ∈ toAFacts b (restrictTreeW keep b t dout) ↔ ∃ c, c ∈ toAFacts b t ∧ rc c dout = some a := by
  have hR : (∃ c, c ∈ toAFacts b t ∧ rc c dout = some a) ↔
      ∃ x, x ∈ treeRF t.excl t.tree ∧ rc ⟨(markX t.mx x).toP b, t.demand⟩ dout = some a := by
    constructor
    · rintro ⟨c, hc, h⟩
      obtain ⟨x, hx, rfl⟩ := (mem_toAFacts b t c).mp hc
      exact ⟨x, hx, h⟩
    · rintro ⟨x, hx, h⟩
      exact ⟨_, (mem_toAFacts b t _).mpr ⟨x, hx, rfl⟩, h⟩
  rw [hR]
  unfold restrictTreeW
  rcases Bool.eq_false_or_eq_true (Nat.beq b dout.base) with hb | hb
  · rw [if_pos hb, mem_toAFacts]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases (rTree_mem keep t.excl dout.kind dout.path MarkSet.empty t.tree hwf y).mp hy with
        ⟨m, hm, _⟩ | ⟨x, hx, hxy⟩
      · exact absurd hm has_empty
      · exact ⟨x, hx, by rw [hrc, if_pos hb, rC_markX, hxy]; rfl⟩
    · rintro ⟨x, hx, h⟩
      rw [hrc, if_pos hb, rC_markX] at h
      cases hxy : rC keep dout.kind dout.path x with
      | none => rw [hxy] at h; exact nomatch h
      | some y =>
        rw [hxy] at h
        have h' : (⟨(markX t.mx y).toP b, t.demand⟩ : AFact) = a := Option.some.inj h
        exact ⟨y, (rTree_mem keep t.excl dout.kind dout.path MarkSet.empty t.tree hwf y).mpr
          (Or.inr ⟨x, hx, hxy⟩), h'.symm⟩
  · have hn : ¬ (Nat.beq b dout.base = true) := by rw [hb]; exact Bool.false_ne_true
    rw [if_neg hn]
    constructor
    · intro h
      obtain ⟨y, hy, _⟩ := (mem_toAFacts b _ a).mp h
      exact nomatch hy
    · rintro ⟨x, _, h⟩
      rw [hrc, if_neg hn] at h
      exact nomatch h

/-- MAIN (tree by `D-p`, S rule). The conclusions of the restricted tree are EXACTLY the
    `restrictConcS` results of the conclusions of the input tree (fact AND layer). -/
theorem restrictTree_mem (b : Base) (t : EdgeTree) (hwf : t.tree.wf = true) (dout : PFact)
    (a : AFact) :
    a ∈ toAFacts b (restrictTree b t dout) ↔
      ∃ c, c ∈ toAFacts b t ∧ restrictConcS c dout = some a :=
  restrictTreeW_mem true restrictConcS b dout (fun x δ => conc_S x δ b dout) t hwf a

/-- The same for the U rule. -/
theorem restrictTreeU_mem (b : Base) (t : EdgeTree) (hwf : t.tree.wf = true) (dout : PFact)
    (a : AFact) :
    a ∈ toAFacts b (restrictTreeU b t dout) ↔
      ∃ c, c ∈ toAFacts b t ∧ restrictConcU c dout = some a :=
  restrictTreeW_mem false restrictConcU b dout (fun x δ => conc_U x δ b dout) t hwf a

#print axioms restrictTree_mem
#print axioms restrictTreeU_mem

theorem restrictTreeE_mem (keep : Bool) (rc : AFact → PFact → Option AFact) (b : Base)
    (hrc : ∀ dout x δ, rc ⟨x.toP b, δ⟩ dout =
      if Nat.beq b dout.base then (rC keep dout.kind dout.path x).map (fun y => ⟨y.toP b, δ⟩)
      else none)
    (j : PFact) (t : EdgeTree) (hwf : t.tree.wf = true) (d : DemandEdge) (a : AFact) :
    a ∈ optFacts b (restrictTreeE keep b j t d) ↔
      ∃ c, c ∈ toAFacts b t ∧ restrictWith rc j c d = some a := by
  cases hd : d.dout with
  | none =>
    have h1 : restrictTreeE keep b j t d = none := by unfold restrictTreeE; rw [hd]
    have h2 : ∀ c, restrictWith rc j c d = none := fun c => by unfold restrictWith; rw [hd]
    rw [h1]
    exact ⟨fun h => (nomatch h), fun ⟨c, _, h⟩ => by rw [h2] at h; exact nomatch h⟩
  | some p =>
    rcases Bool.eq_false_or_eq_true (overlapB j d.din) with ho | ho
    · have h1 : restrictTreeE keep b j t d = some (restrictTreeW keep b t p) := by
        unfold restrictTreeE; rw [hd]; exact if_pos ho
      have h2 : ∀ c, restrictWith rc j c d = rc c p := fun c => by
        unfold restrictWith; rw [hd]; exact if_pos ho
      rw [h1]
      show a ∈ toAFacts b (restrictTreeW keep b t p) ↔ _
      rw [restrictTreeW_mem keep rc b p (hrc p) t hwf a]
      constructor
      · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by rw [h2]; exact h⟩
      · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by rw [← h2]; exact h⟩
    · have hn : ¬ (overlapB j d.din = true) := by rw [ho]; exact Bool.false_ne_true
      have h1 : restrictTreeE keep b j t d = none := by
        unfold restrictTreeE; rw [hd]; exact if_neg hn
      have h2 : ∀ c, restrictWith rc j c d = none := fun c => by
        unfold restrictWith; rw [hd]; exact if_neg hn
      rw [h1]
      exact ⟨fun h => (nomatch h), fun ⟨c, _, h⟩ => by rw [h2] at h; exact nomatch h⟩

/-- MAIN (tree by a demand edge, S rule). The restricted tree of the premise `j` holds exactly
    the `restrictS j g d` results of the conclusions `g` of the input tree. -/
theorem restrictTreeE_mem_S (b : Base) (j : PFact) (t : EdgeTree) (hwf : t.tree.wf = true)
    (d : DemandEdge) (a : AFact) :
    a ∈ optFacts b (restrictTreeE true b j t d) ↔
      ∃ c, c ∈ toAFacts b t ∧ restrictS j c d = some a :=
  restrictTreeE_mem true restrictConcS b (fun dout x δ => conc_S x δ b dout) j t hwf d a

/-- The same for the U rule. -/
theorem restrictTreeE_mem_U (b : Base) (j : PFact) (t : EdgeTree) (hwf : t.tree.wf = true)
    (d : DemandEdge) (a : AFact) :
    a ∈ optFacts b (restrictTreeE false b j t d) ↔
      ∃ c, c ∈ toAFacts b t ∧ restrictU j c d = some a :=
  restrictTreeE_mem false restrictConcU b (fun dout x δ => conc_U x δ b dout) j t hwf d a

#print axioms restrictTreeE_mem_S
#print axioms restrictTreeE_mem_U

/-- The denotation form: the pairs of the restricted tree in the layer `δ` are the pairs of
    the `restrictS` results in the layer `δ`. -/
theorem restrictTreeE_den_S (b : Base) (j : PFact) (t : EdgeTree) (hwf : t.tree.wf = true)
    (d : DemandEdge) {i : PFact} {δ : Bool} {l0 l1 : Loc} :
    denA i (optFacts b (restrictTreeE true b j t d)) δ l0 l1 ↔
      ∃ c, c ∈ toAFacts b t ∧ ∃ g', restrictS j c d = some g' ∧ g'.demand = δ ∧
        den i g'.fact l0 l1 := by
  constructor
  · rintro ⟨a, ha, hd, hden⟩
    obtain ⟨c, hc, h⟩ := (restrictTreeE_mem_S b j t hwf d a).mp ha
    exact ⟨c, hc, a, h, hd, hden⟩
  · rintro ⟨c, hc, g', h, hd, hden⟩
    exact ⟨g', (restrictTreeE_mem_S b j t hwf d g').mpr ⟨c, hc, h⟩, hd, hden⟩

#print axioms restrictTreeE_den_S

/-! ### 3.3 Cost and sharing

Cost model (as Tree.lean, section 9): `rCmp` counts the sibling cells that the walk compares
(left-child / right-sibling encoding); `size` counts nodes; `twidth` counts the siblings of
one node. The operation:
  * walks `|D-p| + 1` levels and compares each input cell at most once (`rCmp ≤ trieSize`);
  * builds `|D-p| + 1` new nodes on the path (each with one child), and one new sibling cell
    per KEPT child at `D-p` (`newCells`);
  * SHARES every kept child: its payload and its whole subtrie are the input's
    (`rTree_shape`, `keepKids_children`). So the kept subtree is never copied: the cost is
    `|D-p| + width at D-p`, not `|D-p| + size of the kept subtree`.
  * For a `[any]` tail of `D-p` all children are kept (`keepKids_any`: the child list is
    the input's); for a `$` tail none (`keepKids_exact`).
  * The union of the moved marks is not counted here: it costs the number of `[any]` marks
    on the path.
The list form calls `restrictConcS` once per conclusion (`restrictListC_spec`). -/

/-- The node at the end of the walk (an empty node if the path leaves the tree). -/
def endAt : List Acc → Tree → Tree
  | [],     t => t
  | a :: q, t => endAt q ((childAt a t.kids).getD emptyTree)

/-- The children of a node: (accessor, payload, subtrie) — the shared parts. -/
def children : Trie → List (Acc × Payload × Trie)
  | .nil => []
  | .cons a h bl nx => (a, h, bl) :: children nx

/-- The number of siblings. -/
def twidth (k : Trie) : Nat := (children k).length

/-- SHARING. `keepKids` keeps the children of the input AS THEY ARE: the list of
    (accessor, payload, subtrie) of the result is a filter of the input's list. -/
theorem keepKids_children (dk : Kind) : ∀ k : Trie,
    children (keepKids dk k) = (children k).filter (fun c => admitsTailB dk [c.1])
  | .nil => rfl
  | .cons a h bl nx => by
    rcases Bool.eq_false_or_eq_true (admitsTailB dk [a]) with hA | hA
    · simp only [keepKids, children, List.filter_cons, hA, ↓reduceIte, keepKids_children dk nx]
    · simp only [keepKids, children, List.filter_cons, hA, Bool.false_eq_true, ↓reduceIte,
        keepKids_children dk nx]

theorem keepKids_any : ∀ k : Trie, keepKids .any k = k
  | .nil => rfl
  | .cons a h bl nx => by
    show (if admitsTailB .any [a] = true then Trie.cons a h bl (keepKids .any nx)
      else keepKids .any nx) = _
    have hA : admitsTailB Kind.any [a] = true := rfl
    rw [if_pos hA, keepKids_any nx]

theorem keepKids_exact : ∀ k : Trie, keepKids .exact k = .nil
  | .nil => rfl
  | .cons a h bl nx => by
    show (if admitsTailB .exact [a] = true then Trie.cons a h bl (keepKids .exact nx)
      else keepKids .exact nx) = _
    have hA : ¬ (admitsTailB Kind.exact [a] = true) := Bool.false_ne_true
    rw [if_neg hA, keepKids_exact nx]

theorem twidth_keepKids (dk : Kind) (k : Trie) : twidth (keepKids dk k) ≤ twidth k := by
  unfold twidth
  rw [keepKids_children]
  exact List.length_filter_le _ _

theorem trieSize_keepKids (dk : Kind) : ∀ k : Trie, trieSize (keepKids dk k) ≤ trieSize k
  | .nil => Nat.le_refl _
  | .cons a h bl nx => by
    have ih := trieSize_keepKids dk nx
    rcases Bool.eq_false_or_eq_true (admitsTailB dk [a]) with hA | hA
    · simp only [keepKids, hA, ↓reduceIte, trieSize]; omega
    · simp only [keepKids, hA, Bool.false_eq_true, ↓reduceIte, trieSize]; omega

theorem childAt_self (a : Acc) (r : Payload) (k : Trie) :
    childAt a (.cons a r k .nil) = some ⟨r, k⟩ := by
  simp only [childAt, Nat.beq_refl, ↓reduceIte]

/-- SHARING. At the end of the walk, the result node holds the input payload with the moved
    marks, and the kept children of the input node. -/
theorem rTree_shape (keep : Bool) (E : Excl) (dk : Kind) : ∀ (q : List Acc) (M : MarkSet) (t : Tree),
    ∃ M', endAt q (rTree keep E dk M q t) =
      ⟨addMarks dk (endAt q t).root M', keepKids dk (endAt q t).kids⟩
  | [], M, _ => ⟨M, rfl⟩
  | a :: q, M, t => by
    obtain ⟨M', h⟩ := rTree_shape keep E dk q (M.union t.root.anyM) ((childAt a t.kids).getD emptyTree)
    refine ⟨M', ?_⟩
    show endAt q ((childAt a (.cons a
      (rTree keep E dk (M.union t.root.anyM) q ((childAt a t.kids).getD emptyTree)).root
      (rTree keep E dk (M.union t.root.anyM) q ((childAt a t.kids).getD emptyTree)).kids .nil)).getD
        emptyTree) = _
    rw [childAt_self]
    exact h

/-- The size of the result, counted with the shared nodes. -/
theorem rTree_size (keep : Bool) (E : Excl) (dk : Kind) : ∀ (q : List Acc) (M : MarkSet) (t : Tree),
    size (rTree keep E dk M q t) ≤ q.length + 1 + trieSize (endAt q t).kids
  | [], M, t => by
    have h := trieSize_keepKids dk t.kids
    show 1 + trieSize (keepKids dk t.kids) ≤ 0 + 1 + trieSize t.kids
    omega
  | a :: q, M, t => by
    have ih := rTree_size keep E dk q (M.union t.root.anyM) ((childAt a t.kids).getD emptyTree)
    unfold size at ih
    show 1 + (1 + trieSize (rTree keep E dk (M.union t.root.anyM) q
      ((childAt a t.kids).getD emptyTree)).kids + 0) ≤
      q.length + 1 + 1 + trieSize (endAt q ((childAt a t.kids).getD emptyTree)).kids
    omega

/-- The cells that the operation builds: one node per level of the walk, and one sibling cell
    per kept child at `D-p`. Every other node of the result is a node of the input. -/
def newCells (dk : Kind) : List Acc → Tree → Nat
  | [],     t => 1 + twidth (keepKids dk t.kids)
  | a :: q, t => 1 + newCells dk q ((childAt a t.kids).getD emptyTree)

theorem newCells_eq (dk : Kind) : ∀ (q : List Acc) (t : Tree),
    newCells dk q t = q.length + 1 + twidth (keepKids dk (endAt q t).kids)
  | [], t => by
    show 1 + twidth (keepKids dk t.kids) = 0 + 1 + twidth (keepKids dk t.kids); omega
  | a :: q, t => by
    show 1 + newCells dk q _ = q.length + 1 + 1 + _
    rw [newCells_eq dk q]
    show 1 + (q.length + 1 + _) = q.length + 1 + 1 + twidth (keepKids dk (endAt q _).kids)
    omega

/-- The sibling cells that the walk compares (as `Tree.walkCmp`; a missing child gives the
    empty node, which costs nothing). -/
def rCmp : List Acc → Tree → Nat
  | [],     _ => 0
  | a :: q, t => scanCost a t.kids + rCmp q ((childAt a t.kids).getD emptyTree)

theorem rCmp_empty : ∀ q : List Acc, rCmp q emptyTree = 0
  | [] => rfl
  | a :: q => by
    show 0 + rCmp q ((childAt a .nil).getD emptyTree) = 0
    rw [show (childAt a Trie.nil).getD emptyTree = emptyTree from rfl, rCmp_empty q]

theorem rCmp_eq : ∀ (q : List Acc) (t : Tree), rCmp q t = walkCmp q t
  | [], _ => rfl
  | a :: q, t => by
    show scanCost a t.kids + rCmp q ((childAt a t.kids).getD emptyTree) =
      scanCost a t.kids + (match childAt a t.kids with | none => 0 | some s => walkCmp q s)
    cases childAt a t.kids with
    | none => rw [show (none : Option Tree).getD emptyTree = emptyTree from rfl, rCmp_empty]
    | some s => rw [show (some s).getD emptyTree = s from rfl, rCmp_eq q s]

/-- COST of the tree restriction.
    (1) the walk compares each input cell at most once;
    (2) the operation builds `|D-p| + 1 + (kept children at D-p)` cells, at most
        `|D-p| + 1 + width at D-p`;
    (3) SHARING: the result node at `D-p` holds the kept children of the input node as they
        are (payload and subtrie), and every node below them is an input node;
    (4) with the shared nodes counted, the result has at most `|D-p| + 1 + size below D-p`
        nodes. -/
theorem restrictTree_cost (keep : Bool) (E : Excl) (dk : Kind) (M : MarkSet) (q : List Acc)
    (t : Tree) :
    rCmp q t ≤ trieSize t.kids ∧
    newCells dk q t = q.length + 1 + twidth (keepKids dk (endAt q t).kids) ∧
    newCells dk q t ≤ q.length + 1 + twidth (endAt q t).kids ∧
    (∃ M', endAt q (rTree keep E dk M q t) =
      ⟨addMarks dk (endAt q t).root M', keepKids dk (endAt q t).kids⟩) ∧
    children (keepKids dk (endAt q t).kids) =
      (children (endAt q t).kids).filter (fun c => admitsTailB dk [c.1]) ∧
    size (rTree keep E dk M q t) ≤ q.length + 1 + trieSize (endAt q t).kids := by
  refine ⟨by rw [rCmp_eq]; exact walkCmp_le q t, newCells_eq dk q t, ?_, rTree_shape keep E dk q M t,
    keepKids_children dk _, rTree_size keep E dk q M t⟩
  rw [newCells_eq]
  have := twidth_keepKids dk (endAt q t).kids
  omega

#print axioms restrictTree_cost

/-- The list form with a call counter: one `restrictConcS` call per conclusion. -/
def restrictListC (rc : AFact → PFact → Option AFact) (dout : PFact) :
    List AFact → List AFact × Nat
  | []      => ([], 0)
  | c :: fs =>
    let r := restrictListC rc dout fs
    ((rc c dout).toList ++ r.1, 1 + r.2)

theorem restrictListC_spec (rc : AFact → PFact → Option AFact) (dout : PFact) :
    ∀ fs : List AFact, (restrictListC rc dout fs).1 = fs.filterMap (fun c => rc c dout) ∧
      (restrictListC rc dout fs).2 = fs.length
  | [] => ⟨rfl, rfl⟩
  | c :: fs => by
    have ih := restrictListC_spec rc dout fs
    refine ⟨?_, ?_⟩
    · show (rc c dout).toList ++ (restrictListC rc dout fs).1 = (c :: fs).filterMap _
      rw [ih.1, List.filterMap_cons]
      cases rc c dout <;> rfl
    · show 1 + (restrictListC rc dout fs).2 = fs.length + 1
      rw [ih.2]; omega

#print axioms restrictListC_spec

/-! ### 3.4 The restriction keeps the tree invariants

The result is a well-formed trie (sibling accessors are distinct), and a tree without `*`
leaves (the invariant of the demand layer) gives a tree without `*` leaves. So the result
can go back into the store, and Tree.lean's theorems apply to it. -/

theorem keepKids_labels {dk : Kind} {c : Acc} (k : Trie) :
    memB c (labels (keepKids dk k)) = true → memB c (labels k) = true := by
  induction k with
  | nil => exact id
  | cons a h bl nx _ ihn =>
    intro hc
    show (Nat.beq c a || memB c (labels nx)) = true
    rcases Bool.eq_false_or_eq_true (admitsTailB dk [a]) with hp | hp
    · simp only [keepKids, hp, ↓reduceIte] at hc
      have hc' : (Nat.beq c a || memB c (labels (keepKids dk nx))) = true := hc
      rw [Bool.or_eq_true] at hc'
      rcases hc' with h1 | h1
      · rw [h1]; rfl
      · rw [ihn h1, Bool.or_true]
    · simp only [keepKids, hp, Bool.false_eq_true, ↓reduceIte] at hc
      rw [ihn hc, Bool.or_true]

theorem wfT_keepKids (dk : Kind) (k : Trie) (hk : wfT k = true) : wfT (keepKids dk k) = true := by
  induction k with
  | nil => rfl
  | cons a h bl nx _ ihn =>
    obtain ⟨hl, hbl, hnx⟩ := wfT_cons.mp hk
    rcases Bool.eq_false_or_eq_true (admitsTailB dk [a]) with hp | hp
    · simp only [keepKids, hp, ↓reduceIte]
      refine wfT_cons.mpr ⟨?_, hbl, ihn hnx⟩
      rcases Bool.eq_false_or_eq_true (memB a (labels (keepKids dk nx))) with h1 | h1
      · rw [keepKids_labels nx h1] at hl; exact nomatch hl
      · exact h1
    · simp only [keepKids, hp, Bool.false_eq_true, ↓reduceIte]
      exact ihn hnx

theorem keepKids_noStar (dk : Kind) (k : Trie) (hk : noStarT k = true) :
    noStarT (keepKids dk k) = true := by
  induction k with
  | nil => rfl
  | cons a h bl nx _ ihn =>
    obtain ⟨hh, hbl, hnx⟩ := noStarT_cons.mp hk
    rcases Bool.eq_false_or_eq_true (admitsTailB dk [a]) with hp | hp
    · simp only [keepKids, hp, ↓reduceIte]
      exact noStarT_cons.mpr ⟨hh, hbl, ihn hnx⟩
    · simp only [keepKids, hp, Bool.false_eq_true, ↓reduceIte]
      exact ihn hnx

theorem addMarks_star (dk : Kind) (pl : Payload) (M : MarkSet) : (addMarks dk pl M).star = pl.star := by
  cases dk <;> rfl

theorem getD_noStar (k : Trie) (hk : noStarT k = true) (a : Acc) :
    ((childAt a k).getD emptyTree).noStar = true := by
  cases h : childAt a k with
  | none => rfl
  | some s => exact childAt_noStar k hk h

theorem rTree_wf (keep : Bool) (E : Excl) (dk : Kind) : ∀ (q : List Acc) (M : MarkSet) (t : Tree),
    t.wf = true → (rTree keep E dk M q t).wf = true
  | [], _, t, ht => wfT_keepKids dk t.kids ht
  | a :: q, _, t, ht =>
    wfT_cons.mpr ⟨rfl, rTree_wf keep E dk q _ _ (getD_wf t.kids ht a), rfl⟩

theorem rTree_noStar (keep : Bool) (E : Excl) (dk : Kind) : ∀ (q : List Acc) (M : MarkSet) (t : Tree),
    t.noStar = true → (rTree keep E dk M q t).noStar = true
  | [], M, t, ht => by
    have ⟨h1, h2⟩ := noStar_iff.mp ht
    exact noStar_iff.mpr ⟨by show (addMarks dk t.root M).star = false; rw [addMarks_star, h1],
      keepKids_noStar dk t.kids h2⟩
  | a :: q, M, t, ht => by
    have ⟨h1, h2⟩ := noStar_iff.mp ht
    have ih := noStar_iff.mp (rTree_noStar keep E dk q (M.union t.root.anyM)
      ((childAt a t.kids).getD emptyTree) (getD_noStar t.kids h2 a))
    refine noStar_iff.mpr ⟨?_, noStarT_cons.mpr ⟨ih.1, ih.2, rfl⟩⟩
    show (keep && t.root.star && E.admits (a :: q)) = false
    rw [h1, Bool.and_false, Bool.false_and]

/-- INVARIANTS. A restricted tree is well formed, it keeps the exclusion and the layer of the
    input, and a demand-layer tree stays without `*` leaves. -/
theorem restrictTreeE_inv (keep : Bool) (b : Base) (j : PFact) (t : EdgeTree) (d : DemandEdge)
    (hwf : t.tree.wf = true) (hinv : t.demand = true → t.tree.noStar = true) (t' : EdgeTree)
    (h : restrictTreeE keep b j t d = some t') :
    t'.tree.wf = true ∧ t'.excl = t.excl ∧ t'.demand = t.demand ∧
      (t'.demand = true → t'.tree.noStar = true) := by
  have hW : ∀ p, (restrictTreeW keep b t p).tree.wf = true ∧ (restrictTreeW keep b t p).excl = t.excl ∧
      (restrictTreeW keep b t p).demand = t.demand ∧
      ((restrictTreeW keep b t p).demand = true → (restrictTreeW keep b t p).tree.noStar = true) := by
    intro p
    unfold restrictTreeW
    rcases Bool.eq_false_or_eq_true (Nat.beq b p.base) with hb | hb
    · rw [if_pos hb]
      exact ⟨rTree_wf keep t.excl p.kind p.path _ t.tree hwf, rfl, rfl,
        fun hd => rTree_noStar keep t.excl p.kind p.path _ t.tree (hinv hd)⟩
    · have hn : ¬ (Nat.beq b p.base = true) := by rw [hb]; exact Bool.false_ne_true
      rw [if_neg hn]
      exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  unfold restrictTreeE at h
  cases hd : d.dout with
  | none => rw [hd] at h; exact nomatch h
  | some p =>
    have h' : (if overlapB j d.din = true then some (restrictTreeW keep b t p) else none) = some t' := by
      rw [hd] at h; exact h
    rcases Bool.eq_false_or_eq_true (overlapB j d.din) with ho | ho
    · rw [if_pos ho] at h'
      cases h'
      exact hW p
    · have hn : ¬ (overlapB j d.din = true) := by rw [ho]; exact Bool.false_ne_true
      rw [if_neg hn] at h'
      exact nomatch h'

#print axioms restrictTreeE_inv

/-- Version 5. The restriction keeps the mark exclusion of the tree: the result tree reads
    its stored flag `*` as the abstract mark `starM t.mx` of the input tree. -/
theorem restrictTreeW_mx (keep : Bool) (b : Base) (t : EdgeTree) (dout : PFact) :
    (restrictTreeW keep b t dout).mx = t.mx := by
  unfold restrictTreeW
  rcases Bool.eq_false_or_eq_true (Nat.beq b dout.base) with hb | hb
  · rw [if_pos hb]
  · have hn : ¬ (Nat.beq b dout.base = true) := by rw [hb]; exact Bool.false_ne_true
    rw [if_neg hn]

/-- MAIN (version 5). The restriction of a tree by `D-p` (S rule) has the mark exclusion of
    the input tree. -/
theorem restrictTree_mx (b : Base) (t : EdgeTree) (dout : PFact) :
    (restrictTree b t dout).mx = t.mx :=
  restrictTreeW_mx true b t dout

/-- The same for the U rule. -/
theorem restrictTreeU_mx (b : Base) (t : EdgeTree) (dout : PFact) :
    (restrictTreeU b t dout).mx = t.mx :=
  restrictTreeW_mx false b t dout

/-- MAIN (version 5). The restriction of the edge tree of the premise `j` by a demand edge
    keeps the whole key of the tree: the exclusion, the mark exclusion and the layer. -/
theorem restrictTreeE_mx (keep : Bool) (b : Base) (j : PFact) (t : EdgeTree) (d : DemandEdge)
    (t' : EdgeTree) (h : restrictTreeE keep b j t d = some t') :
    t'.mx = t.mx ∧ t'.excl = t.excl ∧ t'.demand = t.demand := by
  have hW : ∀ p, (restrictTreeW keep b t p).excl = t.excl ∧
      (restrictTreeW keep b t p).demand = t.demand := by
    intro p
    unfold restrictTreeW
    rcases Bool.eq_false_or_eq_true (Nat.beq b p.base) with hb | hb
    · rw [if_pos hb]; exact ⟨rfl, rfl⟩
    · have hn : ¬ (Nat.beq b p.base = true) := by rw [hb]; exact Bool.false_ne_true
      rw [if_neg hn]; exact ⟨rfl, rfl⟩
  unfold restrictTreeE at h
  cases hd : d.dout with
  | none => rw [hd] at h; exact nomatch h
  | some p =>
    have h' : (if overlapB j d.din = true then some (restrictTreeW keep b t p) else none) = some t' := by
      rw [hd] at h; exact h
    rcases Bool.eq_false_or_eq_true (overlapB j d.din) with ho | ho
    · rw [if_pos ho] at h'
      cases h'
      exact ⟨restrictTreeW_mx keep b t p, hW p⟩
    · have hn : ¬ (overlapB j d.din = true) := by rw [ho]; exact Bool.false_ne_true
      rw [if_neg hn] at h'
      exact nomatch h'

#print axioms restrictTreeW_mx
#print axioms restrictTree_mx
#print axioms restrictTreeU_mx
#print axioms restrictTreeE_mx

end TreeR

/-! ## 4. Examples (decide-checked) -/

namespace Ex
open ApSpec.Tree

def f : Acc := 1
def g : Acc := 2
def h : Acc := 3
def st : Kind := .star Excl.empty
def pf (b : Base) (p : List Acc) (k : Kind) : PFact := ⟨b, p, k, .star⟩

def sameSetP (l1 l2 : List PFact) : Bool :=
  l1.all (fun p => l2.contains p) && l2.all (fun p => l1.contains p)

/-! ### 4.1 The demand store -/

/-- Demand edges of one method: entry chains at `[]`, `.f.g`, `.h` (base 1), `.f` (base 4). -/
def ds : List DemandEdge :=
  [ ⟨pf 1 [] .any, some (pf 2 [] st)⟩,
    ⟨pf 1 [f, g] st, some (pf 2 [f] st)⟩,
    ⟨pf 1 [h] st, none⟩,
    ⟨pf 4 [f] st, some (pf 2 [] .exact)⟩,
    ⟨pf 1 [f] (.star (.set [g])), none⟩ ]

/-- Added facts: at `.f` (`*`, `$`, `[any]`), at the root, and below `.f.g`. -/
def adds : List PFact :=
  [pf 1 [f] st, pf 1 [f] .exact, pf 1 [f] .any, pf 1 [] (.star (.set [h])), pf 1 [f, g, h] st,
   pf 4 [] .any]

-- the index finds the same initial facts as the scan, for the S and the U rules
example : adds.all (fun a =>
    sameSetP ((emitCands ds a).filterMap (fun d => emitS d.din a))
      (ds.filterMap (fun d => emitS d.din a)) &&
    sameSetP ((emitCands ds a).filterMap (fun d => emitU d.din a))
      (ds.filterMap (fun d => emitU d.din a))) = true := by decide

-- the `.h` chain is apart from `.f`: the index does not return it; each edge comes once
example : (emitCands ds (pf 1 [f] st)).map (fun d => (d.din.base, d.din.path)) =
    [(1, []), (4, [f]), (1, [f]), (1, [f, g])] := by decide
-- the base-keyed index also drops the edge on base 4
example : (nearK ds (pf 1 [f] st)).map (fun d => (d.din.base, d.din.path)) =
    [(1, []), (1, [f]), (1, [f, g])] := by decide

/-! ### 4.2 The restriction of an edge tree -/

def x : Base := 10
def b : Base := 12
def T : Mark := 5
def E1 : Excl := .set [h]

/-- The tree of conclusions on base `b` with the exclusion `E1` (Tree.lean, `Ex.tE1`). -/
def tE1 : EdgeTree := ⟨E1, [], false, fromList
  [ ⟨b, [f], .star E1, .star⟩, ⟨b, [], .star E1, .star⟩, ⟨b, [], .any, .star⟩,
    ⟨b, [], .exact, .star⟩, ⟨b, [h], .any, .conc T⟩, ⟨b, [f, g], .exact, .conc T⟩,
    ⟨b, [f, g], .star E1, .star⟩ ]⟩
def tD : EdgeTree := ⟨Excl.empty, [], true, fromList [⟨b, [], .any, .conc T⟩, ⟨b, [f], .exact, .star⟩,
  ⟨b, [f, h], .any, .star⟩, ⟨b, [g], .any, .star⟩]⟩
def trees : List EdgeTree := [tE1, tD]

def j0 : PFact := pf x [] st

/-- Demand edges of the callee: several exit patterns, no exit, and an entry on another base. -/
def dsR : List DemandEdge :=
  [ ⟨pf x [] st, some (pf b [f] st)⟩,
    ⟨pf x [] st, some (pf b [f] .exact)⟩,
    ⟨pf x [] st, some (pf b [f, g] (.star (.set [h])))⟩,
    ⟨pf x [] st, some (pf b [f, g] (.star (.set [f])))⟩,
    ⟨pf x [] st, some (pf b [h, f] .any)⟩,
    ⟨pf x [] st, some (pf b [] (.star (.set [f])))⟩,
    ⟨pf x [] st, some (pf 11 [f] st)⟩,
    ⟨pf x [] st, none⟩,
    ⟨pf 11 [] st, some (pf b [] st)⟩ ]

-- tree form = list form (S and U), for every tree and every demand edge
example : trees.all (fun t => dsR.all (fun d =>
    Tree.Ex.sameSetA (optFacts b (restrictTreeE true b j0 t d))
      ((toAFacts b t).filterMap (fun c => restrictS j0 c d)) &&
    Tree.Ex.sameSetA (optFacts b (restrictTreeE false b j0 t d))
      ((toAFacts b t).filterMap (fun c => restrictU j0 c d)))) = true := by decide

/-- `D-p = b.f.g.*/{h}`. The root `*/{h}` leaf is ABOVE it, and `{h}` admits the rest `.f.g`. -/
def dFG : DemandEdge := ⟨pf x [] st, some (pf b [f, g] (.star (.set [h])))⟩

-- the S rule keeps the correlated root `*` leaf; the U rule drops it
example : ((optFacts b (restrictTreeE true b j0 tE1 dFG)).contains ⟨⟨b, [], .star E1, .star⟩, false⟩,
    (optFacts b (restrictTreeE false b j0 tE1 dFG)).contains ⟨⟨b, [], .star E1, .star⟩, false⟩)
    = (true, false) := by decide

-- the root `[any]` leaf moves to `D-p`; the root `$` leaf and the `.h` subtree are dropped
example : ((optFacts b (restrictTreeE true b j0 tE1 dFG)).contains ⟨⟨b, [f, g], .any, .star⟩, false⟩,
    (optFacts b (restrictTreeE true b j0 tE1 dFG)).contains ⟨⟨b, [], .exact, .star⟩, false⟩,
    (optFacts b (restrictTreeE true b j0 tE1 dFG)).contains ⟨⟨b, [h], .any, .conc T⟩, false⟩)
    = (true, false, false) := by decide

-- an exact `D-p`: the moved leaf is `$`, and no child below `D-p` stays
example : (optFacts b (restrictTreeE true b j0 tE1 ⟨pf x [] st, some (pf b [f] .exact)⟩)).contains
    ⟨⟨b, [f], .exact, .star⟩, false⟩ = true := by decide

#eval (restrictTreeE true b j0 tE1 dFG)

/-! ### 4.2a Trees with a mark exclusion (version 5, cleaners) -/

def U : Mark := 6

/-- A tree behind a cleaner of the mark `T` (Tree.lean, `Ex.tX`): its abstract mark is
    `*∖{T}`. The trie stores the flag `*`. -/
def tX : EdgeTree := ⟨E1, [T], false, fromList [⟨b, [f], .star E1, .starEx [T]⟩,
  ⟨b, [], .star E1, .starEx [T]⟩, ⟨b, [], .any, .starEx [T]⟩, ⟨b, [h], .any, .conc U⟩,
  ⟨b, [f, g], .exact, .starEx [T]⟩, ⟨b, [f, g], .star E1, .starEx [T]⟩]⟩
def tXD : EdgeTree := ⟨Excl.empty, [T], true, fromList [⟨b, [f], .exact, .starEx [T]⟩,
  ⟨b, [g], .any, .starEx [T]⟩, ⟨b, [], .any, .conc T⟩, ⟨b, [f, h], .any, .starEx [T]⟩]⟩
def treesX : List EdgeTree := [tX, tXD]

-- tree form = list form (S and U) for the trees with a mark exclusion
example : treesX.all (fun t => dsR.all (fun d =>
    Tree.Ex.sameSetA (optFacts b (restrictTreeE true b j0 t d))
      ((toAFacts b t).filterMap (fun c => restrictS j0 c d)) &&
    Tree.Ex.sameSetA (optFacts b (restrictTreeE false b j0 t d))
      ((toAFacts b t).filterMap (fun c => restrictU j0 c d)))) = true := by decide

-- every result tree keeps the mark exclusion `{T}` (and the exclusion and the layer)
example : treesX.all (fun t => dsR.all (fun d =>
    (restrictTreeE true b j0 t d).all (fun t' => t'.mx == t.mx && t'.excl == t.excl &&
      t'.demand == t.demand) &&
    (restrictTreeE false b j0 t d).all (fun t' => t'.mx == t.mx && t'.excl == t.excl &&
      t'.demand == t.demand))) = true := by decide

-- the root `[any]` leaf with the mark `*∖{T}` moves to `D-p` and keeps the mark `*∖{T}`;
-- the correlated root `*` leaf stays with `*∖{T}` (S rule); the concrete mark `U` below
-- `.h` is dropped (apart)
example : ((optFacts b (restrictTreeE true b j0 tX dFG)).contains
      ⟨⟨b, [f, g], .any, .starEx [T]⟩, false⟩,
    (optFacts b (restrictTreeE true b j0 tX dFG)).contains ⟨⟨b, [], .star E1, .starEx [T]⟩, false⟩,
    (optFacts b (restrictTreeE true b j0 tX dFG)).contains ⟨⟨b, [f, g], .any, .star⟩, false⟩,
    (optFacts b (restrictTreeE true b j0 tX dFG)).contains ⟨⟨b, [h], .any, .conc U⟩, false⟩)
    = (true, true, false, false) := by decide

/-! ### 4.3 Cost and sharing -/

-- `D-p = b.f`: 2 levels, 2 new cells + 1 kept child cell; the kept child `.g` is the input's
example : newCells (.star Excl.empty) [f] tE1.tree = 3 := by decide
example : children (endAt [f] (rTree true E1 st MarkSet.empty [f] tE1.tree)).kids =
    children (endAt [f] tE1.tree).kids := by decide

/-! ### 4.4 The emission of version 4 (`emitM`) -/

/-- A fact with a concrete mark. -/
def pc (b : Base) (p : List Acc) (k : Kind) (t : Mark) : PFact := ⟨b, p, k, .conc t⟩

/-- The added facts of §4.1 with their `*` mark, and with the concrete mark `T`. -/
def addsM : List PFact := adds ++ adds.map (fun a => { a with mark := .conc T })

/-- The demand edges of §4.1, and three entry patterns with a concrete mark. -/
def dsM : List DemandEdge :=
  ds ++ [⟨pc 1 [f] st T, none⟩, ⟨pc 1 [f, g] .exact 7, none⟩, ⟨pc 1 [] .any T, none⟩]

-- the index and the base-keyed index find the same initial facts as the scan
example : addsM.all (fun a =>
    sameSetP ((emitCands dsM a).filterMap (fun d => emitM d.din a))
      (dsM.filterMap (fun d => emitM d.din a)) &&
    sameSetP ((nearK dsM a).filterMap (fun d => emitM d.din a))
      (dsM.filterMap (fun d => emitM d.din a))) = true := by decide

-- an exact added fact (two in `addsM`): the prefix walk alone finds the same initial facts
example : (addsM.filter (fun a => a.kind == .exact)).length = 2 ∧
    (addsM.filter (fun a => a.kind == .exact)).all (fun a =>
      sameSetP ((emitPrefCands dsM a).filterMap (fun d => emitM d.din a))
        (dsM.filterMap (fun d => emitM d.din a))) = true := by decide

-- a `*` or an `[any]` added fact at `.f`: the chain `.f.g` below it emits, and the prefix walk
-- misses it (so the subtree half of `near` is necessary for these kinds)
example : [pf 1 [f] st, pf 1 [f] .any].map (fun a =>
    (((emitPrefCands ds a).filterMap (fun d => emitM d.din a)).contains (pf 1 [f, g] st),
     (ds.filterMap (fun d => emitM d.din a)).contains (pf 1 [f, g] st))) =
    [(false, true), (false, true)] := by decide

-- the mark gate: a demand mark `T` admits only the fact mark `T`; a `*` demand mark admits all
example : (emitM (pc 1 [f] st T) (pf 1 [f] st), emitM (pc 1 [f] st T) (pc 1 [f] st 7),
    (emitM (pc 1 [f] st T) (pc 1 [f] st T)).isSome, (emitM (pf 1 [f] st) (pc 1 [f] st 7)).isSome)
    = (none, none, true, true) := by decide

-- the equivalence is on membership: the index gives the facts in another order than the scan
example : ((emitCands ds (pf 1 [f] st)).filterMap (fun d => emitM d.din (pf 1 [f] st)) ==
    ds.filterMap (fun d => emitM d.din (pf 1 [f] st))) = false := by decide

-- the cost at `.f`: the prefix walk visits 2 nodes, `near` visits 3 (the subtree node `.g`)
example : ((demandIdx ds).prefHits [f], nearVisits ds [f]) = (2, 3) := by decide

end Ex

/-! ## 5. Axiom audit of the helpers -/

#print axioms nearBy_iff_around
#print axioms mem_near
#print axioms fNodes_le
#print axioms fromList_pruned
#print axioms mEnts_fromList
#print axioms rC_cons
#print axioms rC_markX
#print axioms root_rC
#print axioms kids_rC
#print axioms mem_keepKids
#print axioms mem_addMarks
#print axioms keepKids_children
#print axioms keepKids_any
#print axioms keepKids_exact
#print axioms rTree_shape
#print axioms rTree_size
#print axioms newCells_eq
#print axioms rCmp_eq
#print axioms rTree_wf
#print axioms rTree_noStar
#print axioms relBelow_path
#print axioms relAbove_path
#print axioms admitsTailB_exact
#print axioms emitM_exactPrefix
#print axioms mem_nearPre
#print axioms nearPre_sub
#print axioms emit_complete_exact
#print axioms emit_lookup_equiv_exact

end ApSpec.RStore
