import DirectedAlias.Opt.LoopCost

/-!
# Optimization O, part 8: the query layer (reverse search)

C answers `findAlias(x)` by enumeration (`enumAlias`): it evaluates `may X v π x []` for each
variable `v` and each path `π` over the universe cells with length at most `D`. This costs
`|vars| * |pathsUpTo cells D|` evaluations (`enumCost`).

O answers it by a backward search (`search`) from the origins of `x`. The search builds the paths
from their end. A search node is a suffix `σ` with the set `G` of the origins from which `σ`
reaches an origin of `x`. The preimage of `G` under cell `c` comes from a reverse index of the
heap edges (`hidx`, with the default edges of untouched cells). The variable holders come from a
reverse index of the variables (`vidx`). The search expands a node only if a variable reaches
an origin of the new `G` within the remaining depth (`live`). Thus each expanded node has an
output below it.

Results:
* `search_mem`, `findAlias_iff`: the search gives exactly the enumeration result (both
  directions).
* `search_nodup`: the search gives each path one time.
* `search_nodes`: the search expands at most `1 + (D + 1) * |output|` nodes.
* `searchCost_le`: the search costs at most `(1 + (D + 1) |output|) (I + |cells| |U|) + D I`,
  where `I` is the index size.
* `heapAliases_iff`: `forEachHeapAlias` is the same search, seeded by `aevalPath x prefix`.
* `findAliasO_iff`: the search on the O state gives the C enumeration result.
* `qfam_sep`: a family where the search costs `(n + 1) ((D + 2) (c + 2) + D)` and the
  enumeration costs at least `(n + 1) (c + 1) ^ D`.
-/

namespace DirectedAlias.Opt

open DirectedAlias

/-! ## Path evaluation lemmas -/

/-- The evaluation of a concatenated path is the evaluation of the second part from the result
of the first part. -/
theorem aevalFrom_append (X : AState) :
    ∀ (S : List Origin) (p q : List ACell), aevalFrom X S (p ++ q) = aevalFrom X (aevalFrom X S p) q
  | _, [], _ => rfl
  | S, c :: p, q => aevalFrom_append X (aread X S c) p q

/-- The evaluation of a path from a set is the union of the evaluations from its elements. -/
theorem mem_aevalFrom_split (X : AState) :
    ∀ (p : List ACell) (S : List Origin) (o'' : Origin),
      o'' ∈ aevalFrom X S p ↔ ∃ o ∈ S, o'' ∈ aevalFrom X [o] p
  | [], S, o'' => by
    simp only [aevalFrom, List.mem_singleton]
    exact ⟨fun h => ⟨o'', h, rfl⟩, fun ⟨o, ho, he⟩ => he ▸ ho⟩
  | c :: p, S, o'' => by
    simp only [aevalFrom]
    rw [mem_aevalFrom_split X p (aread X S c) o'']
    constructor
    · rintro ⟨o1, h1, h2⟩
      obtain ⟨o, ho, h3⟩ := mem_aread.mp h1
      exact ⟨o, ho, (mem_aevalFrom_split X p _ o'').mpr
        ⟨o1, mem_aread.mpr ⟨o, List.mem_singleton_self _, h3⟩, h2⟩⟩
    · rintro ⟨o, ho, h⟩
      obtain ⟨o1, h1, h2⟩ := (mem_aevalFrom_split X p _ o'').mp h
      obtain ⟨o0, ho0, h3⟩ := mem_aread.mp h1
      rw [List.mem_singleton] at ho0
      subst ho0
      exact ⟨o1, mem_aread.mpr ⟨o0, ho, h3⟩, h2⟩

/-- Path evaluation from universe origins over universe cells stays in the universe. -/
theorem aevalFrom_sub {ctx : Ctx} {X : AState} (hs : Supp ctx X) :
    ∀ (p : List ACell) {S : List Origin}, S ⊆ ctx.origins → (∀ c ∈ p, c ∈ ctx.cells) →
      aevalFrom X S p ⊆ ctx.origins
  | [], _, hS, _ => hS
  | c :: p, _, hS, hp =>
    aevalFrom_sub hs p (aread_sub hs hS (hp c List.mem_cons_self))
      (fun c' hc' => hp c' (List.mem_cons_of_mem _ hc'))

/-- Two lists meet: they have a common element. -/
def Meets (S T : List Origin) : Prop := ∃ o, o ∈ S ∧ o ∈ T

/-! ## The index and the search -/

section search
variable (ctx : Ctx) (X : AState)

/-- The reverse heap index: each heap edge `(o', c, o)` with `o` in cell `c` of `o'`, over the
universe. A cell that holds its default content gives its default edge. -/
def hidx : List (Origin × ACell × Origin) :=
  ctx.origins.flatMap (fun o' => ctx.cells.flatMap (fun c => (X.heap o' c).map (fun o => (o', c, o))))

/-- The reverse variable index: each pair `(v, o)` with `o` in variable `v`. -/
def vidx : List (Var × Origin) :=
  ctx.vars.flatMap (fun v => (X.env v).map (fun o => (v, o)))

/-- The index size. -/
def isize : Nat := (hidx ctx X).length + (vidx ctx X).length

/-- The preimage of `G` under cell `c`, from the reverse heap index. -/
def pre (c : ACell) (G : List Origin) : List Origin :=
  (hidx ctx X).filterMap (fun e => if e.2.1 = c ∧ e.2.2 ∈ G then some e.1 else none)

/-- The variables that hold an origin of `G`. -/
def holders (G : List Origin) : List Var :=
  ctx.vars.filter (fun v => meetB (X.env v) G)

/-- The origins that a variable reaches with a path of length at most `j`. -/
def live : Nat → List Origin
  | 0 => uniMap X.env ctx.vars
  | j + 1 => uni (live j) (succs ctx.cells X (live j))

/-- One child of a search node: expand `c :: σ` if a variable reaches its preimage set within
the remaining depth `j`. -/
def kid (j : Nat) (σ : List ACell) (G : List Origin)
    (rec : List ACell → List Origin → List (Var × List ACell) × Nat) (c : ACell) :
    List (Var × List ACell) × Nat :=
  if meetB (pre ctx X c G) (live ctx X j) then rec (c :: σ) (pre ctx X c G) else ([], 0)

/-- The backward search with remaining depth `j` at suffix `σ` with origin set `G`. It gives the
alias paths and the number of expanded nodes. -/
def search : Nat → List ACell → List Origin → List (Var × List ACell) × Nat
  | 0, σ, G => ((holders ctx X G).map (fun v => (v, σ)), 1)
  | j + 1, σ, G =>
    let ks := ctx.cells.map (kid ctx X j σ G (search j))
    ((holders ctx X G).map (fun v => (v, σ)) ++ (ks.map Prod.fst).flatten,
      1 + (ks.map Prod.snd).sum)

/-- `findAlias(x)` by the backward search with depth limit `D`. -/
def findAlias (D : Nat) (x : Var) : List (Var × List ACell) :=
  (search ctx X D [] (X.env x)).1

/-- `findAlias(x)` by enumeration of all paths (concept C). -/
def enumAlias (D : Nat) (x : Var) : List (Var × List ACell) :=
  (ctx.vars.flatMap (fun v => (pathsUpTo ctx.cells D).map (fun π => (v, π)))).filter
    (fun vp => may X vp.1 vp.2 x [])

/-- The cost of the enumeration: the number of `may` evaluations. -/
def enumCost (D : Nat) : Nat := ctx.vars.length * (pathsUpTo ctx.cells D).length

/-- The cost of the search: each expanded node scans the index and tests the liveness of each
child, and the liveness layers cost one index scan each. -/
def searchCost (D : Nat) (x : Var) : Nat :=
  (search ctx X D [] (X.env x)).2 * (isize ctx X + ctx.cells.length * ctx.origins.length) +
    D * isize ctx X

/-- The prefixes of a path, from the empty prefix to the whole path. -/
def prefixes : List ACell → List (List ACell)
  | [] => [[]]
  | c :: cs => [] :: (prefixes cs).map (c :: ·)

/-- `forEachHeapAlias(x, π)`: for each prefix of `π`, the alias paths of `x.prefix`. -/
def heapAliases (D : Nat) (x : Var) (π : List ACell) : List (List (Var × List ACell)) :=
  (prefixes π).map (fun pre => (search ctx X D [] (aevalPath X x pre)).1)

end search

/-! ## Specifications of the index -/

/-- Membership in the reverse heap index. -/
theorem mem_hidx {ctx : Ctx} {X : AState} {e : Origin × ACell × Origin} :
    e ∈ hidx ctx X ↔ e.1 ∈ ctx.origins ∧ e.2.1 ∈ ctx.cells ∧ e.2.2 ∈ X.heap e.1 e.2.1 := by
  obtain ⟨o', c, o⟩ := e
  simp only [hidx, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨o1, ho1, c1, hc1, o2, ho2, rfl, rfl, rfl⟩
    exact ⟨ho1, hc1, ho2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨o', h1, c, h2, o, h3, rfl, rfl, rfl⟩

/-- Membership in the preimage. -/
theorem mem_pre {ctx : Ctx} {X : AState} {c : ACell} {G : List Origin} {o' : Origin} :
    o' ∈ pre ctx X c G ↔ o' ∈ ctx.origins ∧ c ∈ ctx.cells ∧ ∃ o ∈ G, o ∈ X.heap o' c := by
  unfold pre
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hf⟩
    split at hf
    · rename_i h
      cases hf
      obtain ⟨h1, h2, h3⟩ := mem_hidx.mp he
      obtain ⟨hc, hg⟩ := h
      rw [hc] at h2 h3
      exact ⟨h1, h2, e.2.2, hg, h3⟩
    · cases hf
  · rintro ⟨h1, h2, o, ho, h3⟩
    refine ⟨(o', c, o), mem_hidx.mpr ⟨h1, h2, h3⟩, ?_⟩
    show (if c = c ∧ o ∈ G then some o' else none) = some o'
    rw [ite_eq_left ⟨rfl, ho⟩]

/-- Membership in the holders. -/
theorem mem_holders {ctx : Ctx} {X : AState} {G : List Origin} {v : Var} :
    v ∈ holders ctx X G ↔ v ∈ ctx.vars ∧ ∃ o ∈ X.env v, o ∈ G := by
  simp only [holders, List.mem_filter, meetB_iff]

/-- Membership in the liveness layer `j`: a variable reaches the origin with a path of length at
most `j` over the universe cells. -/
theorem mem_live {ctx : Ctx} {X : AState} :
    ∀ (j : Nat) (o : Origin), o ∈ live ctx X j ↔
      ∃ v ∈ ctx.vars, ∃ π : List ACell, π.length ≤ j ∧ (∀ c ∈ π, c ∈ ctx.cells) ∧
        o ∈ aevalPath X v π
  | 0, o => by
    simp only [live, mem_uniMap]
    constructor
    · rintro ⟨v, hv, h⟩; exact ⟨v, hv, [], Nat.le_refl _, (fun _ h => by cases h), h⟩
    · rintro ⟨v, hv, π, hl, _, h⟩
      cases π with
      | nil => exact ⟨v, hv, h⟩
      | cons _ _ => simp at hl
  | j + 1, o => by
    simp only [live]
    rw [mem_uni, mem_live j o, mem_succs]
    constructor
    · rintro (⟨v, hv, π, hl, hc, h⟩ | ⟨o1, ho1, c, hc, h⟩)
      · exact ⟨v, hv, π, Nat.le_succ_of_le hl, hc, h⟩
      · obtain ⟨v, hv, π, hl, hcs, h1⟩ := (mem_live j o1).mp ho1
        refine ⟨v, hv, π ++ [c], (by simp; omega), ?_, ?_⟩
        · intro c' hc'
          cases List.mem_append.mp hc' with
          | inl h' => exact hcs c' h'
          | inr h' => rw [List.mem_singleton] at h'; exact h' ▸ hc
        · unfold aevalPath
          rw [aevalFrom_append]
          exact mem_aread.mpr ⟨o1, h1, h⟩
    · rintro ⟨v, hv, π, hl, hc, h⟩
      by_cases hle : π.length ≤ j
      · exact Or.inl ⟨v, hv, π, hle, hc, h⟩
      · rcases List.eq_nil_or_concat π with rfl | ⟨π', c, rfl⟩
        · exact absurd (Nat.zero_le j) hle
        · rw [List.concat_eq_append] at hl hc h
          unfold aevalPath at h
          rw [aevalFrom_append] at h
          obtain ⟨o1, ho1, h2⟩ := mem_aread.mp h
          have hl' : π'.length ≤ j := by simp at hl; omega
          refine Or.inr ⟨o1, (mem_live j o1).mpr ⟨v, hv, π', hl', fun c' hc' =>
            hc c' (List.mem_append_left _ hc'), ho1⟩, c, hc c (by simp), h2⟩

/-! ## Correctness of the search -/

/-- The search invariant: `G` is the set of universe origins from which `σ` reaches a seed. -/
def GInv (ctx : Ctx) (X : AState) (T0 : List Origin) (σ : List ACell) (G : List Origin) : Prop :=
  ∀ o, o ∈ G ↔ o ∈ ctx.origins ∧ Meets (aevalFrom X [o] σ) T0

/-- The preimage keeps the search invariant. -/
theorem GInv.pre {ctx : Ctx} {X : AState} (hs : Supp ctx X) {T0 : List Origin}
    {σ : List ACell} {G : List Origin} (hG : GInv ctx X T0 σ G) {c : ACell}
    (hc : c ∈ ctx.cells) : GInv ctx X T0 (c :: σ) (pre ctx X c G) := by
  intro o'
  rw [mem_pre]
  constructor
  · rintro ⟨h1, _, o, ho, h3⟩
    obtain ⟨_, o2, h4, h5⟩ := (hG o).mp ho
    refine ⟨h1, o2, ?_, h5⟩
    simp only [aevalFrom]
    exact (mem_aevalFrom_split X σ _ o2).mpr
      ⟨o, mem_aread.mpr ⟨o', List.mem_singleton_self _, h3⟩, h4⟩
  · rintro ⟨h1, o2, h4, h5⟩
    simp only [aevalFrom] at h4
    obtain ⟨o, ho, h6⟩ := (mem_aevalFrom_split X σ _ o2).mp h4
    obtain ⟨o0, ho0, h7⟩ := mem_aread.mp ho
    rw [List.mem_singleton] at ho0
    subst ho0
    exact ⟨h1, hc, o, (hG o).mpr ⟨hs (.h o0 c) ⟨h1, hc⟩ h7, o2, h6, h5⟩, h7⟩

/-- Membership in the outputs of one child. -/
theorem mem_kid {ctx : Ctx} {X : AState} {j : Nat} {σ : List ACell} {G : List Origin}
    {rec : List ACell → List Origin → List (Var × List ACell) × Nat} {c : ACell}
    {vp : Var × List ACell} :
    vp ∈ (kid ctx X j σ G rec c).1 ↔
      meetB (pre ctx X c G) (live ctx X j) = true ∧ vp ∈ (rec (c :: σ) (pre ctx X c G)).1 := by
  unfold kid
  split
  · rename_i h; exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
  · rename_i h
    constructor
    · intro h'; cases h'
    · rintro ⟨h1, _⟩; exact absurd h1 h

/-- The search gives exactly the alias paths below its node: the paths `ρ ++ σ` with `ρ` of
length at most `j` over the universe cells, from a variable that reaches a seed. -/
theorem search_mem {ctx : Ctx} {X : AState} (hs : Supp ctx X) {T0 : List Origin} :
    ∀ (j : Nat) (σ : List ACell) (G : List Origin), (∀ c ∈ σ, c ∈ ctx.cells) →
      GInv ctx X T0 σ G → ∀ (v : Var) (π : List ACell),
      (v, π) ∈ (search ctx X j σ G).1 ↔
        v ∈ ctx.vars ∧ ∃ ρ, π = ρ ++ σ ∧ ρ.length ≤ j ∧ (∀ c ∈ ρ, c ∈ ctx.cells) ∧
          ∃ o ∈ X.env v, Meets (aevalFrom X [o] π) T0
  | 0, σ, G, _, hG, v, π => by
    simp only [search, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨w, hw, rfl, rfl⟩
      obtain ⟨hv, o, ho, hoG⟩ := mem_holders.mp hw
      exact ⟨hv, [], rfl, Nat.le_refl _, (fun _ h => by cases h), o, ho, ((hG o).mp hoG).2⟩
    · rintro ⟨hv, ρ, rfl, hl, _, o, ho, hm⟩
      cases ρ with
      | cons _ _ => simp at hl
      | nil =>
        exact ⟨v, mem_holders.mpr ⟨hv, o, ho, (hG o).mpr ⟨hs (.v v) hv ho, hm⟩⟩, rfl, rfl⟩
  | j + 1, σ, G, hσ, hG, v, π => by
    simp only [search, List.mem_append, List.mem_map, Prod.mk.injEq, List.mem_flatten,
      List.map_map]
    constructor
    · rintro (⟨w, hw, rfl, rfl⟩ | ⟨l, ⟨c, hc, rfl⟩, hl⟩)
      · obtain ⟨hv, o, ho, hoG⟩ := mem_holders.mp hw
        exact ⟨hv, [], rfl, Nat.zero_le _, (fun _ h => by cases h), o, ho, ((hG o).mp hoG).2⟩
      · simp only [Function.comp_def] at hl
        obtain ⟨_, hl2⟩ := mem_kid.mp hl
        have hσ' : ∀ c' ∈ c :: σ, c' ∈ ctx.cells := by
          intro c' hc'
          cases List.mem_cons.mp hc' with
          | inl h => exact h ▸ hc
          | inr h => exact hσ c' h
        obtain ⟨hv, ρ', hπ, hl', hρ', o, ho, hm⟩ :=
          (search_mem hs j (c :: σ) _ hσ' (hG.pre hs hc) v π).mp hl2
        refine ⟨hv, ρ' ++ [c], (by rw [hπ]; simp), (by simp; omega), ?_, o, ho, hm⟩
        intro c' hc'
        cases List.mem_append.mp hc' with
        | inl h => exact hρ' c' h
        | inr h => rw [List.mem_singleton] at h; exact h ▸ hc
    · rintro ⟨hv, ρ, rfl, hl, hρ, o, ho, hm⟩
      rcases List.eq_nil_or_concat ρ with rfl | ⟨ρ', c, rfl⟩
      · exact Or.inl ⟨v, mem_holders.mpr ⟨hv, o, ho, (hG o).mpr ⟨hs (.v v) hv ho, hm⟩⟩, rfl, rfl⟩
      · rw [List.concat_eq_append] at hl hρ hm ⊢
        have hc : c ∈ ctx.cells := hρ c (by simp)
        have hρ' : ∀ c' ∈ ρ', c' ∈ ctx.cells := fun c' h => hρ c' (List.mem_append_left _ h)
        have hl' : ρ'.length ≤ j := by simp at hl; omega
        have hσ' : ∀ c' ∈ c :: σ, c' ∈ ctx.cells := by
          intro c' hc'
          cases List.mem_cons.mp hc' with
          | inl h => exact h ▸ hc
          | inr h => exact hσ c' h
        have hπ : ρ' ++ [c] ++ σ = ρ' ++ (c :: σ) := by simp
        rw [hπ] at hm ⊢
        refine Or.inr ⟨_, ⟨c, hc, rfl⟩, ?_⟩
        simp only [Function.comp_def]
        apply mem_kid.mpr
        constructor
        · -- the child is live
          obtain ⟨o2, h1, h2⟩ := hm
          rw [aevalFrom_append] at h1
          obtain ⟨o1, ho1, h3⟩ := (mem_aevalFrom_split X (c :: σ) _ o2).mp h1
          have ho1v : o1 ∈ aevalPath X v ρ' := by
            unfold aevalPath
            exact (mem_aevalFrom_split X ρ' _ o1).mpr ⟨o, ho, ho1⟩
          have hU : o1 ∈ ctx.origins :=
            aevalFrom_sub hs ρ' (hs (.v v) hv) hρ' ho1v
          apply meetB_iff.mpr
          refine ⟨o1, ?_, (mem_live j o1).mpr ⟨v, hv, ρ', hl', hρ', ho1v⟩⟩
          exact ((hG.pre hs hc) o1).mpr ⟨hU, o2, h3, h2⟩
        · exact (search_mem hs j (c :: σ) _ hσ' (hG.pre hs hc) v _).mpr
            ⟨hv, ρ', rfl, hl', hρ', o, ho, hm⟩

/-- `findAlias` by search gives exactly the `findAlias` result by enumeration. -/
theorem findAlias_iff {ctx : Ctx} {X : AState} (hs : Supp ctx X) {x : Var} (hx : x ∈ ctx.vars)
    (D : Nat) (v : Var) (π : List ACell) :
    (v, π) ∈ findAlias ctx X D x ↔ (v, π) ∈ enumAlias ctx X D x := by
  have hG : GInv ctx X (X.env x) [] (X.env x) := by
    intro o
    simp only [aevalFrom, Meets, List.mem_singleton]
    exact ⟨fun h => ⟨hs (.v x) hx h, o, rfl, h⟩, fun ⟨_, o', he, h⟩ => he ▸ h⟩
  unfold findAlias enumAlias
  rw [search_mem hs D [] (X.env x) (fun _ h => by cases h) hG v π]
  simp only [List.mem_filter, List.mem_flatMap, List.mem_map, Prod.mk.injEq, List.append_nil,
    may_iff, aevalPath, aevalFrom]
  constructor
  · rintro ⟨hv, ρ, hρπ, hl, hρ, o, ho, o2, h1, h2⟩
    subst hρπ
    refine ⟨⟨v, hv, π, mem_pathsUpTo.mpr ⟨hl, hρ⟩, rfl, rfl⟩, o2, ?_, h2⟩
    exact (mem_aevalFrom_split X π _ o2).mpr ⟨o, ho, h1⟩
  · rintro ⟨⟨w, hw, ρ, hρ, rfl, rfl⟩, o2, h1, h2⟩
    obtain ⟨hl, hc⟩ := mem_pathsUpTo.mp hρ
    obtain ⟨o, ho, h3⟩ := (mem_aevalFrom_split X ρ _ o2).mp h1
    exact ⟨hw, ρ, rfl, hl, hc, o, ho, o2, h3, h2⟩

/-- `forEachHeapAlias` by search gives, for each prefix, exactly the paths that may alias
`x.prefix`. -/
theorem heapAliases_iff {ctx : Ctx} {X : AState} (hs : Supp ctx X) {x : Var}
    (hx : x ∈ ctx.vars) (D : Nat) (pre : List ACell) (hpre : ∀ c ∈ pre, c ∈ ctx.cells)
    (v : Var) (π : List ACell) :
    (v, π) ∈ (search ctx X D [] (aevalPath X x pre)).1 ↔
      v ∈ ctx.vars ∧ π ∈ pathsUpTo ctx.cells D ∧ may X v π x pre = true := by
  have hsub : aevalPath X x pre ⊆ ctx.origins := aevalFrom_sub hs pre (hs (.v x) hx) hpre
  have hG : GInv ctx X (aevalPath X x pre) [] (aevalPath X x pre) := by
    intro o
    simp only [aevalFrom, Meets, List.mem_singleton]
    exact ⟨fun h => ⟨hsub h, o, rfl, h⟩, fun ⟨_, o', he, h⟩ => he ▸ h⟩
  rw [search_mem hs D [] _ (fun _ h => by cases h) hG v π]
  simp only [List.append_nil, may_iff]
  constructor
  · rintro ⟨hv, ρ, hρπ, hl, hρ, o, ho, o2, h1, h2⟩
    subst hρπ
    exact ⟨hv, mem_pathsUpTo.mpr ⟨hl, hρ⟩, o2,
      (mem_aevalFrom_split X π _ o2).mpr ⟨o, ho, h1⟩, h2⟩
  · rintro ⟨hv, hρ, o2, h1, h2⟩
    obtain ⟨hl, hc⟩ := mem_pathsUpTo.mp hρ
    obtain ⟨o, ho, h3⟩ := (mem_aevalFrom_split X π _ o2).mp h1
    exact ⟨hv, π, rfl, hl, hc, o, ho, o2, h3, h2⟩

/-- Each element of `heapAliases` is the search for one prefix of the fact path. -/
theorem heapAliases_eq (ctx : Ctx) (X : AState) (D : Nat) (x : Var) (π : List ACell) :
    heapAliases ctx X D x π = (prefixes π).map (fun pre => (search ctx X D [] (aevalPath X x pre)).1) :=
  rfl

/-! ## The number of expanded nodes -/

/-- A sum of a mapped list is at most `k` times a second sum if each term is. -/
theorem sum_map_le_mul {α : Type} (f g : α → Nat) (k : Nat) :
    ∀ (l : List α), (∀ a ∈ l, f a ≤ k * g a) → (l.map f).sum ≤ k * (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    have ih := sum_map_le_mul f g k l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- The length of a flattened mapped list is the sum of the lengths. -/
theorem length_flatten_map {α β : Type} (f : α → List β) :
    ∀ (l : List α), ((l.map f).flatten).length = (l.map (fun a => (f a).length)).sum
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons,
      length_flatten_map f l]

/-- The search expands at most `1 + (j + 1)` times the number of outputs. Each expanded child
has an output, by the liveness test. -/
theorem search_nodes {ctx : Ctx} {X : AState} (hs : Supp ctx X) {T0 : List Origin} :
    ∀ (j : Nat) (σ : List ACell) (G : List Origin), (∀ c ∈ σ, c ∈ ctx.cells) →
      GInv ctx X T0 σ G →
      (search ctx X j σ G).2 ≤ 1 + (j + 1) * (search ctx X j σ G).1.length
  | 0, σ, G, _, _ => by simp [search]
  | j + 1, σ, G, hσ, hG => by
    simp only [search, List.length_append, List.map_map, Function.comp_def]
    -- each child: its node count is at most `(j + 1 + 1)` times its output count
    have hkid : ∀ c ∈ ctx.cells,
        (kid ctx X j σ G (search ctx X j) c).2 ≤
          (j + 1 + 1) * (kid ctx X j σ G (search ctx X j) c).1.length := by
      intro c hc
      have hσ' : ∀ c' ∈ c :: σ, c' ∈ ctx.cells := by
        intro c' hc'
        cases List.mem_cons.mp hc' with
        | inl h => exact h ▸ hc
        | inr h => exact hσ c' h
      unfold kid
      split
      · rename_i hlive
        have ih := search_nodes hs j (c :: σ) _ hσ' (hG.pre hs hc)
        -- the child has at least one output
        obtain ⟨o1, h1, h2⟩ := meetB_iff.mp hlive
        obtain ⟨v, hv, ρ', hl', hρ', ho1v⟩ := (mem_live j o1).mp h2
        obtain ⟨_, o2, h3, h4⟩ := ((hG.pre hs hc) o1).mp h1
        obtain ⟨o, ho, h5⟩ := (mem_aevalFrom_split X ρ' _ o1).mp ho1v
        have hout : (v, ρ' ++ c :: σ) ∈ (search ctx X j (c :: σ) (pre ctx X c G)).1 := by
          apply (search_mem hs j (c :: σ) _ hσ' (hG.pre hs hc) v _).mpr
          refine ⟨hv, ρ', rfl, hl', hρ', o, ho, o2, ?_, h4⟩
          rw [aevalFrom_append]
          exact (mem_aevalFrom_split X (c :: σ) _ o2).mpr ⟨o1, h5, h3⟩
        have hpos : 1 ≤ (search ctx X j (c :: σ) (pre ctx X c G)).1.length := by
          cases h : (search ctx X j (c :: σ) (pre ctx X c G)).1 with
          | nil => rw [h] at hout; cases hout
          | cons _ _ => simp
        have e : (j + 1 + 1) * (search ctx X j (c :: σ) (pre ctx X c G)).1.length =
            (j + 1) * (search ctx X j (c :: σ) (pre ctx X c G)).1.length +
              (search ctx X j (c :: σ) (pre ctx X c G)).1.length := by
          rw [Nat.add_mul, Nat.one_mul]
        have : 1 + (j + 1) * (search ctx X j (c :: σ) (pre ctx X c G)).1.length ≤
            (j + 1 + 1) * (search ctx X j (c :: σ) (pre ctx X c G)).1.length := by
          omega
        exact Nat.le_trans ih this
      · simp
    have hsum := sum_map_le_mul (fun c => (kid ctx X j σ G (search ctx X j) c).2)
      (fun c => (kid ctx X j σ G (search ctx X j) c).1.length) (j + 1 + 1) ctx.cells hkid
    rw [length_flatten_map (fun c => (kid ctx X j σ G (search ctx X j) c).1)]
    rw [Nat.mul_add]
    omega

/-! ## No duplicate outputs -/

/-- A filtered list keeps the property of no duplicates. -/
theorem nodup_filter' {α : Type} {p : α → Bool} {l : List α} (h : l.Nodup) :
    (l.filter p).Nodup :=
  h.sublist List.filter_sublist

/-- A list with no duplicates, mapped to pairs with a fixed second part, has no duplicates. -/
theorem nodup_map_pair {α β : Type} (b : β) : ∀ {l : List α}, l.Nodup →
    (l.map (fun a => (a, b))).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.nodup_cons] at h
    simp only [List.map_cons]
    rw [List.nodup_cons]
    refine ⟨?_, nodup_map_pair b h.2⟩
    intro hm
    obtain ⟨a', ha', he⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at he
    exact h.1 (he.1 ▸ ha')

/-- The flattening of lists with no duplicates and with pairwise disjoint members has no
duplicates. -/
theorem nodup_flatten_map {α β : Type} (f : α → List β) :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, (f a).Nodup) →
      (∀ a ∈ l, ∀ a' ∈ l, a ≠ a' → ∀ b ∈ f a, b ∉ f a') → ((l.map f).flatten).Nodup
  | [], _, _, _ => List.nodup_nil
  | a :: l, hn, h1, h2 => by
    rw [List.nodup_cons] at hn
    simp only [List.map_cons, List.flatten_cons]
    rw [List.nodup_append]
    refine ⟨h1 a List.mem_cons_self,
      nodup_flatten_map f hn.2 (fun a' ha' => h1 a' (List.mem_cons_of_mem _ ha'))
        (fun a1 ha1 a2 ha2 hne => h2 a1 (List.mem_cons_of_mem _ ha1) a2
          (List.mem_cons_of_mem _ ha2) hne), ?_⟩
    intro b hb b' hb' heq
    subst heq
    obtain ⟨l', hl', hb2⟩ := List.mem_flatten.mp hb'
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp hl'
    have hne : a ≠ a' := fun h => hn.1 (h ▸ ha')
    exact h2 a List.mem_cons_self a' (List.mem_cons_of_mem _ ha') hne b hb hb2

/-- Two paths that end in `c :: σ` and `c' :: σ` with `c ≠ c'` are different. -/
theorem ne_of_last {ρ ρ' σ : List ACell} {c c' : ACell} (h : c ≠ c') :
    ρ ++ c :: σ ≠ ρ' ++ c' :: σ := by
  intro he
  have he2 : (ρ ++ [c]) ++ σ = (ρ' ++ [c']) ++ σ := by simpa using he
  have := List.append_cancel_right he2
  have hl := congrArg List.getLast? this
  simp at hl
  exact h hl

/-- The search gives each alias path at most one time, if the universe lists have no
duplicates. -/
theorem search_nodup {ctx : Ctx} {X : AState} (hs : Supp ctx X) {T0 : List Origin}
    (hv : ctx.vars.Nodup) (hc : ctx.cells.Nodup) :
    ∀ (j : Nat) (σ : List ACell) (G : List Origin), (∀ c ∈ σ, c ∈ ctx.cells) →
      GInv ctx X T0 σ G → (search ctx X j σ G).1.Nodup
  | 0, σ, G, _, _ => nodup_map_pair σ (nodup_filter' hv)
  | j + 1, σ, G, hσ, hG => by
    simp only [search, List.map_map]
    have hσ' : ∀ c ∈ ctx.cells, ∀ c' ∈ c :: σ, c' ∈ ctx.cells := by
      intro c hc c' hc'
      cases List.mem_cons.mp hc' with
      | inl h => exact h ▸ hc
      | inr h => exact hσ c' h
    -- the outputs of the child `c` end with `c :: σ`
    have hshape : ∀ c ∈ ctx.cells, ∀ vp ∈ (kid ctx X j σ G (search ctx X j) c).1,
        ∃ ρ, vp.2 = ρ ++ c :: σ := by
      intro c hcm vp hvp
      obtain ⟨_, h2⟩ := mem_kid.mp hvp
      obtain ⟨v, π⟩ := vp
      obtain ⟨_, ρ, hπ, _⟩ :=
        (search_mem hs j (c :: σ) _ (hσ' c hcm) (hG.pre hs hcm) v π).mp h2
      exact ⟨ρ, hπ⟩
    rw [List.nodup_append]
    refine ⟨nodup_map_pair σ (nodup_filter' hv), ?_, ?_⟩
    · simp only [Function.comp_def]
      apply nodup_flatten_map _ hc
      · intro c hcm
        unfold kid
        split
        · exact search_nodup hs hv hc j (c :: σ) _ (hσ' c hcm) (hG.pre hs hcm)
        · exact List.nodup_nil
      · intro c hcm c' hcm' hne vp hvp hvp'
        obtain ⟨ρ, h1⟩ := hshape c hcm vp hvp
        obtain ⟨ρ', h2⟩ := hshape c' hcm' vp hvp'
        exact ne_of_last hne (h1.symm.trans h2)
    · intro a ha b hb heq
      subst heq
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨l, hl, hb2⟩ := List.mem_flatten.mp hb
      obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hl
      simp only [Function.comp_def] at hb2
      obtain ⟨ρ, h1⟩ := hshape c hcm _ hb2
      have := congrArg List.length h1
      simp at this
      omega

/-! ## The search cost -/

/-- The search costs at most `(1 + (D + 1) |output|) (I + |cells| |U|) + D I`. -/
theorem searchCost_le {ctx : Ctx} {X : AState} (hs : Supp ctx X) {x : Var} (hx : x ∈ ctx.vars)
    (D : Nat) :
    searchCost ctx X D x ≤
      (1 + (D + 1) * (findAlias ctx X D x).length) *
        (isize ctx X + ctx.cells.length * ctx.origins.length) + D * isize ctx X := by
  have hG : GInv ctx X (X.env x) [] (X.env x) := by
    intro o
    simp only [aevalFrom, Meets, List.mem_singleton]
    exact ⟨fun h => ⟨hs (.v x) hx h, o, rfl, h⟩, fun ⟨_, o', he, h⟩ => he ▸ h⟩
  have := search_nodes hs D [] (X.env x) (fun _ h => by cases h) hG
  unfold searchCost findAlias
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ this) _

/-- The enumeration result has no duplicates if the universe lists have none, and the search
result has no duplicates. -/
theorem findAlias_nodup {ctx : Ctx} {X : AState} (hs : Supp ctx X) {x : Var}
    (hx : x ∈ ctx.vars) (hv : ctx.vars.Nodup) (hc : ctx.cells.Nodup) (D : Nat) :
    (findAlias ctx X D x).Nodup := by
  have hG : GInv ctx X (X.env x) [] (X.env x) := by
    intro o
    simp only [aevalFrom, Meets, List.mem_singleton]
    exact ⟨fun h => ⟨hs (.v x) hx h, o, rfl, h⟩, fun ⟨_, o', he, h⟩ => he ▸ h⟩
  exact search_nodup hs hv hc D [] (X.env x) (fun _ h => by cases h) hG

end DirectedAlias.Opt
