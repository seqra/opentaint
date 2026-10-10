/-
  A complete executable tree reference for current mark-aware summary reduction.

  The reference reads each leaf, applies restrictI, then rebuilds one tree with
  the same exclusion, mark exclusion and layer. Exact whole-fact membership is
  proved for every tree and demand. This is a reference implementation, not a
  proof of a shared-subtree shortcut. CurrentDemand proves the independent
  demand-prefix index optimization and its practical query cost.
-/
import ApSpec.CurrentDemand

namespace ApSpec.CurrentTreeReduction
open ApSpec ApSpec.Handoff ApSpec.Tree

private theorem pay_fits {E : Excl} {pl : Payload} {x : RFact}
    (hx : x ∈ payRF E pl) : fitsB E x.kind x.mark = true := by
  rcases mem_payRF.mp hx with ⟨_, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
  · simp [fitsB]
  all_goals cases m <;> first | rfl | cases hm

private theorem trie_fits (E : Excl) (k : Trie) :
    ∀ x, x ∈ trieRF E k → fitsB E x.kind x.mark = true := by
  induction k with
  | nil => intro x hx; cases hx
  | cons a h bl nx ihb ihn =>
    intro x hx
    rw [trieRF_cons] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases List.mem_append.mp hy with hy | hy
      · exact pay_fits (x := y) hy
      · exact ihb y hy
    · exact ihn x hx

private theorem tree_fits (E : Excl) (t : Tree) (x : RFact)
    (hx : x ∈ treeRF E t) : fitsB E x.kind x.mark = true := by
  rcases List.mem_append.mp hx with hx | hx
  · exact pay_fits hx
  · exact trie_fits E t.kids x hx

private theorem read_fits {E : Excl} {X : List Mark} {k : Kind} {m : MarkA}
    (h : fitsB E k m = true) : fitsX E X k (mxMark X m) = true := by
  cases m with
  | star =>
    cases X with
    | nil => simpa [fitsX, mxMark, starM, stripM, markFitsB] using h
    | cons t xs => simpa [fitsX, mxMark, starM, stripM, markFitsB] using h
  | conc t => simpa [fitsX, mxMark, stripM, markFitsB] using h
  | starEx xs => cases k <;> cases h

/-- The tree itself supplies all base, layer and encoding invariants. -/
theorem leaf_shape {b : Base} {t : EdgeTree} {c : AFact} (hc : c ∈ toAFacts b t) :
    c.fact.base = b ∧ c.demand = t.demand ∧ fitsX t.excl t.mx c.fact.kind c.fact.mark = true := by
  obtain ⟨x, hx, rfl⟩ := (mem_toAFacts b t c).mp hc
  exact ⟨rfl, rfl, read_fits (tree_fits t.excl t.tree x hx)⟩

private theorem nonstar_fits (E : Excl) (X : List Mark) (m : MarkA) :
    fitsX E X .exact m = markFitsB X m ∧
    fitsX E X .any m = markFitsB X m := by
  cases m <;> exact ⟨rfl, rfl⟩

private theorem meet_fits {E : Excl} {X : List Mark} {k : Kind} {m : MarkA}
    (h : fitsX E X k m = true) (dk : Kind) : fitsX E X (meetConcK k dk) m = true := by
  cases k with
  | star e => exact h
  | exact => exact h
  | any => cases dk with
    | star e => exact h
    | any => exact h
    | exact => exact (nonstar_fits E X m).1.trans ((nonstar_fits E X m).2.symm.trans h)

/-- Reduction keeps every component needed to rebuild the original tree key. -/
theorem reduction_shape {j : PFact} {g g' : AFact} {d : DemandEdge}
    {E : Excl} {X : List Mark} (hr : restrictI j g d = some g')
    (hf : fitsX E X g.fact.kind g.fact.mark = true) :
    g'.fact.base = g.fact.base ∧ g'.demand = g.demand ∧
    fitsX E X g'.fact.kind g'.fact.mark = true := by
  obtain ⟨p, _, _, hc⟩ := restrictI_some hr
  obtain ⟨_, ⟨_, he⟩ | ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, _, _, he⟩⟩ :=
    restrictConcI_cases hc
  · subst he
    exact ⟨rfl, rfl, meet_fits hf p.kind⟩
  · subst he; exact ⟨rfl, rfl, hf⟩
  · subst he
    refine ⟨rfl, rfl, ?_⟩
    have hm := (fitsX_parts hf).2
    cases p.kind with
    | exact => exact (nonstar_fits E X g.fact.mark).1.trans hm
    | any => exact (nonstar_fits E X g.fact.mark).2.trans hm
    | star e => exact (nonstar_fits E X g.fact.mark).2.trans hm
  · subst he; exact ⟨rfl, rfl, hf⟩

def reduceLeaves (b : Base) (j : PFact) (t : EdgeTree) (d : DemandEdge) : List AFact :=
  (toAFacts b t).filterMap (fun g => restrictI j g d)

/-- The key is unchanged; each reduced fact is stored in its correct payload. -/
def reduceTree (b : Base) (j : PFact) (t : EdgeTree) (d : DemandEdge) : EdgeTree :=
  ⟨t.excl, t.mx, t.demand, fromList ((reduceLeaves b j t d).map (·.fact))⟩

theorem reduced_leaf_shape {b : Base} {j : PFact} {t : EdgeTree} {d : DemandEdge} {a : AFact}
    (ha : a ∈ reduceLeaves b j t d) :
    a.fact.base = b ∧ a.demand = t.demand ∧ fitsX t.excl t.mx a.fact.kind a.fact.mark = true := by
  obtain ⟨g, hg, hr⟩ := List.mem_filterMap.mp ha
  obtain ⟨hb, hd, hf⟩ := leaf_shape hg
  obtain ⟨hb', hd', hf'⟩ := reduction_shape hr hf
  exact ⟨hb'.trans hb, hd'.trans hd, hf'⟩

/-- Exact whole-fact membership, including demand layer and mark exclusions. -/
theorem tree_reference_equiv (b : Base) (j : PFact) (t : EdgeTree) (d : DemandEdge) (a : AFact) :
    a ∈ toAFacts b (reduceTree b j t d) ↔ a ∈ reduceLeaves b j t d := by
  have hb : ∀ f, f ∈ (reduceLeaves b j t d).map (·.fact) → f.base = b := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact (reduced_leaf_shape hg).1
  have hf : ∀ f, f ∈ (reduceLeaves b j t d).map (·.fact) → fitsX t.excl t.mx f.kind f.mark = true := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact (reduced_leaf_shape hg).2.2
  rw [reduceTree, fromList_mem b t.excl t.mx t.demand _ hb hf]
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    have hd := (reduced_leaf_shape hg).2.1
    cases g with
    | mk f dm => dsimp only at hd; cases hd; exact hg
  · intro ha
    exact ⟨a.fact, List.mem_map.mpr ⟨a, ha, rfl⟩, by
      cases a with
      | mk f dm => have hd := (reduced_leaf_shape ha).2.1; dsimp only at hd; cases hd; rfl⟩

theorem tree_reference_wf (b : Base) (j : PFact) (t : EdgeTree) (d : DemandEdge) :
    (reduceTree b j t d).tree.wf = true := fromList_wf _

theorem tree_reference_key (b : Base) (j : PFact) (t : EdgeTree) (d : DemandEdge) :
    (reduceTree b j t d).excl = t.excl ∧ (reduceTree b j t d).mx = t.mx ∧
    (reduceTree b j t d).demand = t.demand := ⟨rfl, rfl, rfl⟩

/-! Executable vectors cover the two differences from the historical S tree walk. -/

def input : EdgeTree := ⟨.set [8], [3], true, fromList [
    ⟨5, [], .any, .conc 1⟩,
    ⟨5, [], .any, .conc 2⟩,
    ⟨5, [], .any, .starEx [3]⟩,
    ⟨5, [4], .exact, .conc 1⟩]⟩
def premise : PFact := ⟨3, [], .exact, .star⟩
def demand : DemandEdge := ⟨premise, some ⟨5, [], .exact, .conc 1⟩⟩
def expected : List AFact := [
  ⟨⟨5, [], .exact, .conc 1⟩, true⟩,
  ⟨⟨5, [], .exact, .starEx [3]⟩, true⟩]

theorem reference_vectors :
    expected.all (fun a => (toAFacts 5 (reduceTree 5 premise input demand)).contains a) = true ∧
    (toAFacts 5 (reduceTree 5 premise input demand)).all (fun a => expected.contains a) = true :=
  by decide

/-- The tree can be evaluated and retains the selected mark gate and exact cut. -/
def treeWitness : {t : EdgeTree // t = reduceTree 5 premise input demand ∧
    t.tree.wf = true ∧ t.excl = input.excl ∧ t.mx = input.mx ∧ t.demand = true ∧
    expected.all (fun a => (toAFacts 5 t).contains a) = true ∧
    (toAFacts 5 t).all (fun a => expected.contains a) = true} :=
  ⟨reduceTree 5 premise input demand, rfl, tree_reference_wf _ _ _ _, rfl, rfl, rfl,
    reference_vectors.1, reference_vectors.2⟩

#eval toAFacts 5 treeWitness.val
#print axioms tree_reference_equiv
#print axioms tree_reference_wf
#print axioms treeWitness

end ApSpec.CurrentTreeReduction
