import ApSpec.BackNDRefine
import ApSpec.BackCondRules
import ApSpec.BackCondExamples

/-!
# ApSpec.BackCondImpl — the implementation level of the backward condition progress

Source: `spec/backward-condition-progress.md` (the rules) and
`spec/backward-condition-progress-implementation.md` §6 (this module). The rule level is
`BackCond` (the seed layer) and `BackND` (the capture tree). This module states what the CODE
does and proves that it keeps the rule-level results.

## What the code does, and what is proved

1. SEED LAYER. `seedFact` puts a requirement in the NORMAL layer iff the literal is unary and has
   the `$` tail (`seedDemand`). A predicate sink reads `RulePredicate.isUnary`, which is the DNF
   reading (`Form.single_iff`); a legacy sink computes `legacyUnary` from all alternatives of its
   rule at the statement (`Form.single_eq_legacy`). `code_normal_iff`: with duplicate-free
   alternatives the code layer is the rule layer `BackCond.reqs_normal_iff` (K1, K3, K5);
   `code_normal_must`: a NORMAL code seed is MUST for every condition.
2. NORMAL FORM. A captured input with a concrete mark `t` is stored with the literal mark `T` (the
   check matched it, `t = T`) and with the field tail `*/e` read as `[any]` with the exclusion `e`
   (`nfFact`, `nfEx`). An input with the abstract mark (`*`, `*∖x`: a FLOW fact) has no production
   site (a conditional literal never holds on a FLOW fact, proposal §3 code fact F4); if one
   arrives, the code stores the literal itself (`nfOne`). `nfOne_cov`: the stored form covers each
   location with the literal mark that the input covers. `ncap_wf`: with legal literals the
   stored form is a legal capture (concrete mark, tail `$`/`[any]`).
3. ONE TREE IN ARRIVAL ORDER. The code inserts the leaves one at a time (`List.foldl`), the rule
   model merges them with `List.foldr`. `mergeL_cov`: the code tree serves exactly the stored
   leaves, so it serves the same locations as `BackND.mergeLeaves` (`mergeL_mergeLeaves_cov`).
4. CODE SEEDS. `codeSeeds`: the code tree of each literal, the literal itself if the tree is
   empty. `codeSeeds_sound` (each real route location of a literal is served), `codeSeeds_inside`
   (each seed lies inside its literal), `codeSeeds_legal` (tail `$`/`[any]`, concrete mark),
   `codeSeeds_deepens` (G1 and G2 for each leaf, against the input in normal form).
5. THE BACKWARD CONTRACT WITH THE CODE SEEDS (the open item of spec §II.7, now proved):
   `seedsCover_code`, `B_general_code`, `iteration_general_code`.
6. VECTORS (`Vec`): the `*/E` start of a C2 cut, the spine exclusion, a FLOW input (the literal),
   the mixed capture that is unsound if a FLOW input is IGNORED (`cex_mixed_raw`), and the seed
   layer rows K1, K3, K5.

All results are constructive (`propext`, `Quot.sound` only; see the `#print axioms` lines).
-/

namespace ApSpec.BackCondImpl

open ApSpec ApSpec.AnyTaint ApSpec.AnyTaintEx ApSpec.BackND

/-! ## 1. The seed layer in the code -/

/-- `seedFact`: the requirement of a literal is in the DEMAND layer unless the literal is unary
    and has the `$` tail. -/
def seedDemand (unary : Bool) (p : PFact) : Bool := !(unary && BackCond.exactB p)

/-- The code reading of "unary": an alternative whose literal SET is `{p}`. The rule model reads
    `[p] ∈ c`; the two agree when no alternative repeats a literal (`unaryC_iff_mem`). -/
def UnaryC (c : BackCond.Cond) (p : PFact) : Prop := ∃ x ∈ c, x ≠ [] ∧ ∀ y ∈ x, y = p

/-- A legacy sink (no compiled predicate): the literal is unary iff an alternative of its rule at
    the statement has the literal alone (`SinkRule.patterns` is never empty). -/
def legacyUnary (c : BackCond.Cond) (p : PFact) : Bool :=
  c.any (fun alt => !alt.isEmpty && alt.all (fun y => decide (y = p)))

theorem legacyUnary_iff {c : BackCond.Cond} {p : PFact} : legacyUnary c p = true ↔ UnaryC c p := by
  unfold legacyUnary UnaryC
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨x, hx, ?_, fun y hy => of_decide_eq_true (h.2 y hy)⟩
    intro hn
    rw [hn] at h
    cases h.1
  · rintro ⟨x, hx, hne, hall⟩
    refine ⟨x, hx, ?_⟩
    rw [Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, fun y hy => decide_eq_true (hall y hy)⟩
    cases x with
    | nil => exact (hne rfl).elim
    | cons _ _ => rfl

#print axioms legacyUnary_iff

theorem eq_single_of_nodup {x : List PFact} {p : PFact} (hnd : x.Nodup) (hne : x ≠ [])
    (hall : ∀ y ∈ x, y = p) : x = [p] := by
  cases x with
  | nil => exact (hne rfl).elim
  | cons a t =>
    have ha : a = p := hall a (List.mem_cons_self ..)
    subst ha
    cases t with
    | nil => rfl
    | cons b u =>
      have hb : b = a := hall b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      subst hb
      exact ((List.nodup_cons.mp hnd).1 (List.mem_cons_self ..)).elim

/-- With duplicate-free alternatives the code reading is the rule reading. -/
theorem unaryC_iff_mem {c : BackCond.Cond} {p : PFact} (hnd : ∀ x ∈ c, x.Nodup) :
    UnaryC c p ↔ [p] ∈ c := by
  constructor
  · rintro ⟨x, hx, hne, hall⟩
    rw [← eq_single_of_nodup (hnd x hx) hne hall]
    exact hx
  · intro h
    exact ⟨[p], h, List.cons_ne_nil _ _, fun y hy => List.mem_singleton.mp hy⟩

#print axioms unaryC_iff_mem

/-- A code-unary literal is MUST: each location of the literal alone fires the condition. So a
    NORMAL seed is MUST also for an alternative that repeats its literal. -/
theorem unaryC_must {c : BackCond.Cond} {p : PFact} {l : Loc} (h : UnaryC c p) (hl : p.covers l) :
    BackCond.Suff c l := by
  obtain ⟨x, hx, _, hall⟩ := h
  intro st hst
  unfold BackCond.fires
  rw [List.any_eq_true]
  refine ⟨x, hx, List.all_eq_true.mpr fun y hy => ?_⟩
  rw [hall y hy]
  exact BackCond.holds_iff.mpr ⟨l, hst, hl⟩

#print axioms unaryC_must

theorem seedDemand_false {u : Bool} {p : PFact} :
    seedDemand u p = false ↔ u = true ∧ BackCond.exactB p = true := by
  unfold seedDemand
  cases u <;> cases BackCond.exactB p <;> decide

/-- THE CODE LAYER IS THE RULE LAYER (K1, K3, K5): with duplicate-free alternatives, the code seeds
    a literal in the NORMAL layer iff the rule model has the NORMAL requirement `⟨p, false⟩`. -/
theorem code_normal_iff {c : BackCond.Cond} {p : PFact} (hnd : ∀ x ∈ c, x.Nodup) :
    seedDemand (legacyUnary c p) p = false ↔ (⟨p, false⟩ : AFact) ∈ BackCond.reqs c := by
  rw [BackCond.reqs_normal_iff, seedDemand_false, legacyUnary_iff, unaryC_iff_mem hnd]

#print axioms code_normal_iff

/-- A NORMAL code seed is MUST, for every condition. -/
theorem code_normal_must {c : BackCond.Cond} {p : PFact} {l : Loc}
    (h : seedDemand (legacyUnary c p) p = false) (hl : p.covers l) : BackCond.Suff c l :=
  unaryC_must (legacyUnary_iff.mp (seedDemand_false.mp h).1) hl

#print axioms code_normal_must

/-! ### 1b. The unary flag of a compiled predicate

`RulePredicate` (`interp/RulePredicate.kt:166-201`) computes `singletons` on the NNF DAG: a LEAF
gives `{leaf}`, an OR the union, an AND the intersection; `isUnary(leaf)` iff `leaf ∈
singletons(root)`. The builder folds `TRUE` and `FALSE` away (`junction`, `:119-130`), so the
model has no constants. The concept is the DNF reading `UnaryC`. -/

/-- A positive condition without constants. A shared DAG node is the same subformula. -/
inductive Form
  | leaf (p : PFact)
  | and (a b : Form)
  | or (a b : Form)

/-- The DNF: a list of alternatives. -/
def Form.dnf : Form → BackCond.Cond
  | .leaf p  => [[p]]
  | .or a b  => a.dnf ++ b.dnf
  | .and a b => a.dnf.flatMap (fun x => b.dnf.map (fun y => x ++ y))

/-- The code: `singletons`. -/
def Form.single : Form → PFact → Bool
  | .leaf q,  p => decide (q = p)
  | .or a b,  p => a.single p || b.single p
  | .and a b, p => a.single p && b.single p

theorem Form.dnf_ne_nil : ∀ (φ : Form) (x : List PFact), x ∈ φ.dnf → x ≠ []
  | .leaf p, x, hx => by
    rw [Form.dnf, List.mem_singleton] at hx
    subst hx
    exact List.cons_ne_nil _ _
  | .or a b, x, hx => by
    rw [Form.dnf, List.mem_append] at hx
    rcases hx with h | h
    · exact a.dnf_ne_nil x h
    · exact b.dnf_ne_nil x h
  | .and a _, x, hx => by
    rw [Form.dnf, List.mem_flatMap] at hx
    obtain ⟨y, hy, hz⟩ := hx
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hz
    intro h
    exact a.dnf_ne_nil y hy (List.append_eq_nil_iff.mp h).1

/-- THE PREDICATE FLAG IS THE DNF READING: `isUnary` holds iff an alternative of the DNF has the
    literal set `{p}`. -/
theorem Form.single_iff : ∀ (φ : Form) (p : PFact), φ.single p = true ↔ UnaryC φ.dnf p
  | .leaf q, p => by
    unfold Form.single Form.dnf UnaryC
    constructor
    · intro h
      have hq : q = p := of_decide_eq_true h
      exact ⟨[q], List.mem_singleton_self _, List.cons_ne_nil _ _,
        fun y hy => (List.mem_singleton.mp hy).trans hq⟩
    · rintro ⟨x, hx, _, hall⟩
      rw [List.mem_singleton] at hx
      subst hx
      exact decide_eq_true (hall q (List.mem_singleton_self _))
  | .or a b, p => by
    unfold Form.single Form.dnf
    rw [Bool.or_eq_true, a.single_iff p, b.single_iff p]
    unfold UnaryC
    constructor
    · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
      · exact ⟨x, List.mem_append_left _ hx, h⟩
      · exact ⟨x, List.mem_append_right _ hx, h⟩
    · rintro ⟨x, hx, h⟩
      rcases List.mem_append.mp hx with hx' | hx'
      · exact Or.inl ⟨x, hx', h⟩
      · exact Or.inr ⟨x, hx', h⟩
  | .and a b, p => by
    unfold Form.single Form.dnf
    rw [Bool.and_eq_true, a.single_iff p, b.single_iff p]
    unfold UnaryC
    constructor
    · rintro ⟨⟨x, hx, hxne, hxa⟩, ⟨z, hz, _, hza⟩⟩
      refine ⟨x ++ z, List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨z, hz, rfl⟩⟩, ?_, ?_⟩
      · intro h
        exact hxne (List.append_eq_nil_iff.mp h).1
      · intro y hy
        rcases List.mem_append.mp hy with h | h
        · exact hxa y h
        · exact hza y h
    · rintro ⟨w, hw, _, hall⟩
      obtain ⟨x, hx, hm⟩ := List.mem_flatMap.mp hw
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hm
      exact ⟨⟨x, hx, a.dnf_ne_nil x hx, fun y hy => hall y (List.mem_append_left _ hy)⟩,
        ⟨z, hz, b.dnf_ne_nil z hz, fun y hy => hall y (List.mem_append_right _ hy)⟩⟩

#print axioms Form.single_iff

/-- The predicate flag and the legacy computation agree on the DNF of the condition. -/
theorem Form.single_eq_legacy (φ : Form) (p : PFact) : φ.single p = legacyUnary φ.dnf p := by
  cases h : φ.single p with
  | true => exact (legacyUnary_iff.mpr ((φ.single_iff p).mp h)).symm
  | false =>
    cases h' : legacyUnary φ.dnf p with
    | false => rfl
    | true =>
      have := (φ.single_iff p).mpr (legacyUnary_iff.mp h')
      rw [h] at this
      cases this

#print axioms Form.single_eq_legacy

/-! ## 2. The normal form of a captured input -/

/-- The field tail `*/e` is read as `[any]` (its exclusion goes to `nfEx`). -/
def nfKind : Kind → Kind
  | .star _ => .any
  | k       => k

/-- The exclusion of the normal form: `*/e` adds `e`. -/
def nfEx : Kind → Excl → Excl
  | .star e, ex => ex.union e
  | _,       ex => ex

/-- The input `a` in normal form for the literal mark `T`. -/
def nfFact (a : PFact) (T : Mark) : PFact := ⟨a.base, a.path, nfKind a.kind, .conc T⟩

/-- The stored form of one input `a` (exclusion `aex`) of the literal `d` with the mark `T`: a
    concrete mark must be `T` (the check matched it); an abstract mark (a FLOW input) that admits `T`
    gives the literal itself. -/
def nfOne (d : PFact) (T : Mark) (a : PFact) (aex : Excl) : Option (PFact × Excl) :=
  match a.mark with
  | .conc t    => if Nat.beq t T then some (nfFact a T, nfEx a.kind aex) else none
  | .star      => some (d, Excl.empty)
  | .starEx x  => if BackCond.markAdmB (.starEx x) T then some (d, Excl.empty) else none

/-- The code capture of one input `(j, a, aex)`. -/
def nfIn (lits : List PFact) (x : Nat × PFact × Excl) : Option (Nat × PFact × Excl) :=
  match lits[x.1]? with
  | some d =>
    match d.mark with
    | .conc T => (nfOne d T x.2.1 x.2.2).map (fun q => (x.1, q.1, q.2))
    | _ => none
  | none => none

/-- The literals of a sink: the tail `$` or `[any]` and a concrete mark (`SinkRule` init,
    RuleStatement.kt:30-32). -/
def LitsWF (lits : List PFact) : Prop :=
  ∀ d, d ∈ lits → (d.kind = .exact ∨ d.kind = .any) ∧ ∃ T, d.mark = .conc T

/-- The capture in normal form. -/
def ncap (lits : List PFact) (cap : Cap) : Cap := cap.filterMap (nfIn lits)

theorem nf_tail (k : Kind) (ex : Excl) (σ : List Acc) :
    (tailI k σ ∧ ex.admits σ = true) ↔ (tailI (nfKind k) σ ∧ (nfEx k ex).admits σ = true) := by
  cases k with
  | star e =>
    show (e.admits σ = true ∧ ex.admits σ = true) ↔ (True ∧ (ex.union e).admits σ = true)
    rw [CoreAux.Excl.admits_union, Bool.and_eq_true]
    exact ⟨fun h => ⟨trivial, h.2, h.1⟩, fun h => ⟨h.2.2, h.2.1⟩⟩
  | any => exact Iff.rfl
  | exact => exact Iff.rfl

/-- THE NORMAL FORM IS EXACT on the literal mark: an input whose mark admits `T` covers a location
    with the mark `T` iff its normal form covers it. -/
theorem nf_cov {a : PFact} {aex : Excl} {T : Mark} {l : Loc} (hl : l.mark = T)
    (hT : a.mark.admits T) :
    coversX a aex l ↔ coversX (nfFact a T) (nfEx a.kind aex) l := by
  constructor
  · rintro ⟨hb, ⟨σ, hp, ht, he⟩, _⟩
    obtain ⟨ht', he'⟩ := (nf_tail a.kind aex σ).mp ⟨ht, he⟩
    exact ⟨hb, ⟨σ, hp, ht', he'⟩, hl⟩
  · rintro ⟨hb, ⟨σ, hp, ht, he⟩, _⟩
    obtain ⟨ht', he'⟩ := (nf_tail a.kind aex σ).mpr ⟨ht, he⟩
    exact ⟨hb, ⟨σ, hp, ht', he'⟩, by rw [hl]; exact hT⟩

#print axioms nf_cov

/-- The stored form covers each location with the literal mark that the input covers. -/
theorem nfOne_cov {d a : PFact} {aex : Excl} {T : Mark} {l : Loc} (hl : l.mark = T)
    (hdl : d.covers l) (hal : coversX a aex l) :
    ∃ q qex, nfOne d T a aex = some (q, qex) ∧ coversX q qex l := by
  have ham := hal.2.2
  unfold nfOne
  cases hm : a.mark with
  | conc t =>
    rw [hm] at ham
    have htT : t = T := ham.symm.trans hl
    subst htT
    refine ⟨nfFact a t, nfEx a.kind aex, ?_, ?_⟩
    · simp only [Nat.beq_refl]
      rfl
    · exact (nf_cov hl (by rw [hm]; rfl)).mp hal
  | star =>
    exact ⟨d, Excl.empty, rfl, covers_coversX hdl⟩
  | starEx x =>
    rw [hm, hl] at ham
    refine ⟨d, Excl.empty, ?_, covers_coversX hdl⟩
    show (if BackCond.markAdmB (.starEx x) T then some (d, Excl.empty) else none) = some (d, Excl.empty)
    rw [BackCond.markAdmB_iff.mpr ham]
    rfl

#print axioms nfOne_cov

/-- The stored form has the literal mark, and the tail `$`/`[any]` when the literal has it; it is
    the input in normal form (concrete mark) or the literal (abstract mark). -/
theorem nfOne_shape {d a q : PFact} {aex qex : Excl} {T : Mark} (hdm : d.mark = .conc T)
    (h : nfOne d T a aex = some (q, qex)) :
    q.mark = .conc T ∧ ((d.kind = .exact ∨ d.kind = .any) → (q.kind = .exact ∨ q.kind = .any)) ∧
      ((∃ t, a.mark = .conc t) → q = nfFact a T) ∧ ((∀ t, a.mark ≠ .conc t) → q = d) := by
  unfold nfOne at h
  cases hm : a.mark with
  | conc t =>
    rw [hm] at h
    dsimp only at h
    cases hb : Nat.beq t T with
    | false =>
      rw [if_neg (by rw [hb]; decide)] at h
      cases h
    | true =>
      rw [if_pos hb] at h
      cases h
      refine ⟨rfl, fun _ => ?_, fun _ => rfl, fun hn => (hn t rfl).elim⟩
      show nfKind a.kind = .exact ∨ nfKind a.kind = .any
      cases a.kind with
      | star _ => exact Or.inr rfl
      | any => exact Or.inr rfl
      | exact => exact Or.inl rfl
  | star =>
    rw [hm] at h
    dsimp only at h
    cases h
    exact ⟨hdm, id, (fun h' => by obtain ⟨t, ht⟩ := h'; cases ht), fun _ => rfl⟩
  | starEx x =>
    rw [hm] at h
    dsimp only at h
    cases hb : BackCond.markAdmB (.starEx x) T with
    | false =>
      rw [if_neg (by rw [hb]; decide)] at h
      cases h
    | true =>
      rw [if_pos hb] at h
      cases h
      exact ⟨hdm, id, (fun h' => by obtain ⟨t, ht⟩ := h'; cases ht), fun _ => rfl⟩

#print axioms nfOne_shape

theorem nfIn_some {lits : List PFact} {x y : Nat × PFact × Excl} :
    nfIn lits x = some y ↔ ∃ d T q qex, lits[x.1]? = some d ∧ d.mark = .conc T ∧
      nfOne d T x.2.1 x.2.2 = some (q, qex) ∧ y = (x.1, q, qex) := by
  unfold nfIn
  constructor
  · intro h
    cases hd : lits[x.1]? with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      dsimp only at h
      cases hm : d.mark with
      | star => rw [hm] at h; cases h
      | starEx _ => rw [hm] at h; cases h
      | conc T =>
        rw [hm] at h
        dsimp only at h
        cases ho : nfOne d T x.2.1 x.2.2 with
        | none => rw [ho] at h; cases h
        | some q =>
          rw [ho] at h
          cases h
          exact ⟨d, T, q.1, q.2, rfl, hm, ho, rfl⟩
  · rintro ⟨d, T, q, qex, hd, hm, ho, rfl⟩
    rw [hd]
    dsimp only
    rw [hm]
    dsimp only
    rw [ho]
    rfl

#print axioms nfIn_some

theorem mem_ncap {lits : List PFact} {cap : Cap} {j : Nat} {q : PFact} {qex : Excl} :
    (j, q, qex) ∈ ncap lits cap ↔ ∃ a aex d T, (j, a, aex) ∈ cap ∧ lits[j]? = some d ∧
      d.mark = .conc T ∧ nfOne d T a aex = some (q, qex) := by
  unfold ncap
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨j', a, aex⟩, hm, hx⟩
    obtain ⟨d, T, q', qex', hd, hdm, ho, hy⟩ := nfIn_some.mp hx
    cases hy
    exact ⟨a, aex, d, T, hm, hd, hdm, ho⟩
  · rintro ⟨a, aex, d, T, hm, hd, hdm, ho⟩
    exact ⟨(j, a, aex), hm, nfIn_some.mpr ⟨d, T, q, qex, hd, hdm, ho, rfl⟩⟩

#print axioms mem_ncap

/-- With legal literals the stored form is a legal capture: a concrete mark and the tail `$` or
    `[any]`. -/
theorem ncap_wf {lits : List PFact} (hl : LitsWF lits) (cap : Cap) : CapWF (ncap lits cap) := by
  intro e he
  obtain ⟨j, q, qex⟩ := e
  obtain ⟨_, _, d, T, _, hd, hdm, ho⟩ := mem_ncap.mp he
  obtain ⟨hqm, hqk, _, _⟩ := nfOne_shape hdm ho
  exact ⟨⟨T, hqm⟩, hqk (hl d (List.mem_of_getElem? hd)).1⟩

#print axioms ncap_wf

/-! ## 3. One tree in arrival order -/

/-- The code tree: the leaves inserted one at a time, in arrival order. -/
def mergeL (ts : List Leaf) : List Leaf := ts.foldl (fun L t => insertLeaf t L) []

theorem foldl_insert_cov {ts L : List Leaf} {j : Nat} {l : Loc} :
    (∃ s ∈ ts.foldl (fun L t => insertLeaf t L) L, LeafCov j l s) ↔
      (∃ s ∈ L, LeafCov j l s) ∨ ∃ s ∈ ts, LeafCov j l s := by
  induction ts generalizing L with
  | nil =>
    constructor
    · exact Or.inl
    · rintro (h | ⟨s, hs, _⟩)
      · exact h
      · cases hs
  | cons t ts ih =>
    rw [List.foldl_cons, ih, insertLeaf_cov]
    constructor
    · rintro ((h | h) | ⟨s, hs, hc⟩)
      · exact Or.inr ⟨t, List.mem_cons.mpr (Or.inl rfl), h⟩
      · exact Or.inl h
      · exact Or.inr ⟨s, List.mem_cons.mpr (Or.inr hs), hc⟩
    · rintro (h | ⟨s, hs, hc⟩)
      · exact Or.inl (Or.inr h)
      · rcases List.mem_cons.mp hs with rfl | hs'
        · exact Or.inl (Or.inl hc)
        · exact Or.inr ⟨s, hs', hc⟩

/-- THE CODE TREE IS EXACT: it serves exactly the locations of the stored leaves. -/
theorem mergeL_cov {ts : List Leaf} {j : Nat} {l : Loc} :
    (∃ s ∈ mergeL ts, LeafCov j l s) ↔ ∃ s ∈ ts, LeafCov j l s := by
  unfold mergeL
  rw [foldl_insert_cov]
  constructor
  · rintro (⟨s, hs, _⟩ | h)
    · cases hs
    · exact h
  · exact Or.inr

#print axioms mergeL_cov

/-- The arrival order does not change the served locations: the code tree and the rule tree serve
    the same locations. -/
theorem mergeL_mergeLeaves_cov {ts : List Leaf} {j : Nat} {l : Loc} :
    (∃ s ∈ mergeL ts, LeafCov j l s) ↔ ∃ s ∈ mergeLeaves ts, LeafCov j l s := by
  rw [mergeL_cov, mergeLeaves_cov]

#print axioms mergeL_mergeLeaves_cov

theorem foldl_insert_sub {ts L : List Leaf} {s : Leaf}
    (h : s ∈ ts.foldl (fun L t => insertLeaf t L) L) : s ∈ L ∨ s ∈ ts := by
  induction ts generalizing L with
  | nil => exact Or.inl h
  | cons t ts ih =>
    rw [List.foldl_cons] at h
    rcases ih h with h' | h'
    · rcases List.mem_cons.mp (insertLeaf_sub h') with rfl | h''
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · exact Or.inl h''
    · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

/-- Each leaf of the code tree is a stored leaf. -/
theorem mergeL_sub {ts : List Leaf} {s : Leaf} (h : s ∈ mergeL ts) : s ∈ ts := by
  rcases foldl_insert_sub h with h' | h'
  · cases h'
  · exact h'

#print axioms mergeL_sub

theorem foldl_insert_length (ts L : List Leaf) :
    (ts.foldl (fun L t => insertLeaf t L) L).length ≤ L.length + ts.length := by
  induction ts generalizing L with
  | nil => exact Nat.le_refl _
  | cons t ts ih =>
    rw [List.foldl_cons, List.length_cons]
    refine Nat.le_trans (ih _) ?_
    have := insertLeaf_length t L
    omega

/-- The code tree has at most one leaf per stored leaf. -/
theorem mergeL_length (ts : List Leaf) : (mergeL ts).length ≤ ts.length := by
  have := foldl_insert_length ts []
  unfold mergeL
  simpa using this

#print axioms mergeL_length

/-! ## 4. The code seeds -/

/-- The leaves that the code stores: MEET FIRST with the input in normal form, LEAVES ONLY. -/
def codeLeaves (lits : List PFact) (cap : Cap) : List Leaf := capMeets lits (ncap lits cap)

/-- The seeds of the next backward run: the code tree of each literal, the literal itself if its
    tree is empty. -/
def codeSeeds (lits : List PFact) (cap : Cap) : List Leaf :=
  lits.zipIdx.filterMap (fun x => if hasLeaf (codeLeaves lits cap) x.2 then none else some (x.2, x.1)) ++
    mergeL (codeLeaves lits cap)

/-- The forward capture that the code needs: each real route location of literal `j` is a location
    of the literal, and, unless the code tree of `j` is empty (the fallback), a captured input of
    `j` covers it. -/
def CodeCaptured (lits : List PFact) (cap : Cap) (Real : Nat → Loc → Prop) : Prop :=
  ∀ j l, Real j l → ∃ d, lits[j]? = some d ∧ d.covers l ∧
    (hasLeaf (codeLeaves lits cap) j = true → ∃ a aex, (j, a, aex) ∈ cap ∧ coversX a aex l)

/-- The task form (`BackND.ForwardCaptured`: the inputs of all completed combinations,
    `forwardCaptured_of_combos`) gives the code form. -/
theorem codeCaptured_of_forward {lits : List PFact} {cap : Cap} {Real : Nat → Loc → Prop}
    (h : ForwardCaptured lits cap Real) : CodeCaptured lits cap Real := by
  intro j l hr
  obtain ⟨d, hd, hdl, a, aex, hm, hal⟩ := h j l hr
  exact ⟨d, hd, hdl, fun _ => ⟨a, aex, hm, hal⟩⟩

#print axioms codeCaptured_of_forward

/-- More captured inputs keep the task form (for example, one tree for the same literal pattern
    of several legacy alternatives). -/
theorem forwardCaptured_mono {lits : List PFact} {cap cap' : Cap} {Real : Nat → Loc → Prop}
    (hsub : ∀ e, e ∈ cap → e ∈ cap') (h : ForwardCaptured lits cap Real) :
    ForwardCaptured lits cap' Real := by
  intro j l hr
  obtain ⟨d, hd, hdl, a, aex, hm, hal⟩ := h j l hr
  exact ⟨d, hd, hdl, a, aex, hsub _ hm, hal⟩

#print axioms forwardCaptured_mono

theorem hasLeaf_true {ts : List Leaf} {j : Nat} : hasLeaf ts j = true ↔ ∃ p, (j, p) ∈ ts := by
  unfold hasLeaf
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨j', p⟩, hm, hj⟩
    have : j' = j := beq_iff_eq.mp hj
    subst this
    exact ⟨p, hm⟩
  · rintro ⟨p, hm⟩
    exact ⟨(j, p), hm, beq_iff_eq.mpr rfl⟩

theorem mem_codeLeaves {lits : List PFact} {cap : Cap} {j : Nat} {p : PFact} :
    (j, p) ∈ codeLeaves lits cap ↔ ∃ q qex d pex, (j, q, qex) ∈ ncap lits cap ∧
      lits[j]? = some d ∧ meetLit d q qex = some (p, pex) := by
  unfold codeLeaves capMeets
  rw [List.mem_map]
  constructor
  · rintro ⟨s, hs, hsp⟩
    obtain ⟨j', q, qex, d, p', pex, hm, hd, he, rfl⟩ := mem_meets.mp hs
    cases hsp
    exact ⟨q, qex, d, pex, hm, hd, he⟩
  · rintro ⟨q, qex, d, pex, hm, hd, he⟩
    exact ⟨(j, p, pex), mem_meets.mpr ⟨j, q, qex, d, p, pex, hm, hd, he, rfl⟩, rfl⟩

theorem fallback_mem {lits : List PFact} {cap : Cap} {j : Nat} {d : PFact}
    (hd : lits[j]? = some d) (hl : hasLeaf (codeLeaves lits cap) j = false) :
    (j, d) ∈ codeSeeds lits cap := by
  unfold codeSeeds
  refine List.mem_append.mpr (Or.inl (List.mem_filterMap.mpr
    ⟨(d, j), List.mem_zipIdx_iff_getElem?.mpr hd, ?_⟩))
  simp only [hl]
  rfl

theorem mem_codeSeeds {lits : List PFact} {cap : Cap} {j : Nat} {p : PFact}
    (h : (j, p) ∈ codeSeeds lits cap) :
    lits[j]? = some p ∨ (j, p) ∈ mergeL (codeLeaves lits cap) := by
  unfold codeSeeds at h
  rcases List.mem_append.mp h with h1 | h2
  · obtain ⟨⟨d, j'⟩, hm, hf⟩ := List.mem_filterMap.mp h1
    rw [List.mem_zipIdx_iff_getElem?] at hm
    dsimp only at hf
    cases hc : hasLeaf (codeLeaves lits cap) j' with
    | true => rw [hc] at hf; cases hf
    | false =>
      rw [hc] at hf
      cases hf
      exact Or.inl hm
  · exact Or.inr h2

/-- THE CODE SEEDS ARE SOUND: each real route location of literal `j` is served by a seed of `j`
    (a leaf of the code tree, or the literal when the tree is empty). -/
theorem codeSeeds_sound {lits : List PFact} {cap : Cap} {Real : Nat → Loc → Prop}
    (h : CodeCaptured lits cap Real) {j : Nat} {l : Loc} (hr : Real j l) :
    ∃ s ∈ codeSeeds lits cap, LeafCov j l s := by
  obtain ⟨d, hd, hdl, hcap⟩ := h j l hr
  cases hl : hasLeaf (codeLeaves lits cap) j with
  | false => exact ⟨(j, d), fallback_mem hd hl, rfl, hdl⟩
  | true =>
    obtain ⟨a, aex, ha, hal⟩ := hcap hl
    -- the literal has a concrete mark: a leaf of `j` came through `nfIn`
    obtain ⟨p0, hp0⟩ := hasLeaf_true.mp hl
    obtain ⟨q0, qex0, d0, _, hq0, hd0, _⟩ := mem_codeLeaves.mp hp0
    obtain ⟨_, _, d1, T, _, hd1, hdm, _⟩ := mem_ncap.mp hq0
    rw [hd] at hd1
    cases hd1
    have hlT : l.mark = T := by
      have h' := hdl.2.2
      rw [hdm] at h'
      exact h'
    obtain ⟨q, qex, ho, hqc⟩ := nfOne_cov hlT hdl hal
    have hn : (j, q, qex) ∈ ncap lits cap := mem_ncap.mpr ⟨a, aex, d, T, ha, hd, hdm, ho⟩
    obtain ⟨hqm, _, _, _⟩ := nfOne_shape hdm ho
    obtain ⟨p, pex, he, hpc, _⟩ := AnyTaintExCov.emitX_contract d q qex l T hqm hdl hqc
    have hleaf : (j, p) ∈ codeLeaves lits cap := mem_codeLeaves.mpr ⟨_, _, d, pex, hn, hd, he⟩
    obtain ⟨s, hs, hsc⟩ := mergeL_cov.mpr ⟨(j, p), hleaf, rfl, coversX_covers hpc⟩
    exact ⟨s, List.mem_append.mpr (Or.inr hs), hsc⟩

#print axioms codeSeeds_sound

/-- Each leaf of the code tree is the meet of its literal with the stored form of a captured input. -/
theorem codeTree_meet {lits : List PFact} {cap : Cap} {j : Nat} {p : PFact}
    (hm : (j, p) ∈ mergeL (codeLeaves lits cap)) :
    ∃ a aex d T q qex pex, (j, a, aex) ∈ cap ∧ lits[j]? = some d ∧ d.mark = .conc T ∧
      nfOne d T a aex = some (q, qex) ∧ meetLit d q qex = some (p, pex) := by
  obtain ⟨q, qex, d, pex, hq, hd, he⟩ := mem_codeLeaves.mp (mergeL_sub hm)
  obtain ⟨a, aex, d', T, ha, hd', hdm, ho⟩ := mem_ncap.mp hq
  rw [hd] at hd'
  cases hd'
  exact ⟨a, aex, d, T, q, qex, pex, ha, hd, hdm, ho, he⟩

/-- EACH CODE SEED LIES INSIDE ITS LITERAL (never wider than the CURRENT seed). -/
theorem codeSeeds_inside {lits : List PFact} {cap : Cap} {j : Nat} {p : PFact}
    (h : (j, p) ∈ codeSeeds lits cap) :
    ∃ d, lits[j]? = some d ∧ ∀ l, p.covers l → d.covers l := by
  rcases mem_codeSeeds h with hd | hm
  · exact ⟨p, hd, fun _ hl => hl⟩
  · obtain ⟨a, aex, d, T, q, qex, pex, _, hd, hdm, ho, he⟩ := codeTree_meet hm
    obtain ⟨hqm, _, _, _⟩ := nfOne_shape hdm ho
    exact ⟨d, hd, fun l hl => (emitM_inside_conc (HandoffX.emitX_emitM he) hqm hl).1⟩

#print axioms codeSeeds_inside

/-- THE CODE SEEDS ARE LEGAL backward seeds: the tail `$` or `[any]`, a concrete mark. -/
theorem codeSeeds_legal {lits : List PFact} {cap : Cap} (hlw : LitsWF lits) {j : Nat} {d p : PFact}
    (hd : lits[j]? = some d) (h : (j, p) ∈ codeSeeds lits cap) :
    (p.kind = .exact ∨ p.kind = .any) ∧ ∃ T, p.mark = .conc T := by
  obtain ⟨hdk, hdm⟩ := hlw d (List.mem_of_getElem? hd)
  rcases mem_codeSeeds h with hp | hm
  · rw [hd] at hp
    cases hp
    exact ⟨hdk, hdm⟩
  · obtain ⟨q, qex, d', pex, hq, hd', he⟩ := mem_codeLeaves.mp (mergeL_sub hm)
    have hr : (j, p, pex) ∈ refine lits (ncap lits cap) :=
      List.mem_append.mpr (Or.inr (mem_meets.mpr ⟨j, q, qex, d', p, pex, hq, hd', he, rfl⟩))
    exact refine_legal (ncap_wf hlw cap) hd hdk hdm hr

#print axioms codeSeeds_legal

/-- G1 AND G2 FOR THE CODE TREE. Each leaf lies inside its literal `d` and its path extends the
    literal path. If it comes from an input `a` with a concrete mark (every production input,
    proposal §3 F3, F4), it also lies inside `a` in normal form (the literal mark, the exclusions
    forgotten) and its path extends the path of `a`. -/
theorem codeSeeds_deepens {lits : List PFact} {cap : Cap} {j : Nat} {p : PFact}
    (hm : (j, p) ∈ mergeL (codeLeaves lits cap)) :
    ∃ d a aex T, lits[j]? = some d ∧ d.mark = .conc T ∧ (j, a, aex) ∈ cap ∧
      d.path <+: p.path ∧ (∀ l, p.covers l → d.covers l) ∧
      ((∃ t, a.mark = .conc t) → a.path <+: p.path ∧ ∀ l, p.covers l → (nfFact a T).covers l) := by
  obtain ⟨a, aex, d, T, q, qex, pex, ha, hd, hdm, ho, he⟩ := codeTree_meet hm
  obtain ⟨hqm, _, hconc, _⟩ := nfOne_shape hdm ho
  obtain ⟨h1, h2⟩ := meet_deepens he
  refine ⟨d, a, aex, T, hd, hdm, ha, h2,
    fun l hl => (emitM_inside_conc (HandoffX.emitX_emitM he) hqm hl).1, fun hc => ?_⟩
  have hq := hconc hc
  subst hq
  exact ⟨h1, fun l hl => (emitM_inside_conc (HandoffX.emitX_emitM he) hqm hl).2⟩

#print axioms codeSeeds_deepens

/-! ## 5. The backward contract with the code seeds

`BackND.B_general_refined` is proved for the list of meets with their exclusions. The code seeds
the merged tree (the exclusions dropped, the arrival order, the fallback on an empty tree). The
contract reads the seeds only through `SeedsCover`, so it holds for the code seeds too. -/

section Stretch
open ApSpec.Backward ApSpec.Reverse

/-- The code seeds of one witness at `(M, n)`. -/
def codeSeedsAt (M : MethodId) (n : Node) (lits : List PFact) (cap : Cap) :
    List (MethodId × Node × PFact) :=
  (codeSeeds lits cap).map (fun s => (M, n, s.2))

/-- THE CODE SEEDING: every reported sink pattern `s` at `(M, n)` is the literal `j` of a literal
    list whose capture covers each witness location of the literal (`CodeCaptured`), and the code
    seeds of that literal list are seeded at `(M, n)`. -/
def CodeSeeding (W : MethodId → Node → Loc → Prop) (Rk : Obj → Prop)
    (sinks seeds : List (MethodId × Node × PFact)) : Prop :=
  ∀ M n s b, Rk (.vuln M n s b) → (M, n, s) ∈ sinks →
    ∃ (lits : List PFact) (cap : Cap) (j : Nat), lits[j]? = some s ∧ LitsWF lits ∧
      CodeCaptured lits cap (fun j' l => j' = j ∧ s.covers l ∧ W M n l) ∧
      ∀ x, x ∈ codeSeedsAt M n lits cap → x ∈ seeds

/-- THE CODE SEEDING SATISFIES `SeedsCover`. -/
theorem seedsCover_code {W : MethodId → Node → Loc → Prop} {Rk : Obj → Prop}
    {sinks seeds : List (MethodId × Node × PFact)}
    (h : CodeSeeding W Rk sinks seeds) : SeedsCover W Rk sinks seeds := by
  intro M n s T b l hv hs hT hsc hWl
  obtain ⟨lits, cap, j, hj, hlw, hfc, hsub⟩ := h M n s b hv hs
  obtain ⟨⟨j', p⟩, hm, hj', hpl⟩ := codeSeeds_sound hfc (j := j) (l := l) ⟨rfl, hsc, hWl⟩
  have hjj : j' = j := hj'
  subst hjj
  have hin : (M, n, p) ∈ codeSeedsAt M n lits cap := List.mem_map.mpr ⟨(j', p), hm, rfl⟩
  obtain ⟨hpk, hpm⟩ := codeSeeds_legal hlw hj hm
  exact ⟨p, hsub _ hin, hpl, hpm, hpk⟩

#print axioms seedsCover_code

/-- CONTRACT B IN THE GENERAL CASE WITH THE CODE SEEDS. -/
theorem B_general_code {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    {Rk : Obj → Prop} {seeds : List (MethodId × Node × PFact)}
    (hseeds : CodeSeeding (ReachRD P Rk roots) Rk sinks seeds)
    {counted : Acc → Bool} {L : Nat} {demB : MethodId → DemandEdge → Prop}
    (hdemB : ∀ m d, revSummaryDemand P Rk m d → demB m d)
    {recsB : MethodId → PFact × AFact → Prop} {sinksB : List (MethodId × Node × PFact)} :
    BackwardContractD P roots sinks Rk (demOf (Program.rev P)
      (DB (Program.rev P) counted L demB emitM satI restrictU recsB sinksB roots seeds true)) :=
  B_general_cov hW hT hmr hNZB hZ hX (seedsCover_code hseeds) hdemB

#print axioms B_general_code

/-- THE GENERAL ITERATION THEOREM WITH THE CODE SEEDS. -/
theorem iteration_general_code {P : Program} (hW : P.WF) (hT : BindTargetsStar P)
    (hmr : StmtsMarkRev P) (hNZB : NoZeroBack P) (hZ : ZeroKept P) {roots : List MethodId}
    (hX : ExitReach P roots) {sinks : List (MethodId × Node × PFact)}
    {counted : Acc → Bool} {Ls : Nat → Nat}
    {dem : Nat → MethodId → DemandEdge → Prop} {recs : Nat → MethodId → PFact × AFact → Prop}
    (LB : Nat → Nat) (demB : Nat → MethodId → DemandEdge → Prop)
    (recsB : Nat → MethodId → PFact × AFact → Prop) (seeds : Nat → List (MethodId × Node × PFact))
    (hdemB : ∀ k m d, revSummaryDemand P
      (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k) m d → demB k m d)
    (hseeds : ∀ k, CodeSeeding
      (ReachRD P (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k) roots)
      (RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k) sinks (seeds k))
    (hdem : ∀ k m d, demOf (Program.rev P) (DB (Program.rev P) counted (LB k) (demB k) emitM satI
      restrictU (recsB k) [] roots (seeds k) true) m d → dem k m d)
    {M : MethodId} {n : Node} {l : Loc} {s : PFact} {T : Mark}
    (hRe : Reach P roots M n l) (hs : (M, n, s) ∈ sinks) (hT' : s.mark = .conc T)
    (hsc : s.covers l) :
    ∀ k, ∃ b, RCov.runSeq P counted Ls dem emitM satI restrictU recs sinks roots k
      (.vuln M n s b) :=
  iteration_sound_M_D hW (fun k M' n' l' s' T' hs' hT'' hc' hr' hv' =>
    RCov.reachR_mono (hdem k)
      (B_general_code hW hT hmr hNZB hZ hX (hseeds k) (hdemB k) M' n' l' s' T' hs' hT''
        hc' hr' hv'))
    hRe hs hT' hsc

#print axioms iteration_general_code

end Stretch

/-! ## 6. Vectors -/

namespace Vec
open ApSpec.BackCondEx

/-- The literal `vb.[any](U)`. -/
def litB : PFact := pf vb [] .any U

/-- A FLOW input `vb.f.*(*)` (no production site): the code stores the literal. -/
theorem flow_literal : codeSeeds [litB] [(0, pf vb [f] s0 .star, Excl.empty)] = [(0, litB)] := by
  decide

/-- A MIXED capture: a concrete input `vb.f.$(U)` and a FLOW input `vb.g.*(*)`. -/
def mixed : Cap := [(0, pf vb [f] .exact U, Excl.empty), (0, pf vb [g] s0 .star, Excl.empty)]

/-- The location `vb.g (U)` is a real route location: the literal and the FLOW input cover it. -/
def locG : Loc := ⟨vb, [g], tU⟩

theorem mixed_real : litB.covers locG ∧ coversX (pf vb [g] s0 .star) Excl.empty locG :=
  ⟨⟨rfl, ⟨[g], rfl, trivial⟩, rfl⟩, ⟨rfl, ⟨[], rfl, rfl, rfl⟩, trivial⟩⟩

/-- If the FLOW input is IGNORED (no meet, `BackND.capMeets`), the tree has the concrete leaf only.
    It is not empty, so there is no fallback. -/
theorem mixed_raw : BackND.treeSeeds [litB] (BackND.capMeets [litB] mixed) = [(0, pf vb [f] .exact U)] := by
  decide

/-- COUNTEREXAMPLE: an ignored FLOW input loses the real location `vb.g (U)`. So a FLOW input must
    not be dropped; the code stores the literal for it. -/
theorem cex_mixed_raw : ¬ ∃ s ∈ BackND.treeSeeds [litB] (BackND.capMeets [litB] mixed), LeafCov 0 locG s := by
  rw [mixed_raw]
  rintro ⟨s, hs, _, hc⟩
  rw [List.mem_singleton] at hs
  subst hs
  have : BackCond.covB (pf vb [f] .exact U) locG = false := by decide
  rw [BackCond.covB_iff.mpr hc] at this
  cases this

#print axioms cex_mixed_raw

/-- The code stores the literal for the FLOW input; it subsumes the concrete leaf. -/
theorem mixed_code : codeSeeds [litB] mixed = [(0, litB)] := by decide

theorem mixed_code_covers : ∃ s ∈ codeSeeds [litB] mixed, LeafCov 0 locG s := by
  rw [mixed_code]
  exact ⟨(0, litB), List.mem_cons.mpr (Or.inl rfl), rfl, mixed_real.1⟩

#print axioms mixed_code_covers

/-- A C2 cut start `x.f.*(T)` (a STAR tail with a concrete mark): the leaf `x.f.[any](T)`. -/
theorem star_start : codeSeeds [pf x [] .any T] [(0, pf x [f] s0 T, Excl.empty)] =
    [(0, pf x [f] .any T)] := by decide

/-- The spine exclusion stays: `x.[any-taint]/{f}` does not overlap the literal `x.f.[any](T)`, so
    it gives no leaf; the tree keeps the leaf `x.f.g.$(T)` only. (Dropping `{f}` BEFORE the meet
    would give the leaf `x.f.[any](T)` and lose the precision.) -/
theorem spine_excl : codeSeeds [pf x [f] .any T]
    [(0, pf x [f, g] .exact T, Excl.empty), (0, pf x [] .any T, .set [f])] =
    [(0, pf x [f, g] .exact T)] := by decide

/-- A FLOW input whose mark excludes the literal mark (`*∖{U}`) gives no leaf: the fallback. -/
theorem flow_excluded : codeSeeds [litB] [(0, pf vb [f] s0 (.starEx [tU]), Excl.empty)] =
    [(0, litB)] := by decide

/-- Seed layer rows: K1 (unary `$`: NORMAL), K3 (ND `$`: DEMAND), K5 (unary and ND: NORMAL),
    an `[any]` literal (DEMAND). -/
theorem layer_k1 : seedDemand (legacyUnary [[pf va [] .exact T]] (pf va [] .exact T))
    (pf va [] .exact T) = false := by decide
theorem layer_k3 : seedDemand (legacyUnary [[pf va [] .exact T, litB]] (pf va [] .exact T))
    (pf va [] .exact T) = true := by decide
theorem layer_k5 : seedDemand (legacyUnary [[pf va [] .exact T], [pf va [] .exact T, litB]]
    (pf va [] .exact T)) (pf va [] .exact T) = false := by decide
theorem layer_any : seedDemand (legacyUnary [[litB]] litB) litB = true := by decide
/-- An alternative that repeats its `$` literal: the code keeps NORMAL (CURRENT), the rule model
    `BackCond.reqs` gives DEMAND. The code is right: the literal is MUST (`unaryC_must`). -/
theorem layer_repeat : seedDemand (legacyUnary [[pf va [] .exact T, pf va [] .exact T]] (pf va [] .exact T))
    (pf va [] .exact T) = false ∧
    BackCond.reqs [[pf va [] .exact T, pf va [] .exact T]] =
      [⟨pf va [] .exact T, true⟩, ⟨pf va [] .exact T, true⟩] := by decide
/-- The predicate flag on `(va ∨ vb) ∧ (va ∨ x)`: `va` is unary (DNF alternative `[va, va]`). -/
theorem flag_shared : (Form.and (.or (.leaf (pf va [] .exact T)) (.leaf litB))
    (.or (.leaf (pf va [] .exact T)) (.leaf (pf x [] .any T)))).single (pf va [] .exact T) = true := by
  decide

end Vec

end ApSpec.BackCondImpl
