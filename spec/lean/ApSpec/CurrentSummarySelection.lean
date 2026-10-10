/-
  Current raw summary demand selection, including F76.

  This model checks the complete local selector used by demandPart: cardinality,
  layer, backward zero, generic crossing, and the forward exact-to-must view.
  Selection is computed on the raw leaf and kept beside each publication.
  It does not prove record provenance, summary exactness, or whole-run coverage.
  Native provenance includes the typed kind guards: a must Entry has concrete
  mark and ANY kind, and no backward Entry is must. In a native STAR premise,
  premiseEx and the exclusion in kind must agree. Normal backward conclusions
  have no ANY tail. The three-tail carrier does not prove these construction rules.
-/
import ApSpec.CurrentMustReverse
import ApSpec.HandoffCases

namespace ApSpec.CurrentSummarySelection
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.HandoffCases
open ApSpec.AnyTaintEx ApSpec.CurrentMustReverse

inductive Direction where
  | forward | backward
deriving DecidableEq, Repr

structure Entry where
  fact : PFact
  must : Bool
  ex : Excl
deriving DecidableEq, Repr

structure RawLeaf where
  premises : List Entry
  conclusion : XFact
deriving DecidableEq, Repr

def native (j : Entry) (g : XFact) : NativeRecord :=
  ⟨j.fact, j.must, j.ex, g⟩

def forwardB (j : Entry) (g : XFact) : Bool :=
  omitMustDemand (native j g) || crossB j.fact g.af

/-- The generic reversal is partial in the proposal. Test its mark guard first.
    Native S7 records satisfy that guard; arbitrary malformed leaves need not. -/
def backwardB (j : Entry) (g : XFact) : Bool :=
  !j.must && !g.af.demand && markRevB j.fact g.af.fact &&
    crossB (revRec (j.fact, g.af)).1 (revRec (j.fact, g.af)).2

def reuseB : Direction → Entry → XFact → Bool
  | .forward => forwardB
  | .backward => backwardB

/-- Zero has its canonical native form; this is the zero-premise seed-path rule. -/
def selectedB (dir : Direction) (raw : RawLeaf) : Bool :=
  match raw.premises with
  | [j] =>
    if dir == .backward && j.fact == zeroFact then true
    else !reuseB dir j raw.conclusion
  | _ => true

def Reusable (dir : Direction) (raw : RawLeaf) : Prop :=
  ∃ j, raw.premises = [j] ∧
    (dir = .backward → j.fact ≠ zeroFact) ∧
    match dir with
    | .forward => RawReusable (native j raw.conclusion)
    | .backward => j.must = false ∧ MarkRev j.fact raw.conclusion.af.fact ∧
        CrossB j.fact raw.conclusion.af

theorem forward_iff (j : Entry) (g : XFact) :
    forwardB j g = true ↔ RawReusable (native j g) := by
  simp only [forwardB, Bool.or_eq_true, RawReusable, native]
  rw [← cross_iff]
  exact or_comm

theorem backward_iff (j : Entry) (g : XFact) :
    backwardB j g = true ↔ j.must = false ∧ MarkRev j.fact g.af.fact ∧ CrossB j.fact g.af := by
  simp only [backwardB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, ← markRev_iff,
    ← cross_iff, CrossB]
  exact ⟨fun h => ⟨h.1.1.1, h.1.2, h.1.1.2, h.2⟩,
    fun h => ⟨⟨⟨h.1, h.2.2.1⟩, h.2.1⟩, h.2.2.2⟩⟩

theorem selected_iff (dir : Direction) (raw : RawLeaf) :
    selectedB dir raw = false ↔ Reusable dir raw := by
  obtain ⟨js, g⟩ := raw
  cases js with
  | nil => simp [selectedB, Reusable]
  | cons j js =>
    cases js with
    | cons k ks => simp [selectedB, Reusable]
    | nil =>
      cases dir with
      | forward => simp [selectedB, Reusable, reuseB, forward_iff]
      | backward =>
        by_cases hz : j.fact = zeroFact
        · simp [selectedB, Reusable, hz]
        · simp [selectedB, Reusable, hz, reuseB, backward_iff]

theorem demand_iff (dir : Direction) (raw : RawLeaf) :
    selectedB dir raw = true ↔ ¬ Reusable dir raw := by
  rw [← selected_iff]
  cases selectedB dir raw <;> simp

/-- No data are selected from an existential proposition. The caller obtains
    the concrete normal read view by evaluating normalMustWitness. -/
def selectedMustView (j : Entry) (g : XFact)
    (h : omitMustDemand (native j g) = true) : NormalMustWitness (native j g) :=
  normalMustWitness (native j g) h

theorem must_view_omitted (j : Entry) (g : XFact)
    (h : omitMustDemand (native j g) = true) :
    selectedB .forward ⟨[j], g⟩ = false := by
  simp [selectedB, reuseB, forwardB, h]

theorem multi_selected (dir : Direction) (j k : Entry) (rest : List Entry) (g : XFact) :
    selectedB dir ⟨j :: k :: rest, g⟩ = true := rfl

theorem backward_zero_selected (j : Entry) (g : XFact) (hz : j.fact = zeroFact) :
    selectedB .backward ⟨[j], g⟩ = true := by simp [selectedB, hz]

theorem demand_layer_selected (dir : Direction) (js : List Entry) (g : XFact)
    (hd : g.af.demand = true) : selectedB dir ⟨js, g⟩ = true := by
  cases js with
  | nil => rfl
  | cons j js =>
    cases js with
    | cons k ks => rfl
    | nil => cases dir <;>
        simp [selectedB, reuseB, forwardB, backwardB, omitMustDemand, native, crossB, hd]

/-- The publication carries the complete raw demand bit, not just F76's new bit.
    This is a reference for restricting the already selected demand part. -/
def publicationPlan (dir : Direction) (raw : RawLeaf) (piece : XFact) : Bool × XFact :=
  (selectedB dir raw, piece)

theorem publication_keeps_selection (dir : Direction) (raw : RawLeaf) (piece : XFact) :
    (publicationPlan dir raw piece).1 = selectedB dir raw ∧
    (publicationPlan dir raw piece).2 = piece := ⟨rfl, rfl⟩

theorem publication_independent (dir : Direction) (raw : RawLeaf) (a b : XFact) :
    (publicationPlan dir raw a).1 = (publicationPlan dir raw b).1 := rfl

/-- A concrete conclusion's base, path, mark identity and must exclusion do
    not change crossing. The shortcut can test one representative per tail.
    The premise and its annotation are kept unchanged. -/
theorem concrete_class (dir : Direction) (j : Entry) (k : Kind) (dm : Bool)
    (b₁ b₂ : Base) (p₁ p₂ : List Acc) (t₁ t₂ : Mark) (e₁ e₂ : Excl) :
    reuseB dir j ⟨⟨⟨b₁, p₁, k, .conc t₁⟩, dm⟩, e₁⟩ =
      reuseB dir j ⟨⟨⟨b₂, p₂, k, .conc t₂⟩, dm⟩, e₂⟩ := by
  obtain ⟨⟨jb, jp, jk, jm⟩, must, je⟩ := j
  cases dir <;> cases must <;> cases jk <;> cases jm <;> cases k <;> cases dm <;>
    simp [reuseB, forwardB, backwardB, native, omitMustDemand, crossB,
      markRevB, crossKB, revRec, revEdge_eq, revKinds, pmOf, fmOf]

/-- Normal FLOW selection also needs one class test. Conclusion field E,
    base and path do not affect crossing; its abstract mark exclusion stays. -/
theorem flow_class (dir : Direction) (j : Entry) (m : MarkA)
    (hm : concB m = false) (b₁ b₂ : Base) (p₁ p₂ : List Acc) (e₁ e₂ : Excl) :
    reuseB dir j ⟨⟨⟨b₁, p₁, .star e₁, m⟩, false⟩, Excl.empty⟩ =
      reuseB dir j ⟨⟨⟨b₂, p₂, .star e₂, m⟩, false⟩, Excl.empty⟩ := by
  obtain ⟨⟨jb, jp, jk, jm⟩, must, je⟩ := j
  cases m <;> simp only [concB] at hm
  all_goals cases dir <;> cases must <;> cases jk <;> cases jm <;>
    simp [reuseB, forwardB, backwardB, native, omitMustDemand, crossB,
      markRevB, crossKB, revRec, revEdge_eq, revKinds, pmOf, fmOf]

def representative (g : XFact) : XFact :=
  ⟨⟨⟨0, [], g.af.fact.kind, .conc 0⟩, g.af.demand⟩, Excl.empty⟩

theorem selected_representative (dir : Direction) (js : List Entry) (g : XFact)
    (t : Mark) (hm : g.af.fact.mark = .conc t) :
    selectedB dir ⟨js, g⟩ = selectedB dir ⟨js, representative g⟩ := by
  obtain ⟨⟨⟨b, p, k, m⟩, dm⟩, e⟩ := g
  dsimp at hm
  subst m
  cases js with
  | nil => rfl
  | cons j js =>
    cases js with
    | cons k ks => rfl
    | nil =>
      simp only [selectedB, representative]
      rw [concrete_class dir j k dm b 0 p [] t 0 e Excl.empty]

/-- Per-leaf reference selection and the class shortcut have exactly the
    same list, including order and duplicates. No tree packing is assumed. -/
def selectLeaves (dir : Direction) (js : List Entry) (leaves : List XFact) : List XFact :=
  leaves.filter (fun g => selectedB dir ⟨js, g⟩)

def selectClasses (dir : Direction) (js : List Entry) (leaves : List XFact) : List XFact :=
  leaves.filter (fun g => selectedB dir ⟨js, representative g⟩)

theorem class_selection_equiv (dir : Direction) (js : List Entry) (leaves : List XFact)
    (hc : ∀ g, g ∈ leaves → ∃ t, g.af.fact.mark = .conc t) :
    selectLeaves dir js leaves = selectClasses dir js leaves := by
  apply List.filter_congr
  intro g hg
  obtain ⟨t, ht⟩ := hc g hg
  exact selected_representative dir js g t ht

def taintFlags (dir : Direction) (js : List Entry) (dm : Bool) : Bool × Bool :=
  (selectedB dir ⟨js, ⟨⟨⟨0, [], .exact, .conc 0⟩, dm⟩, Excl.empty⟩⟩,
    selectedB dir ⟨js, ⟨⟨⟨0, [], .any, .conc 0⟩, dm⟩, Excl.empty⟩⟩)

def flagFor (flags : Bool × Bool) : Kind → Bool
  | .exact => flags.1
  | .any => flags.2
  | .star _ => false

/-- A normal TAINT tree has exact/must leaves; a demand TAINT tree has
    exact/may leaves. Compute two gates, then map only when they differ. -/
def selectPacked (dir : Direction) (js : List Entry) (dm : Bool)
    (leaves : List XFact) : List XFact :=
  let flags := taintFlags dir js dm
  if flags.1 && flags.2 then leaves
  else if !flags.1 && !flags.2 then []
  else leaves.filter (fun g => flagFor flags g.af.fact.kind)

private theorem filter_none {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x, x ∈ xs → p x = false) : xs.filter p = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons, h x (List.Mem.head xs)]
    simp only [Bool.false_eq_true, ite_false]
    exact ih (fun y hy => h y (List.Mem.tail x hy))

private theorem filter_all {α : Type} (p : α → Bool) (xs : List α)
    (h : ∀ x, x ∈ xs → p x = true) : xs.filter p = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons, h x (List.Mem.head xs)]
    simp only [ite_true]
    exact congrArg (x :: ·) (ih (fun y hy => h y (List.Mem.tail x hy)))

theorem flag_matches (dir : Direction) (js : List Entry) (dm : Bool) (g : XFact)
    (hd : g.af.demand = dm) (hc : ∃ t, g.af.fact.mark = .conc t)
    (hk : g.af.fact.kind = .exact ∨ g.af.fact.kind = .any) :
    selectedB dir ⟨js, g⟩ = flagFor (taintFlags dir js dm) g.af.fact.kind := by
  obtain ⟨t, ht⟩ := hc
  rw [selected_representative dir js g t ht]
  rcases hk with hk | hk <;>
    simp [flagFor, taintFlags, representative, hk, hd]

theorem packed_selection_equiv (dir : Direction) (js : List Entry) (dm : Bool)
    (leaves : List XFact)
    (shape : ∀ g, g ∈ leaves → g.af.demand = dm ∧
      (∃ t, g.af.fact.mark = .conc t) ∧
      (g.af.fact.kind = .exact ∨ g.af.fact.kind = .any)) :
    selectPacked dir js dm leaves = selectLeaves dir js leaves := by
  have eq : leaves.filter (fun g => flagFor (taintFlags dir js dm) g.af.fact.kind) =
      selectLeaves dir js leaves := by
    apply List.filter_congr
    intro g hg
    obtain ⟨hd, hc, hk⟩ := shape g hg
    exact (flag_matches dir js dm g hd hc hk).symm
  unfold selectPacked
  generalize hf : taintFlags dir js dm = flags at *
  obtain ⟨fe, fa⟩ := flags
  cases fe <;> cases fa <;> simp only [Bool.and_self, Bool.false_and,
    Bool.and_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
  · rw [← eq]
    symm
    apply filter_none
    intro g hg
    obtain ⟨_, _, hk⟩ := shape g hg
    rcases hk with hk | hk <;> simp [flagFor, hk]
  · exact eq
  · exact eq
  · rw [← eq]
    symm
    apply filter_all
    intro g hg
    obtain ⟨_, _, hk⟩ := shape g hg
    rcases hk with hk | hk <;> simp [flagFor, hk]

/-- Local work counts: selector calls and leaf visits. This excludes mark-set
    comparisons, input construction, trie packing and later consumers. -/
structure SelectionWork where
  calls : Nat
  visits : Nat
deriving DecidableEq, BEq, Repr

def countedLeaves (dir : Direction) (js : List Entry) :
    List XFact → List XFact × SelectionWork
  | [] => ([], ⟨0, 0⟩)
  | g :: gs =>
    let next := countedLeaves dir js gs
    let selected := selectedB dir ⟨js, g⟩
    (if selected then g :: next.1 else next.1,
      ⟨next.2.calls + 1, next.2.visits + 1⟩)

theorem countedLeaves_result (dir : Direction) (js : List Entry) (gs : List XFact) :
    (countedLeaves dir js gs).1 = selectLeaves dir js gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [countedLeaves, selectLeaves, List.filter_cons, ih]

theorem countedLeaves_work (dir : Direction) (js : List Entry) (gs : List XFact) :
    (countedLeaves dir js gs).2 = ⟨gs.length, gs.length⟩ := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [countedLeaves, ih]

/-- Two selector calls compute the flags. Equal flags retain or drop the whole
    value; differing flags require a leaf walk. This models the proposal's gate
    shortcut, not allocation or the complexity of the whole analyzer. -/
def countedPacked (dir : Direction) (js : List Entry) (dm : Bool)
    (gs : List XFact) : List XFact × SelectionWork :=
  let flags := taintFlags dir js dm
  if flags.1 && flags.2 then (gs, ⟨2, 0⟩)
  else if !flags.1 && !flags.2 then ([], ⟨2, 0⟩)
  else (gs.filter (fun g => flagFor flags g.af.fact.kind), ⟨2, gs.length⟩)

theorem countedPacked_result (dir : Direction) (js : List Entry) (dm : Bool)
    (gs : List XFact) : (countedPacked dir js dm gs).1 = selectPacked dir js dm gs := by
  simp only [countedPacked, selectPacked]
  split <;> (try split) <;> rfl

theorem countedPacked_uniform (dir : Direction) (js : List Entry) (dm : Bool)
    (gs : List XFact) (h : (taintFlags dir js dm).1 = (taintFlags dir js dm).2) :
    (countedPacked dir js dm gs).2 = ⟨2, 0⟩ := by
  unfold countedPacked
  generalize hf : taintFlags dir js dm = flags at *
  obtain ⟨fe, fa⟩ := flags
  cases fe <;> cases fa <;> simp_all

theorem counted_selection_equiv (dir : Direction) (js : List Entry) (dm : Bool)
    (gs : List XFact)
    (shape : ∀ g, g ∈ gs → g.af.demand = dm ∧
      (∃ t, g.af.fact.mark = .conc t) ∧
      (g.af.fact.kind = .exact ∨ g.af.fact.kind = .any)) :
    (countedPacked dir js dm gs).1 = (countedLeaves dir js gs).1 := by
  rw [countedPacked_result, countedLeaves_result]
  exact packed_selection_equiv dir js dm gs shape

namespace Certificate

def exactEntry : Entry := ⟨⟨3, [], .exact, .conc 9⟩, false, Excl.empty⟩
def mustEntry : Entry := ⟨⟨3, [], .any, .conc 9⟩, true, .set [8]⟩
def outputMust : XFact := ⟨⟨⟨5, [2], .any, .conc 1⟩, false⟩, .set [4]⟩
def outputExact : XFact := ⟨⟨⟨5, [2, 7], .exact, .conc 1⟩, false⟩, Excl.empty⟩
def outputDemand : XFact := ⟨⟨outputMust.af.fact, true⟩, Excl.empty⟩
def zeroEntry : Entry := ⟨zeroFact, false, Excl.empty⟩
def zeroOutput : XFact := ⟨⟨zeroFact, false⟩, Excl.empty⟩

def cases : List Bool := [
  selectedB .forward ⟨[exactEntry], outputMust⟩,
  selectedB .forward ⟨[exactEntry], outputExact⟩,
  selectedB .forward ⟨[mustEntry], outputMust⟩,
  selectedB .forward ⟨[mustEntry], outputExact⟩,
  selectedB .forward ⟨[exactEntry], outputDemand⟩,
  selectedB .forward ⟨[exactEntry, mustEntry], outputExact⟩,
  selectedB .backward ⟨[zeroEntry], zeroOutput⟩,
  selectedB .backward ⟨[exactEntry], outputExact⟩,
  selectedB .backward ⟨[mustEntry], outputExact⟩]

theorem case_values : cases = [false, false, true, true, true, true, true, false, true] := by decide

/-- A must-premise remains selected after it publishes an exact piece. -/
def rawMust : RawLeaf := ⟨[mustEntry], outputMust⟩

theorem published_raw_bit :
    publicationPlan .forward rawMust outputExact = (true, outputExact) ∧
    selectedB .forward ⟨[mustEntry], outputExact⟩ = true := by decide

def restrictedDemand : DemandEdge := ⟨mustEntry.fact, some outputExact.af.fact⟩

theorem actual_restricted_piece :
    ApSpec.HandoffX.restrictIX mustEntry.fact mustEntry.ex outputMust restrictedDemand =
      some outputExact := by decide

def classLeaves : List XFact := [outputMust, outputExact, outputDemand]

theorem class_values :
    selectLeaves .forward [exactEntry] classLeaves = [outputDemand] ∧
    selectClasses .forward [exactEntry] classLeaves = [outputDemand] ∧
    selectLeaves .forward [mustEntry] classLeaves = classLeaves := by decide

def normalLeaves : List XFact := [outputMust, outputExact]

theorem packed_values :
    selectPacked .forward [exactEntry] false normalLeaves = [] ∧
    selectPacked .forward [mustEntry] false normalLeaves = normalLeaves ∧
    selectPacked .backward [exactEntry] false [outputExact] = [] := by decide

/-- Thirty-three sibling must leaves have distinct paths and the same gate. -/
def workload : List XFact := (List.range 33).map fun n =>
  { outputMust with af := { outputMust.af with
    fact := { outputMust.af.fact with path := [n] } } }

def workWitness : SelectionWork × SelectionWork :=
  ((countedLeaves .forward [exactEntry] workload).2,
    (countedPacked .forward [exactEntry] false workload).2)

theorem work_values : workWitness = (⟨33, 33⟩, ⟨2, 0⟩) := by decide

theorem workload_same_result :
    (countedPacked .forward [exactEntry] false workload).1 =
      (countedLeaves .forward [exactEntry] workload).1 := by decide

end Certificate

end ApSpec.CurrentSummarySelection
