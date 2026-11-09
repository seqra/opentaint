/-!
# The summary compression deletes a chain; the star lift keeps it

`MergingTreeSummaryStorage.compressNode` calls `AccessNode.removeAllAccessorChains` on every
non-trivial strongly connected component of the accessor graph.  That operator descends two
accessors drawn from the component, lifts the subtree it reaches, and merges every lifted
subtree AT THE ROOT.  A summary path `a :: b :: rest` becomes `rest`.

The original word leaves the language.  So the compressed summary ANSWERS LESS than the one it
replaces, which is `registration-not-matching` in its exact form: a premise that asks about
`a :: b :: rest` gets nothing back.

This module proves that, and proves the repair.  The repair places the lifted subtree under a
Kleene star over the accessors the unroll strategy COVERS -- `[any]` -- instead of at the bare
root.  `AccessNode.getChild` descends through `[any]` for every covered accessor, so the star is
a real prefix closure and the original word is still answered.

* `reroot_loses` -- the shipped operator drops the word it descended;
* `lift_answers` -- the repaired operator still answers it;
* `lift_sound` -- the repaired operator answers for a SUPERSET, so it can add findings but never
  remove one (this is the no-false-negative obligation);
* `coverage_is_necessary` -- with an UNCOVERED accessor the star does not close over it, so the
  guard that skips such a component is required, not decorative.

Constructive: no `Classical.choice`, no `sorry`.
-/

namespace FactExplosion.ChainLift

/-- An accessor index.  `AccessorIdx = Int` in the engine; the identity of an accessor is all the
argument uses, so a bare type is enough. -/
abbrev Acc := Nat

/-- The denotation of an access tree: the set of access paths it answers for. -/
abbrev Lang := List Acc → Prop

/-- `starOver covered R` is the language of `[any]* . R` restricted to covered accessors: any
number of covered accessors, then a word of `R`.  This is what `getChild` implements when it
descends through an `[any]` child and re-wraps the remainder with `addParentIfPossible`. -/
inductive starOver (covered : Acc → Prop) (R : Lang) : List Acc → Prop
  | /-- Zero repeats: the star may be skipped entirely. -/
    base {w : List Acc} : R w → starOver covered R w
  | /-- One more covered accessor in front. -/
    step {a : Acc} {w : List Acc} : covered a → starOver covered R w → starOver covered R (a :: w)

/-- What the shipped operator produces: the lifted subtree merged at the ROOT, with no star. -/
def reroot (R : Lang) : Lang := R

/-- What the repaired operator produces: the lifted subtree under an `[any]` edge. -/
def lift (covered : Acc → Prop) (R : Lang) : Lang := starOver covered R

/-- The word the compression descended through, for a chain of length two.  This is exactly the
shape `removeAllAccessorChains` removes: `chainLengthToRemove = 2`. -/
def chained (a b : Acc) (rest : List Acc) : List Acc := a :: b :: rest

/-! ## The shipped operator loses the word -/

/-- `reroot` does not answer for the word it descended.  The witness is the smallest possible
one: a language holding only the empty suffix, and a two-accessor chain in front of it. -/
theorem reroot_loses :
    ∃ (R : Lang) (a b : Acc) (rest : List Acc), R rest ∧ ¬ reroot R (chained a b rest) := by
  refine ⟨fun w => w = [], 0, 0, [], rfl, ?_⟩
  intro h
  simp [reroot, chained] at h

/-! ## The repaired operator keeps it -/

/-- The star answers for any covered prefix placed in front of a word it already answers. -/
theorem starOver_prefix {covered : Acc → Prop} {R : Lang} :
    ∀ {pre : List Acc}, (∀ a ∈ pre, covered a) → ∀ {w}, R w → starOver covered R (pre ++ w) := by
  intro pre
  induction pre with
  | nil => intro _ w hw; exact starOver.base hw
  | cons a pre ih =>
    intro hcov w hw
    exact starOver.step (hcov a (by simp))
      (ih (fun x hx => hcov x (by simp [hx])) hw)

/-- THE REPAIR IS CORRECT.  When both accessors of the removed chain are covered, the lifted
language still answers for the word the compression descended through. -/
theorem lift_answers {covered : Acc → Prop} {R : Lang} {a b : Acc} {rest : List Acc}
    (ha : covered a) (hb : covered b) (hrest : R rest) :
    lift covered R (chained a b rest) :=
  starOver.step ha (starOver.step hb (starOver.base hrest))

/-- NO FALSE NEGATIVE.  The lift only ever adds words: everything the pre-compression language
answered for, the lifted language answers for too.  A widening, not a discard. -/
theorem lift_sound {covered : Acc → Prop} {R : Lang} {w : List Acc} (h : R w) :
    lift covered R w :=
  starOver.base h

/-- The lift is monotone in the language it wraps, so composing it with the recursive descent in
`removeAllAccessorChains` cannot lose a word either. -/
theorem lift_mono {covered : Acc → Prop} {R S : Lang} (h : ∀ w, R w → S w) :
    ∀ w, lift covered R w → lift covered S w := by
  intro w hw
  induction hw with
  | base hr => exact starOver.base (h _ hr)
  | step hc _ ih => exact starOver.step hc ih

/-! ## The coverage guard is required -/

/-- With an accessor the strategy does NOT cover, the star does not close over it, so the word is
still lost.  This is why `compressNode` skips a component that contains an uncovered accessor
instead of lifting it: the star cannot stand in for what `getChild` will not descend through. -/
theorem coverage_is_necessary :
    ∃ (covered : Acc → Prop) (R : Lang) (a : Acc) (rest : List Acc),
      ¬ covered a ∧ R rest ∧ ¬ lift covered R (a :: rest) := by
  refine ⟨fun _ => False, fun w => w = [], 0, [], not_false, rfl, ?_⟩
  intro h
  cases h with
  | base hr => simp at hr
  | step hc _ => exact hc

/-! ## What this does and does not establish

`lift_sound` discharges the no-false-negative obligation for the OPERATOR.  It says nothing about
whether the operator is worth running: measurement on conductor shows `compressNode` is inert
there -- disabling it entirely moves events by 0.2% and changes no finding -- so this is a latent
recall bug repaired, not a performance lever.

It also says nothing about COST.  `lift` answers for strictly more words than `reroot`, and by
`structure-destruction-relocates-to-demand` a language that answers for more is asked for more.
The star is cheap to store and expensive to read, which is `collapse-moves-the-cost`. -/

end FactExplosion.ChainLift
