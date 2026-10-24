/-
  Local run-1 FLOW/TAINT coverage investigation, 24 October 2026.

  This file uses the original AP pair denotation and original F72 emitter.
  It does not use StrongQueries. It proves cross-premise ANY coverage and
  distinguishes mark-changing dependencies from mark-preserving transport.
  It does not prove a complete inter-run simulation or permission to remove
  arbitrary source/cleaner observations. Those are separate obligations.
-/
import ApSpec.AbsWitness

namespace ApSpec.Run1FlowTaintCoverage
open ApSpec ApSpec.Abs

def initial (b : Base) (p : List Acc) (m : MarkA) : PFact :=
  ⟨b, p, .star Excl.empty, m⟩

def anyFinal (b : Base) (p : List Acc) (m : MarkA) : PFact :=
  ⟨b, p, .any, m⟩

/-- ANY FLOW covers same-mark ANY TAINT across corresponding initial keys. -/
theorem any_flow_covers_taint
    (a b : Base) (p q : List Acc) (t : Mark) (excluded : List Mark)
    (allowed : memB t excluded = false) (l0 l1 : Loc)
    (marked : den (initial a p (.conc t)) (anyFinal b q (.conc t)) l0 l1) :
    den (initial a p .star) (anyFinal b q (.starEx excluded)) l0 l1 := by
  obtain ⟨hb0, hb1, hm0, hm1, _, s, r, hp0, hp1, hi, hf⟩ := marked
  have mark0 : l0.mark = t := hm0
  have mark1 : l1.mark = t := hm1
  refine ⟨hb0, hb1, trivial, ?_, ?_, s, r, hp0, hp1, hi, hf⟩
  · change l1.mark = l0.mark
    exact mark1.trans mark0.symm
  · change memB l0.mark excluded = false
    rw [mark0]
    exact allowed

/-- A FLOW output preserves the input mark, also when its tail is ANY. -/
theorem flow_preserves_mark
    (a b : Base) (p q : List Acc) (excluded : List Mark) (l0 l1 : Loc)
    (pair : den (initial a p .star) (anyFinal b q (.starEx excluded)) l0 l1) :
    l1.mark = l0.mark := pair.2.2.2.1

/-- T-to-U generation cannot be covered by a mark-preserving FLOW if T differs from U. -/
theorem different_mark_not_covered
    (a b : Base) (p q : List Acc) (t u : Mark) (excluded : List Mark)
    (different : t ≠ u) (l0 l1 : Loc)
    (generated : den (initial a p (.conc t)) (anyFinal b q (.conc u)) l0 l1) :
    ¬ den (initial a p .star) (anyFinal b q (.starEx excluded)) l0 l1 := by
  intro flow
  have input : l0.mark = t := generated.2.2.1
  have output : l1.mark = u := generated.2.2.2.1
  have same := flow_preserves_mark a b p q excluded l0 l1 flow
  exact different (input.symm.trans (same.symm.trans output))

/-- Concrete witness for the STAR-versus-ANY correlation gap. -/
def leftInput : Loc := ⟨1, [10], 7⟩
def rightOutput : Loc := ⟨2, [20], 7⟩

theorem any_taint_cross_suffix :
    den (initial 1 [] (.conc 7)) (anyFinal 2 [] (.conc 7)) leftInput rightOutput := by
  exact ⟨rfl, rfl, rfl, rfl, trivial, [10], [20], rfl, rfl, rfl, trivial⟩

theorem star_flow_rejects_cross_suffix :
    ¬ den (initial 1 [] .star) (initial 2 [] .star) leftInput rightOutput := by
  intro h
  obtain ⟨_, _, _, _, _, s, r, hp0, hp1, _, hf⟩ := h
  have hs : s = [10] := by simpa [initial, leftInput] using hp0.symm
  have hr : r = [20] := by simpa [initial, rightOutput] using hp1.symm
  have same : r = s := hf.1
  rw [hs, hr] at same
  cases same

/-- A cleaner's exclusion prevents the cross-premise coverage. -/
theorem excluded_mark_not_covered :
    ¬ den (initial 1 [] .star) (anyFinal 2 [] (.starEx [7])) leftInput rightOutput := by
  intro h
  have stopped : memB 7 [7] = false := h.2.2.2.2.1
  cases stopped

/-- The original abstract demand emits its FLOW form, not a concrete T query. -/
theorem original_abstract_emission :
    emitW (anyFinal 2 [] .star) ⟨2, [], .exact, .conc 7⟩ =
      some (initial 2 [] .star) := by
  rfl

/-- A concrete guide keeps its concrete query. The two starts are intentionally different. -/
theorem original_concrete_emission :
    emitW (anyFinal 2 [] (.conc 7)) ⟨2, [], .exact, .conc 7⟩ =
      some ⟨2, [], .exact, .conc 7⟩ := by
  rfl

/-! A rule can be redundant in a coarse run-1 relation but necessary to
    the concrete program. Use the original AP operations, with empty E.
    Base 1 is p, base 2 is x, base 3 is the returned value. Accessor 10 is
    left and accessor 20 is right. `spread` is a lawful may-target pass. -/

def readFrom : PFact := ⟨1, [20], .star Excl.empty, .star⟩
def readTo : PFact := initial 2 [] .star
def genFrom : PFact := ⟨1, [10], .exact, .conc 7⟩
def genTo : PFact := ⟨2, [], .exact, .conc 7⟩
def spreadFrom : PFact := initial 2 [] .star
def spreadTo : PFact := anyFinal 3 [] .star
def actualLeft : Loc := ⟨1, [10], 7⟩
def actualX : Loc := ⟨2, [], 7⟩

theorem read_abstracts_to_any :
    applyEdge (startFact (initial 1 [] .star)) readFrom readTo =
      ⟨[⟨anyFinal 2 [] .star, true⟩], []⟩ := by rfl

theorem marked_gen_fires :
    applyEdge (startFact (initial 1 [] (.conc 7))) genFrom genTo =
      ⟨[⟨genTo, true⟩], []⟩ := by rfl

theorem spread_flow :
    applyEdge ⟨anyFinal 2 [] .star, true⟩ spreadFrom spreadTo =
      ⟨[⟨anyFinal 3 [] .star, true⟩], []⟩ := by rfl

theorem spread_generated_mark :
    applyEdge ⟨genTo, true⟩ spreadFrom spreadTo =
      ⟨[⟨anyFinal 3 [] (.conc 7), true⟩], []⟩ := by rfl

theorem generated_output_is_coarsely_covered (l0 l1 : Loc)
    (h : den (initial 1 [] (.conc 7)) (anyFinal 3 [] (.conc 7)) l0 l1) :
    den (initial 1 [] .star) (anyFinal 3 [] .star) l0 l1 := by
  simpa [den, initial, anyFinal, MarkA.out, MarkA.passes, memB] using
    any_flow_covers_taint 1 3 [] [] 7 [] rfl l0 l1 h

theorem gen_adds_a_real_pair : den genFrom genTo actualLeft actualX := by
  exact ⟨rfl, rfl, rfl, rfl, trivial, [], [], rfl, rfl, rfl, rfl⟩

theorem read_does_not_supply_that_pair : ¬ den readFrom readTo actualLeft actualX := by
  intro h
  obtain ⟨_, _, _, _, _, s, _, hp, _, _, _⟩ := h
  have impossible : [10] = [20] ++ s := hp
  cases impossible

theorem abstract_backward_query_does_not_fire_gen :
    (applyEdge ⟨initial 2 [] .star, false⟩ genTo genFrom).facts = [] := by rfl

theorem concrete_backward_query_fires_gen :
    (applyEdge ⟨genTo, false⟩ genTo genFrom).facts = [⟨genFrom, false⟩] := by rfl

/-! Selected protection rules. This is edge metadata, not a new mark atom.
    No CM definiteness test, field change, or StrongQueries rule is added. -/

def assignProtection (old : Bool) (origin assigned : Mark) : Bool :=
  old || Nat.beq origin assigned

def summaryProtection (inputProtected summaryProtected : Bool)
    (origin incoming outgoing : Mark) : Bool :=
  inputProtected || summaryProtected ||
    (Nat.beq origin outgoing && !(Nat.beq incoming outgoing))

def mergeProtection (a b : Bool) : Bool := a || b

def maySubsume (covered blocked : Bool) : Bool := covered && !blocked

theorem same_mark_assignment_is_protected (old : Bool) (t : Mark) :
    assignProtection old t t = true := by
  simp [assignProtection]

theorem protected_summary_is_carried (input : Bool) (t u v : Mark) :
    summaryProtection input true t u v = true := by
  simp [summaryProtection]

theorem protected_input_is_carried (callee : Bool) (t u v : Mark) :
    summaryProtection true callee t u v = true := by
  simp [summaryProtection]

theorem mark_cycle_is_protected (input callee : Bool) (t u : Mark)
    (different : Nat.beq u t = false) :
    summaryProtection input callee t u t = true := by
  simp [summaryProtection, different]

theorem ordinary_diagonal_transport_is_not_new_protection (t : Mark) :
    summaryProtection false false t t t = false := by
  simp [summaryProtection]

theorem protected_duplicate_dominates (old : Bool) :
    mergeProtection old true = true ∧ mergeProtection true old = true := by
  cases old <;> decide

theorem protection_merge_order_independent (a b : Bool) :
    mergeProtection a b = mergeProtection b a := by
  cases a <;> cases b <;> decide

theorem protection_merge_idempotent (a : Bool) : mergeProtection a a = a := by
  cases a <;> decide

theorem protected_member_is_not_subsumed (covered : Bool) :
    maySubsume covered true = false := by
  cases covered <;> decide

theorem late_protection_changes_admission :
    maySubsume true false = true ∧ maySubsume true true = false := by decide

theorem gen_counterexample_keeps_its_marked_obligation :
    maySubsume true (assignProtection false 7 7) = false := by decide

#print axioms any_flow_covers_taint
#print axioms flow_preserves_mark
#print axioms different_mark_not_covered
#print axioms any_taint_cross_suffix
#print axioms star_flow_rejects_cross_suffix
#print axioms excluded_mark_not_covered
#print axioms original_abstract_emission
#print axioms original_concrete_emission
#print axioms read_abstracts_to_any
#print axioms marked_gen_fires
#print axioms spread_flow
#print axioms spread_generated_mark
#print axioms generated_output_is_coarsely_covered
#print axioms gen_adds_a_real_pair
#print axioms read_does_not_supply_that_pair
#print axioms abstract_backward_query_does_not_fire_gen
#print axioms concrete_backward_query_fires_gen
#print axioms same_mark_assignment_is_protected
#print axioms protected_summary_is_carried
#print axioms protected_input_is_carried
#print axioms mark_cycle_is_protected
#print axioms ordinary_diagonal_transport_is_not_new_protection
#print axioms protected_duplicate_dominates
#print axioms protection_merge_order_independent
#print axioms protection_merge_idempotent
#print axioms protected_member_is_not_subsumed
#print axioms late_protection_changes_admission
#print axioms gen_counterexample_keeps_its_marked_obligation

end ApSpec.Run1FlowTaintCoverage
