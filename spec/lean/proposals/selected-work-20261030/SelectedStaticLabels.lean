import Std

/-
  Source reference: analyzer core bb74cef6c; documentation HEAD 9d997343a.
  Scope: necessary mark selection before decoding/owner tests; complete rows
  and the final AP predicate are retained. There is no SCC owner index here.

  `Atom.zero` represents the private nullable endpoint of a local W/R row.
  A bridge never has that endpoint. FLOW is a separate relation, not an atom.
  The mark-free AP image below is parametric in *all* existing geometry checks.
  The factorization binds to a legal FULL original and nonzero mapped target;
  it does not claim a new proof of the whole AP emitter or a new AP policy.
-/
namespace SelectedStaticLabels

inductive Atom where
  | zero
  | full (group id : Nat)
  | group (id : Nat)
deriving DecidableEq, Repr

def covers : Atom → Atom → Bool
  | .zero, .zero => true
  | .full g t, .full h u => g == h && t == u
  | .group g, .full h _ => g == h
  | .group g, .group h => g == h
  | _, _ => false

def nonzero : Atom → Bool
  | .zero => false
  | _ => true

/-- Exact current composeMarks guard: ZERO endpoints cannot be joined. -/
def composable (leftOutput rightInput : Atom) : Bool :=
  nonzero leftOutput && nonzero rightInput &&
    (covers leftOutput rightInput || covers rightInput leftOutput)

theorem covers_self (a : Atom) : covers a a = true := by
  cases a <;> simp only [covers, BEq.beq, decide_true, Bool.true_and]

theorem zero_not_composable (a : Atom) :
    composable .zero a = false ∧ composable a .zero = false := by
  cases a <;> simp [composable, nonzero]

theorem group_covers_full (g t : Nat) : covers (.group g) (.full g t) = true := by
  simp only [covers, BEq.beq, decide_true]

theorem full_does_not_cover_group (g t : Nat) :
    covers (.full g t) (.group g) = false := rfl

theorem different_fulls_in_group (g t u : Nat) (different : t ≠ u) :
    covers (.full g t) (.full g u) = false ∧
    composable (.full g t) (.full g u) = false := by
  have reverse : u ≠ t := Ne.symm different
  simp only [covers, composable, nonzero, BEq.beq, different, reverse,
    decide_false, decide_true, Bool.true_and, Bool.false_or]
  exact ⟨True.intro, True.intro⟩

inductive Label where
  | flow
  | mapped (input output : Atom)
deriving DecidableEq, Repr

inductive Selection where
  | all
  | flowOnly
  | outputCovers (actual : Atom)
  | outputComposesWith (rightInput : Atom)
deriving DecidableEq, Repr

def selected : Selection → Label → Bool
  | .all, _ => true
  | _, .flow => true
  | .flowOnly, .mapped _ _ => false
  | .outputCovers actual, .mapped _ output => covers output actual
  | .outputComposesWith required, .mapped _ output => composable output required

/-- This table is the bucket-selection specification. FULL/GROUP is directional. -/
def bucketCover : Atom → Atom → Bool
  | .zero, output => output == .zero
  | .full g t, output => output == .full g t || output == .group g
  | .group g, output => output == .group g

def sameFullGroup (group : Nat) : Atom → Bool
  | .full g _ => g == group
  | _ => false

def bucketCompose : Atom → Atom → Bool
  | .zero, _ => false
  | .full g t, output => output == .full g t || output == .group g
  | .group g, output => output == .group g || sameFullGroup g output

theorem bucket_cover_exact (query output : Atom) :
    bucketCover query output = covers output query := by
  cases query <;> cases output <;> simp [bucketCover, covers, BEq.beq]

theorem bucket_compose_exact (query output : Atom) :
    bucketCompose query output = composable output query := by
  cases query <;> cases output <;>
    simp [bucketCompose, sameFullGroup, composable, nonzero, covers,
      BEq.beq, Bool.or_comm, eq_comm]

/-- The pair, geometry ID and owner family are retained in one old row. -/
structure Row where
  ordinal : Nat
  geometry : Nat
  ownerFamily : Nat
  label : Label
deriving DecidableEq, Repr

def selectRows (selection : Selection) (rows : List Row) : List Row :=
  rows.filter (fun row => selected selection row.label)

theorem selected_row_is_same_complete_row (selection : Selection) (rows : List Row)
    (row : Row) (member : row ∈ selectRows selection rows) : row ∈ rows := by
  exact (List.mem_filter.mp member).1

def baseline (rows : List Row) (owner keep : Row → Bool) : List Row :=
  rows.filter (fun row => owner row && keep row)

def optimized (rows : List Row) (selection : Selection) (owner keep : Row → Bool) : List Row :=
  (selectRows selection rows).filter (fun row => owner row && keep row)

/-- Row order and every complete pair are equal after the final predicate.
    The owner is any pure Boolean. Removing impossible questions cannot change it. -/
theorem selected_final_list_equal (rows : List Row) (selection : Selection)
    (owner keep : Row → Bool)
    (necessary : ∀ row, keep row = true → selected selection row.label = true) :
    optimized rows selection owner keep = baseline rows owner keep := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases hk : keep row with
    | false =>
      cases hs : selected selection row.label <;>
        simp [optimized, baseline, selectRows, hk, hs] at ih ⊢
      all_goals exact ih
    | true =>
      have hs := necessary row hk
      cases ho : owner row <;>
        simp [optimized, baseline, selectRows, hk, hs, ho] at ih ⊢
      all_goals exact ih

/-- Existing owner scratch/memo is permitted to change work, not answers.
    This cache contract is separate from, and does not replace, the unchanged
    graph-reachability implementation. A skipped query need not fill a cache. -/
def truthfulOwnerCache (eligible : Nat → Bool) (cache : Nat → Option Bool) : Prop :=
  ∀ family answer, cache family = some answer → answer = eligible family

def cachedOwner (eligible : Nat → Bool) (cache : Nat → Option Bool) (family : Nat) : Bool :=
  match cache family with
  | some answer => answer
  | none => eligible family

theorem owner_answer_independent_of_cache_history (eligible : Nat → Bool)
    (cache : Nat → Option Bool) (truth : truthfulOwnerCache eligible cache) (family : Nat) :
    cachedOwner eligible cache family = eligible family := by
  cases found : cache family with
  | none => simp only [cachedOwner, found]
  | some answer => simpa only [cachedOwner, found] using truth family answer found

inductive EntryMark where
  | flow
  | atom (value : Atom)
deriving DecidableEq, Repr

def markGate : EntryMark → EntryMark → Bool
  | .flow, _ => true
  | .atom _, .flow => false
  | .atom guide, .atom actual => covers guide actual

def entrySelection : EntryMark → Selection
  | .flow => .flowOnly
  | .atom actual => .outputCovers actual

/-- Adapter for the output selector only, not a new runtime guidance edge. -/
def entryLabel : EntryMark → Label
  | .flow => .flow
  | .atom atom => .mapped .zero atom

theorem c2_selected_exact_mark_gate (entry actual : EntryMark) :
    selected (entrySelection actual) (entryLabel entry) = markGate entry actual := by
  cases entry <;> cases actual <;> rfl

/-- Exact syntactic first gate of RestrictedInitialPolicy.emit. `raw` includes
    every later path/tail/E/budget/legality operation and its possible failure. -/
def c2Image {α : Type} (entry actual : EntryMark) (raw : Option α) : Option α :=
  if markGate entry actual then raw else none

theorem c2_gate_necessary {α : Type} (entry actual : EntryMark) (raw : Option α)
    (value : α) (emitted : c2Image entry actual raw = some value) :
    markGate entry actual = true := by
  cases gate : markGate entry actual with
  | false => simp [c2Image, gate] at emitted
  | true => rfl

theorem wrong_c2_mark_has_no_image {α : Type} (entry actual : EntryMark)
    (raw : Option α) (wrong : markGate entry actual = false) :
    c2Image entry actual raw = none := by simp [c2Image, wrong]

/- For a legal FULL member and nonzero mapped right endpoint, current
   canStoreInitial has no abstract-key raw-preimage alternative. All remaining
   checks are mark-ID independent: concrete mark kind, normalized E, base,
   counted path budget, raw-emitter shape and insideLoc. `geometry` is their
   conjunction. This is a modular source-factorization proof, not an AP axiom. -/
def fullMappedImage (geometry : Bool) (guide : Atom) (group fullId : Nat) : Bool :=
  geometry && covers guide (.full group fullId)

def fullMappedPrecheck (geometry : Bool) (group fullId : Nat) : Bool :=
  fullMappedImage geometry (.full group fullId) group fullId

theorem full_precheck_is_geometry (geometry : Bool) (group fullId : Nat) :
    fullMappedPrecheck geometry group fullId = geometry := by
  simp only [fullMappedPrecheck, fullMappedImage, covers, BEq.beq,
    decide_true, Bool.and_true]

theorem productive_mapped_implies_geometry (geometry : Bool) (guide : Atom)
    (group fullId : Nat)
    (productive : fullMappedImage geometry guide group fullId = true) :
    fullMappedPrecheck geometry group fullId = true := by
  rw [full_precheck_is_geometry]
  exact (Bool.and_eq_true_iff.mp productive).1

def fixedRight (geometry : Bool) (member : EntryMark) : Label → Bool
  | .flow => true
  | .mapped _ output => match member with
    | .flow => false
    | .atom actual => geometry && covers output actual

def targetSelection : EntryMark → Selection
  | .flow => .flowOnly
  | .atom actual => .outputCovers actual

theorem target_selection_necessary (geometry : Bool) (member : EntryMark)
    (label : Label) (kept : fixedRight geometry member label = true) :
    selected (targetSelection member) label = true := by
  cases label with
  | flow => cases member <;> rfl
  | mapped input output =>
    cases member with
    | flow => simp [fixedRight] at kept
    | atom actual => exact (Bool.and_eq_true_iff.mp kept).2

def compose : Label → Label → Option Label
  | .flow, right => some right
  | .mapped i o, .flow => some (.mapped i o)
  | .mapped i o, .mapped u t =>
    if composable o u then some (.mapped i t) else none

def incomingSelection (member : EntryMark) : Label → Selection
  | .flow => targetSelection member
  | .mapped input _ => .outputComposesWith input

theorem productive_predecessor_selected (geometry : Bool) (member : EntryMark)
    (left right result : Label) (composed : compose left right = some result)
    (kept : fixedRight geometry member result = true) :
    selected (incomingSelection member right) left = true := by
  cases left with
  | flow => cases right <;> cases member <;> rfl
  | mapped li lo =>
    cases right with
    | flow =>
      have same : Label.mapped li lo = result := by simpa [compose] using composed
      subst result
      exact target_selection_necessary geometry member (.mapped li lo) kept
    | mapped ri ro =>
      cases hj : composable lo ri with
      | false => simp [compose, hj] at composed
      | true => exact hj

/-- FLOW itself is not rejected when its mapped predecessor can supply T. -/
theorem flow_repair_is_preserved (g u t : Nat) :
    compose (.mapped (.full g u) (.full g t)) .flow =
      some (.mapped (.full g u) (.full g t)) ∧
    selected (incomingSelection (.atom (.full g t)) .flow)
      (.mapped (.full g u) (.full g t)) = true := by
  simp only [compose, incomingSelection, targetSelection, selected, covers,
    BEq.beq, decide_true, Bool.true_and, eq_self, true_and]

def isFlow : Label → Bool
  | .flow => true
  | _ => false

theorem no_flow_filter (labels : List Label) (absent : .flow ∉ labels) :
    labels.filter isFlow = [] := by
  induction labels with
  | nil => rfl
  | cons label rest ih =>
    cases label with
    | flow => exact False.elim (absent List.mem_cons_self)
    | mapped i o =>
      have tail : Label.flow ∉ rest := fun h => absent (List.mem_cons_of_mem _ h)
      exact (List.filter_cons_of_neg (fun h => Bool.false_ne_true h)).trans (ih tail)

theorem unique_flow_visits_at_most_one (labels : List Label) (unique : labels.Nodup) :
    (labels.filter isFlow).length ≤ 1 := by
  induction labels with
  | nil => exact Nat.zero_le 1
  | cons label rest ih =>
    have parts := List.nodup_cons.mp unique
    cases label with
    | flow =>
      rw [List.filter_cons_of_pos (rfl : isFlow .flow = true), no_flow_filter rest parts.1]
      exact Nat.le_refl 1
    | mapped i o =>
      rw [List.filter_cons_of_neg (fun h => Bool.false_ne_true h)]
      exact ih parts.2

/- The endpoint-source preflight must remain conservative: an earlier U writer
   can be changed to T by a later bridge. Filtering the writer by T is invalid. -/
theorem source_preflight_counterexample :
    covers (.full 7 1) (.full 7 2) = false ∧
    compose (.mapped .zero (.full 7 1))
      (.mapped (.full 7 1) (.full 7 2)) =
        some (.mapped .zero (.full 7 2)) := by decide

def controls : Bool :=
  bucketCover (.full 7 2) (.group 7) &&
  !bucketCover (.group 7) (.full 7 2) &&
  bucketCompose (.group 7) (.full 7 2) &&
  !bucketCompose (.zero) (.zero) &&
  bucketCover .zero .zero &&
  !bucketCompose (.full 7 2) (.full 7 3)

example : controls = true := by decide

#eval controls
#print axioms covers_self
#print axioms zero_not_composable
#print axioms group_covers_full
#print axioms full_does_not_cover_group
#print axioms different_fulls_in_group
#print axioms bucket_cover_exact
#print axioms bucket_compose_exact
#print axioms selected_final_list_equal
#print axioms selected_row_is_same_complete_row
#print axioms owner_answer_independent_of_cache_history
#print axioms c2_selected_exact_mark_gate
#print axioms c2_gate_necessary
#print axioms wrong_c2_mark_has_no_image
#print axioms full_precheck_is_geometry
#print axioms productive_mapped_implies_geometry
#print axioms target_selection_necessary
#print axioms productive_predecessor_selected
#print axioms flow_repair_is_preserved
#print axioms no_flow_filter
#print axioms unique_flow_visits_at_most_one
#print axioms source_preflight_counterexample

end SelectedStaticLabels
