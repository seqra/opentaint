import Std
namespace EquivalentOutputSelectors
/- Exact DATA output equivalence only. Never normalize C2 demand entries. -/
inductive Tail where | exact | star | may | must
  deriving DecidableEq, Repr
inductive Mark where | flow (excluded : List Nat) | concrete (id : Nat)
  deriving DecidableEq, Repr
structure Pattern where
  base : Nat
  path : List Nat
  tail : Tail
  mark : Mark
  excluded : List Nat
  deriving DecidableEq, Repr
structure Conclusion (Metadata : Type) where
  pattern : Pattern
  demand : Bool
  metadata : Metadata

def marksMeet : Mark → Mark → Bool
  | .concrete a, .concrete b => a == b
  | .concrete a, .flow e | .flow e, .concrete a => !e.contains a
  | .flow _, .flow _ => true
def admits (excluded suffix : List Nat) : Bool :=
  match suffix with | [] => true | a :: _ => !excluded.contains a
def tailAdmits (tail : Tail) (excluded suffix : List Nat) : Bool :=
  match tail with
  | .exact => suffix.isEmpty
  | .star | .must => admits excluded suffix
  | .may => true
def prefixB (p q : List Nat) : Bool := decide (p = q.take p.length)
def normalizeDemand (p : Pattern) : Pattern :=
  match p.mark, p.tail with
  | .flow _, .star => { p with excluded := [] }
  | _, _ => p
def unionE (a b : List Nat) : List Nat := a ++ b.filter (fun m => !a.contains m)
def meetConclusion {M : Type} (c : Conclusion M) (d : Pattern) : Conclusion M :=
  match c.pattern.tail with
  | .exact | .star => c
  | .may | .must =>
    if d.tail == .exact then
      { c with pattern := { c.pattern with tail := .exact, excluded := if c.pattern.tail == .must then (match c.pattern.mark with | .flow _ => c.pattern.excluded | _ => []) else [] } }
    else if c.pattern.tail == .must && d.tail == .star then
      { c with pattern := { c.pattern with excluded := unionE c.pattern.excluded d.excluded } }
    else c

def restrictExit {M : Type} (c : Conclusion M) (rawDemand : Pattern) : Option (Conclusion M) :=
  let d := normalizeDemand rawDemand
  if !marksMeet d.mark c.pattern.mark || c.pattern.base != d.base then none else
  let p := d.path
  let q := c.pattern.path
  if q == p then some (meetConclusion c d)
  else if prefixB p q then
    if tailAdmits d.tail d.excluded (q.drop p.length) then some c else none
  else if prefixB q p then
    match c.pattern.tail with
    | .may | .must =>
      if !admits c.pattern.excluded (p.drop q.length) then none
      else if d.tail == .exact then
        some { c with pattern := { c.pattern with path := p, tail := .exact, excluded := [] } }
      else some { c with pattern := { c.pattern with path := p, excluded := if c.pattern.tail == .must && d.tail == .star then d.excluded else [] } }
    | .star => if admits c.pattern.excluded (p.drop q.length) then some c else none
    | .exact => none
  else none

def selector (base : Nat) (path : List Nat) (mark : Mark) (tail : Tail) : Pattern :=
  ⟨base, path, tail, mark, []⟩
theorem normalized_empty_selector (base : Nat) (path : List Nat) (mark : Mark) (tail : Tail) :
    normalizeDemand (selector base path mark tail) = selector base path mark tail := by
  cases mark <;> cases tail <;> rfl

theorem admits_empty (suffix : List Nat) : admits [] suffix = true := by
  cases suffix <;> rfl

theorem empty_star_and_may_meet_equal {M : Type} (c : Conclusion M)
    (base : Nat) (path : List Nat) (mark : Mark) :
    meetConclusion c (selector base path mark .star) = meetConclusion c (selector base path mark .may) := by
  cases c with | mk p demand metadata =>
    cases p with | mk b q tail actualMark e =>
      cases tail <;> simp [meetConclusion, selector, unionE]

theorem empty_star_and_may_exit_equal {M : Type} (c : Conclusion M)
    (base : Nat) (path : List Nat) (mark : Mark) :
    restrictExit c (selector base path mark .star) = restrictExit c (selector base path mark .may) := by
  simp only [restrictExit, normalized_empty_selector]
  by_cases valid : (!marksMeet mark c.pattern.mark || c.pattern.base != base) = true
  · simp [selector, valid]
  · simp only [selector] at valid ⊢
    simp only [valid, Bool.false_eq_true, ↓reduceIte]
    by_cases same : (c.pattern.path == path) = true
    · simpa only [same, selector, ↓reduceIte, Option.some.injEq] using empty_star_and_may_meet_equal c base path mark
    · simp only [same, Bool.false_eq_true, ↓reduceIte]
      cases c with | mk p demand metadata =>
        cases p with | mk b q tail actualMark e =>
          cases tail <;> simp [tailAdmits, admits_empty] <;> rfl

def canonicalExit (p : Pattern) : Pattern :=
  if p.tail == .may && p.excluded.isEmpty then { p with tail := .star } else p

theorem canonical_keeps_geometry (p : Pattern) :
    (canonicalExit p).base = p.base ∧ (canonicalExit p).path = p.path ∧ (canonicalExit p).mark = p.mark := by
  unfold canonicalExit
  split <;> exact ⟨rfl,rfl,rfl⟩
theorem canonical_output_preserves_restriction {M : Type} (c : Conclusion M) (p : Pattern) :
    restrictExit c p = restrictExit c (canonicalExit p) := by
  cases p with | mk base path tail mark excluded =>
    cases tail <;> simp [canonicalExit]
    cases excluded with
    | nil => exact (empty_star_and_may_exit_equal c base path mark).symm
    | cons _ _ => rfl

theorem equal_canonical_outputs_equal_restriction {M : Type}
    (c : Conclusion M) (p q : Pattern) (same : canonicalExit p = canonicalExit q) :
    restrictExit c p = restrictExit c q := by
  rw [canonical_output_preserves_restriction c p, same]
  exact (canonical_output_preserves_restriction c q).symm

structure Owner where
  method : Nat
  context : Nat
  block : Nat
  entryPort : Nat
  deriving DecidableEq, Repr
structure Pair where
  owner : Owner
  exitPort : Nat
  entry : Pattern
  exit : Pattern
  deriving DecidableEq, Repr
structure Query where
  owner : Owner
  exitPort : Nat
  deriving DecidableEq, Repr

def pairEquivalent (a b : Pair) : Prop :=
  a.owner = b.owner ∧ a.exitPort = b.exitPort ∧ a.entry = b.entry ∧ canonicalExit a.exit = canonicalExit b.exit

def c2Pair {Added Initial : Type} (admit : Pattern → Added → List Initial)
    (owner : Owner) (added : Added) (p : Pair) : List Initial :=
  if p.owner == owner then admit p.entry added else []
def countedDepth (counted : Nat → Bool) (p : Pattern) : Nat := (p.path.filter counted).length
def budget (global : Nat) (counted : Nat → Bool) (p : Pattern) : Nat :=
  let depth := countedDepth counted p
  if depth >= global then global else depth + 1

def c5Pair {M Result Initial : Type} (acceptEntry : Pattern → Initial → Bool)
    (cut : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (query : Query) (initial : Initial) (raw : Conclusion M) (p : Pair) : List Result :=
  if p.owner == query.owner && p.exitPort == query.exitPort && acceptEntry p.entry initial then
    (restrictExit raw p.exit).toList.flatMap (cut (budget global counted p.exit)) else []

theorem equivalent_pair_c2 {Added Initial : Type} (admit : Pattern → Added → List Initial)
    (owner : Owner) (added : Added) (a b : Pair) (same : pairEquivalent a b) :
    c2Pair admit owner added a = c2Pair admit owner added b := by
  simp [c2Pair, same.1, same.2.2.1]

theorem equivalent_output_budget (global : Nat) (counted : Nat → Bool) (a b : Pattern)
    (same : canonicalExit a = canonicalExit b) : budget global counted a = budget global counted b := by
  have pathEq : a.path = b.path := by
    calc a.path = (canonicalExit a).path := (canonical_keeps_geometry a).2.1.symm
         _ = (canonicalExit b).path := congrArg Pattern.path same
         _ = b.path := (canonical_keeps_geometry b).2.1
  simp [budget, countedDepth, pathEq]

theorem equivalent_pair_c5 {M Result Initial : Type} (acceptEntry : Pattern → Initial → Bool)
    (cut : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (query : Query) (initial : Initial) (raw : Conclusion M) (a b : Pair)
    (same : pairEquivalent a b) :
    c5Pair acceptEntry cut global counted query initial raw a = c5Pair acceptEntry cut global counted query initial raw b := by
  rcases same with ⟨owner, port, entry, exit⟩
  simp only [c5Pair, owner, port, entry, equal_canonical_outputs_equal_restriction raw _ _ exit,
    equivalent_output_budget global counted _ _ exit]

structure Prepared (M Result : Type) where
  execute : Conclusion M → List Result

def preparePair {M Result Initial : Type} (acceptEntry : Pattern → Initial → Bool)
    (cut : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (query : Query) (initial : Initial) (p : Pair) : Option (Prepared M Result) :=
  if p.owner == query.owner && p.exitPort == query.exitPort && acceptEntry p.entry initial then
    some ⟨fun raw => (restrictExit raw p.exit).toList.flatMap (cut (budget global counted p.exit))⟩ else none

def executePrepared {M Result : Type} (p : Option (Prepared M Result)) (raw : Conclusion M) : List Result :=
  match p with | none => [] | some command => command.execute raw

theorem prepared_is_native {M Result Initial : Type} (acceptEntry : Pattern → Initial → Bool)
    (cut : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (query : Query) (initial : Initial) (raw : Conclusion M) (p : Pair) :
    executePrepared (preparePair acceptEntry cut global counted query initial p) raw =
      c5Pair acceptEntry cut global counted query initial raw p := by
  unfold preparePair c5Pair
  split <;> rfl

theorem equivalent_prepared_outputs {M Result Initial : Type} (acceptEntry : Pattern → Initial → Bool)
    (cut : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (query : Query) (initial : Initial) (raw : Conclusion M) (a b : Pair) (same : pairEquivalent a b) :
    executePrepared (preparePair acceptEntry cut global counted query initial a) raw =
      executePrepared (preparePair acceptEntry cut global counted query initial b) raw := by
  rw [prepared_is_native, prepared_is_native]
  exact equivalent_pair_c5 acceptEntry cut global counted query initial raw a b same


/- Reply equality includes prepared output-base eligibility and owner/method
   support. Counts are diagnostic; supported native policies use these booleans. -/
inductive Request (Added Initial M : Type) where
  | initials (owner : Owner) (added : Added)
  | summary (query : Query) (initial : Initial) (raw : Conclusion M)
  | outputBase (query : Query) (initial : Initial) (base : Nat)
  | owner (owner : Owner)
  | method (method context : Nat)
  | nonempty
  | unaffected (id : Nat)
inductive Atom (Initial Result : Type) where
  | initial (value : Initial)
  | output (value : Result)
  | support
  deriving DecidableEq

def pairReply {Added Initial M Result : Type} (admit : Pattern → Added → List Initial)
    (acceptEntry : Pattern → Initial → Bool) (cut : Nat → Conclusion M → List Result)
    (global : Nat) (counted : Nat → Bool) (p : Pair) : Request Added Initial M → List (Atom Initial Result)
  | .initials owner added => (c2Pair admit owner added p).map .initial
  | .summary query initial raw => (c5Pair acceptEntry cut global counted query initial raw p).map .output
  | .outputBase query initial base =>
      if p.owner == query.owner && p.exitPort == query.exitPort && acceptEntry p.entry initial && p.exit.base == base then [.support] else []
  | .owner owner => if p.owner == owner then [.support] else []
  | .method method context => if p.owner.method == method && p.owner.context == context then [.support] else []
  | .nonempty => [.support]
  | .unaffected _ => []

theorem equivalent_pair_all_replies {Added Initial M Result : Type} (admit : Pattern → Added → List Initial)
    (acceptEntry : Pattern → Initial → Bool) (cut : Nat → Conclusion M → List Result)
    (global : Nat) (counted : Nat → Bool) (a b : Pair) (same : pairEquivalent a b)
    (query : Request Added Initial M) :
    pairReply admit acceptEntry cut global counted a query = pairReply admit acceptEntry cut global counted b query := by
  have bases : a.exit.base = b.exit.base := by
    calc a.exit.base = (canonicalExit a.exit).base := (canonical_keeps_geometry a.exit).1.symm
         _ = (canonicalExit b.exit).base := congrArg Pattern.base same.2.2.2
         _ = b.exit.base := (canonical_keeps_geometry b.exit).1
  cases query with
  | initials owner added => exact congrArg _ (equivalent_pair_c2 admit owner added a b same)
  | summary query initial raw => exact congrArg _ (equivalent_pair_c5 acceptEntry cut global counted query initial raw a b same)
  | outputBase query initial base => simp [pairReply, same.1, same.2.1, same.2.2.1, bases]
  | owner owner => simp [pairReply, same.1]
  | method method context => simp [pairReply, same.1]
  | nonempty => rfl
  | unaffected _ => rfl

inductive Projection where
  | data (pair : Pair)
  | other (opaqueNativeKey : Nat)
  deriving DecidableEq, Repr

def canonicalPair (p : Pair) : Pair := { p with exit := canonicalExit p.exit }
def canonicalProjection : Projection → Projection
  | .data p => .data (canonicalPair p)
  | .other key => .other key

theorem canonical_pair_equal_is_equivalent (a b : Pair)
    (same : canonicalPair a = canonicalPair b) : pairEquivalent a b := by
  exact ⟨by simpa only [canonicalPair] using congrArg Pair.owner same,
    by simpa only [canonicalPair] using congrArg Pair.exitPort same,
    by simpa only [canonicalPair] using congrArg Pair.entry same,
    by simpa only [canonicalPair] using congrArg Pair.exit same⟩

def projectionReply {Added Initial M Result : Type} (admit : Pattern → Added → List Initial)
    (acceptEntry : Pattern → Initial → Bool) (cut : Nat → Conclusion M → List Result)
    (global : Nat) (counted : Nat → Bool)
    (other : Nat → Request Added Initial M → List (Atom Initial Result)) :
    Projection → Request Added Initial M → List (Atom Initial Result)
  | .data p, query => pairReply admit acceptEntry cut global counted p query
  | .other key, query => other key query

theorem equivalent_projection_all_replies {Added Initial M Result : Type} (admit : Pattern → Added → List Initial)
    (acceptEntry : Pattern → Initial → Bool) (cut : Nat → Conclusion M → List Result)
    (global : Nat) (counted : Nat → Bool) (other : Nat → Request Added Initial M → List (Atom Initial Result))
    (a b : Projection) (same : canonicalProjection a = canonicalProjection b) (query : Request Added Initial M) :
    projectionReply admit acceptEntry cut global counted other a query =
      projectionReply admit acceptEntry cut global counted other b query := by
  cases a <;> cases b <;> simp only [canonicalProjection, Projection.data.injEq, Projection.other.injEq] at same
  · exact equivalent_pair_all_replies admit acceptEntry cut global counted _ _
      (canonical_pair_equal_is_equivalent _ _ same) query
  · cases same
  · cases same
  · cases same; rfl

/- All unrelated emissions stay an arbitrary shared function. A certificate
   must cover EVERY projection of each removed edge; one ND arm is not enough. -/
def retained (edges : List Nat) (remove : Nat → Bool) : List Nat := edges.filter (fun id => !remove id)
def snapshotReply {Q A : Type} (emit : Nat → List Projection) (reply : Projection → Q → List A)
    (edges : List Nat) (query : Q) : List A := edges.flatMap (fun edge => (emit edge).flatMap (fun p => reply p query))
def SetEq {A : Type} (xs ys : List A) : Prop := ∀ a, a ∈ xs ↔ a ∈ ys

def Anchored (emit : Nat → List Projection) (edges : List Nat) (remove : Nat → Bool) : Prop :=
  ∀ edge ∈ edges, remove edge = true → ∀ p ∈ emit edge,
    ∃ anchor ∈ edges, remove anchor = false ∧
      ∃ q ∈ emit anchor, canonicalProjection p = canonicalProjection q

theorem retained_subset (edges : List Nat) (remove : Nat → Bool) (edge : Nat)
    (member : edge ∈ retained edges remove) : edge ∈ edges := (List.mem_filter.mp member).1

theorem anchored_snapshot_replies {Q A : Type} (emit : Nat → List Projection)
    (reply : Projection → Q → List A)
    (equiv : ∀ p q, canonicalProjection p = canonicalProjection q → ∀ query, reply p query = reply q query)
    (edges : List Nat) (remove : Nat → Bool) (anchors : Anchored emit edges remove) (query : Q) :
    SetEq (snapshotReply emit reply edges query) (snapshotReply emit reply (retained edges remove) query) := by
  intro value
  simp only [snapshotReply, List.mem_flatMap]
  constructor
  · rintro ⟨edge, he, p, hp, hv⟩
    cases removed : remove edge with
    | false => exact ⟨edge, by simp [retained, he, removed], p, hp, hv⟩
    | true =>
      rcases anchors edge he removed p hp with ⟨anchor, ha, keep, q, hq, same⟩
      exact ⟨anchor, by simp [retained, ha, keep], q, hq, by simpa only [equiv p q same query] using hv⟩
  · rintro ⟨edge, he, p, hp, hv⟩
    exact ⟨edge, retained_subset edges remove edge he, p, hp, hv⟩

/- Earlier accepted P/Q removals use their own proofs. This lemma does not
   require them to have selector-equivalent anchors. It only requires that
   the independently retained anchors for THIS predicate survive them. -/
theorem anchors_survive_prior_filter (emit : Nat → List Projection) (edges : List Nat)
    (prior remove targetUniverse : Nat → Bool)
    (priorInside : ∀ edge, prior edge = true → targetUniverse edge = true)
    (certificates : ∀ edge ∈ edges, remove edge = true → ∀ p ∈ emit edge,
      ∃ anchor ∈ edges, targetUniverse anchor = false ∧ remove anchor = false ∧
        ∃ q ∈ emit anchor, canonicalProjection p = canonicalProjection q) :
    Anchored emit (retained edges prior) remove := by
  intro edge he removed p hp
  rcases certificates edge (retained_subset edges prior edge he) removed p hp with
    ⟨anchor, ha, outside, keep, q, hq, same⟩
  have priorKeep : prior anchor = false := by
    cases value : prior anchor with
    | false => rfl
    | true => have bad := priorInside anchor value; rw [outside] at bad; contradiction
  exact ⟨anchor, by simp [retained, ha, priorKeep], keep, q, hq, same⟩

theorem anchored_nonempty (emit : Nat → List Projection) (edges : List Nat)
    (remove : Nat → Bool) (anchors : Anchored emit edges remove)
    (noEmpty : ∀ edge ∈ edges, ∃ p, p ∈ emit edge) :
    (∃ edge, edge ∈ edges) ↔ (∃ edge, edge ∈ retained edges remove) := by
  constructor
  · rintro ⟨edge, he⟩
    cases removed : remove edge with
    | false => exact ⟨edge, by simp [retained, he, removed]⟩
    | true =>
      rcases noEmpty edge he with ⟨p, hp⟩
      rcases anchors edge he removed p hp with ⟨anchor, ha, keep, _⟩
      exact ⟨anchor, by simp [retained, ha, keep]⟩
  · rintro ⟨edge, he⟩
    exact ⟨edge, retained_subset edges remove edge he⟩

/- Equality of all demand-oracle membership replies gives equality of every
   iteration of ANY unchanged semantic analyzer transition. The transition
   may contain loops/calls/ND/observations; no future preservation law is an
   input premise. Native scope is the audited built-in demand API, not custom
   policies that inspect exact diagnostic row counts. -/
def oracle {Q A : Type} [DecidableEq A] (emit : Nat → List Projection)
    (reply : Projection → Q → List A) (edges : List Nat) : Q → A → Bool :=
  fun query value => decide (value ∈ snapshotReply emit reply edges query)

theorem anchored_oracles_equal {Q A : Type} [DecidableEq A] (emit : Nat → List Projection)
    (reply : Projection → Q → List A)
    (equiv : ∀ p q, canonicalProjection p = canonicalProjection q → ∀ query, reply p query = reply q query)
    (edges : List Nat) (remove : Nat → Bool) (anchors : Anchored emit edges remove) :
    oracle emit reply edges = oracle emit reply (retained edges remove) := by
  funext query value
  have member := anchored_snapshot_replies emit reply equiv edges remove anchors query value
  simp only [oracle]
  exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using member)

def iterate {Oracle State : Type} (step : Oracle → State → State) (input : Oracle) : Nat → State → State
  | 0, state => state
  | n+1, state => iterate step input n (step input state)

theorem unchanged_transition_all_iterations {Oracle State : Type} (step : Oracle → State → State)
    (left right : Oracle) (equal : left = right) (n : Nat) (initial : State) :
    iterate step left n initial = iterate step right n initial := by cases equal; rfl

theorem anchored_all_future_iterations {Q A State : Type} [DecidableEq A]
    (emit : Nat → List Projection) (reply : Projection → Q → List A)
    (equiv : ∀ p q, canonicalProjection p = canonicalProjection q → ∀ query, reply p query = reply q query)
    (edges : List Nat) (remove : Nat → Bool) (anchors : Anchored emit edges remove)
    (step : (Q → A → Bool) → State → State) (n : Nat) (initial : State) :
    iterate step (oracle emit reply edges) n initial =
      iterate step (oracle emit reply (retained edges remove)) n initial :=
  unchanged_transition_all_iterations step _ _ (anchored_oracles_equal emit reply equiv edges remove anchors) n initial

end EquivalentOutputSelectors
#print axioms EquivalentOutputSelectors.empty_star_and_may_meet_equal
#print axioms EquivalentOutputSelectors.empty_star_and_may_exit_equal
#print axioms EquivalentOutputSelectors.canonical_keeps_geometry
#print axioms EquivalentOutputSelectors.canonical_output_preserves_restriction
#print axioms EquivalentOutputSelectors.equal_canonical_outputs_equal_restriction

#print axioms EquivalentOutputSelectors.equivalent_pair_c2
#print axioms EquivalentOutputSelectors.equivalent_output_budget
#print axioms EquivalentOutputSelectors.equivalent_pair_c5
#print axioms EquivalentOutputSelectors.prepared_is_native
#print axioms EquivalentOutputSelectors.equivalent_prepared_outputs

#print axioms EquivalentOutputSelectors.equivalent_pair_all_replies
#print axioms EquivalentOutputSelectors.canonical_pair_equal_is_equivalent
#print axioms EquivalentOutputSelectors.equivalent_projection_all_replies
#print axioms EquivalentOutputSelectors.retained_subset
#print axioms EquivalentOutputSelectors.anchored_snapshot_replies
#print axioms EquivalentOutputSelectors.anchors_survive_prior_filter
#print axioms EquivalentOutputSelectors.anchored_nonempty
#print axioms EquivalentOutputSelectors.anchored_oracles_equal
#print axioms EquivalentOutputSelectors.unchanged_transition_all_iterations
#print axioms EquivalentOutputSelectors.anchored_all_future_iterations

namespace RetainedQueryBasis
open EquivalentOutputSelectors

/- Closed finite data avoids large-array bounds proofs and substitution into
   a giant lambda during kernel evaluation. Database correctness is still
   checked below; this helper changes no row or certificate proposition. -/
inductive LookupTree (A : Type) where
  | empty
  | leaf (index : Nat) (value : A)
  | branch (pivot : Nat) (left right : LookupTree A)

def treeLookup {A : Type} (tree : LookupTree A) (i : Nat) (fallback : A) : A :=
  match tree with
  | .empty => fallback
  | .leaf index value => if i == index then value else fallback
  | .branch pivot left right =>
    if Nat.blt i pivot then treeLookup left i fallback else treeLookup right i fallback

/- The unchanged projection law is prepended by the assembly step. A finite
   native encoding keeps complete emissions of every removed/anchor origin.
   Unrelated origins remain an arbitrary function. -/
structure Database where
  knownCount : Nat
  rowCount : Nat
  keyCount : Nat
  rows : Nat → List Nat
  rowOf : Nat → Projection
  codeOf : Nat → Nat
  keyOf : Nat → Projection

def RowValid (db : Database) (i : Nat) : Prop :=
  i < db.rowCount ∧ db.codeOf i < db.keyCount ∧
    canonicalProjection (db.rowOf i) = db.keyOf (db.codeOf i)

instance (db : Database) (i : Nat) : Decidable (RowValid db i) := by
  unfold RowValid
  infer_instance

def rowCheck (db : Database) (i : Nat) : Bool :=
  Nat.blt i db.rowCount && Nat.blt (db.codeOf i) db.keyCount &&
    canonicalProjection (db.rowOf i) == db.keyOf (db.codeOf i)

theorem row_check_sound (db : Database) (i : Nat) (h : rowCheck db i = true) :
    RowValid db i := by
  simpa [rowCheck, RowValid, and_assoc] using h

def rowsChecked (db : Database) : Bool :=
  (List.range db.knownCount).all fun edge =>
    (db.rows edge).all (rowCheck db)

theorem checked_row (db : Database) (checked : rowsChecked db = true)
    (edge row : Nat) (edgeKnown : edge < db.knownCount) (member : row ∈ db.rows edge) :
    RowValid db row := by
  have allRows := (List.all_eq_true.mp checked) edge (List.mem_range.mpr edgeKnown)
  exact row_check_sound db row ((List.all_eq_true.mp allRows) row member)

structure Witness where
  sourceRow : Nat
  anchor : Nat
  anchorRow : Nat
  deriving DecidableEq, Repr

structure Certificate where
  target : Nat
  witnesses : List Witness
  deriving DecidableEq, Repr

def WitnessValid (db : Database) (cut : Nat) (w : Witness) : Prop :=
  cut ≤ w.anchor ∧ w.anchor < db.knownCount ∧
    w.anchorRow ∈ db.rows w.anchor ∧ db.codeOf w.sourceRow = db.codeOf w.anchorRow

instance (db : Database) (cut : Nat) (w : Witness) : Decidable (WitnessValid db cut w) := by
  unfold WitnessValid
  infer_instance

def witnessCheck (db : Database) (cut : Nat) (w : Witness) : Bool :=
  Nat.ble cut w.anchor && Nat.blt w.anchor db.knownCount &&
    (db.rows w.anchor).contains w.anchorRow && db.codeOf w.sourceRow == db.codeOf w.anchorRow

theorem witness_check_sound (db : Database) (cut : Nat) (w : Witness)
    (h : witnessCheck db cut w = true) : WitnessValid db cut w := by
  simpa [witnessCheck, WitnessValid, and_assoc] using h

def CertificateValid (db : Database) (cut : Nat) (c : Certificate) : Prop :=
  c.target < cut ∧
    (db.rows c.target).all (fun row => c.witnesses.any (fun w => w.sourceRow == row)) = true ∧
    ∀ w ∈ c.witnesses, WitnessValid db cut w

def certificateCheck (db : Database) (cut : Nat) (c : Certificate) : Bool :=
  Nat.blt c.target cut &&
    (db.rows c.target).all (fun row => c.witnesses.any (fun w => w.sourceRow == row)) &&
    c.witnesses.all (witnessCheck db cut)

theorem certificate_check_sound (db : Database) (cut : Nat) (c : Certificate)
    (h : certificateCheck db cut c = true) : CertificateValid db cut c := by
  simp only [certificateCheck, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1, h.1.2, fun w hw =>
    witness_check_sound db cut w ((List.all_eq_true.mp h.2) w hw)⟩

def certificatesChecked (db : Database) (cut : Nat) (certs : List Certificate) : Bool :=
  certs.all (certificateCheck db cut)

theorem checked_certificate (db : Database) (cut : Nat) (certs : List Certificate)
    (checked : certificatesChecked db cut certs = true)
    (c : Certificate) (member : c ∈ certs) : CertificateValid db cut c := by
  exact certificate_check_sound db cut c ((List.all_eq_true.mp checked) c member)

theorem complete_target (certs : List Certificate) (cut : Nat)
    (complete : certs.map Certificate.target = List.range cut) (edge : Nat) (removed : edge < cut) :
    ∃ c ∈ certs, c.target = edge := by
  have member : edge ∈ certs.map Certificate.target := by
    rw [complete]
    exact List.mem_range.mpr removed
  exact List.mem_map.mp member

def emissions (db : Database) (rest : Nat → List Projection) (edge : Nat) : List Projection :=
  if edge < db.knownCount then (db.rows edge).map db.rowOf else rest edge

def remove (cut edge : Nat) : Bool := decide (edge < cut)

theorem anchor_retained (cut anchor : Nat) (keep : cut ≤ anchor) : remove cut anchor = false := by
  simp [remove, Nat.not_lt_of_ge keep]

theorem equal_codes_equal_canonical (db : Database) (i j : Nat)
    (hi : RowValid db i) (hj : RowValid db j) (same : db.codeOf i = db.codeOf j) :
    canonicalProjection (db.rowOf i) = canonicalProjection (db.rowOf j) :=
  hi.2.2.trans ((congrArg db.keyOf same).trans hj.2.2.symm)

theorem checked_joint_anchors (db : Database) (cut total : Nat) (certs : List Certificate)
    (cutBound : cut ≤ db.knownCount) (knownBound : db.knownCount ≤ total)
    (rowChecks : rowsChecked db = true)
    (certChecks : certificatesChecked db cut certs = true)
    (complete : certs.map Certificate.target = List.range cut)
    (rest : Nat → List Projection) :
    Anchored (emissions db rest) (List.range total) (remove cut) := by
  intro edge _ dropped p hp
  have removed : edge < cut := of_decide_eq_true dropped
  have edgeKnown : edge < db.knownCount := Nat.lt_of_lt_of_le removed cutBound
  obtain ⟨c, hc, target⟩ := complete_target certs cut complete edge removed
  have valid := checked_certificate db cut certs certChecks c hc
  have covered := valid.2.1
  rw [target] at covered
  simp only [emissions, if_pos edgeKnown, List.mem_map] at hp
  obtain ⟨row, hr, sameRow⟩ := hp
  subst p
  have coveredRow := (List.all_eq_true.mp covered) row hr
  obtain ⟨w, hw, hwRow⟩ := List.any_eq_true.mp coveredRow
  have sourceRow : w.sourceRow = row := beq_iff_eq.mp hwRow
  have witnessValid : WitnessValid db cut w := valid.2.2 w hw
  have sourceValid := checked_row db rowChecks edge row edgeKnown hr
  have anchorValid := checked_row db rowChecks w.anchor w.anchorRow
    witnessValid.2.1 witnessValid.2.2.1
  have codeEq : db.codeOf row = db.codeOf w.anchorRow := by
    simpa only [sourceRow] using witnessValid.2.2.2
  refine ⟨w.anchor, List.mem_range.mpr (Nat.lt_of_lt_of_le witnessValid.2.1 knownBound),
    anchor_retained cut w.anchor witnessValid.1, db.rowOf w.anchorRow, ?_,
    equal_codes_equal_canonical db row w.anchorRow sourceValid anchorValid codeEq⟩
  simp only [emissions, if_pos witnessValid.2.1, List.mem_map]
  exact ⟨w.anchorRow, witnessValid.2.2.1, rfl⟩

theorem checked_native_oracles {Added Initial M Result : Type}
    [DecidableEq Initial] [DecidableEq Result]
    (db : Database) (cut total : Nat) (certs : List Certificate)
    (cutBound : cut ≤ db.knownCount) (knownBound : db.knownCount ≤ total)
    (rowChecks : rowsChecked db = true)
    (certChecks : certificatesChecked db cut certs = true)
    (complete : certs.map Certificate.target = List.range cut)
    (admit : Pattern → Added → List Initial) (accept : Pattern → Initial → Bool)
    (collapse : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (other : Nat → Request Added Initial M → List (Atom Initial Result))
    (rest : Nat → List Projection) :
    oracle (emissions db rest) (projectionReply admit accept collapse global counted other)
      (List.range total) =
    oracle (emissions db rest) (projectionReply admit accept collapse global counted other)
      (retained (List.range total) (remove cut)) :=
  anchored_oracles_equal _ _
    (equivalent_projection_all_replies admit accept collapse global counted other)
    _ _ (checked_joint_anchors db cut total certs cutBound knownBound rowChecks certChecks complete rest)

theorem checked_all_future_iterations {Added Initial M Result State : Type}
    [DecidableEq Initial] [DecidableEq Result]
    (db : Database) (cut total : Nat) (certs : List Certificate)
    (cutBound : cut ≤ db.knownCount) (knownBound : db.knownCount ≤ total)
    (rowChecks : rowsChecked db = true)
    (certChecks : certificatesChecked db cut certs = true)
    (complete : certs.map Certificate.target = List.range cut)
    (admit : Pattern → Added → List Initial) (accept : Pattern → Initial → Bool)
    (collapse : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (other : Nat → Request Added Initial M → List (Atom Initial Result))
    (rest : Nat → List Projection)
    (step : (Request Added Initial M → Atom Initial Result → Bool) → State → State)
    (n : Nat) (initial : State) :
    iterate step (oracle (emissions db rest)
      (projectionReply admit accept collapse global counted other) (List.range total)) n initial =
    iterate step (oracle (emissions db rest)
      (projectionReply admit accept collapse global counted other)
      (retained (List.range total) (remove cut))) n initial :=
  unchanged_transition_all_iterations step _ _
    (checked_native_oracles db cut total certs cutBound knownBound rowChecks certChecks complete
      admit accept collapse global counted other rest) n initial

end RetainedQueryBasis

#print axioms RetainedQueryBasis.row_check_sound
#print axioms RetainedQueryBasis.witness_check_sound
#print axioms RetainedQueryBasis.certificate_check_sound
#print axioms RetainedQueryBasis.checked_row
#print axioms RetainedQueryBasis.checked_certificate
#print axioms RetainedQueryBasis.complete_target
#print axioms RetainedQueryBasis.anchor_retained
#print axioms RetainedQueryBasis.equal_codes_equal_canonical
#print axioms RetainedQueryBasis.checked_joint_anchors
#print axioms RetainedQueryBasis.checked_native_oracles
#print axioms RetainedQueryBasis.checked_all_future_iterations
