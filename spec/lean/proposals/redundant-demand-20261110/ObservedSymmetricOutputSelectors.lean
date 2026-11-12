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

namespace EquivalentOutputSelectors.SymmetricObserved
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

structure Certificate where
  target : Nat
  anchor : Nat
  source : Projection
  replacement : Projection
  deriving DecidableEq, Repr

def emits (known : List (Nat × Projection)) (rest : Nat → List Projection)
    (edge : Nat) : List Projection :=
  match known.lookup edge with | some p => [p] | none => rest edge

def drop (certs : List Certificate) (edge : Nat) : Bool :=
  certs.any (fun c => c.target == edge)

def Valid (known : List (Nat × Projection)) (total cut : Nat) (c : Certificate) : Prop :=
  c.target < total ∧ cut ≤ c.target ∧ c.anchor < cut ∧
  known.lookup c.target = some c.source ∧
  known.lookup c.anchor = some c.replacement ∧
  canonicalProjection c.source = canonicalProjection c.replacement

instance (known : List (Nat × Projection)) (total cut : Nat) (c : Certificate) :
    Decidable (Valid known total cut c) := by
  unfold Valid
  infer_instance

def check (known : List (Nat × Projection)) (total cut : Nat) (c : Certificate) : Bool :=
  decide (Valid known total cut c)

theorem checked (known : List (Nat × Projection)) (total cut : Nat)
    (certs : List Certificate) (all : certs.all (check known total cut) = true)
    (c : Certificate) (hc : c ∈ certs) : Valid known total cut c := by
  exact of_decide_eq_true ((List.all_eq_true.mp all) c hc)

theorem anchor_not_dropped (known : List (Nat × Projection)) (total cut : Nat)
    (certs : List Certificate) (all : certs.all (check known total cut) = true)
    (anchor : Nat) (ha : anchor < cut) : drop certs anchor = false := by
  cases h : drop certs anchor with
  | false => rfl
  | true =>
    simp only [drop, List.any_eq_true, beq_iff_eq] at h
    rcases h with ⟨c, hc, same⟩
    have valid := checked known total cut certs all c hc
    exact False.elim ((Nat.not_le_of_lt ha) (same ▸ valid.2.1))

theorem checked_anchors (known : List (Nat × Projection)) (total cut : Nat)
    (cutBound : cut ≤ total) (certs : List Certificate)
    (all : certs.all (check known total cut) = true) (rest : Nat → List Projection) :
    Anchored (emits known rest) (List.range total) (drop certs) := by
  intro edge member removed p hp
  simp only [drop, List.any_eq_true, beq_iff_eq] at removed
  rcases removed with ⟨c, hc, same⟩
  have valid := checked known total cut certs all c hc
  rcases valid with ⟨ht, hu, ha, hs, hr, equal⟩
  subst edge
  simp only [emits, hs, List.mem_singleton] at hp
  subst p
  refine ⟨c.anchor, List.mem_range.mpr (Nat.lt_of_lt_of_le ha cutBound),
    anchor_not_dropped known total cut certs all c.anchor ha,
    c.replacement, ?_, equal⟩
  simp [emits, hr]
def row_34 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 1, ⟨0, [0], .may, (.flow []), []⟩, ⟨0, [], .may, (.flow []), []⟩⟩
def row_52 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 0, ⟨1, [0], .may, (.flow []), []⟩, ⟨0, [], .may, (.flow []), []⟩⟩
def row_56 : Projection := Projection.data ⟨⟨1, 1, 0, 0⟩, 0, ⟨0, [0], .may, (.flow []), []⟩, ⟨0, [], .may, (.flow []), []⟩⟩
def row_57 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 1, ⟨1, [0], .may, (.flow []), []⟩, ⟨0, [], .may, (.flow []), []⟩⟩
def row_62 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 0, ⟨0, [0], .may, (.flow []), []⟩, ⟨0, [], .may, (.flow []), []⟩⟩
def row_324 : Projection := Projection.data ⟨⟨2, 0, 1, 2⟩, 2, ⟨2, [1, 2, 3], .exact, (.concrete 0), []⟩, ⟨3, [4], .may, (.concrete 0), []⟩⟩
def row_2720 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [5], .exact, (.concrete 0), []⟩, ⟨1, [6, 1], .may, (.concrete 0), []⟩⟩
def row_4225 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [6], .may, (.flow []), []⟩, ⟨1, [7, 8], .may, (.flow []), []⟩⟩
def row_9517 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [7], .may, (.flow []), []⟩, ⟨1, [7, 8], .may, (.flow []), []⟩⟩
def row_11404 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [5], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .may, (.concrete 0), []⟩⟩
def row_11857 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨4, [9], .exact, (.concrete 0), []⟩, ⟨4, [10, 9], .may, (.concrete 0), []⟩⟩
def row_16377 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨4, [], .may, (.concrete 0), []⟩, ⟨4, [10, 9], .may, (.concrete 0), []⟩⟩
def row_16701 : Projection := Projection.data ⟨⟨5, 2, 3, 5⟩, 6, ⟨5, [], .may, (.flow []), []⟩, ⟨5, [10], .may, (.flow []), []⟩⟩
def row_17251 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨4, [10, 9], .may, (.concrete 0), []⟩⟩
def row_22288 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [5], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .may, (.concrete 0), []⟩⟩
def row_22646 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [11], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .may, (.concrete 0), []⟩⟩
def row_24009 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨6, [], .may, (.concrete 0), []⟩, ⟨4, [10, 12], .may, (.concrete 0), []⟩⟩
def row_24482 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [13], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .may, (.concrete 0), []⟩⟩
def row_25346 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [7], .may, (.flow []), []⟩, ⟨1, [7, 8], .may, (.flow []), []⟩⟩
def row_27189 : Projection := Projection.data ⟨⟨6, 0, 1, 2⟩, 2, ⟨2, [1, 2, 3], .exact, (.concrete 0), []⟩, ⟨3, [4], .may, (.concrete 0), []⟩⟩
def row_28264 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨4, [], .may, (.concrete 0), []⟩, ⟨4, [10, 12], .may, (.concrete 0), []⟩⟩
def row_29747 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [11], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .may, (.concrete 0), []⟩⟩
def row_29823 : Projection := Projection.data ⟨⟨5, 2, 3, 5⟩, 6, ⟨1, [], .may, (.flow []), []⟩, ⟨5, [10], .may, (.flow []), []⟩⟩
def row_33545 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨6, [9], .exact, (.concrete 0), []⟩, ⟨4, [10, 9], .may, (.concrete 0), []⟩⟩
def row_38040 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨4, [10], .may, (.flow []), []⟩, ⟨4, [10, 12], .may, (.flow []), []⟩⟩
def row_38761 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [14], .exact, (.concrete 0), []⟩, ⟨1, [7], .may, (.concrete 0), []⟩⟩
def row_39086 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [6], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .may, (.concrete 0), []⟩⟩
def row_39785 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨4, [15], .exact, (.concrete 0), []⟩, ⟨4, [10, 9], .may, (.concrete 0), []⟩⟩
def row_43567 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [5], .exact, (.concrete 0), []⟩, ⟨1, [6, 1], .may, (.concrete 0), []⟩⟩
def row_47145 : Projection := Projection.data ⟨⟨8, 0, 2, 3⟩, 4, ⟨4, [10], .may, (.flow []), []⟩, ⟨4, [10, 12], .may, (.flow []), []⟩⟩
def row_48686 : Projection := Projection.data ⟨⟨5, 2, 3, 5⟩, 6, ⟨7, [1], .may, (.flow []), []⟩, ⟨5, [10], .may, (.flow []), []⟩⟩
def row_49483 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨6, [], .may, (.concrete 0), []⟩, ⟨4, [10, 9], .may, (.concrete 0), []⟩⟩
def row_51326 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [6], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .may, (.concrete 0), []⟩⟩
def row_53296 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [11], .exact, (.concrete 0), []⟩, ⟨1, [6, 1], .may, (.concrete 0), []⟩⟩
def row_54523 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [13], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .may, (.concrete 0), []⟩⟩
def row_60587 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [14], .exact, (.concrete 0), []⟩, ⟨1, [6, 1], .may, (.concrete 0), []⟩⟩
def row_61278 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨6, [15], .exact, (.concrete 0), []⟩, ⟨4, [10, 9], .may, (.concrete 0), []⟩⟩
def row_62058 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [11], .exact, (.concrete 0), []⟩, ⟨1, [6, 1], .may, (.concrete 0), []⟩⟩
def row_63422 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [6], .may, (.flow []), []⟩, ⟨1, [7, 8], .may, (.flow []), []⟩⟩
def row_70243 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 0, ⟨0, [0], .may, (.flow []), []⟩, ⟨0, [], .star, (.flow []), []⟩⟩
def row_70399 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 0, ⟨1, [0], .may, (.flow []), []⟩, ⟨0, [], .star, (.flow []), []⟩⟩
def row_70647 : Projection := Projection.data ⟨⟨1, 1, 0, 0⟩, 0, ⟨0, [0], .may, (.flow []), []⟩, ⟨0, [], .star, (.flow []), []⟩⟩
def row_70678 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 1, ⟨0, [0], .may, (.flow []), []⟩, ⟨0, [], .star, (.flow []), []⟩⟩
def row_70734 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 1, ⟨1, [0], .may, (.flow []), []⟩, ⟨0, [], .star, (.flow []), []⟩⟩
def row_70966 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨4, [9], .exact, (.concrete 0), []⟩, ⟨4, [10, 9], .star, (.concrete 0), []⟩⟩
def row_71983 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [6], .may, (.flow []), []⟩, ⟨1, [7, 8], .star, (.flow []), []⟩⟩
def row_72572 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [14], .exact, (.concrete 0), []⟩, ⟨1, [6, 1], .star, (.concrete 0), []⟩⟩
def row_74481 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨4, [], .may, (.concrete 0), []⟩, ⟨4, [10, 12], .star, (.concrete 0), []⟩⟩
def row_74570 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [7], .may, (.flow []), []⟩, ⟨1, [7, 8], .star, (.flow []), []⟩⟩
def row_74673 : Projection := Projection.data ⟨⟨6, 0, 1, 2⟩, 2, ⟨2, [1, 2, 3], .exact, (.concrete 0), []⟩, ⟨3, [4], .star, (.concrete 0), []⟩⟩
def row_77255 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨4, [10], .may, (.flow []), []⟩, ⟨4, [10, 12], .star, (.flow []), []⟩⟩
def row_77285 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [14], .exact, (.concrete 0), []⟩, ⟨1, [7], .star, (.concrete 0), []⟩⟩
def row_77638 : Projection := Projection.data ⟨⟨2, 0, 1, 2⟩, 2, ⟨2, [1, 2, 3], .exact, (.concrete 0), []⟩, ⟨3, [4], .star, (.concrete 0), []⟩⟩
def row_78171 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [5], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .star, (.concrete 0), []⟩⟩
def row_78345 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [11], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .star, (.concrete 0), []⟩⟩
def row_79204 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [5], .exact, (.concrete 0), []⟩, ⟨1, [6, 1], .star, (.concrete 0), []⟩⟩
def row_81044 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [11], .exact, (.concrete 0), []⟩, ⟨1, [6, 1], .star, (.concrete 0), []⟩⟩
def row_82100 : Projection := Projection.data ⟨⟨5, 2, 3, 5⟩, 6, ⟨5, [], .may, (.flow []), []⟩, ⟨5, [10], .star, (.flow []), []⟩⟩
def row_82512 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [5], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .star, (.concrete 0), []⟩⟩
def row_83277 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [6], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .star, (.concrete 0), []⟩⟩
def row_83438 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨4, [10, 9], .star, (.concrete 0), []⟩⟩
def row_83924 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨4, [], .may, (.concrete 0), []⟩, ⟨4, [10, 9], .star, (.concrete 0), []⟩⟩
def row_85587 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [5], .exact, (.concrete 0), []⟩, ⟨1, [6, 1], .star, (.concrete 0), []⟩⟩
def row_85778 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [6], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .star, (.concrete 0), []⟩⟩
def row_88214 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨6, [], .may, (.concrete 0), []⟩, ⟨4, [10, 12], .star, (.concrete 0), []⟩⟩
def row_88402 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [6], .may, (.flow []), []⟩, ⟨1, [7, 8], .star, (.flow []), []⟩⟩
def row_88422 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨6, [9], .exact, (.concrete 0), []⟩, ⟨4, [10, 9], .star, (.concrete 0), []⟩⟩
def row_88521 : Projection := Projection.data ⟨⟨8, 0, 2, 3⟩, 4, ⟨4, [10], .may, (.flow []), []⟩, ⟨4, [10, 12], .star, (.flow []), []⟩⟩
def row_88841 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨6, [], .may, (.concrete 0), []⟩, ⟨4, [10, 9], .star, (.concrete 0), []⟩⟩
def row_90289 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [11], .exact, (.concrete 0), []⟩, ⟨1, [6, 1], .star, (.concrete 0), []⟩⟩
def row_91480 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨6, [15], .exact, (.concrete 0), []⟩, ⟨4, [10, 9], .star, (.concrete 0), []⟩⟩
def row_92123 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [13], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .star, (.concrete 0), []⟩⟩
def row_94254 : Projection := Projection.data ⟨⟨4, 2, 2, 3⟩, 4, ⟨4, [15], .exact, (.concrete 0), []⟩, ⟨4, [10, 9], .star, (.concrete 0), []⟩⟩
def row_94681 : Projection := Projection.data ⟨⟨5, 2, 3, 5⟩, 6, ⟨1, [], .may, (.flow []), []⟩, ⟨5, [10], .star, (.flow []), []⟩⟩
def row_94990 : Projection := Projection.data ⟨⟨5, 2, 3, 5⟩, 6, ⟨7, [1], .may, (.flow []), []⟩, ⟨5, [10], .star, (.flow []), []⟩⟩
def row_95641 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [13], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .star, (.concrete 0), []⟩⟩
def row_95851 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨1, [7], .may, (.flow []), []⟩, ⟨1, [7, 8], .star, (.flow []), []⟩⟩
def row_96135 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [11], .may, (.concrete 0), []⟩, ⟨1, [7, 8], .star, (.concrete 0), []⟩⟩
def known : List (Nat × Projection) := [
  (34, row_34),
  (52, row_52),
  (56, row_56),
  (57, row_57),
  (62, row_62),
  (324, row_324),
  (2720, row_2720),
  (4225, row_4225),
  (9517, row_9517),
  (11404, row_11404),
  (11857, row_11857),
  (16377, row_16377),
  (16701, row_16701),
  (17251, row_17251),
  (22288, row_22288),
  (22646, row_22646),
  (24009, row_24009),
  (24482, row_24482),
  (25346, row_25346),
  (27189, row_27189),
  (28264, row_28264),
  (29747, row_29747),
  (29823, row_29823),
  (33545, row_33545),
  (38040, row_38040),
  (38761, row_38761),
  (39086, row_39086),
  (39785, row_39785),
  (43567, row_43567),
  (47145, row_47145),
  (48686, row_48686),
  (49483, row_49483),
  (51326, row_51326),
  (53296, row_53296),
  (54523, row_54523),
  (60587, row_60587),
  (61278, row_61278),
  (62058, row_62058),
  (63422, row_63422),
  (70243, row_70243),
  (70399, row_70399),
  (70647, row_70647),
  (70678, row_70678),
  (70734, row_70734),
  (70966, row_70966),
  (71983, row_71983),
  (72572, row_72572),
  (74481, row_74481),
  (74570, row_74570),
  (74673, row_74673),
  (77255, row_77255),
  (77285, row_77285),
  (77638, row_77638),
  (78171, row_78171),
  (78345, row_78345),
  (79204, row_79204),
  (81044, row_81044),
  (82100, row_82100),
  (82512, row_82512),
  (83277, row_83277),
  (83438, row_83438),
  (83924, row_83924),
  (85587, row_85587),
  (85778, row_85778),
  (88214, row_88214),
  (88402, row_88402),
  (88422, row_88422),
  (88521, row_88521),
  (88841, row_88841),
  (90289, row_90289),
  (91480, row_91480),
  (92123, row_92123),
  (94254, row_94254),
  (94681, row_94681),
  (94990, row_94990),
  (95641, row_95641),
  (95851, row_95851),
  (96135, row_96135),
]
def certificates : List Certificate := [
  ⟨82100, 16701, row_82100, row_16701⟩,
  ⟨94681, 29823, row_94681, row_29823⟩,
  ⟨94990, 48686, row_94990, row_48686⟩,
  ⟨77285, 38761, row_77285, row_38761⟩,
  ⟨70966, 11857, row_70966, row_11857⟩,
  ⟨74481, 28264, row_74481, row_28264⟩,
  ⟨77255, 38040, row_77255, row_38040⟩,
  ⟨83438, 17251, row_83438, row_17251⟩,
  ⟨83924, 16377, row_83924, row_16377⟩,
  ⟨88214, 24009, row_88214, row_24009⟩,
  ⟨88422, 33545, row_88422, row_33545⟩,
  ⟨88841, 49483, row_88841, row_49483⟩,
  ⟨91480, 61278, row_91480, row_61278⟩,
  ⟨94254, 39785, row_94254, row_39785⟩,
  ⟨74673, 27189, row_74673, row_27189⟩,
  ⟨71983, 63422, row_71983, row_63422⟩,
  ⟨72572, 60587, row_72572, row_60587⟩,
  ⟨74570, 9517, row_74570, row_9517⟩,
  ⟨78171, 11404, row_78171, row_11404⟩,
  ⟨78345, 22646, row_78345, row_22646⟩,
  ⟨79204, 43567, row_79204, row_43567⟩,
  ⟨81044, 62058, row_81044, row_62058⟩,
  ⟨82512, 22288, row_82512, row_22288⟩,
  ⟨83277, 39086, row_83277, row_39086⟩,
  ⟨85587, 2720, row_85587, row_2720⟩,
  ⟨85778, 51326, row_85778, row_51326⟩,
  ⟨88402, 4225, row_88402, row_4225⟩,
  ⟨90289, 53296, row_90289, row_53296⟩,
  ⟨92123, 54523, row_92123, row_54523⟩,
  ⟨95641, 24482, row_95641, row_24482⟩,
  ⟨95851, 25346, row_95851, row_25346⟩,
  ⟨96135, 29747, row_96135, row_29747⟩,
  ⟨88521, 47145, row_88521, row_47145⟩,
  ⟨77638, 324, row_77638, row_324⟩,
  ⟨70243, 62, row_70243, row_62⟩,
  ⟨70399, 52, row_70399, row_52⟩,
  ⟨70647, 56, row_70647, row_56⟩,
  ⟨70678, 34, row_70678, row_34⟩,
  ⟨70734, 57, row_70734, row_57⟩,
]
theorem all_certificates_checked : certificates.all (check known 96575 67944) = true := by decide
theorem observed_joint_anchors (rest : Nat → List Projection) : Anchored (emits known rest) (List.range 96575) (drop certificates) :=
  checked_anchors known 96575 67944 (by decide) certificates all_certificates_checked rest

theorem observed_native_query_oracles {Added Initial M Result : Type}
    [DecidableEq Initial] [DecidableEq Result]
    (admit : Pattern → Added → List Initial) (accept : Pattern → Initial → Bool)
    (cut : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (other : Nat → Request Added Initial M → List (Atom Initial Result))
    (rest : Nat → List Projection) :
    oracle (emits known rest) (projectionReply admit accept cut global counted other)
      (List.range 96575) =
    oracle (emits known rest) (projectionReply admit accept cut global counted other)
      (retained (List.range 96575) (drop certificates)) :=
  anchored_oracles_equal (emits known rest)
    (projectionReply admit accept cut global counted other)
    (equivalent_projection_all_replies admit accept cut global counted other)
    (List.range 96575) (drop certificates) (observed_joint_anchors rest)

theorem observed_all_future_iterations {Added Initial M Result State : Type}
    [DecidableEq Initial] [DecidableEq Result]
    (admit : Pattern → Added → List Initial) (accept : Pattern → Initial → Bool)
    (cut : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (other : Nat → Request Added Initial M → List (Atom Initial Result))
    (rest : Nat → List Projection)
    (step : (Request Added Initial M → Atom Initial Result → Bool) → State → State)
    (n : Nat) (initial : State) :
    iterate step (oracle (emits known rest)
      (projectionReply admit accept cut global counted other) (List.range 96575)) n initial =
    iterate step (oracle (emits known rest)
      (projectionReply admit accept cut global counted other)
      (retained (List.range 96575) (drop certificates))) n initial :=
  unchanged_transition_all_iterations step _ _
    (observed_native_query_oracles admit accept cut global counted other rest) n initial

end EquivalentOutputSelectors.SymmetricObserved
#print axioms EquivalentOutputSelectors.SymmetricObserved.checked
#print axioms EquivalentOutputSelectors.SymmetricObserved.anchor_not_dropped
#print axioms EquivalentOutputSelectors.SymmetricObserved.checked_anchors
#print axioms EquivalentOutputSelectors.SymmetricObserved.all_certificates_checked
#print axioms EquivalentOutputSelectors.SymmetricObserved.observed_joint_anchors
#print axioms EquivalentOutputSelectors.SymmetricObserved.observed_native_query_oracles
#print axioms EquivalentOutputSelectors.SymmetricObserved.observed_all_future_iterations
