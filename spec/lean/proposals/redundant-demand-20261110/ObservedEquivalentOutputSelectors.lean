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

namespace EquivalentOutputSelectors.Observed
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
def row_680 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 1, ⟨0, [0, 1], .may, (.concrete 0), []⟩, ⟨1, [2], .star, (.concrete 0), []⟩⟩
def row_904 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [3], .star, (.flow []), []⟩⟩
def row_1864 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 3, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_3716 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [5], .star, (.flow []), []⟩⟩
def row_4631 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [6], .star, (.flow []), []⟩⟩
def row_5025 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [], .may, (.flow []), []⟩, ⟨7, [2], .star, (.flow []), []⟩⟩
def row_5274 : Projection := Projection.data ⟨⟨5, 2, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [2], .star, (.flow []), []⟩⟩
def row_5938 : Projection := Projection.data ⟨⟨6, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [6], .star, (.flow []), []⟩⟩
def row_6387 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 3, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_6621 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [9], .star, (.concrete 0), []⟩⟩
def row_7231 : Projection := Projection.data ⟨⟨8, 0, 4, 7⟩, 8, ⟨8, [0, 1], .may, (.flow []), []⟩, ⟨9, [2], .star, (.flow []), []⟩⟩
def row_7353 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.flow []), []⟩, ⟨4, [2, 11], .star, (.flow []), []⟩⟩
def row_8146 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .star, (.concrete 0), []⟩⟩
def row_8375 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [2], .star, (.flow []), []⟩⟩
def row_9991 : Projection := Projection.data ⟨⟨6, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [12], .star, (.flow []), []⟩⟩
def row_11788 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨2, [13], .may, (.concrete 0), []⟩, ⟨4, [13], .star, (.concrete 0), []⟩⟩
def row_11843 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.flow []), []⟩, ⟨3, [14], .star, (.flow []), []⟩⟩
def row_13304 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨3, [15], .star, (.concrete 0), []⟩⟩
def row_13327 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 3, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_13855 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 9, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_16090 : Projection := Projection.data ⟨⟨12, 1, 1, 2⟩, 2, ⟨4, [4], .may, (.flow []), []⟩, ⟨4, [], .star, (.flow []), []⟩⟩
def row_16301 : Projection := Projection.data ⟨⟨13, 1, 1, 2⟩, 2, ⟨2, [0], .may, (.concrete 0), []⟩, ⟨4, [0], .star, (.concrete 0), []⟩⟩
def row_16951 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨3, [9], .star, (.concrete 0), []⟩⟩
def row_17305 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 9, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_17452 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [16], .may, (.concrete 0), []⟩, ⟨4, [2], .star, (.concrete 0), []⟩⟩
def row_18863 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 6, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_19276 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨3, [14], .star, (.flow []), []⟩⟩
def row_19427 : Projection := Projection.data ⟨⟨15, 1, 1, 2⟩, 2, ⟨2, [], .may, (.concrete 0), []⟩, ⟨4, [6], .star, (.concrete 0), []⟩⟩
def row_19618 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [16], .may, (.concrete 0), []⟩, ⟨7, [2], .star, (.concrete 0), []⟩⟩
def row_19940 : Projection := Projection.data ⟨⟨2, 1, 1, 2⟩, 2, ⟨2, [4], .may, (.flow []), []⟩, ⟨4, [], .star, (.flow []), []⟩⟩
def row_20063 : Projection := Projection.data ⟨⟨8, 0, 4, 7⟩, 7, ⟨8, [0, 1], .may, (.flow []), []⟩, ⟨9, [2], .star, (.flow []), []⟩⟩
def row_20325 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 9, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_20410 : Projection := Projection.data ⟨⟨16, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨4, [17, 2], .star, (.concrete 0), []⟩⟩
def row_21185 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.concrete 0), []⟩, ⟨4, [2], .star, (.concrete 0), []⟩⟩
def row_21265 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [19], .star, (.flow []), []⟩⟩
def row_22851 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [16], .may, (.concrete 0), []⟩, ⟨7, [2], .star, (.concrete 0), []⟩⟩
def row_23231 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [18], .may, (.concrete 0), []⟩, ⟨7, [2], .star, (.concrete 0), []⟩⟩
def row_24157 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨3, [14], .star, (.concrete 0), []⟩⟩
def row_25317 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨7, [2], .star, (.concrete 0), []⟩⟩
def row_26478 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.concrete 0), []⟩, ⟨4, [2], .star, (.concrete 0), []⟩⟩
def row_26816 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 6, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_26977 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 6, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_27736 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.concrete 0), []⟩, ⟨4, [2], .star, (.concrete 0), []⟩⟩
def row_28039 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [18], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .star, (.concrete 0), []⟩⟩
def row_28474 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨2, [10], .may, (.concrete 0), []⟩, ⟨4, [2], .star, (.concrete 0), []⟩⟩
def row_29011 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [15], .star, (.concrete 0), []⟩⟩
def row_29519 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 6, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_29527 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 6, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_30254 : Projection := Projection.data ⟨⟨17, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [6], .star, (.flow []), []⟩⟩
def row_31016 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨4, [], .may, (.flow []), []⟩, ⟨4, [2], .star, (.flow []), []⟩⟩
def row_31066 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [18], .may, (.concrete 0), []⟩, ⟨7, [2], .star, (.concrete 0), []⟩⟩
def row_31428 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [20], .star, (.flow []), []⟩⟩
def row_32142 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 3, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_32191 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [], .may, (.flow []), []⟩, ⟨7, [2], .star, (.flow []), []⟩⟩
def row_32282 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨7, [2], .star, (.concrete 0), []⟩⟩
def row_32511 : Projection := Projection.data ⟨⟨8, 0, 5, 12⟩, 13, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨9, [2], .star, (.flow []), []⟩⟩
def row_33207 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 9, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_33343 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 0, ⟨0, [0, 1], .may, (.flow []), []⟩, ⟨1, [2], .star, (.flow []), []⟩⟩
def row_35059 : Projection := Projection.data ⟨⟨18, 1, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [6], .star, (.flow []), []⟩⟩
def row_35751 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [15], .star, (.concrete 0), []⟩⟩
def row_36230 : Projection := Projection.data ⟨⟨2, 1, 1, 2⟩, 2, ⟨2, [7], .may, (.flow []), []⟩, ⟨4, [], .star, (.flow []), []⟩⟩
def row_37662 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [21], .star, (.flow []), []⟩⟩
def row_38646 : Projection := Projection.data ⟨⟨16, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [17, 2], .star, (.flow []), []⟩⟩
def row_38713 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.flow []), []⟩, ⟨3, [14], .star, (.flow []), []⟩⟩
def row_38885 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.concrete 0), []⟩, ⟨4, [2], .star, (.concrete 0), []⟩⟩
def row_39034 : Projection := Projection.data ⟨⟨12, 1, 1, 2⟩, 2, ⟨2, [4], .may, (.flow []), []⟩, ⟨4, [], .star, (.flow []), []⟩⟩
def row_39743 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [16], .may, (.flow []), []⟩, ⟨4, [2, 11], .star, (.flow []), []⟩⟩
def row_41999 : Projection := Projection.data ⟨⟨0, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [17, 2], .star, (.flow []), []⟩⟩
def row_42186 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [], .may, (.flow []), []⟩, ⟨7, [2], .star, (.flow []), []⟩⟩
def row_42347 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨4, [13], .may, (.concrete 0), []⟩, ⟨4, [13], .star, (.concrete 0), []⟩⟩
def row_42425 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨4, [2], .star, (.concrete 0), []⟩⟩
def row_43130 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [18], .may, (.concrete 0), []⟩, ⟨7, [2], .star, (.concrete 0), []⟩⟩
def row_43622 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 3, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_44230 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [16], .may, (.flow []), []⟩, ⟨4, [2, 11], .star, (.flow []), []⟩⟩
def row_44429 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.flow []), []⟩, ⟨4, [2, 11], .star, (.flow []), []⟩⟩
def row_44570 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [10], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .star, (.concrete 0), []⟩⟩
def row_44593 : Projection := Projection.data ⟨⟨12, 1, 1, 2⟩, 2, ⟨2, [7], .may, (.flow []), []⟩, ⟨4, [], .star, (.flow []), []⟩⟩
def row_45030 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [10], .may, (.flow []), []⟩, ⟨4, [2, 11], .star, (.flow []), []⟩⟩
def row_47215 : Projection := Projection.data ⟨⟨19, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨4, [17, 2], .star, (.concrete 0), []⟩⟩
def row_47941 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 3, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_47991 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨2, [18], .may, (.concrete 0), []⟩, ⟨4, [2], .star, (.concrete 0), []⟩⟩
def row_48469 : Projection := Projection.data ⟨⟨20, 2, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [2], .star, (.flow []), []⟩⟩
def row_49210 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 1, ⟨0, [0, 1], .may, (.flow []), []⟩, ⟨1, [2], .star, (.flow []), []⟩⟩
def row_50797 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 6, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_51145 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨7, [2], .star, (.concrete 0), []⟩⟩
def row_51955 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [18], .may, (.flow []), []⟩, ⟨4, [2, 11], .star, (.flow []), []⟩⟩
def row_52109 : Projection := Projection.data ⟨⟨15, 1, 1, 2⟩, 2, ⟨2, [], .may, (.concrete 0), []⟩, ⟨4, [12], .star, (.concrete 0), []⟩⟩
def row_52445 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 0, ⟨0, [0, 1], .may, (.concrete 0), []⟩, ⟨1, [2], .star, (.concrete 0), []⟩⟩
def row_52496 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 9, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_54844 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 9, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_56272 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 9, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_57253 : Projection := Projection.data ⟨⟨0, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [22, 14], .star, (.flow []), []⟩⟩
def row_58746 : Projection := Projection.data ⟨⟨13, 1, 1, 2⟩, 2, ⟨4, [], .may, (.concrete 0), []⟩, ⟨4, [0], .star, (.concrete 0), []⟩⟩
def row_58982 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [2], .star, (.flow []), []⟩⟩
def row_59126 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 6, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_59277 : Projection := Projection.data ⟨⟨0, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.flow []), []⟩, ⟨4, [22, 14], .star, (.flow []), []⟩⟩
def row_59922 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [14], .star, (.concrete 0), []⟩⟩
def row_60809 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [23], .star, (.flow []), []⟩⟩
def row_61159 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [24], .star, (.flow []), []⟩⟩
def row_61441 : Projection := Projection.data ⟨⟨2, 1, 1, 2⟩, 2, ⟨4, [4], .may, (.flow []), []⟩, ⟨4, [], .star, (.flow []), []⟩⟩
def row_62146 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 3, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_62487 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [], .may, (.flow []), []⟩, ⟨4, [2], .star, (.flow []), []⟩⟩
def row_62769 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 9, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_62988 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 6, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_63167 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 3, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .star, (.flow []), []⟩⟩
def row_63762 : Projection := Projection.data ⟨⟨2, 1, 1, 2⟩, 2, ⟨4, [7], .may, (.flow []), []⟩, ⟨4, [], .star, (.flow []), []⟩⟩
def row_65222 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [2], .star, (.flow []), []⟩⟩
def row_65713 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [9], .star, (.concrete 0), []⟩⟩
def row_65962 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [16], .may, (.concrete 0), []⟩, ⟨7, [2], .star, (.concrete 0), []⟩⟩
def row_65964 : Projection := Projection.data ⟨⟨8, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [17, 2], .star, (.flow []), []⟩⟩
def row_66086 : Projection := Projection.data ⟨⟨19, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [17, 2], .star, (.flow []), []⟩⟩
def row_66545 : Projection := Projection.data ⟨⟨0, 0, 6, 12⟩, 14, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨1, [2], .star, (.flow []), []⟩⟩
def row_67165 : Projection := Projection.data ⟨⟨21, 0, 1, 2⟩, 2, ⟨4, [], .may, (.flow []), []⟩, ⟨4, [2], .star, (.flow []), []⟩⟩
def row_67368 : Projection := Projection.data ⟨⟨21, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [2], .star, (.flow []), []⟩⟩
def row_67426 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .star, (.concrete 0), []⟩⟩
def row_67494 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨3, [14], .star, (.flow []), []⟩⟩
def row_68059 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [18], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_68114 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 9, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_68123 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_68384 : Projection := Projection.data ⟨⟨17, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [6], .may, (.flow []), []⟩⟩
def row_68412 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [16], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_68518 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 9, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_68840 : Projection := Projection.data ⟨⟨16, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨4, [17, 2], .may, (.concrete 0), []⟩⟩
def row_69211 : Projection := Projection.data ⟨⟨2, 1, 1, 2⟩, 2, ⟨2, [4], .may, (.flow []), []⟩, ⟨4, [], .may, (.flow []), []⟩⟩
def row_69421 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.flow []), []⟩, ⟨3, [14], .may, (.flow []), []⟩⟩
def row_69449 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .may, (.concrete 0), []⟩⟩
def row_69768 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [18], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_69887 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_70202 : Projection := Projection.data ⟨⟨0, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.flow []), []⟩, ⟨4, [22, 14], .may, (.flow []), []⟩⟩
def row_70234 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨2, [10], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_70351 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [16], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_70686 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 9, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_70772 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 6, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_70932 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [23], .may, (.flow []), []⟩⟩
def row_71500 : Projection := Projection.data ⟨⟨2, 1, 1, 2⟩, 2, ⟨2, [7], .may, (.flow []), []⟩, ⟨4, [], .may, (.flow []), []⟩⟩
def row_71723 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [19], .may, (.flow []), []⟩⟩
def row_72024 : Projection := Projection.data ⟨⟨13, 1, 1, 2⟩, 2, ⟨4, [], .may, (.concrete 0), []⟩, ⟨4, [0], .may, (.concrete 0), []⟩⟩
def row_72028 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 9, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_72046 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_72090 : Projection := Projection.data ⟨⟨0, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [22, 14], .may, (.flow []), []⟩⟩
def row_72109 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 9, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_72195 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 9, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_72236 : Projection := Projection.data ⟨⟨8, 0, 5, 12⟩, 13, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨9, [2], .may, (.flow []), []⟩⟩
def row_72362 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [10], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .may, (.concrete 0), []⟩⟩
def row_72372 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 3, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_72535 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 6, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_72544 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [21], .may, (.flow []), []⟩⟩
def row_72816 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_73352 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨4, [], .may, (.flow []), []⟩, ⟨4, [2], .may, (.flow []), []⟩⟩
def row_73525 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_73628 : Projection := Projection.data ⟨⟨15, 1, 1, 2⟩, 2, ⟨2, [], .may, (.concrete 0), []⟩, ⟨4, [6], .may, (.concrete 0), []⟩⟩
def row_73711 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨2, [18], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_73722 : Projection := Projection.data ⟨⟨0, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [17, 2], .may, (.flow []), []⟩⟩
def row_73728 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨3, [14], .may, (.concrete 0), []⟩⟩
def row_73772 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [15], .may, (.concrete 0), []⟩⟩
def row_73874 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨3, [15], .may, (.concrete 0), []⟩⟩
def row_74115 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [16], .may, (.flow []), []⟩, ⟨4, [2, 11], .may, (.flow []), []⟩⟩
def row_74199 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [], .may, (.flow []), []⟩, ⟨7, [2], .may, (.flow []), []⟩⟩
def row_74267 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [], .may, (.flow []), []⟩, ⟨4, [2], .may, (.flow []), []⟩⟩
def row_74336 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 9, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_74338 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨3, [15], .may, (.concrete 0), []⟩⟩
def row_74412 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨2, [13], .may, (.concrete 0), []⟩, ⟨4, [13], .may, (.concrete 0), []⟩⟩
def row_74452 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 1, ⟨0, [0, 1], .may, (.concrete 0), []⟩, ⟨1, [2], .may, (.concrete 0), []⟩⟩
def row_74783 : Projection := Projection.data ⟨⟨8, 0, 4, 7⟩, 8, ⟨8, [0, 1], .may, (.flow []), []⟩, ⟨9, [2], .may, (.flow []), []⟩⟩
def row_75913 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.flow []), []⟩, ⟨4, [2, 11], .may, (.flow []), []⟩⟩
def row_76097 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 3, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_76126 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 3, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_76196 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 3, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_76205 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 6, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_76242 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [9], .may, (.concrete 0), []⟩⟩
def row_76435 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 3, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_76439 : Projection := Projection.data ⟨⟨15, 1, 1, 2⟩, 2, ⟨2, [], .may, (.concrete 0), []⟩, ⟨4, [12], .may, (.concrete 0), []⟩⟩
def row_76731 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_76818 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_77280 : Projection := Projection.data ⟨⟨6, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [6], .may, (.flow []), []⟩⟩
def row_77357 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_77408 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [24], .may, (.flow []), []⟩⟩
def row_77543 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [3], .may, (.flow []), []⟩⟩
def row_77563 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 6, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_77672 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_78373 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 0, ⟨0, [0, 1], .may, (.concrete 0), []⟩, ⟨1, [2], .may, (.concrete 0), []⟩⟩
def row_78432 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨3, [9], .may, (.concrete 0), []⟩⟩
def row_78899 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨3, [14], .may, (.concrete 0), []⟩⟩
def row_79081 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 6, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_79520 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 6, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_79634 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [18], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_79930 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .may, (.concrete 0), []⟩⟩
def row_80103 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [20], .may, (.flow []), []⟩⟩
def row_80130 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [9], .may, (.concrete 0), []⟩⟩
def row_80349 : Projection := Projection.data ⟨⟨12, 1, 1, 2⟩, 2, ⟨2, [4], .may, (.flow []), []⟩, ⟨4, [], .may, (.flow []), []⟩⟩
def row_80431 : Projection := Projection.data ⟨⟨3, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [6], .may, (.flow []), []⟩⟩
def row_80447 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨4, [10], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_80558 : Projection := Projection.data ⟨⟨20, 2, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [2], .may, (.flow []), []⟩⟩
def row_81386 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨2, [10], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_81660 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [15], .may, (.concrete 0), []⟩⟩
def row_81696 : Projection := Projection.data ⟨⟨19, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨4, [17, 2], .may, (.concrete 0), []⟩⟩
def row_82052 : Projection := Projection.data ⟨⟨15, 1, 1, 2⟩, 2, ⟨2, [], .may, (.concrete 0), []⟩, ⟨4, [12], .may, (.concrete 0), []⟩⟩
def row_82308 : Projection := Projection.data ⟨⟨0, 0, 6, 12⟩, 14, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨1, [2], .may, (.flow []), []⟩⟩
def row_82343 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_82627 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [16], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_82705 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 9, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_83146 : Projection := Projection.data ⟨⟨13, 1, 1, 2⟩, 2, ⟨2, [0], .may, (.concrete 0), []⟩, ⟨4, [0], .may, (.concrete 0), []⟩⟩
def row_83389 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [18], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .may, (.concrete 0), []⟩⟩
def row_83518 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [2], .may, (.flow []), []⟩⟩
def row_83606 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 1, ⟨0, [0, 1], .may, (.flow []), []⟩, ⟨1, [2], .may, (.flow []), []⟩⟩
def row_83713 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [], .may, (.flow []), []⟩, ⟨7, [2], .may, (.flow []), []⟩⟩
def row_83726 : Projection := Projection.data ⟨⟨12, 1, 1, 2⟩, 2, ⟨4, [4], .may, (.flow []), []⟩, ⟨4, [], .may, (.flow []), []⟩⟩
def row_83840 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .may, (.concrete 0), []⟩⟩
def row_83962 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨4, [13], .may, (.concrete 0), []⟩, ⟨4, [13], .may, (.concrete 0), []⟩⟩
def row_84157 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨2, [18], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_84246 : Projection := Projection.data ⟨⟨19, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨4, [17, 2], .may, (.concrete 0), []⟩⟩
def row_84271 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [18], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_84404 : Projection := Projection.data ⟨⟨16, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [17, 2], .may, (.flow []), []⟩⟩
def row_84461 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [14], .may, (.concrete 0), []⟩⟩
def row_84835 : Projection := Projection.data ⟨⟨12, 1, 1, 2⟩, 2, ⟨2, [7], .may, (.flow []), []⟩, ⟨4, [], .may, (.flow []), []⟩⟩
def row_84970 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 3, ⟨5, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_85038 : Projection := Projection.data ⟨⟨13, 1, 1, 2⟩, 2, ⟨2, [0], .may, (.concrete 0), []⟩, ⟨4, [0], .may, (.concrete 0), []⟩⟩
def row_85117 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 6, ⟨5, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_85196 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨3, [14], .may, (.flow []), []⟩⟩
def row_85304 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨3, [14], .may, (.flow []), []⟩⟩
def row_85752 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [16], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_85956 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.flow []), []⟩, ⟨4, [2, 11], .may, (.flow []), []⟩⟩
def row_85994 : Projection := Projection.data ⟨⟨1, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨3, [5], .may, (.flow []), []⟩⟩
def row_86134 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_86267 : Projection := Projection.data ⟨⟨10, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_86305 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [15], .may, (.concrete 0), []⟩⟩
def row_86551 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_87057 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 1, ⟨0, [0, 1], .may, (.concrete 0), []⟩, ⟨1, [2], .may, (.concrete 0), []⟩⟩
def row_87165 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .may, (.concrete 0), []⟩⟩
def row_87174 : Projection := Projection.data ⟨⟨21, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [2], .may, (.flow []), []⟩⟩
def row_87331 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [16], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_87451 : Projection := Projection.data ⟨⟨21, 0, 1, 2⟩, 2, ⟨4, [], .may, (.flow []), []⟩, ⟨4, [2], .may, (.flow []), []⟩⟩
def row_87475 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [18], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_87483 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨4, [16], .may, (.flow []), []⟩, ⟨4, [2, 11], .may, (.flow []), []⟩⟩
def row_87509 : Projection := Projection.data ⟨⟨2, 1, 1, 2⟩, 2, ⟨4, [4], .may, (.flow []), []⟩, ⟨4, [], .may, (.flow []), []⟩⟩
def row_87513 : Projection := Projection.data ⟨⟨16, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨4, [17, 2], .may, (.concrete 0), []⟩⟩
def row_87527 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.concrete 0), []⟩, ⟨3, [9], .may, (.concrete 0), []⟩⟩
def row_87724 : Projection := Projection.data ⟨⟨13, 1, 1, 2⟩, 2, ⟨4, [], .may, (.concrete 0), []⟩, ⟨4, [0], .may, (.concrete 0), []⟩⟩
def row_88152 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [10], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .may, (.concrete 0), []⟩⟩
def row_88322 : Projection := Projection.data ⟨⟨18, 1, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [6], .may, (.flow []), []⟩⟩
def row_88447 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [9], .may, (.concrete 0), []⟩⟩
def row_88769 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [18], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_88956 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [2], .may, (.flow []), []⟩⟩
def row_89100 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 6, ⟨4, [4], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_89126 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [], .may, (.flow []), []⟩, ⟨7, [2], .may, (.flow []), []⟩⟩
def row_89328 : Projection := Projection.data ⟨⟨14, 0, 1, 2⟩, 2, ⟨4, [16], .may, (.concrete 0), []⟩, ⟨4, [2], .may, (.concrete 0), []⟩⟩
def row_89656 : Projection := Projection.data ⟨⟨8, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [17, 2], .may, (.flow []), []⟩⟩
def row_89928 : Projection := Projection.data ⟨⟨11, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.flow []), []⟩, ⟨3, [14], .may, (.flow []), []⟩⟩
def row_90098 : Projection := Projection.data ⟨⟨6, 0, 1, 2⟩, 2, ⟨2, [], .may, (.flow []), []⟩, ⟨4, [12], .may, (.flow []), []⟩⟩
def row_90255 : Projection := Projection.data ⟨⟨19, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [17, 2], .may, (.flow []), []⟩⟩
def row_90420 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 5, ⟨6, [16], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_91156 : Projection := Projection.data ⟨⟨8, 0, 4, 7⟩, 7, ⟨8, [0, 1], .may, (.flow []), []⟩, ⟨9, [2], .may, (.flow []), []⟩⟩
def row_91243 : Projection := Projection.data ⟨⟨2, 1, 1, 2⟩, 2, ⟨4, [7], .may, (.flow []), []⟩, ⟨4, [], .may, (.flow []), []⟩⟩
def row_91356 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [18], .may, (.concrete 0), []⟩, ⟨4, [2, 11], .may, (.concrete 0), []⟩⟩
def row_91461 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [10], .may, (.flow []), []⟩, ⟨4, [2, 11], .may, (.flow []), []⟩⟩
def row_91576 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [15], .may, (.concrete 0), []⟩⟩
def row_91799 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [16], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_91890 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 0, ⟨0, [0, 1], .may, (.concrete 0), []⟩, ⟨1, [2], .may, (.concrete 0), []⟩⟩
def row_91943 : Projection := Projection.data ⟨⟨5, 2, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [2], .may, (.flow []), []⟩⟩
def row_91968 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 11, ⟨6, [10], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def row_91999 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 1], .may, (.flow []), []⟩, ⟨4, [2], .may, (.flow []), []⟩⟩
def row_92175 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [14], .may, (.concrete 0), []⟩⟩
def row_92669 : Projection := Projection.data ⟨⟨2, 1, 2, 3⟩, 3, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_92953 : Projection := Projection.data ⟨⟨9, 0, 1, 2⟩, 2, ⟨2, [18], .may, (.flow []), []⟩, ⟨4, [2, 11], .may, (.flow []), []⟩⟩
def row_93057 : Projection := Projection.data ⟨⟨15, 1, 1, 2⟩, 2, ⟨2, [], .may, (.concrete 0), []⟩, ⟨4, [6], .may, (.concrete 0), []⟩⟩
def row_93095 : Projection := Projection.data ⟨⟨0, 0, 0, 0⟩, 0, ⟨0, [0, 1], .may, (.flow []), []⟩, ⟨1, [2], .may, (.flow []), []⟩⟩
def row_93240 : Projection := Projection.data ⟨⟨2, 1, 2, 6⟩, 3, ⟨4, [7], .may, (.flow []), []⟩, ⟨5, [], .may, (.flow []), []⟩⟩
def row_93549 : Projection := Projection.data ⟨⟨7, 0, 1, 2⟩, 2, ⟨2, [0, 8], .may, (.concrete 0), []⟩, ⟨3, [9], .may, (.concrete 0), []⟩⟩
def row_93659 : Projection := Projection.data ⟨⟨4, 0, 3, 4⟩, 10, ⟨6, [18], .may, (.concrete 0), []⟩, ⟨7, [2], .may, (.concrete 0), []⟩⟩
def known : List (Nat × Projection) := [
  (680, row_680),
  (904, row_904),
  (1864, row_1864),
  (3716, row_3716),
  (4631, row_4631),
  (5025, row_5025),
  (5274, row_5274),
  (5938, row_5938),
  (6387, row_6387),
  (6621, row_6621),
  (7231, row_7231),
  (7353, row_7353),
  (8146, row_8146),
  (8375, row_8375),
  (9991, row_9991),
  (11788, row_11788),
  (11843, row_11843),
  (13304, row_13304),
  (13327, row_13327),
  (13855, row_13855),
  (16090, row_16090),
  (16301, row_16301),
  (16951, row_16951),
  (17305, row_17305),
  (17452, row_17452),
  (18863, row_18863),
  (19276, row_19276),
  (19427, row_19427),
  (19618, row_19618),
  (19940, row_19940),
  (20063, row_20063),
  (20325, row_20325),
  (20410, row_20410),
  (21185, row_21185),
  (21265, row_21265),
  (22851, row_22851),
  (23231, row_23231),
  (24157, row_24157),
  (25317, row_25317),
  (26478, row_26478),
  (26816, row_26816),
  (26977, row_26977),
  (27736, row_27736),
  (28039, row_28039),
  (28474, row_28474),
  (29011, row_29011),
  (29519, row_29519),
  (29527, row_29527),
  (30254, row_30254),
  (31016, row_31016),
  (31066, row_31066),
  (31428, row_31428),
  (32142, row_32142),
  (32191, row_32191),
  (32282, row_32282),
  (32511, row_32511),
  (33207, row_33207),
  (33343, row_33343),
  (35059, row_35059),
  (35751, row_35751),
  (36230, row_36230),
  (37662, row_37662),
  (38646, row_38646),
  (38713, row_38713),
  (38885, row_38885),
  (39034, row_39034),
  (39743, row_39743),
  (41999, row_41999),
  (42186, row_42186),
  (42347, row_42347),
  (42425, row_42425),
  (43130, row_43130),
  (43622, row_43622),
  (44230, row_44230),
  (44429, row_44429),
  (44570, row_44570),
  (44593, row_44593),
  (45030, row_45030),
  (47215, row_47215),
  (47941, row_47941),
  (47991, row_47991),
  (48469, row_48469),
  (49210, row_49210),
  (50797, row_50797),
  (51145, row_51145),
  (51955, row_51955),
  (52109, row_52109),
  (52445, row_52445),
  (52496, row_52496),
  (54844, row_54844),
  (56272, row_56272),
  (57253, row_57253),
  (58746, row_58746),
  (58982, row_58982),
  (59126, row_59126),
  (59277, row_59277),
  (59922, row_59922),
  (60809, row_60809),
  (61159, row_61159),
  (61441, row_61441),
  (62146, row_62146),
  (62487, row_62487),
  (62769, row_62769),
  (62988, row_62988),
  (63167, row_63167),
  (63762, row_63762),
  (65222, row_65222),
  (65713, row_65713),
  (65962, row_65962),
  (65964, row_65964),
  (66086, row_66086),
  (66545, row_66545),
  (67165, row_67165),
  (67368, row_67368),
  (67426, row_67426),
  (67494, row_67494),
  (68059, row_68059),
  (68114, row_68114),
  (68123, row_68123),
  (68384, row_68384),
  (68412, row_68412),
  (68518, row_68518),
  (68840, row_68840),
  (69211, row_69211),
  (69421, row_69421),
  (69449, row_69449),
  (69768, row_69768),
  (69887, row_69887),
  (70202, row_70202),
  (70234, row_70234),
  (70351, row_70351),
  (70686, row_70686),
  (70772, row_70772),
  (70932, row_70932),
  (71500, row_71500),
  (71723, row_71723),
  (72024, row_72024),
  (72028, row_72028),
  (72046, row_72046),
  (72090, row_72090),
  (72109, row_72109),
  (72195, row_72195),
  (72236, row_72236),
  (72362, row_72362),
  (72372, row_72372),
  (72535, row_72535),
  (72544, row_72544),
  (72816, row_72816),
  (73352, row_73352),
  (73525, row_73525),
  (73628, row_73628),
  (73711, row_73711),
  (73722, row_73722),
  (73728, row_73728),
  (73772, row_73772),
  (73874, row_73874),
  (74115, row_74115),
  (74199, row_74199),
  (74267, row_74267),
  (74336, row_74336),
  (74338, row_74338),
  (74412, row_74412),
  (74452, row_74452),
  (74783, row_74783),
  (75913, row_75913),
  (76097, row_76097),
  (76126, row_76126),
  (76196, row_76196),
  (76205, row_76205),
  (76242, row_76242),
  (76435, row_76435),
  (76439, row_76439),
  (76731, row_76731),
  (76818, row_76818),
  (77280, row_77280),
  (77357, row_77357),
  (77408, row_77408),
  (77543, row_77543),
  (77563, row_77563),
  (77672, row_77672),
  (78373, row_78373),
  (78432, row_78432),
  (78899, row_78899),
  (79081, row_79081),
  (79520, row_79520),
  (79634, row_79634),
  (79930, row_79930),
  (80103, row_80103),
  (80130, row_80130),
  (80349, row_80349),
  (80431, row_80431),
  (80447, row_80447),
  (80558, row_80558),
  (81386, row_81386),
  (81660, row_81660),
  (81696, row_81696),
  (82052, row_82052),
  (82308, row_82308),
  (82343, row_82343),
  (82627, row_82627),
  (82705, row_82705),
  (83146, row_83146),
  (83389, row_83389),
  (83518, row_83518),
  (83606, row_83606),
  (83713, row_83713),
  (83726, row_83726),
  (83840, row_83840),
  (83962, row_83962),
  (84157, row_84157),
  (84246, row_84246),
  (84271, row_84271),
  (84404, row_84404),
  (84461, row_84461),
  (84835, row_84835),
  (84970, row_84970),
  (85038, row_85038),
  (85117, row_85117),
  (85196, row_85196),
  (85304, row_85304),
  (85752, row_85752),
  (85956, row_85956),
  (85994, row_85994),
  (86134, row_86134),
  (86267, row_86267),
  (86305, row_86305),
  (86551, row_86551),
  (87057, row_87057),
  (87165, row_87165),
  (87174, row_87174),
  (87331, row_87331),
  (87451, row_87451),
  (87475, row_87475),
  (87483, row_87483),
  (87509, row_87509),
  (87513, row_87513),
  (87527, row_87527),
  (87724, row_87724),
  (88152, row_88152),
  (88322, row_88322),
  (88447, row_88447),
  (88769, row_88769),
  (88956, row_88956),
  (89100, row_89100),
  (89126, row_89126),
  (89328, row_89328),
  (89656, row_89656),
  (89928, row_89928),
  (90098, row_90098),
  (90255, row_90255),
  (90420, row_90420),
  (91156, row_91156),
  (91243, row_91243),
  (91356, row_91356),
  (91461, row_91461),
  (91576, row_91576),
  (91799, row_91799),
  (91890, row_91890),
  (91943, row_91943),
  (91968, row_91968),
  (91999, row_91999),
  (92175, row_92175),
  (92669, row_92669),
  (92953, row_92953),
  (93057, row_93057),
  (93095, row_93095),
  (93240, row_93240),
  (93549, row_93549),
  (93659, row_93659),
]
def certificates : List Certificate := [
  ⟨72024, 58746, row_72024, row_58746⟩,
  ⟨83146, 16301, row_83146, row_16301⟩,
  ⟨85038, 16301, row_85038, row_16301⟩,
  ⟨87724, 58746, row_87724, row_58746⟩,
  ⟨74452, 680, row_74452, row_680⟩,
  ⟨83606, 49210, row_83606, row_49210⟩,
  ⟨87057, 680, row_87057, row_680⟩,
  ⟨68840, 20410, row_68840, row_20410⟩,
  ⟨84404, 38646, row_84404, row_38646⟩,
  ⟨87513, 20410, row_87513, row_20410⟩,
  ⟨76097, 32142, row_76097, row_32142⟩,
  ⟨76196, 1864, row_76196, row_1864⟩,
  ⟨76435, 43622, row_76435, row_43622⟩,
  ⟨92669, 63167, row_92669, row_63167⟩,
  ⟨80558, 48469, row_80558, row_48469⟩,
  ⟨70772, 26816, row_70772, row_26816⟩,
  ⟨77563, 62988, row_77563, row_62988⟩,
  ⟨79081, 50797, row_79081, row_50797⟩,
  ⟨89100, 18863, row_89100, row_18863⟩,
  ⟨70202, 59277, row_70202, row_59277⟩,
  ⟨72090, 57253, row_72090, row_57253⟩,
  ⟨73722, 41999, row_73722, row_41999⟩,
  ⟨72372, 13327, row_72372, row_13327⟩,
  ⟨76126, 47941, row_76126, row_47941⟩,
  ⟨84970, 6387, row_84970, row_6387⟩,
  ⟨93240, 62146, row_93240, row_62146⟩,
  ⟨68412, 65962, row_68412, row_65962⟩,
  ⟨69887, 32282, row_69887, row_32282⟩,
  ⟨79634, 31066, row_79634, row_31066⟩,
  ⟨84271, 31066, row_84271, row_31066⟩,
  ⟨87331, 65962, row_87331, row_65962⟩,
  ⟨89126, 42186, row_89126, row_42186⟩,
  ⟨91968, 32282, row_91968, row_32282⟩,
  ⟨69449, 8146, row_69449, row_8146⟩,
  ⟨72362, 44570, row_72362, row_44570⟩,
  ⟨74115, 39743, row_74115, row_39743⟩,
  ⟨75913, 7353, row_75913, row_7353⟩,
  ⟨79930, 8146, row_79930, row_8146⟩,
  ⟨83389, 28039, row_83389, row_28039⟩,
  ⟨83840, 67426, row_83840, row_67426⟩,
  ⟨85956, 44429, row_85956, row_44429⟩,
  ⟨87165, 67426, row_87165, row_67426⟩,
  ⟨87483, 44230, row_87483, row_44230⟩,
  ⟨88152, 44570, row_88152, row_44570⟩,
  ⟨91356, 28039, row_91356, row_28039⟩,
  ⟨91461, 45030, row_91461, row_45030⟩,
  ⟨92953, 51955, row_92953, row_51955⟩,
  ⟨68114, 62769, row_68114, row_62769⟩,
  ⟨72028, 56272, row_72028, row_56272⟩,
  ⟨72109, 54844, row_72109, row_54844⟩,
  ⟨74336, 17305, row_74336, row_17305⟩,
  ⟨80349, 39034, row_80349, row_39034⟩,
  ⟨83726, 16090, row_83726, row_16090⟩,
  ⟨84835, 44593, row_84835, row_44593⟩,
  ⟨70234, 28474, row_70234, row_28474⟩,
  ⟨73352, 31016, row_73352, row_31016⟩,
  ⟨73711, 47991, row_73711, row_47991⟩,
  ⟨74412, 11788, row_74412, row_11788⟩,
  ⟨76731, 21185, row_76731, row_21185⟩,
  ⟨77357, 38885, row_77357, row_38885⟩,
  ⟨80447, 38885, row_80447, row_38885⟩,
  ⟨81386, 28474, row_81386, row_28474⟩,
  ⟨83518, 58982, row_83518, row_58982⟩,
  ⟨83962, 42347, row_83962, row_42347⟩,
  ⟨84157, 47991, row_84157, row_47991⟩,
  ⟨86267, 21185, row_86267, row_21185⟩,
  ⟨69211, 19940, row_69211, row_19940⟩,
  ⟨71500, 36230, row_71500, row_36230⟩,
  ⟨87509, 61441, row_87509, row_61441⟩,
  ⟨91243, 63762, row_91243, row_63762⟩,
  ⟨72816, 27736, row_72816, row_27736⟩,
  ⟨73525, 26478, row_73525, row_26478⟩,
  ⟨74267, 62487, row_74267, row_62487⟩,
  ⟨77672, 26478, row_77672, row_26478⟩,
  ⟨82627, 17452, row_82627, row_17452⟩,
  ⟨87475, 27736, row_87475, row_27736⟩,
  ⟨89328, 17452, row_89328, row_17452⟩,
  ⟨89656, 65964, row_89656, row_65964⟩,
  ⟨74783, 7231, row_74783, row_7231⟩,
  ⟨88322, 35059, row_88322, row_35059⟩,
  ⟨91156, 20063, row_91156, row_20063⟩,
  ⟨73628, 19427, row_73628, row_19427⟩,
  ⟨76439, 52109, row_76439, row_52109⟩,
  ⟨82052, 52109, row_82052, row_52109⟩,
  ⟨93057, 19427, row_93057, row_19427⟩,
  ⟨80431, 4631, row_80431, row_4631⟩,
  ⟨69768, 43130, row_69768, row_43130⟩,
  ⟨70351, 22851, row_70351, row_22851⟩,
  ⟨72046, 25317, row_72046, row_25317⟩,
  ⟨74199, 5025, row_74199, row_5025⟩,
  ⟨86134, 25317, row_86134, row_25317⟩,
  ⟨88769, 43130, row_88769, row_43130⟩,
  ⟨90420, 22851, row_90420, row_22851⟩,
  ⟨70932, 60809, row_70932, row_60809⟩,
  ⟨71723, 21265, row_71723, row_21265⟩,
  ⟨72544, 37662, row_72544, row_37662⟩,
  ⟨77408, 61159, row_77408, row_61159⟩,
  ⟨77543, 904, row_77543, row_904⟩,
  ⟨80103, 31428, row_80103, row_31428⟩,
  ⟨85994, 3716, row_85994, row_3716⟩,
  ⟨68123, 42425, row_68123, row_42425⟩,
  ⟨69421, 38713, row_69421, row_38713⟩,
  ⟨73728, 24157, row_73728, row_24157⟩,
  ⟨73874, 13304, row_73874, row_13304⟩,
  ⟨74338, 13304, row_74338, row_13304⟩,
  ⟨76242, 6621, row_76242, row_6621⟩,
  ⟨76818, 42425, row_76818, row_42425⟩,
  ⟨78432, 16951, row_78432, row_16951⟩,
  ⟨78899, 24157, row_78899, row_24157⟩,
  ⟨84461, 59922, row_84461, row_59922⟩,
  ⟨85304, 67494, row_85304, row_67494⟩,
  ⟨86305, 29011, row_86305, row_29011⟩,
  ⟨87527, 16951, row_87527, row_16951⟩,
  ⟨91576, 29011, row_91576, row_29011⟩,
  ⟨91999, 8375, row_91999, row_8375⟩,
  ⟨92175, 59922, row_92175, row_59922⟩,
  ⟨93549, 6621, row_93549, row_6621⟩,
  ⟨87174, 67368, row_87174, row_67368⟩,
  ⟨87451, 67165, row_87451, row_67165⟩,
  ⟨68518, 13855, row_68518, row_13855⟩,
  ⟨70686, 52496, row_70686, row_52496⟩,
  ⟨72195, 33207, row_72195, row_33207⟩,
  ⟨82705, 20325, row_82705, row_20325⟩,
  ⟨68384, 30254, row_68384, row_30254⟩,
  ⟨77280, 5938, row_77280, row_5938⟩,
  ⟨90098, 9991, row_90098, row_9991⟩,
  ⟨72535, 29519, row_72535, row_29519⟩,
  ⟨76205, 59126, row_76205, row_59126⟩,
  ⟨79520, 29527, row_79520, row_29527⟩,
  ⟨85117, 26977, row_85117, row_26977⟩,
  ⟨81696, 47215, row_81696, row_47215⟩,
  ⟨84246, 47215, row_84246, row_47215⟩,
  ⟨90255, 66086, row_90255, row_66086⟩,
  ⟨68059, 23231, row_68059, row_23231⟩,
  ⟨82343, 51145, row_82343, row_51145⟩,
  ⟨83713, 32191, row_83713, row_32191⟩,
  ⟨85752, 19618, row_85752, row_19618⟩,
  ⟨86551, 51145, row_86551, row_51145⟩,
  ⟨91799, 19618, row_91799, row_19618⟩,
  ⟨93659, 23231, row_93659, row_23231⟩,
  ⟨91943, 5274, row_91943, row_5274⟩,
  ⟨73772, 35751, row_73772, row_35751⟩,
  ⟨80130, 65713, row_80130, row_65713⟩,
  ⟨81660, 35751, row_81660, row_35751⟩,
  ⟨85196, 19276, row_85196, row_19276⟩,
  ⟨88447, 65713, row_88447, row_65713⟩,
  ⟨88956, 65222, row_88956, row_65222⟩,
  ⟨89928, 11843, row_89928, row_11843⟩,
  ⟨78373, 52445, row_78373, row_52445⟩,
  ⟨91890, 52445, row_91890, row_52445⟩,
  ⟨93095, 33343, row_93095, row_33343⟩,
  ⟨72236, 32511, row_72236, row_32511⟩,
  ⟨82308, 66545, row_82308, row_66545⟩,
]
theorem all_certificates_checked : certificates.all (check known 93663 67877) = true := by decide
theorem observed_joint_anchors (rest : Nat → List Projection) : Anchored (emits known rest) (List.range 93663) (drop certificates) :=
  checked_anchors known 93663 67877 (by decide) certificates all_certificates_checked rest

theorem observed_native_query_oracles {Added Initial M Result : Type}
    [DecidableEq Initial] [DecidableEq Result]
    (admit : Pattern → Added → List Initial) (accept : Pattern → Initial → Bool)
    (cut : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (other : Nat → Request Added Initial M → List (Atom Initial Result))
    (rest : Nat → List Projection) :
    oracle (emits known rest) (projectionReply admit accept cut global counted other)
      (List.range 93663) =
    oracle (emits known rest) (projectionReply admit accept cut global counted other)
      (retained (List.range 93663) (drop certificates)) :=
  anchored_oracles_equal (emits known rest)
    (projectionReply admit accept cut global counted other)
    (equivalent_projection_all_replies admit accept cut global counted other)
    (List.range 93663) (drop certificates) (observed_joint_anchors rest)

theorem observed_all_future_iterations {Added Initial M Result State : Type}
    [DecidableEq Initial] [DecidableEq Result]
    (admit : Pattern → Added → List Initial) (accept : Pattern → Initial → Bool)
    (cut : Nat → Conclusion M → List Result) (global : Nat) (counted : Nat → Bool)
    (other : Nat → Request Added Initial M → List (Atom Initial Result))
    (rest : Nat → List Projection)
    (step : (Request Added Initial M → Atom Initial Result → Bool) → State → State)
    (n : Nat) (initial : State) :
    iterate step (oracle (emits known rest)
      (projectionReply admit accept cut global counted other) (List.range 93663)) n initial =
    iterate step (oracle (emits known rest)
      (projectionReply admit accept cut global counted other)
      (retained (List.range 93663) (drop certificates))) n initial :=
  unchanged_transition_all_iterations step _ _
    (observed_native_query_oracles admit accept cut global counted other rest) n initial

end EquivalentOutputSelectors.Observed
#print axioms EquivalentOutputSelectors.Observed.checked
#print axioms EquivalentOutputSelectors.Observed.anchor_not_dropped
#print axioms EquivalentOutputSelectors.Observed.checked_anchors
#print axioms EquivalentOutputSelectors.Observed.all_certificates_checked
#print axioms EquivalentOutputSelectors.Observed.observed_joint_anchors
#print axioms EquivalentOutputSelectors.Observed.observed_native_query_oracles
#print axioms EquivalentOutputSelectors.Observed.observed_all_future_iterations
