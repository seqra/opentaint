/-
  PROPOSAL ONLY. Phase-A raw writer replay, after all runner jobs join.
  The finite arcs are the complete ordinary AP binding images on the frozen
  current N2 inputs. This file does not prove that a JVM adapter builds those
  arcs or that a live publication has exhausted them. EngineClosed is the
  explicit certificate required for that optimization. No static composition
  result is fed back into this binding graph.
-/
import Init

namespace RestrictedDemandNext.WriterReplay
set_option autoImplicit false

/-- Raw equality retains mx. An actual adapter must also retain the original
    field E, tail, owner and mark pair, represented here by geometry. -/
inductive Header where
  | flow
  | marked (atom : Nat)
  deriving DecidableEq, Repr

structure RawKey where
  owner : Nat
  geometry : Nat
  inputMark : Header
  outputMark : Header
  mx : List Nat
  deriving DecidableEq, Repr

/-- Constructive membership avoids a propositional-extensionality-based
    library decider in the computational replay branch. -/
def rawMembership (key : RawKey) : (rows : List RawKey) → Decidable (key ∈ rows)
  | [] => .isFalse (fun member => nomatch member)
  | head :: rest =>
      match decEq key head with
      | .isTrue same => .isTrue (same ▸ List.Mem.head _)
      | .isFalse different =>
          match rawMembership key rest with
          | .isTrue found => .isTrue (.tail head found)
          | .isFalse absent => .isFalse (fun member =>
              match member with
              | .head _ => different rfl
              | .tail _ later => absent later)

structure Arc where
  source : RawKey
  target : RawKey
  deriving DecidableEq, Repr

/-- All data is finite: Known and the complete frozen binding-image arcs. -/
inductive FullReach (known : List RawKey) (arcs : List Arc) : RawKey → Type where
  | seed {key : RawKey} (member : key ∈ known) : FullReach known arcs key
  | bind {source target : RawKey} (prior : FullReach known arcs source)
      (image : (⟨source,target⟩ : Arc) ∈ arcs) : FullReach known arcs target

/-- SeedNeed is raw Known minus raw Exhausted, not normalized lostRows. -/
def SeedNeed (known exhausted : List RawKey) (key : RawKey) : Prop :=
  key ∈ known ∧ key ∉ exhausted

/-- Membership is retained for every Known seed. Only non-exhausted keys can
    be expanded. New bound keys are subject to the same guard. -/
inductive SparseReach (known : List RawKey) (arcs : List Arc)
    (exhausted : List RawKey) : RawKey → Type where
  | seed {key : RawKey} (member : key ∈ known) : SparseReach known arcs exhausted key
  | bind {source target : RawKey} (prior : SparseReach known arcs exhausted source)
      (expand : source ∉ exhausted) (image : (⟨source,target⟩ : Arc) ∈ arcs) :
      SparseReach known arcs exhausted target

/-- A live-publication certificate needs BOTH facts: the exact raw key was
    known, and every image on all current N2 inputs is already in Known. -/
structure ExhaustionCertificate (known : List RawKey) (arcs : List Arc)
    (exhausted : List RawKey) : Prop where
  inKnown : ∀ {key : RawKey}, key ∈ exhausted → key ∈ known
  engineClosed : ∀ {source target : RawKey}, source ∈ exhausted →
    (⟨source,target⟩ : Arc) ∈ arcs → target ∈ known

def fullToSparse {known : List RawKey} {arcs : List Arc} {exhausted : List RawKey}
    (closed : ExhaustionCertificate known arcs exhausted) {key : RawKey}
    (proof : FullReach known arcs key) : SparseReach known arcs exhausted key :=
  match proof with
  | .seed member => .seed member
  | .bind (source := source) prior image =>
      let _ : Decidable (source ∈ exhausted) := rawMembership source exhausted
      if already : source ∈ exhausted then .seed (closed.engineClosed already image)
      else .bind (fullToSparse closed prior) already image

def sparseToFull {known : List RawKey} {arcs : List Arc} {exhausted : List RawKey}
    {key : RawKey} (proof : SparseReach known arcs exhausted key) : FullReach known arcs key :=
  match proof with
  | .seed member => .seed member
  | .bind prior _ image => .bind (sparseToFull prior) image

theorem reachability_equivalent (known : List RawKey) (arcs : List Arc)
    (exhausted : List RawKey) (closed : ExhaustionCertificate known arcs exhausted)
    (key : RawKey) :
    Nonempty (FullReach known arcs key) ↔ Nonempty (SparseReach known arcs exhausted key) :=
  ⟨fun ⟨proof⟩ => ⟨fullToSparse closed proof⟩,
   fun ⟨proof⟩ => ⟨sparseToFull proof⟩⟩

/-- The scheduler can compute the seed work list without visiting a binding arc. -/
def seedQueue (known exhausted : List RawKey) : List RawKey :=
  match known with
  | [] => []
  | head :: rest =>
      match rawMembership head exhausted with
      | .isTrue _ => seedQueue rest exhausted
      | .isFalse _ => head :: seedQueue rest exhausted

theorem seed_queue_is_need {known exhausted : List RawKey} {key : RawKey}
    (member : key ∈ seedQueue known exhausted) : SeedNeed known exhausted key := by
  induction known with
  | nil => cases member
  | cons head rest later =>
      unfold seedQueue at member
      split at member
      · exact ⟨List.Mem.tail head (later member).1,(later member).2⟩
      · cases member with
        | head _ => exact ⟨List.Mem.head _,by assumption⟩
        | tail _ found => exact ⟨List.Mem.tail head (later found).1,(later found).2⟩

theorem exhausted_not_seed_work {known exhausted : List RawKey} {key : RawKey}
    (done : key ∈ exhausted) : key ∉ seedQueue known exhausted :=
  fun queued => (seed_queue_is_need queued).2 done

/-- Seen is admitted before queuing. It contains all Known seeds initially and
    every newly bound raw key thereafter. A completed key does not lose Seen. -/
structure Work where
  seen : List RawKey
  pending : List RawKey
  deriving DecidableEq, Repr

def initialWork (known exhausted : List RawKey) : Work :=
  ⟨known,seedQueue known exhausted⟩

def offer (work : Work) (key : RawKey) : Work :=
  let _ : Decidable (key ∈ work.seen) := rawMembership key work.seen
  if key ∈ work.seen then work else ⟨key :: work.seen,key :: work.pending⟩

theorem known_not_requeued (work : Work) (key : RawKey) (seen : key ∈ work.seen) :
    offer work key = work := by
  unfold offer
  exact if_pos seen

theorem offer_once (work : Work) (key : RawKey) : offer (offer work key) key = offer work key := by
  let _ : Decidable (key ∈ work.seen) := rawMembership key work.seen
  by_cases seen : key ∈ work.seen
  · rw [known_not_requeued work key seen]
    exact known_not_requeued work key seen
  · have first : offer work key = ⟨key :: work.seen,key :: work.pending⟩ := if_neg seen
    rw [first]
    exact known_not_requeued _ key (List.Mem.head _)

theorem known_exhausted_never_requeued {known exhausted : List RawKey} {arcs : List Arc}
    (closed : ExhaustionCertificate known arcs exhausted) {key : RawKey}
    (done : key ∈ exhausted) : offer (initialWork known exhausted) key = initialWork known exhausted :=
  known_not_requeued _ key (closed.inKnown done)

/-- The sparse expansion rule cannot visit an exhausted raw key. Together
    with offer_once this rules out replay and requeue of known Exhausted keys. -/
theorem exhausted_not_expandable {exhausted : List RawKey} {key : RawKey}
    (done : key ∈ exhausted) : ¬ (key ∉ exhausted) := fun expand => expand done

/- Counterexample: guide normalization may equate two different raw mx rows. -/
def blocked : RawKey := ⟨0,0,.flow,.flow,[7]⟩
def openRow : RawKey := ⟨0,0,.flow,.flow,[]⟩
def fresh : RawKey := ⟨1,1,.marked 7,.marked 7,[]⟩
def guide (key : RawKey) : Nat × Nat × Header × Header :=
  (key.owner,key.geometry,key.inputMark,key.outputMark)
def exampleKnown : List RawKey := [blocked,openRow]
def exampleArcs : List Arc := [⟨openRow,fresh⟩]
def actualExhausted : List RawKey := [blocked]
def badGuideExhausted : List RawKey := [blocked,openRow]

/-- The mx example is a legal abstract writer, not a concrete marked row
    with an illegal mark-exclusion header. An actual T input can distinguish
    the open result from the T-excluded result at ordinary binding. -/
theorem counterexample_has_FLOW_headers :
    blocked.inputMark = .flow ∧ blocked.outputMark = .flow ∧
    openRow.inputMark = .flow ∧ openRow.outputMark = .flow := ⟨rfl,rfl,rfl,rfl⟩

theorem normalized_guides_equal : guide blocked = guide openRow := rfl

theorem raw_rows_differ : blocked ≠ openRow := by
  intro same
  have marks := congrArg RawKey.mx same
  cases marks

theorem member_singleton {α : Type} {key row : α} (member : key ∈ [row]) : key = row :=
  match member with
  | .head _ => rfl
  | .tail _ impossible => nomatch impossible

theorem actual_certificate : ExhaustionCertificate exampleKnown exampleArcs actualExhausted where
  inKnown := fun member => List.Mem.head _ |> fun first => by
    have same : _ = blocked := member_singleton member
    exact same ▸ first
  engineClosed := fun member image => by
    have sourceEq : _ = blocked := member_singleton member
    have arcEq : _ = (⟨openRow,fresh⟩ : Arc) := member_singleton image
    have rowEq := congrArg Arc.source arcEq
    have impossible : blocked = openRow := sourceEq.symm.trans rowEq
    exact False.elim (raw_rows_differ impossible)

def full_fresh : FullReach exampleKnown exampleArcs fresh :=
  .bind (.seed (List.Mem.tail blocked (List.Mem.head _))) (List.Mem.head _)

def sparse_fresh : SparseReach exampleKnown exampleArcs actualExhausted fresh :=
  fullToSparse actual_certificate full_fresh

theorem fresh_not_known : fresh ∉ exampleKnown := by
  let _ : Decidable (fresh ∈ exampleKnown) := rawMembership fresh exampleKnown
  exact of_decide_eq_false rfl

theorem badReachOnlyKnown {key : RawKey}
    (proof : SparseReach exampleKnown exampleArcs badGuideExhausted key) : key ∈ exampleKnown :=
  match proof with
  | .seed member => member
  | .bind (source := source) _ expand image => by
      have arcEq : (⟨source,key⟩ : Arc) = ⟨openRow,fresh⟩ := member_singleton image
      have sourceEq : source = openRow := congrArg Arc.source arcEq
      have member : source ∈ badGuideExhausted := sourceEq ▸ List.Mem.tail blocked (List.Mem.head _)
      exact False.elim (expand member)

theorem guide_equal_exhaustion_can_lose_image :
    ¬ Nonempty (SparseReach exampleKnown exampleArcs badGuideExhausted fresh) :=
  fun ⟨proof⟩ => fresh_not_known (badReachOnlyKnown proof)

theorem wrong_certificate_impossible :
    ¬ ExhaustionCertificate exampleKnown exampleArcs badGuideExhausted :=
  fun closed => fresh_not_known (closed.engineClosed
    (List.Mem.tail blocked (List.Mem.head _)) (List.Mem.head _))

#print axioms rawMembership
#print axioms fullToSparse
#print axioms sparseToFull
#print axioms reachability_equivalent
#print axioms seed_queue_is_need
#print axioms exhausted_not_seed_work
#print axioms known_not_requeued
#print axioms offer_once
#print axioms known_exhausted_never_requeued
#print axioms exhausted_not_expandable
#print axioms counterexample_has_FLOW_headers
#print axioms normalized_guides_equal
#print axioms raw_rows_differ
#print axioms actual_certificate
#print axioms full_fresh
#print axioms sparse_fresh
#print axioms fresh_not_known
#print axioms guide_equal_exhaustion_can_lose_image
#print axioms wrong_certificate_impossible
end RestrictedDemandNext.WriterReplay
