/-- An executable check for a closed set of possible observation keys.
    The caller supplies a complete census and stable NORMAL receipts. -/
def hasEveryReceipt {Key : Type} [DecidableEq Key]
    (possible receipts : List Key) : Bool :=
  possible.all fun key => decide (key ∈ receipts)

theorem hasEveryReceipt_covers {Key : Type} [DecidableEq Key]
    {possible receipts : List Key} (ok : hasEveryReceipt possible receipts = true)
    {key : Key} (member : key ∈ possible) : key ∈ receipts := by
  have test := (List.all_eq_true.mp ok) key member
  exact of_decide_eq_true test

/-- Keep the identity of every NORMAL finding, even if deleting guidance
    changes the future native admissions or source actions. The two runs
    may visit different sites. The shared census bounds both. -/
theorem sameConfirmedAfterRetirement {Key : Type} [DecidableEq Key]
    {possible receipts : List Key} (ok : hasEveryReceipt possible receipts = true)
    (nativeAfter retiredAfter : List Key)
    (nativeWithin : ∀ key ∈ nativeAfter, key ∈ possible)
    (retiredWithin : ∀ key ∈ retiredAfter, key ∈ possible)
    (key : Key) :
    key ∈ receipts ++ nativeAfter ↔ key ∈ receipts ++ retiredAfter := by
  simp only [List.mem_append]
  constructor
  · rintro (receipt | later)
    · exact Or.inl receipt
    · exact Or.inl (hasEveryReceipt_covers ok (nativeWithin key later))
  · rintro (receipt | later)
    · exact Or.inl receipt
    · exact Or.inl (hasEveryReceipt_covers ok (retiredWithin key later))

inductive CanActivate {Owner : Type} (roots : List Owner) (calls : Owner → List Owner) :
    Owner → Prop where
  | root {owner} : owner ∈ roots → CanActivate roots calls owner
  | call {caller callee} : CanActivate roots calls caller → callee ∈ calls caller →
      CanActivate roots calls callee

/-- A finite list can certify a closed activation scope even when the
    graph has loops. Every root and every compiled alternative must be
    in the list. All its observers and replayable terminal IDs need a
    retained receipt. -/
def closedObservers {Owner Key : Type} [DecidableEq Owner] [DecidableEq Key]
    (roots : List Owner) (calls : Owner → List Owner) (observers : Owner → List Key)
    (scope : List Owner) (replay receipts : List Key) : Bool :=
  (roots.all fun root => decide (root ∈ scope)) &&
    (scope.all fun owner =>
      (calls owner).all (fun callee => decide (callee ∈ scope)) &&
        hasEveryReceipt (observers owner) receipts) &&
      hasEveryReceipt replay receipts

theorem closedObservers_covers_activation {Owner Key : Type} [DecidableEq Owner] [DecidableEq Key]
    {roots : List Owner} {calls : Owner → List Owner} {observers : Owner → List Key}
    {scope : List Owner} {replay receipts : List Key}
    (ok : closedObservers roots calls observers scope replay receipts = true)
    {owner : Owner} (active : CanActivate roots calls owner) :
    owner ∈ scope := by
  simp only [closedObservers, Bool.and_eq_true] at ok
  induction active with
  | root present =>
    exact of_decide_eq_true ((List.all_eq_true.mp ok.1.1) _ present)
  | call _ edge ih =>
    have caller := (List.all_eq_true.mp ok.1.2) _ ih
    simp only [Bool.and_eq_true] at caller
    exact of_decide_eq_true ((List.all_eq_true.mp caller.1) _ edge)

theorem closedObservers_covers_observation {Owner Key : Type}
    [DecidableEq Owner] [DecidableEq Key]
    {roots : List Owner} {calls : Owner → List Owner} {observers : Owner → List Key}
    {scope : List Owner} {replay receipts : List Key}
    (ok : closedObservers roots calls observers scope replay receipts = true)
    {owner : Owner} (active : CanActivate roots calls owner) {key : Key}
    (emitted : key ∈ observers owner ∨ key ∈ replay) :
    key ∈ receipts := by
  have present := closedObservers_covers_activation ok active
  simp only [closedObservers, Bool.and_eq_true] at ok
  cases emitted with
  | inl observer =>
    have owned := (List.all_eq_true.mp ok.1.2) owner present
    simp only [Bool.and_eq_true] at owned
    exact hasEveryReceipt_covers owned.2 observer
  | inr terminal => exact hasEveryReceipt_covers ok.2 terminal

/-- A physical report may already be confirmed when the solver still
    has a second marking point to find. Applying the identity-only
    certificate to individual tracks would be invalid. -/
example :
    let early : List (Nat × Nat) := [(0, 7)]
    let later : List (Nat × Nat) := [(1, 7)]
    hasEveryReceipt (later.map Prod.snd) (early.map Prod.snd) = true ∧
      hasEveryReceipt later early = false := by decide

/-- For a scope with one possible marking-action/full-mark pair, a
    proved receipt for each observer also covers the corresponding track.
    The embedding must come from a native receipt at each observer. -/
theorem singleOriginCoversTrack {Origin Key : Type} [DecidableEq Key]
    {possible scopedReceipts : List Key} (ok : hasEveryReceipt possible scopedReceipts = true)
    (originSeen : Origin) (observedTracks : List (Origin × Key))
    (embedding : ∀ key ∈ scopedReceipts, (originSeen, key) ∈ observedTracks)
    (origin : Origin) (key : Key) (member : key ∈ possible)
    (sameOrigin : origin = originSeen) : (origin, key) ∈ observedTracks := by
  rw [sameOrigin]
  exact embedding key (hasEveryReceipt_covers ok member)

/-- The completion ordinal is assigned after every called context
    completed. An edge to a pending context rejects the census. -/
inductive CompletedCallPath {Owner : Type} (endOrder : Owner → Nat) : Owner → Owner → Prop where
  | step {p q} : endOrder q < endOrder p → CompletedCallPath endOrder p q
  | join {p q r} : CompletedCallPath endOrder p q → CompletedCallPath endOrder q r →
      CompletedCallPath endOrder p r

theorem completionOrderStrict {Owner : Type} {endOrder : Owner → Nat}
    {p q : Owner} (path : CompletedCallPath endOrder p q) : endOrder q < endOrder p := by
  induction path with
  | step smaller => exact smaller
  | join _ _ first last => exact Nat.lt_trans last first

theorem noCycleInCompletedScope {Owner : Type} {endOrder : Owner → Nat}
    (owner : Owner) (cycle : CompletedCallPath endOrder owner owner) : False :=
  Nat.lt_irrefl (endOrder owner) (completionOrderStrict cycle)
