/-- The legacy exception only matters for exact input. FULL nonstatic
    exact input has no strict-descendant result under R13. -/
def r13Ancestor (exact full static keep : Bool) : Bool :=
  !exact || ((!full || static) && keep)

def r13LazyAncestor (exact full static : Bool) (keep : Unit → Bool) : Bool :=
  if !exact then true else if full && !static then false else keep ()

theorem r13_lazy_same (exact full static keep : Bool) :
    r13LazyAncestor exact full static (fun _ => keep) = r13Ancestor exact full static keep := by
  cases exact <;> cases full <;> cases static <;> cases keep <;> rfl

/-- An exact input supports only its own field word. The native
    strict-descendant keep tests a nonempty additional word. -/
theorem r13_exact_support_excludes_strict_descendants {Field : Type}
    (head suffix : List Field) (proper : suffix ≠ []) :
    head ++ suffix ≠ head := by
  intro same
  have sameTail : head ++ suffix = head ++ [] := by simpa using same
  exact proper (List.append_cancel_left sameTail)

/-- One operation combines values at each canonical key and emits
    keys in their first-insertion order. -/
def addOrdered {K V : Type} [DecidableEq K] (merge : V → V → V)
    (key : K) (value : V) : List (K × V) → List (K × V)
  | [] => [(key, value)]
  | (k, v) :: rest =>
      if k = key then (k, merge v value) :: rest
      else (k, v) :: addOrdered merge key value rest

def addAfterFirst {K V : Type} [DecidableEq K] (merge : V → V → V)
    (key : K) (value : V) (first : K × V) (rest : List (K × V)) :
    (K × V) × List (K × V) :=
  if first.1 = key then ((first.1, merge first.2 value), rest)
  else (first, addOrdered merge key value rest)

theorem inlineFirstOutputSame {K V : Type} [DecidableEq K] (merge : V → V → V)
    (key k : K) (value v : V) (rest : List (K × V)) :
    let stored := addAfterFirst merge key value (k, v) rest
    stored.1 :: stored.2 = addOrdered merge key value ((k, v) :: rest) := by
  by_cases same : k = key <;> simp [addAfterFirst, addOrdered, same]

/-- A closed observer plan divides its checks into immutable form checks
    and checks that depend on the incoming packet. -/
def validObserver (form packet : Bool) : Bool := form && packet

def observerOffers (form : Unit → Bool) (packets : List Bool) : List Bool :=
  let checked := form ()
  packets.map (validObserver checked)

theorem observer_cache_same (form : Bool) (packets : List Bool) :
    observerOffers (fun _ => form) packets = packets.map (validObserver form) := rfl

theorem observer_rejects_closed_gate (packet : Bool) :
    validObserver false packet = false := rfl

/-- At the last field, the native restricted MUST cleanup already emits
    exactly this one residual and, for BELOW, the point. -/
inductive Residual where
  | sibling (head : Nat) (mask : List Nat)
  | point (head : Nat)
  deriving DecidableEq

def finalField (depth field : Nat) (mask : List Nat) (below : Bool) : List Residual :=
  .sibling depth (field :: mask) :: if below then [.point (depth + 1)] else []

def mustPartition (depth : Nat) (mask : List Nat) (below : Bool) : List Nat → List Residual
  | [] => if below then [.point depth] else []
  | field :: rest => .sibling depth (field :: mask) :: mustPartition (depth + 1) [] below rest

theorem r36_last_field_native (depth field : Nat) (mask : List Nat) (below : Bool) :
    mustPartition depth mask below [field] = finalField depth field mask below := rfl

theorem r36_cap_on_residual_count (depth : Nat) (mask : List Nat) (below : Bool)
    (rest : List Nat) : (mustPartition depth mask below rest).length ≤ rest.length + 1 := by
  induction rest generalizing depth mask with
  | nil => cases below <;> simp [mustPartition]
  | cons field rest ih =>
    simp only [mustPartition, List.length_cons]
    exact Nat.add_le_add_right (ih (depth + 1) []) 1

def startsWithFields : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | f :: fs, x :: xs => f == x && startsWithFields fs xs

/-- A sibling residual covers the current point and every other
    child. A fact through the selected child uses the next residual. -/
def acceptsResidual (below : Bool) : List Nat → List Nat → Bool
  | [], xs => below && xs.isEmpty
  | _ :: _, [] => true
  | f :: fs, x :: xs => if f == x then acceptsResidual below fs xs else true

theorem r36_partition_exact (below : Bool) (clean fact : List Nat) :
    acceptsResidual below clean fact =
      (!startsWithFields clean fact || (below && clean == fact)) := by
  induction clean generalizing fact with
  | nil => cases fact <;> cases below <;> rfl
  | cons f fs ih =>
    cases fact with
    | nil => cases below <;> rfl
    | cons x xs =>
      rw [List.cons_beq_cons]
      change (if f == x then acceptsResidual below fs xs else true) =
        (!(f == x && startsWithFields fs xs) || (below && (f == x && fs == xs)))
      cases f == x
      · rfl
      · exact ih xs

def repeatedSiblings (head field : Nat) : Nat → List Residual
  | 0 => []
  | n + 1 => .sibling head [field] :: repeatedSiblings (head + 1) field n

theorem r36_packed_spine_same_leaves (head field size : Nat) :
    repeatedSiblings head field size =
      mustPartition head [] false (List.replicate size field) := by
  induction size generalizing head with
  | zero => rfl
  | succ n ih => simp [repeatedSiblings, List.replicate_succ, mustPartition, ih]

def Residual.depth : Residual → Nat
  | .sibling head _ => head
  | .point head => head

theorem r36_field_limit (depth : Nat) (mask : List Nat) (below : Bool)
    (path : List Nat) (limit : Nat) (fits : depth + path.length ≤ limit)
    (residual : Residual) (member : residual ∈ mustPartition depth mask below path) :
    residual.depth ≤ limit := by
  induction path generalizing depth mask with
  | nil =>
    cases below
    · simp [mustPartition] at member
    · simp [mustPartition] at member
      subst residual
      simpa [Residual.depth] using fits
  | cons field rest ih =>
    simp only [mustPartition, List.mem_cons] at member
    cases member with
    | inl first => subst residual; simp [Residual.depth]; omega
    | inr next => exact ih (depth + 1) [] (by simp at fits; omega) next

/-- Per-group C5 indexing is unused if C2 has no provider from a
    different origin. A second leaf of the same origin is not a provider. -/
def sharedC2 (entries : List (Nat × Nat)) (origin key : Nat) : Bool :=
  entries.any (fun row => row.1 != origin && row.2 == key)

def removable (entries : List (Nat × Nat)) (c5 : Nat → Nat → Bool) (origin : Nat) :
    List Nat → Bool
  | [] => false
  | key :: keys => (key :: keys).all (fun k => sharedC2 entries origin k && c5 origin k)

theorem unique_c2_skips_c5 (entries : List (Nat × Nat)) (c5 : Nat → Nat → Bool)
    (origin : Nat) (keys : List Nat) (unique : ∀ k, sharedC2 entries origin k = false) :
    removable entries c5 origin keys = false := by
  cases keys with
  | nil => rfl
  | cons k ks => simp [removable, unique k]

/-- A native origin uses the full serialized key only to break a tie on
    exit port and protection. Group order and stable equal-key order
    remain the caller's responsibility. -/
def compareDeferredOrigin {Key : Type} (compareKey : Key → Key → Ordering)
    (header : Ordering) (left right : Unit → Key) : Ordering :=
  match header with
  | .eq => compareKey (left ()) (right ())
  | other => other

theorem compareDeferredOrigin_exact {Key : Type} (compareKey : Key → Key → Ordering)
    (header : Ordering) (left right : Unit → Key) :
    compareDeferredOrigin compareKey header left right =
      (if header == .eq then compareKey (left ()) (right ()) else header) := by
  cases header <;> rfl

/-- A saved geometry query may finish with a rejection. Only a complete
    result can be shared. Budget exhaustion has no geometry value. -/
inductive Geometry (α : Type) where
  | completed (value : Option α)
  | exhausted

def reuseGeometry {α : Type} (cached : Option (Option α)) (probe : Unit → Geometry α) :
    Geometry α :=
  match cached with
  | some value => .completed value
  | none => probe ()

theorem same_frozen_geometry {α : Type} (cached : Option α)
    (probe : Unit → Geometry α) (equivalent : probe () = .completed cached) :
    reuseGeometry (some cached) probe = probe () := by
  rw [equivalent]
  rfl

/-- Both inputs of a direct witness are prefixes of the requested
    relation. It is sufficient to query the shorter broad head. -/
theorem r41_direct_prefix {head broadTail relationTail : List Nat} :
    (head ++ broadTail) ++ relationTail = head ++ (broadTail ++ relationTail) :=
  List.append_assoc _ _ _

/-- Once the shift is known, a packed output has at most one matching
    leaf path for the chosen input witness. -/
theorem r41_required_output_unique {a b suffix : List Nat}
    (same : a ++ suffix = b ++ suffix) : a = b :=
  List.append_cancel_right same

/-! A fragment of restricted C2 for a root STAR/FLOW demand in run-3 or
later. The same-head concrete MAY offer starts FLOW at the root point.
The deeper concrete point is rejected before any companion is made. -/
inductive CopyReply where
  | rootMay
  | point (path : List Nat)

def coversPoint : CopyReply → List Nat → Prop
  | .rootMay, _ => True
  | .point path, candidate => path = candidate

def admitsRootFlowStar : CopyReply → Bool
  | .rootMay => true
  | .point path => path.isEmpty

theorem native_c2_not_monotone_under_reply_narrowing (field : Nat) :
    (∀ p, coversPoint (.point [field]) p → coversPoint .rootMay p) ∧
    coversPoint (.point [field]) [field] ∧
    admitsRootFlowStar .rootMay = true ∧
    admitsRootFlowStar (.point [field]) = false := by
  simp [coversPoint, admitsRootFlowStar]

/-- Identical boundary offers have the same frozen restriction answer.
    After that answer has entered the completion store, repeating the
    offer cannot add a new completion. The executable witness is the
    first stored result at the same boundary key. -/
theorem repeatedBoundaryMembership {α : Type} {produced saved : List α}
    (previous : ∀ x ∈ produced, x ∈ saved) (value : α) :
    value ∈ saved ++ produced ↔ value ∈ saved := by
  rw [List.mem_append]
  exact ⟨fun h => h.elim id (previous value), Or.inl⟩

/-- Read-only restriction selects a value, independently of the
    physical completion where the caller subsequently delivers it. -/
theorem reuseLoopRestriction {Key Output : Type} (restrict : Key → List Output)
    (cachedKey key : Key) (cached : List Output)
    (completed : restrict cachedKey = cached) (same : cachedKey = key) :
    restrict key = cached := by
  exact same ▸ completed

/-- Exit metadata can delete members of a saved DATA replay, but cannot
    move them to a base for which an enclosing C5 plan has a program. -/
theorem noEnclosingReplayAtRejectedBase {Fact Base Output : Type}
    (replay : List Fact) (baseOf : Fact → Base) (base : Base)
    (finish : Fact → List Fact) (c5 : Fact → List Output)
    (replayBase : ∀ f ∈ replay, baseOf f = base)
    (preservesBase : ∀ f g, g ∈ finish f → baseOf g = baseOf f)
    (planEmpty : ∀ f, baseOf f = base → c5 f = []) :
    (replay.flatMap finish).flatMap c5 = [] := by
  cases result : (replay.flatMap finish).flatMap c5 with
  | nil => rfl
  | cons output rest =>
    have member : output ∈ (replay.flatMap finish).flatMap c5 :=
      result.symm ▸ List.mem_cons_self
    obtain ⟨g, hg, hout⟩ := List.mem_flatMap.mp member
    obtain ⟨f, hf, hfinish⟩ := List.mem_flatMap.mp hg
    rw [planEmpty g ((preservesBase f g hfinish).trans (replayBase f hf))] at hout
    exact False.elim (List.not_mem_nil hout)

/-- For C5's deeper-output case the demanded head and first remaining
    field both fit within a cap strictly below the actual tail. -/
theorem outputSelectorBeforeCut {Field : Type} (demand head rest : List Field)
    (fits : demand.length < head.length) :
    (head ++ rest).take demand.length = head.take demand.length ∧
    ((head ++ rest).drop demand.length).head? = (head.drop demand.length).head? := by
  constructor
  · exact List.take_append_of_le_length (by omega)
  · induction head generalizing demand with
    | nil => simp at fits
    | cons field next ih =>
      cases demand with
      | nil => rfl
      | cons first remaining =>
        simp only [List.length_cons] at fits
        simpa using ih remaining (by omega)

/-- A second cut at a smaller paired budget sees exactly the same
    known field chain for two words in the overflow class. -/
theorem outputCutCommonPrefix {Field : Type} (head left right : List Field) (budget : Nat)
    (within : budget ≤ head.length) :
    (head ++ left).take budget = (head ++ right).take budget := by
  rw [List.take_append_of_le_length within, List.take_append_of_le_length within]
