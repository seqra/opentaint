import Std

/-
  Coordinate component for the frozen backward FLOW policy. Guards for bases,
  exclusions, marks and field limits can reject these branches. This model
  covers nonstatic paths whose accessors count toward the field limit.
  It describes C2 geometry and a single prefix transfer, not call closure.
-/
namespace BackwardUriInitialCoordinates

inductive Tail where
  | exact | star | may | must
  deriving DecidableEq, Repr

structure Shape where
  path : List Nat
  tail : Tail
  deriving DecidableEq, Repr

def Safe (uri : Nat) (fact : Shape) : Prop :=
  uri ∉ fact.path.dropLast ∧ (fact.tail = .exact → uri ∉ fact.path)

def AllowedEntry (uri : Nat) (demand : Shape) : Prop :=
  uri ∉ demand.path ∨ (demand.tail = .may ∧ uri ∉ demand.path.dropLast)

inductive C2 (demand actual : Shape) : Shape → Prop where
  | sameExact (path : actual.path = demand.path)
      (tail : demand.tail = .star ∨ actual.tail = .exact) : C2 demand actual ⟨demand.path, .exact⟩
  | sameStar : C2 demand actual ⟨demand.path, .star⟩
  | ancestorExact (tail : demand.tail = .star) : C2 demand actual ⟨demand.path, .exact⟩
  | ancestorStar : C2 demand actual ⟨demand.path, .star⟩
  | firstField (field : Nat) (rest : List Nat)
      (path : actual.path = demand.path ++ field :: rest) : C2 demand actual ⟨demand.path ++ [field], .star⟩
  | rootCompanion (field : Nat) (rest : List Nat)
      (path : actual.path = demand.path ++ field :: rest) : C2 demand actual ⟨demand.path, .exact⟩

theorem safe_free (uri : Nat) (path : List Nat) (tail : Tail) (free : uri ∉ path) :
    Safe uri ⟨path, tail⟩ :=
  ⟨fun h => free (List.dropLast_subset path h), fun _ => free⟩

theorem safe_first_field (uri field : Nat) (path : List Nat) (free : uri ∉ path) :
    Safe uri ⟨path ++ [field], .star⟩ := by
  simp [Safe, free]

theorem free_entry_safe (uri : Nat) (demand actual result : Shape)
    (free : uri ∉ demand.path) (emitted : C2 demand actual result) : Safe uri result := by
  cases emitted with
  | sameExact | ancestorExact | rootCompanion => exact safe_free uri demand.path .exact free
  | sameStar | ancestorStar => exact safe_free uri demand.path .star free
  | firstField field => exact safe_first_field uri field demand.path free

theorem strict_prefix_free (uri : Nat) (actual : Shape) (headPath : List Nat) (field : Nat)
    (rest : List Nat) (path : actual.path = headPath ++ field :: rest) (safe : Safe uri actual) :
    uri ∉ headPath := by
  intro h
  apply safe.1
  rw [path, List.dropLast_append_of_ne_nil (by simp : field :: rest ≠ [])]
  exact List.mem_append.mpr (Or.inl h)

theorem allowed_entry_keeps_safe (uri : Nat) (demand actual result : Shape)
    (entry : AllowedEntry uri demand) (safe : Safe uri actual)
    (emitted : C2 demand actual result) : Safe uri result := by
  rcases entry with free | ⟨may, finalOnly⟩
  · exact free_entry_safe uri demand actual result free emitted
  cases emitted with
  | sameExact path tail =>
      rcases tail with star | exactTail
      · rw [may] at star
        cases star
      · apply safe_free uri demand.path .exact
        rw [← path]
        exact safe.2 exactTail
  | ancestorExact star =>
      rw [may] at star
      cases star
  | sameStar | ancestorStar => simp [Safe, finalOnly]
  | firstField field rest path =>
      exact safe_first_field uri field demand.path (strict_prefix_free uri actual demand.path field rest path safe)
  | rootCompanion field rest path =>
      exact safe_free uri demand.path .exact (strict_prefix_free uri actual demand.path field rest path safe)

theorem prefix_transfer_keeps_safe (uri : Nat) (source target suffix : List Nat)
    (before after : Tail) (free : uri ∉ target)
    (safe : Safe uri ⟨source ++ suffix, before⟩) (keepsExact : after = .exact → before = .exact) :
    Safe uri ⟨target ++ suffix, after⟩ := by
  cases suffix with
  | nil => simpa using safe_free uri target after free
  | cons field rest =>
      have tailNotEmpty : field :: rest ≠ [] := by simp
      constructor
      · simp only [List.dropLast_append_of_ne_nil tailNotEmpty, List.mem_append, not_or]
        refine ⟨free, ?_⟩
        intro h
        apply safe.1
        rw [List.dropLast_append_of_ne_nil tailNotEmpty]
        exact List.mem_append.mpr (Or.inr h)
      · intro exactTail h
        rcases List.mem_append.mp h with h | h
        · exact free h
        · exact safe.2 (keepsExact exactTail) (List.mem_append.mpr (Or.inr h))

def PreciseUri (uri : Nat) (fact : Shape) : Prop :=
  uri ∈ fact.path ∧ fact.tail ≠ .may

/- The backward FLOW restriction has no MUST input. The relation admits
   extra geometry branches. They cannot falsify the coordinate implication. -/
inductive C5 (selector input : Shape) : Shape → Prop where
  | keep : C5 selector input input
  | maySelect (inputMay : input.tail = .may) : C5 selector input ⟨selector.path, .may⟩
  | exactSelect (selectorExact : selector.tail = .exact) : C5 selector input ⟨selector.path, .exact⟩

theorem precise_restriction_requires_precise_input (uri : Nat) (selector input output : Shape)
    (noExactUriSelector : selector.tail = .exact → uri ∉ selector.path)
    (selected : C5 selector input output) (precise : PreciseUri uri output) : PreciseUri uri input := by
  cases selected with
  | keep => exact precise
  | maySelect => exact False.elim (precise.2 rfl)
  | exactSelect selectorExact => exact False.elim (noExactUriSelector selectorExact precise.1)

def normalizeFlowExact (fact : Shape) : Shape :=
  if fact.tail = .exact then { fact with tail := .star } else fact

theorem normalization_preserves_precise_uri (uri : Nat) (fact : Shape) :
    PreciseUri uri (normalizeFlowExact fact) ↔ PreciseUri uri fact := by
  unfold normalizeFlowExact
  split <;> rename_i h
  · simp [PreciseUri, h]
  · rfl

/- A derivation may use another derived summary. The below lane of a STAR
   result retains the actual suffix and tail. An inside lane in this backward
   FLOW domain produces MAY, including when the child started on STAR.
   A native binding still has to account for every producer and runtime lane. -/
inductive FlowTrace (uri : Nat) : Shape → Shape → Prop where
  | identity (initial : Shape) : FlowTrace uri initial initial
  | primitive {initial : Shape} (source target suffix : List Nat) (tail : Tail)
      (earlier : FlowTrace uri initial ⟨source ++ suffix, tail⟩)
      (targetFree : uri ∉ target) : FlowTrace uri initial ⟨target ++ suffix, tail⟩
  | current {initial childEntry actual childResult : Shape} (suffix : List Nat)
      (earlier : FlowTrace uri initial actual) (child : FlowTrace uri childEntry childResult)
      (star : childResult.tail = .star) (below : actual.path = childEntry.path ++ suffix) :
      FlowTrace uri initial ⟨childResult.path ++ suffix, actual.tail⟩
  | widen {initial : Shape} (path : List Nat) : FlowTrace uri initial ⟨path, .may⟩
  | restrict {initial selector input output : Shape} (earlier : FlowTrace uri initial input)
      (noExactUriSelector : selector.tail = .exact → uri ∉ selector.path)
      (selected : C5 selector input output) : FlowTrace uri initial output
  | normalize {initial fact : Shape} (earlier : FlowTrace uri initial fact) :
      FlowTrace uri initial (normalizeFlowExact fact)

theorem precise_trace_requires_precise_origin (uri : Nat) (initial result : Shape)
    (trace : FlowTrace uri initial result) (precise : PreciseUri uri result) : PreciseUri uri initial := by
  induction trace with
  | identity => exact precise
  | primitive source target suffix tail _ free ih =>
      have occurrence := List.mem_append.mp precise.1
      rcases occurrence with h | h
      · exact False.elim (free h)
      · exact ih ⟨List.mem_append.mpr (Or.inr h), precise.2⟩
  | current suffix _ _ star below earlier child =>
      apply earlier
      refine ⟨?_, precise.2⟩
      rw [below]
      rcases List.mem_append.mp precise.1 with h | h
      · exact List.mem_append.mpr (Or.inl (child ⟨h, by simp [star]⟩).1)
      · exact List.mem_append.mpr (Or.inr h)
  | widen => exact False.elim (precise.2 rfl)
  | restrict _ guard selected ih => exact ih (precise_restriction_requires_precise_input uri _ _ _ guard selected precise)
  | normalize _ ih => exact ih ((normalization_preserves_precise_uri uri _).mp precise)

theorem exact_trace_requires_exact_origin (uri : Nat) (initial result : Shape)
    (trace : FlowTrace uri initial result) (exactTail : result.tail = .exact)
    (containsUri : uri ∈ result.path) : initial.tail = .exact ∧ uri ∈ initial.path := by
  induction trace with
  | identity => exact ⟨exactTail, containsUri⟩
  | primitive source target suffix tail _ free ih =>
      rcases List.mem_append.mp containsUri with h | h
      · exact False.elim (free h)
      · exact ih exactTail (List.mem_append.mpr (Or.inr h))
  | current suffix _ childTrace star below earlier _ =>
      apply earlier exactTail
      rw [below]
      rcases List.mem_append.mp containsUri with h | h
      · exact List.mem_append.mpr (Or.inl (precise_trace_requires_precise_origin uri _ _ childTrace ⟨h, by simp [star]⟩).1)
      · exact List.mem_append.mpr (Or.inr h)
  | widen => cases exactTail
  | restrict _ guard selected ih =>
      cases selected with
      | keep => exact ih exactTail containsUri
      | maySelect => cases exactTail
      | exactSelect e => exact False.elim (guard e containsUri)
  | normalize =>
      simp only [normalizeFlowExact] at exactTail
      split at exactTail <;> contradiction

theorem one_field_star_summary_keeps_safe (uri : Nat) (entry actual : Shape)
    (target suffix : List Nat) (shallow : target.length ≤ 1)
    (targetUsesInput : uri ∈ target → uri ∈ entry.path)
    (matchPath : actual.path = entry.path ++ suffix) (safe : Safe uri actual) :
    Safe uri ⟨target ++ suffix, actual.tail⟩ := by
  by_cases free : uri ∈ target
  · have emptySuffix : suffix = [] := by
      cases suffix with
      | nil => rfl
      | cons field rest => exact False.elim (strict_prefix_free uri actual entry.path field rest matchPath safe (targetUsesInput free))
    subst suffix
    simp only [List.append_nil] at matchPath ⊢
    refine ⟨?_, ?_⟩
    · cases target with
      | nil => simp
      | cons field rest =>
          cases rest with
          | nil => simp
          | cons next rest => simp at shallow
    · intro exactTail _
      apply safe.2 exactTail
      rw [matchPath]
      exact targetUsesInput free
  · have inputSafe : Safe uri ⟨entry.path ++ suffix, actual.tail⟩ := by
      simpa only [Safe, ← matchPath] using safe
    exact prefix_transfer_keeps_safe uri entry.path target suffix actual.tail actual.tail free inputSafe id

end BackwardUriInitialCoordinates

#print axioms BackwardUriInitialCoordinates.free_entry_safe
#print axioms BackwardUriInitialCoordinates.allowed_entry_keeps_safe
#print axioms BackwardUriInitialCoordinates.prefix_transfer_keeps_safe
#print axioms BackwardUriInitialCoordinates.precise_restriction_requires_precise_input
#print axioms BackwardUriInitialCoordinates.normalization_preserves_precise_uri
#print axioms BackwardUriInitialCoordinates.precise_trace_requires_precise_origin
#print axioms BackwardUriInitialCoordinates.exact_trace_requires_exact_origin
#print axioms BackwardUriInitialCoordinates.one_field_star_summary_keeps_safe
