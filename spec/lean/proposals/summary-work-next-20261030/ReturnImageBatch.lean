import Std

/-!
Proposal kernel only. Tokens denote complete canonical runtime keys, not AP coverage.
The ordinary image is a finite literal-coordinate signature. Protection coordinates
are observations; they are not part of ordinary signature equality.
No theorem below assumes that an arbitrary stateful return suffix is additive.
-/
namespace ReturnImageBatch

inductive Layer where | normal | demand deriving DecidableEq, Repr
inductive Kind where | reach | flow | taint deriving DecidableEq, Repr
inductive Tail where | exact | star | may | must deriving DecidableEq, Repr

structure ReturnScope where
  callerMethod : Nat
  callerContext : List Nat
  statement : Nat
  stageOrdinal : Nat
  originalPremise : List Nat
  resultPremise : List Nat
  callerLayer : Layer
  identityCandidate : Option Bool
  pendingDemotion : Bool
  deriving DecidableEq, Repr

structure FactsHeader where
  kind : Kind
  layer : Layer
  base : Nat
  tail : Tail
  fieldExclusions : List Nat
  markExclusions : List Nat
  deriving DecidableEq, Repr

structure Signature where
  scope : ReturnScope
  header : FactsHeader
  ordinary : List Bool
  deriving DecidableEq, Repr

structure Image where
  signature : Signature
  protection : Nat → Bool

def maskUnion (a b : Nat → Bool) : Nat → Bool := fun i => a i || b i

def put (x : Image) : List Image → List Image
  | [] => [x]
  | y :: ys =>
      if x.signature = y.signature then
        { y with protection := maskUnion y.protection x.protection } :: ys
      else y :: put x ys

def compact : List Image → List Image
  | [] => []
  | x :: xs => put x (compact xs)

def hasSignature : List Image → Signature → Bool
  | [], _ => false
  | x :: xs, q => decide (x.signature = q) || hasSignature xs q

def protectedAt : List Image → Signature → Nat → Bool
  | [], _, _ => false
  | x :: xs, q, i =>
      (decide (x.signature = q) && x.protection i) || protectedAt xs q i

def ordinaryAt (rows : List Image) (q : Signature) (i : Nat) : Bool :=
  hasSignature rows q && (q.ordinary[i]?.getD false)

def annotatedWithinOrdinary (rows : List Image) : Prop :=
  ∀ q i, protectedAt rows q i = true → ordinaryAt rows q i = true

def keys (rows : List Image) : List Signature := rows.map Image.signature

theorem hasSignature_put (x : Image) (rows : List Image) (q : Signature) :
    hasSignature (put x rows) q = (decide (x.signature = q) || hasSignature rows q) := by
  induction rows with
  | nil => simp [put, hasSignature]
  | cons y ys ih =>
      by_cases same : x.signature = y.signature
      · by_cases hit : y.signature = q
        · simp [put, same, hasSignature, hit]
        · simp [put, same, hasSignature, hit]
      · simp [put, same, hasSignature, ih, Bool.or_left_comm]

theorem protectedAt_put (x : Image) (rows : List Image) (q : Signature) (i : Nat) :
    protectedAt (put x rows) q i =
      ((decide (x.signature = q) && x.protection i) || protectedAt rows q i) := by
  induction rows with
  | nil => simp [put, protectedAt]
  | cons y ys ih =>
      by_cases same : x.signature = y.signature
      · by_cases hit : y.signature = q
        · simp [put, same, protectedAt, hit, maskUnion, Bool.or_assoc, Bool.or_left_comm]
        · simp [put, same, protectedAt, hit]
      · simp [put, same, protectedAt, ih, Bool.or_left_comm]

theorem compact_preserves_signatures (rows : List Image) (q : Signature) :
    hasSignature (compact rows) q = hasSignature rows q := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simp [compact, hasSignature_put, hasSignature, ih]

theorem compact_preserves_protection (rows : List Image) (q : Signature) (i : Nat) :
    protectedAt (compact rows) q i = protectedAt rows q i := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simp [compact, protectedAt_put, protectedAt, ih]

theorem compact_preserves_ordinary (rows : List Image) (q : Signature) (i : Nat) :
    ordinaryAt (compact rows) q i = ordinaryAt rows q i := by
  simp [ordinaryAt, compact_preserves_signatures]

theorem compact_preserves_annotation_subset (rows : List Image)
    (h : annotatedWithinOrdinary rows) : annotatedWithinOrdinary (compact rows) := by
  intro q i hp
  rw [compact_preserves_protection] at hp
  rw [compact_preserves_ordinary]
  exact h q i hp

theorem put_other_signature_unchanged (x : Image) (rows : List Image) (q : Signature)
    (h : x.signature ≠ q) :
    hasSignature (put x rows) q = hasSignature rows q ∧
      (∀ i, protectedAt (put x rows) q i = protectedAt rows q i) := by
  constructor
  · simp [hasSignature_put, h]
  · intro i; simp [protectedAt_put, h]

theorem different_scope_keeps_observations_separate (x : Image) (rows : List Image)
    (q : Signature) (h : x.signature.scope ≠ q.scope) :
    hasSignature (put x rows) q = hasSignature rows q ∧
      (∀ i, protectedAt (put x rows) q i = protectedAt rows q i) := by
  apply put_other_signature_unchanged
  intro eq
  exact h (congrArg Signature.scope eq)

theorem put_key_membership (x : Image) (rows : List Image) (q : Signature) :
    q ∈ keys (put x rows) ↔ q = x.signature ∨ q ∈ keys rows := by
  induction rows with
  | nil => simp [put, keys]
  | cons y ys ih =>
      by_cases same : x.signature = y.signature
      · simp [put, same, keys, eq_comm]
      · simp only [put, same, ↓reduceIte, keys, List.map_cons, List.mem_cons] at *
        rw [ih]
        simp only [or_left_comm]

theorem put_preserves_distinct_keys (x : Image) (rows : List Image)
    (h : (keys rows).Nodup) : (keys (put x rows)).Nodup := by
  induction rows with
  | nil => simp [put, keys]
  | cons y ys ih =>
      have hy : y.signature ∉ keys ys := (List.nodup_cons.mp h).1
      have hys : (keys ys).Nodup := (List.nodup_cons.mp h).2
      by_cases same : x.signature = y.signature
      · simpa [put, same, keys] using h
      · simp only [put, same, ↓reduceIte, keys, List.map_cons]
        apply List.nodup_cons.mpr
        constructor
        · intro bad
          rcases (put_key_membership x ys y.signature).mp bad with eq | mem
          · exact same eq.symm
          · exact hy mem
        · exact ih hys

theorem compact_keys_are_distinct (rows : List Image) : (keys (compact rows)).Nodup := by
  induction rows with
  | nil => simp [compact, keys]
  | cons x xs ih => exact put_preserves_distinct_keys x _ ih

theorem compact_key_membership (rows : List Image) (q : Signature) :
    q ∈ keys (compact rows) ↔ q ∈ keys rows := by
  induction rows with
  | nil => rfl
  | cons x xs ih =>
      simp only [compact]
      rw [put_key_membership, ih]
      simp only [keys, List.map_cons, List.mem_cons]

theorem put_length_le (x : Image) (rows : List Image) :
    (put x rows).length ≤ rows.length + 1 := by
  induction rows with
  | nil => simp [put]
  | cons y ys ih =>
      by_cases same : x.signature = y.signature
      · simp [put, same]
      · simp only [put, same, ↓reduceIte, List.length_cons]
        omega

def oldSuffixCalls (rows : List Image) : Nat := rows.length
def newSuffixCalls (rows : List Image) : Nat := (compact rows).length
/-- K counts every distinct complete signature once, by the two preceding theorems. -/
def distinctSignatureCount (rows : List Image) : Nat := (keys (compact rows)).length

theorem calls_equal_distinct_signature_count (rows : List Image) :
    newSuffixCalls rows = distinctSignatureCount rows := by
  simp [newSuffixCalls, distinctSignatureCount, keys]

theorem suffix_calls_do_not_increase (rows : List Image) :
    newSuffixCalls rows ≤ oldSuffixCalls rows := by
  induction rows with
  | nil => simp [newSuffixCalls, oldSuffixCalls, compact]
  | cons x xs ih =>
      have hp := put_length_le x (compact xs)
      simp only [newSuffixCalls, oldSuffixCalls] at ih ⊢
      simp only [compact, List.length_cons]
      omega

theorem two_equal_images_use_one_suffix (s : Signature) (a b : Nat → Bool) :
    oldSuffixCalls [⟨s, a⟩, ⟨s, b⟩] = 2 ∧
      newSuffixCalls [⟨s, a⟩, ⟨s, b⟩] = 1 := by
  simp [oldSuffixCalls, newSuffixCalls, compact, put]

theorem two_equal_images_union_each_protection_coordinate
    (s : Signature) (a b : Nat → Bool) (i : Nat) :
    protectedAt (compact [⟨s, a⟩, ⟨s, b⟩]) s i = (a i || b i) := by
  simp [compact_preserves_protection, protectedAt]

theorem two_distinct_images_keep_two_suffixes (a b : Image)
    (h : a.signature ≠ b.signature) : newSuffixCalls [a,b] = 2 := by
  simp [newSuffixCalls, compact, put, h]

end ReturnImageBatch
