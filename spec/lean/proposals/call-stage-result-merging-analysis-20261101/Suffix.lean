import Results

/-!
A deterministic suffix is a pure finite observation function. The required
OR law is explicit; it is not asserted for arbitrary stateful analyzer hooks.
Runtime effect ordering and idempotence remain separate adapter obligations.
-/
namespace CallStageMerge
set_option autoImplicit false

abbrev Output := Fin 8
abbrev SuffixTransfer := Row → Output → Bool

def OrPreserving (transfer : SuffixTransfer) : Prop :=
  ∀ old incoming, old.key = incoming.key → ∀ output,
    transfer (joinRows old incoming) output =
      (transfer old output || transfer incoming output)

def suffixObserve (transfer : SuffixTransfer) : List Row → Output → Bool
  | [], _ => false
  | row :: rest, output => transfer row output || suffixObserve transfer rest output

theorem suffix_insert (transfer : SuffixTransfer) (preserves : OrPreserving transfer)
    (incoming : Row) (rows : List Row) (output : Output) :
    suffixObserve transfer (insert incoming rows) output =
      (suffixObserve transfer rows output || transfer incoming output) := by
  induction rows with
  | nil => simp [insert, suffixObserve]
  | cons old rest ih =>
    by_cases same : incoming.key = old.key
    · simp only [insert, if_pos same, suffixObserve]
      rw [preserves old incoming same.symm output]
      exact bool_shuffle_right _ _ _
    · simp only [insert, if_neg same, suffixObserve]
      rw [ih]
      exact bool_associate _ _ _

theorem suffix_collect (transfer : SuffixTransfer) (preserves : OrPreserving transfer)
    (rows stored : List Row) (output : Output) :
    suffixObserve transfer (collect rows stored) output =
      (suffixObserve transfer stored output || suffixObserve transfer rows output) := by
  induction rows generalizing stored with
  | nil => simp [collect, suffixObserve]
  | cons row rest ih =>
    rw [collect, ih, suffix_insert transfer preserves]
    simp only [suffixObserve]
    exact (bool_associate _ _ _).symm

theorem deterministic_suffix_observation_equal (transfer : SuffixTransfer)
    (preserves : OrPreserving transfer) (rows : List Row) (output : Output) :
    suffixObserve transfer (normalize rows) output = suffixObserve transfer rows output := by
  simpa [normalize, suffixObserve] using suffix_collect transfer preserves rows [] output

theorem deterministic_suffix_set_equal (transfer : SuffixTransfer)
    (preserves : OrPreserving transfer) (rows : List Row) (output : Output) :
    suffixObserve transfer (normalize rows) output = true ↔
      suffixObserve transfer rows output = true := by
  rw [deterministic_suffix_observation_equal transfer preserves]

/-- An executable witness of the contract: a fixed suffix can rename the
finite output observations, including ordinary/protected membership. -/
def transportSuffix (select : Output → Observation) : SuffixTransfer :=
  fun row output => rowObservation row (select output)

theorem transport_suffix_preserves_or (select : Output → Observation) :
    OrPreserving (transportSuffix select) := by
  intro old incoming same output
  exact joined_observation old incoming same (select output)

theorem executable_transport_set_equal (select : Output → Observation)
    (rows : List Row) (output : Output) :
    suffixObserve (transportSuffix select) (normalize rows) output = true ↔
      suffixObserve (transportSuffix select) rows output = true := by
  exact deterministic_suffix_set_equal (transportSuffix select)
    (transport_suffix_preserves_or select) rows output

end CallStageMerge
