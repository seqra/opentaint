import Std

/- Constructive finite report selection. IDs denote physical sink keys. The
   model assumes witness capture at the actual forward sink handler; it does
   not prove a provisional witness is a concrete source-to-sink path. -/
namespace Run11Reports

structure Entry where
  id : Nat
  provisional : Bool
  deriving DecidableEq, Repr

def confirmedEntries (confirmed : List Nat) : List Entry :=
  confirmed.eraseDups.map (fun id => ⟨id, false⟩)

def provisionalEntries (confirmed latest : List Nat) : List Entry :=
  (latest.eraseDups.filter (fun id => !confirmed.contains id)).map
    (fun id => ⟨id, true⟩)

def report (limited : Bool) (confirmed latest : List Nat) : List Entry :=
  confirmedEntries confirmed ++
    if limited then provisionalEntries confirmed latest else []

def nextLatest (committed forward : Bool) (previous fresh : List Nat) : List Nat :=
  if committed && forward then fresh else previous

theorem completed_forward_replaces (previous fresh : List Nat) :
    nextLatest true true previous fresh = fresh := rfl

theorem backward_keeps_latest (committed : Bool) (previous fresh : List Nat) :
    nextLatest committed false previous fresh = previous := by
  cases committed <;> rfl

theorem uncommitted_barrier_keeps_latest (forward : Bool) (previous fresh : List Nat) :
    nextLatest false forward previous fresh = previous := rfl

theorem later_forward_discards_candidate_history (older previous fresh : List Nat) :
    nextLatest true true (nextLatest true true older previous) fresh = fresh := rfl

theorem confirmed_member (confirmed latest : List Nat) (limited : Bool) (id : Nat) :
    Entry.mk id false ∈ report limited confirmed latest ↔ id ∈ confirmed := by
  cases limited <;> simp [report, confirmedEntries, provisionalEntries]

theorem provisional_member (confirmed latest : List Nat) (id : Nat) :
    Entry.mk id true ∈ report true confirmed latest ↔
      id ∈ latest ∧ id ∉ confirmed := by
  simp [report, confirmedEntries, provisionalEntries]

theorem no_provisional_before_limit (confirmed latest : List Nat) (id : Nat) :
    Entry.mk id true ∉ report false confirmed latest := by
  simp [report, confirmedEntries]

theorem confirmed_wins (confirmed latest : List Nat) (id : Nat)
    (known : id ∈ confirmed) : Entry.mk id true ∉ report true confirmed latest := by
  simp [provisional_member, known]

theorem discarded_candidate_absent (confirmed latest : List Nat) (id : Nat)
    (notLatest : id ∉ latest) (notConfirmed : id ∉ confirmed) :
    ∀ entry ∈ report true confirmed latest, entry.id ≠ id := by
  intro entry present
  cases entry with
  | mk value provisional =>
    cases provisional
    · have h := (confirmed_member confirmed latest true value).mp present
      intro eq; exact notConfirmed (eq ▸ h)
    · have h := (provisional_member confirmed latest value).mp present
      intro eq; exact notLatest (eq ▸ h.1)

theorem empty_latest_preserves_confirmed (confirmed : List Nat) :
    report true confirmed [] = confirmedEntries confirmed := by
  simp [report, provisionalEntries]

example : report true [1, 1] [1, 2, 2] = [⟨1, false⟩, ⟨2, true⟩] := by decide
example : report true [1] [] = [⟨1, false⟩] := by decide
example : report false [1] [2] = [⟨1, false⟩] := by decide

end Run11Reports

#print axioms Run11Reports.confirmed_member
#print axioms Run11Reports.provisional_member
#print axioms Run11Reports.no_provisional_before_limit
#print axioms Run11Reports.confirmed_wins
#print axioms Run11Reports.discarded_candidate_absent
#print axioms Run11Reports.empty_latest_preserves_confirmed
#print axioms Run11Reports.completed_forward_replaces
#print axioms Run11Reports.backward_keeps_latest
#print axioms Run11Reports.uncommitted_barrier_keeps_latest
#print axioms Run11Reports.later_forward_discards_candidate_history
