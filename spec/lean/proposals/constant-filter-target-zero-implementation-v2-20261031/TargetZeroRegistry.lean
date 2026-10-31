import SelectedCore

/-!
Constructive registry laws for the selected location/rule ReportId design.
The input location is a globally unique sink location, not a local line number.
These laws describe one persistent append-only catalog; adapters must preserve
that catalog/identity across caches and both analysis directions.
-/
namespace TargetZeroRegistry
open SelectedCore
set_option autoImplicit false

def keyAt : List SinkKey → Nat → Option SinkKey
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: rest, n + 1 => keyAt rest n

theorem intern_points_to_key (catalog : List SinkKey) (key : SinkKey) (id : Nat)
    (found : internSink catalog key = some id) : keyAt catalog id = some key := by
  induction catalog generalizing id with
  | nil => cases found
  | cons head rest ih =>
      cases same : (key == head) with
      | false =>
          simp only [internSink, same, Bool.false_eq_true, ↓reduceIte] at found
          cases result : internSink rest key with
          | none => simp only [result, Option.map_none] at found; cases found
          | some prior =>
              simp only [result, Option.map_some] at found
              have equal := Option.some.inj found
              subst id
              exact ih prior result
      | true =>
          simp only [internSink, same, ↓reduceIte] at found
          have equal := Option.some.inj found
          subst id
          have keyEqual : key = head := of_decide_eq_true same
          exact congrArg some keyEqual.symm

theorem distinct_keys_have_distinct_ids (catalog : List SinkKey) (left right : SinkKey)
    (leftId rightId : Nat) (leftFound : internSink catalog left = some leftId)
    (rightFound : internSink catalog right = some rightId) (different : left ≠ right) :
    leftId ≠ rightId := by
  intro equal
  subst rightId
  have leftAt := intern_points_to_key catalog left leftId leftFound
  have rightAt := intern_points_to_key catalog right leftId rightFound
  exact different (Option.some.inj (leftAt.symm.trans rightAt))

theorem append_preserves_existing_id (catalog extra : List SinkKey) (key : SinkKey)
    (id : Nat) (found : internSink catalog key = some id) :
    internSink (catalog ++ extra) key = some id := by
  induction catalog generalizing id with
  | nil => cases found
  | cons head rest ih =>
      cases same : (key == head) with
      | false =>
          simp only [internSink, same, Bool.false_eq_true, ↓reduceIte] at found
          cases result : internSink rest key with
          | none => simp only [result, Option.map_none] at found; cases found
          | some prior =>
              simp only [result, Option.map_some] at found
              have equal := Option.some.inj found
              subst id
              simp only [List.cons_append, internSink, same, Bool.false_eq_true, ↓reduceIte]
              exact congrArg (Option.map Nat.succ) (ih prior result)
      | true =>
          simp only [internSink, same, ↓reduceIte] at found
          simpa only [List.cons_append, internSink, same, ↓reduceIte] using found

theorem append_missing_key_gets_fresh_id (catalog : List SinkKey) (key : SinkKey)
    (missing : internSink catalog key = none) :
    internSink (catalog ++ [key]) key = some catalog.length := by
  induction catalog with
  | nil =>
      have self : (key == key) = true := decide_eq_true rfl
      simp only [List.nil_append, internSink, self, ↓reduceIte, List.length_nil]
  | cons head rest ih =>
      cases same : (key == head) with
      | false =>
          have restMissing : internSink rest key = none := by
            cases result : internSink rest key with
            | none => rfl
            | some prior =>
                simp only [internSink, same, Bool.false_eq_true, ↓reduceIte, result,
                  Option.map_some] at missing
                cases missing
          simp only [List.cons_append, internSink, same, Bool.false_eq_true, ↓reduceIte,
            ih restMissing, Option.map_some, List.length_cons]
      | true =>
          simp only [internSink, same, ↓reduceIte] at missing
          cases missing

/-- Total registration returns an executable id whose catalog lookup succeeds. -/
def registeredIdWitness (catalog : List SinkKey) (key : SinkKey) :
    {idAndCatalog : Nat × List SinkKey //
      idAndCatalog = registerSink catalog key ∧
      internSink idAndCatalog.2 key = some idAndCatalog.1} := by
  cases result : internSink catalog key with
  | none =>
      exact ⟨(catalog.length, catalog ++ [key]), by simp only [registerSink, result],
        append_missing_key_gets_fresh_id catalog key result⟩
  | some id => exact ⟨(id, catalog), by simp only [registerSink, result], result⟩

#print axioms intern_points_to_key
#print axioms distinct_keys_have_distinct_ids
#print axioms append_preserves_existing_id
#print axioms append_missing_key_gets_fresh_id
#print axioms registeredIdWitness

end TargetZeroRegistry
