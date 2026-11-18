namespace NativeOutputFilter

-- A destination is from the ordinary post-statement CFG delivery. This
-- model counts semantic events, excluding the processing/work counters.
inductive Destination where
  | statement (touches hasOutgoing hasConjunction hasSource hasStatic : Bool)
  | call | boundary
  deriving DecidableEq

inductive Event where
  | data | conjunction | source | staticEffect | call | boundary
  deriving DecidableEq

def ordinary : Destination → List Event
  | .statement touches outgoing conjunction source static =>
    (if !touches || outgoing then [.data] else []) ++
      (if conjunction then [.conjunction] else []) ++
      (if source then [.source] else []) ++
      (if static then [.staticEffect] else [])
  | .call => [.call]
  | .boundary => [.boundary]

def overwritten : Destination → Bool
  | .statement touches outgoing conjunction source static =>
    touches && !outgoing && !conjunction && !source && !static
  | _ => false

def skipOutput (normalCover : Bool) (destinations : List Destination) : Bool :=
  normalCover && destinations.all overwritten

theorem overwritten_destination_has_no_result
    (dead : overwritten dest = true) : ordinary dest = [] := by
  cases dest with
  | call => contradiction
  | boundary => contradiction
  | statement touches outgoing conjunction source static =>
    cases touches <;> cases outgoing <;> cases conjunction <;>
      cases source <;> cases static <;> simp_all [overwritten, ordinary]

theorem skipped_deliveries_have_no_semantic_events
    (skipped : skipOutput cover destinations = true) :
    destinations.flatMap ordinary = [] := by
  have allDead := (Bool.and_eq_true_iff.mp skipped).2
  simp only [List.flatMap_eq_nil_iff]
  intro dest present
  exact overwritten_destination_has_no_result (List.all_eq_true.mp allDead _ present)

def overwrite : Destination := .statement true false false false false

theorem covered_value_can_be_omitted_before_a_full_overwrite :
    skipOutput true [overwrite] = true := by decide

theorem one_live_successor_or_boundary_keeps_the_value :
    skipOutput true [overwrite,.call] = false ∧
    skipOutput true [overwrite,.boundary] = false ∧
    skipOutput true [overwrite,.statement true true false false false] = false := by decide

theorem a_rule_can_read_even_when_the_plain_transfer_has_no_output :
    skipOutput true [.statement true false true false false] = false ∧
    skipOutput true [.statement true false false true false] = false ∧
    skipOutput true [.statement true false false false true] = false := by decide

theorem absence_of_a_native_cover_keeps_the_candidate :
    skipOutput false destinations = false := rfl

end NativeOutputFilter
