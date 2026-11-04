import Std
import Geometry

namespace DemandTriePrefix
open LoopFragments.Geometry

variable {fields : Nat}

/-- Ordinary longest common prefix length, evaluated against every compatible demand. -/
def lcp : Path fields → Path fields → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | first :: rest, head :: tail => if first = head then lcp rest tail + 1 else 0

def maxLcp (raw : Path fields) : List (Path fields) → Nat
  | [] => 0
  | demand :: rest => max (lcp raw demand) (maxLcp raw rest)

theorem lcp_right_empty (raw : Path fields) : lcp raw [] = 0 := by
  cases raw <;> rfl

theorem lcp_append_prefix (path suffix : Path fields) : lcp (path ++ suffix) path = path.length := by
  induction path with
  | nil => exact lcp_right_empty suffix
  | cons head tail ih => simp [lcp, ih]

def referencePath (demands : List (Path fields)) (raw : Path fields) : Path fields :=
  raw.take (maxLcp raw demands + 1)

theorem max_lcp_empty_raw (demands : List (Path fields)) : maxLcp [] demands = 0 := by
  induction demands with
  | nil => rfl
  | cons _ _ ih => simp [maxLcp, lcp, ih]

theorem max_lcp_cons (first : Field fields) (rest : Path fields) (demands : List (Path fields)) :
    maxLcp (first :: rest) demands =
      if children first demands = [] then 0 else maxLcp rest (children first demands) + 1 := by
  induction demands with
  | nil => rfl
  | cons demand later ih =>
    cases demand with
    | nil =>
      rw [children, maxLcp, lcp, Nat.zero_max]
      exact ih
    | cons head tail =>
      by_cases same : first = head
      · subst head
        cases child : children first later with
        | nil => simp [children, maxLcp, lcp, ih, child]
        | cons next suffix => simp [children, maxLcp, lcp, ih, child, Nat.succ_max_succ]
      · simpa [children, maxLcp, lcp, same] using ih

theorem node_walk_length_equals_lcp_reference (demands : List (Path fields)) (raw : Path fields) :
    (triePrefix demands raw).length = min raw.length (maxLcp raw demands + 1) := by
  induction raw generalizing demands with
  | nil => rfl
  | cons first rest ih =>
    by_cases missing : children first demands = []
    · simp [triePrefix, missing, max_lcp_cons]
    · simp only [triePrefix, List.length_cons, max_lcp_cons, if_neg missing]
      rw [ih]
      omega

theorem node_walk_equals_full_lcp_reference (demands : List (Path fields)) (raw : Path fields) :
    triePrefix demands raw = referencePath demands raw := by
  have isPref := List.prefix_iff_eq_take.mp (triePrefix_is_prefix demands raw)
  rw [node_walk_length_equals_lcp_reference] at isPref
  unfold referencePath
  by_cases bound : raw.length ≤ maxLcp raw demands + 1
  · rw [List.take_of_length_le bound]
    simpa only [Nat.min_eq_left bound, List.take_length] using isPref
  · have right : maxLcp raw demands + 1 ≤ raw.length := by omega
    simpa only [Nat.min_eq_right right] using isPref

theorem reference_is_prefix (demands : List (Path fields)) (raw : Path fields) :
    (referencePath demands raw).IsPrefix raw := List.take_prefix _ _

theorem reference_depth_bound (demands : List (Path fields)) (raw : Path fields) :
    (referencePath demands raw).length ≤ maxDepth demands + 1 := by
  rw [← node_walk_equals_full_lcp_reference]
  exact triePrefix_depth_bound demands raw

theorem reference_idempotent (demands : List (Path fields)) (raw : Path fields) :
    referencePath demands (referencePath demands raw) = referencePath demands raw := by
  simp only [← node_walk_equals_full_lcp_reference, triePrefix_idempotent]

theorem requested_prefix_identity (demands : List (Path fields)) (requested : Path fields)
    (member : requested ∈ demands) (count : Nat) :
    referencePath demands (requested.take count) = requested.take count := by
  rw [← node_walk_equals_full_lcp_reference]
  exact requested_prefix_retained demands requested member count

theorem demand_lcp_le_max (raw demand : Path fields) (demands : List (Path fields))
    (member : demand ∈ demands) : lcp raw demand ≤ maxLcp raw demands := by
  induction demands with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst demand
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih later) (Nat.le_max_right _ _)

/-- Constructive boundary witness: choose by LCP with RAW, not global depth. -/
def boundaryWitness (raw : Path fields) : List (Path fields) → Option (Path fields)
  | [] => none
  | demand :: rest =>
      match boundaryWitness raw rest with
      | none => some demand
      | some later => if lcp raw demand < lcp raw later then some later else some demand

theorem boundary_witness_spec (raw : Path fields) (demands : List (Path fields)) :
    match boundaryWitness raw demands with
    | none => demands = []
    | some demand => demand ∈ demands ∧ lcp raw demand = maxLcp raw demands := by
  induction demands with
  | nil => rfl
  | cons head rest ih =>
    simp only [boundaryWitness]
    cases found : boundaryWitness raw rest with
    | none =>
      simp only [found] at ih ⊢
      subst rest
      simp [maxLcp]
    | some later =>
      simp only [found] at ih ⊢
      by_cases larger : lcp raw head < lcp raw later
      · simp only [if_pos larger]
        exact ⟨List.mem_cons_of_mem _ ih.1,
          by simp [maxLcp, ← ih.2, Nat.max_eq_right (Nat.le_of_lt larger)]⟩
      · simp only [if_neg larger]
        exact ⟨List.mem_cons_self,
          by simp [maxLcp, ← ih.2, Nat.max_eq_left (Nat.le_of_not_gt larger)]⟩

theorem lcp_is_shared_prefix (raw demand : Path fields) :
    (raw.take (lcp raw demand)).IsPrefix demand := by
  induction raw generalizing demand with
  | nil => exact ⟨demand, rfl⟩
  | cons first rest ih =>
    cases demand with
    | nil => exact ⟨[], rfl⟩
    | cons head tail =>
      by_cases same : first = head
      · subst head
        simpa [lcp] using ih tail
      · exact ⟨head :: tail, by simp [lcp, same]⟩

theorem boundary_witness_shares_maximum_prefix (raw demand : Path fields)
    (demands : List (Path fields)) (found : boundaryWitness raw demands = some demand) :
    demand ∈ demands ∧ (raw.take (maxLcp raw demands)).IsPrefix demand := by
  have witness := boundary_witness_spec raw demands
  simp only [found] at witness
  exact ⟨witness.1, by rw [← witness.2]; exact lcp_is_shared_prefix raw demand⟩

theorem take_prefix_of_le (raw : Path fields) (a b : Nat) (bound : a ≤ b) :
    (raw.take a).IsPrefix (raw.take b) := by
  have isPref := List.take_prefix a (raw.take b)
  simpa [List.take_take, Nat.min_eq_left bound] using isPref

/-- Retain the LCP and its next raw field for EVERY demand, including siblings. -/
theorem retained_first_distinguishing_field (raw demand : Path fields)
    (demands : List (Path fields)) (member : demand ∈ demands) :
    (raw.take (lcp raw demand + 1)).IsPrefix (referencePath demands raw) := by
  exact take_prefix_of_le raw _ _ (Nat.add_le_add_right (demand_lcp_le_max raw demand demands member) 1)

theorem requested_path_plus_one_bound (raw demand : Path fields) (demands : List (Path fields))
    (member : demand ∈ demands) (isPref : demand.IsPrefix raw) :
    (raw.take (demand.length + 1)).IsPrefix (referencePath demands raw) := by
  have same : lcp raw demand = demand.length := by
    obtain ⟨suffix, rfl⟩ := isPref
    exact lcp_append_prefix demand suffix
  simpa [same] using retained_first_distinguishing_field raw demand demands member

/-- Ordered terminal payloads are attached to exact paths, not replaced by a longest path. -/
def terminalPayloads {Payload : Type} (path : Path fields)
    (rows : List (Path fields × Payload)) : List Payload :=
  rows.filterMap (fun row => if row.1 = path then some row.2 else none)

theorem terminal_payload_append {Payload : Type} (path : Path fields)
    (left right : List (Path fields × Payload)) :
    terminalPayloads path (left ++ right) = terminalPayloads path left ++ terminalPayloads path right := by
  simp [terminalPayloads, List.filterMap_append]

theorem shorter_terminal_keeps_own_payload {Payload : Type} (short long : Path fields)
    (different : long ≠ short) (a b : Payload) :
    terminalPayloads short [(short, a), (long, b)] = [a] := by
  simp [terminalPayloads, different]

theorem longer_terminal_keeps_own_payload {Payload : Type} (short long : Path fields)
    (different : short ≠ long) (a b : Payload) :
    terminalPayloads long [(short, a), (long, b)] = [b] := by
  simp [terminalPayloads, different]

theorem same_raw_prefix_order (raw left right : Path fields) (leftPrefix : left.IsPrefix raw)
    (rightPrefix : right.IsPrefix raw) (bound : left.length ≤ right.length) : left.IsPrefix right := by
  rw [List.prefix_iff_eq_take.mp leftPrefix, List.prefix_iff_eq_take.mp rightPrefix]
  exact take_prefix_of_le raw _ _ bound

theorem take_kept_prefix (raw kept : Path fields) (isPref : kept.IsPrefix raw)
    (count : Nat) (bound : count ≤ kept.length) : kept.take count = raw.take count := by
  obtain ⟨suffix, same⟩ := isPref
  rw [← same, List.take_append_of_le_length bound]

/-- A strict cut certificate is GEOMETRIC, not an assumed C2 output equality.
    Prefix rows retain their first new field; other rows stay incomparable. -/
structure StrictCutCertificate (raw kept : Path fields) (demands : List (Path fields)) : Prop where
  keptPrefix : kept.IsPrefix raw
  shorter : kept.length < raw.length
  firstNew : ∀ demand ∈ demands, demand.IsPrefix raw → demand.length + 1 ≤ kept.length
  distinct : ∀ demand ∈ demands, ¬ demand.IsPrefix raw →
    ¬ demand.IsPrefix kept ∧ ¬ kept.IsPrefix demand

abbrev rowCertificate (raw kept demand : Path fields) : Prop :=
  (demand.IsPrefix raw → demand.length + 1 ≤ kept.length) ∧
  (¬ demand.IsPrefix raw → ¬ demand.IsPrefix kept ∧ ¬ kept.IsPrefix demand)

def certificateCheck (raw kept : Path fields) (demands : List (Path fields)) : Bool :=
  decide (kept.IsPrefix raw ∧ kept.length < raw.length) &&
    demands.all (fun demand => decide (rowCertificate raw kept demand))

theorem checked_certificate (raw kept : Path fields) (demands : List (Path fields))
    (checked : certificateCheck raw kept demands = true) : StrictCutCertificate raw kept demands := by
  obtain ⟨prefixAndDepth, rows⟩ := Bool.and_eq_true_iff.mp checked
  have base := of_decide_eq_true prefixAndDepth
  refine ⟨base.1, base.2, ?_, ?_⟩
  · intro demand member
    have cell := of_decide_eq_true ((List.all_eq_true.mp rows) demand member)
    exact cell.1
  · intro demand member
    have cell := of_decide_eq_true ((List.all_eq_true.mp rows) demand member)
    exact cell.2

inductive InitialTail where | exact | star | may deriving DecidableEq, Repr

/-- Matching concrete FULL base+mark and empty E have already been selected.
    This is the counted nonstatic EXACT/ANY C2 geometry subset. -/
def c2Key {bases marks : Nat} (demand : Path fields) (tail : Tail)
    (actual : Fact bases marks fields) : Option (Path fields × InitialTail) :=
  if actual.path = demand then
    match tail, actual.tail with
    | .may, .may => some (demand, .may)
    | _, _ => some (demand, .exact)
  else if demand.IsPrefix actual.path then
    match tail with
    | .exact => none
    | .may => some (actual.path.take (demand.length + 1),
        if actual.tail = .exact ∧ demand.length + 1 = actual.path.length then .exact else .star)
  else if actual.path.IsPrefix demand ∧ actual.tail = .may then
    some (demand, match tail with | .exact => .exact | .may => .may)
  else none

def initialLayer {bases marks : Nat} (tail : InitialTail) (actual : Fact bases marks fields) : Layer :=
  if actual.layer = .demand ∨ actual.tail = .may then .demand
  else match tail with | .exact => .normal | .star | .may => .demand

def c2Image {bases marks : Nat} (demand : Path fields) (tail : Tail)
    (actual : Fact bases marks fields) : Option ((Path fields × InitialTail) × Layer) :=
  (c2Key demand tail actual).map fun key => (key, initialLayer key.2 actual)

theorem star_initial_layer {bases marks : Nat} (actual : Fact bases marks fields) :
    initialLayer .star actual = .demand := by
  unfold initialLayer
  split <;> rfl

/-- A matching ANY demand emits one constant MAY/DEMAND key from every
    MAY ancestor, including equality. This is a local scalar cell theorem. -/
theorem any_demand_may_ancestor_constant {bases marks : Nat} (actual : Fact bases marks fields)
    (demand : Path fields) (mayActual : actual.tail = .may) (ancestor : actual.path.IsPrefix demand) :
    c2Image demand .may actual = some ((demand, .may), .demand) := by
  by_cases same : actual.path = demand
  · simp [c2Image, c2Key, same, mayActual, initialLayer]
  · have notReverse : ¬ demand.IsPrefix actual.path := by
      intro reversePrefix
      have lengths := Nat.le_antisymm ancestor.length_le reversePrefix.length_le
      have equal := List.prefix_iff_eq_take.mp ancestor
      apply same
      simpa [lengths] using equal
    simp [c2Image, c2Key, same, notReverse, ancestor, mayActual, initialLayer]

theorem strict_certificate_preserves_c2 {bases marks : Nat} (actual : Fact bases marks fields)
    (kept : Path fields) (demands : List (Path fields))
    (certificate : StrictCutCertificate actual.path kept demands)
    (demand : Path fields) (member : demand ∈ demands) (tail : Tail) :
    c2Image demand tail {actual with path := kept, tail := .may, layer := .demand} =
      c2Image demand tail actual := by
  have shorter := certificate.shorter
  by_cases rowPrefix : demand.IsPrefix actual.path
  · have newBound := certificate.firstNew demand member rowPrefix
    have demandKept : demand.IsPrefix kept := same_raw_prefix_order actual.path demand kept
      rowPrefix certificate.keptPrefix (by omega)
    have rawDifferent : actual.path ≠ demand := by
      intro same
      have sameLength := congrArg List.length same
      omega
    have keptDifferent : kept ≠ demand := by
      intro same
      have sameLength := congrArg List.length same
      omega
    have endDifferent : demand.length + 1 ≠ actual.path.length := by omega
    have takeSame := take_kept_prefix actual.path kept certificate.keptPrefix _ newBound
    cases tail with
    | exact => simp [c2Image, c2Key, rawDifferent, keptDifferent, rowPrefix, demandKept]
    | may => simp [c2Image, c2Key, rawDifferent, keptDifferent, rowPrefix, demandKept,
        endDifferent, takeSame, star_initial_layer]
  · obtain ⟨notDemandKept, notKeptDemand⟩ := certificate.distinct demand member rowPrefix
    have rawDifferent : actual.path ≠ demand := by
      intro same
      apply rowPrefix
      rw [same]
      exact ⟨[], by simp⟩
    have keptDifferent : kept ≠ demand := by
      intro same
      apply notDemandKept
      rw [same]
      exact ⟨[], by simp⟩
    have notRawDemand : ¬ actual.path.IsPrefix demand := by
      intro isPref
      exact notKeptDemand (certificate.keptPrefix.trans isPref)
    simp [c2Image, c2Key, rawDifferent, keptDifferent, rowPrefix, notDemandKept, notKeptDemand, notRawDemand]

/-- Exact identity never forces MAY or changes NORMAL evidence. -/
def certifiedProject {bases marks : Nat} (actual : Fact bases marks fields) (kept : Path fields) :
    Fact bases marks fields :=
  if kept = actual.path then actual
  else {actual with path := kept, tail := .may, layer := .demand}

theorem certified_project_c2 {bases marks : Nat} (actual : Fact bases marks fields)
    (kept : Path fields) (demands : List (Path fields))
    (certificate : kept = actual.path ∨ StrictCutCertificate actual.path kept demands)
    (demand : Path fields) (member : demand ∈ demands) (tail : Tail) :
    c2Image demand tail (certifiedProject actual kept) = c2Image demand tail actual := by
  cases certificate with
  | inl same => simp [certifiedProject, same]
  | inr strict =>
    have different : kept ≠ actual.path := by
      intro same
      have sameLength := congrArg List.length same
      have shorter := strict.shorter
      omega
    rw [certifiedProject, if_neg different]
    exact strict_certificate_preserves_c2 actual kept demands strict demand member tail

theorem certified_project_base {bases marks : Nat} (actual : Fact bases marks fields) (kept : Path fields) :
    (certifiedProject actual kept).base = actual.base := by unfold certifiedProject; split <;> rfl

theorem certified_project_mark {bases marks : Nat} (actual : Fact bases marks fields) (kept : Path fields) :
    (certifiedProject actual kept).mark = actual.mark := by unfold certifiedProject; split <;> rfl

theorem certified_project_protection {bases marks : Nat} (actual : Fact bases marks fields) (kept : Path fields) :
    (certifiedProject actual kept).protection = actual.protection := by unfold certifiedProject; split <;> rfl

/-- One demand sharing m raw fields supplies the SAME ANY key for the entire
    earlier range, provided those budgets really shorten raw. -/
theorem shared_prefix_constant_any_range {bases marks : Nat} (actual : Fact bases marks fields)
    (demand : Path fields) (m budget : Nat) (shared : (actual.path.take m).IsPrefix demand)
    (earlier : budget ≤ m) (shortens : budget < actual.path.length) :
    c2Image demand .may (certifiedProject actual (actual.path.take budget)) =
      some ((demand, .may), .demand) := by
  have different : actual.path.take budget ≠ actual.path := by
    intro same
    have bound := List.length_take_le budget actual.path
    have equal := congrArg List.length same
    omega
  rw [certifiedProject, if_neg different]
  apply any_demand_may_ancestor_constant _ demand rfl
  exact (take_prefix_of_le actual.path budget m earlier).trans shared

theorem proper_projection_is_any_demand {bases marks : Nat} (actual : Fact bases marks fields)
    (kept : Path fields) (different : kept ≠ actual.path) :
    (certifiedProject actual kept).tail = .may ∧ (certifiedProject actual kept).layer = .demand := by
  simp [certifiedProject, different]

def c2Family {bases marks : Nat} (rows : List (Path fields × Tail))
    (actual : Fact bases marks fields) : List ((Path fields × InitialTail) × Layer) :=
  rows.filterMap (fun row => c2Image row.1 row.2 actual)

theorem shared_prefix_witness_in_family {bases marks : Nat} (actual : Fact bases marks fields)
    (rows : List (Path fields × Tail)) (demand : Path fields) (member : (demand, Tail.may) ∈ rows)
    (m budget : Nat) (shared : (actual.path.take m).IsPrefix demand)
    (earlier : budget ≤ m) (shortens : budget < actual.path.length) :
    ((demand, InitialTail.may), Layer.demand) ∈
      c2Family rows (certifiedProject actual (actual.path.take budget)) := by
  apply List.mem_filterMap.mpr
  exact ⟨(demand, Tail.may), member,
    shared_prefix_constant_any_range actual demand m budget shared earlier shortens⟩

/-- The complete ordered per-row image (including layers) is preserved, not only
    Boolean nonemptiness. Rows are already filtered for native compatible owners. -/
theorem complete_c2_image_preserved {bases marks : Nat} (actual : Fact bases marks fields)
    (kept : Path fields) (rows : List (Path fields × Tail))
    (certificate : kept = actual.path ∨ StrictCutCertificate actual.path kept (rows.map Prod.fst)) :
    rows.map (fun row => c2Image row.1 row.2 (certifiedProject actual kept)) =
      rows.map (fun row => c2Image row.1 row.2 actual) := by
  apply List.map_congr_left
  intro row member
  exact certified_project_c2 actual kept _ certificate row.1 (List.mem_map_of_mem member) row.2

/-- Search remains the first accepting native candidate in its original order. -/
def firstAccepted (accept : Nat → Bool) : List Nat → Option Nat
  | [] => none
  | budget :: rest => if accept budget then some budget else firstAccepted accept rest

theorem skip_only_certified_rejected_prefix (accept : Nat → Bool) (earlier later : List Nat)
    (rejects : ∀ budget ∈ earlier, accept budget = false) :
    firstAccepted accept (earlier ++ later) = firstAccepted accept later := by
  induction earlier with
  | nil => rfl
  | cons budget rest ih =>
    have rejected := rejects budget List.mem_cons_self
    simp only [List.cons_append, firstAccepted, rejected, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun other member => rejects other (List.mem_cons_of_mem budget member))

theorem absent_witness_rejects_range {Key : Type} (accept : Nat → Bool)
    (earlier : List Nat) (baseline : List Key) (family : Nat → List Key) (witness : Key)
    (absent : witness ∉ baseline) (present : ∀ budget ∈ earlier, witness ∈ family budget)
    (noNewOnAccept : ∀ budget, accept budget = true → ∀ key ∈ family budget, key ∈ baseline) :
    ∀ budget ∈ earlier, accept budget = false := by
  intro budget member
  cases answer : accept budget with
  | false => rfl
  | true => exact False.elim (absent (noNewOnAccept budget answer witness (present budget member)))

theorem skip_absent_witness_range {Key : Type} (accept : Nat → Bool)
    (earlier later : List Nat) (baseline : List Key) (family : Nat → List Key) (witness : Key)
    (absent : witness ∉ baseline) (present : ∀ budget ∈ earlier, witness ∈ family budget)
    (noNewOnAccept : ∀ budget, accept budget = true → ∀ key ∈ family budget, key ∈ baseline) :
    firstAccepted accept (earlier ++ later) = firstAccepted accept later := by
  exact skip_only_certified_rejected_prefix accept earlier later
    (absent_witness_rejects_range accept earlier baseline family witness absent present noNewOnAccept)

def userRaw : Path 5 := [0, 1, 2, 3]
def nestedDemands : List (Path 5) := [[0], [0, 1]]
def siblingDemands : List (Path 5) := [[0], [0, 1, 4]]

theorem user_nested_fghk_to_fgh : referencePath nestedDemands userRaw = [0, 1, 2] := rfl

theorem user_sibling_fgz_retains_h : referencePath siblingDemands userRaw = [0, 1, 2] := rfl

theorem user_nested_certificate :
    certificateCheck userRaw [0, 1, 2] nestedDemands = true := by decide

theorem user_sibling_certificate :
    certificateCheck userRaw [0, 1, 2] siblingDemands = true := by decide

theorem user_nested_any_demand_image {bases marks : Nat} (actual : Fact bases marks 5)
    (raw : actual.path = userRaw) (demand : Path 5) (member : demand ∈ nestedDemands) (tail : Tail) :
    c2Image demand tail (certifiedProject actual [0, 1, 2]) = c2Image demand tail actual := by
  apply certified_project_c2 actual [0, 1, 2] nestedDemands _ demand member tail
  apply Or.inr
  rw [raw]
  exact checked_certificate _ _ _ user_nested_certificate

theorem nested_terminal_payloads_both_survive :
    terminalPayloads ([0] : Path 5) [([0], 17), ([0, 1], 29)] = [17] ∧
    terminalPayloads ([0, 1] : Path 5) [([0], 17), ([0, 1], 29)] = [29] := by decide

theorem deepest_matching_terminal_is_not_enough :
    referencePath ([[0], [0, 1, 4]] : List (Path 5)) [0, 1, 2, 3] ≠
      referencePath ([[0]] : List (Path 5)) [0, 1, 2, 3] := by decide

theorem one_global_longest_path_is_not_enough :
    referencePath ([[0], [0, 1], [4, 4, 4, 4]] : List (Path 5)) [0, 1, 2, 3] ≠
      referencePath ([[4, 4, 4, 4]] : List (Path 5)) [0, 1, 2, 3] := by decide

def mayCounterexample : Fact 1 1 5 := ⟨0, 0, [0, 1], .may, .demand, false⟩

/-- Preserving an image does not prove that the trie proposes the first native cut. -/
theorem may_geometry_is_not_always_minimal :
    referencePath ([[0, 1]] : List (Path 5)) [0, 1] = [0, 1] ∧
    c2Image [0, 1] .may (certifiedProject mayCounterexample [0]) =
      c2Image [0, 1] .may mayCounterexample := by decide

end DemandTriePrefix
