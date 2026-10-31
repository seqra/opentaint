import Std

/-!
Later-run method support, abstracted from production e090118e5.

Adapter boundaries (assumptions, not theorems of the Kotlin engine):
* The incoming explicit rows are the immutable completed preceding handoff.
* Run >= 3: no virtual static completion or shared static carry. Run-1 point
  resumes and mark answers are absent. Roots/direct ZERO deliveries start ZERO.
* Every nonzero initial is delivered by local C2 from an incoming row. `emits`
  stands for the full marked/field-bounded RestrictedInitialPolicy relation.
* Every ordinary publication has a local paired C5 witness. `restricts` stands
  for the complete image, mark, field, layer and protection checks. No payload
  theorem is assumed or proved here. Backward ZERO is the sole bypass.
* Projection, normalization, exact dedup and builder ownership preserve owner
  keys. `project` models projection before dedup; dedup cannot add support.
* Summary premises have valid nonempty shape. Pattern tags abstract canonical
  payloads: zero is ZERO. These tags do not prove any AP normalization result.

Source binding:
  engine/RunMethodCallServices.kt:318-348,352-393
  engine/RestrictedInitialEmission.kt:6-27
  engine/RunMethodAnalyzer.kt:120-125,180-195,370-371,791-805
  store/DemandStore.kt:20-24,44-58,80-105,137,145-194
  ap/Demand.kt:90-96; driver/HandOff.kt:143-162

No global iteration/no-loss, AP narrowing, whole-program closure or production
speed claim follows. The chain is an executable identity-binding seed protocol
instance, not an executed Java/production analyzer fixture.
-/
namespace MethodSupport

inductive Direction where
  | forward | backward
  deriving DecidableEq, Repr

inductive Initial where
  | zero
  | fact (shape : Nat)
  deriving DecidableEq, Repr

inductive Premise where
  | zero
  | singleton (shape : Nat)
  | conjunction (left right : Nat)
  deriving DecidableEq, Repr

inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr

structure Row where
  owner : Nat
  entry : Nat
  exit : Option Nat
  deriving DecidableEq, Repr

structure Summary where
  owner : Nat
  premise : Premise
  result : Nat
  layer : Layer
  deriving DecidableEq, Repr

/-- Explicit method support; ZERO demand is an implicit family, outside rows. -/
def Support (rows : List Row) (owner : Nat) : Prop :=
  ∃ row, row ∈ rows ∧ row.owner = owner

/-- The local C2 boundary. `emits` contains all actual AP emission checks. -/
inductive Admitted (rows : List Row) (emits : Row → Initial → Prop)
    (owner : Nat) : Initial → Prop where
  | zero : Admitted rows emits owner .zero
  | c2 (row : Row) (initial : Initial) (localRow : row ∈ rows)
      (sameOwner : row.owner = owner) (emitted : emits row initial) :
      Admitted rows emits owner initial

def Analysed (rows : List Row) (emits : Row → Initial → Prop) (owner : Nat) : Prop :=
  ∃ initial, Admitted rows emits owner initial ∧ initial ≠ .zero

theorem admitted_nonzero_has_local_row {rows : List Row} {emits : Row → Initial → Prop}
    {owner : Nat} {initial : Initial} (h : Admitted rows emits owner initial)
    (nonzero : initial ≠ .zero) : Support rows owner := by
  cases h with
  | zero => exact False.elim (nonzero rfl)
  | c2 row _ localRow sameOwner _ => exact ⟨row, localRow, sameOwner⟩

theorem analysed_subset_incoming {rows : List Row} {emits : Row → Initial → Prop}
    {owner : Nat} (h : Analysed rows emits owner) : Support rows owner := by
  obtain ⟨initial, admitted, nonzero⟩ := h
  exact admitted_nonzero_has_local_row admitted nonzero

theorem no_local_row_means_zero_only {rows : List Row} {emits : Row → Initial → Prop}
    {owner : Nat} (absent : ¬ Support rows owner) : ¬ Analysed rows emits owner := by
  intro h
  exact absent (analysed_subset_incoming h)

/-- Local paired C5, or the selected balanced backward ZERO exception. -/
inductive Published (direction : Direction) (rows : List Row)
    (restricts : Row → Summary → Prop) (summary : Summary) : Prop where
  | ordinary (row : Row) (localRow : row ∈ rows) (sameOwner : row.owner = summary.owner)
      (paired : row.exit ≠ none) (restricted : restricts row summary) :
      Published direction rows restricts summary
  | backwardZero (backward : direction = .backward) (zero : summary.premise = .zero) :
      Published direction rows restricts summary

/-- F77 raw selection. A selected NORMAL conjunction remains NORMAL. -/
def Selected (direction : Direction) (summary : Summary) : Prop :=
  summary.layer = .demand ∨
  (∃ a b, summary.premise = .conjunction a b) ∨
  (direction = .backward ∧ summary.premise = .zero)

def members : Premise → List Nat
  | .zero => [0]
  | .singleton shape => [shape + 1]
  | .conjunction a b => [a + 1, b + 1]

/-- Handoff projection uses the summary's owner, with entry-only backward ZERO. -/
def project (direction : Direction) (summary : Summary) : List Row :=
  match direction, summary.premise with
  | .backward, .zero => [⟨summary.owner, summary.result, none⟩]
  | _, premise => (members premise).map fun member =>
      ⟨summary.owner, summary.result, some member⟩

/-- The builder suppresses precisely the virtual ZERO entry with no paired exit. -/
def Explicit (row : Row) : Prop := ¬ (row.entry = 0 ∧ row.exit = none)

instance (row : Row) : Decidable (Explicit row) :=
  inferInstanceAs (Decidable (¬ (row.entry = 0 ∧ row.exit = none)))

structure Exported (direction : Direction) (rows : List Row)
    (restricts : Row → Summary → Prop) (summary : Summary) (row : Row) : Prop where
  published : Published direction rows restricts summary
  selected : Selected direction summary
  projected : row ∈ project direction summary
  explicit : Explicit row

def Outgoing (direction : Direction) (rows : List Row)
    (restricts : Row → Summary → Prop) (owner : Nat) : Prop :=
  ∃ summary row, Exported direction rows restricts summary row ∧ row.owner = owner

theorem projection_preserves_owner {direction : Direction} {summary : Summary} {row : Row}
    (h : row ∈ project direction summary) : row.owner = summary.owner := by
  cases direction with
  | forward =>
      simp only [project] at h
      obtain ⟨member, _, equal⟩ := List.mem_map.mp h
      exact (congrArg Row.owner equal).symm
  | backward =>
      cases hp : summary.premise with
      | zero =>
          simp [project, hp] at h
          subst row
          rfl
      | singleton shape =>
          simp only [project, hp] at h
          obtain ⟨member, _, equal⟩ := List.mem_map.mp h
          exact (congrArg Row.owner equal).symm
      | conjunction a b =>
          simp only [project, hp] at h
          obtain ⟨member, _, equal⟩ := List.mem_map.mp h
          exact (congrArg Row.owner equal).symm

theorem ordinary_publication_has_local_owner {direction : Direction} {rows : List Row}
    {restricts : Row → Summary → Prop} {summary : Summary}
    (h : Published direction rows restricts summary)
    (notBypass : ¬ (direction = .backward ∧ summary.premise = .zero)) :
    Support rows summary.owner := by
  cases h with
  | ordinary row localRow sameOwner _ _ => exact ⟨row, localRow, sameOwner⟩
  | backwardZero backward zero => exact False.elim (notBypass ⟨backward, zero⟩)

theorem forward_publication_has_local_owner {rows : List Row}
    {restricts : Row → Summary → Prop} {summary : Summary}
    (h : Published .forward rows restricts summary) : Support rows summary.owner := by
  apply ordinary_publication_has_local_owner h
  intro impossible
  cases impossible.1

theorem forward_outgoing_subset_incoming {rows : List Row}
    {restricts : Row → Summary → Prop} {owner : Nat}
    (h : Outgoing .forward rows restricts owner) : Support rows owner := by
  obtain ⟨summary, row, exported, sameOwner⟩ := h
  have localOwner := forward_publication_has_local_owner exported.published
  have projectedOwner := projection_preserves_owner exported.projected
  rw [← projectedOwner, sameOwner] at localOwner
  exact localOwner

theorem new_backward_publication_is_zero {rows : List Row}
    {restricts : Row → Summary → Prop} {summary : Summary}
    (h : Published .backward rows restricts summary)
    (absent : ¬ Support rows summary.owner) : summary.premise = .zero := by
  cases h with
  | ordinary row localRow sameOwner _ _ => exact False.elim (absent ⟨row, localRow, sameOwner⟩)
  | backwardZero _ zero => exact zero

theorem new_backward_outgoing_has_zero_witness {rows : List Row}
    {restricts : Row → Summary → Prop} {owner : Nat}
    (h : Outgoing .backward rows restricts owner) (absent : ¬ Support rows owner) :
    ∃ summary row, Exported .backward rows restricts summary row ∧
      summary.owner = owner ∧ summary.premise = .zero := by
  obtain ⟨summary, row, exported, sameOwner⟩ := h
  have projectedOwner := projection_preserves_owner exported.projected
  have ownerEq : summary.owner = owner := projectedOwner.symm.trans sameOwner
  have absentSummary : ¬ Support rows summary.owner := by simpa [ownerEq] using absent
  exact ⟨summary, row, exported, ownerEq,
    new_backward_publication_is_zero exported.published absentSummary⟩

theorem new_backward_outgoing_is_zero_only {rows : List Row}
    {restricts : Row → Summary → Prop} {emits : Row → Initial → Prop} {owner : Nat}
    (_outgoing : Outgoing .backward rows restricts owner) (absent : ¬ Support rows owner) :
    ¬ Analysed rows emits owner := no_local_row_means_zero_only absent

theorem normal_backward_zero_selected (owner result : Nat) :
    Selected .backward ⟨owner, .zero, result, .normal⟩ :=
  Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem normal_forward_singleton_not_selected (owner shape result : Nat) :
    ¬ Selected .forward ⟨owner, .singleton shape, result, .normal⟩ := by
  simp [Selected]

theorem entry_only_cannot_witness_c5 (_direction : Direction) (rows : List Row)
    (restricts : Row → Summary → Prop) (summary : Summary) (row : Row)
    (entryOnly : row.exit = none) :
    ¬ (row ∈ rows ∧ row.owner = summary.owner ∧ row.exit ≠ none ∧ restricts row summary) := by
  intro h
  exact h.2.2.1 entryOnly

/-- NORMAL backward ZERO seed paths are deliberately ineligible for persistence. -/
def NativeRecord (direction : Direction) (summary : Summary) : Prop :=
  summary.layer = .normal ∧
  (match summary.premise with | .conjunction _ _ => False | _ => True) ∧
  ¬ (direction = .backward ∧ summary.premise = .zero)

theorem backward_zero_not_native_record (owner result : Nat) (layer : Layer) :
    ¬ NativeRecord .backward ⟨owner, .zero, result, layer⟩ := by
  simp [NativeRecord]

/-- Exact canonical row deduplication, with no owner-generating operation. -/
def dedupRows : List Row → List Row
  | [] => []
  | row :: rest => if row ∈ rest then dedupRows rest else row :: dedupRows rest

theorem dedup_membership (row : Row) (rows : List Row) :
    row ∈ dedupRows rows ↔ row ∈ rows := by
  induction rows with
  | nil => simp [dedupRows]
  | cons head rest ih =>
      by_cases present : head ∈ rest
      · simp [dedupRows, present, ih]
        intro same
        simpa [same] using present
      · simp [dedupRows, present, ih]

theorem dedup_support_iff (rows : List Row) (owner : Nat) :
    Support (dedupRows rows) owner ↔ Support rows owner := by
  simp only [Support, dedup_membership]

theorem dedup_unchanged_if_distinct_owners (rows : List Row)
    (distinct : (rows.map Row.owner).Nodup) : dedupRows rows = rows := by
  induction rows with
  | nil => rfl
  | cons head rest ih =>
      have parts := List.nodup_cons.mp distinct
      have notRow : head ∉ rest := by
        intro present
        exact parts.1 (List.mem_map.mpr ⟨head, present, rfl⟩)
      simpa [dedupRows, notRow] using congrArg (head :: ·) (ih parts.2)

/-! Executable identity-binding sink-seeded chain. Method n calls method n-1.
The sole nonzero generator is the terminal sink seed. The returned requirement
is propagated by balanced ZERO returns. `returnsRequirement` is a packet of
sink dependency, never a nonzero method initial. All payloads are exact/NORMAL.
The reach summary result 0 is implicit; result 1 is arg0.f.$/T, within budget.
-/
structure ChainPacket where
  returnsRequirement : Bool
  raw : List Summary
  deriving DecidableEq, Repr

def reach (owner : Nat) : Summary := ⟨owner, .zero, 0, .normal⟩
def requirement (owner : Nat) : Summary := ⟨owner, .zero, 1, .normal⟩

def chain (seeded : Bool) : Nat → ChainPacket
  | 0 => ⟨seeded, []⟩
  | n + 1 =>
      let child := chain seeded n
      ⟨child.returnsRequirement,
       child.raw ++ [reach n] ++ if child.returnsRequirement then [requirement n] else []⟩

def exportRows (direction : Direction) (summaries : List Summary) : List Row :=
  summaries.flatMap fun summary => (project direction summary).filter fun row =>
    decide (Explicit row)

def chainRows (seeded : Bool) (n : Nat) : List Row :=
  exportRows .backward (chain seeded n).raw

theorem chain_returns (seeded : Bool) (n : Nat) :
    (chain seeded n).returnsRequirement = seeded := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [chain] using ih

theorem chain_premises_are_zero (seeded : Bool) (n : Nat) :
    ∀ summary ∈ (chain seeded n).raw, summary.premise = .zero := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
      intro summary member
      cases seeded with
      | false =>
          simp [chain, chain_returns] at member
          rcases member with old | equal
          · exact ih summary old
          · simp [equal, reach]
      | true =>
          simp [chain, chain_returns] at member
          rcases member with old | equal | equal
          · exact ih summary old
          · simp [equal, reach]
          · simp [equal, requirement]

theorem chain_publication_permitted (seeded : Bool) (n : Nat) (rows : List Row)
    (restricts : Row → Summary → Prop) (summary : Summary)
    (member : summary ∈ (chain seeded n).raw) :
    Published .backward rows restricts summary :=
  .backwardZero rfl (chain_premises_are_zero seeded n summary member)

theorem chain_publication_selected (seeded : Bool) (n : Nat) (summary : Summary)
    (member : summary ∈ (chain seeded n).raw) : Selected .backward summary :=
  Or.inr (Or.inr ⟨rfl, chain_premises_are_zero seeded n summary member⟩)

theorem seeded_chain_owner_list (n : Nat) : (chainRows true n).map Row.owner = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [chainRows, chain, exportRows, chain_returns, reach, requirement, project,
        Explicit, List.flatMap_append, List.map_append, List.range_succ] using ih

theorem export_rows_append (direction : Direction) (left right : List Summary) :
    exportRows direction (left ++ right) = exportRows direction left ++ exportRows direction right := by
  simp only [exportRows, List.flatMap_append]

theorem unseeded_chain_no_explicit_rows (n : Nat) : chainRows false n = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change exportRows .backward ((chain false n).raw ++ [reach n] ++
        if (chain false n).returnsRequirement then [requirement n] else []) = []
      rw [chain_returns]
      change exportRows .backward ((chain false n).raw ++ [reach n] ++ []) = []
      rw [List.append_nil, export_rows_append]
      change chainRows false n ++ [] = []
      rw [ih]
      rfl

theorem constructive_range_nodup (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      have smaller := List.mem_range.mp ha
      omega

theorem seeded_chain_support_size (n : Nat) : (chainRows true n).length = n := by
  have h := congrArg List.length (seeded_chain_owner_list n)
  simpa using h

theorem seeded_chain_distinct_owners (n : Nat) : ((chainRows true n).map Row.owner).Nodup := by
  rw [seeded_chain_owner_list]
  exact constructive_range_nodup n

/-- One unrelated incoming explicit method keeps the selected forward driver running. -/
def unrelatedIncoming (n : Nat) : List Row := [⟨n, 2, some 3⟩]

theorem chain_owner_absent_from_incoming {n owner : Nat} (h : owner < n) :
    ¬ Support (unrelatedIncoming n) owner := by
  simp [Support, unrelatedIncoming]
  omega

theorem chain_row_exported (seeded : Bool) (n : Nat) (rows : List Row)
    (restricts : Row → Summary → Prop) (row : Row)
    (member : row ∈ chainRows seeded n) :
    ∃ summary, Exported .backward rows restricts summary row := by
  simp only [chainRows, exportRows, List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at member
  obtain ⟨summary, rawMember, projected, explicit⟩ := member
  exact ⟨summary, ⟨chain_publication_permitted seeded n rows restricts summary rawMember,
    chain_publication_selected seeded n summary rawMember, projected, explicit⟩⟩

theorem seeded_chain_outgoing (n owner : Nat) (h : owner < n)
    (restricts : Row → Summary → Prop) : Outgoing .backward (unrelatedIncoming n) restricts owner := by
  have ownerMember : owner ∈ (chainRows true n).map Row.owner := by
    rw [seeded_chain_owner_list]
    exact List.mem_range.mpr h
  obtain ⟨row, rowMember, sameOwner⟩ := List.mem_map.mp ownerMember
  obtain ⟨summary, exported⟩ := chain_row_exported true n (unrelatedIncoming n) restricts row rowMember
  exact ⟨summary, row, exported, sameOwner⟩

theorem seeded_chain_new_methods_zero_only (n owner : Nat) (h : owner < n)
    (emits : Row → Initial → Prop) : ¬ Analysed (unrelatedIncoming n) emits owner :=
  no_local_row_means_zero_only (chain_owner_absent_from_incoming h)

theorem arbitrarily_large_support_growth (n : Nat) :
    (chainRows true (n + 2)).length > (unrelatedIncoming (n + 2)).length := by
  rw [seeded_chain_support_size]
  simp [unrelatedIncoming]

def storedChainRows (seeded : Bool) (n : Nat) : List Row := dedupRows (chainRows seeded n)

theorem seeded_chain_dedup_unchanged (n : Nat) : storedChainRows true n = chainRows true n :=
  dedup_unchanged_if_distinct_owners _ (seeded_chain_distinct_owners n)

theorem stored_seeded_support_size (n : Nat) : (storedChainRows true n).length = n := by
  rw [seeded_chain_dedup_unchanged, seeded_chain_support_size]

theorem stored_support_arbitrarily_grows (n : Nat) :
    (storedChainRows true (n + 2)).length > (unrelatedIncoming (n + 2)).length := by
  rw [seeded_chain_dedup_unchanged]
  exact arbitrarily_large_support_growth n

theorem support_contraction_counterexample :
    ∃ owner, Support (storedChainRows true 2) owner ∧ ¬ Support (unrelatedIncoming 2) owner := by
  refine ⟨0, ?_, chain_owner_absent_from_incoming (by decide)⟩
  refine ⟨⟨0, 1, none⟩, ?_, rfl⟩
  decide

namespace Controls

theorem two_new_methods : (chainRows true 2).map Row.owner = [0, 1] := rfl

theorem two_exceed_incoming : (chainRows true 2).length > (unrelatedIncoming 2).length := by decide

theorem ten_support : (chainRows true 10).length = 10 := rfl

theorem no_seed_no_support : chainRows false 10 = [] := rfl

theorem reach_only_not_counted : exportRows .backward [reach 7] = [] := rfl

theorem normal_requirement_counted :
    exportRows .backward [requirement 7] = [⟨7, 1, none⟩] := rfl

def checks : Bool :=
  decide ((chainRows true 2).map Row.owner = [0, 1]) &&
  decide ((chainRows true 2).length > (unrelatedIncoming 2).length) &&
  decide ((chainRows true 10).length = 10) &&
  decide (chainRows false 10 = []) &&
  decide (exportRows .backward [reach 7] = []) &&
  decide (exportRows .backward [requirement 7] = [⟨7, 1, none⟩])

theorem checks_pass : checks = true := rfl

end Controls
end MethodSupport
