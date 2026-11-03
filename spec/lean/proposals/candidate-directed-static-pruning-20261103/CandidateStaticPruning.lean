import Std

namespace CandidateStaticPruning

/- Finite scalar snapshots after the existing domain/packet filters.
   No coverage, publication permission or storage implementation is supplied. -/
inductive Tail where
  | exact | star | any | must
  deriving DecidableEq, Repr

inductive Mark where
  | flow (excluded : List Nat)
  | colored (id : Nat)
  deriving DecidableEq, Repr

inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr

structure Pattern where
  base : Nat
  fields : List Nat
  tail : Tail
  mark : Mark
  fieldExclusions : List Nat
  deriving DecidableEq, Repr

structure Row where
  src : Pattern
  dst : Pattern
  layer : Layer
  isProtected : Bool
  deriving DecidableEq, Repr

inductive Relation where
  | flow
  | mapped (input output : Option Nat)
  | outsideScope
  deriving DecidableEq, Repr

structure Key where
  src : Pattern
  dst : Pattern
  relation : Relation
  deriving DecidableEq, Repr

def isFlow : Mark → Bool
  | .flow _ => true
  | .colored _ => false

def pairEndpoint (p : Pattern) : Pattern :=
  if p.tail = .exact then { p with tail := .star } else p

def normalizePair (a b : Pattern) : Pattern × Pattern :=
  if isFlow a.mark && isFlow b.mark then (pairEndpoint a, pairEndpoint b) else (a,b)

def guidancePattern (p : Pattern) : Pattern :=
  let q := if p.tail = .must then { p with tail := .any, fieldExclusions := [] } else p
  let mark := match q.mark with | .flow _ => Mark.flow [] | .colored x => Mark.colored x
  let q := { q with mark := mark }
  if isFlow q.mark && q.tail == .star then { q with fieldExclusions := [] } else q

def relation (a b : Pattern) : Relation :=
  match a.mark, b.mark with
  | .flow _, .flow _ => .flow
  | .colored x, .colored y =>
      .mapped (if a.base = 0 then none else some x) (if b.base = 0 then none else some y)
  | _, _ => .outsideScope

def key (r : Row) : Key :=
  let p := normalizePair r.src r.dst
  let a := guidancePattern p.1
  let b := guidancePattern p.2
  { src := a, dst := b, relation := relation a b }

def survivors (common privateB : List Row) : List Key :=
  common.map key ++ privateB.map key

def member (common privateB : List Row) (q : Key) : Bool :=
  decide (q ∈ survivors common privateB)

structure Frozen where
  observed : List Nat
  lost : List Nat
  peak : Nat
  deriving DecidableEq, Repr

def oldFreeze (ids : List Nat) (peak : Nat) (row : Nat → Row)
    (common privateB : List Row) : Frozen :=
  { observed := ids, lost := ids.filter (fun id => !(member common privateB (key (row id)))), peak }

def queryFreeze (ids : List Nat) (peak : Nat) (row : Nat → Row)
    (oracle : Key → Bool) : Frozen :=
  { observed := ids, lost := ids.filter (fun id => !(oracle (key (row id)))), peak }

/- This is an explicit prerequisite, not a fact about a Kotlin query/index. -/
def OracleEquivalent (ids : List Nat) (row : Nat → Row) (common privateB : List Row)
    (oracle : Key → Bool) : Prop :=
  ∀ id ∈ ids, oracle (key (row id)) = member common privateB (key (row id))

theorem exact_reference_oracle (ids : List Nat) (row : Nat → Row) (common privateB : List Row) :
    OracleEquivalent ids row common privateB (member common privateB) := by
  intro id _
  rfl

theorem equivalent_oracle_preserves_lost (ids : List Nat) (peak : Nat) (row : Nat → Row)
    (common privateB : List Row) (oracle : Key → Bool)
    (h : OracleEquivalent ids row common privateB oracle) :
    (queryFreeze ids peak row oracle).lost = (oldFreeze ids peak row common privateB).lost := by
  apply List.filter_congr
  intro id hi
  rw [h id hi]

theorem equivalent_oracle_preserves_exact_result (ids : List Nat) (peak : Nat) (row : Nat → Row)
    (common privateB : List Row) (oracle : Key → Bool)
    (h : OracleEquivalent ids row common privateB oracle) :
    queryFreeze ids peak row oracle = oldFreeze ids peak row common privateB := by
  exact congrArg (fun lost => Frozen.mk ids lost peak)
    (equivalent_oracle_preserves_lost ids peak row common privateB oracle h)

theorem observed_ids_and_order_unchanged (ids : List Nat) (peak : Nat) (row : Nat → Row)
    (oracle : Key → Bool) : (queryFreeze ids peak row oracle).observed = ids := rfl

theorem peak_unchanged (ids : List Nat) (peak : Nat) (row : Nat → Row)
    (oracle : Key → Bool) : (queryFreeze ids peak row oracle).peak = peak := rfl

theorem lost_is_ordered_filter (ids : List Nat) (peak : Nat) (row : Nat → Row)
    (oracle : Key → Bool) :
    (queryFreeze ids peak row oracle).lost = ids.filter (fun id => !(oracle (key (row id)))) := rfl

theorem layer_ignored (r : Row) (layer : Layer) : key { r with layer := layer } = key r := rfl

theorem protection_ignored (r : Row) (p : Bool) : key { r with isProtected := p } = key r := rfl

theorem survivors_include_both_layers (r : Row) (q : Key) :
    member [r] [] q = member [{ r with layer := .demand }] [] q := by
  simp [member, survivors, layer_ignored]

theorem protection_does_not_change_membership (r : Row) (q : Key) (p : Bool) :
    member [r] [] q = member [{ r with isProtected := p }] [] q := by
  simp [member, survivors, protection_ignored]

theorem flow_exact_pair_widens (a b : Pattern) (ma mb : List Nat)
    (ha : a.mark = .flow ma) (hb : b.mark = .flow mb) :
    normalizePair a b = (pairEndpoint a, pairEndpoint b) := by
  simp [normalizePair, ha, hb, isFlow]

theorem colored_pair_keeps_exact (a b : Pattern) (m : Nat) (ha : a.mark = .colored m) :
    normalizePair a b = (a,b) := by simp [normalizePair, ha, isFlow]

theorem guidance_preserves_base_fields (p : Pattern) :
    (guidancePattern p).base = p.base ∧ (guidancePattern p).fields = p.fields := by
  cases p with
  | mk base fields tail mark ex =>
    cases tail <;> cases mark <;> simp [guidancePattern, isFlow]

theorem must_becomes_any_clears_fields (p : Pattern) (h : p.tail = .must) :
    (guidancePattern p).tail = .any ∧ (guidancePattern p).fieldExclusions = [] := by
  cases p with
  | mk base fields tail mark ex =>
    cases mark <;> simp_all [guidancePattern, isFlow]

theorem flow_mark_exclusions_dropped (p : Pattern) (mx : List Nat)
    (h : p.mark = .flow mx) : (guidancePattern p).mark = .flow [] := by
  cases p with
  | mk base fields tail mark ex =>
    cases tail <;> cases mark <;> simp_all [guidancePattern, isFlow]

theorem colored_mark_preserved (p : Pattern) (m : Nat)
    (h : p.mark = .colored m) : (guidancePattern p).mark = .colored m := by
  cases p with
  | mk base fields tail mark ex =>
    cases tail <;> cases mark <;> simp_all [guidancePattern, isFlow]

/- Demand has no separate key field. Only existing emitted scalar rows enter S. -/
def samplePattern (mark : Mark) (tail : Tail) (mxFields : List Nat := []) : Pattern :=
  { base := 1, fields := [9], tail, mark, fieldExclusions := mxFields }

def sampleFlow : Row :=
  { src := samplePattern (.flow [7]) .exact [6],
    dst := { samplePattern (.flow [8]) .exact [5] with base := 2 }, layer := .normal, isProtected := false }

def normalizedFlow : Row :=
  { src := samplePattern (.flow []) .star,
    dst := { samplePattern (.flow []) .star with base := 2 }, layer := .demand, isProtected := true }

def sampleColored : Row :=
  { src := samplePattern (.colored 3) .exact,
    dst := { samplePattern (.colored 3) .exact with base := 2 }, layer := .normal, isProtected := false }

def mustColored : Row :=
  { sampleColored with dst := { sampleColored.dst with tail := .must, fieldExclusions := [8] } }

def anyColored : Row :=
  { sampleColored with dst := { sampleColored.dst with tail := .any, fieldExclusions := [] } }

theorem full_flow_normalization_example : key sampleFlow = key normalizedFlow := by decide

theorem must_any_key_collision : key mustColored = key anyColored := by decide

theorem raw_rows_differ_despite_guidance_collision : mustColored ≠ anyColored := by decide

def rawDirectory (id : Nat) : Row := if id = 11 then mustColored else anyColored

theorem raw_ids_not_merged_when_keys_equal :
    queryFreeze [11,12] 7 rawDirectory (fun _ => false) =
      { observed := [11,12], lost := [11,12], peak := 7 } := by decide

theorem raw_observed_ids_retained_when_keys_survive :
    queryFreeze [11,12] 7 rawDirectory (fun _ => true) =
      { observed := [11,12], lost := [], peak := 7 } := by decide

theorem flow_is_not_colored_membership : member [sampleFlow] [] (key sampleColored) = false := by decide

theorem omitted_colored_row_remains_lost :
    oldFreeze [3] 1 (fun _ => sampleColored) [sampleFlow] [] =
      { observed := [3], lost := [3], peak := 1 } := by decide

theorem demand_colored_survivor_is_present :
    member [{ sampleColored with layer := .demand, isProtected := true }] [] (key sampleColored) = true := by decide

theorem private_b_normalized_membership : member [] [mustColored] (key anyColored) = true := by decide

/- Plans are executable access traces. Common/private B are lazy resources; candidate
   plans contain no operation that requests either full enumeration. Oracle internals
   and their costs are explicitly outside this access trace. -/
inductive Read where
  | commonRow (index : Nat)
  | privateRow (index : Nat)
  | candidateRow (id : Nat)
  | oracle (id : Nat)
  deriving DecidableEq, Repr

def oldPlan (ids : List Nat) (commonCount privateCount : Nat) : List Read :=
  (List.range commonCount).map Read.commonRow ++
  (List.range privateCount).map Read.privateRow ++ ids.map Read.candidateRow

def candidatePlan (ids : List Nat) : List Read :=
  ids.flatMap (fun id => [Read.candidateRow id, Read.oracle id])

def candidateQueries (ids : List Nat) : List Nat := ids

theorem candidate_queries_keep_raw_order (ids : List Nat) : candidateQueries ids = ids := rfl

theorem duplicate_normalized_key_queries_not_merged : candidateQueries [11,12] = [11,12] := rfl

theorem zero_candidates_request_no_enumeration : candidatePlan [] = [] := rfl

theorem old_empty_candidates_still_materializes : oldPlan [] 2 1 =
    [.commonRow 0,.commonRow 1,.privateRow 0] := by decide

theorem zero_candidates_no_oracle_calls (row : Nat → Row) (oracle : Key → Bool) (peak : Nat) :
    queryFreeze [] peak row oracle = { observed := [], lost := [], peak } := rfl

def isEnumeration : Read → Bool
  | .commonRow _ => true
  | .privateRow _ => true
  | _ => false

def enumerationCount (trace : List Read) : Nat := (trace.filter isEnumeration).length

theorem candidate_no_full_row_materialization (ids : List Nat) :
    enumerationCount (candidatePlan ids) = 0 := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    change enumerationCount (candidatePlan ids) = 0
    exact ih

theorem filterTrue {α : Type} (xs : List α) : xs.filter (fun _ => true) = xs := by
  exact List.filter_eq_self.mpr (by intro _ _; rfl)

theorem filterFalse {α : Type} (xs : List α) : xs.filter (fun _ => false) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem old_full_row_materializations (ids : List Nat) (n m : Nat) :
    enumerationCount (oldPlan ids n m) = n + m := by
  simp [enumerationCount, oldPlan, List.filter_map, Function.comp_def, isEnumeration, filterTrue, filterFalse]

def oldUnrelatedRows (candidateKeys : List Key) (common privateB : List Row) : Nat :=
  ((common ++ privateB).filter (fun row => !(decide (key row ∈ candidateKeys)))).length

def newCallerUnrelatedRows : Nat := 0

theorem no_candidates_all_old_rows_unrelated (common privateB : List Row) :
    oldUnrelatedRows [] common privateB = common.length + privateB.length := by
  simp [oldUnrelatedRows, filterTrue]

theorem candidate_caller_avoids_unrelated_rows (keys : List Key) (common privateB : List Row) :
    newCallerUnrelatedRows ≤ oldUnrelatedRows keys common privateB := by
  simp [newCallerUnrelatedRows]

theorem strict_caller_work_witness :
    newCallerUnrelatedRows < oldUnrelatedRows [] [sampleFlow] [sampleColored] := by decide

theorem strict_nonempty_caller_work_witness :
    newCallerUnrelatedRows < oldUnrelatedRows [key sampleColored] [sampleFlow] [sampleColored] := by decide

theorem candidate_plan_linear_actions (ids : List Nat) :
    (candidatePlan ids).length = 2 * ids.length := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    change Nat.succ (Nat.succ (candidatePlan ids).length) = 2 * Nat.succ ids.length
    rw [ih]
    omega

/- The model does not bound the supplied oracle's implementation work. -/
def newTotalUnrelatedRows (oracleUnrelatedRows : Nat) : Nat := oracleUnrelatedRows

theorem zero_total_unrelated_requires_oracle_cost_law (oracleUnrelatedRows : Nat)
    (h : oracleUnrelatedRows = 0) : newTotalUnrelatedRows oracleUnrelatedRows = 0 := by
  exact h

end CandidateStaticPruning
