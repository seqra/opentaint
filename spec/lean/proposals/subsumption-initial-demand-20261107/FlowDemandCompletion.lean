import Std
import Geometry

/-!
PREPARED, not kernel checked. Demand query-view completion, never a summary.
Input rows must already be the final admitted/subsumed incoming paired view.
The component does not implement C2, body transfer, C5, publication or progress.
It adds no actual fact, layer, InitialAp, source permission or NORMAL provider.
-/
namespace FlowDemandCompletion
set_option autoImplicit false

abbrev Accessor := RelativeRestriction.Accessor
abbrev Path := RelativeRestriction.Path
abbrev Tail := RelativeRestriction.Tail

inductive Base where
  | local (id : Nat)
  | staticRoot
  deriving DecidableEq, Repr
inductive Mark where
  | full (id : Nat)
  | flow
  | group (id : Nat)
  deriving DecidableEq, Repr

structure Pattern where
  base : Base
  path : Path
  tail : Tail
  mark : Mark
  exclusion : List Accessor
  deriving DecidableEq, Repr

/-- All fields are actual owner/interface coordinates, not a provenance flag.
`methodContext` identifies the complete logical method and its context. -/
structure Interface where
  methodContext : Nat
  direction : Bool
  scope : Nat
  entryPort : Int
  outputPort : Int
  deriving DecidableEq, Repr

inductive Entry where
  | zero | target | data (value : Pattern)
  deriving DecidableEq, Repr
inductive Exit where
  | zero | data (value : Pattern)
  deriving DecidableEq, Repr
structure Row where
  interface : Interface
  entry : Entry
  exit : Exit
  deriving DecidableEq, Repr

def counted : Accessor → Bool
  | .classId _ => false
  | .field _ | .element => true

def fieldsOnly (path : Path) : Bool := path.all counted

/-- A static hypothesis must begin at a named field, not a class/root wildcard.
This applies to both self-pairs and paired DATA/DATA erasure. -/
def legalHead : Base → Path → Bool
  | .local _, path => fieldsOnly path
  | .staticRoot, .classId _ :: .field _ :: rest => fieldsOnly rest
  | .staticRoot, _ => false

def fullMarked (pattern : Pattern) : Bool :=
  match pattern.mark with | .full _ => true | _ => false

def endpointEligible (pattern : Pattern) : Bool :=
  legalHead pattern.base pattern.path

/-- Ordered semantic oracle. An implementation can share these prefixes in a
trie/cursor; this list model does not claim linear allocation of copied paths. -/
def rawPrefixes : Path → List Path
  | [] => [[]]
  | first :: rest => [] :: (rawPrefixes rest).map (List.cons first)

def validPrefixes (pattern : Pattern) : List Path :=
  (rawPrefixes pattern.path).filter (legalHead pattern.base)

def flowAny (pattern : Pattern) (head : Path) : Pattern :=
  ⟨pattern.base,head,.may,.flow,[]⟩

def selfPair (interface : Interface) (pattern : Pattern) (head : Path) : Row :=
  ⟨interface,.data (flowAny pattern head),.data (flowAny pattern head)⟩

def selfRows (interface : Interface) (pattern : Pattern) : List Row :=
  if endpointEligible pattern then (validPrefixes pattern).map (selfPair interface pattern) else []

def entryEndpoint : Entry → List Pattern
  | .data pattern => [pattern]
  | _ => []
def exitEndpoint : Exit → List Pattern
  | .data pattern => [pattern]
  | .zero => []

def prefixRows (row : Row) : List Row :=
  (entryEndpoint row.entry ++ exitEndpoint row.exit).flatMap (selfRows row.interface)

/-- Exactly one original DATA/DATA head pair; never a prefix cross product. -/
def pairedRow (row : Row) : List Row :=
  match row.entry, row.exit with
  | .data left, .data right =>
      if legalHead left.base left.path && legalHead right.base right.path then
        [⟨row.interface,.data (flowAny left left.path),.data (flowAny right right.path)⟩]
      else []
  | _, _ => []

def additions (row : Row) : List Row := prefixRows row ++ pairedRow row

def generated (finalRows : List Row) : List Row := finalRows.flatMap additions

/-- Keep old rows literally. New rows are query permissions, not frontier roots.
Exact duplicate deduplication can be an equivalent index view, not pruning. -/
def completed (finalRows : List Row) : List Row := finalRows ++ generated finalRows

theorem raw_prefixes_contain_source (path : Path) : path ∈ rawPrefixes path := by
  induction path with
  | nil => exact List.mem_cons.mpr (Or.inl rfl)
  | cons first rest ih =>
    exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨rest,ih,rfl⟩))

theorem raw_prefixes_contain_empty (path : Path) : [] ∈ rawPrefixes path := by
  cases path <;> exact List.mem_cons.mpr (Or.inl rfl)

theorem raw_prefix_count (path : Path) : (rawPrefixes path).length = path.length + 1 := by
  induction path with
  | nil => rfl
  | cons first rest ih => simp [rawPrefixes,ih]

theorem each_raw_head_is_a_prefix (path head : Path) (member : head ∈ rawPrefixes path) :
    head.IsPrefix path := by
  induction path generalizing head with
  | nil =>
    have same : head = [] := by simpa [rawPrefixes] using member
    subst head
    exact ⟨[],rfl⟩
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | mapped
    · subst head; exact ⟨first :: rest,rfl⟩
    · obtain ⟨earlier,present,same⟩ := List.mem_map.mp mapped
      obtain ⟨suffix,witness⟩ := ih earlier present
      rw [← same]
      exact ⟨suffix,by simpa only [List.cons_append] using congrArg (List.cons first) witness⟩

theorem valid_prefix_has_source_and_shape (pattern : Pattern) (head : Path)
    (member : head ∈ validPrefixes pattern) :
    head.IsPrefix pattern.path ∧ legalHead pattern.base head = true := by
  have selected := List.mem_filter.mp member
  exact ⟨each_raw_head_is_a_prefix pattern.path head selected.1,selected.2⟩

theorem valid_prefix_depth_bound (pattern : Pattern) (head : Path)
    (member : head ∈ validPrefixes pattern) :
    RelativeRestriction.depth head ≤ RelativeRestriction.depth pattern.path :=
  RelativeRestriction.prefix_depth_le (valid_prefix_has_source_and_shape pattern head member).1

theorem source_head_is_a_valid_prefix (pattern : Pattern)
    (valid : legalHead pattern.base pattern.path = true) : pattern.path ∈ validPrefixes pattern :=
  List.mem_filter.mpr ⟨raw_prefixes_contain_source pattern.path,valid⟩

theorem local_empty_head_is_valid (id : Nat) : legalHead (.local id) [] = true := rfl
theorem static_empty_head_is_invalid : legalHead .staticRoot [] = false := rfl
theorem static_class_only_head_is_invalid (owner : Nat) :
    legalHead .staticRoot [.classId owner] = false := rfl
theorem static_array_without_named_field_is_invalid (owner : Nat) :
    legalHead .staticRoot [.classId owner,.element] = false := rfl
theorem static_named_field_head_is_valid (owner field : Nat) :
    legalHead .staticRoot [.classId owner,.field field] = true := rfl

theorem self_pair_is_complete_FLOW_ANY (interface : Interface) (pattern : Pattern) (head : Path) :
    (selfPair interface pattern head).interface = interface ∧
    (selfPair interface pattern head).entry = .data ⟨pattern.base,head,.may,.flow,[]⟩ ∧
    (selfPair interface pattern head).exit = .data ⟨pattern.base,head,.may,.flow,[]⟩ :=
  ⟨rfl,rfl,rfl⟩

theorem self_result_has_one_real_endpoint (interface : Interface) (pattern : Pattern) (result : Row)
    (member : result ∈ selfRows interface pattern) :
    endpointEligible pattern = true ∧ ∃ head, head ∈ validPrefixes pattern ∧
      result = selfPair interface pattern head := by
  unfold selfRows at member
  split at member
  next eligible =>
    obtain ⟨head,inHeads,same⟩ := List.mem_map.mp member
    exact ⟨eligible,head,inHeads,same.symm⟩
  next => cases member

theorem eligible_endpoint_gets_its_full_head (interface : Interface) (pattern : Pattern)
    (eligible : endpointEligible pattern = true) :
    selfPair interface pattern pattern.path ∈ selfRows interface pattern := by
  have valid : legalHead pattern.base pattern.path = true := eligible
  simp only [selfRows,eligible,if_true]
  exact List.mem_map.mpr ⟨pattern.path,source_head_is_a_valid_prefix pattern valid,rfl⟩

theorem original_rows_are_kept (finalRows : List Row) (row : Row) (member : row ∈ finalRows) :
    row ∈ completed finalRows := List.mem_append_left _ member

theorem generated_row_has_one_final_complete_source (finalRows : List Row) (result : Row)
    (member : result ∈ generated finalRows) :
    ∃ source, source ∈ finalRows ∧ result ∈ additions source := List.mem_flatMap.mp member

theorem paired_result_keeps_both_heads (source result : Row) (member : result ∈ pairedRow source) :
    ∃ left right, source.entry = .data left ∧ source.exit = .data right ∧
      legalHead left.base left.path = true ∧ legalHead right.base right.path = true ∧
      result = ⟨source.interface,.data (flowAny left left.path),.data (flowAny right right.path)⟩ := by
  cases entry : source.entry with
  | zero => simp [pairedRow,entry] at member
  | target => simp [pairedRow,entry] at member
  | data left =>
    cases output : source.exit with
    | zero => simp [pairedRow,entry,output] at member
    | data right =>
      simp only [pairedRow,entry,output] at member
      split at member
      next eligible =>
        have heads := Bool.and_eq_true_iff.mp eligible
        have same : result = ⟨source.interface,.data (flowAny left left.path),
            .data (flowAny right right.path)⟩ := by simpa only [List.mem_singleton] using member
        exact ⟨left,right,rfl,rfl,heads.1,heads.2,same⟩
      next => cases member

theorem paired_rows_are_not_a_prefix_product (source : Row) : (pairedRow source).length ≤ 1 := by
  cases entry : source.entry with
  | zero => simp [pairedRow,entry]
  | target => simp [pairedRow,entry]
  | data left =>
    cases output : source.exit with
    | zero => simp [pairedRow,entry,output]
    | data right =>
      simp only [pairedRow,entry,output]
      split <;> simp

theorem no_incoming_rows_give_no_completed_view : completed [] = [] := rfl

theorem self_completion_is_mark_independent (interface : Interface) (pattern : Pattern)
    (other : Mark) :
    selfRows interface {pattern with mark := other} = selfRows interface pattern := by
  unfold selfRows endpointEligible validPrefixes selfPair flowAny
  rfl

theorem paired_completion_is_mark_independent (interface : Interface) (left right : Pattern)
    (leftMark rightMark : Mark) :
    pairedRow ⟨interface,.data {left with mark := leftMark},.data {right with mark := rightMark}⟩ =
      pairedRow ⟨interface,.data left,.data right⟩ := by
  unfold pairedRow flowAny
  rfl

theorem controls_do_not_become_DATA_endpoints :
    entryEndpoint .zero = [] ∧ entryEndpoint .target = [] ∧ exitEndpoint .zero = [] :=
  ⟨rfl,rfl,rfl⟩

theorem self_result_keeps_exact_interface (interface : Interface) (pattern : Pattern) (result : Row)
    (member : result ∈ selfRows interface pattern) : result.interface = interface := by
  obtain ⟨_,head,_,same⟩ := self_result_has_one_real_endpoint interface pattern result member
  rw [same]; rfl

theorem prefix_result_keeps_exact_interface (source result : Row) (member : result ∈ prefixRows source) :
    result.interface = source.interface := by
  obtain ⟨endpoint,_,present⟩ := List.mem_flatMap.mp member
  exact self_result_keeps_exact_interface source.interface endpoint result present

theorem all_additions_keep_exact_interface (source result : Row) (member : result ∈ additions source) :
    result.interface = source.interface := by
  rcases List.mem_append.mp member with fromSelf | fromPair
  · exact prefix_result_keeps_exact_interface source result fromSelf
  · obtain ⟨_,_,_,_,_,_,same⟩ := paired_result_keeps_both_heads source result fromPair
    rw [same]

theorem generated_scopes_and_ports_have_a_final_source (finalRows : List Row) (result : Row)
    (member : result ∈ generated finalRows) :
    ∃ source, source ∈ finalRows ∧ result.interface = source.interface := by
  obtain ⟨source,inFinal,derived⟩ := generated_row_has_one_final_complete_source finalRows result member
  exact ⟨source,inFinal,all_additions_keep_exact_interface source result derived⟩

theorem generated_has_no_history_witness (finalRows : List Row) (result : Row)
    (absent : ∀ source, source ∈ finalRows → result ∉ additions source) :
    result ∉ generated finalRows := by
  intro member
  obtain ⟨source,inFinal,derived⟩ := generated_row_has_one_final_complete_source finalRows result member
  exact absent source inFinal derived

theorem filter_length_bound {A : Type} (test : A → Bool) (values : List A) :
    (values.filter test).length ≤ values.length := by
  induction values with
  | nil => exact Nat.le_refl _
  | cons first rest ih => cases selected : test first <;> simp [List.filter,selected] <;> omega

theorem valid_prefix_count_bound (pattern : Pattern) :
    (validPrefixes pattern).length ≤ pattern.path.length + 1 := by
  exact Nat.le_trans (filter_length_bound _ _) (Nat.le_of_eq (raw_prefix_count pattern.path))

def endpointBudget (pattern : Pattern) : Nat :=
  if endpointEligible pattern then pattern.path.length + 1 else 0

theorem self_count_bound (interface : Interface) (pattern : Pattern) :
    (selfRows interface pattern).length ≤ endpointBudget pattern := by
  unfold selfRows endpointBudget
  split
  · simpa only [List.length_map] using valid_prefix_count_bound pattern
  · exact Nat.le_refl _

def rowBudget (source : Row) : Nat :=
  ((entryEndpoint source.entry ++ exitEndpoint source.exit).map endpointBudget).sum + 1

def finalBudget (finalRows : List Row) : Nat := (finalRows.map rowBudget).sum

theorem endpoint_flatmap_bound (interface : Interface) (patterns : List Pattern) :
    (patterns.flatMap (selfRows interface)).length ≤ (patterns.map endpointBudget).sum := by
  induction patterns with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
    have one := self_count_bound interface first
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons]
    omega

theorem additions_count_is_linear_in_endpoint_budget (source : Row) :
    (additions source).length ≤ rowBudget source := by
  have prefixBound := endpoint_flatmap_bound source.interface
    (entryEndpoint source.entry ++ exitEndpoint source.exit)
  have pairBound := paired_rows_are_not_a_prefix_product source
  simp only [additions,List.length_append,rowBudget]
  exact Nat.add_le_add prefixBound pairBound

theorem generated_count_is_linear_in_final_budget (finalRows : List Row) :
    (generated finalRows).length ≤ finalBudget finalRows := by
  induction finalRows with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
    have one := additions_count_is_linear_in_endpoint_budget first
    simp only [generated,List.flatMap_cons,List.length_append,finalBudget,List.map_cons,List.sum_cons]
    change (additions first).length + (generated rest).length ≤ rowBudget first + finalBudget rest
    omega

/-! Query-local run-2 static carry: one row at the actual named-field head.
The callback receives the genuine exact interface; it enumerates no method ×
field × mark product and has no persistent memo/history in its definition. -/
def virtualStaticCarry (run2 : Bool) (interface : Interface) (actual : Pattern) : List Row :=
  if run2 && decide (actual.base = .staticRoot) && legalHead actual.base actual.path then
    [selfPair interface actual actual.path] else []

theorem virtual_carry_is_single_query_row (run2 : Bool) (interface : Interface) (actual : Pattern) :
    (virtualStaticCarry run2 interface actual).length ≤ 1 := by
  unfold virtualStaticCarry
  split <;> simp

theorem virtual_carry_has_no_run3plus_completion (interface : Interface) (actual : Pattern) :
    virtualStaticCarry false interface actual = [] := by simp [virtualStaticCarry]

theorem virtual_carry_is_mark_independent (run2 : Bool) (interface : Interface)
    (actual : Pattern) (otherMark : Mark) :
    virtualStaticCarry run2 interface {actual with mark := otherMark} =
      virtualStaticCarry run2 interface actual := by
  unfold virtualStaticCarry selfPair flowAny
  rfl

/-! Bounded native-shaped witnesses; these are permissions, not executions. -/
def loop5 : Interface := ⟨17,true,2,5,5⟩
def markedFF : Pattern := ⟨.local 3,[.field 4,.field 4],.star,.full 11,[]⟩
def ZERO_to_FF : Row := ⟨loop5,.zero,.data markedFF⟩

theorem paired_exit_alone_supplies_repeat_self_guidance :
    selfPair loop5 markedFF markedFF.path ∈ additions ZERO_to_FF := by decide

theorem exit_derived_guidance_keeps_repeat_scope_and_ports :
    (selfPair loop5 markedFF markedFF.path).interface = ⟨17,true,2,5,5⟩ := rfl

theorem prefix_closure_includes_root_and_intermediate :
    (selfPair loop5 markedFF [] ∈ additions ZERO_to_FF) ∧
    (selfPair loop5 markedFF [.field 4] ∈ additions ZERO_to_FF) := by decide

theorem fine_next_key_differs_from_depth_two_cut_key (head : Path) (field : Nat) :
    head ++ [.field field] ≠ head := by
  intro same
  have lengths := congrArg List.length same
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  omega

def staticG : Pattern := ⟨.staticRoot,[.classId 7,.field 8],.star,.full 11,[]⟩
def staticGChild : Pattern :=
  ⟨.staticRoot,[.classId 7,.field 8,.field 9],.star,.full 11,[.field 10]⟩

theorem static_prefixes_start_at_named_field_and_include_full_head :
    validPrefixes staticGChild =
      [[.classId 7,.field 8],[.classId 7,.field 8,.field 9]] := by decide

theorem concrete_class_marker_is_not_a_completion_source :
    selfRows loop5 ⟨.staticRoot,[.classId 7],.exact,.full 11,[]⟩ = [] := by decide

theorem virtual_static_carry_uses_actual_named_field_not_root :
    virtualStaticCarry true loop5 staticG = [selfPair loop5 staticG staticG.path] ∧
    virtualStaticCarry true loop5 ⟨.staticRoot,[.classId 7],.exact,.full 11,[]⟩ = [] := by decide

def copyScope : Interface := ⟨41,true,0,-1,-2⟩
def copyInput : Pattern := ⟨.local 1,[],.star,.full 11,[]⟩
def copyOutput : Pattern := ⟨.local 2,[],.star,.full 11,[]⟩
def markedCopy : Row := ⟨copyScope,.data copyInput,.data copyOutput⟩

/-- A necessary C5 base/abstract-entry check, not a replacement C5 operator. -/
def permitsFLOWBases (input output : Base) (row : Row) : Bool :=
  match row.entry,row.exit with
  | .data left,.data right =>
      decide (left.mark = .flow ∧ right.mark = .flow ∧
        left.base = input ∧ right.base = output)
  | _,_ => false

theorem self_only_completion_cannot_retain_cross_base_FLOW :
    (prefixRows markedCopy).any (permitsFLOWBases (.local 1) (.local 2)) = false := by decide

theorem paired_erasure_preserves_the_original_cross_base_pair :
    pairedRow markedCopy =
      [⟨copyScope,.data (flowAny copyInput []),.data (flowAny copyOutput [])⟩] := by decide

theorem paired_completion_supplies_cross_base_FLOW_permission :
    (additions markedCopy).any (permitsFLOWBases (.local 1) (.local 2)) = true := by decide

theorem completion_has_no_crossed_prefix_product :
    (pairedRow ⟨copyScope,.data markedFF,.data staticGChild⟩).length = 1 := by decide

def oldMarkedOnlySelfRows (interface : Interface) (pattern : Pattern) : List Row :=
  if fullMarked pattern then selfRows interface pattern else []

theorem marked_only_filter_misses_final_provisional_FLOW_permission :
    oldMarkedOnlySelfRows copyScope (flowAny copyInput []) = [] ∧
    selfPair copyScope copyInput [] ∈ selfRows copyScope (flowAny copyInput []) := by decide

theorem removed_long_FLOW_row_is_not_reopened_from_final_short_row :
    selfPair copyScope copyOutput [.field 6,.field 6] ∉
      generated [⟨copyScope,.data (flowAny copyInput []),.data (flowAny copyOutput [])⟩] := by decide

end FlowDemandCompletion
