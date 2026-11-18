import LocalRouting

/- Ordinary code only: choose(x) either reads x.f.f or wraps x twice.
   Its caller calls choose twice. Whole-object source/sink rules are the
   standard MUST source and MAY sink, not pass rules or method summaries.
   Retained witnesses below are fresh global-cut results, not copied demand. -/
namespace BoundedOrdinaryCycle
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open BoundedRefinementPipeline BoundedLocalRouting
set_option linter.unusedSimpArgs false

local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h

def fields (n : Nat) : Path := List.replicate n f
def data (base n : Nat) (tail : Tail) (mark : Option Nat := none) : Ap :=
  ap base (fields n) tail mark
def actualSource : Offered := ⟨data p 0 .must (some t),false⟩
def actualSink : Offered := ⟨data ret 0 .may (some t),true⟩
def rowF (n : Nat) : Row := ⟨data p (n+1) .ne,data ret (n+1) .star⟩
def rowB (n : Nat) : Row := ⟨data ret (n+2) .ne,data p (n+2) .star⟩
def queryF (n : Nat) : Seed := ⟨data p (n+1) .must,false⟩
def queryF2 (n : Nat) : Seed := ⟨data p (n+2) .star,false⟩
def queryB (n : Nat) : Seed := ⟨data ret (n+2) .star,false⟩
def queryB2 (n : Nat) : Seed := ⟨data ret (n+3) .star,false⟩
def offerF2 (n : Nat) : Offered := ⟨data p (n+2) .ne (some t),true⟩
def offerB1 (n : Nat) : Offered := ⟨data ret (n+3) .ne (some t),true⟩

@[simp] theorem fields_length (n : Nat) : (fields n).length = n := by
  exact List.length_replicate ..

theorem fields_step (n : Nat) : fields (n+1) = f :: fields n := rfl

@[simp] theorem fields_zero : fields 0 = [] := rfl

@[simp] theorem fields_nonempty (n : Nat) : fields (n+1) ≠ [] := by
  rw [fields_step]
  simp only [ne_eq,List.cons_ne_nil,not_false_eq_true]

@[simp] theorem fields_ne_next (n : Nat) : fields n ≠ fields (n+1) := by
  intro h
  have bad := congrArg List.length h
  simp only [fields_length] at bad
  omega

@[simp] theorem fields_next_ne (n : Nat) : fields (n+1) ≠ fields n := by
  intro h
  exact fields_ne_next n h.symm

theorem fields_two (n : Nat) : [f,f] ++ fields n = fields (n+2) := rfl

theorem drop_fields (m n : Nat) :
    dropHead (fields m) (fields (m+n)) = some (fields n) := by
  induction m with
  | zero => simp only [Nat.zero_add,fields_zero,dropHead]
  | succ m ih =>
    simpa only [Nat.succ_add,fields_step,dropHead,ite_true] using ih

@[simp] theorem drop_fields_next (n : Nat) :
    dropHead (fields n) (fields (n+1)) = some [f] := by
  exact drop_fields n 1

@[simp] theorem fields_append_one (n : Nat) : fields n ++ [f] = fields (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (f :: fields n) ++ [f] = f :: fields (n+1)
    rw [List.cons_append,ih]

theorem fields_take (m n : Nat) :
    (fields n).take m = fields (min m n) := by
  simp only [fields,List.take_replicate]

theorem forward_source_query (run n : Nat) :
    emit run (n+2) false (rowF n).entry actualSource = [queryF n] := by
  simp [emit,emitBase,completeFamily,primary,atHead,actualSource,rowF,queryF,
    data,selector,marksOK,admits,seed,probe,legalSeed,ap,fields_step,dropHead]
  <;> omega

theorem second_forward_query (run n : Nat) :
    emit run (n+2) false (rowF n).entry (offerF2 n) = [queryF2 n] := by
  simp [emit,emitBase,completeFamily,primary,atHead,offerF2,rowF,queryF2,
    data,selector,marksOK,admits,seed,probe,legalSeed,ap,drop_fields]
  <;> omega

theorem first_backward_query (run n : Nat) :
    emit run (n+3) true (rowB n).entry actualSink = [queryB n] := by
  have bound : ¬ n+3 < n+1+1 := by omega
  simp [emit,emitBase,completeFamily,primary,atHead,actualSink,rowB,queryB,
    data,selector,marksOK,admits,seed,probe,legalSeed,ap,fields_step,dropHead,bound]
  <;> omega

theorem second_backward_query (run n : Nat) :
    emit run (n+3) true (rowB n).entry (offerB1 n) = [queryB2 n] := by
  simp [emit,emitBase,completeFamily,primary,atHead,offerB1,rowB,queryB2,
    data,selector,marksOK,admits,seed,probe,legalSeed,ap,drop_fields]
  <;> omega

/-- Prefix writes are not unknown-suffix reads. Local routing cannot
    delegate these results, regardless of the plan's field mask. -/
theorem prefix_write_is_unchanged_by_any_routing_mask
    (fromBase toBase n : Nat) (tail : Tail) (mask : List Nat) :
    routedMove ⟨⟨data fromBase (n+1) tail,false⟩,mask⟩ fromBase toBase [] [f,f] =
      some (val (data toBase (n+3) tail)) := by
  cases tail <;>
    simp [routedMove,moveE,move,data,ap,fields_step,dropHead,val]

theorem a_real_global_cut_keeps_only_nonempty_may
    (budget extra base : Nat) (tail : Tail) :
    cut budget (val (data base (budget+extra+1) tail)) =
      val (data base budget .ne) true := by
  have longer : budget+extra+1 > budget := by omega
  have within : budget ≤ budget+extra+1 := by omega
  simp only [cut,data,ap,val,fields_length]
  rw [ite_eq_left longer,fields_take,Nat.min_eq_left within]

/-- The proposal tests NORMAL precoverage at the boundary, after the
    ordinary global transfer limit. A cut result is D, so it cannot pass.
    `normalCover` may represent any complete retained NORMAL basis. -/
def publishAfterGlobalCut (limit : Nat) (q : Seed) (c : Value) (row : Row)
    (normalCover : Bool) : Option (Ap × Value) :=
  if !c.demand && normalCover then none else restricted limit [q] q c row

def edgeF (n : Nat) : Ap × Value :=
  ((queryF n).ap,val (data ret (n+2) .ne) true)
def edgeF2 (n : Nat) : Ap × Value :=
  ((queryF2 n).ap,val (data ret (n+2) .ne) true)
def edgeB (n : Nat) : Ap × Value :=
  ((queryB n).ap,val (data p (n+3) .ne) true)
def edgeB2 (n : Nat) : Ap × Value :=
  ((queryB2 n).ap,val (data p (n+3) .ne) true)

theorem forward_cut_passes_its_original_paired_c5 (n : Nat) (normalCover : Bool) :
    publishAfterGlobalCut (n+2) (queryF n)
      (val (data ret (n+2) .ne) true) (rowF n) normalCover = some (edgeF n) := by
  simp [publishAfterGlobalCut,restricted,queryF,rowF,edgeF,normalize,normalAp,
    intersectExit,selector,marksMeet,admits,data,ap,val,cut]

theorem second_forward_cut_passes_the_same_paired_c5 (n : Nat) (normalCover : Bool) :
    publishAfterGlobalCut (n+2) (queryF2 n)
      (val (data ret (n+2) .ne) true) (rowF n) normalCover = some (edgeF2 n) := by
  simp [publishAfterGlobalCut,restricted,queryF2,rowF,edgeF2,normalize,normalAp,
    intersectExit,selector,marksMeet,admits,data,ap,val,cut]

theorem backward_cut_passes_its_original_paired_c5 (n : Nat) (normalCover : Bool) :
    publishAfterGlobalCut (n+3) (queryB n)
      (val (data p (n+3) .ne) true) (rowB n) normalCover = some (edgeB n) := by
  simp [publishAfterGlobalCut,restricted,queryB,rowB,edgeB,normalize,normalAp,
    intersectExit,selector,marksMeet,admits,data,ap,val,cut]

theorem second_backward_cut_passes_the_same_paired_c5 (n : Nat) (normalCover : Bool) :
    publishAfterGlobalCut (n+3) (queryB2 n)
      (val (data p (n+3) .ne) true) (rowB n) normalCover = some (edgeB2 n) := by
  simp [publishAfterGlobalCut,restricted,queryB2,rowB,edgeB2,normalize,normalAp,
    intersectExit,selector,marksMeet,admits,data,ap,val,cut]

/-- Both directions have one ordinary prefix-growing branch:
    forward writes two fields; backward reverses the two field reads.
    The other branch is not removed from the real program. -/
def prefixSummaries (run limit : Nat) (backward : Bool) (row : Row)
    (actual : Offered) (mask : List Nat) (normalCover : Bool) : List (Ap × Value) :=
  (emit run limit backward row.entry actual).filterMap fun q => do
    let raw ← routedMove ⟨q,mask⟩ (if backward then ret else p)
      (if backward then p else ret) [] [f,f]
    publishAfterGlobalCut limit q (cut limit raw) row normalCover

theorem first_forward_publishes_the_cut (run n : Nat) (mask : List Nat)
    (normalCover : Bool) :
    prefixSummaries run (n+2) false (rowF n) actualSource mask normalCover =
      [edgeF n] := by
  simp only [prefixSummaries,forward_source_query,List.filterMap_cons,List.filterMap_nil,
    Bool.false_eq_true,ite_false]
  have moved := prefix_write_is_unchanged_by_any_routing_mask p ret n .must mask
  change routedMove ⟨queryF n,mask⟩ p ret [] [f,f] = _ at moved
  rw [moved]
  change (publishAfterGlobalCut (n+2) (queryF n)
    (cut (n+2) (val (data ret (n+3) .must))) (rowF n) normalCover).toList = _
  rw [show n+3 = (n+2)+0+1 by omega,
    a_real_global_cut_keeps_only_nonempty_may (n+2) 0 ret .must,
    forward_cut_passes_its_original_paired_c5]
  rfl

theorem second_forward_publishes_the_cut (run n : Nat) (mask : List Nat)
    (normalCover : Bool) :
    prefixSummaries run (n+2) false (rowF n) (offerF2 n) mask normalCover =
      [edgeF2 n] := by
  simp only [prefixSummaries,second_forward_query,List.filterMap_cons,List.filterMap_nil,
    Bool.false_eq_true,ite_false]
  have moved := prefix_write_is_unchanged_by_any_routing_mask p ret (n+1) .star mask
  change routedMove ⟨queryF2 n,mask⟩ p ret [] [f,f] = _ at moved
  rw [moved]
  change (publishAfterGlobalCut (n+2) (queryF2 n)
    (cut (n+2) (val (data ret (n+4) .star))) (rowF n) normalCover).toList = _
  rw [show n+4 = (n+2)+1+1 by omega,
    a_real_global_cut_keeps_only_nonempty_may (n+2) 1 ret .star,
    second_forward_cut_passes_the_same_paired_c5]
  rfl

theorem first_backward_publishes_the_cut (run n : Nat) (mask : List Nat)
    (normalCover : Bool) :
    prefixSummaries run (n+3) true (rowB n) actualSink mask normalCover =
      [edgeB n] := by
  simp only [prefixSummaries,first_backward_query,List.filterMap_cons,List.filterMap_nil,
    ite_true]
  have moved := prefix_write_is_unchanged_by_any_routing_mask ret p (n+1) .star mask
  change routedMove ⟨queryB n,mask⟩ ret p [] [f,f] = _ at moved
  rw [moved]
  change (publishAfterGlobalCut (n+3) (queryB n)
    (cut (n+3) (val (data p (n+4) .star))) (rowB n) normalCover).toList = _
  rw [show n+4 = (n+3)+0+1 by omega,
    a_real_global_cut_keeps_only_nonempty_may (n+3) 0 p .star,
    backward_cut_passes_its_original_paired_c5]
  rfl

theorem second_backward_publishes_the_cut (run n : Nat) (mask : List Nat)
    (normalCover : Bool) :
    prefixSummaries run (n+3) true (rowB n) (offerB1 n) mask normalCover =
      [edgeB2 n] := by
  simp only [prefixSummaries,second_backward_query,List.filterMap_cons,List.filterMap_nil,
    ite_true]
  have moved := prefix_write_is_unchanged_by_any_routing_mask ret p (n+2) .star mask
  change routedMove ⟨queryB2 n,mask⟩ ret p [] [f,f] = _ at moved
  rw [moved]
  change (publishAfterGlobalCut (n+3) (queryB2 n)
    (cut (n+3) (val (data p (n+5) .star))) (rowB n) normalCover).toList = _
  rw [show n+5 = (n+3)+1+1 by omega,
    a_real_global_cut_keeps_only_nonempty_may (n+3) 1 p .star,
    second_backward_cut_passes_the_same_paired_c5]
  rfl

/-- Scoped native applications of independent NE outputs. The three
    reached bindings are: covering uniform actual, ordinary MAY overlap,
    and a known/same prefix. No STAR-ancestor exception is used. -/
def bindIndependentNE (edge : Ap × Value) (a : Offered) : Option Offered :=
  if !edge.2.demand || edge.2.ap.tail != .ne then none else
  let accepted := if edge.1.tail == .must then
      a.ap.tail == .must && (dropHead a.ap.path edge.1.path).isSome
    else if edge.1.tail == .star then
      (dropHead edge.1.path a.ap.path).isSome ||
        ((a.ap.tail == .may || a.ap.tail == .ne || a.ap.tail == .must) &&
          (dropHead a.ap.path edge.1.path).isSome)
    else false
  if edge.1.base == a.ap.base && accepted then
    some ⟨{edge.2.ap with mark := a.ap.mark},true⟩
  else none

theorem first_forward_actual_supplies_the_second_call (n : Nat) :
    (bindIndependentNE (edgeF n) actualSource).map bindArgument =
      some (offerF2 n) := by
  simp [bindIndependentNE,edgeF,queryF,actualSource,offerF2,bindArgument,
    data,ap,val,fields_step,dropHead]

theorem second_forward_actual_reaches_the_sink_on_demand (n : Nat) :
    bindIndependentNE (edgeF2 n) (offerF2 n) =
      some ⟨data ret (n+2) .ne (some t),true⟩ := by
  simp [bindIndependentNE,edgeF2,queryF2,offerF2,data,ap,val]
  rw [show n+2 = (n+2)+0 by omega,drop_fields]
  simp

theorem second_reverse_actual_supplies_the_first_call (n : Nat) :
    (bindIndependentNE (edgeB n) actualSink).map bindReturn =
      some (offerB1 n) := by
  simp [bindIndependentNE,edgeB,queryB,actualSink,offerB1,bindReturn,
    data,ap,val,fields_step,dropHead]

theorem first_reverse_actual_reaches_the_uniform_source (n : Nat) :
    bindIndependentNE (edgeB2 n) (offerB1 n) =
      some ⟨data p (n+3) .ne (some t),true⟩ := by
  simp [bindIndependentNE,edgeB2,queryB2,offerB1,data,ap,val]
  rw [show n+3 = (n+3)+0 by omega,drop_fields]
  simp

theorem handoff_supplies_the_next_opposite_row (n : Nat) :
    (⟨(edgeF2 n).2.ap,(edgeF2 n).1⟩ : Row) = rowB n ∧
    (⟨(edgeB2 n).2.ap,(edgeB2 n).1⟩ : Row) = rowF (n+2) := by
  constructor <;> rfl

/-- Run-1 learns no complete double-write provider at limit 1: its
    ordinary root STAR result is already globally cut. -/
def run1Writer : Ap × Value :=
  (data p 0 .star,cut 1 (val (data ret 2 .star)))
def bootstrapRow : Row := ⟨run1Writer.2.ap,run1Writer.1⟩
def bootstrapQuery : Seed := ⟨data ret 1 .star,false⟩
def bootstrapEdge : Ap × Value :=
  (bootstrapQuery.ap,val (data p 1 .ne) true)
def run1VisibleMay : Ap × Value :=
  (data p 0 .star,val (data ret 0 .may) true)
def bootstrapVisibleMay : Ap × Value :=
  (bootstrapQuery.ap,val (data p 0 .may) true)

theorem run1_really_cuts_the_double_write :
    run1Writer = (data p 0 .star,val (data ret 1 .ne) true) ∧
    (bindIndependentNE run1Writer actualSource).map bindArgument =
      some ⟨data p 1 .ne (some t),true⟩ ∧
    bindIndependentNE run1Writer ⟨data p 1 .ne (some t),true⟩ =
      some ⟨data ret 1 .ne (some t),true⟩ := by decide

theorem run1_caller_visible_may_already_reaches_the_sink :
    moveE p ret [f,f] [] (data p 0 .star) =
      some (val (data ret 0 .may) true) ∧
    ((applyLoss run1VisibleMay actualSource).map bindArgument).bind
      (applyLoss run1VisibleMay) = some actualSink := by decide

theorem run2_really_bootstraps_the_first_forward_row (mask : List Nat)
    (normalCover : Bool) :
    prefixSummaries 2 1 true bootstrapRow actualSink mask normalCover =
      [bootstrapEdge] ∧
    (⟨bootstrapEdge.2.ap,bootstrapEdge.1⟩ : Row) = rowF 0 := by
  constructor
  · simp [prefixSummaries,bootstrapRow,run1Writer,bootstrapQuery,bootstrapEdge,
      actualSink,emit,emitBase,completeFamily,primary,atHead,selector,marksOK,
      admits,seed,probe,legalSeed,routedMove,moveE,move,dropHead,
      publishAfterGlobalCut,restricted,normalize,normalAp,intersectExit,
      marksMeet,cut,data,ap,val,fields,f,p,ret,t]
  · rfl

theorem bootstrap_caller_visible_may_renews_the_real_source :
    routedMove ⟨bootstrapQuery,[]⟩ ret p [f,f] [] =
      some (val (data p 0 .may) true) ∧
    publishAfterGlobalCut 1 bootstrapQuery (val (data p 0 .may) true)
      bootstrapRow true = some bootstrapVisibleMay ∧
    (((applyLoss bootstrapVisibleMay actualSink).map bindReturn).bind
      (applyLoss bootstrapVisibleMay)) =
      some ⟨data p 0 .may (some t),true⟩ := by decide

/-- Standard whole-object rules: the source marks root and descendants;
    the sink checks the root and descendants. No special pass operation. -/
def demandSink (a : Offered) : Bool :=
  a.ap.base == ret && a.ap.mark == some t && a.demand
def sourcePermission (a : Offered) : Bool :=
  a.ap.base == p && a.ap.mark == some t

theorem the_uniform_source_covers_every_required_field_path (n : Nat) :
    admits .must [] (fields n) = true := by
  cases n with
  | zero => rfl
  | succ n => simp [fields_step,admits]

def forwardCertificate (run n : Nat) (mask : List Nat) (normalCover : Bool) : Bool :=
  (prefixSummaries run (n+2) false (rowF n) actualSource mask normalCover).any fun e =>
    ((bindIndependentNE e actualSource).map bindArgument).any fun offered =>
      (prefixSummaries run (n+2) false (rowF n) offered mask normalCover).any fun e2 =>
        decide (e2 = edgeF2 n) && (bindIndependentNE e2 offered).any demandSink

def backwardCertificate (run n : Nat) (mask : List Nat) (normalCover : Bool) : Bool :=
  (prefixSummaries run (n+3) true (rowB n) actualSink mask normalCover).any fun e =>
    ((bindIndependentNE e actualSink).map bindReturn).any fun offered =>
      (prefixSummaries run (n+3) true (rowB n) offered mask normalCover).any fun e2 =>
        decide (e2 = edgeB2 n) && (bindIndependentNE e2 offered).any sourcePermission

theorem every_forward_pair_renews_the_demand_sink
    (run n : Nat) (mask : List Nat) (normalCover : Bool) :
    forwardCertificate run n mask normalCover = true := by
  unfold forwardCertificate
  rw [first_forward_publishes_the_cut]
  simp only [List.any_cons,List.any_nil,Bool.or_false]
  rw [first_forward_actual_supplies_the_second_call]
  simp only [Option.any_some]
  rw [second_forward_publishes_the_cut]
  have same : decide (edgeF2 n = edgeF2 n) = true := decide_eq_true rfl
  simp only [List.any_cons,List.any_nil,Bool.or_false,same,Bool.true_and]
  rw [second_forward_actual_reaches_the_sink_on_demand]
  rfl

theorem every_backward_pair_renews_the_real_source_permission
    (run n : Nat) (mask : List Nat) (normalCover : Bool) :
    backwardCertificate run n mask normalCover = true := by
  unfold backwardCertificate
  rw [first_backward_publishes_the_cut]
  simp only [List.any_cons,List.any_nil,Bool.or_false]
  rw [second_reverse_actual_supplies_the_first_call]
  simp only [Option.any_some]
  rw [second_backward_publishes_the_cut]
  have same : decide (edgeB2 n = edgeB2 n) = true := decide_eq_true rfl
  simp only [List.any_cons,List.any_nil,Bool.or_false,same,Bool.true_and]
  rw [first_reverse_actual_reaches_the_uniform_source]
  rfl

def bootstrap : Bool :=
  let candidates := prefixSummaries 2 1 true bootstrapRow actualSink [] true
  (candidates.any fun e => decide ((⟨e.2.ap,e.1⟩ : Row) = rowF 0)) &&
    ((((applyLoss bootstrapVisibleMay actualSink).map bindReturn).bind
      (applyLoss bootstrapVisibleMay)).any sourcePermission)

theorem bootstrap_is_constructed_from_run1_and_run2 : bootstrap = true := by decide

/-- Certificate projection of the complete witness pipeline. k=0 is
    run-3/limit 2; each successor traverses B(2k+4), F(2k+5).
    Masks and the retained NORMAL coverage answer may vary arbitrarily.
    The inputs of call 2 / reverse call 1 are computed, never assumed. -/
def forwardHandoffs (masks : Nat → List Nat) (covers : Nat → Bool) : Nat → Bool
  | 0 => bootstrap && forwardCertificate 3 0 (masks 3) (covers 3)
  | k+1 => forwardHandoffs masks covers k &&
      backwardCertificate (2*k+4) (2*k) (masks (2*k+4)) (covers (2*k+4)) &&
      forwardCertificate (2*k+5) (2*k+2) (masks (2*k+5)) (covers (2*k+5))

theorem all_forward_handoffs_keep_a_demand_witness
    (masks : Nat → List Nat) (covers : Nat → Bool) (k : Nat) :
    forwardHandoffs masks covers k = true := by
  induction k with
  | zero =>
    rw [forwardHandoffs,bootstrap_is_constructed_from_run1_and_run2,
      every_forward_pair_renews_the_demand_sink]
    rfl
  | succ k ih =>
    rw [forwardHandoffs,ih,every_backward_pair_renews_the_real_source_permission,
      every_forward_pair_renews_the_demand_sink]
    rfl

/-- The same typed terminal edge is regenerated at every root handoff.
    Its local DATA guidance can move deeper; that does not discharge this X.
    This definition is the unchanged Target rule for a demand sink/source. -/
inductive Control where
  | zero
  | demandTarget
  deriving DecidableEq, BEq, Repr
structure RootEdge where
  premise : Control
  conclusion : Control
  demand : Bool
  deriving DecidableEq, Repr
def repeatedTarget : RootEdge := ⟨.zero,.demandTarget,true⟩
/-- For the row [Target;ZERO], Dc accepts ZERO and Dp accepts
    ZERO/Target. DATA-to-control matching is not introduced. -/
def rootC5 (e : RootEdge) : Option RootEdge :=
  if e.premise == .zero && (e.conclusion == .zero || e.conclusion == .demandTarget)
  then some e else none

theorem the_terminal_passes_the_existing_paired_control_gate :
    rootC5 repeatedTarget = some repeatedTarget := by decide

def rootHandoff (masks : Nat → List Nat) (covers : Nat → Bool) (k : Nat) :
    List RootEdge :=
  if forwardHandoffs masks covers k then (rootC5 repeatedTarget).toList else []

theorem the_same_root_edge_repeats_without_an_iteration_limit
    (masks : Nat → List Nat) (covers : Nat → Bool) (k : Nat) :
    rootHandoff masks covers k = [repeatedTarget] := by
  rw [rootHandoff,all_forward_handoffs_keep_a_demand_witness]
  rfl

theorem outgoing_demand_is_never_empty
    (masks : Nat → List Nat) (covers : Nat → Bool) (k : Nat) :
    (rootHandoff masks covers k).isEmpty = false := by
  rw [the_same_root_edge_repeats_without_an_iteration_limit]
  rfl

end BoundedOrdinaryCycle

#print axioms BoundedOrdinaryCycle.fields_length
#print axioms BoundedOrdinaryCycle.fields_step
#print axioms BoundedOrdinaryCycle.fields_zero
#print axioms BoundedOrdinaryCycle.fields_nonempty
#print axioms BoundedOrdinaryCycle.fields_ne_next
#print axioms BoundedOrdinaryCycle.fields_next_ne
#print axioms BoundedOrdinaryCycle.fields_two
#print axioms BoundedOrdinaryCycle.drop_fields
#print axioms BoundedOrdinaryCycle.drop_fields_next
#print axioms BoundedOrdinaryCycle.fields_append_one
#print axioms BoundedOrdinaryCycle.fields_take
#print axioms BoundedOrdinaryCycle.forward_source_query
#print axioms BoundedOrdinaryCycle.second_forward_query
#print axioms BoundedOrdinaryCycle.first_backward_query
#print axioms BoundedOrdinaryCycle.second_backward_query
#print axioms BoundedOrdinaryCycle.prefix_write_is_unchanged_by_any_routing_mask
#print axioms BoundedOrdinaryCycle.a_real_global_cut_keeps_only_nonempty_may
#print axioms BoundedOrdinaryCycle.forward_cut_passes_its_original_paired_c5
#print axioms BoundedOrdinaryCycle.second_forward_cut_passes_the_same_paired_c5
#print axioms BoundedOrdinaryCycle.backward_cut_passes_its_original_paired_c5
#print axioms BoundedOrdinaryCycle.second_backward_cut_passes_the_same_paired_c5
#print axioms BoundedOrdinaryCycle.first_forward_publishes_the_cut
#print axioms BoundedOrdinaryCycle.second_forward_publishes_the_cut
#print axioms BoundedOrdinaryCycle.first_backward_publishes_the_cut
#print axioms BoundedOrdinaryCycle.second_backward_publishes_the_cut
#print axioms BoundedOrdinaryCycle.first_forward_actual_supplies_the_second_call
#print axioms BoundedOrdinaryCycle.second_forward_actual_reaches_the_sink_on_demand
#print axioms BoundedOrdinaryCycle.second_reverse_actual_supplies_the_first_call
#print axioms BoundedOrdinaryCycle.first_reverse_actual_reaches_the_uniform_source
#print axioms BoundedOrdinaryCycle.handoff_supplies_the_next_opposite_row
#print axioms BoundedOrdinaryCycle.run1_really_cuts_the_double_write
#print axioms BoundedOrdinaryCycle.run1_caller_visible_may_already_reaches_the_sink
#print axioms BoundedOrdinaryCycle.run2_really_bootstraps_the_first_forward_row
#print axioms BoundedOrdinaryCycle.bootstrap_caller_visible_may_renews_the_real_source
#print axioms BoundedOrdinaryCycle.every_forward_pair_renews_the_demand_sink
#print axioms BoundedOrdinaryCycle.every_backward_pair_renews_the_real_source_permission
#print axioms BoundedOrdinaryCycle.bootstrap_is_constructed_from_run1_and_run2
#print axioms BoundedOrdinaryCycle.the_uniform_source_covers_every_required_field_path
#print axioms BoundedOrdinaryCycle.all_forward_handoffs_keep_a_demand_witness
#print axioms BoundedOrdinaryCycle.the_terminal_passes_the_existing_paired_control_gate
#print axioms BoundedOrdinaryCycle.the_same_root_edge_repeats_without_an_iteration_limit
#print axioms BoundedOrdinaryCycle.outgoing_demand_is_never_empty
