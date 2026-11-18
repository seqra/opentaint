import RegularCertificate
namespace RegionSemantics
open RegularCertificate
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
set_option linter.unnecessarySimpa false

def appendAtBases (grammar : List Clause) (suffix : Word) : List Clause:=
  grammar.map fun c=>if c.callee.isNone then {c with chunk:=c.chunk++suffix} else c

theorem appending_the_actual_source_or_observer_word_needs_no_unfolding
    (d : Derives grammar owner word) :
    Derives (appendAtBases grammar suffix) owner (word++suffix) := by
  induction d with
  | base member=>
    apply Derives.base
    apply List.mem_map.mpr
    exact ⟨_,member,rfl⟩
  | @call callee word owner chunk member _ ih=>
    have own : ⟨owner,chunk,some callee⟩∈appendAtBases grammar suffix := by
      apply List.mem_map.mpr
      exact ⟨_,member,rfl⟩
    simpa only [List.append_assoc] using Derives.call own ih

-- Exact points use actual field strings. A source word a passes through a
-- prefix writer w as w++a. A reader r can observe q only when that same
-- string equals r++q. No uncut AP is enqueued to establish this equation.
def ConcreteRoute (gw gr : List Clause) (ow or : Nat) (source observed : Word) : Prop:=
  ∃w r, Derives gw ow w ∧ Derives gr or r ∧ w++source=r++observed

theorem a_complete_empty_product_preserves_every_exact_point_route
    (cw : (appendAtBases gw source).all (validatesClause w)=true)
    (cr : (appendAtBases gr observed).all (validatesClause r)=true)
    (empty : certifiesEmpty w r=true) :
    ¬ConcreteRoute gw gr w.start r.start source observed := by
  intro route
  obtain ⟨ww,rr,hw,hr,same⟩:=route
  have left:=appending_the_actual_source_or_observer_word_needs_no_unfolding (suffix:=source) hw
  have right:=appending_the_actual_source_or_observer_word_needs_no_unfolding (suffix:=observed) hr
  rw [same] at left
  exact all_true_ordinary_routes_survive_certified_pruning cw cr left right empty

-- Ordinary loop writes prepend, so their control path must be reversed
-- in the writer's language view. Reader traversal stays in forward order.
def writeFields (fields path : Word) : Word:=fields.foldl (fun p f=>f::p) path
theorem a_real_loop_write_trace_has_reversed_prefix_order (fields path : Word) :
    writeFields fields path=fields.reverse++path := by
  induction fields generalizing path with
  | nil=>rfl
  | cons f fields ih=>
    simpa [writeFields,List.foldl_cons,List.reverse_cons,List.append_assoc] using ih (f::path)

theorem reversing_each_instruction_does_not_mean_reversing_a_literal_chunk :
    writeFields [3,2] [1]=[2,3,1] := rfl

-- Existing run1/loop ports are not replaced by this proof view. Caller
-- adapters must cover every route to the goal, not just one selected pair.
theorem one_unmodelled_route_prevents_a_complete_slice_certificate :
    (false && certifiesEmpty writer reader)=false := rfl
end RegionSemantics
