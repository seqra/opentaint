import FieldFrozen
import ScopedHomogeneous
import ExactKernel
namespace FieldKernel
open FieldCycle FieldFrozen AlternatingCondition NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def point : Seed := ⟨fact p [f,g] .exact .t,false⟩
def desired : Value := value ret [h,h] .must .u false
def extra : Value := value ret [kfield] .must .u false

theorem exact_query_has_two_same_mark_NORMAL_returns :
    gen .t point=[desired,extra] := by decide +kernel

theorem exact_query_does_not_satisfy_the_deep_guard :
    CompletePoint.gen .t point=[value ret [h] .must .u false] := by decide +kernel

theorem both_marks_are_assigned_and_checked :
    colors.map Color.id=[1,2] ∧ colors.map (fun m => m.flip.id)=[2,1] := by decide +kernel

theorem disjoint_same_mark_return_rejects_every_h_output :
    intersectExit extra (fact ret [h] .star .u)=none ∧
    intersectExit extra (fact ret [h] .may .u)=none ∧
    intersectExit extra (fact ret [h,h] .star .u)=none := by decide +kernel

theorem desired_return_has_no_real_field_cut :
    cut 2 desired=desired ∧ cut 1 extra=extra := by decide +kernel

theorem normal_return_service_has_no_k_effect :
    s9.saved.all (fun e => e.edge.2.ap.path != [kfield])=true ∧
    s9.data.raw.all (fun e => e.2.ap.path != [kfield])=true ∧
    s10.data.raw.all (fun e => e.2.ap.path != [kfield])=true := by decide +kernel

theorem whole_and_mark_scoped_completion_really_fail :
    completePoint s9.data.raw point=false ∧
    ScopedCore.completeFor s9.data.raw point (colors.flatMap (fun m => gen m point)) 2=false ∧
    s9.complete=[] ∧ s9.services=[] ∧ s10.complete=[] ∧ s10.services=[] := by decide +kernel

theorem same_mark_missing_service_is_the_blocker :
    ScopedCore.completeFor [(point.ap,desired)] point [desired] 2=true ∧
    ScopedCore.completeFor [(point.ap,desired)] point [desired,extra] 2=false := by decide +kernel

theorem generator_has_one_output_mark (m : Color) (q : Seed) :
    (gen m q).all (fun c => c.ap.mark==some m.flip.id)=true := by
  unfold gen
  split
  · rfl
  · simp only [List.all_append,List.all_map,Bool.and_eq_true,Function.comp_def]
    constructor
    · exact ScopedHomogeneous.old_generator_has_one_output_mark m q
    · simp [value,fact]

theorem output_requires_input_mark (m : Color) (q : Seed) (c : Value)
    (member : c ∈ gen m q) : q.ap.mark=some m.id := by
  by_cases same : q.ap.mark=some m.id
  · exact same
  · have empty : gen m q=[] := by simp [gen,same]
    rw [empty] at member
    cases member

theorem raw_returns_are_homogeneous (q : Seed) :
    ∀ c ∈ colors.flatMap (fun m => gen m q),
      c.ap.mark=some (if q.ap.mark==some 1 then 2 else 1) :=
  ScopedHomogeneous.homogeneous_colored_family gen output_requires_input_mark generator_has_one_output_mark q

theorem full_mark_scoping_cannot_add_a_partial_certificate
    (current : List ScopedCore.Edge) (q : Seed) :
    ScopedCore.extra current q (colors.flatMap fun m => gen m q)=[] :=
  ScopedCore.homogeneous_query_gets_no_extra_cells current q _ _ (raw_returns_are_homogeneous q)

theorem coarse_and_exact_queries_are_still_admitted :
    (HeadPolicy.emit 5 8 false (fact p [] .may .t) ⟨point.ap,false⟩).contains (star p [f] .t)=true ∧
    HeadPolicy.emit 5 8 false (fact p [f] .ne .t) ⟨point.ap,false⟩=[point] := by decide +kernel

theorem coarse_read_returns_root_MAY_but_NORMAL_read_stays_below_h :
    consumeH (value ret [h] .may .u)=some (value ret [] .may .u) ∧
    consumeH desired=some (value ret [h] .must .u false) ∧
    consumeH extra=none := by decide +kernel

theorem child_NORMAL_does_not_cover_root_MAY :
    UniformActual.foldValues false [] [rootMay .u,value p [h] .must .u false]=
      [rootMay .u,value p [h] .must .u false] := by decide +kernel

end FieldKernel
