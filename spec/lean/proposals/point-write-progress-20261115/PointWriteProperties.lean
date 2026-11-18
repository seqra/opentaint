import PointWriteReplay

namespace PointWriteProperties
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle BoundedRefinementPipeline
open NormalUniformNE NestedSavedReplayCycle NestedColdMachine OverwriteReplay PointWriteReplay
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 80000000

theorem strip_own_prefix (a b : Path) : dropHead a (a ++ b) = some b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [dropHead,ih]

theorem no_strict_descendant_guard_at_a_point (a : Path) (field : Nat) (rest : Path) :
    dropHead (a ++ field :: rest) a = none := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [dropHead,ih]

theorem successful_strip_gives_the_extension (a b rest : Path)
    (h : dropHead a b = some rest) : b = a ++ rest := by
  induction a generalizing b with
  | nil => simpa [dropHead] using h
  | cons f fs ih =>
    cases b with
    | nil => simp [dropHead] at h
    | cons g gs =>
      by_cases eq : f = g
      · subst g
        simp only [dropHead,ite_true] at h
        exact congrArg (f :: ·) (ih gs h)
      · simp [dropHead,eq] at h

theorem a_blocked_native_reply_is_demand_or_absent (run field : Nat)
    (head : Path) (a : Value) (h : blocked head a = true) :
    (NestedWriteReplay.keep run head field a).all (fun c => c.demand) = true := by
  have shape : a.ap.tail = .exact ∧ a.ap.mark = none :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  have suffix := (Bool.and_eq_true_iff.mp h).2
  cases hd : dropHead a.ap.path head with
  | none => simp [blocked,hd] at h
  | some word =>
    cases word with
    | nil => simp [blocked,hd] at h
    | cons f rest =>
      have eq := successful_strip_gives_the_extension a.ap.path head (f :: rest) hd
      have no := no_strict_descendant_guard_at_a_point a.ap.path f rest
      rw [←eq] at no
      simp [NestedWriteReplay.keep,no,hd,shape.1,shape.2]
      split <;> rfl

theorem every_kept_reply_is_the_native_reply (run field : Nat) (head : Path)
    (a result : Value) (h : keep run head field a = some result) :
    NestedWriteReplay.keep run head field a = some result := by
  unfold keep at h
  split at h
  · contradiction
  · exact h

theorem no_normal_native_reply_is_removed (run field : Nat) (head : Path)
    (a result : Value) (h : NestedWriteReplay.keep run head field a = some result)
    (normal : result.demand = false) : keep run head field a = some result := by
  unfold keep
  split
  · rename_i blocked
    have demand := a_blocked_native_reply_is_demand_or_absent run field head a blocked
    simp [h,normal] at demand
  · exact h

theorem all_nonexact_operands_keep_the_native_rule (run field : Nat) (head : Path)
    (a : Value) (h : a.ap.tail ≠ .exact) :
    keep run head field a = NestedWriteReplay.keep run head field a := by
  simp [keep,blocked,h]

theorem all_concrete_operands_keep_the_native_rule (run field mark : Nat) (head : Path)
    (a : Value) :
    keep run head field {a with ap := {a.ap with mark := some mark}} =
      NestedWriteReplay.keep run head field {a with ap := {a.ap with mark := some mark}} := by
  simp [keep,blocked]

theorem a_root_keep_is_unchanged (run field : Nat) (a : Value) :
    keep run [] field a = NestedWriteReplay.keep run [] field a := by
  cases hp : a.ap.path <;> simp [keep,blocked,dropHead,hp]

theorem no_child_cover_or_new_query_is_needed_for_the_point_correction
    (run field : Nat) (pointAt : Path) (next : Nat) (rest excluded : Path) :
    keep run (pointAt ++ next :: rest) field
      (val {point p pointAt .exact with e := excluded}) = none := by
  simp [keep,blocked,point,ap,val,strip_own_prefix]

/-- Fixed-plan filter bound; no assumption about later antichain cardinality. -/
theorem no_extra_postprocessing_for_fixed_native_contributions
    (run : Nat) (guards : List (Path × Nat)) (a : Value) (post : Value → List α) :
    ((guards.filterMap fun g => keep run g.1 g.2 a).flatMap post).length ≤
      ((guards.filterMap fun g => NestedWriteReplay.keep run g.1 g.2 a).flatMap post).length := by
  induction guards with
  | nil => simp
  | cons g gs ih =>
    cases old : NestedWriteReplay.keep run g.1 g.2 a with
    | none =>
      cases new : keep run g.1 g.2 a with
      | none => simpa [List.filterMap_cons,old,new] using ih
      | some result =>
        have same := every_kept_reply_is_the_native_reply run g.2 g.1 a result new
        simp [old] at same
    | some value =>
      cases new : keep run g.1 g.2 a with
      | none => simp only [List.filterMap_cons,old,new,List.flatMap_cons,List.length_append]; omega
      | some result =>
        have same := every_kept_reply_is_the_native_reply run g.2 g.1 a result new
        have eq := Option.some.inj (old.symm.trans same)
        subst result
        simp only [List.filterMap_cons,old,new,List.flatMap_cons,List.length_append]
        omega

/-- Concrete point service at one identity keep; all real exclusions stay. -/
def pointService (head excluded input output : Path) : Prop :=
  ∃ residual, dropHead head input = some residual ∧
    ExclusionChildCover.permits excluded residual = true ∧ output = input

theorem removed_guard_has_no_exact_point_witness (pointAt : Path) (field : Nat)
    (rest excluded output : Path) : ¬pointService (pointAt ++ field :: rest) excluded pointAt output := by
  rintro ⟨residual,hit,_,_⟩
  rw [no_strict_descendant_guard_at_a_point] at hit
  cases hit

/-- A concrete proper descendant belongs to its already admitted first-field
    STAR family; it need not be carried by the structural root point probe. -/
theorem first_field_family_keeps_the_actual_descendant (head rest suffix : Path)
    (field : Nat) :
    ∃ residual, head ++ field :: rest ++ suffix = (head ++ [field]) ++ residual := by
  exact ⟨rest ++ suffix,by simp [List.append_assoc]⟩

theorem same_head_may_has_empty_and_descendant_families (word : Path) :
    word = [] ∨ ∃ field rest, word = field :: rest := by
  cases word with
  | nil => exact Or.inl rfl
  | cons f fs => exact Or.inr ⟨f,fs,rfl⟩

end PointWriteProperties
#print axioms PointWriteProperties.strip_own_prefix
#print axioms PointWriteProperties.no_strict_descendant_guard_at_a_point
#print axioms PointWriteProperties.successful_strip_gives_the_extension
#print axioms PointWriteProperties.a_blocked_native_reply_is_demand_or_absent
#print axioms PointWriteProperties.every_kept_reply_is_the_native_reply
#print axioms PointWriteProperties.no_normal_native_reply_is_removed
#print axioms PointWriteProperties.all_nonexact_operands_keep_the_native_rule
#print axioms PointWriteProperties.all_concrete_operands_keep_the_native_rule
#print axioms PointWriteProperties.a_root_keep_is_unchanged
#print axioms PointWriteProperties.no_child_cover_or_new_query_is_needed_for_the_point_correction
#print axioms PointWriteProperties.no_extra_postprocessing_for_fixed_native_contributions
#print axioms PointWriteProperties.removed_guard_has_no_exact_point_witness
#print axioms PointWriteProperties.first_field_family_keeps_the_actual_descendant
#print axioms PointWriteProperties.same_head_may_has_empty_and_descendant_families
