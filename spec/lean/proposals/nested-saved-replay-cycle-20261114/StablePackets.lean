import SavedReplayCycle
namespace NestedSavedReplayCycle
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle BoundedLocalRouting BoundedRefinementPipeline NormalUniformNE
local instance : ReflBEq Nat where
  rfl := by intro a; exact Nat.beq_refl a
local instance : LawfulBEq Nat where
  eq_of_beq := by intro a b h; exact Nat.eq_of_beq_eq_true h
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

 theorem prepared_stable (n : Nat) (row : Row) (a : Offered)
    (hr : row ∈ stableRows) (ha : a ∈ domainF) :
    prepared (n+9) (n+8) row a = prepared 9 8 row a := by
  have l1 : ¬n+8<1 := by omega
  have l2 : ¬n+8<2 := by omega
  have l4 : ¬n+8<4 := by omega
  have l6 : ¬n+8<6 := by omega
  have b1 : 1 ≤ n+8 := by omega
  have b2 : 2 ≤ n+8 := by omega
  have b3 : 3 ≤ n+8 := by omega
  have nz : n+8 ≠ 0 := by omega
  simp only [stableRows,List.mem_cons,List.not_mem_nil,or_false] at hr
  simp only [domainF,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases hr with h | h | h | h <;> subst row <;>
    rcases ha with h | h | h | h <;> subst a <;>
    simp [prepared,NestedSavedReplayCycle.source,need,inputSelector,point,emit,emitBase,
      completeFamily,primary,atHead,selector,marksOK,admits,seed,probe,legalSeed,ap,
      dropHead,List.replicate_succ,List.replicate_zero,p,ret,f,g,
      l1,l2,l4,l6,b1,b2,b3,nz]

theorem prep_0_0 (exit : Ap) : prepared 9 8 ⟨inputSelector [],exit⟩ (NestedSavedReplayCycle.source 0) = [⟨point p [f] .star,false⟩,⟨point p [] .exact,false⟩] := by
  change prepared 9 8 ⟨inputSelector [],outputSelector []⟩ (NestedSavedReplayCycle.source 0) = [⟨point p [f] .star,false⟩,⟨point p [] .exact,false⟩]
  decide

theorem prep_0_1 (exit : Ap) : prepared 9 8 ⟨inputSelector [],exit⟩ (NestedSavedReplayCycle.source 1) = [⟨point p [f] .star,false⟩,⟨point p [] .exact,false⟩] := by
  change prepared 9 8 ⟨inputSelector [],outputSelector []⟩ (NestedSavedReplayCycle.source 1) = [⟨point p [f] .star,false⟩,⟨point p [] .exact,false⟩]
  decide

theorem prep_0_2 (exit : Ap) : prepared 9 8 ⟨inputSelector [],exit⟩ (NestedSavedReplayCycle.source 2) = [⟨point p [f] .star,false⟩,⟨point p [] .exact,false⟩] := by
  change prepared 9 8 ⟨inputSelector [],outputSelector []⟩ (NestedSavedReplayCycle.source 2) = [⟨point p [f] .star,false⟩,⟨point p [] .exact,false⟩]
  decide

theorem prep_0_3 (exit : Ap) : prepared 9 8 ⟨inputSelector [],exit⟩ need = [⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩] := by
  change prepared 9 8 ⟨inputSelector [],outputSelector []⟩ need = [⟨point p [] .exact,false⟩,⟨point p [] .star,false⟩,⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩]
  decide

theorem prep_1_0 (exit : Ap) : prepared 9 8 ⟨inputSelector [f],exit⟩ (NestedSavedReplayCycle.source 0) = [⟨point p [f,g] .star,false⟩,⟨point p [f] .exact,false⟩] := by
  change prepared 9 8 ⟨inputSelector [f],outputSelector []⟩ (NestedSavedReplayCycle.source 0) = [⟨point p [f,g] .star,false⟩,⟨point p [f] .exact,false⟩]
  decide

theorem prep_1_1 (exit : Ap) : prepared 9 8 ⟨inputSelector [f],exit⟩ (NestedSavedReplayCycle.source 1) = [⟨point p [f,f] .star,false⟩,⟨point p [f] .exact,false⟩] := by
  change prepared 9 8 ⟨inputSelector [f],outputSelector []⟩ (NestedSavedReplayCycle.source 1) = [⟨point p [f,f] .star,false⟩,⟨point p [f] .exact,false⟩]
  decide

theorem prep_1_2 (exit : Ap) : prepared 9 8 ⟨inputSelector [f],exit⟩ (NestedSavedReplayCycle.source 2) = [⟨point p [f,f] .star,false⟩,⟨point p [f] .exact,false⟩] := by
  change prepared 9 8 ⟨inputSelector [f],outputSelector []⟩ (NestedSavedReplayCycle.source 2) = [⟨point p [f,f] .star,false⟩,⟨point p [f] .exact,false⟩]
  decide

theorem prep_1_3 (exit : Ap) : prepared 9 8 ⟨inputSelector [f],exit⟩ need = [⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩] := by
  change prepared 9 8 ⟨inputSelector [f],outputSelector []⟩ need = [⟨point p [f] .exact,false⟩,⟨point p [f] .star,false⟩,⟨point p [f,f] .exact,false⟩,⟨point p [f,f] .star,false⟩]
  decide

def cell (run limit : Nat) (row : Row) (a : Offered) : List Edge :=
 let qs := prepared run limit row a
 qs.flatMap fun q => (leafReplay q.ap).filterMap fun raw =>
    if normalPrecovered q.ap raw then none
    else restricted limit qs q (cut limit raw) row

 theorem cell_stable (n : Nat) (row : Row) (a : Offered)
    (hr : row ∈ stableRows) (ha : a ∈ domainF) :
    cell (n+9) (n+8) row a = cell 9 8 row a := by
  have l1 : ¬n+8<1 := by omega
  have l2 : ¬n+8<2 := by omega
  have l3 : ¬n+8<3 := by omega
  have l4 : ¬n+8<4 := by omega
  have l5 : ¬n+8<5 := by omega
  have l6 : ¬n+8<6 := by omega
  have l7 : ¬n+8<7 := by omega
  have l8 : ¬n+8<8 := by omega
  have high : 2 ≤ n+8 := by omega
  simp only [cell,prepared_stable n row a hr ha]
  simp only [stableRows,List.mem_cons,List.not_mem_nil,or_false] at hr
  simp only [domainF,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases hr with h | h | h | h <;> subst row <;>
    rcases ha with h | h | h | h <;> subst a <;>
  all_goals simp only [prep_0_0,prep_0_1,prep_0_2,prep_0_3,prep_1_0,prep_1_1,prep_1_2,prep_1_3]
  all_goals simp [prepared,NestedSavedReplayCycle.source,need,inputSelector,outputSelector,point,
      emit,emitBase,completeFamily,primary,atHead,selector,marksOK,admits,seed,probe,
      legalSeed,ap,dropHead,List.replicate_succ,List.replicate_zero,p,ret,f,g,
      leafReplay,savedRead,savedWrite,moveE,move,normalPrecovered,restricted,
      normalize,normalAp,intersectExit,marksMeet,exactAt,cut,val,
      l1,l2,l3,l4,l5,l6,l7,l8,high,List.eraseDups,List.eraseDupsBy,List.eraseDupsBy.loop]


theorem flatMap_equal_on_members (xs : List α) (left right : α → List β)
    (same : ∀ x ∈ xs, left x = right x) : xs.flatMap left = xs.flatMap right := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [same x (by simp)]
      rw [ih (by intro a ha; exact same a (by simp [ha]))]

def fromRows (run limit : Nat) (rows : List Row) (domain : List Offered) : List Edge :=
  sortBy (fun e => e.1.path.length*2+e.2.ap.path.length)
    ((rows.flatMap fun row => domain.flatMap fun a => cell run limit row a).eraseDups)

theorem candidates_are_complete_cells (run limit : Nat) (domain : List Offered) :
    candidates run limit domain = fromRows run limit stableRows domain := rfl

theorem all_large_packets_are_stable (n : Nat) (domain : List Offered)
    (subset : ∀ a ∈ domain, a ∈ domainF) :
    fromRows (n+9) (n+8) stableRows domain = fromRows 9 8 stableRows domain := by
  have same := flatMap_equal_on_members stableRows
    (fun row => domain.flatMap fun a => cell (n+9) (n+8) row a)
    (fun row => domain.flatMap fun a => cell 9 8 row a) (by
      intro row hr
      apply flatMap_equal_on_members
      intro a ha
      exact cell_stable n row a hr (subset a ha))
  exact congrArg
    (fun es => sortBy (fun e => e.1.path.length*2+e.2.ap.path.length) es.eraseDups) same

theorem every_large_forward_packet (n : Nat) :
    fromRows (n+9) (n+8) stableRows domainF = parentPubs := by
  rw [all_large_packets_are_stable n domainF (by intro _ h; exact h)]
  exact full_forward_packet_at_run9

theorem every_large_backward_packet (n : Nat) :
    fromRows (n+9) (n+8) stableRows domainB = parentPubs := by
  rw [all_large_packets_are_stable n domainB (by
    intro a h
    simp only [domainB,List.mem_cons,List.not_mem_nil,or_false] at h
    subst a
    simp [domainF])]
  decide

def advance (run limit : Nat) (rows : List Row) : List Row :=
  nextRows (fromRows run limit rows (if run % 2 == 0 then domainB else domainF))

theorem handoff_fixed_point_for_every_later_run (n : Nat) :
    advance (n+9) (n+8) stableRows = stableRows := by
  unfold advance
  split
  · rw [every_large_backward_packet,the_complete_four_row_handoff_is_unchanged]
  · rw [every_large_forward_packet,the_complete_four_row_handoff_is_unchanged]

def repeatFromRun9 : Nat → List Row
  | 0 => stableRows
  | n+1 => advance (n+9) (n+8) (repeatFromRun9 n)

theorem uncapped_recurrence (n : Nat) : repeatFromRun9 n = stableRows := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [repeatFromRun9,ih,handoff_fixed_point_for_every_later_run]

theorem outgoing_demand_is_never_empty (n : Nat) :
    (repeatFromRun9 n).isEmpty = false := by
  rw [uncapped_recurrence]
  decide

end NestedSavedReplayCycle

#print axioms NestedSavedReplayCycle.prepared_stable
#print axioms NestedSavedReplayCycle.prep_0_0
#print axioms NestedSavedReplayCycle.prep_0_1
#print axioms NestedSavedReplayCycle.prep_0_2
#print axioms NestedSavedReplayCycle.prep_0_3
#print axioms NestedSavedReplayCycle.prep_1_0
#print axioms NestedSavedReplayCycle.prep_1_1
#print axioms NestedSavedReplayCycle.prep_1_2
#print axioms NestedSavedReplayCycle.prep_1_3
#print axioms NestedSavedReplayCycle.cell_stable
#print axioms NestedSavedReplayCycle.flatMap_equal_on_members
#print axioms NestedSavedReplayCycle.candidates_are_complete_cells
#print axioms NestedSavedReplayCycle.all_large_packets_are_stable
#print axioms NestedSavedReplayCycle.every_large_forward_packet
#print axioms NestedSavedReplayCycle.every_large_backward_packet
#print axioms NestedSavedReplayCycle.handoff_fixed_point_for_every_later_run
#print axioms NestedSavedReplayCycle.uncapped_recurrence
#print axioms NestedSavedReplayCycle.outgoing_demand_is_never_empty
