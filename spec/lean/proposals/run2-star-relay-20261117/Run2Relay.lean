import NestedSTAR
namespace Run2Relay
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

-- Phase and shape, not a method/field name or a call-specific exception.
def cell (run : Nat) (back : Bool) (d : Ap) (a : Offered) : Bool :=
  run==2 && back && d.tail==.star && a.ap.tail==.star && d.path==a.ap.path

-- Same base/mark/budget gates as emitBase, specialized to two STAR tails.
-- Native runtime grammar checks stay outside this scalar policy as before.
def gates (k : Nat) (d : Ap) (a : Offered) : Bool :=
  k != 0 && marksOK (selector d) a.ap && d.base==a.ap.base &&
    decide (d.path.length≤k) && decide (a.ap.path.length≤k)

def primary (d : Ap) (a : Offered) : Seed :=
  let selected:=selector d
  seed selected a selected.path .star selected.e

def family (d : Ap) (a : Offered) : List Seed :=
  let q:=primary d a
  let raw:=q :: (if q.ap.mark.isSome then
    [{q with ap:={q.ap with mark:=none,mx:=[]},demand:=false}] else [])
  -- Reuse the current unchanged-head real-E map. No new E union/movement.
  if d.mark.isNone || a.ap.e.isEmpty then raw else raw.map (CarryPolicy.carry a)

def emit (run k : Nat) (back : Bool) (d : Ap) (a : Offered) : List Seed :=
  if cell run back d a then
    if gates k d a then family d a else []
  else HeadPolicy.emit run k back d a

def rawImage (run k : Nat) (back : Bool) (d : Ap) (offers : List Offered) : List Ap :=
  offers.flatMap fun a => (emit run k back d a).map Seed.ap

def restrictOne (run k : Nat) (back : Bool) (offers : List Offered)
    (raw : Ap) (c : Value) (row : Row) : Option (Ap × Value) := do
  if (rawImage run k back row.entry offers).any (fun p => decide (p=raw)) then
    let normalized:=normalize raw c
    let selected←intersectExit normalized.2 row.exit
    return normalize normalized.1 (cut (min k (row.exit.path.length+1)) selected)
  else none

theorem phase_and_shape_are_the_only_new_branch
    (run : Nat) (back : Bool) (d : Ap) (a : Offered) (hit : cell run back d a=true) :
    run=2 ∧ back=true ∧ d.tail=.star ∧ a.ap.tail=.star ∧ d.path=a.ap.path := by
  simpa [cell,Bool.and_assoc] using hit

theorem outside_the_new_cell_every_old_offer_is_unchanged
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (no : cell run back d a=false) :
    emit run k back d a=HeadPolicy.emit run k back d a := by simp [emit,no]

theorem run1_and_all_later_runs_keep_the_old_policy
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (not2 : run≠2) :
    emit run k back d a=HeadPolicy.emit run k back d a := by simp [emit,cell,not2]

theorem forward_runs_keep_the_old_policy (run k : Nat) (d : Ap) (a : Offered) :
    emit run k false d a=HeadPolicy.emit run k false d a := by simp [emit,cell]

theorem exact_MAY_NE_and_MUST_demands_are_unchanged
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (notStar : d.tail≠.star) :
    emit run k back d a=HeadPolicy.emit run k back d a := by simp [emit,cell,notStar]

theorem non_STAR_actuals_are_unchanged
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (notStar : a.ap.tail≠.star) :
    emit run k back d a=HeadPolicy.emit run k back d a := by simp [emit,cell,notStar]

theorem every_new_cell_was_previously_empty
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (hit : cell run back d a=true) :
    HeadPolicy.emit run k back d a=[] := by
  obtain ⟨r,b,dt,actualTail,head⟩:=phase_and_shape_are_the_only_new_branch run back d a hit
  subst run;subst back
  have selectedTail : (selector d).tail=.star := by
    unfold selector;split <;> simp_all
  have emptyPrimary : NonEmptyPolicy.primary 2 (selector d) a=[] := by
    simp only [NonEmptyPolicy.primary,selector_path,head,beq_self_eq_true,ite_true]
    simp [atHead,selectedTail,actualTail]
  have emptyFamily : completeFamily 2 (selector d) a=[] := by
    simp [completeFamily,emptyPrimary]
  simp [HeadPolicy.emit,CarryPolicy.emit,NonEmptyPolicy.emit,dt,emitBase,emptyFamily]

theorem bad_mark_base_or_budget_cannot_use_the_new_branch
    (k : Nat) (d : Ap) (a : Offered) (no : gates k d a=false) :
    emit 2 k true d a=HeadPolicy.emit 2 k true d a := by
  unfold emit
  split
  · rename_i yes
    rw [every_new_cell_was_previously_empty 2 k true d a yes]
    simp [no]
  · rfl

theorem no_old_C2_membership_is_removed
    (run k : Nat) (back : Bool) (d : Ap) (a : Offered) (q : Seed)
    (old : q∈HeadPolicy.emit run k back d a) : q∈emit run k back d a := by
  by_cases yes : cell run back d a=true
  · rw [every_new_cell_was_previously_empty run k back d a yes] at old
    cases old
  · have no : cell run back d a=false := by cases h : cell run back d a <;> simp_all
    simpa [emit,no] using old

theorem a_new_family_has_at_most_two_starts (d : Ap) (a : Offered) : (family d a).length≤2 := by
  unfold family
  dsimp only
  split <;> simp only [List.length_map, List.length_cons]
  all_goals split <;> simp

theorem carry_does_not_change_paths_tails_marks_or_layers (a : Offered) (q : Seed) :
    (CarryPolicy.carry a q).ap.path=q.ap.path ∧ (CarryPolicy.carry a q).ap.tail=q.ap.tail ∧
    (CarryPolicy.carry a q).ap.mark=q.ap.mark ∧ (CarryPolicy.carry a q).demand=q.demand := by
  unfold CarryPolicy.carry;split <;> simp

theorem every_new_family_member_has_the_requested_STAR_head
    (d : Ap) (a : Offered) (q : Seed) (member : q∈family d a) :
    q.ap.path=d.path ∧ q.ap.tail=.star := by
  unfold family at member
  dsimp only at member
  split at member
  · simp only [List.mem_cons] at member
    rcases member with rfl | companion
    · simp [primary,seed,selector];split <;> rfl
    · split at companion
      · simp only [List.mem_singleton] at companion;subst q
        simp [primary,seed,selector];split <;> rfl
      · cases companion
  · rcases List.mem_map.mp member with ⟨before,present,same⟩
    rw [←same]
    have keep:=carry_does_not_change_paths_tails_marks_or_layers a before
    simp only [keep.1,keep.2.1]
    simp only [List.mem_cons] at present
    rcases present with rfl | companion
    · simp [primary,seed,selector];split <;> rfl
    · split at companion
      · simp only [List.mem_singleton] at companion;subst before
        simp [primary,seed,selector];split <;> rfl
      · cases companion

theorem new_admission_has_no_field_limit_exception
    (k : Nat) (d : Ap) (a : Offered) (q : Seed)
    (yes : cell 2 true d a=true) (member : q∈emit 2 k true d a) :
    q.ap.path.length≤k ∧ q.ap.path.length≤d.path.length+1 := by
  simp only [emit,yes,ite_true] at member
  split at member
  · rename_i passed
    have gd : d.path.length≤k := by
      have parts:=passed;simp only [gates,Bool.and_eq_true] at parts
      exact of_decide_eq_true parts.1.2
    rw [(every_new_family_member_has_the_requested_STAR_head d a q member).1]
    exact ⟨gd,by omega⟩
  · cases member

theorem resumed_DEMAND_never_becomes_NORMAL (actual : Offered) (v : Value)
    (demand : actual.demand=true) : (v.demand || actual.demand)=true := by simp [demand]

theorem every_old_raw_C5_witness_is_retained
    (run k : Nat) (back : Bool) (d : Ap) (offers : List Offered) (raw : Ap)
    (old : raw∈HeadPolicy.rawImage run k back d offers) :
    raw∈rawImage run k back d offers := by
  rcases List.mem_flatMap.mp old with ⟨a,present,inside⟩
  rcases List.mem_map.mp inside with ⟨q,emitted,same⟩
  apply List.mem_flatMap.mpr
  refine ⟨a,present,List.mem_map.mpr ?_⟩
  exact ⟨q,no_old_C2_membership_is_removed run k back d a q emitted,same⟩

theorem every_new_raw_C5_witness_has_an_executable_offer
    (run k : Nat) (back : Bool) (d : Ap) (offers : List Offered) (raw : Ap)
    (inside : raw∈rawImage run k back d offers) :
    ∃ a∈offers,∃ q∈emit run k back d a,q.ap=raw := by
  rcases List.mem_flatMap.mp inside with ⟨a,present,atOffer⟩
  rcases List.mem_map.mp atOffer with ⟨q,emitted,same⟩
  exact ⟨a,present,q,emitted,same⟩

theorem every_old_paired_C5_result_is_unchanged
    (run k : Nat) (back : Bool) (offers : List Offered)
    (raw : Ap) (c : Value) (row : Row) (out : Ap × Value)
    (old : HeadPolicy.restrictOne run k back offers raw c row=some out) :
    restrictOne run k back offers raw c row=some out := by
  unfold HeadPolicy.restrictOne at old
  split at old
  · rename_i accepted
    have member : raw∈HeadPolicy.rawImage run k back row.entry offers := by
      simpa [List.any_eq_true] using accepted
    have fresh:=every_old_raw_C5_witness_is_retained run k back row.entry offers raw member
    have checked : (rawImage run k back row.entry offers).any (fun p => decide (p=raw))=true := by
      simpa [List.any_eq_true] using fresh
    simpa only [restrictOne,checked,ite_true] using old
  · simp at old

-- New raw STAR permission is required even at the global field cap.
-- EXACT-to-STAR normalization must never serve as its raw witness.
def capHead : Ap := ⟨0,[1],.star,none,[],[]⟩
theorem same_head_at_the_cap_has_its_own_raw_STAR_C5_witness :
    emit 2 1 true capHead ⟨capHead,false⟩=[⟨capHead,false⟩] ∧
    rawImage 2 1 true capHead [⟨capHead,false⟩]=[capHead] ∧
    restrictOne 2 1 true [⟨capHead,false⟩] capHead ⟨capHead,false,false⟩
      ⟨capHead,capHead⟩=some (capHead,⟨capHead,false,false⟩) := by decide +kernel

def marked : Ap := ⟨0,[],.star,some 7,[],[]⟩
def withE : Ap := {marked with e:=[1]}
theorem concrete_STAR_stays_DEMAND_with_a_conditional_NORMAL_FLOW_companion :
    emit 2 1 true marked ⟨marked,false⟩=
      [⟨marked,true⟩,⟨{marked with mark:=none},false⟩] := by decide +kernel

theorem actual_E_is_carried_only_by_the_existing_unchanged_head_rule :
    emit 2 1 true marked ⟨withE,false⟩=
      [⟨withE,true⟩,⟨{withE with mark:=none},false⟩] ∧
    emit 2 1 true {marked with mark:=none} ⟨withE,false⟩=
      [⟨{marked with mark:=none},false⟩] := by decide +kernel

theorem demand_E_is_not_erased_for_a_concrete_selector :
    emit 2 1 true withE ⟨marked,false⟩=
      [⟨withE,true⟩,⟨{withE with mark:=none},false⟩] := by decide +kernel

theorem wrong_mark_wrong_base_and_zero_budget_still_reject :
    emit 2 1 true marked ⟨{marked with mark:=some 8},false⟩=[] ∧
    emit 2 1 true marked ⟨{marked with base:=1},false⟩=[] ∧
    emit 2 0 true marked ⟨marked,false⟩=[] := by decide +kernel

theorem exact_demands_and_later_precise_STAR_demands_still_reject_STAR :
    emit 2 1 true {marked with tail:=.exact} ⟨marked,true⟩=[] ∧
    emit 3 2 false marked ⟨marked,true⟩=[] ∧
    emit 4 3 true marked ⟨marked,true⟩=[] := by decide +kernel

theorem mark_exclusion_gates_and_backward_MUST_rejection_are_retained :
    emit 2 1 true {marked with mark:=none,mx:=[7]} ⟨marked,false⟩=[] ∧
    emit 2 1 true marked ⟨{marked with tail:=.must},false⟩=[] := by decide +kernel

end Run2Relay
