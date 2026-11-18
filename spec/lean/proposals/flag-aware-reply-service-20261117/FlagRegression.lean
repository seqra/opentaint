import FlagProof
import FlagOldUnrelatedCold
import FlagOldFieldCold
import FlagOldExactCold
import FlagOldMarkCold
namespace FlagRegression
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

theorem ordinary_Double_has_no_new_protected_reply_selection :
    (HeadOldDouble.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state6.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state7.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state8.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state9.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state10.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state11.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state12.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state13.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state14.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state15.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldDouble.state16.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_Growth_has_no_new_protected_reply_selection :
    (HeadOldGrowth.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldGrowth.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldGrowth.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldGrowth.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldGrowth.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldGrowth.state6.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldGrowth.state7.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldGrowth.state8.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_LongReader_has_no_new_protected_reply_selection :
    (HeadOldLongReader.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldLongReader.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldLongReader.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldLongReader.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldLongReader.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldLongReader.state6.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_Nested_has_no_new_protected_reply_selection :
    (HeadOldNested.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNested.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNested.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNested.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNested.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNested.state6.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNested.state7.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNested.state8.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNested.state9.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNested.state10.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_NestedDeep_has_no_new_protected_reply_selection :
    (HeadOldNestedDeep.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedDeep.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedDeep.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedDeep.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedDeep.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedDeep.state6.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_NestedExact_has_no_new_protected_reply_selection :
    (HeadOldNestedExact.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedExact.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedExact.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedExact.state4.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_NestedLarger_has_no_new_protected_reply_selection :
    (HeadOldNestedLarger.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state6.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state7.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state8.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state9.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state10.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state11.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedLarger.state12.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_NestedNegative_has_no_new_protected_reply_selection :
    (HeadOldNestedNegative.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedNegative.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedNegative.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedNegative.state4.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_NestedPositive_has_no_new_protected_reply_selection :
    (HeadOldNestedPositive.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedPositive.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedPositive.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedPositive.state4.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_NestedSurvivor_has_no_new_protected_reply_selection :
    (HeadOldNestedSurvivor.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedSurvivor.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedSurvivor.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedSurvivor.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedSurvivor.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldNestedSurvivor.state6.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_OldBB_has_no_new_protected_reply_selection :
    (HeadOldOldBB.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOldBB.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOldBB.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOldBB.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOldBB.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOldBB.state6.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_OldMethod_has_no_new_protected_reply_selection :
    (HeadOldOldMethod.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOldMethod.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOldMethod.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOldMethod.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOldMethod.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOldMethod.state6.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_OrdinaryTwo_has_no_new_protected_reply_selection :
    (HeadOldOrdinaryTwo.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOrdinaryTwo.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOrdinaryTwo.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOrdinaryTwo.state4.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_Overwrite_has_no_new_protected_reply_selection :
    (HeadOldOverwrite.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOverwrite.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOverwrite.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOverwrite.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOverwrite.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOverwrite.state6.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOverwrite.state7.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOverwrite.state8.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOverwrite.state9.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldOverwrite.state10.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_Postfix_has_no_new_protected_reply_selection :
    (HeadOldPostfix.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state6.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state7.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state8.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state9.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state10.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state11.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state12.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state13.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPostfix.state14.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_Prefix_has_no_new_protected_reply_selection :
    (HeadOldPrefix.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefix.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefix.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefix.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefix.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefix.state6.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefix.state7.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefix.state8.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_PrefixPostfix_has_no_new_protected_reply_selection :
    (HeadOldPrefixPostfix.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state6.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state7.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state8.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state9.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state10.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state11.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldPrefixPostfix.state12.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem ordinary_RoundTrip_has_no_new_protected_reply_selection :
    (HeadOldRoundTrip.state1.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldRoundTrip.state2.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldRoundTrip.state3.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldRoundTrip.state4.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldRoundTrip.state5.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldRoundTrip.state6.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldRoundTrip.state7.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldRoundTrip.state8.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldRoundTrip.state9.data.current.flatten).all (fun e => !e.2.h)=true ∧
    (HeadOldRoundTrip.state10.data.current.flatten).all (fun e => !e.2.h)=true := by decide +kernel

theorem HeadDeepCold_has_no_new_protected_reply_selection :
    (HeadDeepCold.s1.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadDeepCold.s2.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadDeepCold.s3.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadDeepCold.s4.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadDeepCold.s5.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadDeepCold.s6.data.raw).all (fun e => !e.2.h)=true := by decide +kernel

theorem HeadShallowCold_has_no_new_protected_reply_selection :
    (HeadShallowCold.s1.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadShallowCold.s2.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadShallowCold.s3.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadShallowCold.s4.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadShallowCold.s5.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadShallowCold.s6.data.raw).all (fun e => !e.2.h)=true := by decide +kernel

theorem HeadOldAlternating_has_no_new_protected_reply_selection :
    (HeadOldAlternating.state1.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadOldAlternating.state2.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadOldAlternating.state3.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadOldAlternating.state4.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadOldAlternating.state5.data.raw).all (fun e => !e.2.h)=true ∧
    (HeadOldAlternating.state6.data.raw).all (fun e => !e.2.h)=true := by decide +kernel

theorem old_guard_ineligible_plain_packet_cannot_use_the_new_path
    (run : Nat) (a : Offered) (xs : List FlagBody.Edge)
    (closed : List Ap) (service : List FlagBody.Edge) (native : List Value) (originalH : Bool)
    (plain : ∀ e∈xs,e.2.h=false)
    (old : ∀ e∈xs,FlagBody.suppress run closed a e=false) :
    xs.filter (fun e => !FlagBody.suppressFlaggedReply run closed service native a originalH e)=xs := by
  apply List.filter_eq_self.mpr
  intro e he
  have flag := plain e he
  have equal : (e.1,{e.2 with h:=false})=e := by
    rcases e with ⟨p,c⟩
    cases c
    simp_all
  have no : FlagBody.suppress run closed a (e.1,{e.2 with h:=false})=false := by rw [equal];exact old e he
  simp only [FlagProof.a_rejected_existing_shape_guard_rejects_both_flags run closed service native a originalH e no,Bool.not_false]

end FlagRegression
