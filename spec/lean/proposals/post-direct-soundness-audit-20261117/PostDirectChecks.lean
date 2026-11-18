import PostDirectReference
namespace PostDirectChecks
open NonEmptyPolicy NonEmptyRestriction NestedSavedReplayCycle NestedColdMachine
open PrefixPointAudit
set_option maxRecDepth 32768
set_option maxHeartbeats 160000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def targetDemand (c : Config) (st : ReplayCases.Frame) : Bool :=
  (st.data.offers.getLast!).any (fun a=>a.demand && observes c a)
def dataOnlyStop (st : ReplayCases.Frame) : Bool:=st.rows.all List.isEmpty
def frontierEmpty (c : Config) (st : ReplayCases.Frame) : Bool:=dataOnlyStop st && !targetDemand c st

theorem an_observation_DEMAND_forbids_the_empty_frontier_stop
    (c : Config) (st : ReplayCases.Frame) (pending : targetDemand c st=true) :
    frontierEmpty c st=false := by simp [frontierEmpty,pending]

def pack : Config := ⟨[([],[1])],[],[],[1],.exact,[],1,[],.may⟩
def packFrame : Nat → ReplayCases.Frame
 | 0=>⟨{},[[],[]],[[],[]]⟩
 | n+1=>(step pack (n+1) (packFrame n)).1

theorem the_saved_normal_pack_service_does_not_make_the_run1_result_precise :
    dataOnlyStop (packFrame 1)=true ∧ targetDemand pack (packFrame 1)=true ∧
    frontierEmpty pack (packFrame 1)=false := by decide +kernel

theorem the_unchanged_pack_case_keeps_its_NORMAL_observation_at_run3 :
    (scan pack).stop=3 ∧ (scan pack).fixed=true ∧ (scan pack).missing=[] ∧ (scan pack).extra=[] := by decide +kernel

theorem the_pack_backward_offer_keeps_its_real_field_limit :
    ((packFrame 2).data.domains[0]!).all (fun a=>decide (a.ap.path.length≤1))=true := by decide +kernel

-- The native controls below are source/condition/action tests; their
-- marked rule engine is not added to this neutral prefix reference.
-- This theorem explains why a shorter first-field query does NOT assert
-- uniform taint at its shorter head, including when actual is MUST.
theorem first_new_field_from_MUST_uses_STAR_not_a_stronger_MUST
    (run : Nat) (head : Path) (first : Nat) (rest : Path) :
    NonEmptyPolicy.primary run
      (⟨0,head,.may,some 7,[],[]⟩ : Ap)
      (⟨⟨0,head++first::rest,.must,some 7,[],[]⟩,false⟩ : Offered)=
      [seed ⟨0,head,.may,some 7,[],[]⟩
        ⟨⟨0,head++first::rest,.must,some 7,[],[]⟩,false⟩ (head++[first]) .star] := by
  have unequal : head≠head++first::rest := by
    intro h
    have longer : head.length < (head++first::rest).length := by
      rw [List.length_append,List.length_cons]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos rest.length)
    exact (Nat.ne_of_lt longer) (congrArg List.length h)
  have different : (head==head++first::rest)=false := by
    exact beq_eq_false_iff_ne.mpr unequal
  unfold NonEmptyPolicy.primary
  dsimp only
  rw [different]
  simp only [Bool.false_eq_true,ite_false,PointWriteProperties.strip_own_prefix]
  cases rest <;> rfl

-- The same legal first-field cell in current C2. These are constructive
-- executable witnesses, with full-mark and FLOW companion layers shown.
theorem current_C2_does_not_strengthen_a_deeper_uniform_actual :
    (Run2Relay.emit 5 4 false
      (⟨0,[],.may,some 7,[],[]⟩ : Ap)
      ⟨⟨0,[1,2],.must,some 7,[],[]⟩,false⟩).map (fun q=>(q.ap.path,q.ap.tail,q.ap.mark,q.demand))=
      [([1],.star,some 7,true),([1],.star,none,false),([],.exact,none,false)] := by decide +kernel

theorem current_C2_retains_the_definite_MUST_lane_at_its_own_head :
    (Run2Relay.emit 7 6 false
      (⟨0,[1,2],.may,some 7,[],[]⟩ : Ap)
      ⟨⟨0,[1,2],.must,some 7,[],[]⟩,false⟩).map (fun q=>(q.ap.path,q.ap.tail,q.ap.mark,q.demand))=
      [([1,2],.must,some 7,false)] := by decide +kernel

theorem backward_QUERY_cannot_use_a_MUST_actual :
    Run2Relay.emit 6 5 true
      (⟨0,[],.may,some 7,[],[]⟩ : Ap)
      ⟨⟨0,[1,2],.must,some 7,[],[]⟩,false⟩=[] := by decide +kernel
end PostDirectChecks
