import NDProjection

/- Rule-owned per-result bookkeeping. The outer immutable key includes the
   occurrence/action/statement, origin, and result geometry/full mark.
   Support metadata stays in the rule owner, outside MethodEdgeStore. -/
namespace ExactDemand.ResultLanes
open ExactDemand NDProjection
set_option autoImplicit false

structure Key where
  occurrence : Nat
  statement : Nat
  action : Nat
  origin : Origin
  conclusion : Pattern
  deriving DecidableEq, Repr

structure Row where
  key : Key
  layer : Layer
  protectedMark : Bool
  deriving DecidableEq, Repr

def covers (old incoming : Row) : Bool :=
  decide (old.key = incoming.key) && decide (old.layer = incoming.layer) &&
    (!incoming.protectedMark || old.protectedMark)

structure State where
  seen : List Row := []
  pending : List Row := []
  deriving DecidableEq, Repr

def offer (state : State) (row : Row) : State × Bool :=
  if state.seen.any (fun old => covers old row) then (state,false)
  else (⟨state.seen ++ [row],state.pending ++ [row]⟩,true)

theorem demand_result_does_not_hide_later_normal (key : Key) (oldFlag newFlag : Bool) :
    covers ⟨key,.demand,oldFlag⟩ ⟨key,.normal,newFlag⟩ = false := by
  change (decide (key = key) && false && (!newFlag || oldFlag)) = false
  simp only [Bool.and_false, Bool.false_and]

theorem normal_result_does_not_hide_demand (key : Key) (oldFlag newFlag : Bool) :
    covers ⟨key,.normal,oldFlag⟩ ⟨key,.demand,newFlag⟩ = false := by
  change (decide (key = key) && false && (!newFlag || oldFlag)) = false
  simp only [Bool.and_false, Bool.false_and]

theorem unprotected_result_does_not_hide_protection_upgrade (key : Key) (layer : Layer) :
    covers ⟨key,layer,false⟩ ⟨key,layer,true⟩ = false := by
  change (decide (key = key) && decide (layer = layer) && false) = false
  exact Bool.and_false _

theorem protected_result_keeps_protection (key : Key) (layer : Layer) (incomingFlag : Bool) :
    covers ⟨key,layer,true⟩ ⟨key,layer,incomingFlag⟩ = true := by
  simp only [covers, decide_true, Bool.or_true, Bool.and_self]

theorem both_layers_are_enqueued_for_same_rule_origin (key : Key) :
    offer ⟨[⟨key,.demand,false⟩], [⟨key,.demand,false⟩]⟩ ⟨key,.normal,false⟩ =
      (⟨[⟨key,.demand,false⟩,⟨key,.normal,false⟩],
        [⟨key,.demand,false⟩,⟨key,.normal,false⟩]⟩,true) := by
  simp only [offer, List.any_cons, List.any_nil, demand_result_does_not_hide_later_normal,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]

theorem pending_result_is_never_erased (state : State) (row pending : Row)
    (member : pending ∈ state.pending) : pending ∈ (offer state row).1.pending := by
  unfold offer
  split
  · exact member
  · exact List.mem_append_left _ member

end ExactDemand.ResultLanes
