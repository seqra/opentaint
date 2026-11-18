import BoundProof
import ScopedBounds
namespace BoundBounds
open BoundBody BoundBodyCold NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
local instance : BEq Row where beq a b := decide (a = b)
local instance : LawfulBEq Row where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

theorem closed_keys_reference_existing_raw_queries
    (run k : Nat) (rows : List Row) (saved : List Saved) (as : List Offered) (key : Ap)
    (inside : key∈certifyClosed run k rows saved as) :
    ∃ q∈queries run k false rows saved as,q.ap=key ∧ bodyClosed k q=true := by
  unfold certifyClosed at inside
  split at inside
  · cases inside
  · rcases List.mem_map.mp inside with ⟨q,hq,eq⟩
    have member := List.mem_filter.mp hq
    exact ⟨q,member.1,eq,member.2⟩

theorem closure_keeps_every_uncut_NORMAL_result (k : Nat) (q : Seed)
    (ok : bodyClosed k q=true) (c : Value) (inside : c∈colors.flatMap (fun m => gen m q)) :
    LayerCore.normalLayer c=true ∧ c.ap.path.length≤k := by
  have hs := ok
  simp only [bodyClosed,Bool.and_eq_true] at hs
  have leaf := List.all_eq_true.mp hs.2 c inside
  simp only [Bool.and_eq_true] at leaf
  exact ⟨leaf.1,of_decide_eq_true leaf.2⟩

def selected (run : Nat) (closed : List Ap) (images : List Value)
    (actual : Offered) (inputH : Bool) (xs : List Edge) :=
  xs.filter (fun e => !suppressNativeReply run closed images actual inputH e)

theorem selection_cannot_create_a_query_path_or_edge
    (run : Nat) (closed : List Ap) (images : List Value) (a : Offered) (inputH : Bool)
    (xs : List Edge) (e : Edge) (hit : e∈selected run closed images a inputH xs) : e∈xs :=
  (List.mem_filter.mp hit).1

theorem selected_delivery_is_no_larger_than_current_delivery
    (run : Nat) (closed : List Ap) (images : List Value) (a : Offered) (inputH : Bool)
    (xs : List Edge) : (selected run closed images a inputH xs).length≤xs.length :=
  List.length_filter_le _ _

theorem C5_output_budget_is_unchanged
    (run k : Nat) (back : Bool) (as : List Offered) (raw : Ap) (c : Value)
    (row : Row) (out : Ap × Value)
    (ok : HeadPolicy.restrictOne run k back as raw c row=some out) :
    out.2.ap.path.length≤min k (row.exit.path.length+1) :=
  ScopedBounds.C5_keeps_its_paired_output_cap run k back as raw c row out ok

def bounded (run : Nat) (old new : State) : Bool :=
  new.data.domains.all fun a => old.rows.all fun row =>
    (prepare run (limit run) (run%2==0) row old.rows old.saved a).all fun q =>
      decide (q.ap.path.length≤limit run ∧ q.ap.path.length≤row.entry.path.length+1)

theorem new_cold_history_has_no_entry_cap_exception :
    bounded 2 s1 s2=true ∧ bounded 3 s2 s3=true ∧ bounded 4 s3 s4=true ∧
    bounded 5 s4 s5=true ∧ bounded 6 s5 s6=true := by decide +kernel

theorem owner_DEMAND_rows_are_not_removed_by_this_delivery_rule :
    s5.rows.length=5 ∧ s5.data.raw.any (fun e => e.2.demand)=true ∧
    s5.saved.length=1 ∧ s5.data.closed.length=1 := by decide +kernel

theorem no_early_Target_is_canceled :
    s3.observationActive=true ∧ s4.sourceAllowed=true ∧
    s5.observationActive=false ∧ s5.report=true := by decide +kernel

theorem previously_emitted_Targets_remain_monotone
    (test : α → Bool) (advance : α → α) (fuel : Nat) (data : α) (seen : test data=true) :
    UniformSticky.seenDemand test advance fuel data=true :=
  ScopedBounds.already_emitted_Target_is_never_cancelled test advance fuel data seen

end BoundBounds
