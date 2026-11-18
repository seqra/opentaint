import FlagCold
import FlagProof
import ScopedBounds
namespace FlagBounds
open FlagBody FlagCold NonEmptyPolicy NonEmptyRestriction
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
    have mem := List.mem_filter.mp hq
    exact ⟨q,mem.1,eq,mem.2⟩

theorem closure_preserves_every_uncut_NORMAL_boundary_state (k : Nat) (q : Seed)
    (ok : bodyClosed k q=true) (c : Value) (inside : c∈colors.flatMap (fun m => gen m q)) :
    LayerCore.normalLayer c=true ∧ c.ap.path.length≤k := by
  have h := ok
  simp only [bodyClosed,Bool.and_eq_true] at h
  have leaf := List.all_eq_true.mp h.2 c inside
  simp only [Bool.and_eq_true] at leaf
  exact ⟨leaf.1,of_decide_eq_true leaf.2⟩

def selected (run : Nat) (closed : List Ap) (service : List LayerCore.Edge)
    (native : List Value) (a : Offered) (xs : List LayerCore.Edge) :=
  xs.filter (fun e => !suppressFlaggedReply run closed service native a false e)

theorem a_selected_reply_is_an_existing_member (run : Nat) (closed : List Ap)
    (service : List LayerCore.Edge) (native : List Value) (a : Offered)
    (xs : List LayerCore.Edge) (e : LayerCore.Edge)
    (hit : e∈selected run closed service native a xs) : e∈xs := (List.mem_filter.mp hit).1

theorem selection_does_not_create_field_paths (run : Nat) (closed : List Ap)
    (service : List LayerCore.Edge) (native : List Value) (a : Offered)
    (xs : List LayerCore.Edge) : (selected run closed service native a xs).length≤xs.length :=
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

theorem no_new_entry_cap_exception_in_the_new_cold_history :
    bounded 2 s1 s2=true ∧ bounded 3 s2 s3=true ∧ bounded 4 s3 s4=true ∧ bounded 5 s4 s5=true := by decide +kernel

theorem no_new_query_metadata_or_unrestricted_summary_archive :
    s3.data.closed.length=1 ∧ s5.data.closed.length=2 ∧ s6.data.closed=[] ∧ s5.saved.length=6 := by decide +kernel

theorem old_whole_and_mark_flags_are_not_falsely_set :
    s5.complete=[] ∧ s5.services=[] := by decide +kernel

theorem no_early_Target_is_canceled_to_get_the_new_stop :
    s3.observationActive=true ∧ s4.sourceAllowed=true ∧
    s5.observationActive=false ∧ stopped 5 s5=true := by decide +kernel

theorem already_emitted_Target_is_monotone
    (test : α → Bool) (advance : α → α) (fuel : Nat) (data : α) (seen : test data=true) :
    UniformSticky.seenDemand test advance fuel data=true :=
  ScopedBounds.already_emitted_Target_is_never_cancelled test advance fuel data seen

end FlagBounds
