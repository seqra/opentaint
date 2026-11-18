import RelevantRecurrence
namespace RelevantBounds
open RelevantReturn RelevantFrozen RelevantSteady RelevantRecurrence NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def outputWithinCaps (k : Nat) (rows : List Row) (d : Data) : Bool :=
  d.raw.all fun e => decide (e.2.ap.path.length≤k) &&
    rows.any (fun row => decide (e.2.ap.path.length≤row.exit.path.length+1))

theorem every_steady_output_keeps_the_existing_Dp_plus_one_and_global_caps (n : Nat) :
    outputWithinCaps (n+8) s10.rows forward.data=true ∧
    outputWithinCaps (n+8) forward.rows s10.data=true := by kernel_decide_open

theorem complete_worklist_fixed_points_have_no_hidden_pending_exact_or_STAR_work (n : Nat) :
    round true 5 (n+8) s10.rows s10.saved s10.complete s10.services forward.data=forward.data ∧
    round true 6 (n+8) forward.rows forward.saved forward.complete forward.services s10.data=s10.data := by
  exact ⟨RelevantRounds.roundF8 n,RelevantRounds.roundB8 n⟩

def allMarksAreT (s : State) : Bool :=
  s.rows.all (fun r => r.entry.mark==some 1 && r.exit.mark==some 1) &&
  s.saved.all (fun r => r.edge.1.mark==some 1 && r.edge.2.ap.mark==some 1) &&
  s.data.raw.all (fun e => e.1.mark==some 1 && e.2.ap.mark==some 1)

theorem one_mark_is_enough_for_the_entire_cold_prefix :
    [s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10].all allMarksAreT=true := by decide +kernel

theorem one_mark_is_enough_at_every_later_pair (n : Nat) :
    allMarksAreT (history true (2*n+9))=true ∧
    allMarksAreT (history true (2*n+10))=true := by
  rw [(every_uncapped_later_pair n).1,(every_uncapped_later_pair n).2]
  decide +kernel

def allForwardReturnsProtected (d : Data) : Bool := d.raw.all (fun e => e.2.h)

theorem all_steady_forward_records_keep_their_literal_protection :
    allForwardReturnsProtected forward.data=true := by decide +kernel

theorem the_same_normal_records_are_retained_without_any_new_provider :
    forward.saved=s10.saved ∧ forward.saved.length=6 ∧
    forward.complete=[] ∧ forward.services=[] ∧ forward.data.closed.length=2 := by decide +kernel

end RelevantBounds
