import ProtectedRecurrence
namespace ProtectedBounds
open ProtectedReturn ProtectedFrozen ProtectedSteady ProtectedRecurrence NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

def noNewLabels (s : State) : Bool :=
  s.data.raw.all (fun e => !e.2.h && e.1.mx.isEmpty && e.2.ap.mx.isEmpty) &&
  s.data.offers.all (fun vs => vs.all (fun v => !v.h && v.ap.mx.isEmpty))

theorem all_steady_published_memberships_remain_plain :
    noNewLabels forward=true ∧ noNewLabels s12=true := by decide +kernel

theorem no_protection_or_mark_exclusions_at_any_later_run (n : Nat) :
    noNewLabels (history true (2*n+11))=true ∧
    noNewLabels (history true (2*n+12))=true := by
  rw [(every_uncapped_later_pair n).1,(every_uncapped_later_pair n).2]
  decide +kernel

def outputWithinCaps (k : Nat) (rows : List Row) (d : Data) : Bool :=
  d.raw.all fun e => decide (e.2.ap.path.length≤k) &&
    rows.any (fun row => decide (e.2.ap.path.length≤row.exit.path.length+1))

theorem every_steady_output_has_a_paired_Dp_plus_one_budget (n : Nat) :
    outputWithinCaps (n+8) s12.rows forward.data=true ∧
    outputWithinCaps (n+8) forward.rows s12.data=true := by kernel_decide_open

theorem exact_and_STAR_priority_does_not_hide_unprocessed_work (n : Nat) :
    round true 5 (n+8) s12.rows s12.saved s12.complete s12.services forward.data=forward.data ∧
    round true 6 (n+8) forward.rows forward.saved forward.complete forward.services s12.data=s12.data := by
  exact ⟨ProtectedRounds.roundF8 n,ProtectedRounds.roundB8 n⟩

end ProtectedBounds
