import Std
import FlagMatchedSubsumption

/-!
Prepared stable U/H current-coverage reference for the fixed MAY/T/DEMAND
domain of FlagMatchedSubsumption. Certificates are current canonical region
views, not extra propagated rows or raw offer history. Rendering alone is
intentionally not an authority from which U/H can be reconstructed.
-/
namespace PlainCoverageFlagViews
open FlagMatchedSubsumption
set_option autoImplicit false

structure Geometry where
  owner : Nat
  path : List Nat
  deriving DecidableEq

def geometry (row : Row) : Geometry := ⟨row.owner,row.path⟩
def lift (g : Geometry) (flag : Bool) : Row := ⟨g.owner,g.path,flag⟩
def covers (short long : Geometry) : Bool :=
  decide (short.owner = long.owner) && prefixB short.path long.path
def presentGeometry (g : Geometry) (view : List Geometry) : Bool := decide (g ∈ view)

def addCurrent (view : List Geometry) (offered : Geometry) : List Geometry :=
  if view.any (fun old => covers old offered) then view
  else offered :: view.filter (fun old => !covers offered old)

structure Views where
  plain : List Geometry := []
  flagged : List Geometry := []
  deriving DecidableEq

def emptyViews : Views := ⟨[],[]⟩

def offer (state : Views) (incoming : Row) : Views :=
  if incoming.h then ⟨state.plain,addCurrent state.flagged (geometry incoming)⟩
  else ⟨addCurrent state.plain (geometry incoming),state.flagged⟩

def run (offered : List Row) : Views := offered.foldl offer emptyViews

/-- One visible flag-OR row per exact coordinate: H is rendered first; a
plain coordinate equal to a current H coordinate is not rendered twice. -/
def render (state : Views) : List Row :=
  state.flagged.map (fun g => lift g true) ++
    (state.plain.filter (fun g => !presentGeometry g state.flagged)).map (fun g => lift g false)

def logicalCover (state : Views) (candidate : Row) : Bool :=
  (if candidate.h then state.flagged else state.plain).any
    (fun provider => covers provider (geometry candidate))

def passRow (row : Row) : Row := row

theorem geometry_of_lift (g : Geometry) (flag : Bool) : geometry (lift g flag) = g := by
  cases g
  rfl

theorem flagged_offer_preserves_plain_current_view (state : Views) (incoming : Row)
    (flagged : incoming.h = true) : (offer state incoming).plain = state.plain := by
  simp [offer,flagged]

theorem plain_offer_preserves_flagged_current_view (state : Views) (incoming : Row)
    (plain : incoming.h = false) : (offer state incoming).flagged = state.flagged := by
  simp [offer,plain]

theorem plain_subsumption_reads_only_plain_certificates (state : Views) (g : Geometry) :
    logicalCover state (lift g false) = state.plain.any (fun provider => covers provider g) := by
  rw [logicalCover,geometry_of_lift]
  rfl

theorem flagged_subsumption_reads_only_flagged_certificates (state : Views) (g : Geometry) :
    logicalCover state (lift g true) = state.flagged.any (fun provider => covers provider g) := by
  rw [logicalCover,geometry_of_lift]
  rfl

theorem pass_transports_flag (row : Row) : (passRow row).h = row.h := rfl
theorem plain_pass_cannot_introduce_H (row : Row) (plain : row.h = false) :
    (passRow row).h = false := plain

def parentGeometry : Geometry := ⟨42,[]⟩
def childGeometry : Geometry := ⟨42,[7]⟩
def parent (flag : Bool) : Row := lift parentGeometry flag
def child (flag : Bool) : Row := lift childGeometry flag

def beforeUpgrade : Views := run [parent false,child false,parent true]
def afterUpgrade : Views := run [parent true,parent false,child false]

theorem old_negative_histories_now_have_identical_current_views :
    beforeUpgrade = afterUpgrade ∧
    beforeUpgrade = ⟨[parentGeometry],[parentGeometry]⟩ := by decide

theorem old_negative_histories_render_one_OR_upgraded_row :
    render beforeUpgrade = [parent true] ∧ render afterUpgrade = [parent true] := by decide

theorem upgraded_parent_keeps_plain_child_coverage_certificate :
    logicalCover beforeUpgrade (child false) = true ∧
    logicalCover afterUpgrade (child false) = true := by decide

theorem protected_parent_alone_does_not_cover_plain_child :
    logicalCover (run [parent true]) (child false) = false := by decide

theorem plain_parent_alone_does_not_cover_protected_child :
    logicalCover (run [parent false]) (child true) = false := by decide

theorem same_plain_arrivals_are_canonical_in_both_orders :
    run [parent false,child false] = run [child false,parent false] ∧
    render (run [parent false,child false]) = [parent false] := by decide

theorem same_protected_arrivals_are_canonical_in_both_orders :
    run [parent true,child true] = run [child true,parent true] ∧
    render (run [parent true,child true]) = [parent true] := by decide

theorem mixed_plain_parent_protected_child_keep_both_in_both_orders :
    render (run [parent false,child true]) = [child true,parent false] ∧
    render (run [child true,parent false]) = [child true,parent false] := by decide

theorem mixed_protected_parent_plain_child_keep_both_in_both_orders :
    render (run [parent true,child false]) = [parent true,child false] ∧
    render (run [child false,parent true]) = [parent true,child false] := by decide

theorem exact_flag_upgrade_has_one_visible_edge_and_both_certificates :
    run [parent false,parent true] = run [parent true,parent false] ∧
    (run [parent false,parent true]).plain = [parentGeometry] ∧
    (run [parent false,parent true]).flagged = [parentGeometry] ∧
    render (run [parent false,parent true]) = [parent true] := by decide

theorem rendering_is_not_a_plain_coverage_authority :
    render (run [parent true]) = render (run [parent false,parent true]) ∧
    logicalCover (run [parent true]) (child false) = false ∧
    logicalCover (run [parent false,parent true]) (child false) = true := by decide

theorem invisible_plain_certificate_can_change_current_view :
    run [parent true] ≠ run [parent true,parent false] ∧
    render (run [parent true]) = render (run [parent true,parent false]) := by decide

def childThenProtectedParent : Views := run [child false,child true,parent true]

theorem protected_child_can_be_compacted_and_visible_plain_child_stays_plain :
    childThenProtectedParent = ⟨[childGeometry],[parentGeometry]⟩ ∧
    render childThenProtectedParent = [parent true,child false] ∧
    logicalCover childThenProtectedParent (child true) = true := by decide

theorem changed_visible_child_flag_is_not_sticky_history :
    render (run [child false,child true]) = [child true] ∧
    render childThenProtectedParent = [parent true,child false] := by decide

theorem pass_of_visible_plain_child_does_not_inherit_parent_H :
    (passRow (child false)).h = false := rfl

theorem duplicate_offers_do_not_add_a_second_visible_edge :
    render (run [parent false,parent true,parent false,parent true]) = [parent true] := by decide

end PlainCoverageFlagViews
