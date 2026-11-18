import BoundBounds
namespace BoundPreservation
open NonEmptyPolicy NonEmptyRestriction BoundBody
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
local instance : BEq Row where beq a b := decide (a = b)
local instance : LawfulBEq Row where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
deriving instance ReflBEq, LawfulBEq for Tail, Ap, Value, Saved

theorem every_current_owner_DEMAND_record_keeps_its_handoff_row
    (d : Data) (e : Edge) (inside : e∈d.raw) (needed : e.2.demand=true) :
    (⟨normalGuidance e.2.ap,normalGuidance e.1⟩ : Row)∈outputRows d := by
  unfold outputRows
  apply List.mem_eraseDups.mpr
  apply List.mem_filterMap.mpr
  exact ⟨e,inside,by simp [needed]⟩

theorem existing_NORMAL_records_are_never_deleted_from_persistence
    (back : Bool) (saved : List Saved) (d : Data) (s : Saved) (inside : s∈saved) :
    s∈outputSaved back saved d := by
  unfold outputSaved
  apply List.mem_eraseDups.mpr
  exact List.mem_append_left _ inside

theorem an_uncertified_owner_preserves_all_current_reply_memberships
    (run : Nat) (images : List Value) (a : Offered) (h : Bool) (xs : List Edge) :
    BoundBounds.selected run [] images a h xs=xs := by
  apply List.filter_eq_self.mpr
  intro e _
  simp [suppressNativeReply]

-- This pointwise theorem supplies a finite witness for every needed return.
-- It also preserves conjunctions: all witnesses belong to the same already
-- committed packet. No incompatible owner/caller context can be substituted.
theorem finite_joint_observations_have_simultaneous_native_witnesses
    (native : List Value) (needed : List Value) (observe : Value → Prop)
    (answer : ∀ c∈needed,∃ n∈native,BoundCore.covers n c=true)
    (monotone : ∀ n∈native,∀ c,BoundCore.covers n c=true → observe c → observe n)
    (allNeeded : ∀ c∈needed,observe c) :
    ∀ c∈needed,∃ n∈native,BoundCore.covers n c=true ∧ observe n := by
  intro c hc
  obtain ⟨n,hn,cover⟩ := answer c hc
  exact ⟨n,hn,cover,monotone n hn c cover (allNeeded c hc)⟩

theorem owner_closure_metadata_is_current_and_not_historical (run k : Nat)
    (rows : List Row) (saved : List Saved) (as : List Offered) (key : Ap)
    (hit : key∈certifyClosed run k rows saved as) :
    ∃ q∈queries run k false rows saved as,q.ap=key := by
  obtain ⟨q,hq,keyEq,_⟩ := BoundBounds.closed_keys_reference_existing_raw_queries
    run k rows saved as key hit
  exact ⟨q,hq,keyEq⟩

theorem a_pass_cannot_create_protection_from_a_valid_native_mark_context
    (ctx : BoundCore.Context) (c : Value)
    (localPlain : c.h=false) (inputPlain : ctx.inputH=false)
    (noRestoration : c.ap.mark.any ctx.restored.contains=false) :
    (BoundCore.bind ctx c).h=false := by
  simp [BoundCore.bind,BoundCore.flag,localPlain,inputPlain,noRestoration]

end BoundPreservation
