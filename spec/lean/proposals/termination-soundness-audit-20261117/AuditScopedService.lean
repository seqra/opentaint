import AuditServices
namespace AuditScopedService
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

-- Proof-only structural view of existing callback ownership, not a new
-- MethodEdgeStore/query key and not a hash-only identifier.
structure Frame where
  run : Nat := 3
  currentReply : Bool := true
  actualDemand : Bool := false
  method : Nat := 0
  block : Nat := 0
  revision : Nat := 0
  entryPort : Nat := 0
  returnPort : Nat := 0
  continuation : Nat := 0
  backward : Bool := false
  fullMode : Bool := true
  original : List Ap := []
  actual : Ap
  actualH : Bool := false
  deriving DecidableEq, Repr

structure Image where
  frame : Frame
  value : Value

def values (frame : Frame) (images : List Image) : List Value :=
  images.filterMap fun image => if image.frame=frame then some image.value else none

theorem every_native_witness_has_the_same_complete_application_frame
    (frame : Frame) (images : List Image) (v : Value) (hit : v∈values frame images) :
    ∃ image∈images,image.frame=frame ∧ image.value=v := by
  obtain ⟨image,inside,selected⟩ := List.mem_filterMap.mp hit
  split at selected
  · rename_i same
    exact ⟨image,inside,same,Option.some.inj selected⟩
  · contradiction

def complete (frame : Frame) (images : List Image) (q : Seed) (raw : List Value)
    (region : Ap) (ctx : BoundCore.Context) (h : Bool) : Bool :=
  decide (frame.run>=3) && frame.currentReply && !frame.actualDemand && frame.fullMode && !frame.backward &&
    decide (q.ap=frame.actual ∧ ctx.inputH=frame.actualH) &&
    BoundCore.completeFor (values frame images) q raw region ctx h

theorem selected_bound_returns_have_same_frame_NORMAL_full_mark_and_H_witnesses
    (frame : Frame) (images : List Image) (q : Seed) (raw : List Value)
    (region : Ap) (ctx : BoundCore.Context) (h : Bool)
    (yes : complete frame images q raw region ctx h=true)
    (c : Value) (present : c∈raw) (flag : BoundCore.flag ctx c=h)
    (overlap : ReplyCore.overlaps c.ap region=true) :
    ∃ image∈images,image.frame=frame ∧ image.value.demand=false ∧
      image.value.h=h ∧ image.value.ap.mark=c.ap.mark ∧
      BoundCore.covers image.value (BoundCore.bind ctx c)=true := by
  have parts := yes
  simp only [complete,Bool.and_eq_true] at parts
  obtain ⟨n,hn,cover,normal,nh⟩ := BoundCoreProof.completed_query_constructs_a_real_native_witness
    (values frame images) q raw region ctx h parts.2 c present flag overlap
  obtain ⟨image,hi,sameFrame,sameValue⟩ :=
    every_native_witness_has_the_same_complete_application_frame frame images n hn
  refine ⟨image,hi,sameFrame,?_,?_,?_,?_⟩
  · simpa [sameValue] using normal
  · simpa [sameValue] using nh
  · have marks := (BoundCoreProof.coverage_keeps_the_same_base_and_full_mark n (BoundCore.bind ctx c) cover).2
    simpa [sameValue,BoundCore.bind] using marks
  · simpa [sameValue] using cover

theorem a_caller_side_real_cut_cannot_be_a_NORMAL_provider
    (budget : Nat) (provider candidate : Value) (cutHere : budget<provider.ap.path.length) :
    BoundCore.covers (cut budget provider) candidate=false := by
  simp [cut,cutHere,BoundCore.covers]

def point : Seed := ⟨⟨0,[1,2],.exact,some 1,[],[]⟩,false⟩
def output : Value := ⟨⟨1,[3],.must,some 1,[],[]⟩,false,false⟩
def frame : Frame := {actual:=point.ap}
def foreignFrame : Frame := {frame with method:=1}
def foreignImage : Image := ⟨foreignFrame,BoundCore.bind ⟨false,[]⟩ output⟩

theorem a_foreign_scalar_witness_cannot_authorize_current_delivery_selection :
    BoundCore.completeFor [foreignImage.value] point [output] output.ap ⟨false,[]⟩ false=true ∧
    complete frame [foreignImage] point [output] output.ap ⟨false,[]⟩ false=false := by decide +kernel

theorem stale_revisions_are_not_current_service :
    complete frame [⟨{frame with revision:=1},foreignImage.value⟩]
      point [output] output.ap ⟨false,[]⟩ false=false := by decide +kernel

theorem DEMAND_actuals_never_use_the_new_certificate
    (frame : Frame) (images : List Image) (q : Seed) (raw : List Value)
    (region : Ap) (ctx : BoundCore.Context) (h : Bool) :
    complete {frame with actualDemand:=true} images q raw region ctx h=false := by
  simp [complete]

theorem saved_replay_is_outside_current_delivery_selection
    (frame : Frame) (images : List Image) (q : Seed) (raw : List Value)
    (region : Ap) (ctx : BoundCore.Context) (h : Bool) :
    complete {frame with currentReply:=false} images q raw region ctx h=false := by
  simp [complete]

theorem backward_GROUP_and_run1_remain_outside_the_new_certificate
    (frame : Frame) (images : List Image) (q : Seed) (raw : List Value)
    (region : Ap) (ctx : BoundCore.Context) (h : Bool) :
    complete {frame with backward:=true} images q raw region ctx h=false ∧
    complete {frame with fullMode:=false} images q raw region ctx h=false ∧
    complete {frame with run:=1} images q raw region ctx h=false := by
  simp [complete]

end AuditScopedService
