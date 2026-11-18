import Excluded
namespace ExcludedPhase
open NonEmptyPolicy NonEmptyRestriction ExcludedGuardCycle
set_option maxRecDepth 65536
set_option maxHeartbeats 160000000
set_option linter.unusedSimpArgs false
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

theorem emit_regular (run ref k : Nat) (b : Bool) (d : Ap) (a : Offered)
    (hr : run ≠ 2) (hs : ref ≠ 2) : emit run k b d a = emit ref k b d a := by
  simp [emit,emitBase,completeFamily,primary,hr,hs]

theorem keep_regular (run ref : Nat) (head : Path) (field : Nat) (a : Value)
    (hr : run ≠ 1) (hs : ref ≠ 1) :
    NestedWriteReplay.keep run head field a = NestedWriteReplay.keep ref head field a := by
  simp [NestedWriteReplay.keep,hr,hs,show (run == 1) = false by simp [hr],show (ref == 1) = false by simp [hs]]

theorem afterWrite_regular (run ref k : Nat) (hr : run ≠ 1) (hs : ref ≠ 1) :
    afterWrite run k = afterWrite ref k := by
  simp only [afterWrite,PointWriteReplay.nestedWrite,PointWriteReplay.keep]
  simp only [keep_regular run ref _ _ _ hr hs]

theorem prepare_regular (run ref k : Nat) (b : Bool) (row : Row) (rows : List Row)
    (saved : List Saved) (a : Offered) (hr : run ≠ 2) (hs : ref ≠ 2) :
    prepare run k b row rows saved a = prepare ref k b row rows saved a := by
  simp only [prepare]
  simp only [emit_regular run ref k _ _ _ hr hs]

theorem candidates_regular (run ref k : Nat) (b : Bool) (rows : List Row)
    (saved : List Saved) (as : List Offered)
    (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2) :
    candidates run k b rows saved as = candidates ref k b rows saved as := by
  simp only [candidates,show (run == 1) = false by simp [hr],show (ref == 1) = false by simp [hs],Bool.false_eq_true,ite_false]
  simp only [prepare_regular run ref k _ _ _ _ _ hr2 hs2]
  rfl

theorem replies_regular (enabled : Bool) (run ref k : Nat) (rows : List Row)
    (saved : List Saved) (current : List Edge) (a : Offered)
    (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2)
    (parity : run % 2 = ref % 2) :
    actualReplies enabled run k rows saved current a = actualReplies enabled ref k rows saved current a := by
  simp only [actualReplies,parity,show (run == 1) = false by simp [hr],show (ref == 1) = false by simp [hs]]
  simp only [prepare_regular run ref k _ _ _ _ _ hr2 hs2]

theorem round_regular (enabled : Bool) (run ref k : Nat) (rows : List Row)
    (saved : List Saved) (d : Data)
    (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2)
    (parity : run % 2 = ref % 2) :
    round enabled run k rows saved d = round enabled ref k rows saved d := by
  simp only [round,parity]
  simp only [replies_regular enabled run ref k _ _ _ _ hr hs hr2 hs2 parity,
    candidates_regular run ref k _ _ _ _ hr hs hr2 hs2]

theorem initial_regular (run ref k : Nat) (hr : run ≠ 1) (hs : ref ≠ 1)
    (parity : run % 2 = ref % 2) : initialData run k = initialData ref k := by
  simp only [initialData,parity,afterWrite_regular run ref k hr hs]

theorem analyze_regular (enabled : Bool) (fuel run ref k : Nat) (rows : List Row)
    (saved : List Saved) (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2)
    (parity : run % 2 = ref % 2) :
    analyze enabled fuel run k rows saved = analyze enabled fuel ref k rows saved := by
  simp only [analyze,initial_regular run ref k hr hs parity]
  simp only [round_regular enabled run ref k _ _ _ hr hs hr2 hs2 parity]

theorem beforeWrite_regular (run ref k : Nat) (d : Data) (hr : run ≠ 1) (hs : ref ≠ 1) :
    beforeWrite run k d = beforeWrite ref k d := by
  simp only [beforeWrite,PointWriteReplay.nestedWrite,PointWriteReplay.keep]
  simp only [keep_regular run ref _ _ _ hr hs]

theorem target_regular (enabled : Bool) (run ref k : Nat) (old : State)
    (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2)
    (parity : run % 2 = ref % 2) :
    anyTarget enabled run k old = anyTarget enabled ref k old := by
  simp only [anyTarget,initial_regular run ref k hr hs parity]
  have hf : round enabled run k old.rows old.saved = round enabled ref k old.rows old.saved := by
    funext d
    exact round_regular enabled run ref k _ _ d hr hs hr2 hs2 parity
  rw [hf]

theorem step_regular (enabled : Bool) (run ref k : Nat) (old : State)
    (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2)
    (parity : run % 2 = ref % 2) :
    stepWithLimit enabled run k old = stepWithLimit enabled ref k old := by
  simp only [stepWithLimit,parity,analyze_regular enabled 8 run ref k _ _ hr hs hr2 hs2 parity,
    target_regular enabled run ref k old hr hs hr2 hs2 parity,producerHit,
    beforeWrite_regular run ref k _ hr hs]
end ExcludedPhase
