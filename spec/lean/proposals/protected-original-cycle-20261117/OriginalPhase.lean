import OriginalReturn
namespace OriginalPhase
open NonEmptyPolicy NonEmptyRestriction OriginalReturn
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

theorem carry_emit_regular (run ref k : Nat) (b : Bool) (d : Ap) (a : Offered)
    (hr : run ≠ 2) (hs : ref ≠ 2) (ge : 2 ≤ run) (gf : 2 ≤ ref) :
    CarryPolicy.emit run k b d a = CarryPolicy.emit ref k b d a := by
  unfold CarryPolicy.emit
  rw [emit_regular run ref k b d a hr hs]
  simp [show ¬ run < 2 by omega, show ¬ ref < 2 by omega]

theorem head_emit_regular (run ref k : Nat) (b : Bool) (d : Ap) (a : Offered)
    (hr : run ≠ 2) (hs : ref ≠ 2) (ge : 2 ≤ run) (gf : 2 ≤ ref) :
    HeadPolicy.emit run k b d a = HeadPolicy.emit ref k b d a := by
  unfold HeadPolicy.emit
  rw [carry_emit_regular run ref k b d a hr hs ge gf]
  simp [show ¬ run < 2 by omega, show ¬ ref < 2 by omega]

theorem entryValues_regular (run ref k : Nat) (_hr : run ≠ 1) (_hs : ref ≠ 1) :
    entryValues run k=entryValues ref k := by rfl

theorem prepare_regular (run ref k : Nat) (b : Bool) (row : Row) (rows : List Row)
    (saved : List Saved) (a : Offered) (hr : run ≠ 2) (hs : ref ≠ 2) (ge : 2 ≤ run) (gf : 2 ≤ ref) :
    prepare run k b row rows saved a = prepare ref k b row rows saved a := by
  simp only [prepare]
  simp only [head_emit_regular run ref k _ _ _ hr hs ge gf]

theorem candidates_regular (run ref k : Nat) (b : Bool) (rows : List Row)
    (saved : List Saved) (as : List Offered)
    (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2) (ge : 2 ≤ run) (gf : 2 ≤ ref) :
    candidates run k b rows saved as = candidates ref k b rows saved as := by
  simp only [candidates,show (run == 1) = false by simp [hr],show (ref == 1) = false by simp [hs],Bool.false_eq_true,ite_false]
  simp only [prepare_regular run ref k _ _ _ _ _ hr2 hs2 ge gf]
  rfl

theorem suppress_regular (run ref : Nat) (complete : List Ap) (a : Offered) (e : Edge)
    (ge : 3 ≤ run) (gf : 3 ≤ ref) (parity : run % 2 = ref % 2) :
    suppress run complete a e=suppress ref complete a e := by
  simp [suppress,ge,gf,parity]

theorem certify_regular (run ref k : Nat) (rows : List Row) (saved : List Saved)
    (as : List Offered) (current : List Edge) (ge : 3 ≤ run) (gf : 3 ≤ ref)
    (parity : run % 2 = ref % 2) :
    certify run k rows saved as current=certify ref k rows saved as current := by
  simp only [certify,show ¬ run < 3 by omega,show ¬ ref < 3 by omega,parity]
  simp only [Bool.false_or,Bool.false_eq_true,ite_false,queries,
    prepare_regular run ref k _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]

theorem suppressMark_regular (run ref : Nat) (services : List (Ap × Nat)) (a : Offered) (e : Edge)
    (ge : 3 ≤ run) (gf : 3 ≤ ref) (parity : run % 2 = ref % 2) :
    suppressMark run services a e=suppressMark ref services a e := by
  unfold suppressMark
  split <;> simp only [suppress_regular run ref _ _ _ ge gf parity]

theorem certifyMarks_regular (run ref k : Nat) (rows : List Row) (saved : List Saved)
    (as : List Offered) (current : List Edge) (ge : 3 ≤ run) (gf : 3 ≤ ref)
    (parity : run % 2 = ref % 2) :
    certifyMarks run k rows saved as current=certifyMarks ref k rows saved as current := by
  simp only [certifyMarks,show ¬ run < 3 by omega,show ¬ ref < 3 by omega,parity]
  simp only [Bool.false_or,Bool.false_eq_true,ite_false,queries,
    prepare_regular run ref k _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]

theorem suppressReply_regular (run ref : Nat) (closed : List Ap) (service : List Edge)
    (native : List Value) (a : Offered) (e : Edge)
    (ge : 3 ≤ run) (gf : 3 ≤ ref) (parity : run % 2 = ref % 2) :
    suppressReply run closed service native a e=suppressReply ref closed service native a e := by
  simp only [suppressReply,suppress_regular run ref _ _ _ ge gf parity]

theorem suppressFlagged_regular (run ref : Nat) (closed : List Ap) (service : List Edge)
    (native : List Value) (a : Offered) (originalH : Bool) (e : Edge)
    (ge : 3≤run) (gf : 3≤ref) (parity : run%2=ref%2) :
    suppressFlaggedReply run closed service native a originalH e=
      suppressFlaggedReply ref closed service native a originalH e := by
  simp only [suppressFlaggedReply,suppress_regular run ref _ _ _ ge gf parity]

theorem certifyClosed_regular (run ref k : Nat) (rows : List Row) (saved : List Saved)
    (as : List Offered) (ge : 3 ≤ run) (gf : 3 ≤ ref) (parity : run % 2 = ref % 2) :
    certifyClosed run k rows saved as=certifyClosed ref k rows saved as := by
  simp only [certifyClosed,show ¬ run < 3 by omega,show ¬ ref < 3 by omega,parity]
  simp only [Bool.false_or,Bool.false_eq_true,ite_false,queries,
    prepare_regular run ref k _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]

theorem replies_regular (enabled : Bool) (run ref k : Nat) (rows : List Row)
    (saved : List Saved) (complete : List Ap) (services : List (Ap × Nat)) (closed : List Ap) (current : List Edge) (a : Offered) (originalH : Bool)
    (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2) (ge : 2 ≤ run) (gf : 2 ≤ ref)
    (parity : run % 2 = ref % 2) :
    actualReplies enabled run k rows saved complete services closed current a originalH = actualReplies enabled ref k rows saved complete services closed current a originalH := by
  simp only [actualReplies,parity,show (run == 1) = false by simp [hr],show (ref == 1) = false by simp [hs]]
  simp only [prepare_regular run ref k _ _ _ _ _ hr2 hs2 ge gf,
    suppress_regular run ref _ _ _ (by omega) (by omega) parity,
    suppressMark_regular run ref _ _ _ (by omega) (by omega) parity,
    suppressReply_regular run ref _ _ _ _ _ (by omega) (by omega) parity,
    suppressFlagged_regular run ref _ _ _ _ _ _ (by omega) (by omega) parity]

theorem round_regular (enabled : Bool) (run ref k : Nat) (rows : List Row)
    (saved : List Saved) (complete : List Ap) (services : List (Ap × Nat)) (d : Data)
    (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2) (ge : 2 ≤ run) (gf : 2 ≤ ref)
    (parity : run % 2 = ref % 2) :
    round enabled run k rows saved complete services d = round enabled ref k rows saved complete services d := by
  simp only [round,parity]
  simp only [replies_regular enabled run ref k _ _ _ _ _ _ _ _ hr hs hr2 hs2 ge gf parity,
    candidates_regular run ref k _ _ _ _ hr hs hr2 hs2 ge gf,
    certify_regular run ref k _ _ _ _ (by omega) (by omega) parity,
    certifyMarks_regular run ref k _ _ _ _ (by omega) (by omega) parity,
    certifyClosed_regular run ref k _ _ _ (by omega) (by omega) parity]

theorem initial_regular (run ref k : Nat) (hr : run ≠ 1) (hs : ref ≠ 1)
    (parity : run % 2 = ref % 2) : initialData run k = initialData ref k := by
  simp only [initialData,parity,entryValues_regular run ref k hr hs]

theorem analyze_regular (enabled : Bool) (fuel run ref k : Nat) (rows : List Row)
    (saved : List Saved) (complete : List Ap) (services : List (Ap × Nat)) (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2) (ge : 2 ≤ run) (gf : 2 ≤ ref)
    (parity : run % 2 = ref % 2) :
    analyze enabled fuel run k rows saved complete services = analyze enabled fuel ref k rows saved complete services := by
  simp only [analyze,initial_regular run ref k hr hs parity]
  simp only [round_regular enabled run ref k _ _ _ _ _ hr hs hr2 hs2 ge gf parity]

theorem entryBackValues_regular (run ref k : Nat) (d : Data) (_hr : run ≠ 1) (_hs : ref ≠ 1) :
    entryBackValues run k d=entryBackValues ref k d := by rfl

theorem target_regular (enabled : Bool) (run ref k : Nat) (old : State)
    (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2) (ge : 2 ≤ run) (gf : 2 ≤ ref)
    (parity : run % 2 = ref % 2) :
    anyTarget enabled run k old = anyTarget enabled ref k old := by
  simp only [anyTarget,initial_regular run ref k hr hs parity]
  have hf : round enabled run k old.rows old.saved old.complete old.services = round enabled ref k old.rows old.saved old.complete old.services := by
    funext d
    exact round_regular enabled run ref k _ _ _ _ d hr hs hr2 hs2 ge gf parity
  rw [hf]

theorem step_regular (enabled : Bool) (run ref k : Nat) (old : State)
    (hr : run ≠ 1) (hs : ref ≠ 1) (hr2 : run ≠ 2) (hs2 : ref ≠ 2) (ge : 2 ≤ run) (gf : 2 ≤ ref)
    (parity : run % 2 = ref % 2) :
    stepWithLimit enabled run k old = stepWithLimit enabled ref k old := by
  simp only [stepWithLimit,parity,analyze_regular enabled 8 run ref k _ _ _ _ hr hs hr2 hs2 ge gf parity,
    target_regular enabled run ref k old hr hs hr2 hs2 ge gf parity,producerHit,
    entryBackValues_regular run ref k _ hr hs]
end OriginalPhase
