/-
  ApSpec.FlowGroupIncrementalImpl — the implementation of rule P3 (spec/next-iteration-p3-p2m-implementation.md
  §3): the production form of the incremental `FlowGroup.addAll` (ap/Groups.kt).

  It extends `ApSpec.FlowGroupIncremental` (the rule) with four production facts:
    1. `insert` is total. It changes the list in place and its return value is not used. P3 returns
       early when the list after the insert has the same row objects as before (`sameRows`), not when
       `insert` returns null: `insert` can return null after it removed a row (Groups.kt:42).
    2. `addAll` returns a delta: each row of the new list minus the positions of the old rows with the
       same group key (`FlowAlgebra.minusNode`, exact position difference). The early return gives [].
    3. A call that throws (cancellation) restores the list that it read (`before`), so it has no
       effect on the store.
    4. The store starts empty, and every list that it holds between two calls is a fixpoint.

  Theorems.
    * `addAllImpl_eq`: on a stored fixpoint, the P3 list equals the native list.
    * `delta_self`: the delta of a list against itself is empty (the early return returns []).
    * `callImpl_eq`: on a stored fixpoint, the P3 call gives the native list and the native delta.
    * `callNative_fixpoint`: the list that a native call stores is a fixpoint (when its loop exits).
    * `empty_fixpoint`: the empty list is a fixpoint.
    * `runImpl_eq`: for every sequence of values from a fixpoint (for example the empty store), P3
      gives the native list and the native delta after every call.
    * `runAbort_eq`: with calls that throw, P3 gives the native run of the calls that complete.

  Constructive: no classical axioms beyond `propext` (simp).
-/
import ApSpec.FlowGroupIncremental

namespace ApSpec.FlowGroupImpl

open ApSpec.FlowGroupInc

set_option linter.unusedSectionVars false

variable {Pos H G : Type} [DecidableEq Pos] [DecidableEq H] [DecidableEq G]
variable (covAt : H → Pos → H → Pos → Bool) (dom : H → Pos → Pos → Bool)
variable (merge : List (Row Pos H) → Option (List (Row Pos H)))
variable (promote : List (Row Pos H) → Option (Row Pos H))
-- The production insert: the list after `insert` (Groups.kt:14-51). It is total.
variable (ins : List (Row Pos H) → Row Pos H → List (Row Pos H))
-- `FlowTree.groupKey`, a function of the header.
variable (gk : H → G)

/-- The total insert as the optional insert of the rule model. -/
def insOpt (L : List (Row Pos H)) (t : Row Pos H) : Option (List (Row Pos H)) := some (ins L t)

/-- Native `addAll` (Groups.kt:57-109): insert, loop, final pass. -/
def addAllNativeP (n : Nat) (S : List (Row Pos H)) (t : Row Pos H) : List (Row Pos H) :=
  pass covAt dom (loop covAt dom merge promote (insOpt ins) n (ins S t))

/-- P3 `addAll`: return when the list is unchanged; incremental passes with the old rows as the first
    clean rows; no final pass. -/
def addAllImpl (n : Nat) (S : List (Row Pos H)) (t : Row Pos H) : List (Row Pos H) :=
  if ins S t = S then S
  else loopInc covAt dom merge promote (insOpt ins) n (fun r => decide (r ∈ S)) (ins S t)

theorem addAllImpl_eq (n : Nat) (S : List (Row Pos H)) (t : Row Pos H)
    (hS : Fixpoint covAt dom merge promote S) :
    addAllImpl covAt dom merge promote ins n S t = addAllNativeP covAt dom merge promote ins n S t := by
  unfold addAllImpl addAllNativeP
  split
  · rename_i hsame
    rw [hsame, loop_fixpoint covAt dom merge promote (insOpt ins) n S hS]
    exact hS.1.symm
  · rw [final_pass_noop]
    have hcl : (fun r => decide (r ∈ S)) = (fun r => decide (r ∈ pass covAt dom S)) := by
      rw [hS.1]
    rw [hcl]
    exact loopInc_eq covAt dom merge promote (insOpt ins) n S (ins S t)

/-! ### The delta -/

/-- One row of the delta: the positions of `r` that no old row with the same group key has. -/
def deltaRow (before : List (Row Pos H)) (r : Row Pos H) : Option (Row Pos H) :=
  let ps := r.pos.filter (fun p =>
    !((before.filter (fun o => decide (gk o.hdr = gk r.hdr))).any (fun o => decide (p ∈ o.pos))))
  if ps.isEmpty then none else some ⟨r.id, r.hdr, ps⟩

/-- The delta that `addAll` returns (Groups.kt:100-108). -/
def delta (before L : List (Row Pos H)) : List (Row Pos H) := L.filterMap (deltaRow gk before)

theorem filterMap_none {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, f x = none) → l.filterMap f = []
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filterMap_cons, h x (List.mem_cons_self ..)]
    exact filterMap_none f xs (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem filter_nil_of {α : Type} (f : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, f x = false) → l.filter f = []
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filter_cons, h x (List.mem_cons_self ..)]
    exact filter_nil_of f xs (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- A row that is in `before` has an empty delta. -/
theorem deltaRow_mem (before : List (Row Pos H)) (r : Row Pos H) (hr : r ∈ before) :
    deltaRow gk before r = none := by
  unfold deltaRow
  have hf : r.pos.filter (fun p =>
      !((before.filter (fun o => decide (gk o.hdr = gk r.hdr))).any (fun o => decide (p ∈ o.pos)))) = [] := by
    apply filter_nil_of
    intro p hp
    have hin : r ∈ before.filter (fun o => decide (gk o.hdr = gk r.hdr)) :=
      List.mem_filter.mpr ⟨hr, decide_eq_true rfl⟩
    have hany : (before.filter (fun o => decide (gk o.hdr = gk r.hdr))).any (fun o => decide (p ∈ o.pos)) = true :=
      List.any_eq_true.mpr ⟨r, hin, decide_eq_true hp⟩
    rw [hany]
    rfl
  simp only []
  rw [hf]
  rfl

/-- The early return is exact: the delta of a list against itself is empty. -/
theorem delta_self (S : List (Row Pos H)) : delta gk S S = [] :=
  filterMap_none _ S (fun r hr => deltaRow_mem gk S r hr)

/-! ### One call and a sequence of calls -/

/-- A native call: the new stored list and the returned delta. -/
def callNative (n : Nat) (S : List (Row Pos H)) (t : Row Pos H) : List (Row Pos H) × List (Row Pos H) :=
  let F := addAllNativeP covAt dom merge promote ins n S t
  (F, delta gk S F)

/-- A P3 call. -/
def callImpl (n : Nat) (S : List (Row Pos H)) (t : Row Pos H) : List (Row Pos H) × List (Row Pos H) :=
  if ins S t = S then (S, [])
  else
    let F := loopInc covAt dom merge promote (insOpt ins) n (fun r => decide (r ∈ S)) (ins S t)
    (F, delta gk S F)

theorem callImpl_eq (n : Nat) (S : List (Row Pos H)) (t : Row Pos H)
    (hS : Fixpoint covAt dom merge promote S) :
    callImpl covAt dom merge promote ins gk n S t = callNative covAt dom merge promote ins gk n S t := by
  have hl := addAllImpl_eq covAt dom merge promote ins n S t hS
  unfold callImpl callNative
  unfold addAllImpl at hl
  split
  · rename_i hsame
    rw [if_pos hsame] at hl
    rw [← hl]
    show (S, []) = (S, delta gk S S)
    rw [delta_self]
  · rename_i hsame
    rw [if_neg hsame] at hl
    simp only
    rw [hl]

/-- The native call stores a fixpoint when its loop exits within the fuel. -/
theorem callNative_fixpoint (n : Nat) (S : List (Row Pos H)) (t : Row Pos H)
    (hx : exits covAt dom merge promote (insOpt ins) n (ins S t)) :
    Fixpoint covAt dom merge promote (callNative covAt dom merge promote ins gk n S t).1 := by
  have hF := exit_fixpoint covAt dom merge promote (insOpt ins) n (ins S t) hx
  unfold callNative addAllNativeP
  simp only
  rw [hF.1]
  exact hF

/-- The empty store is a fixpoint (production: `mergeMustOverlap` and the promotion scan find nothing in
    an empty list). -/
theorem empty_fixpoint (hm : merge [] = none) (hp : promote [] = none) :
    Fixpoint covAt dom merge promote ([] : List (Row Pos H)) :=
  ⟨rfl, hm, hp⟩

/-- Every call of the native run from `S` exits within the fuel. -/
def AllExit (n : Nat) : List (Row Pos H) → List (Row Pos H) → Prop
  | [], _ => True
  | t :: ts, S => exits covAt dom merge promote (insOpt ins) n (ins S t) ∧
      AllExit n ts (callNative covAt dom merge promote ins gk n S t).1

/-- The results (stored list, delta) of a sequence of native calls. -/
def runNative (n : Nat) : List (Row Pos H) → List (Row Pos H) → List (List (Row Pos H) × List (Row Pos H))
  | [], _ => []
  | t :: ts, S => callNative covAt dom merge promote ins gk n S t ::
      runNative n ts (callNative covAt dom merge promote ins gk n S t).1

def runImpl (n : Nat) : List (Row Pos H) → List (Row Pos H) → List (List (Row Pos H) × List (Row Pos H))
  | [], _ => []
  | t :: ts, S => callImpl covAt dom merge promote ins gk n S t ::
      runImpl n ts (callImpl covAt dom merge promote ins gk n S t).1

/-- P3 is exact on a whole store: from a fixpoint (the empty store), every call gives the native list
    and the native delta. -/
theorem runImpl_eq (n : Nat) (ts : List (Row Pos H)) (S : List (Row Pos H))
    (hS : Fixpoint covAt dom merge promote S)
    (hx : AllExit covAt dom merge promote ins gk n ts S) :
    runImpl covAt dom merge promote ins gk n ts S = runNative covAt dom merge promote ins gk n ts S := by
  induction ts generalizing S with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨hx1, hxs⟩ := hx
    have hc := callImpl_eq covAt dom merge promote ins gk n S t hS
    simp only [runImpl, runNative]
    rw [hc, ih _ (callNative_fixpoint covAt dom merge promote ins gk n S t hx1) hxs]

/-! ### Calls that throw

A call that throws (a cancellation checkpoint) restores the list that it read and returns no delta.
`none` is such a call. -/

def runAbortImpl (n : Nat) : List (Option (Row Pos H)) → List (Row Pos H) →
    List (List (Row Pos H) × List (Row Pos H))
  | [], _ => []
  | none :: ts, S => runAbortImpl n ts S
  | some t :: ts, S => callImpl covAt dom merge promote ins gk n S t ::
      runAbortImpl n ts (callImpl covAt dom merge promote ins gk n S t).1

/-- The calls that complete. -/
def completed : List (Option (Row Pos H)) → List (Row Pos H)
  | [] => []
  | none :: ts => completed ts
  | some t :: ts => t :: completed ts

/-- A call that throws has no effect: P3 gives the native run of the completed calls. -/
theorem runAbort_eq (n : Nat) (ts : List (Option (Row Pos H))) (S : List (Row Pos H))
    (hS : Fixpoint covAt dom merge promote S)
    (hx : AllExit covAt dom merge promote ins gk n (completed ts) S) :
    runAbortImpl covAt dom merge promote ins gk n ts S =
      runNative covAt dom merge promote ins gk n (completed ts) S := by
  induction ts generalizing S with
  | nil => rfl
  | cons o ts ih =>
    cases o with
    | none => exact ih S hS hx
    | some t =>
      obtain ⟨hx1, hxs⟩ := hx
      have hc := callImpl_eq covAt dom merge promote ins gk n S t hS
      simp only [runAbortImpl, completed, runNative]
      rw [hc, ih _ (callNative_fixpoint covAt dom merge promote ins gk n S t hx1) hxs]

end ApSpec.FlowGroupImpl
