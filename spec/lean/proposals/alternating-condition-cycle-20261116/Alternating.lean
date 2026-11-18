import PriorReplay

/- A generative source family on a fresh result, not a pass:
   CM(p.f.g.M,T) -> GEN(r.MUST,U); CM(p.M,T) -> GEN(r.f.MUST,U),
   and the symmetric U-to-T actions. Three calls to the same acyclic owner.
   The proof core uses real C2, raw C5 and actual current STAR applications.
   Normal/extra deliveries remain explicit, and cannot erase root MAY/D. -/
namespace AlternatingCondition
open NonEmptyPolicy NonEmptyRestriction
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
-- Lean 4.35's generic Ord-to-ReflBEq instance carries classical choice.
-- Use the constructive decidable-equality proof of the same Nat equality.
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl

local instance : BEq Row where beq a b := decide (a = b)
local instance : LawfulBEq Row where
  rfl := by intro a; simp
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

inductive Color where | t | u
  deriving DecidableEq, BEq, Repr
def Color.flip : Color → Color | .t => .u | .u => .t
def Color.id : Color → Nat | .t => 1 | .u => 2
def p : Nat := 0
def ret : Nat := 1
def f : Nat := 1
def g : Nat := 2
def fact (base : Nat) (path : Path) (tail : Tail) (m : Color) : Ap :=
  ⟨base,path,tail,some m.id,[],[]⟩
def value (base : Nat) (path : Path) (tail : Tail) (m : Color) (d : Bool := true) : Value :=
  ⟨fact base path tail m,d,false⟩
def rootMayAt (b : Nat) (m : Color) : Value := value b [] .may m
def rootMay (m : Color) : Value := rootMayAt p m
def source : Offered := ⟨fact p [f] .must .t,false⟩
def unknown (m : Color) : Offered := ⟨fact p [] .may m,true⟩
def backwardUnknown (m : Color) : Offered := ⟨fact ret [] .may m,true⟩
def star (base : Nat) (path : Path) (m : Color) : Seed := ⟨fact base path .star m,true⟩
def forwardRow (m : Color) : Row := ⟨fact p [] .may m,fact ret [] .star m.flip⟩
def backwardRow (m : Color) : Row := ⟨fact ret [] .may m.flip,fact p [] .star m⟩
abbrev Edge := Ap × Value
local instance : BEq Edge where beq a b := decide (a = b)
local instance : LawfulBEq Edge where
  rfl := by intro a; simp
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
def forwardEdge (path : Path) (m : Color) : Edge :=
  (fact p path .star m,value ret [] .may m.flip)
def backwardEdge (m : Color) : Edge :=
  (fact ret [] .star m.flip,value p [] .may m)

/-- Direct native source-transfer cases. The two actions generate fresh
    uniform marks at r or r.f; they copy no input suffix or object. -/
def generate (m : Color) (q : Seed) : List Value :=
  if q.ap.base != p || q.ap.mark != some m.id then [] else
  let root := if (dropHead [f,g] q.ap.path).isSome then
      [value ret [] .must m.flip q.demand]
    else if (dropHead q.ap.path [f,g]).isSome && q.ap.tail != .exact then
      [value ret [] (if q.ap.tail == .must then .must else .may) m.flip
        (q.demand || q.ap.tail != .must)]
    else []
  root ++ [value ret [f] .must m.flip q.demand]

def reverseGenerate (k : Nat) (m : Color) (q : Seed) : List Value :=
  if q.ap.base != ret || q.ap.mark != some m.flip.id then [] else
  [cut k (value p [f,g] .may m)] ++
    (if (dropHead [f] q.ap.path).isSome ||
        ((dropHead q.ap.path [f]).isSome && q.ap.tail != .exact)
     then [value p [] .may m] else [])

def forwardCandidates (run k : Nat) (m : Color) (a : Offered) : List Edge :=
  (emit run k false (forwardRow m).entry a).flatMap fun q =>
    (generate m q).filterMap fun c =>
      restrictOne run k false [a] q.ap (cut k c) (forwardRow m)

def backwardCandidates (run k : Nat) (m : Color) : List Edge :=
  let actual : Offered := ⟨fact ret [] .may m.flip,true⟩
  (emit run k true (backwardRow m).entry actual).flatMap fun q =>
    (reverseGenerate k m q).filterMap fun c =>
      restrictOne run k true [actual] q.ap c (backwardRow m)

def unique [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then unique xs else x :: unique xs
theorem unique_membership [DecidableEq α] (x : α) (xs : List α) :
    x ∈ unique xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [unique]
  | cons a rest ih =>
      unfold unique
      split
      · rename_i duplicate
        simp only [ih,List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (same | inside)
          · simpa [same] using duplicate
          · exact inside
      · simp only [List.mem_cons,ih]

/-- E/mx are empty in this source family. This canonical form keeps EXACT
    beside MUST, removes proper same-layer MAY/MUST covered facts and
    deduplicates exact memberships. It never merges the support layers. -/
def properCover (a b : Value) : Bool :=
  a.ap.base == b.ap.base && a.ap.mark == b.ap.mark && a.demand == b.demand && a.h == b.h &&
    match dropHead a.ap.path b.ap.path with
    | none => false
    | some [] => a.ap.tail == .may && b.ap.tail != .may
    | some (_ :: _) => a.ap.tail == .may || (a.ap.tail == .must && b.ap.tail == .must)
def packet (xs : List Value) : List Value :=
  DefiniteReplySupport.foldValues (unique (xs.filter (fun x => !(xs.any (fun a => properCover a x)))))

theorem root_may_is_never_properly_covered (a : Value) (b : Nat) (m : Color) :
    properCover a (rootMayAt b m) = false := by
  cases h : a.ap.path with
  | nil => simp [properCover,rootMayAt,value,fact,h,dropHead]
  | cons x rest => simp [properCover,rootMayAt,value,fact,h,dropHead]

theorem any_extra_ready_replies_keep_the_may_witness (b : Nat) (m : Color) (xs : List Value)
    (present : rootMayAt b m ∈ xs) : rootMayAt b m ∈ packet xs := by
  have inCanonical : rootMayAt b m ∈ unique (xs.filter (fun x => !(xs.any (fun a => properCover a x)))) := by
    apply (unique_membership _ _).mpr
    apply List.mem_filter.mpr
    exact ⟨present,by simp [root_may_is_never_properly_covered]⟩
  apply List.mem_map.mpr
  refine ⟨ExactSupportCycle.wrap (rootMayAt b m),?_,rfl⟩
  apply ReplySupportKernel.unsupported_members_retained DefiniteReplySupport.eligible
  · exact List.mem_map.mpr ⟨rootMayAt b m,inCanonical,rfl⟩
  · cases m <;> rfl

theorem colors_really_change (m : Color) : m.id ≠ m.flip.id := by cases m <;> decide

theorem source_first_field_star_is_admitted (run k : Nat) (positive : 1 ≤ k) :
    star p [f] .t ∈ emit run k false (forwardRow .t).entry source := by
  simp [emit,emitBase,forwardRow,source,star,fact,p,ret,f,Color.id,
    selector,marksOK,completeFamily,primary,dropHead,admits,seed,probe,legalSeed,positive] <;> exact Nat.ne_of_gt positive

theorem unknown_star_is_admitted (run k : Nat) (back : Bool) (m : Color) (positive : 1 ≤ k) :
    star (if back then ret else p) [] (if back then m.flip else m) ∈
      emit run k back (if back then (backwardRow m).entry else (forwardRow m).entry)
        ⟨fact (if back then ret else p) [] .may (if back then m.flip else m),true⟩ := by
  cases back <;> cases m <;>
    simp [emit,emitBase,forwardRow,backwardRow,star,fact,Color.id,Color.flip,
      selector,marksOK,completeFamily,primary,dropHead,atHead,seed,probe,legalSeed,positive] <;> exact Nat.ne_of_gt positive


theorem root_forward_step (run k : Nat) (m : Color) (positive : 1 ≤ k) :
    forwardEdge [] m ∈ forwardCandidates run k m (unknown m) := by
  have nz : k ≠ 0 := Nat.ne_of_gt positive
  cases m <;> simp [forwardCandidates,emit,emitBase,generate,forwardRow,unknown,
    forwardEdge,value,fact,p,ret,f,g,Color.id,Color.flip,selector,marksOK,
    completeFamily,primary,dropHead,atHead,seed,probe,legalSeed,nz,positive,
    cut,restrictOne,rawImage,normalize,intersectExit,marksMeet]

theorem source_forward_step (run k : Nat) (positive : 1 ≤ k) :
    forwardEdge [f] .t ∈ forwardCandidates run k .t source := by
  have nz : k ≠ 0 := Nat.ne_of_gt positive
  simp [forwardCandidates,emit,emitBase,generate,forwardRow,source,
    forwardEdge,value,fact,p,ret,f,g,Color.id,Color.flip,selector,marksOK,
    completeFamily,primary,dropHead,atHead,seed,probe,legalSeed,nz,positive,
    cut,restrictOne,rawImage,normalize,intersectExit,marksMeet,admits]

theorem root_backward_step (run k : Nat) (m : Color) (positive : 1 ≤ k) :
    backwardEdge m ∈ backwardCandidates run k m := by
  have nz : k ≠ 0 := Nat.ne_of_gt positive
  cases m <;> simp [backwardCandidates,emit,emitBase,reverseGenerate,backwardRow,
    backwardEdge,value,fact,p,ret,f,g,Color.id,Color.flip,selector,marksOK,
    completeFamily,primary,dropHead,atHead,seed,probe,legalSeed,nz,positive,
    cut,restrictOne,rawImage,normalize,intersectExit,marksMeet,admits]



/-- Complete rows may have more qualified heads. Base starts are not
    cancelled when a fresh bounded child is prepared. Concrete GEN is
    outside the delegated correlated-FLOW transfer class. -/
def prepared (run k : Nat) (back : Bool) (d : Ap) (a : Offered)
    (extraChildren : List Seed) : List Seed := unique (emit run k back d a ++ extraChildren)
theorem children_do_not_cancel_an_admitted_base_start (run k : Nat) (back : Bool)
    (d : Ap) (a : Offered) (extra : List Seed) (q : Seed)
    (admitted : q ∈ emit run k back d a) : q ∈ prepared run k back d a extra := by
  exact (unique_membership _ _).mpr (List.mem_append_left _ admitted)

/-- Native STAR application used below. The owned input is not MUST;
    strict saved-MUST filtering does not alter these current applications.
    No suffix is copied by a mark-changing generated output. -/
def applyCurrent (edge : Edge) (actual : Offered) : Option Value :=
  if edge.1.base == actual.ap.base && edge.1.mark == actual.ap.mark &&
      edge.1.tail == .star && (dropHead edge.1.path actual.ap.path).isSome then
    some { edge.2 with
      ap := {edge.2.ap with base := p}
      demand := edge.2.demand || actual.demand }
  else none

theorem current_source_call_keeps_the_intrinsic_may :
    applyCurrent (forwardEdge [f] .t) source = some (rootMay .u) := by decide

/-- Run-1 uses the root STAR relation, not the finer restricted Ff.
    The U offer needed by the second generator is produced by call one;
    the T offer used by call three is produced by call two. -/
theorem cold_bootstrap_actual_offers_are_derived :
    applyCurrent (forwardEdge [] .t) source = some (rootMay .u) ∧
    applyCurrent (forwardEdge [] .u) (unknown .u) = some (rootMay .t) ∧
    applyCurrent (forwardEdge [] .t) (unknown .t) = some (rootMay .u) := by decide

theorem current_unknown_call_changes_the_mark (m : Color) :
    applyCurrent (forwardEdge [] m) (unknown m) = some (rootMay m.flip) := by
  cases m <;> decide

theorem current_reverse_call_changes_the_mark (m : Color) :
    applyCurrent (backwardEdge m) (backwardUnknown m.flip) = some (rootMay m) := by
  cases m <;> decide

def canonicalEdges (xs : List Edge) : List Edge := unique (xs.filter fun e =>
  !(xs.any (fun a => a.1 == e.1 && properCover a.2 e.2)))

theorem root_may_edge_survives_all_extra_summaries (P : Ap) (b : Nat) (m : Color)
    (xs : List Edge) (present : (P,rootMayAt b m) ∈ xs) :
    (P,rootMayAt b m) ∈ canonicalEdges xs := by
  apply (unique_membership _ _).mpr
  apply List.mem_filter.mpr
  exact ⟨present,by simp [root_may_is_never_properly_covered]⟩

def rowsFrom (edges : List Edge) : List Row := unique (edges.filterMap fun e =>
  if e.2.demand then some ⟨e.2.ap,e.1⟩ else none)

theorem forward_projection_is_the_paired_backward_row (m : Color) :
    backwardRow m ∈ rowsFrom [forwardEdge [] m] := by
  apply (unique_membership _ _).mpr
  cases m <;> simp [forwardEdge,backwardRow,rowsFrom,value,fact,Color.flip,Color.id]

theorem backward_projection_is_the_paired_forward_row (m : Color) :
    forwardRow m ∈ rowsFrom [backwardEdge m] := by
  apply (unique_membership _ _).mpr
  cases m <;> simp [backwardEdge,forwardRow,rowsFrom,value,fact,Color.flip,Color.id]

theorem project_present_forward_row (m : Color) (xs : List Edge)
    (present : forwardEdge [] m ∈ xs) : backwardRow m ∈ rowsFrom xs := by
  apply (unique_membership _ _).mpr
  exact List.mem_filterMap.mpr ⟨forwardEdge [] m,present,by cases m <;> rfl⟩

theorem project_present_backward_row (m : Color) (xs : List Edge)
    (present : backwardEdge m ∈ xs) : forwardRow m ∈ rowsFrom xs := by
  apply (unique_membership _ _).mpr
  exact List.mem_filterMap.mpr ⟨backwardEdge m,present,by cases m <;> rfl⟩

/-- Adversarial ready extras include every result of saved replay, every
    prepared child and every other current query. They can add even a
    NORMAL MUST at the root. The mandatory MAY/D fact still survives. -/
def deliver (edge : Edge) (actual : Offered) (readyExtras : List Value) : List Value :=
  packet ((applyCurrent edge actual).toList ++ readyExtras)

theorem source_delivery_with_arbitrary_extras (extra : List Value) :
    rootMay .u ∈ deliver (forwardEdge [f] .t) source extra := by
  unfold deliver
  rw [current_source_call_keeps_the_intrinsic_may]
  exact any_extra_ready_replies_keep_the_may_witness _ _ _ (by simp [rootMay])

theorem forward_delivery_with_arbitrary_extras (m : Color) (extra : List Value) :
    rootMay m.flip ∈ deliver (forwardEdge [] m) (unknown m) extra := by
  unfold deliver
  rw [current_unknown_call_changes_the_mark]
  exact any_extra_ready_replies_keep_the_may_witness _ _ _ (by simp [rootMay])

theorem backward_delivery_with_arbitrary_extras (m : Color) (extra : List Value) :
    rootMay m ∈ deliver (backwardEdge m) (backwardUnknown m.flip) extra := by
  unfold deliver
  rw [current_reverse_call_changes_the_mark]
  exact any_extra_ready_replies_keep_the_may_witness _ _ _ (by simp [rootMay])

/-- Zero is the original premise throughout root. No data-mark restoration
    cycle is attached to root's normal observation. -/
def terminal (v : Value) : TargetZeroKernel.Summary :=
  TargetZeroKernel.forwardSinkTarget 0 .zero (if v.demand then .demand else .normal) 0

def targetDemand : TargetZeroKernel.Demand := TargetZeroKernel.handoffTarget 0 .zero

def sourceHit : Option TargetZeroKernel.Summary :=
  TargetZeroKernel.backwardGenEventTarget .actualReverseTransfer
    ⟨.zero,.ap .a⟩
    (admits (rootMay .t).ap.tail (rootMay .t).ap.e [f] &&
      (rootMay .t).ap.mark == source.ap.mark) true 0 .zero

theorem the_three_forward_calls_reach_a_demand_observation :
    applyCurrent (forwardEdge [f] .t) source = some (rootMay .u) ∧
    applyCurrent (forwardEdge [] .u) (unknown .u) = some (rootMay .t) ∧
    applyCurrent (forwardEdge [] .t) (unknown .t) = some (rootMay .u) ∧
    TargetZeroKernel.continuationRelevant (terminal (rootMay .u)) = true := by decide

theorem the_three_backward_calls_reach_the_actual_producer :
    applyCurrent (backwardEdge .t) (backwardUnknown .u) = some (rootMay .t) ∧
    applyCurrent (backwardEdge .u) (backwardUnknown .t) = some (rootMay .u) ∧
    sourceHit = some (TargetZeroKernel.targetSummary 0 .zero) := by decide

theorem root_control_passes_real_paired_c5_and_restarts_zero :
    TargetZeroKernel.c5Restrict TargetZeroKernel.exactEntry TargetZeroKernel.exactExit
      targetDemand (terminal (rootMay .u)) = some (terminal (rootMay .u)) ∧
    TargetZeroKernel.selectedTargetHandoff (terminal (rootMay .u)) = some targetDemand ∧
    TargetZeroKernel.emittedZero .restricted [targetDemand] 0 .zero = [.zero] ∧
    sourceHit.bind (TargetZeroKernel.c5Restrict TargetZeroKernel.exactEntry
      TargetZeroKernel.exactExit targetDemand) = sourceHit := by decide



/-- Generate witnesses with the actual C2/C5 functions. The additional
    rows/starts/replies are deliberately not a hypothesis of recurrence:
    membership lemmas above make this a lower-bound simulation closed
    under all those additions, not a full-state equality claim. -/
def forwardRaw (run k : Nat) (rows : List Row) : List Edge :=
  (if forwardRow .t ∈ rows then
    forwardCandidates run k .t source ++ forwardCandidates run k .t (unknown .t)
   else []) ++
  (if forwardRow .u ∈ rows then forwardCandidates run k .u (unknown .u) else [])
def backwardRaw (run k : Nat) (rows : List Row) : List Edge :=
  (if backwardRow .t ∈ rows then backwardCandidates run k .t else []) ++
  (if backwardRow .u ∈ rows then backwardCandidates run k .u else [])
def bootstrapRaw (k : Nat) : List Edge :=
  ([Color.t,Color.u].flatMap fun m =>
    (generate m (star p [] m)).map fun c => ((star p [] m).ap,cut k c))

def forwardInputs (rows : List Row) : Prop :=
  forwardRow .t ∈ rows ∧ forwardRow .u ∈ rows
def backwardInputs (rows : List Row) : Prop :=
  backwardRow .t ∈ rows ∧ backwardRow .u ∈ rows

theorem complete_forward_round_keeps_both_shared_owner_relations
    (run k : Nat) (rows : List Row) (positive : 1 ≤ k) (inputs : forwardInputs rows)
    (extraSummaries : List Edge) :
    backwardInputs (rowsFrom (canonicalEdges (forwardRaw run k rows ++ extraSummaries))) := by
  have hT := root_forward_step run k .t positive
  have hU := root_forward_step run k .u positive
  constructor
  · apply project_present_forward_row
    apply root_may_edge_survives_all_extra_summaries
    exact List.mem_append_left _ (by
      simp only [forwardRaw,inputs.1,inputs.2,ite_true,List.mem_append]
      exact Or.inl (Or.inr hT))
  · apply project_present_forward_row
    apply root_may_edge_survives_all_extra_summaries
    exact List.mem_append_left _ (by
      simp only [forwardRaw,inputs.1,inputs.2,ite_true,List.mem_append]
      exact Or.inr hU)

theorem complete_backward_round_keeps_both_shared_owner_relations
    (run k : Nat) (rows : List Row) (positive : 1 ≤ k) (inputs : backwardInputs rows)
    (extraSummaries : List Edge) :
    forwardInputs (rowsFrom (canonicalEdges (backwardRaw run k rows ++ extraSummaries))) := by
  have hT := root_backward_step run k .t positive
  have hU := root_backward_step run k .u positive
  constructor
  · apply project_present_backward_row
    apply root_may_edge_survives_all_extra_summaries
    exact List.mem_append_left _ (by
      simp only [backwardRaw,inputs.1,inputs.2,ite_true,List.mem_append]
      exact Or.inl hT)
  · apply project_present_backward_row
    apply root_may_edge_survives_all_extra_summaries
    exact List.mem_append_left _ (by
      simp only [backwardRaw,inputs.1,inputs.2,ite_true,List.mem_append]
      exact Or.inr hU)

theorem cold_bootstrap_generates_both_forward_witnesses :
    forwardEdge [] .t ∈ bootstrapRaw 1 ∧ forwardEdge [] .u ∈ bootstrapRaw 1 := by
  decide

theorem cold_bootstrap_supplies_the_first_handoff (extraSummaries : List Edge) :
    backwardInputs (rowsFrom (canonicalEdges (bootstrapRaw 1 ++ extraSummaries))) := by
  constructor
  · apply project_present_forward_row
    apply root_may_edge_survives_all_extra_summaries
    exact List.mem_append_left _ cold_bootstrap_generates_both_forward_witnesses.1
  · apply project_present_forward_row
    apply root_may_edge_survives_all_extra_summaries
    exact List.mem_append_left _ cold_bootstrap_generates_both_forward_witnesses.2

/-- E, H and marks are literal. No correlated FLOW provider or diagonal
    taint support can cover either mark-changing root-MAY witness. -/
theorem witnesses_are_cross_mark_and_plain (m : Color) :
    (forwardEdge [] m).1.mark ≠ (forwardEdge [] m).2.ap.mark ∧
    (backwardEdge m).1.mark ≠ (backwardEdge m).2.ap.mark ∧
    (forwardEdge [] m).2.h = false ∧ (backwardEdge m).2.h = false := by
  cases m <;> decide

theorem current_star_not_saved_must (m : Color) :
    (forwardEdge [] m).1.tail = .star ∧ (backwardEdge m).1.tail = .star ∧
    (forwardEdge [] m).2.ap.tail = .may ∧ (backwardEdge m).2.ap.tail = .may := by
  cases m <;> decide

theorem all_generator_outputs_change_the_original_mark (m : Color) (q : Seed)
    (v : Value) (present : v ∈ generate m q) :
    q.ap.mark = some m.id ∧ v.ap.mark = some m.flip.id ∧ v.h = false := by
  unfold generate at present
  split at present
  · simp at present
  · rename_i yes
    have mark : q.ap.mark = some m.id := by
      by_cases h : q.ap.mark = some m.id
      · exact h
      · have bad : (q.ap.base != p || q.ap.mark != some m.id) = true := by simp [h]
        exact False.elim (yes bad)
    simp only [List.mem_append] at present
    rcases present with h | h
    · split at h
      · simp [value,fact] at h
        subst v; exact ⟨mark,rfl,rfl⟩
      · split at h
        · simp [value,fact] at h
          subst v; exact ⟨mark,rfl,rfl⟩
        · simp at h
    · simp at h
      subst v; exact ⟨mark,rfl,rfl⟩

/-- No normal whole-root marked conclusion can be learned from the
    critical root STAR query: the root action remains MAY/D and the other
    action writes r.f, not r. Both fields fit once k>=2; the intrinsic
    whole-root MAY still has FL=0 at every k. -/
theorem exact_root_star_transfer (m : Color) :
    generate m (star p [] m) =
      [value ret [] .may m.flip, value ret [f] .must m.flip] := by
  cases m <;> decide

theorem source_field_star_transfer :
    generate .t (star p [f] .t) = [value ret [] .may .u,value ret [f] .must .u] := by
  decide

/-- This is a witness-projected execution of the acyclic root. All actual
    calls can be scheduled by the preceding delivery lemmas: source->U,
    U->T, T->U forward; U->T, T->U, U->T backward. No actual or owned
    query has a MAY/NE premise. The row history includes arbitrary extra
    admitted summaries at EVERY run. -/
def limit (run : Nat) : Nat := max 1 (run-1)
def history (extras : Nat → List Edge) : Nat → List Row
  | 0 => []
  | 1 => rowsFrom (canonicalEdges (bootstrapRaw 1 ++ extras 1))
  | n+2 =>
      let prior := history extras (n+1)
      let raw := if (n+2) % 2 == 0 then backwardRaw (n+2) (limit (n+2)) prior
                 else forwardRaw (n+2) (limit (n+2)) prior
      rowsFrom (canonicalEdges (raw ++ extras (n+2)))

def pairedInvariant (run : Nat) (rows : List Row) : Prop :=
  if run % 2 == 1 then backwardInputs rows else forwardInputs rows

theorem uncapped_alternating_demand_invariant (extras : Nat → List Edge) (n : Nat) :
    pairedInvariant (n+1) (history extras (n+1)) := by
  induction n with
  | zero => exact cold_bootstrap_supplies_the_first_handoff (extras 1)
  | succ n ih =>
      have positive : 1 ≤ limit (n+2) := Nat.le_max_left _ _
      change pairedInvariant (n+2)
        (rowsFrom (canonicalEdges ((if (n+2) % 2 == 0 then
          backwardRaw (n+2) (limit (n+2)) (history extras (n+1))
          else forwardRaw (n+2) (limit (n+2)) (history extras (n+1))) ++ extras (n+2))))
      have residues : (n+1)%2 = 0 ∨ (n+1)%2 = 1 := Nat.mod_two_eq_zero_or_one _
      rcases residues with even | odd
      · have next : (n+2)%2 = 1 := by
          change (n+1+1)%2 = 1
          rw [Nat.add_mod,even]
        have inputs : forwardInputs (history extras (n+1)) := by simpa [pairedInvariant,even] using ih
        simp only [pairedInvariant,next,Nat.one_ne_zero,ite_false,ite_true]
        exact complete_forward_round_keeps_both_shared_owner_relations (n+2) _ _ positive inputs _
      · have next : (n+2)%2 = 0 := by
          change (n+1+1)%2 = 0
          rw [Nat.add_mod,odd]
        have inputs : backwardInputs (history extras (n+1)) := by simpa [pairedInvariant,odd] using ih
        simp only [pairedInvariant,next,Nat.zero_ne_one,ite_false,ite_true]
        exact complete_backward_round_keeps_both_shared_owner_relations _ _ _ positive inputs _

theorem no_finite_iteration_limit_can_be_a_termination_proof
    (extras : Nat → List Edge) (n : Nat) : history extras (n+1) ≠ [] := by
  have invariant := uncapped_alternating_demand_invariant extras n
  unfold pairedInvariant at invariant
  split at invariant
  · intro empty; rw [empty] at invariant; exact List.not_mem_nil invariant.1
  · intro empty; rw [empty] at invariant; exact List.not_mem_nil invariant.1

theorem the_same_nonempty_demand_returns_at_every_forward_run
    (extras : Nat → List Edge) (n : Nat) :
    backwardRow .t ∈ history extras (2*n+1) ∧
    backwardRow .u ∈ history extras (2*n+1) := by
  have h := uncapped_alternating_demand_invariant extras (2*n)
  simpa [pairedInvariant,backwardInputs,Nat.add_mod,Nat.mul_mod] using h



/-- The critical result is intrinsic MAY. Raising either global or own
    relative field budget cannot refine or reclassify it. -/
theorem critical_forward_result_is_never_a_cut (k b : Nat) (m : Color) :
    cut k (value ret [] .may m.flip) = value ret [] .may m.flip ∧
    cut b (value p [] .may m) = value p [] .may m := by
  simp [cut,value,fact]

def fineBackwardEdge (m : Color) : Edge :=
  (fact ret [] .star m.flip,value p [f] .ne m)
def fineForwardRow (m : Color) : Row :=
  ⟨fact p [f] .ne m,fact ret [] .star m.flip⟩

theorem the_finer_real_cut_is_generated_as_well (run k : Nat) (m : Color)
    (positive : 1 ≤ k) : fineBackwardEdge m ∈ backwardCandidates run k m := by
  have nz : k ≠ 0 := Nat.ne_of_gt positive
  have minOne : min k 1 = 1 := Nat.min_eq_right positive
  cases m <;>
    simp [backwardCandidates,emit,emitBase,reverseGenerate,backwardRow,
      fineBackwardEdge,value,fact,p,ret,f,g,Color.id,Color.flip,selector,marksOK,
      completeFamily,primary,dropHead,atHead,seed,probe,legalSeed,nz,positive,
      restrictOne,rawImage,normalize,intersectExit,marksMeet,admits,minOne,cut] <;>
    split <;> simp_all
  all_goals
    have one : k = 1 := Nat.le_antisymm (Nat.le_of_lt_succ (by assumption)) positive
    subst k
    decide

/-- Finer qualified queries can indeed produce independently NORMAL
    uniform output. This does not give a NORMAL MAY result that would
    authorize deleting the coarse marked-MAY/D observation. -/
theorem fine_uniform_start_and_normal_root_output (run k : Nat) (m : Color)
    (positive : 1 ≤ k) :
    ⟨fact p [f] .must m,false⟩ ∈ emit run k false (fineForwardRow m).entry
      ⟨fact p [f] .must m,false⟩ ∧
    generate m ⟨fact p [f] .must m,false⟩ =
      [value ret [] .must m.flip false,value ret [f] .must m.flip false] := by
  have nz : k ≠ 0 := Nat.ne_of_gt positive
  cases m <;>
    simp [fineForwardRow,generate,emit,emitBase,selector,marksOK,completeFamily,
      primary,dropHead,atHead,seed,probe,legalSeed,nz,positive,value,fact,p,ret,f,g,
      Color.id,Color.flip]

theorem even_identical_normal_may_is_outside_the_selected_definite_support_law (m : Color) :
    rootMay m ∈ packet [rootMay m,value p [] .may m false] := by
  exact any_extra_ready_replies_keep_the_may_witness _ _ _ (by simp [rootMay])

theorem every_forward_phase_also_has_live_zero_target_guidance
    (extras : Nat → List Edge) (n : Nat) :
    backwardInputs (history extras (2*n+1)) ∧
    TargetZeroKernel.continuationRelevant (terminal (rootMay .u)) = true ∧
    sourceHit = some (TargetZeroKernel.targetSummary 0 .zero) := by
  exact ⟨the_same_nonempty_demand_returns_at_every_forward_run extras n,
    the_three_forward_calls_reach_a_demand_observation.2.2.2,
    the_three_backward_calls_reach_the_actual_producer.2.2⟩

end AlternatingCondition
