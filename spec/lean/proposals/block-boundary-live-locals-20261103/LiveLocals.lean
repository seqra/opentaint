import Std

namespace LiveLocals

abbrev Mask (n : Nat) := Fin n → Bool

def allMasks : (n : Nat) → List (Mask n)
  | 0 => [fun i => Fin.elim0 i]
  | n+1 => (allMasks n).flatMap (fun tail => [Fin.cases false tail, Fin.cases true tail])

theorem every_mask_enumerated (n : Nat) (mask : Mask n) : mask ∈ allMasks n := by
  induction n with
  | zero =>
    have same : mask = (fun i => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    rw [same]
    exact List.mem_cons_self
  | succ n ih =>
    let tail : Mask n := fun i => mask i.succ
    have member := ih tail
    have rebuilt : Fin.cases (mask 0) tail = mask := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [← rebuilt]
    apply List.mem_flatMap.mpr
    refine ⟨tail,member,?_⟩
    cases h : mask 0
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self

def MaskLe (a b : Mask n) : Prop := ∀ i, a i = true → b i = true

def MonotoneTransfer (f : Mask n → Mask n) : Prop := ∀ a b, MaskLe a b → MaskLe (f a) (f b)
def Closed (f : Mask n → Mask n) (mask : Mask n) : Prop := MaskLe (f mask) mask

instance closedDecidable (f : Mask n → Mask n) (mask : Mask n) : Decidable (Closed f mask) :=
  inferInstanceAs (Decidable (∀ i, f mask i = true → mask i = true))

/-- Exhaustive finite reference algorithm, not the proposed production worklist. -/
def least (f : Mask n → Mask n) (i : Fin n) : Bool :=
  (allMasks n).all (fun mask => if Closed f mask then mask i else true)

theorem least_characterization (f : Mask n → Mask n) (i : Fin n) :
    least f i = true ↔ ∀ mask, Closed f mask → mask i = true := by
  constructor
  · intro yes mask closed
    have := List.all_eq_true.mp yes mask (every_mask_enumerated n mask)
    simpa [closed] using this
  · intro all
    apply List.all_eq_true.mpr
    intro mask member
    by_cases closed : Closed f mask
    · simpa [closed] using all mask closed
    · simp [closed]

theorem least_below_each_closed (f : Mask n → Mask n) (mask : Mask n) (closed : Closed f mask) :
    MaskLe (least f) mask := fun i hi => (least_characterization f i).mp hi mask closed

theorem least_is_closed (f : Mask n → Mask n) (mono : MonotoneTransfer f) : Closed f (least f) := by
  intro i fi
  apply (least_characterization f i).mpr
  intro mask closed
  exact closed i (mono (least f) mask (least_below_each_closed f mask closed) i fi)

theorem least_is_fixed (f : Mask n → Mask n) (mono : MonotoneTransfer f) : f (least f) = least f := by
  have closed := least_is_closed f mono
  have imageClosed : Closed f (f (least f)) := mono (f (least f)) (least f) closed
  have reverse := least_below_each_closed f (f (least f)) imageClosed
  funext i
  cases a : f (least f) i <;> cases b : least f i
  · rfl
  · have := reverse i b; simp [a] at this
  · have := closed i a; simp [b] at this
  · rfl

abbrev Graph (n : Nat) := Fin n → List (Fin n)

def successorsLive (graph : Graph n) (mask : Mask n) (i : Fin n) : Bool := (graph i).any mask

def forward (graph : Graph n) (use defn : Mask n) (mask : Mask n) (i : Fin n) : Bool :=
  use i || (!defn i && successorsLive graph mask i)

def backward (graph : Graph n) (mentions : Mask n) (mask : Mask n) (i : Fin n) : Bool :=
  mentions i || successorsLive graph mask i

structure Instruction where
  usesOld : Bool
  definesOld : Bool
  deriving DecidableEq, Repr

def blockTransfer : List Instruction → Bool → Bool
  | [], after => after
  | inst::rest, after => inst.usesOld || (!inst.definesOld && blockTransfer rest after)

def blockUse (instructions : List Instruction) : Bool := blockTransfer instructions false
def blockDef (instructions : List Instruction) : Bool := instructions.any Instruction.definesOld

theorem ordered_block_transfer_has_USE_DEF_form (instructions : List Instruction) (after : Bool) :
    blockTransfer instructions after = blockUse instructions || (!blockDef instructions && after) := by
  induction instructions with
  | nil => cases after <;> rfl
  | cons inst rest ih =>
    rcases inst with ⟨use,defn⟩
    cases use <;> cases defn <;> cases h : blockDef rest <;> cases u : blockUse rest <;>
      cases after <;> simp [blockTransfer,blockUse,blockDef] at ih ⊢ <;> simp_all [blockUse,blockDef]

theorem first_definition_blocks_later_use_of_old_tmp :
    blockUse [⟨false,true⟩,⟨true,false⟩] = false := by decide

theorem RHS_read_precedes_LHS_commit : blockUse [⟨true,true⟩] = true := by decide

theorem successors_monotone (graph : Graph n) : MonotoneTransfer (successorsLive graph) := by
  intro a b le i yes
  obtain ⟨next,edge,live⟩ := List.any_eq_true.mp yes
  exact List.any_eq_true.mpr ⟨next,edge,le next live⟩

theorem forward_monotone (graph : Graph n) (use defn : Mask n) : MonotoneTransfer (forward graph use defn) := by
  intro a b le i yes
  cases u : use i <;> cases d : defn i <;> simp [forward,u,d] at yes ⊢
  exact successors_monotone graph a b le i yes

theorem backward_monotone (graph : Graph n) (mentions : Mask n) : MonotoneTransfer (backward graph mentions) := by
  intro a b le i yes
  cases u : mentions i <;> simp [backward,u] at yes ⊢
  exact successors_monotone graph a b le i yes

inductive FirstUse (graph : Graph n) (use defn : Mask n) : Fin n → Prop where
  | here (i) : use i = true → FirstUse graph use defn i
  | next (i j) : defn i = false → j ∈ graph i → FirstUse graph use defn j → FirstUse graph use defn i

theorem first_use_below_every_closed (graph : Graph n) (use defn : Mask n)
    (mask : Mask n) (closed : Closed (forward graph use defn) mask)
    (i : Fin n) (path : FirstUse graph use defn i) : mask i = true := by
  induction path with
  | here i mentioned => exact closed i (by simp [forward,mentioned])
  | next i j noKill edge later ih =>
    apply closed i
    have succ : successorsLive graph mask i = true := List.any_eq_true.mpr ⟨j,edge,ih⟩
    simp [forward,noKill,succ]

theorem first_use_is_live (graph : Graph n) (use defn : Mask n) (i : Fin n)
    (path : FirstUse graph use defn i) : least (forward graph use defn) i = true := by
  apply (least_characterization _ i).mpr
  intro mask closed
  exact first_use_below_every_closed graph use defn mask closed i path

/-- A path-free executable test for first-use reachability. -/
def firstUseMask (graph : Graph n) (use defn : Mask n) : Mask n := least (forward graph use defn)

theorem live_unfolds_to_use_or_live_unkilled_successor (graph : Graph n) (use defn : Mask n) (i : Fin n) :
    firstUseMask graph use defn i = forward graph use defn (firstUseMask graph use defn) i := by
  exact congrFun (least_is_fixed _ (forward_monotone graph use defn)).symm i

/- Every first-use path has a constructive finite search witness and every found
   search result has a path. The dead-token theorem below uses first-use soundness
   and the least fixed-point equation, not an assumed native conclusion equality.
   A polynomial worklist adapter and a fuel bound are not verified here. -/

def firstUseSearch (graph : Graph n) (use defn : Mask n) : Nat → Fin n → Bool
  | 0, _ => false
  | fuel+1, i => use i || (!defn i && (graph i).any (firstUseSearch graph use defn fuel))

theorem search_sound (graph : Graph n) (use defn : Mask n) (fuel : Nat) (i : Fin n)
    (found : firstUseSearch graph use defn fuel i = true) : FirstUse graph use defn i := by
  induction fuel generalizing i with
  | zero => simp [firstUseSearch] at found
  | succ fuel ih =>
    cases u : use i
    · have both : defn i = false ∧ (graph i).any (firstUseSearch graph use defn fuel) = true := by
        simpa [firstUseSearch,u] using found
      obtain ⟨next,edge,live⟩ := List.any_eq_true.mp both.2
      exact FirstUse.next i next both.1 edge (ih next live)
    · exact FirstUse.here i u

theorem path_has_finite_search_witness (graph : Graph n) (use defn : Mask n) (i : Fin n)
    (path : FirstUse graph use defn i) : ∃ fuel, firstUseSearch graph use defn fuel i = true := by
  induction path with
  | here i mentioned => exact ⟨1,by simp [firstUseSearch,mentioned]⟩
  | next i j noKill edge later ih =>
    obtain ⟨fuel,found⟩ := ih
    exact ⟨fuel+1,by
      have := List.any_eq_true.mpr ⟨j,edge,found⟩
      simp [firstUseSearch,noKill,this]⟩

/-- Each route lists only its own actual next destinations; normal exits never
    borrow a feedback route's destinations. -/
def boundary (live : Mask n) (destinations : List (Fin n)) : Bool := destinations.any live

theorem boundary_live_iff_actual_destination_live (live : Mask n) (destinations : List (Fin n)) :
    boundary live destinations = true ↔ ∃ i ∈ destinations, live i = true := List.any_eq_true

theorem boundary_dead_means_every_actual_destination_dead (live : Mask n) (destinations : List (Fin n))
    (dead : boundary live destinations = false) (i : Fin n) (edge : i ∈ destinations) : live i = false := by
  cases h : live i
  · rfl
  · have yes : boundary live destinations = true := List.any_eq_true.mpr ⟨i,edge,h⟩
    simp [dead] at yes

theorem all_exit_continuations_union (live : Mask n) (a b : List (Fin n)) :
    boundary live (a ++ b) = (boundary live a || boundary live b) := List.any_append

def routeExampleLive : Mask 2 := fun i => i == 0

theorem feedback_live_but_AL_dead :
    boundary routeExampleLive [0] = true ∧ boundary routeExampleLive [1] = false := by decide

theorem wrongly_borrowing_feedback_retains_dead_AL_local :
    boundary routeExampleLive ([1] ++ [0]) = true := by decide

/- Old-conclusion instruction semantics. Uses can observe the old token; DEF
   removes it after uses. Nonlocal/premise data is carried unchanged here. -/
def observeOld (use defn : Mask n) : List (Fin n) → Option Nat → List Nat
  | [], _ => []
  | i::rest, token =>
      (if use i then token.toList else []) ++ observeOld use defn rest (if defn i then none else token)

inductive Follows (graph : Graph n) : Fin n → List (Fin n) → Prop where
  | stop (i) : Follows graph i []
  | step (i rest next) : next ∈ graph i → Follows graph next rest → Follows graph i (i::rest)

/-- This start-inclusive path predicate also permits an execution to stop. -/
inductive Execution (graph : Graph n) : Fin n → List (Fin n) → Prop where
  | stop (i) : Execution graph i []
  | last (i) : Execution graph i [i]
  | step (i next rest) : next ∈ graph i → Execution graph next rest → Execution graph i (i::rest)

theorem none_token_is_silent (use defn : Mask n) (path : List (Fin n)) : observeOld use defn path none = [] := by
  induction path with
  | nil => rfl
  | cons i rest ih => cases u : use i <;> cases d : defn i <;> simp [observeOld,u,d,ih]

theorem dead_local_has_no_instruction_observations (graph : Graph n) (use defn : Mask n)
    (i : Fin n) (path : List (Fin n)) (execution : Execution graph i path)
    (dead : firstUseMask graph use defn i = false) (token : Option Nat) :
    observeOld use defn path token = [] := by
  induction execution with
  | stop i => rfl
  | last i =>
    have equation := live_unfolds_to_use_or_live_unkilled_successor graph use defn i
    have noUse : use i = false := by cases h : use i <;> simp_all [forward]
    simp [observeOld,noUse]
  | step i next rest edge follows ih =>
    have equation := live_unfolds_to_use_or_live_unkilled_successor graph use defn i
    have noUse : use i = false := by cases h : use i <;> simp_all [forward]
    cases kill : defn i
    · have nextDead : firstUseMask graph use defn next = false := by
        cases h : firstUseMask graph use defn next
        · rfl
        · have suc : successorsLive graph (firstUseMask graph use defn) i = true := List.any_eq_true.mpr ⟨next,edge,h⟩
          simp [forward,noUse,kill,suc,dead] at equation
      simpa [observeOld,noUse,kill] using ih nextDead
    · simp [observeOld,noUse,kill,none_token_is_silent]

theorem dropping_dead_token_has_same_instruction_observations (graph : Graph n) (use defn : Mask n)
    (i : Fin n) (path : List (Fin n)) (execution : Execution graph i path)
    (dead : firstUseMask graph use defn i = false) (token : Nat) :
    observeOld use defn path (some token) = observeOld use defn path none := by
  rw [dead_local_has_no_instruction_observations graph use defn i path execution dead, none_token_is_silent]

inductive Base where
  | localVar (id : Nat) | zero | staticSlot | argument | receiver | returnSlot | exceptionSlot | target
  deriving DecidableEq, Repr

structure Packet (P A : Type) where
  original : P
  base : Base
  annotation : A
  deriving DecidableEq, Repr

def keepPacket (liveLocal : Nat → Bool) (packet : Packet P A) : Bool :=
  match packet.base with
  | .localVar id => liveLocal id
  | _ => true

def filterBoundary (liveLocal : Nat → Bool) (packets : List (Packet P A)) : List (Packet P A) :=
  packets.filter (keepPacket liveLocal)

theorem retained_packet_preserves_whole_premise_and_annotation (liveLocal : Nat → Bool)
    (packets : List (Packet P A)) (packet : Packet P A) (member : packet ∈ filterBoundary liveLocal packets) :
    packet ∈ packets := (List.mem_filter.mp member).1

theorem live_loop_carried_packet_uses_unchanged_native_path (liveLocal : Nat → Bool)
    (packets : List (Packet P A)) (packet : Packet P A) (member : packet ∈ packets)
    (live : keepPacket liveLocal packet = true) : packet ∈ filterBoundary liveLocal packets :=
  List.mem_filter.mpr ⟨member,live⟩

theorem dead_route_local_cannot_escape (liveLocal : Nat → Bool) (id : Nat)
    (dead : liveLocal id = false) (packets : List (Packet P A)) (packet : Packet P A)
    (base : packet.base = .localVar id) : packet ∉ filterBoundary liveLocal packets := by
  intro found
  have kept := (List.mem_filter.mp found).2
  simp [keepPacket,base,dead] at kept

theorem nonlocals_always_retained (liveLocal : Nat → Bool) (packet : Packet P A)
    (notLocal : ∀ id, packet.base ≠ Base.localVar id) : keepPacket liveLocal packet = true := by
  cases h : packet.base <;> simp [keepPacket,h] at notLocal ⊢

theorem filtering_does_not_rebuild_retained_packets (liveLocal : Nat → Bool)
    (packets : List (Packet P A)) :
    filterBoundary liveLocal packets = packets.filter (keepPacket liveLocal) := rfl

theorem stronger_filter_after_weaker_same_as_stronger (weak strong : Nat → Bool)
    (included : ∀ id, strong id = true → weak id = true) (packets : List (Packet P A)) :
    filterBoundary strong (filterBoundary weak packets) = filterBoundary strong packets := by
  induction packets with
  | nil => rfl
  | cons packet rest ih =>
    have implication : keepPacket strong packet = true → keepPacket weak packet = true := by
      cases b : packet.base <;> simp [keepPacket,b]
      exact included _
    cases w : keepPacket weak packet <;> cases s : keepPacket strong packet <;>
      simp [filterBoundary,w,s] at ih ⊢
    · exact ih
    · have := implication s; simp [w] at this
    · exact ih
    · exact ih

theorem actual_route_live_implies_shared_leave_live (live : Mask n)
    (route sharedLeave : List (Fin n)) (covered : ∀ i ∈ route, i ∈ sharedLeave)
    (yes : boundary live route = true) : boundary live sharedLeave = true := by
  obtain ⟨i,edge,hit⟩ := List.any_eq_true.mp yes
  exact List.any_eq_true.mpr ⟨i,covered i edge,hit⟩

theorem actual_route_filter_removes_shared_exit_leakage (live : Nat → Mask n)
    (route sharedLeave : List (Fin n)) (covered : ∀ i ∈ route, i ∈ sharedLeave)
    (packets : List (Packet P A)) :
    filterBoundary (fun id => boundary (live id) route)
      (filterBoundary (fun id => boundary (live id) sharedLeave) packets) =
    filterBoundary (fun id => boundary (live id) route) packets := by
  apply stronger_filter_after_weaker_same_as_stronger
  intro id hit
  exact actual_route_live_implies_shared_leave_live (live id) route sharedLeave covered hit

structure BoundaryState (E P A : Type) where
  completedEffects : E
  packets : List (Packet P A)

def boundaryState (mask : Nat → Bool) (state : BoundaryState E P A) : BoundaryState E P A :=
  ⟨state.completedEffects,filterBoundary mask state.packets⟩

theorem completed_source_Target_static_effects_unchanged (mask : Nat → Bool)
    (state : BoundaryState E P A) : (boundaryState mask state).completedEffects = state.completedEffects := rfl

theorem dead_local_drops_while_nonlocal_annotations_stay (annotation : A) (original : P) :
    filterBoundary (fun _ => false)
      [⟨original,.localVar 3,annotation⟩,⟨original,.staticSlot,annotation⟩] =
      [⟨original,.staticSlot,annotation⟩] := rfl

def tmpUse : Mask 2 := fun i => i == 1
def tmpDef : Mask 2 := fun i => i == 0
def tmpGraph : Graph 2 := fun i => if i == 0 then [1] else [0]

theorem fresh_iteration_assignment_kills_old_tmp : firstUseMask tmpGraph tmpUse tmpDef 0 = false := by decide

theorem tmp_is_live_after_definition_before_use : firstUseMask tmpGraph tmpUse tmpDef 1 = true := by decide

theorem backward_mentions_do_not_kill_lhs :
    least (backward tmpGraph (fun i => i == 0)) 0 = true := by decide

theorem read_before_write_keeps_old_value :
    firstUseMask tmpGraph (fun i => i == 0) tmpDef 0 = true := by decide

/- x is assigned before the loop. Node 0 is `tmp = x`, node 1 uses tmp,
   and node 2 is the actual after-loop continuation with no local reads. -/
def principalGraph : Graph 3 := fun i => if i == 0 then [1] else if i == 1 then [0,2] else []
def principalTmpUse : Mask 3 := fun i => i == 1
def principalTmpDef : Mask 3 := fun i => i == 0
def principalXUse : Mask 3 := fun i => i == 0
def principalXDef : Mask 3 := fun _ => false

theorem principal_tmp_dead_on_repeat_x_live :
    firstUseMask principalGraph principalTmpUse principalTmpDef 0 = false ∧
    firstUseMask principalGraph principalXUse principalXDef 0 = true := by decide

theorem principal_tmp_live_inside_body_before_use :
    firstUseMask principalGraph principalTmpUse principalTmpDef 1 = true := by decide

theorem principal_tmp_cannot_escape_actual_AL_route :
    boundary (firstUseMask principalGraph principalTmpUse principalTmpDef) [2] = false := by decide

def principalRepeatLocal (id : Nat) : Bool :=
  if id == 0 then boundary (firstUseMask principalGraph principalTmpUse principalTmpDef) [0]
  else if id == 1 then boundary (firstUseMask principalGraph principalXUse principalXDef) [0] else true

theorem principal_repeat_drops_tmp_keeps_x_and_completed_sink (original : P) (annotation : A) (effects : E) :
    boundaryState principalRepeatLocal
      (⟨effects,[⟨original,.localVar 0,annotation⟩,⟨original,.localVar 1,annotation⟩]⟩ : BoundaryState E P A) =
      ⟨effects,[⟨original,.localVar 1,annotation⟩]⟩ := by rfl

end LiveLocals
