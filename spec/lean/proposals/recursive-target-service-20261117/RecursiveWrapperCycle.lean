import DirectPossibleReplay
import RootCleanerPolicy
namespace RecursiveWrapperCycle
open NonEmptyPolicy NonEmptyRestriction AcyclicMayCycle
open NestedSavedReplayCycle NestedColdMachine
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
abbrev Edge:=Ap × Value
local instance : ReflBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
local instance : LawfulBEq Nat where
  rfl := by intro a; exact decide_eq_true rfl
  eq_of_beq := by intro a b h; exact of_decide_eq_true h

def fields (n : Nat) : Path:=List.replicate n f
def normal (n : Nat) : Edge:=(ap p [] .star,val (ap ret (fields n) .star))
def frontier (n : Nat) : Edge:=(ap p [] .star,val (ap ret (fields n) .ne) true)
def point (n : Nat) : Value:=val (ap ret (fields n) .exact)
def wrap (c : Value) : Value:={c with ap:={c.ap with path:=f::c.ap.path}}

theorem fields_successor (n : Nat) : fields (n+1)=f::fields n := by
  simp only [fields,List.replicate_succ]
theorem field_length (n : Nat) : (fields n).length=n := List.length_replicate
theorem take_fields (k n : Nat) : (fields n).take k=fields (min k n) := by
  simp only [fields,List.take_replicate]
theorem strip_own_fields (a b : Nat) : dropHead (fields a) (fields (a+b))=some (fields b) := by
  induction a with
  | zero=>simp only [Nat.zero_add,fields,List.replicate_zero,dropHead]
  | succ a ih=>
    simpa only [Nat.succ_add,fields_successor,dropHead,ite_true] using ih
theorem cannot_strip_a_longer_prefix (n : Nat) : dropHead (fields (n+1)) (fields n)=none := by
  induction n with
  | zero=>rfl
  | succ n ih=>simpa only [fields_successor,dropHead,ite_true] using ih

-- The ordinary branch returns its input. One recursive frame assigns the
-- returned value into fresh y.f, then returns y. These are real transfers.
theorem the_base_case_is_a_NORMAL_identity : normalize (ap p [] .exact) (point 0)=normal 0 := by decide
theorem one_frame_adds_exactly_one_known_field (n : Nat) : wrap (point n)=point (n+1) := by
  simp only [wrap,point,val,ap,fields_successor]

theorem an_uncut_wrapper_relation_is_NORMAL (k n : Nat) (fits : n≤k) :
    normalize (ap p [] .exact) (cut k (point n))=normal n := by
  have bound : (point n).ap.path.length≤k:=by simpa only [point,val,ap,field_length] using fits
  rw [no_cut_preserves_intrinsic_may k (point n) bound]
  simp [normalize,point,normal,val,ap,normalAp]

theorem one_more_recursive_frame_creates_a_real_frontier (k : Nat) :
    normalize (ap p [] .exact) (cut k (wrap (point k)))=frontier k := by
  rw [one_frame_adds_exactly_one_known_field]
  have more : (fields (k+1)).length>k:=by rw [field_length]; exact Nat.lt_succ_self _
  simp only [cut,point,val,ap,more,ite_true,take_fields,Nat.min_self,
    Nat.min_eq_left (Nat.le_succ k)]
  simp [normalize,frontier,val,ap,normalAp]

-- This fixed point is finite at each cap. No diagnostic unroll count is
-- used: every NORMAL depth <=k is reached from the base; the cut is absorbing.
def step (k : Nat) (c : Value) : Value:=cut k (wrap c)
def unfold (k : Nat) : Nat → Value
  | 0=>point 0
  | n+1=>step k (unfold k n)

theorem every_finite_uncut_depth_is_reached (k n : Nat) (fits : n≤k) : unfold k n=point n := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [unfold,ih (Nat.le_trans (Nat.le_succ n) fits),step,one_frame_adds_exactly_one_known_field]
    exact no_cut_preserves_intrinsic_may k (point (n+1)) (by simpa only [point,val,ap,field_length] using fits)

theorem the_first_cut_is_reached (k : Nat) :
    normalize (ap p [] .exact) (unfold k (k+1))=frontier k := by
  rw [unfold,every_finite_uncut_depth_is_reached k k (Nat.le_refl _)]
  exact one_more_recursive_frame_creates_a_real_frontier k

theorem the_cut_value_is_absorbing_within_this_run (k : Nat) :
    step k (frontier k).2=(frontier k).2 := by
  have more : (f::fields k).length>k:=by simp only [List.length_cons,field_length]; exact Nat.lt_succ_self _
  simp only [step,wrap,frontier,val,ap,cut,more,ite_true]
  have take : (f::fields k).take k=fields k:=by
    rw [←fields_successor,take_fields,Nat.min_eq_left (Nat.le_succ k)]
  rw [take]

-- Existing opposite-direction inside matching is the recurring backward
-- source of MAY. This has no cleaner, mark-changing rule or opaque transfer.
def reverseRead (k : Nat) : Option Offered:=
  OverwriteReplay.apply true (OverwriteReplay.reverseEdge (normal (k+1)))
    ⟨ap p (fields k) .star,false⟩

theorem a_saved_NORMAL_wrapper_recreates_root_MAY (k : Nat) :
    reverseRead k=some ⟨ap p [] .may,true⟩ := by
  have first : dropHead (fields k) (fields (k+1))=some [f] := by
    simpa only [fields,List.replicate_one] using strip_own_fields k 1
  simp [reverseRead,normal,val,ap,OverwriteReplay.reverseEdge,OverwriteReplay.apply,
    cannot_strip_a_longer_prefix,first,OverwriteReplay.union]

def rawProbe : Seed:=⟨ap p [] .exact,false⟩
def actual : Offered:=⟨ap p [f,g] .exact (some t),false⟩
def row (k : Nat) : Row:=⟨ap p [] .may,ap ret (fields k) .star⟩

-- C2's real prefix probe, not an extra fabricated query.
theorem the_current_C2_contains_the_structural_prefix_probe (run k : Nat) (room : 2≤k) :
    rawProbe∈emit run k false (row n).entry actual := by
  have positive : k≠0:=by omega
  simp [emit,emitBase,selector,row,actual,ap,marksOK,completeFamily,primary,
    atHead,seed,probe,rawProbe,f,g,admits,dropHead,legalSeed,positive,room]

-- The current paired cap, not the global cap, recreates the next cut.
def publish (k : Nat) (c : Value) : Option Edge :=
  BoundedRefinementPipeline.restricted (k+1) [rawProbe] rawProbe c (row k)

theorem paired_C5_publishes_the_next_NORMAL_wrapper (k : Nat) :
    publish k (point (k+1))=some (normal (k+1)) := by
  have own : dropHead (fields k) (fields (k+1))=some [f]:=by simpa only [fields,List.replicate_one] using strip_own_fields k 1
  have ne : fields (k+1)≠fields k := by
    intro same
    have lengths:=congrArg List.length same
    simp only [field_length] at lengths
    omega
  simp [publish,BoundedRefinementPipeline.restricted,rawProbe,
    normalize,point,val,ap,normalAp,row,intersectExit,selector,own,ne,
    beq_eq_false_iff_ne.mpr ne,marksMeet,admits,normal,cut,field_length]


theorem paired_C5_recreates_the_cut_at_every_larger_cap (k : Nat) :
    publish k (point (k+2))=some (frontier (k+1)) := by
  have own : dropHead (fields k) (fields (k+2))=some [f,f] := by
    simpa only [fields,List.replicate_succ,List.replicate_zero] using strip_own_fields k 2
  have ne : fields (k+2)≠fields k:=by
    intro same
    have lengths:=congrArg List.length same
    simp only [field_length] at lengths
    omega
  simp [publish,BoundedRefinementPipeline.restricted,rawProbe,
    normalize,point,val,ap,normalAp,row,intersectExit,selector,own,ne,
    beq_eq_false_iff_ne.mpr ne,marksMeet,admits,frontier,cut,field_length,
    take_fields,Nat.min_eq_left (Nat.le_succ (k+1))]

theorem an_earlier_global_cut_does_not_remove_the_paired_frontier :
    publish 1 (cut 2 (point 3))=some (frontier 2) := by decide

-- The root's incoming marked fact is always subject to the real run cap.
def limit (n : Nat) : Nat:=max 1 (2*n)
def rootSource (n : Nat) : Offered:=cutOffer (limit n) actual
def observe (c : Offered) : Option UniformRootCleanerCycle.Terminal:=
  if c.ap.mark==some t then some ⟨.zero,.target,c.demand⟩ else none

def forward (n : Nat) : List UniformRootCleanerCycle.Terminal:=
  ((OverwriteReplay.apply false (frontier (n+1)) (rootSource n)).bind observe).toList
def backward (n : Nat) : List UniformRootCleanerCycle.Terminal:=
  -- The body derived this same root MAY through reverseRead. Bind it to
  -- the real T request, then execute the marking rule at x.f.g.
  match reverseRead n with
  | none=>[]
  | some reply=>
    let marked : Offered:={reply with ap:={reply.ap with mark:=some t}}
    if admits marked.ap.tail marked.ap.e [f,g] then (observe marked).toList else []

theorem root_source_never_invents_a_mark (n : Nat) : (rootSource n).ap.mark=some t := by
  by_cases more : 2>limit n <;> simp [rootSource,cutOffer,cut,actual,val,ap,more]

theorem every_forward_root_target_is_computed_from_the_real_cut (n : Nat) :
    forward n=[UniformRootCleanerCycle.target] := by
  have rootPath : dropHead [] (rootSource n).ap.path=some (rootSource n).ap.path:=rfl
  cases pathValue : (rootSource n).ap.path <;>
    simp [forward,frontier,OverwriteReplay.apply,rootPath,pathValue,dropHead,root_source_never_invents_a_mark,
      observe,UniformRootCleanerCycle.target,actual,val,ap,OverwriteReplay.union,sortBy]

theorem every_backward_target_is_computed_from_real_marking_permission (n : Nat) :
    backward n=[UniformRootCleanerCycle.target] := by
  rw [backward,a_saved_NORMAL_wrapper_recreates_root_MAY]
  rfl

theorem no_uncapped_forward_or_backward_handoff_is_empty (n : Nat) :
    UniformRootCleanerCycle.handoff (forward n)=[UniformRootCleanerCycle.guidance] ∧
    UniformRootCleanerCycle.handoff (backward n)=[UniformRootCleanerCycle.guidance] := by
  rw [every_forward_root_target_is_computed_from_the_real_cut,
    every_backward_target_is_computed_from_real_marking_permission]
  constructor <;> rfl

-- The infinite outer history has a computed (not assumed) nonempty guide
-- on every pair. Its per-run recursive value fixed point was proved above.
def history : Nat → List UniformRootCleanerCycle.Terminal
  | 0=>forward 0
  | n+1=>
    let previous:=history n
    let back:=if (UniformRootCleanerCycle.handoff previous).contains UniformRootCleanerCycle.guidance
      then backward n else []
    if (UniformRootCleanerCycle.handoff back).isEmpty then [] else forward (n+1)

theorem every_later_forward_repeats_the_literal_root_demand (n : Nat) :
    UniformRootCleanerCycle.handoff (history n)=[UniformRootCleanerCycle.guidance] := by
  induction n with
  | zero=>exact (no_uncapped_forward_or_backward_handoff_is_empty 0).1
  | succ n ih=>
    have admitted : [UniformRootCleanerCycle.guidance].contains UniformRootCleanerCycle.guidance=true:=rfl
    simp only [history,ih,admitted,ite_true,
      (no_uncapped_forward_or_backward_handoff_is_empty n).2,List.isEmpty_cons,Bool.false_eq_true,ite_false]
    exact (no_uncapped_forward_or_backward_handoff_is_empty (n+1)).1

theorem root_cut_paths_stay_within_the_global_field_limit (n : Nat) :
    (frontier (n+1)).2.ap.path.length=n+1 ∧ n+1≤limit n := by
  constructor
  · exact field_length _
  · unfold limit
    cases n with
    | zero=>decide
    | succ n=>omega

theorem the_exact_origin_has_a_NORMAL_base_case_after_run1 (n : Nat) :
    rootSource (n+1)=actual ∧
    OverwriteReplay.apply false (normal 0) (rootSource (n+1))=some actual := by
  have room : 2≤limit (n+1):=by unfold limit; omega
  have full : rootSource (n+1)=actual:=by
    simp [rootSource,cutOffer,actual,cut,val,ap,f,g,Nat.not_lt.mpr room]
  rw [full]
  constructor
  · rfl
  · rfl

theorem the_repeated_owner_frontier_is_FLOW_and_not_a_concrete_completion_row (n : Nat) :
    (frontier n).1.mark=none ∧ (frontier n).2.ap.mark=none ∧
    (frontier n).2.h=false ∧ (frontier n).2.ap.tail=.ne := by
  repeat constructor

theorem the_structural_point_probe_cannot_delegate_a_saved_read
    (mask : List Nat) (e : Edge) (opposite : Bool) (a : Offered) :
    ExclusionChildReplay.eligible rawProbe.ap mask e opposite a=false := by
  simp [ExclusionChildReplay.eligible,rawProbe,ap]

theorem no_ready_child_at_the_longest_saved_guard_can_remove_the_backward_read
    (q : Ap) (e : Edge) (opposite : Bool) (a : Offered) :
    ExclusionChildReplay.eligible q [] e opposite a=false := by
  unfold ExclusionChildReplay.eligible
  cases pathCase : dropHead a.ap.path e.1.path with
  | none=>simp
  | some rest=>cases rest <;> simp

end RecursiveWrapperCycle
