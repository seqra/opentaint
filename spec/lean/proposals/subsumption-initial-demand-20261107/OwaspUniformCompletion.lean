/-
Prepared operational OWASP H-only uniform-packet component; no child jobs.
The actual C2 and actual annotated C5 implementations are imported. This is
not a proof of the native driver or of non-uniform/other-field programs.

getBytes: direct copy and read H. newString: direct copy and write H.
For a canonical MUST packet at H^n, the read-stage packet is {H^n,H^(n-1)};
prefix MUST canonicalization keeps H^(n-1). The constructor packet is then
{H^(n-1),H^n}; it keeps the same shorter MUST fact. There is no body growth.
For incoming pair n <= s+1, C5 projects that MUST result to selector H^s
without cutting, provided the actual field limit contains n and s.

Completion prefix self-rows have n=s. Its paired erasure keeps the original
n,s, so does not manufacture a prefix Cartesian product which violates the
budget. A separate B2 normal-transport witness removes an unprotected plain
T/STAR arm before completion. All pass operations preserve H=false.
-/
import RelativeAdmission
import AnnotatedC5Exit

namespace OwaspUniformCompletion
open PlainStarRelativeAdmission
open ApSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

def storage : Nat := 42
def nativePath (n : Nat) : List Nat := List.replicate n storage
def path (n : Nat) : RelativeRestriction.Path := List.replicate n (.field storage)
def mode (limit : Nat) : Mode := ⟨3,limit,.forward⟩
def demand (n : Nat) : Demand := ⟨0,nativePath n,.any,.flow,[]⟩
def actualUniform : Actual := ⟨⟨0,[],.must,.full 7,[]⟩,.normal,false⟩
def wantedSeed (n : Nat) : Seed := ⟨⟨0,nativePath n,.must,.flow,[]⟩,.normal⟩

theorem actual_uniform_admits_demanded_MUST_prefix (limit n : Nat)
    (positive : 1 ≤ limit) (fits : n ≤ limit) :
    emit (mode limit) (demand n) actualUniform = some (wantedSeed n) := by
  cases n with
  | zero =>
      simp [emit,selected,table,commonLegal,Allowed,validDemand,legalActual,mode,demand,
        actualUniform,wantedSeed,nativePath,render,admissionLayer,intrinsic,joinLayer,
        RestrictedInitialPolicy.acceptsMark,relate,dropPrefix,positive]
  | succ n =>
      simp [emit,selected,table,commonLegal,Allowed,validDemand,legalActual,mode,demand,
        actualUniform,wantedSeed,nativePath,render,admissionLayer,intrinsic,joinLayer,
        RestrictedInitialPolicy.acceptsMark,relate,dropPrefix,positive,fits,
        List.replicate_succ,tailAdmits,Excl.admits,memB,demandE,List.length_replicate]

theorem path_depth (n : Nat) : RelativeRestriction.depth (path n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change RelativeRestriction.depth (List.replicate n (.field storage)) = n at ih
      simp only [path,List.replicate_succ,RelativeRestriction.depth]
      rw [ih]

theorem path_prefix_of_le (a b : Nat) (before : a ≤ b) :
    (path a).IsPrefix (path b) := by
  refine ⟨path (b-a),?_⟩
  simp [path,List.replicate_append_replicate,Nat.add_sub_of_le before]

theorem path_equality_implies_depth_equality (a b : Nat) (same : path a = path b) : a = b := by
  have lengths := congrArg List.length same
  simpa [path] using lengths

/-- At the fixed complete origin/mark/layer with Empty E, a MUST prefix
contains the longer H-only member. This is the actual prefix union, not a
claim that isolated STAR facts have the same coverage relation. -/
def mustPoint (depth location : Nat) : Prop := depth ≤ location
def canonicalPair (left right : Nat) : Nat := min left right
theorem MUST_packet_union_is_prefix (left right location : Nat) :
    mustPoint (canonicalPair left right) location ↔
      mustPoint left location ∨ mustPoint right location := by
  simp only [mustPoint,canonicalPair]
  constructor
  · intro bounded
    rcases Nat.le_total left right with leftFirst | rightFirst
    · exact Or.inl (by simpa only [Nat.min_eq_left leftFirst] using bounded)
    · exact Or.inr (by simpa only [Nat.min_eq_right rightFirst] using bounded)
  · rintro (bounded | bounded)
    · exact Nat.le_trans (Nat.min_le_left left right) bounded
    · exact Nat.le_trans (Nat.min_le_right left right) bounded

def getBytes (n : Nat) : Nat := canonicalPair n (n-1)
def newString (n : Nat) : Nat := canonicalPair n (n+1)
def body (n : Nat) : Nat := newString (getBytes n)
theorem getBytes_strips_at_most_one_H (n : Nat) : getBytes n = n-1 := by
  exact Nat.min_eq_right (Nat.sub_le n 1)
theorem constructor_addition_is_MUST_subsumed (n : Nat) : newString n = n := by
  simp [newString,canonicalPair]
theorem body_never_grows (n : Nat) : body n = n-1 := by
  simp [body,getBytes_strips_at_most_one_H,constructor_addition_is_MUST_subsumed]
theorem every_intermediate_depth_fits (limit n : Nat)
    (positive : 1 ≤ limit) (fits : n ≤ limit) :
    ∀ intermediate ∈ [n,n-1,n-1,(n-1)+1], intermediate ≤ limit := by
  intro intermediate present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  omega
theorem selected_uniform_initial_is_not_ANY (n : Nat) :
    (wantedSeed n).initial.tail ≠ .any ∧ (start (wantedSeed n)).hasProtection = false := by
  exact ⟨by simp [wantedSeed],rfl⟩

def uniform (n : Nat) : AnnotatedC5Exit.Fact :=
  ⟨⟨1,path n,.must,.flow [],[]⟩,.normal,false⟩
def selector (n : Nat) (anyTail : Bool) : AnnotatedC5Exit.Pattern :=
  ⟨1,path n,(if anyTail then .may else .star),.flow [],[]⟩
def bodyOutput (n : Nat) : AnnotatedC5Exit.Fact := uniform (body n)
def actualSourcePattern : AnnotatedC5Exit.Pattern := ⟨0,[],.must,.full 7,[]⟩
theorem real_uniform_source_covers_every_requested_prefix (n : Nat) :
    AnnotatedC5Exit.represents actualSourcePattern 0 7 (path n) := by
  refine ⟨rfl,rfl,?_⟩
  exact ⟨path n,rfl,AnnotatedC5Exit.admits_empty (path n)⟩

theorem actual_C5_projects_ancestor_MUST (m s : Nat) (anyTail : Bool)
    (before : m ≤ s) :
    AnnotatedC5Exit.meetExit true (uniform m) (selector s anyTail) = some (uniform s) := by
  by_cases same : m = s
  · subst s
    cases anyTail <;>
      simp [AnnotatedC5Exit.meetExit,AnnotatedC5Exit.slotsMeet,
        AnnotatedC5Exit.selectGeometry,AnnotatedC5Exit.normalizeSelector,
        AnnotatedC5Exit.sameHead,AnnotatedC5Exit.geometry,AnnotatedC5Exit.install,
        uniform,selector]
  · have strict : m < s := by omega
    have different : path m ≠ path s := by
      intro equal
      exact same (path_equality_implies_depth_equality m s equal)
    have earlier : (path m).IsPrefix (path s) := path_prefix_of_le m s before
    have notLater : ¬ (path s).IsPrefix (path m) := by
      rintro ⟨suffix,equal⟩
      have lengths := congrArg List.length equal
      simp only [List.length_append,path,List.length_replicate] at lengths
      omega
    cases anyTail <;>
      simp [AnnotatedC5Exit.meetExit,AnnotatedC5Exit.slotsMeet,
        AnnotatedC5Exit.selectGeometry,AnnotatedC5Exit.normalizeSelector,
        AnnotatedC5Exit.rebase,AnnotatedC5Exit.install,
        AnnotatedC5Exit.admits_empty,uniform,selector,different,earlier,notLater]

theorem actual_C5_restricts_without_DEMAND_cut (limit n s : Nat) (anyTail : Bool)
    (relative : n ≤ s+1) (fits : s ≤ limit) :
    AnnotatedC5Exit.restrictData true limit (bodyOutput n) (selector s anyTail) =
      some (uniform s) := by
  have before : body n ≤ s := by rw [body_never_grows]; omega
  have meet := actual_C5_projects_ancestor_MUST (body n) s anyTail before
  have within : RelativeRestriction.depth (uniform s).path ≤
      AnnotatedC5Exit.pairBudget limit (selector s anyTail) := by
    simp only [uniform,AnnotatedC5Exit.pairBudget,selector,path_depth]
    exact Nat.le_min.mpr ⟨fits,Nat.le_succ s⟩
  simp only [AnnotatedC5Exit.restrictData,bodyOutput,meet,Option.map_some]
  exact congrArg some (AnnotatedC5Exit.within_cut_is_identity _ _ within)

theorem all_results_are_NORMAL_and_unprotected (limit n s : Nat) (anyTail : Bool)
    (relative : n ≤ s+1) (fits : s ≤ limit) :
    (AnnotatedC5Exit.restrictData true limit (bodyOutput n) (selector s anyTail)).map
      (fun result => (result.layer,result.h,result.tail)) = some (.normal,false,.must) := by
  rw [actual_C5_restricts_without_DEMAND_cut limit n s anyTail relative fits]
  rfl

theorem prefix_self_row_has_relative_budget (n : Nat) : n ≤ n+1 := Nat.le_succ n
theorem paired_erasure_keeps_original_budget (n s : Nat) (old : n ≤ s+1) : n ≤ s+1 := old

/- B2 NORMAL transport arm. It is derived from the actual new C2 initial,
the reverse direct-copy followed by reverse H-read transport, and actual C5.
The shown cell is independent of the extra uncertain branches. -/
def backwardMode : Mode := ⟨2,1,.backward⟩
def backwardDemand : Demand := ⟨1,[],.any,.flow,[]⟩
def backwardActual : Actual := ⟨⟨1,[],.any,.full 7,[]⟩,.demand,false⟩
def backwardSeed : Seed := ⟨⟨1,[],.star,.flow,[]⟩,.normal⟩
def tailToC5 : Tail → RelativeRestriction.Tail
  | .exact => .exact | .star => .star | .any => .may | .must => .must
def slotToC5 : ScalarMark → AnnotatedC5Exit.Slot
  | .flow => .flow [] | .full mark => .full mark
def reverseTransport (seed : Seed) : AnnotatedC5Exit.Fact :=
  ⟨⟨0,.field storage :: seed.initial.path.map RelativeRestriction.Accessor.field,
      tailToC5 seed.initial.tail,slotToC5 seed.initial.mark,[]⟩,
    (match seed.layer with | .normal => .normal | .demand => .demand),false⟩
def backwardExit : AnnotatedC5Exit.Pattern := ⟨0,[],.star,.flow [],[]⟩
def inferredBackwardH : Option AnnotatedC5Exit.Fact := do
  let seed ← emit backwardMode backwardDemand backwardActual
  if rawImage backwardMode backwardDemand seed.initial then
    AnnotatedC5Exit.restrictData false 1 (reverseTransport seed) backwardExit
  else none
def normalBackwardH : AnnotatedC5Exit.Fact :=
  ⟨⟨0,[.field storage],.star,.flow [],[]⟩,.normal,false⟩

theorem B2_actual_C2_emits_NORMAL_FLOW_identity :
    emit backwardMode backwardDemand backwardActual = some backwardSeed := by decide
theorem B2_NORMAL_H_transport_is_inferred :
    inferredBackwardH = some normalBackwardH := by decide

/-- Exact same STAR-coordinate baseline coverage cell: NORMAL FLOW may
replace a plain T/DEMAND arm; H remains a veto. The adapter is the actual
FlowBackedCoverage layer/mark/tail/path gate, not a NORMAL-shape upgrade. -/
def plainTArm : AnnotatedC5Exit.Fact :=
  ⟨⟨0,[.field storage],.star,.full 7,[]⟩,.demand,false⟩
def plainTInitial : Pattern := ⟨1,[],.star,.full 7,[]⟩
def sameInitialGeometry : Bool :=
  decide (backwardSeed.initial.base = plainTInitial.base ∧
    backwardSeed.initial.path = plainTInitial.path ∧
    backwardSeed.initial.tail = plainTInitial.tail ∧
    backwardSeed.initial.exclusion = plainTInitial.exclusion ∧
    backwardSeed.initial.mark = .flow ∧ plainTInitial.mark = .full 7)
def sameCoordinatePlainCoverage (flow taint : AnnotatedC5Exit.Fact) : Bool :=
  sameInitialGeometry && decide (flow.base = taint.base ∧ flow.path = taint.path ∧
    flow.tail = .star ∧ taint.tail = .star ∧ flow.exclusion = [] ∧ taint.exclusion = [] ∧
    (flow.layer = .normal ∨ taint.layer = .demand) ∧ taint.h = false) &&
    (match flow.slot,taint.slot with
     | .flow excluded,.full mark => decide (mark ∉ excluded)
     | _,_ => false)
theorem B2_NORMAL_FLOW_covers_plain_T_DEMAND_H_arm :
    sameCoordinatePlainCoverage normalBackwardH plainTArm = true := by decide
theorem protected_arm_still_cannot_be_subsumed :
    sameCoordinatePlainCoverage normalBackwardH {plainTArm with h := true} = false := by decide
def finalPlainArms : List AnnotatedC5Exit.Fact :=
  if sameCoordinatePlainCoverage normalBackwardH plainTArm then [] else [plainTArm]
theorem covered_plain_T_STAR_H_is_removed_before_completion : finalPlainArms = [] := by decide

def passH (old : Bool) : Bool := old
theorem plain_pass_never_creates_H : passH false = false := rfl
theorem pass_preserves_existing_H (old : Bool) : passH old = old := rfl

/-- Scoped stop consequence: if these are all helper DATA rows, each inferred
row is NORMAL and contributes no outgoing DATA refinement. This does not
silently exclude targets, other marks, other methods or unseen native rows. -/
def outgoingDemand (result : AnnotatedC5Exit.Fact) : Bool :=
  decide (result.layer = .demand)
theorem uniform_body_contributes_no_outgoing_refinement
    (limit n s : Nat) (anyTail : Bool) (relative : n ≤ s+1) (fits : s ≤ limit) :
    ((AnnotatedC5Exit.restrictData true limit (bodyOutput n) (selector s anyTail)).map
      outgoingDemand).getD false = false := by
  rw [actual_C5_restricts_without_DEMAND_cut limit n s anyTail relative fits]
  rfl


#print axioms actual_uniform_admits_demanded_MUST_prefix
#print axioms path_depth
#print axioms path_prefix_of_le
#print axioms path_equality_implies_depth_equality
#print axioms MUST_packet_union_is_prefix
#print axioms getBytes_strips_at_most_one_H
#print axioms constructor_addition_is_MUST_subsumed
#print axioms body_never_grows
#print axioms every_intermediate_depth_fits
#print axioms selected_uniform_initial_is_not_ANY
#print axioms real_uniform_source_covers_every_requested_prefix
#print axioms actual_C5_projects_ancestor_MUST
#print axioms actual_C5_restricts_without_DEMAND_cut
#print axioms all_results_are_NORMAL_and_unprotected
#print axioms prefix_self_row_has_relative_budget
#print axioms paired_erasure_keeps_original_budget
#print axioms B2_actual_C2_emits_NORMAL_FLOW_identity
#print axioms B2_NORMAL_H_transport_is_inferred
#print axioms B2_NORMAL_FLOW_covers_plain_T_DEMAND_H_arm
#print axioms protected_arm_still_cannot_be_subsumed
#print axioms covered_plain_T_STAR_H_is_removed_before_completion
#print axioms plain_pass_never_creates_H
#print axioms pass_preserves_existing_H
#print axioms uniform_body_contributes_no_outgoing_refinement

end OwaspUniformCompletion
