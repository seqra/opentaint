/-
  Selected FLOW-summary tail normalization. No production implementation.

  Before summary storage, replace each pure-FLOW EXACT endpoint tail with
  STAR. Preserve bases, paths, marks, layers, field E and the explicit MUST
  flag. A raw initial EXACT endpoint has Empty E. A raw EXACT conclusion can
  now carry the field-write exclusion annotation selected for this proposal.
  Other tails remain unchanged.

  This file proves representation laws and an executable normalized C5
  image test. It does not claim global soundness of this normalization.
  The historical field-write witness below rejects normalization that drops
  this annotation. The proposed annotation retains a child-write exclusion,
  carries it through a return, and installs it in the normalized STAR tail.
  The file proves this scalar write cell; it does not implement or prove all
  analyzer transfers, cleaners, alias effects, or summary-storage paths.
-/
import ApSpec.AnyTaintExDefs
import ApSpec.AbsDefs

namespace FlowSummaryNormalization
open ApSpec ApSpec.AnyTaintEx ApSpec.Abs

structure Endpoint where
  fact : PFact
  exclusion : Excl
  must : Bool
deriving DecidableEq, Repr

structure Summary where
  initial : Endpoint
  conclusion : Endpoint
  demand : Bool
deriving DecidableEq, Repr

def abstractMark : MarkA → Bool
  | .star | .starEx _ => true
  | .conc _ => false

def normalizeFlowEndpoint (p : Endpoint) : Endpoint :=
  if abstractMark p.fact.mark then
    match p.fact.kind with
    | .exact => { p with fact := { p.fact with kind := .star p.exclusion } }
    | _ => p
  else p

def pureFlow (s : Summary) : Bool := abstractMark s.initial.fact.mark && abstractMark s.conclusion.fact.mark

def normalizeSummary (s : Summary) : Summary :=
  if pureFlow s then
    ⟨normalizeFlowEndpoint s.initial, normalizeFlowEndpoint s.conclusion, s.demand⟩
  else s

theorem endpoint_fields_unchanged (p : Endpoint) :
    (normalizeFlowEndpoint p).fact.base = p.fact.base ∧
    (normalizeFlowEndpoint p).fact.path = p.fact.path ∧
    (normalizeFlowEndpoint p).fact.mark = p.fact.mark ∧
    (normalizeFlowEndpoint p).exclusion = p.exclusion ∧
    (normalizeFlowEndpoint p).must = p.must := by
  cases p with
  | mk fact e must => cases fact with
    | mk b path k mark => cases mark <;> cases k <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem endpoint_normalization_idempotent (p : Endpoint) :
    normalizeFlowEndpoint (normalizeFlowEndpoint p) = normalizeFlowEndpoint p := by
  cases p with
  | mk fact e must => cases fact with
    | mk b path k mark => cases mark <;> cases k <;> rfl

theorem summary_normalization_idempotent (s : Summary) :
    normalizeSummary (normalizeSummary s) = normalizeSummary s := by
  cases hs : pureFlow s with
  | false => simp only [normalizeSummary, hs, Bool.false_eq_true, if_false]
  | true =>
    have same : pureFlow ⟨normalizeFlowEndpoint s.initial, normalizeFlowEndpoint s.conclusion,
        s.demand⟩ = true := by
      simpa only [pureFlow, (endpoint_fields_unchanged s.initial).2.2.1,
        (endpoint_fields_unchanged s.conclusion).2.2.1] using hs
    simp only [normalizeSummary, hs, if_true, same, endpoint_normalization_idempotent]

theorem summary_layer_and_endpoint_data_unchanged (s : Summary) :
    (normalizeSummary s).demand = s.demand ∧
    (normalizeSummary s).initial.fact.path = s.initial.fact.path ∧
    (normalizeSummary s).conclusion.fact.path = s.conclusion.fact.path ∧
    (normalizeSummary s).initial.exclusion = s.initial.exclusion ∧
    (normalizeSummary s).conclusion.exclusion = s.conclusion.exclusion ∧
    (normalizeSummary s).initial.fact.mark = s.initial.fact.mark ∧
    (normalizeSummary s).conclusion.fact.mark = s.conclusion.fact.mark := by
  cases hs : pureFlow s with
  | false =>
    have same : normalizeSummary s = s := by
      simp only [normalizeSummary, hs, Bool.false_eq_true, if_false]
    rw [same]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  | true =>
    have same : normalizeSummary s =
        ⟨normalizeFlowEndpoint s.initial, normalizeFlowEndpoint s.conclusion, s.demand⟩ := by
      simp only [normalizeSummary, hs, if_true]
    rw [same]
    exact ⟨rfl, (endpoint_fields_unchanged _).2.1, (endpoint_fields_unchanged _).2.1,
      (endpoint_fields_unchanged _).2.2.2.1, (endpoint_fields_unchanged _).2.2.2.1,
      (endpoint_fields_unchanged _).2.2.1, (endpoint_fields_unchanged _).2.2.1⟩

/-! ## Normalized C5 entry image

For a pure-FLOW summary family, CanStoreFrom(Dc,J) means that some raw initial
emittable from Dc normalizes to J. The rawCanEmit predicate below is the
existing complete raw image test. It does not mean an actual arrived before.
There are at most two raw preimages: J itself and the same endpoint with
EXACT tail. Each candidate is verified by normalization; noncanonical raw
EXACT stored values and non-FLOW cases therefore cannot be mistaken for STAR.
-/

def exactTwin (p : Endpoint) : Endpoint := { p with fact := { p.fact with kind := .exact } }

theorem normalization_preimage_cases (raw stored : Endpoint)
    (h : normalizeFlowEndpoint raw = stored) : raw = stored ∨ raw = exactTwin stored := by
  cases raw with
  | mk fact e must => cases fact with
    | mk b path k mark =>
      cases mark <;> cases k
      all_goals first
        | exact Or.inl h
        | right; rw [← h]; rfl

def candidateFits (rawCanEmit : Endpoint → Bool) (stored raw : Endpoint) : Bool :=
  rawCanEmit raw && decide (normalizeFlowEndpoint raw = stored)

def imageWitness (rawCanEmit : Endpoint → Bool) (stored : Endpoint) : Option Endpoint :=
  if candidateFits rawCanEmit stored stored then some stored else
  if candidateFits rawCanEmit stored (exactTwin stored) then some (exactTwin stored) else none

def CanStoreFrom (rawCanEmit : Endpoint → Bool) (stored : Endpoint) : Prop :=
  ∃ raw, rawCanEmit raw = true ∧ normalizeFlowEndpoint raw = stored

theorem image_witness_sound (rawCanEmit : Endpoint → Bool) (stored raw : Endpoint)
    (h : imageWitness rawCanEmit stored = some raw) :
    rawCanEmit raw = true ∧ normalizeFlowEndpoint raw = stored := by
  unfold imageWitness at h
  split at h
  · rename_i found
    have same := Option.some.inj h
    rw [← same]
    obtain ⟨allowed, equal⟩ := (Bool.and_eq_true _ _).mp found
    exact ⟨allowed, of_decide_eq_true equal⟩
  · split at h
    · rename_i found
      have same := Option.some.inj h
      rw [← same]
      obtain ⟨allowed, equal⟩ := (Bool.and_eq_true _ _).mp found
      exact ⟨allowed, of_decide_eq_true equal⟩
    · cases h

theorem image_witness_complete (rawCanEmit : Endpoint → Bool) (stored : Endpoint)
    (possible : CanStoreFrom rawCanEmit stored) :
    ∃ raw, imageWitness rawCanEmit stored = some raw := by
  by_cases first : candidateFits rawCanEmit stored stored = true
  · exact ⟨stored, by simp only [imageWitness, first, if_true]⟩
  · obtain ⟨raw, allowed, equal⟩ := possible
    have fit : candidateFits rawCanEmit stored raw = true := by
      simp only [candidateFits, allowed, Bool.true_and]
      exact decide_eq_true equal
    cases normalization_preimage_cases raw stored equal with
    | inl same => exact False.elim (first (same ▸ fit))
    | inr same =>
      rw [same] at fit
      exact ⟨exactTwin stored, by simp only [imageWitness, if_neg first, fit, if_true]⟩

theorem normalized_c5_image_is_exact (rawCanEmit : Endpoint → Bool) (stored : Endpoint) :
    (∃ raw, imageWitness rawCanEmit stored = some raw) ↔ CanStoreFrom rawCanEmit stored := by
  constructor
  · rintro ⟨raw, h⟩
    exact ⟨raw, image_witness_sound rawCanEmit stored raw h⟩
  · exact image_witness_complete rawCanEmit stored

def ep (fact : PFact) : Endpoint := ⟨fact, Excl.empty, false⟩
def point (b : Base) (path : List Acc := []) : PFact := ⟨b, path, .exact, .star⟩
def star (b : Base) (path : List Acc := []) : PFact := ⟨b, path, .star Excl.empty, .star⟩
def xf (fact : PFact) (d : Bool := false) : XFact := ⟨⟨fact, d⟩, Excl.empty⟩

theorem raw_inside_is_not_the_normalized_image_guard :
    ApSpec.Handoff.insideB (star 1) (point 1) = false ∧
    imageWitness (fun raw => decide (raw = ep (point 1))) (ep (star 1)) =
      some (ep (point 1)) := by decide

/-! ## Helper record: normalization preserves the caller suffix -/

def rawHelper : Summary := ⟨ep (point 2), ep (point 1 [7]), false⟩
def storedHelper : Summary := normalizeSummary rawHelper
def helperReadView : MicroEdge := revEdge storedHelper.initial.fact storedHelper.conclusion.fact
def callerField : XFact := xf (star 1 [7])

theorem normalized_helper_replay_is_correlated :
    storedHelper = ⟨ep (star 2), ep (star 1 [7]), false⟩ ∧
    helperReadView = (star 1 [7], star 2) ∧
    (bindX callerField helperReadView).facts = [xf (star 2)] ∧
    (bindX (xf ⟨1, [7,8], .exact, .conc 1⟩) helperReadView).facts =
      [xf ⟨2, [8], .exact, .conc 1⟩] := by decide

theorem mixed_demand_keeps_any_and_layer :
    normalizeSummary ⟨ep (point 2), ep ⟨1, [7], .any, .star⟩, true⟩ =
      ⟨ep (star 2), ep ⟨1, [7], .any, .star⟩, true⟩ := by decide

/-! ## Write counterexample: no global normality theorem is assumed -/

def overwritten : Excl := .set [7]
def writeKeep : MicroEdge :=
  (⟨1, [], .star overwritten, .star⟩, ⟨1, [], .star overwritten, .star⟩)
def returnEdge : MicroEdge := (star 1, star 2)
def rawWriteResults : List XFact :=
  ((bindX (xf (point 1)) writeKeep).facts).flatMap fun x => (bindX x returnEdge).facts
def rawWriteSummary : Summary := ⟨ep (point 1), ep (point 2), false⟩
def normalizedWriteSummary : Summary := normalizeSummary rawWriteSummary
def inputField : Loc := ⟨1, [7], 1⟩
def outputField : Loc := ⟨2, [7], 1⟩

theorem current_exact_survives_child_overwrite_normal :
    rawWriteResults = [xf (point 2)] ∧
    normalizedWriteSummary = ⟨ep (star 1), ep (star 2), false⟩ ∧
    (bindX (xf ⟨1, [7], .exact, .conc 1⟩) writeKeep).facts = [] := by decide

theorem write_normalization_adds_a_false_normal_pair :
    den normalizedWriteSummary.initial.fact normalizedWriteSummary.conclusion.fact
      inputField outputField ∧
    ¬ ∃ mid, den writeKeep.1 writeKeep.2 inputField mid ∧
      den returnEdge.1 returnEdge.2 mid outputField := by
  constructor
  · exact ⟨rfl,rfl,True.intro,rfl,True.intro,[7],[7],rfl,rfl,rfl,rfl,rfl⟩
  · rintro ⟨mid, ⟨_,_,_,_,_,suffix,_,hs,_,hi,_⟩,_⟩
    have same : suffix = [7] := by simpa [inputField, writeKeep] using hs.symm
    rw [same] at hi
    cases hi

/-! ## Proposed EXACT/FLOW write annotation

This is a new annotation cell, not `AnyTaintEx.normX`. Current `normX` drops
E from EXACT/FLOW. The new cell retains the spatial EXACT tail for reads,
but records the exclusion needed when the summary tail becomes STAR.
The example concerns an immediate-child write below this exact root.
Other transfer cells are outside this executable scalar certificate.
-/

structure AnnotatedResult where
  endpoint : Endpoint
  demand : Bool
deriving DecidableEq, Repr

def writeExactFlowAnnotation (child : Acc) (x : AnnotatedResult) : AnnotatedResult :=
  if abstractMark x.endpoint.fact.mark then
    match x.endpoint.fact.kind with
    | .exact => { x with endpoint := { x.endpoint with
        exclusion := Excl.union x.endpoint.exclusion (.set [child]) } }
    | _ => x
  else x

/-- A root-to-root move transports this new annotation. In particular, a
return must not call the historical non-MUST annotation normalizer. -/
def moveRoot (target : Base) (x : AnnotatedResult) : AnnotatedResult :=
  { x with endpoint := { x.endpoint with fact := { x.endpoint.fact with base := target } } }

def stripTailE : Kind → Kind
  | .star _ => .star Excl.empty
  | k => k

def clearEndpointE (p : Endpoint) : Endpoint :=
  { p with fact := { p.fact with kind := stripTailE p.fact.kind }, exclusion := Excl.empty }

/-- The selected run-1 cover rule: an exclusion update is a DEMAND effect.
It clears E. Later runs retain the NORMAL exclusion annotation. -/
def publishAnnotation (run1 : Bool) (x : AnnotatedResult) : AnnotatedResult :=
  if run1 && !x.endpoint.exclusion.isEmptyB then
    ⟨clearEndpointE x.endpoint, true⟩
  else x

def annotatedStart : AnnotatedResult := ⟨ep (point 1), false⟩
def annotatedWritten : AnnotatedResult := writeExactFlowAnnotation 7 annotatedStart
def annotatedReturned : AnnotatedResult := moveRoot 2 annotatedWritten
def annotatedWriteSummary : Summary :=
  ⟨annotatedStart.endpoint, annotatedReturned.endpoint, annotatedReturned.demand⟩
def storedAnnotatedWrite : Summary := normalizeSummary annotatedWriteSummary

theorem annotation_is_new_and_survives_return :
    annotatedWritten = ⟨⟨point 1, overwritten, false⟩, false⟩ ∧
    annotatedReturned = ⟨⟨point 2, overwritten, false⟩, false⟩ ∧
    normX ⟨⟨point 1, false⟩, overwritten⟩ = xf (point 1) ∧
    storedAnnotatedWrite =
      ⟨ep (star 1), ⟨⟨2, [], .star overwritten, .star⟩, overwritten, false⟩, false⟩ := by decide

theorem move_keeps_new_annotation (target : Base) (x : AnnotatedResult) :
    (moveRoot target x).endpoint.exclusion = x.endpoint.exclusion ∧
    (moveRoot target x).endpoint.fact.kind = x.endpoint.fact.kind ∧
    (moveRoot target x).demand = x.demand := ⟨rfl,rfl,rfl⟩

theorem later_publication_keeps_normal_exclusion_but_run1_demotes :
    publishAnnotation false annotatedReturned = annotatedReturned ∧
    publishAnnotation true annotatedReturned = ⟨ep (point 2), true⟩ ∧
    normalizeSummary ⟨annotatedStart.endpoint,
      (publishAnnotation true annotatedReturned).endpoint,
      (publishAnnotation true annotatedReturned).demand⟩ =
      ⟨ep (star 1), ep (star 2), true⟩ := by decide

theorem annotated_normalization_rejects_overwritten_field :
    ¬ den storedAnnotatedWrite.initial.fact storedAnnotatedWrite.conclusion.fact
        inputField outputField := by
  rintro ⟨_,_,_,_,_,suffix,_,hs,_,_,_,admitted⟩
  have same : suffix = [7] := by simpa [inputField,storedAnnotatedWrite,
    annotatedWriteSummary,annotatedReturned,annotatedWritten,annotatedStart,
    normalizeSummary,pureFlow,normalizeFlowEndpoint,abstractMark,moveRoot,
    writeExactFlowAnnotation,ep,point,star,Excl.union,Excl.empty] using hs.symm
  rw [same] at admitted
  cases admitted

def disjointInput : Loc := ⟨1, [8], 1⟩
def disjointOutput : Loc := ⟨2, [8], 1⟩

theorem annotated_normalization_keeps_disjoint_field :
    den storedAnnotatedWrite.initial.fact storedAnnotatedWrite.conclusion.fact
      disjointInput disjointOutput :=
  ⟨rfl,rfl,True.intro,rfl,True.intro,[8],[8],rfl,rfl,rfl,rfl,rfl⟩

/-- A complete relation check for this scalar write-and-return cell. The new
NORMAL STAR result is exactly the ordinary excluded keep edge followed by
the ordinary return. This is stronger than the two sample fields above. -/
theorem annotated_write_cell_has_exact_survivor_relation (input output : Loc) :
    den storedAnnotatedWrite.initial.fact storedAnnotatedWrite.conclusion.fact input output ↔
    ∃ middle, den writeKeep.1 writeKeep.2 input middle ∧
      den returnEdge.1 returnEdge.2 middle output := by
  change den (star 1) ⟨2, [], .star overwritten, .star⟩ input output ↔ _
  constructor
  · rintro ⟨ib,ob,im,om,pass,suffix,outSuffix,ip,op,_,same,admitted⟩
    have emptyAllows : Excl.empty.admits suffix = true := by cases suffix <;> rfl
    refine ⟨⟨1, suffix, input.mark⟩, ?_, ?_⟩
    · exact ⟨ib,rfl,im,rfl,True.intro,suffix,suffix,ip,rfl,admitted,rfl,admitted⟩
    · exact ⟨rfl,ob,True.intro,om,pass,suffix,outSuffix,rfl,op,emptyAllows,same,emptyAllows⟩
  · rintro ⟨middle,
      ⟨ib,mb,im,mm,_,suffix,midSuffix,ip,mp,admitted,midSame,_⟩,
      ⟨_,ob,_,om,pass,midSuffix2,outSuffix,mp2,op,_,same,_⟩⟩
    have midSame2 : midSuffix2 = suffix := by
      have first : middle.path = suffix := by simpa [writeKeep,midSame] using mp
      have second : middle.path = midSuffix2 := by simpa [returnEdge,star] using mp2
      exact second.symm.trans first
    have emptyAllows : Excl.empty.admits suffix = true := by cases suffix <;> rfl
    refine ⟨ib,ob,im,?_,pass,suffix,outSuffix,ip,op,emptyAllows,?_,admitted⟩
    · exact om.trans mm
    · exact same.trans midSame2

/-! ## Historical rejected BELOW-cleaner alternative

The new raw EXACT/FLOW tail is a field-read barrier. It is not a claim that
an effect can ignore every nonempty suffix. Cleaner geometry uses the
corresponding STAR/E fact. The result keeps the original EXACT read barrier.
The controls in this section check RemoveAllMarksBelow at the same root.
The final contract below rejects that all-marks cleaner. These controls do
not authorize such a cleaner and are not an active runtime proposal. The
effect-view helper is used below only after the final admission check.
No generic cleaner simulation is asserted. Concrete-mark cleaner geometry
and result tails are unchanged.

Raw initial EXACT/FLOW has Empty E. Only a derived conclusion can acquire
the write annotation. The new annotation must not be manufactured on the
raw initial when the conclusion is normalized for storage.
-/

def cleanerGeometry (p : Endpoint) : Endpoint := normalizeFlowEndpoint p

def restoreReadBarrier (original : Endpoint) (result : XFact) : AnnotatedResult :=
  let fact :=
    if abstractMark original.fact.mark then
      match original.fact.kind with
      | .exact => { result.af.fact with kind := .exact }
      | _ => result.af.fact
    else result.af.fact
  ⟨⟨fact, result.ex, original.must⟩, result.af.demand⟩

def guardedCleaner (cleaner : Cleaner) (x : AnnotatedResult) : List AnnotatedResult :=
  let geometry := cleanerGeometry x.endpoint
  let results := cleanResX cleaner ⟨⟨geometry.fact, x.demand⟩, geometry.exclusion⟩
  results.facts.map (restoreReadBarrier x.endpoint)

def allBelowRoot : Cleaner := ⟨1, [], .below, none⟩
def guardedBelowResults : List AnnotatedResult := guardedCleaner allBelowRoot annotatedStart
def guardedBelowSummaries : List Summary := guardedBelowResults.map fun result =>
  normalizeSummary ⟨annotatedStart.endpoint, result.endpoint, result.demand⟩

theorem raw_initial_exact_has_empty_E :
    annotatedStart.endpoint.fact.kind = .exact ∧
    annotatedStart.endpoint.exclusion = Excl.empty := ⟨rfl,rfl⟩

theorem literal_exact_cleaner_is_disjoint_but_effect_geometry_is_partial :
    cleanPos allBelowRoot (point 1) = .disjoint ∧
    (cleanResX allBelowRoot (xf (point 1))).facts = [xf (point 1)] ∧
    cleanPos allBelowRoot (cleanerGeometry annotatedStart.endpoint).fact = .part ∧
    (cleanResX allBelowRoot (xf (star 1))).facts =
      [xf ⟨1, [], .any, .star⟩ true] := by decide

theorem guarded_all_below_retains_read_tail_and_demotes :
    guardedBelowResults = [⟨ep (point 1), true⟩] ∧
    guardedBelowSummaries = [⟨ep (star 1), ep (star 1), true⟩] ∧
    guardedBelowSummaries.all (fun summary => summary.demand) = true := by decide

theorem cleaner_geometry_does_not_change_concrete (p : Endpoint) (mark : Mark)
    (concrete : p.fact.mark = .conc mark) : cleanerGeometry p = p := by
  simp only [cleanerGeometry,normalizeFlowEndpoint,concrete,abstractMark,
    Bool.false_eq_true,if_false]

theorem concrete_cleaner_cell_is_unchanged :
    guardedCleaner allBelowRoot ⟨ep ⟨1, [], .exact, .conc 1⟩, false⟩ =
      [⟨ep ⟨1, [], .exact, .conc 1⟩, false⟩] ∧
    (cleanResX allBelowRoot (xf ⟨1, [], .exact, .conc 1⟩)).facts =
      [xf ⟨1, [], .exact, .conc 1⟩] := by decide

/-! ## Selected whole-position RemoveAll admission

RemoveAllMarks is legal at any named position, including p.f. It must clean
that position and all its descendants. Only partial reach is rejected:
EXACT and BELOW are invalid when `mark = none`. A selected-mark cleaner
keeps its previous reach choices. The active wrapper first validates the
cleaner; the rejected historical BELOW controls cannot enter this path.

This section checks the root and named-field cells. For a newly introduced
EXACT/FLOW barrier above a field cleaner, the direct scalar effect view is
conservative ANY/DEMAND. A DEMAND residual keeps that ANY tail: restoring
EXACT here would create a forbidden later STAR/FLOW demand at storage.
The proposed JIR read/clean/write path can instead record the precise write
exclusion, as the write cell above demonstrates.
There is no whole-analyzer cleaner theorem here.
-/

def admittedCleaner (cleaner : Cleaner) : Bool :=
  match cleaner.mark with
  | some _ => true
  | none => match cleaner.reach with
    | .atAndBelow => true
    | .exact | .below => false

def restoreActiveReadBarrier (original : Endpoint) (result : XFact) : AnnotatedResult :=
  if result.af.demand then
    if abstractMark original.fact.mark && abstractMark result.af.fact.mark &&
        result.af.fact.kind.isAny then
      ⟨⟨result.af.fact,Excl.empty,false⟩,true⟩
    else ⟨⟨result.af.fact,result.ex,original.must⟩,true⟩
  else restoreReadBarrier original result

def activeCleaner (cleaner : Cleaner) (x : AnnotatedResult) :
    Option (List AnnotatedResult) :=
  if admittedCleaner cleaner then
    let geometry := cleanerGeometry x.endpoint
    let results := cleanResX cleaner ⟨⟨geometry.fact,x.demand⟩,geometry.exclusion⟩
    some (results.facts.map (restoreActiveReadBarrier x.endpoint))
  else none

def allAtRoot : Cleaner := ⟨1, [], .atAndBelow, none⟩
def allAtField : Cleaner := ⟨1, [7], .atAndBelow, none⟩
def flowMustRoot : AnnotatedResult := ⟨⟨⟨1, [], .any, .star⟩, Excl.empty, true⟩, false⟩
def concreteMustRoot : AnnotatedResult := ⟨⟨⟨1, [], .any, .conc 1⟩, Excl.empty, true⟩, false⟩
def concreteRoot : AnnotatedResult := ⟨ep ⟨1, [], .exact, .conc 1⟩, false⟩

theorem remove_all_admission_is_independent_of_named_path
    (base : Base) (path : List Acc) :
    admittedCleaner ⟨base, path, .atAndBelow, none⟩ = true ∧
    admittedCleaner ⟨base, path, .exact, none⟩ = false ∧
    admittedCleaner ⟨base, path, .below, none⟩ = false := ⟨rfl,rfl,rfl⟩

theorem selected_mark_reach_is_not_restricted
    (base : Base) (path : List Acc) (reach : CleanReach) (mark : Mark) :
    admittedCleaner ⟨base,path,reach,some mark⟩ = true := rfl

theorem rejected_below_cleaner_cannot_create_MUST_root_survivor :
    activeCleaner allBelowRoot annotatedStart = none ∧
    activeCleaner allBelowRoot flowMustRoot = none ∧
    activeCleaner allBelowRoot concreteMustRoot = none ∧
    activeCleaner ⟨1,[],.exact,none⟩ flowMustRoot = none := by decide

theorem whole_position_root_cleaner_kills_FLOW_MUST_and_concrete :
    activeCleaner allAtRoot annotatedStart = some [] ∧
    activeCleaner allAtRoot flowMustRoot = some [] ∧
    activeCleaner allAtRoot concreteMustRoot = some [] ∧
    activeCleaner allAtRoot concreteRoot = some [] := by decide

theorem whole_position_named_field_is_admitted_and_cleans_its_subtree :
    admittedCleaner allAtField = true ∧
    activeCleaner allAtField ⟨ep (point 1 [7]),false⟩ = some [] ∧
    activeCleaner allAtField ⟨ep (point 1 [7,8]),false⟩ = some [] ∧
    activeCleaner allAtField ⟨ep ⟨1,[7],.exact,.conc 1⟩,false⟩ = some [] ∧
    activeCleaner allAtField ⟨ep ⟨1,[7,8],.exact,.conc 1⟩,false⟩ = some [] ∧
    activeCleaner allAtField ⟨ep (point 1 [8]),false⟩ =
      some [⟨ep (point 1 [8]),false⟩] ∧
    activeCleaner allAtField ⟨ep ⟨1,[8],.exact,.conc 1⟩,false⟩ =
      some [⟨ep ⟨1,[8],.exact,.conc 1⟩,false⟩] := by decide

theorem direct_ancestor_field_effect_does_not_create_NORMAL_EmptyE :
    activeCleaner allAtField annotatedStart =
      some [⟨ep ⟨1,[],.any,.star⟩,true⟩] := by decide

theorem partial_DEMAND_keeps_ANY_but_NORMAL_keeps_the_read_barrier :
    restoreActiveReadBarrier annotatedStart.endpoint (xf ⟨1,[],.any,.star⟩ true) =
      ⟨ep ⟨1,[],.any,.star⟩,true⟩ ∧
    restoreActiveReadBarrier annotatedStart.endpoint
      ⟨⟨⟨1,[],.star overwritten,.star⟩,false⟩,overwritten⟩ =
      ⟨⟨point 1,overwritten,false⟩,false⟩ := by decide

/-- A partial pure-FLOW effect is MAY, even if its incoming query was
uniform/MUST. Keep normal MUST and concrete uniform transport unchanged. -/
theorem partial_FLOW_MUST_cleaner_loses_uniformity_without_changing_other_MUST_transport :
    activeCleaner allAtField flowMustRoot =
      some [⟨ep ⟨1,[],.any,.star⟩,true⟩] ∧
    restoreActiveReadBarrier flowMustRoot.endpoint (xf ⟨1,[],.any,.star⟩ false) =
      flowMustRoot ∧
    restoreActiveReadBarrier concreteMustRoot.endpoint
      (xf ⟨1,[],.any,.conc 1⟩ true) =
      ⟨concreteMustRoot.endpoint,true⟩ := by decide

/-! ## Focused boundary integration contracts

These are scalar integration laws, not a proof of the analyzer driver.
The raw admission predicate is supplied by the selected emitter; the
independent containment predicate is checked on the same raw preimage.
No emitter-history or global observation-coverage assumption is introduced.
-/

namespace Integration

/-- Output grammar selected for completed runs. FLOW DEMAND STAR is legal
only as run-1 output. Later FLOW DEMAND is MAY/ANY. This is an output/next-Dc
contract; it does not forbid STAR at the exit Dp of a demand pair. -/
def validOutgoingFlowDemand (run : Nat) (summary : Summary) : Bool :=
  !pureFlow summary || !summary.demand || Nat.beq run 1 ||
    (summary.conclusion.fact.kind.isAny && !summary.conclusion.must)

theorem outgoing_grammar_allows_run1_STAR_but_rejects_it_afterwards :
    validOutgoingFlowDemand 1 ⟨ep (star 1),ep (star 2),true⟩ = true ∧
    validOutgoingFlowDemand 2 ⟨ep (star 1),ep (star 2),true⟩ = false ∧
    validOutgoingFlowDemand 3 ⟨ep (star 1),ep (star 2),true⟩ = false := by decide

theorem admitted_partial_cleaner_produces_valid_later_ANY_demand (run : Nat) :
    validOutgoingFlowDemand run
      (normalizeSummary ⟨ep (point 1),ep ⟨1,[],.any,.star⟩,true⟩) = true := by
  change (Nat.beq run 1 || true) = true
  simp only [Bool.or_true]

theorem late_FLOW_MUST_demand_is_not_a_MAY_output :
    validOutgoingFlowDemand 2 ⟨ep (star 1),flowMustRoot.endpoint,true⟩ = false ∧
    validOutgoingFlowDemand 2 ⟨ep (star 1),ep ⟨1,[],.any,.star⟩,true⟩ = true := by decide

theorem normal_E_write_and_run1_cover_have_selected_output_shapes :
    validOutgoingFlowDemand 2 storedAnnotatedWrite = true ∧
    validOutgoingFlowDemand 1
      (normalizeSummary ⟨annotatedStart.endpoint,
        (publishAnnotation true annotatedReturned).endpoint,true⟩) = true ∧
    normalizeSummary ⟨ep (point 1),ep ⟨1,[],.any,.star⟩,true⟩ =
      ⟨ep (star 1),ep ⟨1,[],.any,.star⟩,true⟩ := by decide

def rawAdmissible (canEmit insideDemand : Endpoint → Bool) (raw : Endpoint) : Bool :=
  canEmit raw && insideDemand raw

def c5EntryWitness (canEmit insideDemand : Endpoint → Bool) (stored : Endpoint) :
    Option Endpoint := imageWitness (rawAdmissible canEmit insideDemand) stored

theorem normalized_entry_witness_checks_emission_and_raw_containment
    (canEmit insideDemand : Endpoint → Bool) (stored raw : Endpoint)
    (found : c5EntryWitness canEmit insideDemand stored = some raw) :
    canEmit raw = true ∧ insideDemand raw = true ∧ normalizeFlowEndpoint raw = stored := by
  obtain ⟨admitted, normalized⟩ :=
    image_witness_sound (rawAdmissible canEmit insideDemand) stored raw found
  obtain ⟨emitted, contained⟩ := (Bool.and_eq_true _ _).mp admitted
  exact ⟨emitted,contained,normalized⟩

theorem normalized_entry_witness_is_complete
    (canEmit insideDemand : Endpoint → Bool) (stored : Endpoint) :
    (∃ raw, c5EntryWitness canEmit insideDemand stored = some raw) ↔
    ∃ raw, canEmit raw = true ∧ insideDemand raw = true ∧
      normalizeFlowEndpoint raw = stored := by
  constructor
  · rintro ⟨raw,found⟩
    exact ⟨raw,normalized_entry_witness_checks_emission_and_raw_containment
      canEmit insideDemand stored raw found⟩
  · rintro ⟨raw,emitted,contained,normalized⟩
    apply image_witness_complete
    exact ⟨raw,by simp only [rawAdmissible,emitted,contained,Bool.true_and],normalized⟩

def joinLayer (summary : Summary) (additionalDemand : Bool) : Summary :=
  { summary with demand := summary.demand || additionalDemand }

theorem normalization_commutes_with_layer_join (summary : Summary) (additionalDemand : Bool) :
    normalizeSummary (joinLayer summary additionalDemand) =
      joinLayer (normalizeSummary summary) additionalDemand := by
  have sameFlow : pureFlow (joinLayer summary additionalDemand) = pureFlow summary := rfl
  unfold normalizeSummary
  rw [sameFlow]
  cases h : pureFlow summary <;> rfl

theorem boundary_never_promotes_DEMAND (summary : Summary) :
    (normalizeSummary (joinLayer summary true)).demand = true ∧
    (normalizeSummary (joinLayer {summary with demand := true} false)).demand = true := by
  constructor
  · rw [(summary_layer_and_endpoint_data_unchanged _).1]
    simp only [joinLayer,Bool.or_true]
  · rw [(summary_layer_and_endpoint_data_unchanged _).1]
    rfl

/-! ### Nested overwrite residuals

For p.f.g = clean, the old value outside f has the normal residual /{f}.
The affected f subtree has a proper-prefix DEMAND residual. This second
piece must not disappear merely because the point query has an EXACT read
barrier. It uses the existing STAR effect geometry and proper-prefix row.
An inner write cannot be summarized only by the normal outer /{f} piece.
-/

def innerOverwritten : Excl := .set [8]
def nestedKeep : MicroEdge :=
  (⟨1,[7],.star innerOverwritten,.star⟩,⟨1,[7],.star innerOverwritten,.star⟩)
def nestedDemand : PFact := ⟨1,[7],.any,.star⟩

theorem nested_write_uses_effect_geometry_and_keeps_proper_prefix_DEMAND :
    (bindX (xf (point 1)) nestedKeep).facts = [] ∧
    (bindX (xf (star 1)) nestedKeep).facts = [xf nestedDemand true] ∧
    (bindX (xf ⟨1,[7,9],.exact,.conc 1⟩) nestedKeep).facts =
      [xf ⟨1,[7,9],.exact,.conc 1⟩] ∧
    (bindX (xf ⟨1,[7,8],.exact,.conc 1⟩) nestedKeep).facts = [] := by decide

theorem nested_write_normal_piece_keeps_sibling_but_needs_inner_DEMAND :
    den storedAnnotatedWrite.initial.fact storedAnnotatedWrite.conclusion.fact
      ⟨1,[9],1⟩ ⟨2,[9],1⟩ ∧
    ¬ den storedAnnotatedWrite.initial.fact storedAnnotatedWrite.conclusion.fact
      ⟨1,[7,9],1⟩ ⟨2,[7,9],1⟩ ∧
    den (star 1) ⟨2,[7],.any,.star⟩ ⟨1,[7,9],1⟩ ⟨2,[7,9],1⟩ := by
  constructor
  · exact ⟨rfl,rfl,True.intro,rfl,True.intro,[9],[9],rfl,rfl,rfl,rfl,rfl⟩
  constructor
  · rintro ⟨_,_,_,_,_,suffix,_,path,_,_,_,allowed⟩
    have same : suffix = [7,9] := by simpa [storedAnnotatedWrite,
      annotatedWriteSummary,annotatedReturned,annotatedWritten,annotatedStart,
      normalizeSummary,pureFlow,normalizeFlowEndpoint,abstractMark,moveRoot,
      writeExactFlowAnnotation,ep,point,star,Excl.union,Excl.empty] using path.symm
    rw [same] at allowed
    cases allowed
  · exact ⟨rfl,rfl,True.intro,rfl,True.intro,[7,9],[9],rfl,rfl,rfl,True.intro⟩

/-- A first-accessor exclusion belongs to its owning prefix. A valid descent
from a MUST value consumes the ancestor mask. Copying /{f} onto g would
incorrectly exclude the unrelated child g.f. -/
theorem admitted_MUST_descent_consumes_ancestor_E :
    (bindX ⟨⟨⟨1,[],.any,.conc 1⟩,false⟩,overwritten⟩
      (star 1 [9],star 2)).facts = [xf ⟨2,[],.any,.conc 1⟩] ∧
    (bindX ⟨⟨⟨1,[],.any,.conc 1⟩,false⟩,overwritten⟩
      (star 1 [7],star 2)).facts = [] := by decide

/-! ### Same-prefix C5 EXACT selection retains latent write E

The old scalar meet drops E when it selects an EXACT piece from MUST.
For a new FLOW piece, that E is still needed after boundary normalization.
The selected same-prefix cell retains it; an admitted descent is separate.
-/

def selectExactFlowPiece (source : Endpoint) : Endpoint :=
  { source with fact := { source.fact with kind := .exact }, must := false }

def oldSelectExactDroppingE (source : Endpoint) : Endpoint :=
  { selectExactFlowPiece source with exclusion := Excl.empty }

def mustFlowResult : Endpoint := ⟨⟨2,[],.any,.star⟩,overwritten,true⟩
def mustFlowInitial : Endpoint := ⟨⟨1,[],.any,.star⟩,Excl.empty,true⟩
def oldSelectedSummary : Summary :=
  normalizeSummary ⟨mustFlowInitial,oldSelectExactDroppingE mustFlowResult,false⟩
def selectedSummary : Summary :=
  normalizeSummary ⟨mustFlowInitial,selectExactFlowPiece mustFlowResult,false⟩

theorem same_prefix_exact_piece_keeps_E_before_and_after_normalization :
    (selectExactFlowPiece mustFlowResult).fact = point 2 ∧
    (selectExactFlowPiece mustFlowResult).exclusion = overwritten ∧
    selectedSummary.conclusion.fact = ⟨2,[],.star overwritten,.star⟩ ∧
    selectedSummary.conclusion.exclusion = overwritten ∧
    selectedSummary.demand = false := by decide

theorem dropping_C5_E_adds_false_overwritten_pair_but_retaining_E_blocks_it :
    den oldSelectedSummary.initial.fact oldSelectedSummary.conclusion.fact
      inputField outputField ∧
    ¬ den selectedSummary.initial.fact selectedSummary.conclusion.fact
      inputField outputField ∧
    den selectedSummary.initial.fact selectedSummary.conclusion.fact
      disjointInput disjointOutput := by
  constructor
  · exact ⟨rfl,rfl,True.intro,rfl,True.intro,[7],[7],rfl,rfl,True.intro,rfl,rfl⟩
  constructor
  · rintro ⟨_,_,_,_,_,suffix,_,path,_,_,_,allowed⟩
    have same : suffix = [7] := by
      change [7] = suffix at path
      exact path.symm
    rw [same] at allowed
    cases allowed
  · exact ⟨rfl,rfl,True.intro,rfl,True.intro,[8],[8],rfl,rfl,True.intro,rfl,rfl⟩

/-- A canonical STAR/E piece selected from a same-prefix uniform/MUST result
is contained in that original ANY-tail relation, with both own exclusions
retained. The application-side definite-MUST requirement remains separate.
This theorem does not justify generalizing an arbitrary literal EXACT pair.
-/
theorem canonical_C5_piece_is_covered_by_same_prefix_uniform_result
    (initial : PFact) (initialE finalE : Excl) (base : Base)
    (path : List Acc) (mark : MarkA) (input output : Loc)
    (covered : denX initial initialE ⟨base,path,.star finalE,mark⟩ finalE input output) :
    denX initial initialE ⟨base,path,.any,mark⟩ finalE input output := by
  obtain ⟨ib,ob,im,om,pass,suffix,outSuffix,ip,op,initialTail,_,initialAdmits,finalAdmits⟩ := covered
  exact ⟨ib,ob,im,om,pass,suffix,outSuffix,ip,op,initialTail,True.intro,
    initialAdmits,finalAdmits⟩

def check : Bool :=
  (bindX (xf (star 1)) nestedKeep).facts == [xf nestedDemand true] &&
  selectedSummary.conclusion.fact == ⟨2,[],.star overwritten,.star⟩ &&
  (normalizeSummary (joinLayer rawHelper true)).demand

theorem checked : check = true := by decide

#eval check
#print axioms outgoing_grammar_allows_run1_STAR_but_rejects_it_afterwards
#print axioms admitted_partial_cleaner_produces_valid_later_ANY_demand
#print axioms late_FLOW_MUST_demand_is_not_a_MAY_output
#print axioms normal_E_write_and_run1_cover_have_selected_output_shapes
#print axioms normalized_entry_witness_checks_emission_and_raw_containment
#print axioms normalized_entry_witness_is_complete
#print axioms normalization_commutes_with_layer_join
#print axioms boundary_never_promotes_DEMAND
#print axioms nested_write_uses_effect_geometry_and_keeps_proper_prefix_DEMAND
#print axioms nested_write_normal_piece_keeps_sibling_but_needs_inner_DEMAND
#print axioms admitted_MUST_descent_consumes_ancestor_E
#print axioms same_prefix_exact_piece_keeps_E_before_and_after_normalization
#print axioms dropping_C5_E_adds_false_overwritten_pair_but_retaining_E_blocks_it
#print axioms canonical_C5_piece_is_covered_by_same_prefix_uniform_result
#print axioms checked

end Integration

/-! ## Transient native MUST read views

A canonical pure-FLOW native record with a MUST endpoint needs an
opposite-direction read view. The view is transient, not a new persistent
record or a backward MUST initial. Its premise is result.STAR/Eg and its
conclusion is source.ANY/FLOW, DEMAND, Empty E. Source Ep is deliberately
forgotten on the uncorrelated ANY output. Result Eg stays on the read premise.

This certificate covers the transpose of the concrete pair relation. It
does not turn DEMAND into a confirmation and does not prove global native
record availability. Only plain FLOW marks are selected (no mark exclusion).
-/

namespace NativeMustView

def plainFlow : MarkA → Bool
  | .star => true
  | _ => false

def transientView (native : Summary) : Summary :=
  ⟨⟨⟨native.conclusion.fact.base,native.conclusion.fact.path,
        .star native.conclusion.exclusion,.star⟩,native.conclusion.exclusion,false⟩,
    ⟨⟨native.initial.fact.base,native.initial.fact.path,.any,.star⟩,Excl.empty,false⟩,
    true⟩

def selectedView (native : Summary) : Option Summary :=
  if !native.demand && plainFlow native.initial.fact.mark &&
      plainFlow native.conclusion.fact.mark && (native.initial.must || native.conclusion.must)
  then some (transientView native) else none

theorem view_has_no_MUST_initial_and_is_always_DEMAND (native : Summary) :
    (transientView native).initial.fact.kind = .star native.conclusion.exclusion ∧
    (transientView native).initial.exclusion = native.conclusion.exclusion ∧
    (transientView native).initial.must = false ∧
    (transientView native).conclusion.fact.kind = .any ∧
    (transientView native).conclusion.exclusion = Excl.empty ∧
    (transientView native).conclusion.must = false ∧
    (transientView native).demand = true := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem view_preserves_opposite_bases_and_paths (native : Summary) :
    (transientView native).initial.fact.base = native.conclusion.fact.base ∧
    (transientView native).initial.fact.path = native.conclusion.fact.path ∧
    (transientView native).conclusion.fact.base = native.initial.fact.base ∧
    (transientView native).conclusion.fact.path = native.initial.fact.path := ⟨rfl,rfl,rfl,rfl⟩

/-- Executable inverse witness: use the forward output suffix as the view's
input suffix and the forward input suffix as its ANY output suffix. -/
theorem transient_view_covers_forward_transpose (native : Summary)
    (_initialFlow : native.initial.fact.mark = .star)
    (conclusionFlow : native.conclusion.fact.mark = .star)
    (source target : Loc)
    (pair : denX native.initial.fact native.initial.exclusion
      native.conclusion.fact native.conclusion.exclusion source target) :
    denX (transientView native).initial.fact (transientView native).initial.exclusion
      (transientView native).conclusion.fact (transientView native).conclusion.exclusion
      target source := by
  obtain ⟨sb,tb,_,marks,_,inputSuffix,outputSuffix,sp,tp,_,_,_,resultAdmits⟩ := pair
  have sameMark : target.mark = source.mark := by simpa only [conclusionFlow,MarkA.out] using marks
  have emptyAllows : Excl.empty.admits inputSuffix = true := by cases inputSuffix <;> rfl
  exact ⟨tb,sb,True.intro,sameMark.symm,True.intro,
    outputSuffix,inputSuffix,tp,sp,resultAdmits,True.intro,resultAdmits,emptyAllows⟩

theorem transient_view_is_already_canonical (native : Summary) :
    normalizeSummary (transientView native) = transientView native := rfl

def mustToStar (initialBase finalBase : Base) (initialPath finalPath : List Acc)
    (initialE finalE : Excl) : Summary :=
  ⟨⟨⟨initialBase,initialPath,.any,.star⟩,initialE,true⟩,
    ⟨⟨finalBase,finalPath,.star finalE,.star⟩,finalE,false⟩,false⟩

def mustToMust (initialBase finalBase : Base) (initialPath finalPath : List Acc)
    (initialE finalE : Excl) : Summary :=
  ⟨⟨⟨initialBase,initialPath,.any,.star⟩,initialE,true⟩,
    ⟨⟨finalBase,finalPath,.any,.star⟩,finalE,true⟩,false⟩

def starToMust (initialBase finalBase : Base) (initialPath finalPath : List Acc)
    (initialE finalE : Excl) : Summary :=
  ⟨⟨⟨initialBase,initialPath,.star initialE,.star⟩,initialE,false⟩,
    ⟨⟨finalBase,finalPath,.any,.star⟩,finalE,true⟩,false⟩

theorem all_three_normal_MUST_shapes_select_the_same_view (ib fb : Base)
    (ip fp : List Acc) (ie fe : Excl) :
    selectedView (mustToStar ib fb ip fp ie fe) =
      some (transientView (mustToStar ib fb ip fp ie fe)) ∧
    selectedView (mustToMust ib fb ip fp ie fe) =
      some (transientView (mustToStar ib fb ip fp ie fe)) ∧
    selectedView (starToMust ib fb ip fp ie fe) =
      some (transientView (mustToStar ib fb ip fp ie fe)) := ⟨rfl,rfl,rfl⟩

theorem concrete_record_is_not_selected (native : Summary) (mark : Mark)
    (concrete : native.initial.fact.mark = .conc mark) : selectedView native = none := by
  simp only [selectedView,concrete,plainFlow,Bool.and_false,Bool.false_and,
    Bool.false_eq_true,if_false]

theorem concrete_result_is_not_selected (native : Summary) (mark : Mark)
    (concrete : native.conclusion.fact.mark = .conc mark) : selectedView native = none := by
  simp only [selectedView,concrete,plainFlow,Bool.and_false,Bool.false_and,
    Bool.false_eq_true,if_false]

theorem DEMAND_record_cannot_create_a_NORMAL_view (native : Summary)
    (demand : native.demand = true) : selectedView native = none := by
  simp only [selectedView,demand,Bool.not_true,Bool.false_and,Bool.false_eq_true,if_false]

def check : Bool :=
  selectedView (mustToStar 1 2 [7] [8] (.set [9]) (.set [10])) ==
    some ⟨⟨⟨2,[8],.star (.set [10]),.star⟩,.set [10],false⟩,
      ⟨⟨1,[7],.any,.star⟩,Excl.empty,false⟩,true⟩

theorem checked : check = true := by decide

#eval check
#print axioms view_has_no_MUST_initial_and_is_always_DEMAND
#print axioms view_preserves_opposite_bases_and_paths
#print axioms transient_view_covers_forward_transpose
#print axioms transient_view_is_already_canonical
#print axioms all_three_normal_MUST_shapes_select_the_same_view
#print axioms concrete_record_is_not_selected
#print axioms concrete_result_is_not_selected
#print axioms DEMAND_record_cannot_create_a_NORMAL_view
#print axioms checked

end NativeMustView

def check : Bool :=
  storedHelper == ⟨ep (star 2), ep (star 1 [7]), false⟩ &&
  rawWriteResults == [xf (point 2)] &&
  storedAnnotatedWrite ==
    ⟨ep (star 1), ⟨⟨2, [], .star overwritten, .star⟩, overwritten, false⟩, false⟩ &&
  guardedBelowSummaries == [⟨ep (star 1), ep (star 1), true⟩] &&
  admittedCleaner allBelowRoot == false &&
  activeCleaner allAtRoot flowMustRoot == some [] &&
  admittedCleaner allAtField == true

theorem checked : check = true := by decide

#eval check
#print axioms endpoint_fields_unchanged
#print axioms endpoint_normalization_idempotent
#print axioms summary_normalization_idempotent
#print axioms summary_layer_and_endpoint_data_unchanged
#print axioms normalization_preimage_cases
#print axioms image_witness_sound
#print axioms image_witness_complete
#print axioms normalized_c5_image_is_exact
#print axioms raw_inside_is_not_the_normalized_image_guard
#print axioms normalized_helper_replay_is_correlated
#print axioms mixed_demand_keeps_any_and_layer
#print axioms current_exact_survives_child_overwrite_normal
#print axioms write_normalization_adds_a_false_normal_pair
#print axioms annotation_is_new_and_survives_return
#print axioms move_keeps_new_annotation
#print axioms later_publication_keeps_normal_exclusion_but_run1_demotes
#print axioms annotated_normalization_rejects_overwritten_field
#print axioms annotated_normalization_keeps_disjoint_field
#print axioms annotated_write_cell_has_exact_survivor_relation
#print axioms raw_initial_exact_has_empty_E
#print axioms literal_exact_cleaner_is_disjoint_but_effect_geometry_is_partial
#print axioms guarded_all_below_retains_read_tail_and_demotes
#print axioms cleaner_geometry_does_not_change_concrete
#print axioms concrete_cleaner_cell_is_unchanged
#print axioms remove_all_admission_is_independent_of_named_path
#print axioms selected_mark_reach_is_not_restricted
#print axioms rejected_below_cleaner_cannot_create_MUST_root_survivor
#print axioms whole_position_root_cleaner_kills_FLOW_MUST_and_concrete
#print axioms whole_position_named_field_is_admitted_and_cleans_its_subtree
#print axioms direct_ancestor_field_effect_does_not_create_NORMAL_EmptyE
#print axioms partial_DEMAND_keeps_ANY_but_NORMAL_keeps_the_read_barrier
#print axioms partial_FLOW_MUST_cleaner_loses_uniformity_without_changing_other_MUST_transport
#print axioms checked

end FlowSummaryNormalization
