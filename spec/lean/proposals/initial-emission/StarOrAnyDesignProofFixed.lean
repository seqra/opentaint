/-
STAR_OR_ANY investigation/draft adapter. It is decorated STAR, never MUST.
Default C2: retain STAR answer; only a rejected ANY demand tries a virtual MAY
view, gated by ORIGINAL STAR/E reachability. Other interpretations are explicit
comparison parameters, not additional selected admissions.

Ordinary scalar FULL/Empty-demand-E, counted fields; old scalar run/budget guards
are reused. The finite exact image covers the complete672tag ordinary actual
universe (two bases, paths<=2 over f/g, FLOW/T/U, legal tails/layers, decoration).
Current native static/GROUP/mx/full E and mutable-store adapters are OPEN.
Public summary/Target/paired-demand rows erase the marker. Archived scoped
intra-procedural point inputs retain it, even when replayed in a later run.
-/
import SelectedFullAdmissionProofFixed

namespace StarOrAnyDesign
open ApSpec
abbrev Input := MayInitialToStarAudit.Input
abbrev Mark := MayInitialToStarAudit.Mark
abbrev Layer := MayInitialToStarAudit.Layer
abbrev Mode := MayInitialToStarAudit.Mode
abbrev Demand := RestrictedInitialPolicy.Demand
abbrev OldTag := SelectedFullAdmission.ActualTag
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

inductive PlainHead where | exact | star | may | must
deriving DecidableEq, Repr
inductive Head where | plain (tail : PlainHead) | starOrAny
deriving DecidableEq, Repr
structure Pattern where
  base : Nat
  path : List Acc
  head : Head
  mark : Mark
  exclusion : List Acc := []
deriving DecidableEq, Repr
structure Fact where
  pattern : Pattern
  layer : Layer
  protection : Bool := false
deriving DecidableEq, Repr
structure Seed where
  pattern : Pattern
  layer : Layer
deriving DecidableEq, Repr

inductive C2Choice where | starThenMayForAny | mayOnly | unionViews
deriving DecidableEq, Repr

def opHead : Head → PlainHead | .plain h => h | .starOrAny => .star
def marked : Head → Bool | .starOrAny => true | _ => false
def plainOf (i : Input) : PlainHead :=
  if i.must then .must else match i.shape with | .exact => .exact | .star => .star | .any => .may

def scalar (p : Pattern) : Input :=
  let shape : RestrictedInitialPolicy.Shape :=
    match opHead p.head with | .exact => .exact | .star => .star | .may | .must => .any
  ⟨p.base,p.path,shape,p.mark,decide (opHead p.head = .must)⟩
def fromInput (i : Input) (e : List Acc := []) : Pattern := ⟨i.base,i.path,.plain (plainOf i),i.mark,e⟩
def erase (p : Pattern) : Pattern := {p with head := .plain (opHead p.head)}
def eraseFact (f : Fact) : Fact := {f with pattern := erase f.pattern}
def eraseSeed (s : Seed) : Seed := {s with pattern := erase s.pattern}

/-- A virtual MAY view must not walk into a field excluded by the original
STAR. Empty suffix is admitted. This is not an actual MAY/NORMAL data packet. -/
def originalReach (p : Pattern) (demandPath : List Acc) : Bool :=
  match dropPrefix p.path demandPath with
  | some (field :: _) => !decide (field ∈ p.exclusion)
  | _ => true

def provisionalFlowExactBlocked (d : Demand) (a : Input) : Bool :=
  RestrictedInitialPolicy.shapeEq d.shape .exact &&
    (match d.mark with | .flow => true | _ => false) &&
    RestrictedInitialPolicy.shapeEq a.shape .any && !a.must

/-- Current scalar cells with existing budget/direction/provisional FLOW guard.
Demand E is Empty. Actual known-step E is checked before either C2 view. -/
def oldCell (run : Nat) (mode : Mode) (d : Demand) (a : Pattern) : Option Pattern :=
  if decide (2 ≤ run ∧ d.path.length ≤ mode.fieldLimit ∧ a.path.length ≤ mode.fieldLimit) &&
      originalReach a d.path && !provisionalFlowExactBlocked d (scalar a) then
    let raw := if Nat.beq run 2 then RestrictedInitialPolicy.DemandStarPolicy.emit d (scalar a)
      else RestrictedInitialPolicy.emit d (scalar a)
    raw.bind fun i =>
      if MayInitialToStarAudit.directionLegal mode.direction i && decide (i.path.length ≤ mode.fieldLimit) then
        some (fromInput i (if i.must && decide (a.path = d.path) then a.exclusion else []))
      else none
  else none

/-- Mint only a formerly-MAY output. A STAR output inherits an input SOA
marker; an ordinary first-field STAR output never gains it. -/
def renderedHead (input : Head) (raw : PlainHead) : Head :=
  match raw with
  | .may => .starOrAny
  | .star => if marked input then .starOrAny else .plain .star
  | h => .plain h

def answer (input : Fact) (view raw : Pattern) : Seed :=
  let p := {raw with head := renderedHead input.pattern.head (opHead raw.head)}
  ⟨p,MayInitialToStarAudit.admissionLayer (scalar p) (scalar view) input.layer⟩
def starAnswer (run : Nat) (mode : Mode) (d : Demand) (a : Fact) : Option Seed :=
  (oldCell run mode d (erase a.pattern)).map (answer a (erase a.pattern))
def mayView (p : Pattern) : Pattern := {p with head := .plain .may,exclusion := []}
def mayAnswer (run : Nat) (mode : Mode) (d : Demand) (a : Fact) : Option Seed :=
  if marked a.pattern.head && originalReach a.pattern d.path then
    (oldCell run mode d (mayView a.pattern)).map (answer a (mayView a.pattern))
  else none

def combine (left right : Option Seed) : List Seed :=
  match left,right with
  | none,none => [] | some a,none => [a] | none,some b => [b]
  | some a,some b => if a = b then [a] else [a,b]

def c2 (choice : C2Choice) (run : Nat) (mode : Mode) (d : Demand) (a : Fact) : List Seed :=
  if !marked a.pattern.head then (starAnswer run mode d a).toList
  else match choice with
  | .mayOnly => (mayAnswer run mode d a).toList
  | .unionViews => combine (starAnswer run mode d a) (mayAnswer run mode d a)
  | .starThenMayForAny =>
      match starAnswer run mode d a with
      | some s => [s]
      | none => if RestrictedInitialPolicy.shapeEq d.shape .any then (mayAnswer run mode d a).toList else []

structure Tag where
  old : OldTag
  decorate : Bool
deriving DecidableEq, Repr

def materialize (tag : Tag) : Fact :=
  let old := SelectedFullAdmission.actualOf tag.old
  let p := fromInput old.fact
  ⟨{p with head := if tag.decorate && decide (opHead p.head = .star) then .starOrAny else p.head},old.layer,false⟩
def allTags : List Tag :=
  SelectedFullAdmission.allActualTags.flatMap fun old => [false,true].map fun flag => ⟨old,flag⟩
def rawImage (choice : C2Choice) (run : Nat) (mode : Mode) (d : Demand) : List Seed :=
  allTags.flatMap fun tag => c2 choice run mode d (materialize tag)
def canEmitRaw (choice : C2Choice) (run : Nat) (mode : Mode) (d : Demand) (seed : Seed) : Bool :=
  decide (seed ∈ rawImage choice run mode d)
def storedImage (choice : C2Choice) (run : Nat) (mode : Mode) (d : Demand) : List Seed :=
  (rawImage choice run mode d).map eraseSeed

/-- Operations keep STAR semantics and transport the decoration only along a
STAR-shaped result. Genuine EXACT/MAY/MUST results remove the marker. -/
def operationHead (input : Head) (output : PlainHead) : Head :=
  if decide (output = .star) && marked input then .starOrAny else .plain output

def applyStarSummary (entryBase resultBase : Nat) (entryPath resultPath : List Acc) (actual : Fact) : Option Fact :=
  if Nat.beq entryBase actual.pattern.base then
    (dropPrefix entryPath actual.pattern.path).map fun suffix =>
      { actual with
        pattern := { actual.pattern with
          base := resultBase
          path := resultPath ++ suffix
          head := operationHead actual.pattern.head (opHead actual.pattern.head) } }
  else none

inductive PublicPayload where
  | data (conclusion : Fact)
  | normalTarget (id : Nat)
  | demandTarget
  | pairedDemand (entry : Pattern) (exit : Option Pattern)
deriving DecidableEq, Repr
structure PublicRow where
  premises : List Pattern
  payload : PublicPayload
deriving DecidableEq, Repr

def erasePayload : PublicPayload → PublicPayload
  | .data f => .data (eraseFact f)
  | .normalTarget id => .normalTarget id
  | .demandTarget => .demandTarget
  | .pairedDemand entry exit => .pairedDemand (erase entry) (exit.map erase)
def normalizePublic (row : PublicRow) : PublicRow :=
  ⟨row.premises.map erase,erasePayload row.payload⟩
def allPlain : List Pattern → Bool | [] => true | x::xs => !marked x.head && allPlain xs
def payloadPlain : PublicPayload → Bool
  | .data f => !marked f.pattern.head
  | .pairedDemand e none => !marked e.head
  | .pairedDemand e (some x) => !marked e.head && !marked x.head
  | _ => true
def publicPlain (row : PublicRow) : Bool := allPlain row.premises && payloadPlain row.payload

/-- Archived NormalRuleContributorStore-like point inputs remain local inputs,
even across runs. They are not a public summary/demand boundary. -/
structure ArchivedPoint where
  owner : Nat
  scope : Nat
  point : Nat
  original : List Pattern
  actual : Fact
deriving DecidableEq, Repr
def archivePoint (row : ArchivedPoint) : ArchivedPoint := row

def f : Acc := 7
def g : Acc := 8
def T : Mark := .full 11
def mode : Mode := ⟨.forward,2⟩
def anyD (path : List Acc) (mark : Mark := .flow) : Demand := ⟨1,path,.any,mark⟩
def soa (path : List Acc) (mark : Mark := .flow) (e : List Acc := []) : Pattern := ⟨1,path,.starOrAny,mark,e⟩
def plainStar (path : List Acc) (mark : Mark := .flow) : Pattern := ⟨1,path,.plain .star,mark,[]⟩
def fact (p : Pattern) (layer : Layer := .normal) : Fact := ⟨p,layer,false⟩
def seed (p : Pattern) (layer : Layer := .normal) : Seed := ⟨p,layer⟩

theorem SOA_is_operational_STAR_not_uniform_MUST :
    opHead .starOrAny = .star ∧ opHead .starOrAny ≠ .must ∧
    scalar (soa []) = scalar (plainStar []) := by decide

theorem every_finite_actual_has_an_executable_tag (tag : Tag) : tag ∈ allTags := by
  cases tag with
  | mk old flag =>
    apply List.mem_flatMap.mpr
    refine ⟨old,SelectedFullAdmission.every_bounded_typed_actual_is_enumerated old,?_⟩
    apply List.mem_map.mpr
    exact ⟨flag,by cases flag <;> simp,rfl⟩

theorem exact_finite_raw_image_has_actual_witness
    (choice : C2Choice) (run : Nat) (m : Mode) (d : Demand) (s : Seed) :
    canEmitRaw choice run m d s = true ↔ ∃ tag : Tag, s ∈ c2 choice run m d (materialize tag) := by
  change decide (s ∈ allTags.flatMap (fun tag => c2 choice run m d (materialize tag))) = true ↔ _
  rw [decide_eq_true_eq,List.mem_flatMap]
  constructor
  · rintro ⟨tag,_,member⟩; exact ⟨tag,member⟩
  · rintro ⟨tag,member⟩; exact ⟨tag,every_finite_actual_has_an_executable_tag tag,member⟩

theorem normalized_image_keeps_a_raw_constructor_preimage
    (choice : C2Choice) (run : Nat) (m : Mode) (d : Demand) (stored : Seed) :
    stored ∈ storedImage choice run m d ↔
      ∃ raw, raw ∈ rawImage choice run m d ∧ eraseSeed raw = stored := by
  exact List.mem_map

theorem common_wrapper_emits_decorated_STAR_with_current_layers :
    c2 .starThenMayForAny 3 mode (anyD []) (fact (soa [])) = [seed (soa [])] ∧
    c2 .starThenMayForAny 3 mode (anyD [] T) (fact (soa [] T) .demand) = [seed (soa [] T) .demand] := by decide

theorem ordinary_STAR_same_head_ANY_rejection_is_unchanged :
    c2 .starThenMayForAny 3 mode (anyD []) (fact (plainStar [])) = [] ∧
    c2 .mayOnly 3 mode (anyD []) (fact (plainStar [])) = [] ∧
    c2 .unionViews 3 mode (anyD []) (fact (plainStar [])) = [] := by decide

theorem draft_fallback_preserves_any_existing_STAR_answer
    (run : Nat) (m : Mode) (d : Demand) (a : Fact) (s : Seed)
    (soaInput : marked a.pattern.head = true) (oldAnswer : starAnswer run m d a = some s) :
    c2 .starThenMayForAny run m d a = [s] := by
  simp [c2,soaInput,oldAnswer]

theorem both_nonempty_common_views_have_compatible_seed_and_layer :
    starAnswer 3 mode (anyD []) (fact (soa [f,g])) = some (seed (soa [f])) ∧
    mayAnswer 3 mode (anyD []) (fact (soa [f,g])) = some (seed (soa [f])) ∧
    c2 .unionViews 3 mode (anyD []) (fact (soa [f,g])) = [seed (soa [f])] := by decide

theorem equal_two_view_answers_coalesce_without_layer_invention (s : Seed) :
    combine (some s) (some s) = [s] := by simp [combine]

/-- API-only negative cell. This demand is not proved reachable in the driver:
FLOW EXACT demand entries are excluded by current snapshot grammar. -/
theorem strict_MAY_only_can_drop_an_existing_API_STAR_admission :
    c2 .starThenMayForAny 3 mode ⟨1,[],.exact,.flow⟩ (fact (soa [])) =
      [seed ⟨1,[],.plain .exact,.flow,[]⟩] ∧
    c2 .mayOnly 3 mode ⟨1,[],.exact,.flow⟩ (fact (soa [])) = [] := by decide

theorem original_STAR_exclusions_block_virtual_MAY_descents :
    mayAnswer 3 mode (anyD [f]) (fact (soa [] .flow [f])) = none ∧
    c2 .starThenMayForAny 3 mode (anyD [f]) (fact (soa [] .flow [f])) = [] ∧
    c2 .starThenMayForAny 3 mode (anyD [g]) (fact (soa [] .flow [f])) = [seed (soa [g])] := by decide

theorem minimal_minting_and_first_field_inheritance :
    c2 .starThenMayForAny 3 mode (anyD []) (fact ⟨1,[],.plain .may,.flow,[]⟩ .demand) = [seed (soa [])] ∧
    c2 .starThenMayForAny 3 mode (anyD []) (fact ⟨1,[f,g],.plain .may,.flow,[]⟩ .demand) = [seed (plainStar [f])] ∧
    c2 .starThenMayForAny 3 mode (anyD []) (fact (soa [f,g])) = [seed (soa [f])] := by decide

theorem deeper_C2_transition_needs_the_inherited_marker :
    c2 .starThenMayForAny 3 mode (anyD [f]) (fact (soa [f])) = [seed (soa [f])] ∧
    c2 .starThenMayForAny 3 mode (anyD [f]) (fact (erase (soa [f]))) = [] := by decide

theorem genuine_nonSTAR_operation_or_cut_drops_the_marker :
    operationHead .starOrAny .star = .starOrAny ∧
    operationHead .starOrAny .exact = .plain .exact ∧
    operationHead .starOrAny .may = .plain .may ∧
    operationHead .starOrAny .must = .plain .must ∧
    operationHead (.plain .star) .star = .plain .star := by decide

theorem STAR_summary_application_preserves_SOAs_actual_suffix
    (b outBase : Nat) (entryPath resultPath suffix : List Acc) (mark : Mark)
    (layer : Layer) (e : List Acc) (h : Bool) :
    applyStarSummary b outBase entryPath resultPath
      ⟨⟨b,entryPath ++ suffix,.starOrAny,mark,e⟩,layer,h⟩ =
      some ⟨⟨outBase,resultPath ++ suffix,.starOrAny,mark,e⟩,layer,h⟩ := by
  have removed : dropPrefix entryPath (entryPath ++ suffix) = some suffix := CoreAux.dropPrefix_some.mpr rfl
  simp [applyStarSummary,Nat.beq_refl,removed,operationHead,marked,opHead]

@[simp] theorem normalized_pattern_is_plain (p : Pattern) : marked (erase p).head = false := by
  cases p with
  | mk b path head mark e => cases head <;> rfl

@[simp] theorem normalized_pattern_is_idempotent (p : Pattern) : erase (erase p) = erase p := by
  cases p with
  | mk b path head mark e => cases head <;> rfl

theorem every_public_data_ND_Target_and_demand_slot_loses_the_marker (row : PublicRow) :
    publicPlain (normalizePublic row) = true := by
  have premises : allPlain (row.premises.map erase) = true := by
    induction row.premises with
    | nil => rfl
    | cons first rest ih => simp [allPlain,ih]
  cases row with
  | mk ps payload =>
    cases payload with
    | data f => simp [publicPlain,normalizePublic,erasePayload,payloadPlain,eraseFact,premises]
    | normalTarget id => simp [publicPlain,normalizePublic,erasePayload,payloadPlain,premises]
    | demandTarget => simp [publicPlain,normalizePublic,erasePayload,payloadPlain,premises]
    | pairedDemand entry exitValue =>
      cases exitValue <;> simp [publicPlain,normalizePublic,erasePayload,payloadPlain,premises]

theorem public_normalization_keeps_target_id_layer_and_protection (ps : List Pattern) (p : Pattern) (l : Layer) (h : Bool) (id : Nat) :
    (normalizePublic ⟨ps,.normalTarget id⟩).payload = .normalTarget id ∧
    (eraseFact ⟨p,l,h⟩).layer = l ∧ (eraseFact ⟨p,l,h⟩).protection = h := by
  exact ⟨rfl,rfl,rfl⟩

theorem archived_intra_proc_inputs_keep_the_capability (owner scope point : Nat) :
    (archivePoint ⟨owner,scope,point,[soa []],fact (soa [])⟩).actual.pattern.head = .starOrAny := rfl

theorem equal_location_view_does_not_allow_early_C2_erasure :
    scalar (erase (soa [])) = scalar (soa []) ∧
    soa [] ≠ erase (soa []) ∧
    c2 .starThenMayForAny 3 mode (anyD []) (fact (soa [])) ≠
      c2 .starThenMayForAny 3 mode (anyD []) (fact (erase (soa []))) := by decide

theorem SOA_seed_has_normalized_STAR_preimage_not_ordinary_STAR_input_admission :
    eraseSeed (seed (soa [])) = seed (plainStar []) ∧
    c2 .starThenMayForAny 3 mode (anyD []) (fact (soa [])) = [seed (soa [])] ∧
    c2 .starThenMayForAny 3 mode (anyD []) (fact (plainStar [])) = [] := by decide

/- Every counted-field path is allowed when it fits the unchanged budget.
The proof does not enumerate path length or the number of wrappers. -/
/-- This is the normalized entry-image part of C5, not restriction, insideDemand,
exit-side matching, budgets beyond oldCell, or actor publication. -/
theorem normalized_entry_image_has_an_explicit_actual_and_raw_joint_preimage
    (choice : C2Choice) (run : Nat) (m : Mode) (d : Demand) (stored : Seed) :
    stored ∈ storedImage choice run m d ↔
      ∃ tag : Tag, ∃ raw : Seed,
        raw ∈ c2 choice run m d (materialize tag) ∧ eraseSeed raw = stored := by
  rw [normalized_image_keeps_a_raw_constructor_preimage]
  constructor
  · rintro ⟨raw,member,equal⟩
    change raw ∈ allTags.flatMap (fun tag => c2 choice run m d (materialize tag)) at member
    obtain ⟨tag,_,emitted⟩ := List.mem_flatMap.mp member
    exact ⟨tag,raw,emitted,equal⟩
  · rintro ⟨tag,raw,emitted,equal⟩
    refine ⟨raw,?_,equal⟩
    exact List.mem_flatMap.mpr ⟨tag,every_finite_actual_has_an_executable_tag tag,emitted⟩

theorem unrelated_EXACT_on_MAY_loss_and_normal_EXACT_support_are_unchanged :
    c2 .starThenMayForAny 3 mode ⟨1,[],.exact,T⟩
      (fact ⟨1,[],.plain .may,T,[]⟩ .demand) =
        [seed ⟨1,[],.plain .exact,T,[]⟩ .demand] ∧
    c2 .starThenMayForAny 3 mode ⟨1,[],.exact,T⟩
      (fact ⟨1,[],.plain .exact,T,[]⟩) =
        [seed ⟨1,[],.plain .exact,T,[]⟩] := by decide

theorem marker_erasure_keeps_only_the_STAR_geometric_projection (p : Pattern) :
    scalar (erase p) = scalar p ∧ (erase p).exclusion = p.exclusion := by
  cases p with
  | mk b path head mark e => cases head <;> exact ⟨rfl,rfl⟩

def intrinsicMark : Mark → Layer | .flow => .normal | .full _ => .demand

def sameSOA (base : Nat) (path : List Acc) (mark : Mark) : Fact :=
  ⟨⟨base,path,.starOrAny,mark,[]⟩,intrinsicMark mark,false⟩

theorem same_head_ANY_admission_keeps_SOA_at_every_bounded_path
    (run : Nat) (m : Mode) (base : Nat) (path : List Acc) (mark : Mark)
    (restricted : 2 ≤ run) (bounded : path.length ≤ m.fieldLimit) :
    c2 .starThenMayForAny run m ⟨base,path,.any,mark⟩ (sameSOA base path mark) =
      [⟨⟨base,path,.starOrAny,mark,[]⟩,intrinsicMark mark⟩] := by
  have self : dropPrefix path path = some [] := ApSpec.Handoff.RAux.dropPrefix_self' path
  cases m with
  | mk direction limit =>
    cases direction <;> cases mark <;>
      simp [c2,starAnswer,mayAnswer,oldCell,sameSOA,erase,scalar,opHead,marked,
        mayView,originalReach,self,provisionalFlowExactBlocked,restricted,bounded,
        RestrictedInitialPolicy.DemandStarPolicy.emit,
        RestrictedInitialPolicy.DemandStarPolicy.overrideStar,
        RestrictedInitialPolicy.emit,RestrictedInitialPolicy.selectTemplate,
        RestrictedInitialPolicy.rawTemplate,RestrictedInitialPolicy.validTemplate,
        RestrictedInitialPolicy.validInput,RestrictedInitialPolicy.acceptsMark,
        RestrictedInitialPolicy.shapeEq,RestrictedInitialPolicy.render,relate,
        MayInitialToStarAudit.directionLegal,fromInput,plainOf,answer,renderedHead,
        MayInitialToStarAudit.admissionLayer,MayInitialToStarAudit.intrinsic,
        MayInitialToStarAudit.layerOr,intrinsicMark]

/-- Model only physical copy bindings and the conditional STAR/FLOW summary.
No SOURCE, sink, branch, scheduling or loop semantics are added here. -/
def copyTo (base : Nat) (a : Fact) : Fact := {a with pattern := {a.pattern with base := base}}
def plainWrapper (run : Nat) (m : Mode) (a : Fact) : Option Fact :=
  let bound := copyTo 1 (copyTo 2 a)
  let d : Demand := ⟨bound.pattern.base,bound.pattern.path,.any,bound.pattern.mark⟩
  (c2 .starThenMayForAny run m d bound).head?.bind fun s =>
    applyStarSummary 1 1 s.pattern.path s.pattern.path ⟨s.pattern,s.layer,false⟩
def wrapperChain (run : Nat) (m : Mode) : Nat → Fact → Option Fact
  | 0,a => some a
  | n+1,a => (plainWrapper run m a).bind (wrapperChain run m n)

theorem one_plain_wrapper_copies_and_STAR_summary_preserve_the_capability
    (run : Nat) (m : Mode) (path : List Acc) (mark : Mark)
    (restricted : 2 ≤ run) (bounded : path.length ≤ m.fieldLimit) :
    plainWrapper run m (sameSOA 1 path mark) = some (sameSOA 1 path mark) := by
  have enter := same_head_ANY_admission_keeps_SOA_at_every_bounded_path run m 1 path mark restricted bounded
  have self : dropPrefix path path = some [] := ApSpec.Handoff.RAux.dropPrefix_self' path
  simpa [plainWrapper,copyTo,sameSOA,applyStarSummary,self,operationHead,marked,opHead] using
    congrArg (fun seeds : List Seed => seeds.head?.bind fun s =>
      applyStarSummary 1 1 s.pattern.path s.pattern.path ⟨s.pattern,s.layer,false⟩) enter

theorem any_number_of_plain_wrappers_preserves_local_admission_ability
    (n run : Nat) (m : Mode) (path : List Acc) (mark : Mark)
    (restricted : 2 ≤ run) (bounded : path.length ≤ m.fieldLimit) :
    wrapperChain run m n (sameSOA 1 path mark) = some (sameSOA 1 path mark) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wrapperChain,
      one_plain_wrapper_copies_and_STAR_summary_preserve_the_capability run m path mark restricted bounded,
      Option.bind_some,ih]

def check : Bool :=
  decide (c2 .starThenMayForAny 3 mode (anyD []) (fact (soa [])) = [seed (soa [])]) &&
  decide (c2 .starThenMayForAny 3 mode (anyD []) (fact (plainStar [])) = []) &&
  decide (operationHead .starOrAny .may = .plain .may) &&
  publicPlain (normalizePublic ⟨[soa [],soa [] T],.data (fact (soa [f]))⟩)

theorem executable_draft_contract_cells : check = true := by decide
#eval (if check then "STAR_OR_ANY_DESIGN=true" else "STAR_OR_ANY_DESIGN=false")


#print axioms SOA_is_operational_STAR_not_uniform_MUST
#print axioms every_finite_actual_has_an_executable_tag
#print axioms exact_finite_raw_image_has_actual_witness
#print axioms normalized_image_keeps_a_raw_constructor_preimage
#print axioms common_wrapper_emits_decorated_STAR_with_current_layers
#print axioms ordinary_STAR_same_head_ANY_rejection_is_unchanged
#print axioms draft_fallback_preserves_any_existing_STAR_answer
#print axioms both_nonempty_common_views_have_compatible_seed_and_layer
#print axioms equal_two_view_answers_coalesce_without_layer_invention
#print axioms strict_MAY_only_can_drop_an_existing_API_STAR_admission
#print axioms original_STAR_exclusions_block_virtual_MAY_descents
#print axioms minimal_minting_and_first_field_inheritance
#print axioms deeper_C2_transition_needs_the_inherited_marker
#print axioms genuine_nonSTAR_operation_or_cut_drops_the_marker
#print axioms STAR_summary_application_preserves_SOAs_actual_suffix
#print axioms normalized_pattern_is_plain
#print axioms normalized_pattern_is_idempotent
#print axioms every_public_data_ND_Target_and_demand_slot_loses_the_marker
#print axioms public_normalization_keeps_target_id_layer_and_protection
#print axioms archived_intra_proc_inputs_keep_the_capability
#print axioms equal_location_view_does_not_allow_early_C2_erasure
#print axioms SOA_seed_has_normalized_STAR_preimage_not_ordinary_STAR_input_admission
#print axioms normalized_entry_image_has_an_explicit_actual_and_raw_joint_preimage
#print axioms unrelated_EXACT_on_MAY_loss_and_normal_EXACT_support_are_unchanged
#print axioms marker_erasure_keeps_only_the_STAR_geometric_projection
#print axioms same_head_ANY_admission_keeps_SOA_at_every_bounded_path
#print axioms one_plain_wrapper_copies_and_STAR_summary_preserve_the_capability
#print axioms any_number_of_plain_wrappers_preserves_local_admission_ability
#print axioms executable_draft_contract_cells

end StarOrAnyDesign
