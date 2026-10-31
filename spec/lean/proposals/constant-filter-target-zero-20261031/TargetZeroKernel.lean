import Init

/-!
Target-guided ZERO, revised selected laws (2026-10-31).

Dc intersects the actual PREMISE; Dp intersects the actual CONCLUSION.
Dc=Target accepts actual ZERO only. Dp=ZERO accepts actual ZERO or actual
Target and preserves the actual label/id. Ordinary Dp rejects Target. Handoff is
uniformly paired, including a ZERO premise. There is no DEMAND Target C5
publication bypass. NORMAL local terminal publication is raw and separate from
C5 (see TargetZeroSourcePermission). A complete NORMAL sink witness emits NormalTarget(reportId), interned
by sink location/rule. A DEMAND sink witness emits anonymous DemandTarget.
Backward accepted source hits emit DEMAND Target. Only DEMAND Target guides a
future run and counts for continuation. NORMAL Target remains available for
all-NORMAL caller application and retains its id. SelectedTargetApplication
rejects applying a NORMAL Target with any DEMAND support; the old promotion
algebra below is reference only. DemandTarget persists under admitted support.
Final reports come only from ZERO-premise
NormalTarget(id) summaries owned by configured roots. C5 itself emits no report.

Scope: local control, paired C5, explicit caller-support routes, and bounded
finite closure. Existing AP intersection is a parameter. This model does not
prove production AP, source/sink binding, scheduler, report, or replay refinement.
No superseded target constructors or publication bypasses are modeled.
-/
namespace TargetZeroKernel
set_option autoImplicit false
set_option linter.constructorNameAsVariable false

inductive Direction where
  | forward | backward
  deriving DecidableEq, Repr

inductive Layer where
  | normal | demand
  deriving DecidableEq, Repr

inductive Atom where
  | a | b | c
  deriving DecidableEq, Repr

/-- `both` is a distinct premise key. Ordinary conjunction/AP semantics is
    supplied by the unchanged premise adapter, not proved by this tag. -/
inductive Premise where
  | zero | ap (a : Atom) | both (a b : Atom)
  deriving DecidableEq, Repr

inductive Target where
  | normalTarget (reportId : Nat)
  | demandTarget
  deriving DecidableEq, Repr

def Target.layer : Target → Layer
  | .normalTarget _ => .normal
  | .demandTarget => .demand

def Target.fromLayer (layer : Layer) (reportId : Nat) : Target :=
  match layer with
  | .normal => .normalTarget reportId
  | .demand => .demandTarget

inductive Fact where
  | zero | ap (a : Atom) | target (label : Target)
  deriving DecidableEq, Repr

inductive Pattern where
  | zero | ap (a : Atom) | both (a b : Atom) | target
  deriving DecidableEq, Repr

def Premise.pattern : Premise → Pattern
  | .zero => .zero
  | .ap a => .ap a
  | .both a b => .both a b

def Fact.pattern : Fact → Pattern
  | .zero => .zero
  | .ap a => .ap a
  | .target _ => .target

/-- Dc side: Target accepts actual ZERO only. Ordinary matching is delegated. -/
def entryIntersects (ordinary : Premise → Premise → Bool) : Pattern → Premise → Bool
  | .target, .zero => true
  | .target, _ => false
  | .zero, .zero => true
  | .zero, _ => false
  | .ap a, p => ordinary (.ap a) p
  | .both a b, p => ordinary (.both a b) p

/-- Dp side: ZERO accepts ZERO and Target, preserving the actual label.
    Ordinary AP output restriction cannot produce or accept a Target. -/
def exitIntersect (ordinary : Premise → Atom → Option Atom) : Premise → Fact → Option Fact
  | .zero, .zero => some .zero
  | .zero, .target label => some (.target label)
  | .zero, .ap _ => none
  | .ap a, .ap b => (ordinary (.ap a) b).map Fact.ap
  | .both a b, .ap c => (ordinary (.both a b) c).map Fact.ap
  | _, _ => none

theorem target_entry_zero_only (ordinary : Premise → Premise → Bool) (p : Premise) :
    entryIntersects ordinary .target p = true ↔ p = .zero := by
  cases p <;> simp [entryIntersects]

theorem zero_exit_target_preserved (ordinary : Premise → Atom → Option Atom) (label : Target) :
    exitIntersect ordinary .zero (.target label) = some (.target label) := rfl

theorem zero_exit_zero_preserved (ordinary : Premise → Atom → Option Atom) :
    exitIntersect ordinary .zero .zero = some .zero := rfl

theorem ordinary_exit_rejects_target (ordinary : Premise → Atom → Option Atom)
    (p : Premise) (label : Target) (nonzero : p ≠ .zero) :
    exitIntersect ordinary p (.target label) = none := by
  cases p with
  | zero => exact False.elim (nonzero rfl)
  | ap _ => rfl
  | both _ _ => rfl

structure Summary where
  owner : Nat
  premise : Premise
  conclusion : Fact
  layer : Layer
  deriving DecidableEq, Repr

/-- Summary still has a layer for ordinary AP rows. Target constructors and the
    stored layer must agree; all selected Target factories below establish it. -/
def TargetWellFormed (s : Summary) : Prop :=
  match s.conclusion with
  | .target label => s.layer = label.layer
  | _ => True

structure Demand where
  owner : Nat
  entry : Pattern
  exit : Premise
  deriving DecidableEq, Repr

/-- Every handoff is paired: no special ZERO -> entry-only rule. -/
def handoff (s : Summary) : Demand := ⟨s.owner, s.conclusion.pattern, s.premise⟩

def layeredTargetSummary (owner : Nat) (p : Premise) (layer : Layer)
    (reportId : Nat := 0) : Summary := ⟨owner, p, .target (Target.fromLayer layer reportId), layer⟩
def targetSummary (owner : Nat) (p : Premise) : Summary := layeredTargetSummary owner p .demand
def handoffTarget (owner : Nat) (p : Premise) : Demand := handoff (targetSummary owner p)

theorem generated_target_well_formed (owner : Nat) (p : Premise) (layer : Layer)
    (reportId : Nat) : TargetWellFormed (layeredTargetSummary owner p layer reportId) := by
  cases layer <;> rfl

/-- Future-run selection is distinct from local summary publication. The caller
    may compose an unselected NORMAL Target before this selection is applied. -/
def targetGuidanceSelected (s : Summary) : Bool :=
  match s.conclusion with
  | .target .demandTarget => true
  | _ => false

def selectedTargetHandoff (s : Summary) : Option Demand :=
  if targetGuidanceSelected s then some (handoff s) else none

theorem normalTargetNotSelected (owner : Nat) (p : Premise) (reportId : Nat) :
    selectedTargetHandoff (layeredTargetSummary owner p .normal reportId) = none := rfl

theorem demandTargetSelected (owner : Nat) (p : Premise) :
    selectedTargetHandoff (layeredTargetSummary owner p .demand) =
      some (handoffTarget owner p) := rfl

/-- Target selection takes priority over all old ordinary selection exceptions,
    including NORMAL ND and backward ZERO. Ordinary rows use their old selector. -/
def selectHandoff (ordinary : Direction → Summary → Bool) (direction : Direction)
    (s : Summary) : Option Demand :=
  match s.conclusion with
  | .target _ => selectedTargetHandoff s
  | _ => if ordinary direction s then some (handoff s) else none

theorem normal_target_overrides_ordinary_selection (ordinary : Direction → Summary → Bool)
    (direction : Direction) (owner : Nat) (p : Premise) (reportId : Nat) :
    selectHandoff ordinary direction (layeredTargetSummary owner p .normal reportId) = none := rfl

theorem demand_target_overrides_ordinary_selection (ordinary : Direction → Summary → Bool)
    (direction : Direction) (owner : Nat) (p : Premise) :
    selectHandoff ordinary direction (targetSummary owner p) = some (handoffTarget owner p) := rfl

theorem handoff_zero_premise_paired (owner : Nat) (f : Fact) (l : Layer) :
    handoff ⟨owner, .zero, f, l⟩ = ⟨owner, f.pattern, .zero⟩ := rfl

def c5Accept (entryAP : Premise → Premise → Bool)
    (exitAP : Premise → Atom → Option Atom) (d : Demand) (s : Summary) : Bool :=
  (d.owner == s.owner) && entryIntersects entryAP d.entry s.premise &&
    (exitIntersect exitAP d.exit s.conclusion).isSome

def c5Restrict (entryAP : Premise → Premise → Bool)
    (exitAP : Premise → Atom → Option Atom) (d : Demand) (s : Summary) : Option Summary :=
  if (d.owner == s.owner) && entryIntersects entryAP d.entry s.premise then
    (exitIntersect exitAP d.exit s.conclusion).map fun f => {s with conclusion := f}
  else none

/-- The exact C5 criterion for either Target label. DEMAND publication uses this
    gate; raw NORMAL local terminal publication is a separate operation. -/
theorem c5_accept_target_iff (entryAP : Premise → Premise → Bool)
    (exitAP : Premise → Atom → Option Atom) (d : Demand) (owner : Nat)
    (p : Premise) (label : Target) (layer : Layer) :
    c5Accept entryAP exitAP d ⟨owner, p, .target label, layer⟩ = true ↔
      (d.owner == owner) = true ∧ entryIntersects entryAP d.entry p = true ∧ d.exit = .zero := by
  cases d with
  | mk m dc dp =>
      cases dp <;> simp [c5Accept, exitIntersect, Bool.and_eq_true]

theorem c5_target_label_preserved (entryAP : Premise → Premise → Bool)
    (exitAP : Premise → Atom → Option Atom) (d : Demand) (owner : Nat)
    (p : Premise) (label : Target) (layer : Layer)
    (accepted : c5Accept entryAP exitAP d ⟨owner, p, .target label, layer⟩ = true) :
    c5Restrict entryAP exitAP d ⟨owner, p, .target label, layer⟩ =
      some ⟨owner, p, .target label, layer⟩ := by
  obtain ⟨ownerMatch, premiseMatch, zeroExit⟩ :=
    (c5_accept_target_iff entryAP exitAP d owner p label layer).mp accepted
  simp only [c5Restrict, ownerMatch, premiseMatch, Bool.true_and, ↓reduceIte,
    zeroExit, exitIntersect, Option.map_some]

/-- A summary-level ZERO/Reach gate must inspect the actual conclusion. An
    initial ZERO does not make a P -> Target conclusion into a Reach summary.
    This gate follows selected C5; it grants no C5 publication permission. -/
def keepOutsideZeroReach (s : Summary) : Bool :=
  !(s.premise == .zero && s.conclusion == .zero)

theorem target_not_zero_reach (owner : Nat) (p : Premise) (label : Target) (layer : Layer) :
    keepOutsideZeroReach ⟨owner, p, .target label, layer⟩ = true := by
  cases p <;> rfl

theorem selected_target_survives_zero_reach_gate (entryAP : Premise → Premise → Bool)
    (exitAP : Premise → Atom → Option Atom) (d : Demand) (owner : Nat)
    (p : Premise) (label : Target) (layer : Layer)
    (accepted : c5Accept entryAP exitAP d ⟨owner, p, .target label, layer⟩ = true) :
    (c5Restrict entryAP exitAP d ⟨owner, p, .target label, layer⟩).map keepOutsideZeroReach =
      some true := by
  rw [c5_target_label_preserved entryAP exitAP d owner p label layer accepted]
  exact congrArg some (target_not_zero_reach owner p label layer)

/-- Witness acceptance/binding is external. A complete forward sink witness
    creates a local Target summary with exactly the witness layer. -/
def forwardSinkTarget (owner : Nat) (p : Premise) (layer : Layer) (reportId : Nat := 0) : Summary :=
  layeredTargetSummary owner p layer reportId

theorem NormalSinkTargetNormal (owner : Nat) (p : Premise) (reportId : Nat) :
    forwardSinkTarget owner p .normal reportId = layeredTargetSummary owner p .normal reportId := rfl

theorem DemandSinkTarget (owner : Nat) (p : Premise) (reportId : Nat) :
    forwardSinkTarget owner p .demand reportId = targetSummary owner p := rfl

/-- Low-level marker factory for an accepted reverse actual GEN. The production
    adapter must establish original forward.from=ZERO and forward.to!=ZERO.
    Conditional SourceHit/permission transfers and record replay do not qualify. -/
def backwardSourceTarget (owner : Nat) (p : Premise) : Summary := targetSummary owner p

/-- Original source edges cannot contain the new Target control conclusion. -/
inductive OriginalFact where
  | zero | ap (a : Atom)
  deriving DecidableEq, Repr

structure OriginalEdge where
  forwardFrom : OriginalFact
  forwardTo : OriginalFact
  deriving DecidableEq, Repr

def actualGen : OriginalEdge → Bool
  | ⟨.zero, .ap _⟩ => true
  | _ => false

inductive SourceEvent where
  | actualReverseTransfer | recordReplay
  deriving DecidableEq, Repr

/-- The GEN hit occurs before downstream filtering. Its existing seed permission
    and ordinary AP transfer remain outside this marker operation. -/
def backwardGenEventTarget (event : SourceEvent) (edge : OriginalEdge)
    (accepted : Bool) (_downstreamAllowed : Bool) (owner : Nat) (p : Premise) : Option Summary :=
  match event with
  | .recordReplay => none
  | .actualReverseTransfer =>
      if accepted && actualGen edge then some (backwardSourceTarget owner p) else none

theorem record_replay_cannot_create_gen_target (edge : OriginalEdge) (accepted downstream : Bool)
    (owner : Nat) (p : Premise) :
    backwardGenEventTarget .recordReplay edge accepted downstream owner p = none := rfl

theorem conditional_transfer_cannot_create_gen_target (a b : Atom) (accepted downstream : Bool)
    (owner : Nat) (p : Premise) :
    backwardGenEventTarget .actualReverseTransfer ⟨.ap a, .ap b⟩ accepted downstream owner p = none := by
  cases accepted <;> rfl

theorem accepted_gen_target_precedes_downstream_filter (a : Atom) (downstream : Bool)
    (owner : Nat) (p : Premise) :
    backwardGenEventTarget .actualReverseTransfer ⟨.zero, .ap a⟩ true downstream owner p =
      some (targetSummary owner p) := rfl

def continuationRelevant (s : Summary) : Bool :=
  match s.conclusion with
  | .target (.normalTarget _) => false
  | .target .demandTarget => true
  | _ => s.layer == .demand

theorem continuationTargetPositive (owner : Nat) (p : Premise) :
    continuationRelevant (targetSummary owner p) = true := rfl

theorem normalTargetNotContinuation (owner : Nat) (p : Premise) (reportId : Nat) :
    continuationRelevant (layeredTargetSummary owner p .normal reportId) = false := rfl

/-- Reference layer algebra. Selected NormalTarget application first requires
    all-NORMAL support (see SelectedTargetApplication), rather than promoting it. -/
def composeLayer : Layer → Layer → Layer
  | .normal, .normal => .normal
  | _, _ => .demand

def composeTargetLabel : Layer → Target → Target
  | .normal, .normalTarget reportId => .normalTarget reportId
  | _, _ => .demandTarget

theorem composed_target_layer_is_ordinary_join (input : Layer) (callee : Target) :
    (composeTargetLabel input callee).layer = composeLayer input callee.layer := by
  cases input <;> cases callee <;> rfl

/-- Reference algebra only. Do not use without the selected application guard. -/
def composeCallerTarget (caller : Nat) (parentPremise : Premise)
    (callerInput : Layer) (calleeTarget : Target) : Summary :=
  let label := composeTargetLabel callerInput calleeTarget
  ⟨caller, parentPremise, .target label, label.layer⟩

theorem normal_callee_target_demand_caller (caller : Nat) (p : Premise) (reportId : Nat) :
    composeCallerTarget caller p .demand (.normalTarget reportId) = targetSummary caller p := rfl

theorem normal_callee_target_normal_caller (caller : Nat) (p : Premise) (reportId : Nat) :
    composeCallerTarget caller p .normal (.normalTarget reportId) =
      layeredTargetSummary caller p .normal reportId := rfl

theorem demand_callee_target_normal_caller (caller : Nat) (p : Premise) :
    composeCallerTarget caller p .normal .demandTarget = targetSummary caller p := rfl

theorem demand_target_persists_anonymously (caller : Nat) (p : Premise) (input : Layer) :
    composeCallerTarget caller p input .demandTarget = targetSummary caller p := by
  cases input <;> rfl

theorem composed_target_well_formed (caller : Nat) (p : Premise) (input : Layer)
    (callee : Target) : TargetWellFormed (composeCallerTarget caller p input callee) := by
  cases input <;> cases callee <;> rfl

/-- Id identity depends only on sink location/rule, not on a proof witness. -/
structure SinkKey where
  location : Nat
  rule : Nat
  deriving DecidableEq, Repr

def internSink : List SinkKey → SinkKey → Option Nat
  | [], _ => none
  | key :: rest, wanted =>
      if wanted == key then some 0 else (internSink rest wanted).map Nat.succ

/-- A total finite registry operation: reuse an existing id or append a new key.
    The selected finite controls below check stable reuse and distinct inserts. -/
def registerSink (catalog : List SinkKey) (key : SinkKey) : Nat × List SinkKey :=
  match internSink catalog key with
  | some id => (id, catalog)
  | none => (catalog.length, catalog ++ [key])

def internedSinkTarget (catalog : List SinkKey) (key : SinkKey) (owner : Nat)
    (p : Premise) (layer : Layer) : Option Summary :=
  match layer with
  | .normal => (internSink catalog key).map fun id => forwardSinkTarget owner p .normal id
  | .demand => some (targetSummary owner p)

/-- Report extraction is a separate configured-root operation, never a C5 effect. -/
def finalReport (roots : List Nat) (s : Summary) : Option Nat :=
  if s.owner ∈ roots then
    match s.premise, s.conclusion with
    | .zero, .target (.normalTarget reportId) => some reportId
    | _, _ => none
  else none

theorem final_report_iff (roots : List Nat) (s : Summary) (reportId : Nat) :
    finalReport roots s = some reportId ↔
      s.owner ∈ roots ∧ s.premise = .zero ∧ s.conclusion = .target (.normalTarget reportId) := by
  cases s with
  | mk owner premise conclusion layer =>
      by_cases rooted : owner ∈ roots
      · cases premise <;> cases conclusion with
        | zero => simp [finalReport, rooted]
        | ap a => simp [finalReport, rooted]
        | target label => cases label <;> simp [finalReport, rooted]
      · simp [finalReport, rooted]

theorem demand_target_never_reports (roots : List Nat) (owner : Nat) (p : Premise) :
    finalReport roots (targetSummary owner p) = none := by
  cases p <;> exact ite_self none

theorem nonroot_never_reports (roots : List Nat) (s : Summary) (absent : s.owner ∉ roots) :
    finalReport roots s = none := if_neg absent

/-- Even after C5, a non-root Target remains a non-root Target. Reporting is
    performed later by finalReport, which needs a root ZERO summary. -/
theorem c5_target_does_not_create_root_report (entryAP : Premise → Premise → Bool)
    (exitAP : Premise → Atom → Option Atom) (d : Demand) (roots : List Nat) (owner : Nat)
    (p : Premise) (label : Target) (layer : Layer)
    (accepted : c5Accept entryAP exitAP d ⟨owner, p, .target label, layer⟩ = true)
    (absent : owner ∉ roots) :
    (c5Restrict entryAP exitAP d ⟨owner, p, .target label, layer⟩).bind (finalReport roots) = none := by
  rw [c5_target_label_preserved entryAP exitAP d owner p label layer accepted]
  exact nonroot_never_reports roots ⟨owner, p, .target label, layer⟩ absent

def dedupReportIds : List Nat → List Nat
  | [] => []
  | id :: rest => if id ∈ rest then dedupReportIds rest else id :: dedupReportIds rest

def collectReports (roots : List Nat) (summaries : List Summary) : List Nat :=
  dedupReportIds (summaries.filterMap (finalReport roots))

/-- Restricted ZERO discovery is guidance-driven; run-1 discovery is unchanged.
    All modes require an actual ZERO, never an AP or Target actual. -/
inductive Phase where
  | run1 | restricted
  deriving DecidableEq, Repr

def zeroEntry : Pattern → Bool
  | .zero | .target => true
  | _ => false

def zeroAdmit (phase : Phase) (rows : List Demand) (owner : Nat) : Fact → Bool
  | .zero => match phase with
    | .run1 => true
    | .restricted => rows.any fun d => d.owner == owner && zeroEntry d.entry
  | _ => false

def emittedZero (phase : Phase) (rows : List Demand) (owner : Nat) (actual : Fact) : List Fact :=
  if zeroAdmit phase rows owner actual then [.zero] else []

theorem target_initial_zero_only (owner : Nat) (p : Premise) :
    emittedZero .restricted [handoffTarget owner p] owner .zero = [.zero] := by
  change (if ((owner == owner) && true || false) then [Fact.zero] else []) = [Fact.zero]
  have self : (owner == owner) = true := decide_eq_true rfl
  have condition : ((owner == owner) && true || false) = true :=
    congrArg (fun b : Bool => b && true || false) self
  exact if_pos condition

theorem target_cannot_create_zero_from_ap (phase : Phase) (rows : List Demand)
    (owner : Nat) (a : Atom) : emittedZero phase rows owner (.ap a) = [] := rfl

theorem target_actual_cannot_create_zero (phase : Phase) (rows : List Demand)
    (owner : Nat) (label : Target) : emittedZero phase rows owner (.target label) = [] := rfl

theorem run1_discovery_zero_unchanged (rows : List Demand) (owner : Nat) :
    emittedZero .run1 rows owner .zero = [.zero] := rfl

theorem restricted_no_local_guide_no_zero (owner : Nat) :
    emittedZero .restricted [] owner .zero = [] := rfl

/-- Both root and callee adapters must call the same admission boundary. The
    equality below is a model law; current production entry paths are unproved. -/
inductive EntryKind where
  | root | callee
  deriving DecidableEq, Repr
def zeroStart (_kind : EntryKind) (phase : Phase) (rows : List Demand)
    (owner : Nat) (actual : Fact) : List Fact := emittedZero phase rows owner actual
theorem root_and_callee_share_guided_zero_gate (phase : Phase) (rows : List Demand)
    (owner : Nat) (actual : Fact) :
    zeroStart .root phase rows owner actual = zeroStart .callee phase rows owner actual := rfl

structure Terminal where
  direction : Direction
  owner : Nat
  premise : Premise
  site : Nat
  deriving DecidableEq, Repr

def Terminal.summary (t : Terminal) : Summary := targetSummary t.owner t.premise

structure Binding where
  caller : Nat
  callee : Nat
  childPremise : Premise
  parentPremise : Premise
  normalReturn : Bool
  deriving DecidableEq, Repr

/-- Reference finite binding adapter. NORMAL+DEMAND promotion here is historical;
    SelectedTargetApplication adds the selected all-NORMAL application guard.
    Real AP/ND complete binding remains an independent adapter obligation. -/
def composeBoundTarget (b : Binding) (callerInput : Layer) (callee : Summary) : Option Summary :=
  match callee.conclusion with
  | .target label =>
      if callee.owner == b.callee && callee.premise == b.childPremise then
        some (composeCallerTarget b.caller b.parentPremise callerInput label)
      else none
  | _ => none

def exactEntry (p q : Premise) : Bool := p == q
def exactExit (p : Premise) (a : Atom) : Option Atom :=
  if p == .ap a then some a else none

def targetAllowed (incoming : List Demand) (owner : Nat) (p : Premise) : Bool :=
  incoming.any fun d => c5Accept exactEntry exactExit d (targetSummary owner p)

/-- This closure covers already-DEMAND terminal/caller routes. Local NORMAL
    Targets remain available to ordinary composition separately (see mixed-layer
    controls). A route includes selected C5 support at each method. Removing
    these certificates would assume the desired no-loss result. -/
inductive Need (seeds : List Terminal) (bindings : List Binding) (incoming : List Demand) :
    Direction → Nat → Premise → Nat → Type where
  | terminal (t : Terminal) (present : t ∈ seeds)
      (selected : targetAllowed incoming t.owner t.premise = true) :
      Need seeds bindings incoming t.direction t.owner t.premise t.site
  | caller (b : Binding) (actual : b ∈ bindings)
      {direction : Direction} {site : Nat}
      (body : Need seeds bindings incoming direction b.callee b.childPremise site)
      (selected : targetAllowed incoming b.caller b.parentPremise = true) :
      Need seeds bindings incoming direction b.caller b.parentPremise site

def dedupDemands : List Demand → List Demand
  | [] => []
  | d :: rest => if d ∈ rest then dedupDemands rest else d :: dedupDemands rest

theorem dedup_membership (d : Demand) (ds : List Demand) :
    d ∈ dedupDemands ds ↔ d ∈ ds := by
  induction ds with
  | nil => simp [dedupDemands]
  | cons head rest ih =>
      by_cases present : head ∈ rest
      · simp [dedupDemands, present, ih]
        intro same
        simpa [same] using present
      · simp [dedupDemands, present, ih]

def seedDemands (incoming : List Demand) (seeds : List Terminal) : List Demand :=
  seeds.filterMap fun t => if targetAllowed incoming t.owner t.premise then
    some (handoff t.summary) else none

def liftDemands (incoming : List Demand) (bindings : List Binding)
    (demands : List Demand) : List Demand :=
  bindings.filterMap fun b =>
    if handoffTarget b.callee b.childPremise ∈ demands ∧
      targetAllowed incoming b.caller b.parentPremise = true then
      some (handoffTarget b.caller b.parentPremise)
    else none

def close (incoming : List Demand) (bindings : List Binding) : Nat → List Demand → List Demand
  | 0, ds => dedupDemands ds
  | n + 1, ds =>
      let previous := close incoming bindings n ds
      dedupDemands (previous ++ liftDemands incoming bindings previous)

def Need.depth {seeds : List Terminal} {bindings : List Binding} {incoming : List Demand}
    {direction : Direction} {owner : Nat} {p : Premise} {site : Nat} :
    Need seeds bindings incoming direction owner p site → Nat
  | .terminal _ _ _ => 0
  | .caller _ _ body _ => body.depth + 1

theorem selected_terminal_seeded {incoming : List Demand} {seeds : List Terminal}
    (t : Terminal) (present : t ∈ seeds)
    (selected : targetAllowed incoming t.owner t.premise = true) :
    handoffTarget t.owner t.premise ∈ seedDemands incoming seeds := by
  apply List.mem_filterMap.mpr
  exact ⟨t, present, by simp only [selected, ↓reduceIte]; rfl⟩

theorem actual_binding_lifted {incoming : List Demand} {bindings : List Binding}
    {ds : List Demand} (b : Binding) (actual : b ∈ bindings)
    (child : handoffTarget b.callee b.childPremise ∈ ds)
    (selected : targetAllowed incoming b.caller b.parentPremise = true) :
    handoffTarget b.caller b.parentPremise ∈ liftDemands incoming bindings ds := by
  apply List.mem_filterMap.mpr
  exact ⟨b, actual, by simp only [child, selected, and_self, ↓reduceIte]⟩

/-- Constructive bounded completeness under the explicit C5 support certificates.
    The returned witness is computed from the finite route. Production still
    must implement terminal capture, binding projection, C5 and gate retention. -/
def closeCapturesNeed {seeds : List Terminal} {bindings : List Binding}
    {incoming : List Demand} {direction : Direction} {owner : Nat}
    {p : Premise} {site : Nat}
    (route : Need seeds bindings incoming direction owner p site) :
    {d : Demand // d ∈ close incoming bindings route.depth (seedDemands incoming seeds) ∧
      d = handoffTarget owner p} :=
  match route with
  | .terminal t present selected =>
      ⟨_, (dedup_membership _ _).mpr (selected_terminal_seeded t present selected), rfl⟩
  | .caller b actual body selected =>
      let child := closeCapturesNeed body
      let member : handoffTarget b.callee b.childPremise ∈
          close incoming bindings body.depth (seedDemands incoming seeds) := by
        simpa [child.property.2] using child.property.1
      ⟨_, (dedup_membership _ _).mpr
        (List.mem_append_right _ (actual_binding_lifted b actual member selected)), rfl⟩

namespace Controls

/-- Opposite NORMAL ZERO seed -> ordinary AP supplies a paired ZERO exit.
    The resulting row allows the demand sink/source Target at that AP premise. -/
def ordinaryZeroSummary (owner : Nat) (a : Atom) : Summary := ⟨owner, .zero, .ap a, .normal⟩
def sinkTarget : Summary := targetSummary 0 (.ap .a)
def sinkSeed : Summary := ordinaryZeroSummary 0 .a
def sinkIncoming : Demand := handoff sinkSeed
def sinkReverse : Demand := handoff sinkTarget

theorem sink_target_paired_cycle :
    c5Accept exactEntry exactExit sinkIncoming sinkTarget = true ∧
    c5Accept exactEntry exactExit sinkReverse sinkSeed = true ∧
    sinkIncoming = ⟨0, .ap .a, .zero⟩ ∧
    sinkReverse = ⟨0, .target, .ap .a⟩ := by decide

def sourceTarget : Summary := backwardSourceTarget 0 (.ap .b)
def sourceGen : Summary := ordinaryZeroSummary 0 .b
def sourceIncoming : Demand := handoff sourceGen
def sourceReverse : Demand := handoff sourceTarget

theorem source_target_paired_cycle :
    c5Accept exactEntry exactExit sourceIncoming sourceTarget = true ∧
    c5Accept exactEntry exactExit sourceReverse sourceGen = true ∧
    sourceIncoming = ⟨0, .ap .b, .zero⟩ ∧
    sourceReverse = ⟨0, .target, .ap .b⟩ := by decide

theorem zero_premise_target_accepted :
    c5Restrict exactEntry exactExit (handoffTarget 0 .zero) (targetSummary 0 .zero) =
      some (targetSummary 0 .zero) := by decide

theorem ordinary_dp_rejects_target :
    c5Accept exactEntry exactExit ⟨0, .ap .a, .ap .a⟩ sinkTarget = false := by decide

def sink : Terminal := ⟨.forward, 0, .ap .a, 10⟩
def nonreturning : Binding := ⟨1, 0, .ap .a, .ap .b, false⟩
def rootCall : Binding := ⟨2, 1, .ap .b, .zero, true⟩
def bindings : List Binding := [nonreturning, rootCall]
def incoming : List Demand := [⟨0, .ap .a, .zero⟩, ⟨1, .ap .b, .zero⟩, ⟨2, .zero, .zero⟩]
def chain : List Demand := close incoming bindings 3 (seedDemands incoming [sink])

def normalLocalSink : Summary := forwardSinkTarget 0 (.ap .a) .normal
def demandCallerTarget : Summary := composeCallerTarget 1 (.ap .b) .demand (.normalTarget 0)

theorem normal_local_target_c5_preserves_layer :
    c5Restrict exactEntry exactExit sinkIncoming normalLocalSink = some normalLocalSink := by decide

theorem historical_normal_local_target_composes_to_demand_caller :
    composeBoundTarget nonreturning .demand normalLocalSink = some demandCallerTarget ∧
    selectedTargetHandoff normalLocalSink = none ∧
    selectedTargetHandoff demandCallerTarget = some (handoffTarget 1 (.ap .b)) := by decide

def mixedLayerRoot : Option Summary :=
  (composeBoundTarget nonreturning .demand normalLocalSink).bind
    (composeBoundTarget rootCall .normal)

theorem historical_mixed_layer_promotion_chain :
    mixedLayerRoot = some (targetSummary 2 .zero) ∧
    selectedTargetHandoff normalLocalSink = none ∧
    selectedTargetHandoff demandCallerTarget = some (handoffTarget 1 (.ap .b)) ∧
    (mixedLayerRoot.bind selectedTargetHandoff) = some (handoffTarget 2 .zero) ∧
    c5Accept exactEntry exactExit incoming[1] demandCallerTarget = true ∧
    c5Accept exactEntry exactExit incoming[2] (targetSummary 2 .zero) = true := by decide

/-- Historical reference-promotion probe. It is not a selected application rule;
    the selected all-NORMAL guard rejects this NORMAL+DEMAND application. -/
def composeOnlyFutureSelected (b : Binding) (callerInput : Layer) (callee : Summary) : Option Summary :=
  if targetGuidanceSelected callee then composeBoundTarget b callerInput callee else none

theorem historical_early_selection_loses_reference_promotion :
    composeOnlyFutureSelected nonreturning .demand normalLocalSink = none ∧
    composeBoundTarget nonreturning .demand normalLocalSink = some demandCallerTarget := by decide

def normalReportRoot : Option Summary :=
  (composeBoundTarget nonreturning .normal normalLocalSink).bind
    (composeBoundTarget rootCall .normal)

theorem normal_call_chain_retains_id_and_reports_only_at_zero_root :
    normalReportRoot = some (layeredTargetSummary 2 .zero .normal 0) ∧
    finalReport [2] normalLocalSink = none ∧
    normalReportRoot.bind (finalReport [2]) = some 0 ∧
    mixedLayerRoot.bind (finalReport [2]) = none ∧
    finalReport [2] (layeredTargetSummary 2 (.ap .a) .normal 0) = none := by decide

def sinkCatalog : List SinkKey := [⟨10, 3⟩, ⟨10, 4⟩, ⟨11, 3⟩]
theorem ids_interned_by_location_and_rule :
    internSink sinkCatalog ⟨10, 3⟩ = some 0 ∧
    internSink sinkCatalog ⟨10, 4⟩ = some 1 ∧
    internSink sinkCatalog ⟨11, 3⟩ = some 2 := by decide

theorem registry_reuses_same_key_and_separates_other_rules :
    registerSink [] ⟨10, 3⟩ = (0, [⟨10, 3⟩]) ∧
    registerSink [⟨10, 3⟩] ⟨10, 3⟩ = (0, [⟨10, 3⟩]) ∧
    registerSink [⟨10, 3⟩] ⟨10, 4⟩ = (1, [⟨10, 3⟩, ⟨10, 4⟩]) ∧
    registerSink [⟨10, 3⟩, ⟨10, 4⟩] ⟨10, 3⟩ = (0, [⟨10, 3⟩, ⟨10, 4⟩]) := by decide

theorem same_sink_witnesses_share_id_not_premise :
    internedSinkTarget sinkCatalog ⟨10, 3⟩ 0 (.ap .a) .normal =
      some (layeredTargetSummary 0 (.ap .a) .normal 0) ∧
    internedSinkTarget sinkCatalog ⟨10, 3⟩ 0 (.ap .b) .normal =
      some (layeredTargetSummary 0 (.ap .b) .normal 0) ∧
    internedSinkTarget sinkCatalog ⟨10, 4⟩ 0 (.ap .a) .normal =
      some (layeredTargetSummary 0 (.ap .a) .normal 1) ∧
    internedSinkTarget sinkCatalog ⟨10, 3⟩ 0 (.ap .a) .demand =
      internedSinkTarget sinkCatalog ⟨10, 4⟩ 0 (.ap .a) .demand := by decide

def dedupSummaries : List Summary → List Summary
  | [] => []
  | s :: rest => if s ∈ rest then dedupSummaries rest else s :: dedupSummaries rest

theorem ids_participate_in_summary_dedup :
    (dedupSummaries [layeredTargetSummary 0 (.ap .a) .normal 0,
      layeredTargetSummary 0 (.ap .a) .normal 0]).length = 1 ∧
    (dedupSummaries [layeredTargetSummary 0 (.ap .a) .normal 0,
      layeredTargetSummary 0 (.ap .a) .normal 1]).length = 2 ∧
    (dedupSummaries [layeredTargetSummary 0 (.ap .a) .normal 0,
      layeredTargetSummary 0 (.ap .b) .normal 0]).length = 2 := by decide

theorem final_reports_dedup_same_id_keep_distinct_ids :
    collectReports [2] [layeredTargetSummary 2 .zero .normal 0,
      layeredTargetSummary 2 .zero .normal 0] = [0] ∧
    (collectReports [2] [layeredTargetSummary 2 .zero .normal 0,
      layeredTargetSummary 2 .zero .normal 1,
      layeredTargetSummary 2 .zero .normal 0]).length = 2 := by decide

theorem zero_exit_retains_normal_id_without_local_report :
    c5Restrict exactEntry exactExit sinkIncoming (layeredTargetSummary 0 (.ap .a) .normal 7) =
      some (layeredTargetSummary 0 (.ap .a) .normal 7) ∧
    (c5Restrict exactEntry exactExit sinkIncoming (layeredTargetSummary 0 (.ap .a) .normal 7)).bind
      (finalReport [2]) = none := by decide

theorem normal_target_selection_overrides_old_nd_zero_exceptions :
    selectHandoff (fun _ _ => true) .forward (layeredTargetSummary 0 (.both .a .b) .normal) = none ∧
    selectHandoff (fun _ _ => true) .backward (layeredTargetSummary 0 .zero .normal) = none := by decide


def terminalRoute : Need [sink] bindings incoming .forward 0 (.ap .a) 10 :=
  .terminal sink (by simp) (by decide)
def callerRoute : Need [sink] bindings incoming .forward 1 (.ap .b) 10 :=
  .caller nonreturning (by simp [bindings]) terminalRoute (by decide)
def rootRoute : Need [sink] bindings incoming .forward 2 .zero 10 :=
  .caller rootCall (by simp [bindings]) callerRoute (by decide)

theorem sink_chain_exact_support :
    chain = [handoffTarget 0 (.ap .a), handoffTarget 1 (.ap .b), handoffTarget 2 .zero] := by decide

theorem unrelated_method_has_no_guidance :
    emittedZero .restricted chain 3 .zero = [] := by decide

theorem needed_chain_zero_guided :
    emittedZero .restricted chain 0 .zero = [.zero] ∧
    emittedZero .restricted chain 1 .zero = [.zero] ∧
    emittedZero .restricted chain 2 .zero = [.zero] := by decide

def rootCaptured := closeCapturesNeed rootRoute

def normalReturnOnlyChain : List Demand :=
  close incoming (bindings.filter Binding.normalReturn) 3 (seedDemands incoming [sink])
theorem nonreturning_lost_by_return_only :
    handoffTarget 1 (.ap .b) ∉ normalReturnOnlyChain := by decide

def missingCallerZeroExit : List Demand := [⟨0, .ap .a, .zero⟩, ⟨1, .ap .b, .ap .b⟩]
def unsupportedChain : List Demand :=
  close missingCallerZeroExit bindings 3 (seedDemands missingCallerZeroExit [sink])
theorem caller_zero_exit_support_required :
    handoffTarget 0 (.ap .a) ∈ unsupportedChain ∧
    handoffTarget 1 (.ap .b) ∉ unsupportedChain := by decide

def source : Terminal := ⟨.backward, 0, .ap .a, 20⟩
def sourceChain : List Demand := close incoming bindings 3 (seedDemands incoming [source])
def sourceTerminalRoute : Need [source] bindings incoming .backward 0 (.ap .a) 20 :=
  .terminal source (by simp) (by decide)
def sourceCallerRoute : Need [source] bindings incoming .backward 1 (.ap .b) 20 :=
  .caller nonreturning (by simp [bindings]) sourceTerminalRoute (by decide)
def sourceRootRoute : Need [source] bindings incoming .backward 2 .zero 20 :=
  .caller rootCall (by simp [bindings]) sourceCallerRoute (by decide)

theorem source_chain_exact_support : sourceChain = chain := by decide

def secondSite : Terminal := ⟨.forward, 0, .ap .a, 11⟩
theorem demand_targets_anonymously_collapse_sites :
    sink ≠ secondSite ∧ sink.summary = secondSite.summary ∧
    (dedupDemands (seedDemands incoming [sink, secondSite])).length = 1 := by decide

def otherOrigin : Terminal := ⟨.forward, 0, .ap .c, 10⟩
def multiIncoming : List Demand := incoming ++ [⟨0, .ap .c, .zero⟩]
def multiOrigin : List Demand := close multiIncoming bindings 3
  (seedDemands multiIncoming [sink, otherOrigin])
theorem distinct_premises_preserved :
    handoffTarget 0 (.ap .a) ∈ multiOrigin ∧ handoffTarget 0 (.ap .c) ∈ multiOrigin := by decide

/-- Under the isolated demand-row route, excluding NORMAL ZERO ordinary rows
    loses both seed->forward and GEN->backward Target cycles. Record replay may
    provide an alternative production certificate; it is outside this theorem. -/
def demandOnlyExport (summaries : List Summary) : List Demand :=
  (summaries.filter fun s => s.layer == .demand).map handoff

theorem normal_zero_ordinary_row_needed_by_demand_route :
    demandOnlyExport [sinkSeed] = [] ∧ demandOnlyExport [sourceGen] = [] ∧
    targetAllowed (demandOnlyExport [sinkSeed]) 0 (.ap .a) = false ∧
    targetAllowed (demandOnlyExport [sourceGen]) 0 (.ap .b) = false := by decide

theorem normal_zero_handoff_and_stop_are_distinct :
    continuationRelevant sinkSeed = false ∧
    continuationRelevant sourceGen = false ∧
    handoff sinkSeed = sinkIncoming ∧ handoff sourceGen = sourceIncoming := by decide

theorem explicit_zero_zero_row_preserved :
    handoff ⟨0, .zero, .zero, .normal⟩ = ⟨0, .zero, .zero⟩ ∧
    emittedZero .restricted [handoff ⟨0, .zero, .zero, .normal⟩] 0 .zero = [.zero] := by decide

/-- A later source-triggered ZERO requires the same transfer/continuation effects
    as an earlier guided ZERO before owner-only memo reuse is justified. -/
structure ZeroEvent where
  owner : Nat
  sourceEnabled : Bool
  deriving DecidableEq, Repr
def zeroEffects (e : ZeroEvent) : List Demand :=
  if e.sourceEnabled then [handoffTarget e.owner .zero] else []
def processZeroEvents : List Nat → List ZeroEvent → List Demand
  | _, [] => []
  | seen, event :: rest =>
      if event.owner ∈ seen then processZeroEvents seen rest
      else zeroEffects event ++ processZeroEvents (event.owner :: seen) rest
def guideThenSource : List ZeroEvent := [⟨0, false⟩, ⟨0, true⟩]
theorem source_zero_effect_lost_without_subsumption :
    processZeroEvents [] guideThenSource = [] ∧
      guideThenSource.flatMap zeroEffects = [handoffTarget 0 .zero] := by decide
theorem zero_reuse_safe_for_local_effects (old later : ZeroEvent)
    (subsumes : zeroEffects later = zeroEffects old) :
    ∀ d, d ∈ zeroEffects later → d ∈ zeroEffects old := by
  intro d present
  rw [← subsumes]
  exact present

def checks : Bool :=
  decide (forwardSinkTarget 0 (.ap .a) .normal = layeredTargetSummary 0 (.ap .a) .normal) &&
  decide (forwardSinkTarget 0 (.ap .a) .demand = sinkTarget) &&
  decide (selectedTargetHandoff (forwardSinkTarget 0 (.ap .a) .normal) = none) &&
  decide (continuationRelevant sinkTarget = true) &&
  decide (c5Accept exactEntry exactExit sinkIncoming sinkTarget = true) &&
  decide (c5Accept exactEntry exactExit sourceIncoming sourceTarget = true) &&
  decide (c5Accept exactEntry exactExit sinkReverse sinkSeed = true) &&
  decide (c5Accept exactEntry exactExit sourceReverse sourceGen = true) &&
  decide (emittedZero .restricted chain 3 .zero = []) &&
  decide (handoffTarget 1 (.ap .b) ∉ normalReturnOnlyChain) &&
  decide (handoffTarget 1 (.ap .b) ∉ unsupportedChain) &&
  decide (normalReportRoot.bind (finalReport [2]) = some 0) &&
  decide (internSink sinkCatalog ⟨10, 4⟩ = some 1) &&
  decide ((collectReports [2] [layeredTargetSummary 2 .zero .normal 0,
    layeredTargetSummary 2 .zero .normal 1]).length = 2)
theorem checks_pass : checks = true := rfl

end Controls

#print axioms target_entry_zero_only
#print axioms zero_exit_target_preserved
#print axioms c5_accept_target_iff
#print axioms c5_target_label_preserved
#print axioms final_report_iff
#print axioms demand_target_never_reports
#print axioms c5_target_does_not_create_root_report
#print axioms generated_target_well_formed
#print axioms normal_callee_target_normal_caller
#print axioms demand_target_persists_anonymously
#print axioms composed_target_layer_is_ordinary_join
#print axioms selected_target_survives_zero_reach_gate
#print axioms target_initial_zero_only
#print axioms NormalSinkTargetNormal
#print axioms DemandSinkTarget
#print axioms record_replay_cannot_create_gen_target
#print axioms conditional_transfer_cannot_create_gen_target
#print axioms accepted_gen_target_precedes_downstream_filter
#print axioms normalTargetNotSelected
#print axioms demandTargetSelected
#print axioms normal_target_overrides_ordinary_selection
#print axioms normal_callee_target_demand_caller
#print axioms continuationTargetPositive
#print axioms normalTargetNotContinuation
#print axioms closeCapturesNeed
#print axioms Controls.rootCaptured
#print axioms Controls.historical_mixed_layer_promotion_chain
#print axioms Controls.historical_early_selection_loses_reference_promotion
#print axioms Controls.ids_interned_by_location_and_rule
#print axioms Controls.ids_participate_in_summary_dedup
#print axioms Controls.final_reports_dedup_same_id_keep_distinct_ids
#print axioms Controls.normal_call_chain_retains_id_and_reports_only_at_zero_root
#print axioms Controls.checks_pass
#eval Controls.checks

end TargetZeroKernel
