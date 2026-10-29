/-
  OwaspDemandCycleTest: an executable, local transfer model.

  Scope: the helper has one parameter, one named storage accessor H, one full
  mark T, empty exclusions, no ND edges, statics, cleaners or type filters.
  A list contains alternative derivations, not the packed JVM field tree.
  bindX is reused only on FLOW facts and NORMAL whole-object concrete facts;
  its historical concrete-STAR normalization is outside this transfer scope.
  Current initial STAR handling is stated separately below.

  This model does not claim a complete JVM-driver or interprocedural proof.
  The concrete fixture tests the driver. This file checks the local cause of
  its recurring selected helper row, C2, C5, handoff and precise record branch.
  Each modeled round starts fresh with the submitted boundary packets captured
  from the runtime trace. These packets are inputs, not consequences derived
  here from the caller or its persistent records. There is no admission-history
  state and no cross-round record application in this local recurrence.
  Thus its induction is not a theorem that a complete driver must repeat:
  it states that the same packets and demand reproduce the same local work.
-/
import ApSpec.AnyTaintExDefs
import ApSpec.AbsDefs

namespace ApSpec.InitialEmissionCycle
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.AnyTaintEx ApSpec.Abs

def p : Base := 1
def bytes : Base := 2
def out : Base := 3
def ret : Base := 4
def H : Acc := 7
def T : Mark := 1

def flow (b : Base) (path : List Acc := []) (k : Kind := .star Excl.empty) : PFact :=
  ⟨b, path, k, .star⟩

def xf (f : PFact) (demand : Bool := false) : XFact := ⟨⟨f, demand⟩, Excl.empty⟩

def move (b u : Base) (a z : List Acc := []) : MicroEdge :=
  (flow b a, flow u z)

def readEdges (storage : Bool) : List MicroEdge :=
  [move p bytes [] []] ++ if storage then [move p bytes [H] []] else []

def constructEdges (storage : Bool) : List MicroEdge :=
  [move bytes out [] []] ++ if storage then [move bytes out [] [H]] else []

def returnEdges : List MicroEdge := [move out ret [] []]

def applyMoves (es : List MicroEdge) (xs : List XFact) : List XFact :=
  xs.flatMap fun x => es.flatMap fun e => (bindX x e).facts

def fwd (storage : Bool) (seed : XFact) : List XFact :=
  applyMoves returnEdges (applyMoves (constructEdges storage) (applyMoves (readEdges storage) [seed]))

def reverseMoves (es : List MicroEdge) : List MicroEdge := es.map fun e => revEdge e.1 e.2

def bwd (storage : Bool) (seed : XFact) : List XFact :=
  applyMoves (reverseMoves (readEdges storage))
    (applyMoves (reverseMoves (constructEdges storage))
      (applyMoves (reverseMoves returnEdges) [seed]))

def actualSource : XFact := xf ⟨p, [], .any, .conc T⟩
def forwardSeed : XFact := xf (flow p)
def backwardSeed : XFact := xf (flow ret)

-- MAY and MUST have the same serialized path/tail/mark but different layers.
def actualMay : XFact := xf ⟨p, [], .any, .conc T⟩ true

theorem source_is_must_not_may : carriesB actualSource.af = true ∧
    carriesB actualMay.af = false ∧ actualSource ≠ actualMay := by decide

theorem all_micro_tails_star :
    ((readEdges true ++ constructEdges true ++ returnEdges).all fun e =>
      e.1.kind == .star Excl.empty && e.2.kind == .star Excl.empty) = true := by decide

theorem forward_edges : fwd true forwardSeed =
    [xf (flow ret), xf (flow ret [H]), xf (flow ret [] .any) true,
      xf (flow ret [H] .any) true] := by decide

theorem backward_edges : bwd true backwardSeed =
    [xf (flow p), xf (flow p [H]), xf (flow p [] .any) true,
      xf (flow p [H] .any) true] := by decide

/-- Current Kotlin initialFacts preserves a concrete STAR conclusion. The old
    startX delegates to Basic.startFact, which changes it to ANY. Do not use
    that historical row for current concrete-STAR initial proofs. -/
def currentStart (j : PFact) (must : Bool := false) : XFact :=
  if must then xf j else
    match j.kind, j.mark with
    | .star _, .conc _ => xf j true
    | _, _ => ⟨startFact j, Excl.empty⟩

theorem current_concrete_star_start :
    currentStart ⟨p, [], .star Excl.empty, .conc T⟩ =
      xf ⟨p, [], .star Excl.empty, .conc T⟩ true ∧
    startX ⟨p, [], .star Excl.empty, .conc T⟩ false Excl.empty =
      xf ⟨p, [], .any, .conc T⟩ true := by decide

theorem current_flow_and_exact_start :
    currentStart (flow p) = forwardSeed ∧
    currentStart ⟨p, [], .exact, .conc T⟩ = xf ⟨p, [], .exact, .conc T⟩ ∧
    currentStart ⟨p, [], .any, .conc T⟩ true = actualSource := by decide

theorem limit_root (L b : Nat) (k : Kind) (m : MarkA) (d : Bool) :
    limitFX (fun _ => true) (L + 1) (xf ⟨b, [], k, m⟩ d) =
      xf ⟨b, [], k, m⟩ d := rfl

theorem limit_one (L b : Nat) (k : Kind) (m : MarkA) (d : Bool) :
    limitFX (fun _ => true) (L + 1) (xf ⟨b, [H], k, m⟩ d) =
      xf ⟨b, [H], k, m⟩ d := rfl

def readStage : List XFact := applyMoves (readEdges true) [forwardSeed]
def constructStage : List XFact := applyMoves (constructEdges true) readStage
def returnStage : List XFact := applyMoves returnEdges constructStage

theorem read_stage : readStage =
    [xf (flow bytes), xf (flow bytes [] .any) true] := by decide

theorem construct_stage : constructStage =
    [xf (flow out), xf (flow out [H]), xf (flow out [] .any) true,
      xf (flow out [H] .any) true] := by decide

/-- Every intermediate result fits every limit in the real run schedule.
    Raising the limit cannot remove the ancestor-loss approximation here. -/
theorem cuts_do_nothing (L : Nat) :
    readStage.map (limitFX (fun _ => true) (L + 1)) = readStage ∧
    constructStage.map (limitFX (fun _ => true) (L + 1)) = constructStage ∧
    returnStage.map (limitFX (fun _ => true) (L + 1)) = returnStage := by
  rw [read_stage, construct_stage]
  change _ ∧ _ ∧ (fwd true forwardSeed).map _ = fwd true forwardSeed
  rw [forward_edges]
  simp only [List.map_cons, List.map_nil, flow, limit_root, limit_one, and_self]

def reverseReturnStage : List XFact := applyMoves (reverseMoves returnEdges) [backwardSeed]
def reverseConstructStage : List XFact :=
  applyMoves (reverseMoves (constructEdges true)) reverseReturnStage
def reverseReadStage : List XFact :=
  applyMoves (reverseMoves (readEdges true)) reverseConstructStage

theorem reverse_return_stage : reverseReturnStage = [xf (flow out)] := by decide
theorem reverse_construct_stage : reverseConstructStage =
    [xf (flow bytes), xf (flow bytes [] .any) true] := by decide

theorem backward_cuts_do_nothing (L : Nat) :
    reverseReturnStage.map (limitFX (fun _ => true) (L + 1)) = reverseReturnStage ∧
    reverseConstructStage.map (limitFX (fun _ => true) (L + 1)) = reverseConstructStage ∧
    reverseReadStage.map (limitFX (fun _ => true) (L + 1)) = reverseReadStage := by
  rw [reverse_return_stage, reverse_construct_stage]
  change _ ∧ _ ∧ (bwd true backwardSeed).map _ = bwd true backwardSeed
  rw [backward_edges]
  simp only [List.map_cons, List.map_nil, flow, limit_root, limit_one, and_self]

def boundedMoves (L : Nat) (es : List MicroEdge) (xs : List XFact) : List XFact :=
  (applyMoves es xs).map (limitFX (fun _ => true) L)

def boundedFwd (L : Nat) (seed : XFact) : List XFact :=
  boundedMoves L returnEdges
    (boundedMoves L (constructEdges true) (boundedMoves L (readEdges true) [seed]))

def boundedBwd (L : Nat) (seed : XFact) : List XFact :=
  boundedMoves L (reverseMoves (readEdges true))
    (boundedMoves L (reverseMoves (constructEdges true))
      (boundedMoves L (reverseMoves returnEdges) [seed]))

theorem bounded_forward_eq (L : Nat) :
    boundedFwd (L + 1) forwardSeed = fwd true forwardSeed := by
  have h := cuts_do_nothing L
  change (applyMoves returnEdges
    ((applyMoves (constructEdges true)
      (readStage.map (limitFX (fun _ => true) (L + 1)))).map
        (limitFX (fun _ => true) (L + 1)))).map _ = _
  rw [h.1]
  change (applyMoves returnEdges (constructStage.map _)).map _ = _
  rw [h.2.1]
  exact h.2.2

theorem bounded_backward_eq (L : Nat) :
    boundedBwd (L + 1) backwardSeed = bwd true backwardSeed := by
  have h := backward_cuts_do_nothing L
  change (applyMoves (reverseMoves (readEdges true))
    ((applyMoves (reverseMoves (constructEdges true))
      (reverseReturnStage.map (limitFX (fun _ => true) (L + 1)))).map
        (limitFX (fun _ => true) (L + 1)))).map _ = _
  rw [h.1]
  change (applyMoves (reverseMoves (readEdges true)) (reverseConstructStage.map _)).map _ = _
  rw [h.2.1]
  exact h.2.2

/-- On this fixture, ANY prefix coverage is the only tree-packing case.
    A STAR root must not remove an H.STAR relation: the common premise
    correlates the suffix and the relations have different images. -/
def strictCovers (a b : XFact) : Bool :=
  a != b && a.af.demand == b.af.demand && a.af.fact.kind.isAny &&
    b.af.fact.kind.isAny && coversB a.af.fact b.af.fact

def pack (xs : List XFact) : List XFact :=
  (xs.filter fun x => !xs.any fun y => strictCovers y x).eraseDups

theorem packed_forward : pack (fwd true forwardSeed) =
    [xf (flow ret), xf (flow ret [H]), xf (flow ret [] .any) true] := by decide

theorem packed_backward : pack (bwd true backwardSeed) =
    [xf (flow p), xf (flow p [H]), xf (flow p [] .any) true] := by decide

def fDemand : DemandEdge := ⟨flow p [] .any, some (flow ret)⟩
def bDemand : DemandEdge := ⟨flow ret [] .any, some (flow p)⟩

def publish (j : PFact) (d : DemandEdge) (xs : List XFact) : List XFact :=
  pack (xs.filterMap fun x => (restrictI j x.af d).map plain)

def handoff (j : PFact) (xs : List XFact) : List DemandEdge :=
  (xs.filter fun x => x.af.demand).map fun x => normDem ⟨x.af.fact, some j⟩

theorem c5_forward_and_handoff :
    publish (flow p) fDemand (fwd true forwardSeed) =
      [xf (flow ret), xf (flow ret [H]), xf (flow ret [] .any) true] ∧
    handoff (flow p) (publish (flow p) fDemand (fwd true forwardSeed)) = [bDemand] := by
  decide

theorem c5_backward_and_handoff :
    publish (flow ret) bDemand (bwd true backwardSeed) =
      [xf (flow p), xf (flow p [H]), xf (flow p [] .any) true] ∧
    handoff (flow ret) (publish (flow ret) bDemand (bwd true backwardSeed)) = [fDemand] := by
  decide

theorem precise_normal_backward_record :
    xf (flow p [H]) ∈ bwd true backwardSeed ∧
    restrictI (flow ret) (xf (flow p [H])).af bDemand = some (xf (flow p [H])).af ∧
    revEdge (flow ret) (flow p [H]) = (flow p [H], flow ret) ∧
    (xf (flow p [H])).af.demand = false := by decide

theorem coarse_demand_not_removed_by_normal_record :
    xf (flow p [] .any) true ∈ pack (bwd true backwardSeed) ∧
    strictCovers (xf (flow p [H])) (xf (flow p [] .any) true) = false ∧
    strictCovers (xf (flow p)) (xf (flow p [] .any) true) = false := by decide

-- Captured in the real test at B2/B4/B6/B8. This is a may requirement.
-- The forward packet is actualSource, a NORMAL MUST value, at F3/F5/F7/F9.
def actualBackward : XFact := xf ⟨ret, [], .any, .conc T⟩ true

def admit (d : DemandEdge) (actual : XFact) : Option PFact :=
  emitW d.din actual.af.fact

theorem actual_c2_packets :
    admit fDemand actualSource = some (flow p) ∧
    admit bDemand actualBackward = some (flow ret) ∧
    currentStart (flow p) = forwardSeed ∧
    currentStart (flow ret) = backwardSeed := by decide

theorem must_source_transfer_is_normal :
    (fwd true actualSource).all (fun x => !x.af.demand) = true := by decide

abbrev Relation := PFact × XFact

/-- C2, the actual helper transfers, C5 and native-layer storage. This is
    a method-local operator, not a replacement model for the whole driver. -/
def analyze (backward storage : Bool) (d : DemandEdge) (actual : XFact) : List Relation :=
  match admit d actual with
  | none => []
  | some j =>
    let results := if backward then bwd storage (currentStart j) else fwd storage (currentStart j)
    (publish j d results).map fun x => (j, x)

def nextDemand (relations : List Relation) : List DemandEdge :=
  (relations.filter fun x => x.2.af.demand).map fun x => normDem ⟨x.2.af.fact, some x.1⟩

def boundedAnalyze (backward : Bool) (L : Nat) (d : DemandEdge)
    (actual : XFact) : List Relation :=
  match admit d actual with
  | none => []
  | some j =>
    let results := if backward then boundedBwd L (currentStart j) else boundedFwd L (currentStart j)
    (publish j d results).map fun x => (j, x)

theorem bounded_forward_analysis_eq (L : Nat) :
    boundedAnalyze false (L + 1) fDemand actualSource =
      analyze false true fDemand actualSource := by
  unfold boundedAnalyze analyze
  rw [actual_c2_packets.1]
  simp only [Bool.false_eq_true, if_false]
  rw [actual_c2_packets.2.2.1]
  rw [bounded_forward_eq]

theorem bounded_backward_analysis_eq (L : Nat) :
    boundedAnalyze true (L + 1) bDemand actualBackward =
      analyze true true bDemand actualBackward := by
  unfold boundedAnalyze analyze
  rw [actual_c2_packets.2.1]
  simp only [if_true]
  rw [actual_c2_packets.2.2.2]
  rw [bounded_backward_eq]

def forwardStep (storage : Bool) (ds : List DemandEdge) : List DemandEdge :=
  ds.flatMap fun d => nextDemand (analyze false storage d actualSource)

def backwardStep (storage : Bool) (ds : List DemandEdge) : List DemandEdge :=
  ds.flatMap fun d => nextDemand (analyze true storage d actualBackward)

def round (storage : Bool) (ds : List DemandEdge) : List DemandEdge :=
  backwardStep storage (forwardStep storage ds)

def rounds (storage : Bool) : Nat → List DemandEdge → List DemandEdge
  | 0, ds => ds
  | n + 1, ds => rounds storage n (round storage ds)

theorem selected_forward_row :
    forwardStep true [fDemand] = [bDemand] := by decide

theorem selected_backward_row :
    backwardStep true [bDemand] = [fDemand] := by decide

theorem computed_round_fixed : round true [fDemand] = [fDemand] := by decide

/-- For any finite round bound, reset-without-admission-history keeps the
    same nonempty selected demand when supplied the captured packets.
    The JVM test separately checks actual runs 1 to 9. -/
theorem recurring_demand (n : Nat) : rounds true n [fDemand] = [fDemand] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change rounds true n (round true [fDemand]) = [fDemand]
    rw [computed_round_fixed]
    exact ih

theorem recurring_demand_nonempty (n : Nat) : rounds true n [fDemand] ≠ [] := by
  rw [recurring_demand]
  exact List.cons_ne_nil _ _

def boundedRound (forwardLimit backwardLimit : Nat) (ds : List DemandEdge) : List DemandEdge :=
  let bs := ds.flatMap fun d => nextDemand (boundedAnalyze false forwardLimit d actualSource)
  bs.flatMap fun d => nextDemand (boundedAnalyze true backwardLimit d actualBackward)

theorem bounded_round_fixed (Lf Lb : Nat) :
    boundedRound (Lf + 1) (Lb + 1) [fDemand] = [fDemand] := by
  unfold boundedRound
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [bounded_forward_analysis_eq]
  have hf : nextDemand (analyze false true fDemand actualSource) = [bDemand] := by decide
  rw [hf]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [bounded_backward_analysis_eq]
  decide

/-- Each schedule entry stores limit minus one; zero means field limit one.
    This includes the fixture's increasing schedule and a fixed limit one.
    Every round still receives the captured packets, without history. -/
def scheduledRounds (limits : Nat → Nat × Nat) : Nat → List DemandEdge
  | 0 => [fDemand]
  | n + 1 => boundedRound ((limits n).1 + 1) ((limits n).2 + 1) (scheduledRounds limits n)

theorem recurring_demand_any_schedule (limits : Nat → Nat × Nat) (n : Nat) :
    scheduledRounds limits n = [fDemand] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change boundedRound _ _ (scheduledRounds limits n) = _
    rw [ih]
    exact bounded_round_fixed _ _

theorem control_forward_has_no_demand : forwardStep false [fDemand] = [] := by decide

theorem control_empty_fixed : round false [] = [] := by decide

theorem control_converges (n : Nat) : rounds false (n + 1) [fDemand] = [] := by
  have empty : ∀ k, rounds false k [] = [] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      change rounds false k (round false []) = []
      rw [control_empty_fixed]
      exact ih
  change rounds false n (round false [fDemand]) = []
  have done : round false [fDemand] = [] := by decide
  rw [done]
  exact empty n

/-- An executable witness bundle, in addition to the unbounded-in-round-count
    proofs above. Six local rounds exceed the five forward runs in the test. -/
def check : Bool :=
  carriesB actualSource.af && !carriesB actualBackward.af &&
  admit fDemand actualSource == some (flow p) &&
  admit bDemand actualBackward == some (flow ret) &&
  rounds true 6 [fDemand] == [fDemand] &&
  rounds false 6 [fDemand] == [] &&
  (fwd true actualSource).all (fun x => !x.af.demand)

theorem checked : check = true := by decide

#eval check

#print axioms actual_c2_packets
#print axioms forward_edges
#print axioms backward_edges
#print axioms current_concrete_star_start
#print axioms cuts_do_nothing
#print axioms precise_normal_backward_record
#print axioms recurring_demand
#print axioms recurring_demand_any_schedule
#print axioms control_converges

end ApSpec.InitialEmissionCycle
