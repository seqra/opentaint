/-
  An admission audit, not an implementation proposal.

  The original restricted emitter copies the actual mark and intersects its
  geometry with demand. F72's shared emitter replaces an abstract demand by
  its FLOW form. No persistent "completed initial" cache is proposed here.

  A handled initial is ghost history only. A NORMAL summary is a completed
  relation, not proof that every output of its initial is completed. The small
  counterexample below makes that difference explicit.

  Code under analysis:
      helper(p, b) { if (b) return p; else return p.H; }

  Scope: one named field H, one full mark T, no statics, exclusions, ND,
  cleaners or type filters. NORMAL concrete ANY denotes MUST; DEMAND concrete
  ANY denotes a may requirement. The initial/transfer rows used here do not
  involve the legacy concrete-STAR-start difference.
-/
import ApSpec.AnyTaintExDefs
import ApSpec.AbsDefs

namespace ApSpec.InitialEmissionAdmissionHistory
open ApSpec ApSpec.Reverse ApSpec.Handoff ApSpec.AnyTaintEx ApSpec.Abs

def p : Base := 1
def ret : Base := 2
def H : Acc := 7
def T : Mark := 1

def initial : PFact := ⟨p, [], .star Excl.empty, .star⟩
def normalCopy : PFact := ⟨ret, [], .star Excl.empty, .star⟩
def unfinishedRead : PFact := ⟨ret, [], .any, .star⟩
def source : XFact := ⟨⟨⟨p, [], .any, .conc T⟩, false⟩, Excl.empty⟩
def demand : PFact := ⟨p, [], .any, .star⟩

def rootCopy : MicroEdge := (initial, normalCopy)
def fieldRead : MicroEdge := (⟨p, [H], .star Excl.empty, .star⟩, normalCopy)

def handle (input : XFact) : List XFact :=
  (bindX input rootCopy).facts ++ (bindX input fieldRead).facts

theorem handled_initial_has_mixed_outputs :
    handle ⟨⟨initial, false⟩, Excl.empty⟩ =
      [⟨⟨normalCopy, false⟩, Excl.empty⟩,
       ⟨⟨unfinishedRead, true⟩, Excl.empty⟩] := by decide

def fromLocation : Loc := ⟨p, [H], T⟩
def toLocation : Loc := ⟨ret, [], T⟩

/-- A concrete witness for the field-read branch. -/
theorem field_branch_witness : den initial unfinishedRead fromLocation toLocation := by
  refine ⟨rfl, rfl, True.intro, rfl, True.intro, [H], [], rfl, rfl, rfl, True.intro⟩

/-- The NORMAL root-copy relation has correlated suffixes. It does not cover
    the field-read pair p.H/T -> ret/T. -/
theorem completed_copy_does_not_cover_field_read :
    ¬ den initial normalCopy fromLocation toLocation := by
  rintro ⟨_, _, _, _, _, s, t, hs, ht, _, hc⟩
  have hs' : s = [H] := by simpa [fromLocation, initial] using hs.symm
  have ht' : t = [] := by simpa [toLocation, normalCopy] using ht.symm
  have same : t = s := hc.1
  rw [hs', ht'] at same
  cases same

/-- This is diagnostic history, not a proposed runtime object. It keeps the
    three facts that a single "handled" bit would incorrectly collapse. -/
structure History where
  handled : List PFact
  normal : List (PFact × PFact)
  pending : List (PFact × PFact)

def previous : History := ⟨[initial], [(initial, normalCopy)], [(initial, unfinishedRead)]⟩

def blindSuppression (h : History) (j : PFact) : List PFact :=
  if h.handled.contains j then [] else [j]

theorem blind_suppression_drops_unfinished_work :
    blindSuppression previous initial = [] ∧
    previous.pending = [(initial, unfinishedRead)] ∧
    den initial unfinishedRead fromLocation toLocation ∧
    ¬ den initial normalCopy fromLocation toLocation :=
  ⟨by decide, rfl, field_branch_witness, completed_copy_does_not_cover_field_read⟩

/-- Original emitM/emitX keeps the concrete mark. emitTX also keeps the actual
    MUST flag, because both the offered fact and emitted premise are ANY. -/
theorem original_vs_f72_admission :
    emitTX emitX demand source.af.fact true source.ex =
      some (source.af.fact, true, Excl.empty) ∧
    emitW demand source.af.fact = some initial := by decide

theorem original_forward_start_keeps_actual_must :
    startX source.af.fact true Excl.empty = source := by decide

theorem actual_must_finishes_normal :
    handle source =
      [⟨⟨⟨ret, [], .any, .conc T⟩, false⟩, Excl.empty⟩,
       ⟨⟨⟨ret, [], .any, .conc T⟩, false⟩, Excl.empty⟩] := by decide

/-- Original admission does not re-emit the old FLOW initial. This follows
    from preserving the offered mark, without a cross-run admission cache. -/
theorem original_does_not_emit_previous_flow_initial :
    (emitTX emitX demand source.af.fact true source.ex).map (fun x => x.1) ≠
      some initial := by decide

def backwardDemand : PFact := ⟨ret, [], .any, .star⟩
def backwardPacket : XFact := ⟨⟨⟨ret, [], .any, .conc T⟩, true⟩, Excl.empty⟩

/-- A backward may packet stays MAY under the original emitter. The MUST
    property of the actual forward source is not inferred for this packet. -/
theorem original_backward_keeps_may :
    emitTX emitX backwardDemand backwardPacket.af.fact false backwardPacket.ex =
      some (backwardPacket.af.fact, false, Excl.empty) ∧
    startX backwardPacket.af.fact false Excl.empty = backwardPacket := by decide

/-- A checked local ANY-refinement test, not a selected full admission policy.
    It checks three candidate progress cases in this local model:
      * more certainty: a concrete MUST fact;
      * an EXACT location;
      * a strictly longer known field prefix.
    Merely choosing a concrete mark is not field refinement. A same-prefix
    STAR is not field refinement either. Nonempty exclusions and multi-path
    trees are outside this small test's scope. -/
def strictAnyRefinement (d : PFact) (emitted : XFact) : Bool :=
  d.kind.isAny && coversB d emitted.af.fact &&
    (carriesB emitted.af || emitted.af.fact.kind == .exact ||
      match dropPrefix d.path emitted.af.fact.path with
      | some (_ :: _) => true
      | _ => false)

def mayAtRoot : XFact := ⟨⟨source.af.fact, true⟩, Excl.empty⟩
def exactAtRoot : XFact := ⟨⟨⟨p, [], .exact, .conc T⟩, false⟩, Excl.empty⟩
def mayAtField : XFact := ⟨⟨⟨p, [H], .any, .conc T⟩, true⟩, Excl.empty⟩
def correlatedAtRoot : XFact := ⟨⟨⟨p, [], .star Excl.empty, .conc T⟩, true⟩, Excl.empty⟩

theorem strict_any_refinement_witnesses :
    strictAnyRefinement demand source = true ∧
    strictAnyRefinement demand exactAtRoot = true ∧
    strictAnyRefinement demand mayAtField = true ∧
    strictAnyRefinement demand mayAtRoot = false ∧
    strictAnyRefinement demand ⟨⟨initial, false⟩, Excl.empty⟩ = false ∧
    strictAnyRefinement demand correlatedAtRoot = false := by decide

theorem original_emission_preserves_refining_prefix :
    emitTX emitX demand mayAtField.af.fact false Excl.empty =
      some (mayAtField.af.fact, false, Excl.empty) ∧
    strictAnyRefinement demand mayAtField = true := by decide

/-- A nonrefining may requirement can still carry an essential source-hit
    witness. This is the local step in the runtime case:
        main() { sink(helper()); }
        helper() { return sourceAll(); }
    It does not prove a complete source-discovery replacement policy. -/
def fullSource : MicroEdge := (zeroFact, ⟨ret, [], .any, .conc T⟩)
def reversedSource : MicroEdge := revEdge fullSource.1 fullSource.2
def sourceHitDemand : PFact := ⟨ret, [], .any, .conc T⟩

theorem backward_nonrefining_source_hit :
    strictAnyRefinement sourceHitDemand backwardPacket = false ∧
    emitTX emitX sourceHitDemand backwardPacket.af.fact false Excl.empty =
      some (backwardPacket.af.fact, false, Excl.empty) ∧
    (bindX backwardPacket reversedSource).facts =
      [⟨⟨zeroFact, true⟩, Excl.empty⟩] := by decide

def sourceWitness : Loc := ⟨ret, [], T⟩

theorem unchanged_may_has_shared_witness :
    sourceHitDemand.covers sourceWitness ∧
    backwardPacket.af.fact.covers sourceWitness := by
  constructor
  · exact ⟨rfl, ⟨[], rfl, True.intro⟩, rfl⟩
  · exact ⟨rfl, ⟨[], rfl, True.intro⟩, rfl⟩

/-- Local forward observation obligation for an unchanged may input:
        main() { check(mayModel(sourceT())); }
        check(p) { sinkT(p); }
    This proves the sink-check step, not whole-report loss under a new gate.
    A complete admission policy must preserve observations as well as return
    summaries and source hits. -/
def sinkEntry : PFact := ⟨p, [], .any, .conc T⟩
def sinkPattern : PFact := ⟨p, [], .exact, .conc T⟩

theorem forward_nonrefining_sink_observation :
    strictAnyRefinement sinkEntry mayAtRoot = false ∧
    emitTX emitX sinkEntry mayAtRoot.af.fact false Excl.empty =
      some (mayAtRoot.af.fact, false, Excl.empty) ∧
    checkX sinkEntry mayAtRoot sinkPattern = .triggered := by decide

def check : Bool :=
  blindSuppression previous initial == [] &&
  emitW demand source.af.fact == some initial &&
  emitTX emitX demand source.af.fact true source.ex == some (source.af.fact, true, Excl.empty) &&
  (handle source).all (fun x => !x.af.demand)

theorem checked : check = true := by decide

#eval check
#print axioms blind_suppression_drops_unfinished_work
#print axioms original_vs_f72_admission
#print axioms original_does_not_emit_previous_flow_initial
#print axioms original_backward_keeps_may
#print axioms strict_any_refinement_witnesses
#print axioms backward_nonrefining_source_hit
#print axioms forward_nonrefining_sink_observation

end ApSpec.InitialEmissionAdmissionHistory
