/- Original AP execution: cross-premise ANY instantiation, without StrongQueries. -/
import ApSpec.Run1FlowTaintCoverage
import ApSpec.CurrentDemand
import ApSpec.Run1SummaryAliasAdmission

namespace ApSpec.FlowBackedAp
open ApSpec ApSpec.Abs ApSpec.Run1FlowTaintCoverage

/-- The AP reducer returns exactly the same facts, requests and layers.
    Geometry and the concrete input are arbitrary; the covering output is ANY. -/
theorem any_summary_application (a : AFact) (ib ob : Base)
    (ip op : List Acc) (t : Mark) (xs : List Mark) (layer : Bool)
    (actual : a.fact.mark = .conc t) (allowed : memB t xs = false) :
    applySummary a (initial ib ip (.conc t)) ⟨anyFinal ob op (.conc t), layer⟩ =
    applySummary a (initial ib ip .star) ⟨anyFinal ob op (.starEx xs), layer⟩ := by
  simp [applySummary, applyEdge, initial, anyFinal, actual, markGate, markComp, allowed]

/-- ANY output containment is prefix containment of field paths, with the
    shorter FLOW path containing every marked descendant. Initial shapes
    stay equal. This is pair inclusion, not equality of output headers. -/
theorem any_output_prefix_covers
    (ib ob : Base) (ip fp suffix : List Acc) (t : Mark) (xs : List Mark)
    (allowed : memB t xs = false) (l0 l1 : Loc)
    (marked : den (initial ib ip (.conc t))
      (anyFinal ob (fp ++ suffix) (.conc t)) l0 l1) :
    den (initial ib ip .star) (anyFinal ob fp (.starEx xs)) l0 l1 := by
  obtain ⟨hb0, hb1, hm0, hm1, _, s, r, hp0, hp1, hi, _⟩ := marked
  have mark0 : l0.mark = t := hm0
  have mark1 : l1.mark = t := hm1
  refine ⟨hb0, hb1, trivial, ?_, ?_, s, suffix ++ r, hp0, ?_, hi, trivial⟩
  · change l1.mark = l0.mark
    exact mark1.trans mark0.symm
  · change memB l0.mark xs = false
    rw [mark0]
    exact allowed
  · simpa [anyFinal, List.append_assoc] using hp1

/-- Original demand emission also works when the actual marked requirement
    is strictly below the covering abstract ANY pattern. -/
theorem prefix_guide_start (b : Base) (p suffix : List Acc) (t : Mark) :
    emitW (anyFinal b p .star) ⟨b, p ++ suffix, .exact, .conc t⟩ =
      some (initial b p .star) := by
  cases suffix with
  | nil =>
    simp [emitW, emitM, anyFinal, initial, flowForm, relate,
      CoreAux.dropPrefix_some.mpr (List.append_nil p).symm, markMatchB, meetK, flowK]
  | cons a rest =>
    simp [emitW, emitM, anyFinal, initial, flowForm, relate,
      CoreAux.dropPrefix_some.mpr (rfl : p ++ a :: rest = p ++ a :: rest),
      markMatchB, admitsTailB, flowK]

/-- Finite reference for the geometry candidates of an annotated FLOW tree.
    Production visits prefix nodes along the single target path instead. -/
def coveringPaths (flowPaths : List (List Acc)) (taintPath : List Acc) : List (List Acc) :=
  flowPaths.filter (fun p => (dropPrefix p taintPath).isSome)

theorem coveringPaths_exact (paths : List (List Acc)) (target path : List Acc) :
    path ∈ coveringPaths paths target ↔ path ∈ paths ∧ ∃ suffix, target = path ++ suffix := by
  simp only [coveringPaths, List.mem_filter]
  constructor
  · rintro ⟨present, hp⟩
    cases he : dropPrefix path target with
    | none => simp [he] at hp
    | some suffix => exact ⟨present, suffix, CoreAux.dropPrefix_some.mp he⟩
  · rintro ⟨present, suffix, hp⟩
    exact ⟨present, by rw [CoreAux.dropPrefix_some.mpr hp]; rfl⟩

/-- One eligible output path in a FLOW tree is enough. The supplied path
    and suffix are the actual computed prefix witness, not chosen data. -/
theorem any_tree_output_covers
    (ib ob : Base) (ip : List Acc) (paths : List (List Acc))
    (path suffix : List Acc) (t : Mark) (excluded : List Acc → List Mark)
    (present : path ∈ paths) (allowed : memB t (excluded path) = false)
    (l0 l1 : Loc)
    (marked : den (initial ib ip (.conc t))
      (anyFinal ob (path ++ suffix) (.conc t)) l0 l1) :
    ∃ output, output ∈ coveringPaths paths (path ++ suffix) ∧
      den (initial ib ip .star) (anyFinal ob output (.starEx (excluded output))) l0 l1 := by
  exact ⟨path, (coveringPaths_exact paths (path ++ suffix) path).mpr
    ⟨present, suffix, rfl⟩,
    any_output_prefix_covers ib ob ip path suffix t (excluded path) allowed l0 l1 marked⟩

/-- A canonical leaf for the existing raw-summary alias classifier. Layers
    and exclusion headers do not affect that classifier. -/
def aliasCellLeaf (b : Run1SummaryAliasAdmission.Base) (p : List Nat)
    (tail : Run1SummaryAliasAdmission.Tail) (payload : Run1SummaryAliasAdmission.Payload) :
    Run1SummaryAliasAdmission.Leaf := ⟨⟨b, p, tail, .demand, [], []⟩, payload⟩

/-- The selected ANY FLOW is an effect even when its bases and paths agree:
    its output tail is not STAR. -/
theorem any_flow_alias_effect (ib ob : Run1SummaryAliasAdmission.Base) (ip op : List Nat) :
    Run1SummaryAliasAdmission.noMemoryEffect
      (aliasCellLeaf ib ip .star .flow) (aliasCellLeaf ob op .any .flow) = false := by
  simp [Run1SummaryAliasAdmission.noMemoryEffect, aliasCellLeaf]

/-- Equal bases are safe in this nonidentity ANY cell. The marked output
    path differs from the initial path; both raw summaries are effects.
    The FLOW prefix path need not equal the marked path. -/
theorem same_base_nonidentity_any_alias_effect
    (b : Run1SummaryAliasAdmission.Base) (ip fp tp : List Nat)
    (t : Run1SummaryAliasAdmission.Mark) (different : ip ≠ tp) :
    Run1SummaryAliasAdmission.noMemoryEffect
      (aliasCellLeaf b ip .star .flow) (aliasCellLeaf b fp .any .flow) = false ∧
    Run1SummaryAliasAdmission.noMemoryEffect
      (aliasCellLeaf b ip .star (.taint t)) (aliasCellLeaf b tp .any (.taint t)) = false := by
  constructor
  · exact any_flow_alias_effect b b ip fp
  · simp [Run1SummaryAliasAdmission.noMemoryEffect, aliasCellLeaf, different]

/-- A same-path marked output has a different alias class from ANY FLOW.
    Keep this exact annotated output in the scalar residual. -/
theorem same_path_any_alias_mismatch
    (b : Run1SummaryAliasAdmission.Base) (p : List Nat)
    (t : Run1SummaryAliasAdmission.Mark) (nonzero : b ≠ .zero) :
    Run1SummaryAliasAdmission.noMemoryEffect
      (aliasCellLeaf b p .star .flow) (aliasCellLeaf b p .any .flow) = false ∧
    Run1SummaryAliasAdmission.noMemoryEffect
      (aliasCellLeaf b p .star (.taint t)) (aliasCellLeaf b p .any (.taint t)) = true := by
  constructor
  · exact any_flow_alias_effect b b p p
  · simp [Run1SummaryAliasAdmission.noMemoryEffect, aliasCellLeaf, nonzero]

def containmentControls : List Bool := [
  decide (dropPrefix [10] [10,20] = some [20]),
  decide (dropPrefix [10,20] [10] = none),
  decide (dropPrefix [10] [30] = none),
  decide (emitW (anyFinal 2 [10] .star) ⟨2,[10,20],.exact,.conc 7⟩ =
    some (initial 2 [10] .star)),
  decide (coveringPaths [[10], [20,30]] [20,30,40] = [[20,30]]),
  decide (coveringPaths [[10], [20,30]] [20,40] = []),
  decide (coveringPaths [[], [20], [20,30]] [20,30,40] = [[], [20], [20,30]]),
  !Run1SummaryAliasAdmission.noMemoryEffect
    (aliasCellLeaf (.arg 0) [] .star .flow) (aliasCellLeaf (.arg 0) [10] .any .flow),
  !Run1SummaryAliasAdmission.noMemoryEffect
    (aliasCellLeaf (.arg 0) [] .star (.taint (.full 1 7)))
    (aliasCellLeaf (.arg 0) [10] .any (.taint (.full 1 7))),
  Run1SummaryAliasAdmission.noMemoryEffect
    (aliasCellLeaf (.arg 0) [] .star (.taint (.full 1 7)))
    (aliasCellLeaf (.arg 0) [] .any (.taint (.full 1 7)))
]

/-- Reversing the abstract guide uses the existing emitter's FLOW form. -/
theorem abstract_guide_start (b : Base) (p : List Acc) (t : Mark) :
    emitW (anyFinal b p .star) ⟨b, p, .exact, .conc t⟩ =
      some (initial b p .star) := by
  simp [emitW, emitM, anyFinal, initial, flowForm, relate,
    CoreAux.dropPrefix_some.mpr (List.append_nil p).symm, markMatchB, meetK, flowK]

/-- Explicit protected guides still select the original concrete emitter. -/
theorem protected_guide_start (b : Base) (p : List Acc) (t : Mark) :
    emitW (anyFinal b p (.conc t)) ⟨b, p, .exact, .conc t⟩ =
      some ⟨b, p, .exact, .conc t⟩ := by
  simp [emitW, emitM, anyFinal, relate,
    CoreAux.dropPrefix_some.mpr (List.append_nil p).symm, markMatchB, meetK]

#print axioms any_summary_application
#print axioms any_output_prefix_covers
#print axioms prefix_guide_start
#print axioms coveringPaths_exact
#print axioms any_tree_output_covers
#print axioms any_flow_alias_effect
#print axioms same_base_nonidentity_any_alias_effect
#print axioms same_path_any_alias_mismatch
#print axioms abstract_guide_start
#print axioms protected_guide_start
end ApSpec.FlowBackedAp
