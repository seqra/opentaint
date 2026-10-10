/-
  F72 store queries. The list scan is the concept. A maintained path index is the optimization.
  Both forms return the same members after the same exact test. Index construction is outside
  the query cost. This file does not prove the iteration or the whole tree implementation.
-/
import ApSpec.AbsDefs
import ApSpec.RestrictedStore
import ApSpec.PipelineStore

namespace ApSpec.Abs
open ApSpec ApSpec.Handoff ApSpec.Store

/-- F72 emission can succeed only where the earlier emission succeeds. -/
theorem emitW_local : RStore.EmitLocal emitW := by
  intro d a j h
  have he : emitM d a ≠ none := by
    intro hn
    have hw := emitW_eq_none.mpr hn
    rw [h] at hw
    cases hw
  cases hm : emitM d a with
  | none => exact False.elim (he hm)
  | some j0 => exact RStore.emitM_local d a j0 hm

#print axioms emitW_local

/-- The emission index loses no F72 result, including a shared FLOW premise. -/
theorem emitW_lookup_equiv {ds : List DemandEdge} {a j : PFact} :
    j ∈ (RStore.emitCands ds a).filterMap (fun d => emitW d.din a) ↔
      j ∈ ds.filterMap (fun d => emitW d.din a) :=
  RStore.emit_lookup_equiv emitW_local

#print axioms emitW_lookup_equiv

section Subscriptions
variable {ρ : Type}

/-- The exact replay test on a list of published summaries. -/
def replayScanW (prem : ρ → PFact) (pubs : List ρ) (a : PFact) : List ρ :=
  pubs.filter (fun p => satW (prem p) a)

/-- Replay from a maintained index. Both directions of the path query are necessary. -/
def replayIndexW (prem : ρ → PFact) (idx : PathMap ρ) (a : PFact) : List ρ :=
  (around idx (keyB a)).filter (fun p => satW (prem p) a)

/-- The exact delivery test on a list of subscriptions. -/
def deliverScanW (fact : ρ → PFact) (subs : List ρ) (j : PFact) : List ρ :=
  subs.filter (fun s => satW j (fact s))

/-- Delivery uses the same union of path query directions. -/
def deliverIndexW (fact : ρ → PFact) (idx : PathMap ρ) (j : PFact) : List ρ :=
  (around idx (keyB j)).filter (fun s => satW j (fact s))

theorem replayW_complete {prem : ρ → PFact} {pubs : List ρ} {a : PFact} {p : ρ}
    (hp : p ∈ pubs) (hs : satW (prem p) a = true) :
    p ∈ around (indexBy (fun x => keyB (prem x)) pubs) (keyB a) := by
  rcases satW_cases hs with hs | ⟨_, hs⟩
  · exact PipelineStore.record_lookup hp (Or.inl hs)
  · exact PipelineStore.record_lookup hp (Or.inr hs)

#print axioms replayW_complete

theorem deliverW_complete {fact : ρ → PFact} {subs : List ρ} {j : PFact} {s : ρ}
    (hs : s ∈ subs) (hm : satW j (fact s) = true) :
    s ∈ around (indexBy (fun x => keyB (fact x)) subs) (keyB j) := by
  apply mem_around_indexBy.mpr
  refine ⟨hs, ?_⟩
  rcases satW_cases hm with hm | ⟨_, hm⟩
  · obtain ⟨hb, r, hr⟩ := PipelineStore.satI_parts hm
    exact Or.inl ⟨r, by simp only [keyB, hb, hr, List.cons_append]⟩
  · obtain ⟨hb, r, hr⟩ := applicable_parts hm
    exact Or.inr ⟨r, by simp only [keyB, hb, hr, List.cons_append]⟩

#print axioms deliverW_complete

/-- Functional equivalence is set equality. Query order and duplicate removal are immaterial. -/
theorem replayW_equiv {prem : ρ → PFact} {pubs : List ρ} {a : PFact} {p : ρ} :
    p ∈ replayIndexW prem (indexBy (fun x => keyB (prem x)) pubs) a ↔
      p ∈ replayScanW prem pubs a := by
  simp only [replayIndexW, replayScanW, List.mem_filter]
  exact ⟨fun ⟨hp, hm⟩ => ⟨(mem_around_indexBy.mp hp).1, hm⟩,
    fun ⟨hp, hm⟩ => ⟨replayW_complete hp hm, hm⟩⟩

#print axioms replayW_equiv

theorem deliverW_equiv {fact : ρ → PFact} {subs : List ρ} {j : PFact} {s : ρ} :
    s ∈ deliverIndexW fact (indexBy (fun x => keyB (fact x)) subs) j ↔
      s ∈ deliverScanW fact subs j := by
  simp only [deliverIndexW, deliverScanW, List.mem_filter]
  exact ⟨fun ⟨hs, hm⟩ => ⟨(mem_around_indexBy.mp hs).1, hm⟩,
    fun ⟨hs, hm⟩ => ⟨deliverW_complete hs hm, hm⟩⟩

#print axioms deliverW_equiv

/-- The indexed form pays one exact test per candidate; the concept pays one per stored item.
    The path walk has a separate cost (Store.lean and RestrictedStore.near_query_cost). -/
theorem replayW_test_cost (prem : ρ → PFact) (pubs : List ρ) (a : PFact) :
    (filterCount (fun p => satW (prem p) a) pubs).2 = pubs.length ∧
    (filterCount (fun p => satW (prem p) a)
      (around (indexBy (fun x => keyB (prem x)) pubs) (keyB a))).2 =
      (around (indexBy (fun x => keyB (prem x)) pubs) (keyB a)).length :=
  ⟨filterCount_snd, filterCount_snd⟩

#print axioms replayW_test_cost
end Subscriptions

namespace IndexCases
def j : PFact := ⟨1, [], .star Excl.empty, .star⟩
def a : PFact := ⟨1, [4], .exact, .conc 7⟩

/-- The F71 replay query alone misses a valid F72 FLOW summary. -/
theorem replay_needs_prefix :
    satW j a = true ∧
    (indexBy keyB [j]).lookupExtensions (keyB a) = [] ∧
    replayIndexW id (indexBy keyB [j]) a = [j] := by decide

#print axioms replay_needs_prefix

/-- The F71 delivery query alone misses the matching subscription. -/
theorem delivery_needs_extension :
    satW j a = true ∧
    (indexBy keyB [a]).lookupPrefixes (keyB j) = [] ∧
    deliverIndexW id (indexBy keyB [a]) j = [a] := by decide

#print axioms delivery_needs_extension

def pubs : List PFact := j :: (List.range 32).map (fun b => ⟨b + 2, [], .exact, .conc 7⟩)

/-- Practical cost scope: a stored index tests one candidate instead of all 33 summaries. -/
theorem fewer_tests :
    (filterCount (fun p => satW p a) pubs).2 = 33 ∧
    (filterCount (fun p => satW p a) (around (indexBy keyB pubs) (keyB a))).2 = 1 ∧
    replayIndexW id (indexBy keyB pubs) a = replayScanW id pubs a := by decide

#print axioms fewer_tests
end IndexCases
end ApSpec.Abs
