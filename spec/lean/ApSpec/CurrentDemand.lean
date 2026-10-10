/-
  Local demand and summary reduction contracts for F75.

  These operations do not depend on cleaner transfer or closure direction.
  Each witness is computed by the analyzer operation. Proofs never select data
  from an existential proposition. The emission guards are explicit: abstract
  patterns have a supported tail, and a concrete pattern needs a concrete added
  fact. CurrentHandoff derives the tail guard for the canonical base sequence.

  Restriction removes pairs and keeps the layer. It retains every requested
  pair when the whole premise is inside D-c, and D-p admits the exit mark and
  location. It can retain extra pairs in the documented correlated-tail and
  abstract-mark cells. Normalization can enlarge mark sets; it does not enlarge
  location sets. No claim about ND, static fields, or X seeds follows here.
-/
import ApSpec.AbsWitness
import ApSpec.AbsStore

namespace ApSpec.CurrentDemand
open ApSpec ApSpec.Abs ApSpec.Handoff ApSpec.Store

/-- All evidence needed to emit and later reduce a summary premise. -/
structure Emission (d a : PFact) (l : Loc) where
  premise : PFact
  emitted : emitW d a = some premise
  covers : premise.covers l
  satisfies : satW premise a = true
  inside : insideB premise d = true

/-- Executable L6. The returned value is the actual `emitW` result. -/
def emitCertificate (d a : PFact) (l : Loc)
    (tail : d.mark = .star → PatTailB d.kind = true)
    (concrete : d.mark ≠ .star → ∃ t, a.mark = .conc t)
    (demanded : d.covers l) (added : a.covers l) : Emission d a l :=
  let w := emitWitness d a l tail concrete demanded added
  ⟨w.val, w.property.1, w.property.2.1, w.property.2.2, by
    by_cases hs : d.mark = .star
    · exact emitW_insideB_star hs w.property.1
    · obtain ⟨t, ht⟩ := concrete hs
      exact (emitW_insideB_conc hs ht w.property.1).1⟩

/-- A reduced summary, with its retained concrete pair and unchanged layer. -/
structure Reduction (j : PFact) (g : AFact) (d : DemandEdge) (l1 l2 : Loc) where
  conclusion : AFact
  reduced : restrictI j g d = some conclusion
  pair : den j conclusion.fact l1 l2
  layer : conclusion.demand = g.demand
  subset : ∀ x y, den j conclusion.fact x y → den j g.fact x y

/-- Executable C5. Evaluation selects the result of `restrictI` itself. -/
def restrictCertificate (j : PFact) (g : AFact) (d : DemandEdge) (p : PFact)
    (l1 l2 : Loc) (inside : insideB j d.din = true)
    (pair : den j g.fact l1 l2) (exit : d.dout = some p) (demanded : p.covers l2) :
    Reduction j g d l1 l2 :=
  match he : restrictI j g d with
  | some g' => ⟨g', he, by
      obtain ⟨g0, h0, hp, _⟩ := restrictI_contract inside pair exit demanded
      rw [he] at h0
      cases h0
      exact hp,
      (restrictI_sub j g d g' he).1,
      (restrictI_sub j g d g' he).2⟩
  | none => False.elim (by
      obtain ⟨g', hg', _, _⟩ := restrictI_contract inside pair exit demanded
      rw [he] at hg'
      cases hg')

/-- An emitted premise passes the whole-premise gate of summary reduction. -/
def reduceEmission {d : DemandEdge} {a : PFact} {l1 l2 : Loc}
    (e : Emission d.din a l1) (g : AFact) (p : PFact)
    (pair : den e.premise g.fact l1 l2) (exit : d.dout = some p)
    (demanded : p.covers l2) : Reduction e.premise g d l1 l2 :=
  restrictCertificate e.premise g d p l1 l2 e.inside pair exit demanded

/-- Demand normalization preserves base, path and tail, including field exclusions. -/
theorem normFact_shape (f : PFact) :
    (normFact f).base = f.base ∧ (normFact f).path = f.path ∧
    (normFact f).kind = f.kind := ⟨rfl, rfl, rfl⟩

/-- Normalization preserves each demanded concrete pair. -/
structure Normalization (d : DemandEdge) where
  normalized : DemandEdge
  computed : normalized = normDem d
  entry : ∀ l, d.din.covers l → normalized.din.covers l
  exit : ∀ p, d.dout = some p → normalized.dout = some (normFact p)
  exitCovers : ∀ p l, d.dout = some p → p.covers l → (normFact p).covers l
  entryLocations : ∀ l, normalized.din.coversLoc l ↔ d.din.coversLoc l

def normalizeCertificate (d : DemandEdge) : Normalization d :=
  ⟨normDem d, rfl, fun _ => normDem_din, fun _ => normDem_dout,
    fun _ _ _ => normFact_covers, fun _ => Iff.rfl⟩

/-! Summary reduction: list concept and a maintained premise-path index. -/

/-- A successful whole-premise gate requires the demand path above the premise. -/
theorem inside_prefix {j d : PFact} (h : insideB j d = true) :
    j.base = d.base ∧ ∃ r, j.path = d.path ++ r := by
  have hi := insideB_loc h
  unfold insideLocB coversB at hi
  dsimp only at hi
  cases hb : Nat.beq d.base j.base with
  | false => rw [hb] at hi; cases hi
  | true =>
    refine ⟨(CoreAux.beq_iff.mp hb).symm, ?_⟩
    cases hr : dropPrefix d.path j.path with
    | none => rw [hb, hr] at hi; cases hi
    | some r => exact ⟨r, CoreAux.dropPrefix_some.mp hr⟩

/-- The suffix from the whole-premise gate is computed by `dropPrefix`. -/
def insidePrefixWitness (j d : PFact) (h : insideB j d = true) :
    {r : List Acc // j.base = d.base ∧ j.path = d.path ++ r} :=
  match he : dropPrefix d.path j.path with
  | some r => ⟨r, (inside_prefix h).1, CoreAux.dropPrefix_some.mp he⟩
  | none => False.elim (by
      obtain ⟨_, r, hr⟩ := inside_prefix h
      have hs := CoreAux.dropPrefix_some.mpr hr
      rw [he] at hs
      cases hs)

def demandIndex (ds : List DemandEdge) : PathMap DemandEdge :=
  indexBy (fun d => keyB d.din) ds

/-- Prefixes suffice for restriction, unlike abstract emission or replay. -/
def restrictCandidates (idx : PathMap DemandEdge) (j : PFact) : List DemandEdge :=
  idx.lookupPrefixes (keyB j)

def restrictScan (ds : List DemandEdge) (j : PFact) (g : AFact) : List AFact :=
  ds.filterMap (fun d => restrictI j g d)

def restrictIndexed (idx : PathMap DemandEdge) (j : PFact) (g : AFact) : List AFact :=
  (restrictCandidates idx j).filterMap (fun d => restrictI j g d)

theorem restrict_candidate_complete {ds : List DemandEdge} {d : DemandEdge}
    {j : PFact} {g g' : AFact} (stored : d ∈ ds)
    (reduced : restrictI j g d = some g') :
    d ∈ restrictCandidates (demandIndex ds) j := by
  obtain ⟨_, _, hin, _, _⟩ := restrictI_someM reduced
  obtain ⟨hb, r, hr⟩ := inside_prefix hin
  apply mem_prefixes_indexBy.mpr
  exact ⟨stored, r, by simp only [keyB, hb, hr, List.cons_append]⟩

/-- The index and scan return the same result set for every mark and tail cell. -/
theorem restrict_index_equiv {ds : List DemandEdge} {j : PFact} {g g' : AFact} :
    g' ∈ restrictIndexed (demandIndex ds) j g ↔ g' ∈ restrictScan ds j g := by
  simp only [restrictIndexed, restrictScan, List.mem_filterMap]
  constructor
  · rintro ⟨d, hd, hr⟩
    exact ⟨d, (mem_prefixes_indexBy.mp hd).1, hr⟩
  · rintro ⟨d, hd, hr⟩
    exact ⟨d, restrict_candidate_complete hd hr, hr⟩

/-- Count the exact restriction calls, separately from index construction and walking. -/
def restrictCount (ds : List DemandEdge) (j : PFact) (g : AFact) : List AFact × Nat :=
  (restrictScan ds j g, ds.length)

theorem restrict_test_cost (ds : List DemandEdge) (j : PFact) (g : AFact) :
    (restrictCount ds j g).2 = ds.length ∧
    (restrictCount (restrictCandidates (demandIndex ds) j) j g).2 =
      (restrictCandidates (demandIndex ds) j).length ∧
    (demandIndex ds).prefHits (keyB j) ≤ (keyB j).length + 1 :=
  ⟨rfl, rfl, PathMap.prefHits_le⟩

/-! Executable cases: emission sharing, intersection, mark gates and query cost. -/

def sharedEmission (t : Mark) : Emission ⟨3, [], .any, .star⟩
    ⟨3, [4], .exact, .conc t⟩ ⟨3, [4], t⟩ :=
  emitCertificate _ _ _ (fun _ => rfl) (fun h => False.elim (h rfl))
    ⟨rfl, ⟨[4], rfl, trivial⟩, trivial⟩ ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

theorem emission_shares (t u : Mark) :
    (sharedEmission t).premise = (sharedEmission u).premise := rfl

def j : PFact := ⟨3, [], .exact, .conc 1⟩
def g : AFact := ⟨⟨5, [], .any, .conc 1⟩, true⟩
def dp : PFact := ⟨5, [4], .exact, .conc 1⟩
def d : DemandEdge := ⟨⟨3, [], .exact, .star⟩, some dp⟩
def l1 : Loc := ⟨3, [], 1⟩
def l2 : Loc := ⟨5, [4], 1⟩

def reducedWitness : Reduction j g d l1 l2 :=
  restrictCertificate _ _ _ _ _ _ (by decide)
    ⟨rfl, rfl, rfl, rfl, trivial, [], [4], rfl, rfl, rfl, trivial⟩ rfl
    ⟨rfl, ⟨[], rfl, rfl⟩, rfl⟩

theorem reduction_value : reducedWitness.conclusion = ⟨dp, true⟩ := by decide

def markRejected : DemandEdge := ⟨d.din, some ⟨5, [4], .exact, .conc 2⟩⟩
theorem wrong_exit_mark_rejected : restrictI j g markRejected = none := by decide

def excludedDemand : DemandEdge :=
  ⟨⟨3, [], .exact, .starEx [1]⟩, some ⟨5, [4], .exact, .starEx [1]⟩⟩
theorem normalization_only_marks :
    restrictI j g excludedDemand = none ∧
    restrictI j g (normalizeCertificate excludedDemand).normalized = some ⟨dp, true⟩ :=
  by decide

def storedDemands : List DemandEdge :=
  d :: (List.range 32).map (fun b => ⟨⟨b + 6, [], .exact, .star⟩, some dp⟩)

/-- A maintained index needs one exact restriction test instead of 33. -/
def reductionWorkWitness : { costs : Nat × Nat //
    costs = ((restrictCount storedDemands j g).2,
      (restrictCount (restrictCandidates (demandIndex storedDemands) j) j g).2) ∧
    costs = (33, 1) ∧
    restrictIndexed (demandIndex storedDemands) j g = restrictScan storedDemands j g } :=
  ⟨(33, 1), by decide, rfl, by decide⟩

#eval (sharedEmission 1).premise
#eval reducedWitness.conclusion
#eval reductionWorkWitness.val
#print axioms emitCertificate
#print axioms restrictCertificate
#print axioms normalizeCertificate
#print axioms insidePrefixWitness
#print axioms restrict_candidate_complete
#print axioms restrict_index_equiv
#print axioms reductionWorkWitness

end ApSpec.CurrentDemand
