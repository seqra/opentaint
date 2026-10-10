/-
  Fact-threaded forward abstract-mode certificates and local cleaner witnesses.
  These proofs replay supplied certificates; they do not synthesize a certificate
  for every concrete flow or establish preservation under reversal.
  The cleaner and F73 spatial-mode certificates are pre-F75; see BaseCleaner
  for the corrected base gate. A same-base disjoint certificate is historical.
-/
import ApSpec.AbsDefs

namespace ApSpec.Abs
open ApSpec ApSpec.Handoff

/-- Spatial disjointness uses the whole propagated fact and keeps it unchanged. -/
theorem cleanMA_disjoint {cl : Cleaner} {f : AFact} {l : Loc}
    (h : cleanPos cl f.fact = .disjoint) :
    cleanMAB cl f l = true ∧ cleanRes cl f = ⟨[f], []⟩ := by
  simp [cleanMAB, cleanRes, h]

/-- Every supplied fact-threaded certificate retains its concrete pair. -/
theorem flowMA_den {P : Program} {counted : Acc → Bool} {L : Nat}
    {ok : AbstractOK} {rc : Recs} {M : MethodId} {j : PFact} {l0 : Loc}
    {n : Node} {f : AFact} {l : Loc}
    (h : FlowMA P counted L ok rc M j l0 n f l) : den j f.fact l0 l := by
  induction h with
  | start _ _ _ _ hc => exact startFact_sound hc
  | step _ _ _ _ hd _ => exact hd
  | pass _ _ _ _ ih => exact ih
  | call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd _ _ => exact hd
  | rcall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd _ => exact hd
  | clean _ _ _ _ _ hd _ => exact hd
  | filt _ _ _ _ ih => exact ih

/-- L1 for a supplied coherent abstract trace: its indexed output is an actual
    request-free F72 edge. The nested call uses its actual emit/restrict result. -/
theorem flowMA_replay {P : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {rc : Recs}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {j : PFact} {l0 : Loc} {n : Node} {f : AFact} {l : Loc}
    (h : FlowMA P counted L (starOK dem) rc M j l0 n f l) :
    DRW P counted L dem rc sinks roots (.init M j) →
    DRW P counted L dem rc sinks roots (.edge M j n f) := by
  induction h with
  | start _ _ _ _ _ => exact DRA.start
  | step _ he _ hf _ ih => exact fun hi => DRA.step (ih hi) he hf
  | pass _ he _ hm ih => exact fun hi => DRA.pass (ih hi) he hm
  | call _ he he1 _ ha _ _ hok hsat _ hr _ he2 _ hr' _ _ ih ihc =>
    intro hi
    obtain ⟨d, p, hd, _, _, _, _, hem, _, hres, _⟩ := hok
    have hparent := ih hi
    have hj := DRA.initR (DRA.added hparent he he1 ha) hd hem
    exact DRA.ret hparent he he1 ha hj (ihc hj) hd hres hsat hr he2 hr'
  | rcall _ he he1 _ ha _ hrc _ _ _ _ hsat hr _ he2 _ hr' _ _ ih =>
    exact fun hi => DRA.retRec (ih hi) he he1 ha hrc hsat hr he2 hr'
  | clean _ he _ _ hf _ ih => exact fun hi => DRA.clean (ih hi) he hf
  | filt _ he _ hf ih => exact fun hi => DRA.filt (ih hi) he hf

/-- The trace's output fact is ordinary data; its denotation and replay proofs
    certify that very value rather than selecting a new fact from Prop. -/
def flowMA_witness {P : Program} {counted : Acc → Bool} {L : Nat}
    {dem : MethodId → DemandEdge → Prop} {rc : Recs}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    {M : MethodId} {j : PFact} {l0 : Loc} {n : Node} {f : AFact} {l : Loc}
    (h : FlowMA P counted L (starOK dem) rc M j l0 n f l)
    (hi : DRW P counted L dem rc sinks roots (.init M j)) :
    {r : AFact // r = f ∧ den j r.fact l0 l ∧ DRW P counted L dem rc sinks roots (.edge M j n r)} :=
  ⟨f, rfl, flowMA_den h, flowMA_replay h hi⟩

/-- A cleaner accepted by the fact-aware mode has a result covering the selected
    pair. A request for that pair's mark is incompatible with its mode guard. -/
theorem cleanMA_covers {cl : Cleaner} {j : PFact} {f : AFact} {l0 l : Loc}
    (hd : den j f.fact l0 l) (hc : cl.cleansB l = false)
    (hm : cleanMAB cl f l = true) :
    ∃ r, r ∈ (cleanRes cl f).facts ∧ den j r.fact l0 l := by
  rcases cleanRes_sound hd hc with h | ⟨ha, hq⟩
  · exact h
  · have hclm := (cleanRes_reqs_abstract hq).2
    have hmark := den_mark_abs hd ha
    cases hp : cleanPos cl f.fact with
    | disjoint => simp [cleanRes, hp] at hq
    | inside => simp [cleanMAB, hp, hclm, hmark] at hm
    | part => simp [cleanMAB, hp, hclm, hmark] at hm

/-- The existing cleaner produces at most one propagated fact. -/
theorem cleanRes_length (cl : Cleaner) (f : AFact) : (cleanRes cl f).facts.length ≤ 1 := by
  unfold cleanRes
  cases cleanPos cl f.fact with
  | disjoint => simp
  | inside =>
    cases f.fact.mark <;> cases cl.mark <;> simp [Res.none]
    all_goals split <;> simp
  | part =>
    cases f.fact.mark <;> cases cl.mark <;> simp
    all_goals split <;> simp

/-- Compute the local cleaner witness by reading its actual result list. The
    coverage theorem justifies that computed value; no choice axiom is used. -/
def cleanMA_witness (cl : Cleaner) (j : PFact) (f : AFact) (l0 l : Loc)
    (hd : den j f.fact l0 l) (hc : cl.cleansB l = false)
    (hm : cleanMAB cl f l = true) :
    {r : AFact // r ∈ (cleanRes cl f).facts ∧ den j r.fact l0 l} :=
  match hs : (cleanRes cl f).facts with
  | [] => False.elim (by
      obtain ⟨r, hr, _⟩ := cleanMA_covers hd hc hm
      rw [hs] at hr
      exact List.not_mem_nil hr)
  | r :: rs => ⟨r, by
      have hlen := cleanRes_length cl f
      rw [hs] at hlen
      have hz : rs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      obtain ⟨r0, hr0, hdr0⟩ := cleanMA_covers hd hc hm
      rw [hs, hz] at hr0
      have he := List.mem_singleton.mp hr0
      subst r0
      exact ⟨List.mem_cons_self, hdr0⟩⟩

/-- Executable disjoint cleaner vector: the cleaner of the same mark at
    another field preserves the FLOW fact exactly. -/
def cleanerWitnessVector (t : Mark) : AFact :=
  let j : PFact := ⟨3, [4], .star Excl.empty, .star⟩
  let l : Loc := ⟨3, [4], t⟩
  (cleanMA_witness ⟨3, [5], .atAndBelow, some t⟩ j (startFact j) l l
    (startFact_sound ⟨rfl, ⟨[], rfl, by change Excl.empty.admits [] = true; rfl⟩, trivial⟩)
    (by simp [l, Cleaner.cleansB, dropPrefix])
    (by simp [cleanMAB, cleanPos, j, startFact, relate, dropPrefix])).val

/-- Executable overlapping cleaner vector: cleaning another mark keeps this
    pair while recording that cleaned mark in the actual propagated fact. -/
def cleanerOtherMarkVector : AFact :=
  let j : PFact := ⟨3, [], .star Excl.empty, .star⟩
  let l : Loc := ⟨3, [], 1⟩
  (cleanMA_witness ⟨3, [], .atAndBelow, some 2⟩ j (startFact j) l l
    (startFact_sound ⟨rfl, ⟨[], rfl, by change Excl.empty.admits [] = true; rfl⟩, trivial⟩)
    (by decide) (by decide)).val

example : cleanerWitnessVector 1 = ⟨⟨3, [4], .star Excl.empty, .star⟩, false⟩ := by decide
example : cleanerOtherMarkVector = ⟨⟨3, [], .star Excl.empty, .starEx [2]⟩, false⟩ := by decide

#print axioms cleanMA_disjoint
#print axioms flowMA_den
#print axioms flowMA_replay
#print axioms flowMA_witness
#print axioms cleanMA_covers
#print axioms cleanMA_witness
#print axioms cleanerWitnessVector
#print axioms cleanerOtherMarkVector

end ApSpec.Abs
