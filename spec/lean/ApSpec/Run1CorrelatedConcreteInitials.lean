/- Selected FULL run-1 extension. The existing AP pair denotation is unchanged.
   We do not change the historical normalizer or claim Kotlin refinement. -/
import ApSpec.FlowBackedAp
import ApSpec.FlowBackedHandoff

namespace ApSpec.Run1CorrelatedConcreteInitials
open ApSpec ApSpec.Abs ApSpec.Run1FlowTaintCoverage

@[simp] theorem empty_admits (s : List Acc) : Excl.empty.admits s = true := by
  cases s <;> rfl

/-- New seed, under its existing concrete STAR original. The layer stays DEMAND. -/
def seed (b : Base) (p : List Acc) (t : Mark) : AFact :=
  ⟨initial b p (.conc t), true⟩

theorem seed_is_demand (b p t) : (seed b p t).demand = true := rfl

/-- A request does not assert that every suffix is tainted. It gives an identity
    for each suffix which the original input actually supplies. -/
theorem seed_identity (b p t) (s : List Acc) :
    den (initial b p (.conc t)) (seed b p t).fact ⟨b,p ++ s,t⟩ ⟨b,p ++ s,t⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, trivial, s, s, rfl, rfl, empty_admits s, rfl, empty_admits s⟩

theorem star_to_any (i : PFact) (b p m) (l0 l1 : Loc)
    (h : den i (initial b p m) l0 l1) : den i (anyFinal b p m) l0 l1 := by
  obtain ⟨b0,b1,m0,m1,pass,s,r,p0,p1,hi,_⟩ := h
  exact ⟨b0,b1,m0,m1,pass,s,r,p0,p1,hi,trivial⟩

theorem new_seed_inside_old (b p t) (l0 l1 : Loc)
    (h : den (initial b p (.conc t)) (seed b p t).fact l0 l1) :
    den (initial b p (.conc t)) (startFact (initial b p (.conc t))).fact l0 l1 :=
  star_to_any _ _ _ _ _ _ h

/-- The old seed includes a spurious cross-suffix pair. This is a precision
    change, not equality of the old and new abstract candidate sets. -/
theorem old_seed_cross_suffix :
    den (initial 1 [] (.conc 7)) (anyFinal 1 [] (.conc 7))
      ⟨1,[10],7⟩ ⟨1,[20],7⟩ := by
  exact ⟨rfl,rfl,rfl,rfl,trivial,[10],[20],rfl,rfl,rfl,trivial⟩

theorem new_seed_rejects_cross_suffix :
    ¬ den (initial 1 [] (.conc 7)) (seed 1 [] 7).fact
      ⟨1,[10],7⟩ ⟨1,[20],7⟩ := by
  rintro ⟨_,_,_,_,_,s,r,h0,h1,_,hf⟩
  have hs : s = [10] := by simpa [initial] using h0.symm
  have hr : r = [20] := by simpa [initial, seed] using h1.symm
  have he : r = s := hf.1
  rw [hs,hr] at he
  cases he

/-- Pure same-suffix transport. A caller can retain its own suffix through
    any finite number of such copies; no external support label is needed. -/
def location (b : Base) (p s : List Acc) (t : Mark) : Loc := ⟨b,p ++ s,t⟩

theorem correlated_copy (a b : Base) (p q s : List Acc) (t : Mark) :
    den (initial a p (.conc t)) (initial b q (.conc t)) (location a p s t) (location b q s t) := by
  exact ⟨rfl,rfl,rfl,rfl,trivial,s,s,rfl,rfl,empty_admits s,rfl,empty_admits s⟩

/-- A finite copy trace returns an explicit location at every endpoint. -/
def trace (points : List (Base × List Acc)) (s : List Acc) (t : Mark) : List Loc :=
  points.map (fun (b,p) => location b p s t)

theorem trace_keeps_suffix (points : List (Base × List Acc)) (s : List Acc) (t : Mark) :
    trace points s t = points.map (fun (b,p) => ⟨b,p ++ s,t⟩) := rfl

theorem copy_composes (a b c : Base) (p q r s : List Acc) (t : Mark) :
    den (initial a p (.conc t)) (initial b q (.conc t)) (location a p s t) (location b q s t) ∧
    den (initial b q (.conc t)) (initial c r (.conc t)) (location b q s t) (location c r s t) ∧
    den (initial a p (.conc t)) (initial c r (.conc t)) (location a p s t) (location c r s t) :=
  ⟨correlated_copy _ _ _ _ _ _, correlated_copy _ _ _ _ _ _, correlated_copy _ _ _ _ _ _⟩

/-- A read below the tracked prefix consumes part of the unknown suffix.
    ANY retains the witness without claiming that the remaining suffix is s. -/
theorem descent_any_cover (a b : Base) (p q r rest : List Acc) (t : Mark) :
    den (initial a p (.conc t)) (anyFinal b q (.conc t))
      (location a p (r ++ rest) t) (location b q rest t) := by
  exact ⟨rfl,rfl,rfl,rfl,trivial,r ++ rest,rest,rfl,rfl,empty_admits _,trivial⟩

/-- A cut forgets output accessors only. Keep the complete input witness. -/
theorem cut_any_cover (i : PFact) (b : Base) (q lost : List Acc) (m : MarkA)
    (l0 l1 : Loc) (h : den i (initial b (q ++ lost) m) l0 l1) :
    den i (anyFinal b q m) l0 l1 := by
  obtain ⟨b0,b1,m0,m1,pass,s,r,p0,p1,hi,_⟩ := h
  refine ⟨b0,b1,m0,m1,pass,s,lost ++ r,p0,?_,hi,trivial⟩
  simpa [initial,anyFinal,List.append_assoc] using p1

/-- Losing a premise binder requires an independent suffix. It cannot create
    a correlated STAR under ZERO or another unrelated original. -/
theorem independent_supply_any (a b : Base) (p q s r : List Acc) (t : Mark) :
    den (initial a p (.conc t)) (anyFinal b q (.conc t)) (location a p s t) (location b q r t) := by
  exact ⟨rfl,rfl,rfl,rfl,trivial,s,r,rfl,rfl,empty_admits s,trivial⟩

/-- STAR coverage requires equal output paths. The original relation supplies
    the suffix; mark specialization changes no field geometry. -/
theorem star_specialization (a b : Base) (p q : List Acc) (t : Mark)
    (xs : List Mark) (allowed : memB t xs = false) (l0 l1 : Loc) :
    den (initial a p (.conc t)) (initial b q (.conc t)) l0 l1 ↔
      l0.mark = t ∧ den (initial a p .star) (initial b q (.starEx xs)) l0 l1 := by
  constructor
  · rintro ⟨b0,b1,m0,m1,_,s,r,p0,p1,hi,hf⟩
    refine ⟨m0,b0,b1,trivial,?_,?_,s,r,p0,p1,hi,hf⟩
    · exact m1.trans m0.symm
    · change memB l0.mark xs = false
      rw [m0]
      exact allowed
  · rintro ⟨hm,b0,b1,_,m1,_,s,r,p0,p1,hi,hf⟩
    exact ⟨b0,b1,hm,m1.trans hm,trivial,s,r,p0,p1,hi,hf⟩

/-- Prefix coverage from the ANY cell must not be copied to STAR. -/
theorem longer_star_output :
    den (initial 1 [] (.conc 7)) (initial 2 [10,20] (.conc 7))
      ⟨1,[],7⟩ ⟨2,[10,20],7⟩ := by
  exact ⟨rfl,rfl,rfl,rfl,trivial,[],[],rfl,rfl,rfl,rfl,rfl⟩

theorem prefix_star_does_not_cover :
    ¬ den (initial 1 [] .star) (initial 2 [10] .star) ⟨1,[],7⟩ ⟨2,[10,20],7⟩ := by
  rintro ⟨_,_,_,_,_,s,r,h0,h1,_,hf⟩
  have hs : s = [] := by simpa [initial] using h0.symm
  have hr : r = [] := hf.1.trans hs
  simp [initial,hr] at h1

/-- STAR identities have the same raw alias-effect class in both payloads.
    This equality also covers different bases or output paths. -/
theorem star_alias_class
    (a b : Run1SummaryAliasAdmission.Base) (p q : List Nat)
    (t : Run1SummaryAliasAdmission.Mark) :
    Run1SummaryAliasAdmission.noMemoryEffect
      (ApSpec.FlowBackedAp.aliasCellLeaf a p .star .flow)
      (ApSpec.FlowBackedAp.aliasCellLeaf b q .star .flow) =
    Run1SummaryAliasAdmission.noMemoryEffect
      (ApSpec.FlowBackedAp.aliasCellLeaf a p .star (.taint t))
      (ApSpec.FlowBackedAp.aliasCellLeaf b q .star (.taint t)) := by
  by_cases hz : a = .zero <;> by_cases hb : a = b <;> by_cases hp : p = q <;>
    simp [Run1SummaryAliasAdmission.noMemoryEffect,ApSpec.FlowBackedAp.aliasCellLeaf,hz,hb,hp]

/-- Existing geometry dispatch already separates copy from descent and may.
    The new scoped normalizer must retain the first of these raw STAR results. -/
theorem same_prefix_geometry (q : List Acc) :
    belowCase (.star Excl.empty) (.star Excl.empty) [] q (.star Excl.empty) =
      some (q, .star Excl.empty, false) := rfl

theorem descent_geometry (q : List Acc) :
    aboveCase (.star Excl.empty) (.star Excl.empty) [10] q (.star Excl.empty) =
      some (q, .any, true) := rfl

theorem explicit_may_geometry (q : List Acc) :
    (belowCase (.star Excl.empty) (.star Excl.empty) [] q .any).map
      (fun (p,k,_) => (p,k)) = some (q,.any) := rfl

/-- The existing geometry and mark kernels before the historical W2 erasure.
    Production may use this result only after the selected owner legality test.
    In particular this is not a replacement for the general AP normalizer. -/
def rawApply (c : AFact) (fr to : PFact) : Res :=
  if Nat.beq c.fact.base fr.base then
    let geo := match relate fr.path c.fact.path with
      | .below r => belowCase c.fact.kind fr.kind r to.path to.kind
      | .above r => aboveCase c.fact.kind fr.kind r to.path to.kind
      | .apart => none
    match geo with
    | none => Res.none
    | some (p,k,ap) => match markGate fr.mark c.fact.mark with
      | .no => Res.none
      | .req t => ⟨[],[t]⟩
      | .ok => match markComp to.mark c.fact.mark with
        | none => Res.none
        | some m => ⟨[⟨⟨to.base,p,k,m⟩,c.demand || ap⟩],[]⟩
  else Res.none

def rawSummary (c : AFact) (i : PFact) (g : AFact) : Res :=
  let r := rawApply c i g.fact
  ⟨r.facts.map (fun x => ⟨x.fact,x.demand || g.demand⟩),r.reqs⟩

/-- The replacement gives the same outputs, layers and requests for an
    actually supplied T, including the precise STAR case. -/
theorem star_summary_application (c : AFact) (a b : Base) (p q : List Acc)
    (t : Mark) (xs : List Mark) (layer : Bool)
    (actual : c.fact.mark = .conc t) (allowed : memB t xs = false) :
    rawSummary c (initial a p (.conc t)) ⟨initial b q (.conc t),layer⟩ =
      rawSummary c (initial a p .star) ⟨initial b q (.starEx xs),layer⟩ := by
  simp [rawSummary,rawApply,initial,actual,markGate,markComp,allowed]

theorem raw_copy_keeps_star (a b : Base) (p q : List Acc) (t : Mark) :
    rawApply (seed a p t) (initial a p .star) (initial b q .star) =
      ⟨[⟨initial b q (.conc t),true⟩],[]⟩ := by
  simp [rawApply,seed,initial,relate,CoreAux.dropPrefix_some.mpr (List.append_nil p).symm,
    belowCase,admitsTailB,tailExcl,Excl.union,Excl.empty,Excl.admits,markGate,markComp]

theorem raw_descent_widens :
    rawApply (seed 1 [] 7) (initial 1 [10] .star) (initial 2 [] .star) =
      ⟨[⟨anyFinal 2 [] (.conc 7),true⟩],[]⟩ := rfl

/-- The original demand emitter admits a FLOW guide, without StrongQueries. -/
theorem flow_guide_start (b p t) :
    emitW (anyFinal b p .star) ⟨b,p,.exact,.conc t⟩ = some (initial b p .star) :=
  ApSpec.FlowBackedAp.abstract_guide_start b p t

/-- The handoff entry normalizer keeps the exact concrete mark. -/
def handoffEntry (p : PFact) : PFact :=
  match p.kind with
  | .star _ => { p with kind := .any }
  | _ => p

theorem handoff_mark (p : PFact) : (handoffEntry p).mark = p.mark := by
  cases p with | mk b path k m => cases k <;> rfl

theorem marked_handoff (b p t) :
    handoffEntry (seed b p t).fact = anyFinal b p (.conc t) := rfl

theorem flow_handoff (b p) :
    handoffEntry (initial b p .star) = anyFinal b p .star := rfl

/-- A STAR handoff pattern has the same location/mark set when read as a
    demand entry. The bound suffix was a relation property, not a pattern test. -/
theorem handoff_covers (b p m) (l : Loc) :
    (handoffEntry (initial b p m)).covers l ↔ (initial b p m).covers l := by
  simp [handoffEntry,initial,PFact.covers,tailI]

def canReplace (covered excluded blocked : Bool) : Bool := covered && !excluded && !blocked

theorem protection_blocks (covered excluded : Bool) : canReplace covered excluded true = false := by
  simp [canReplace]

theorem exclusion_blocks (covered blocked : Bool) : canReplace covered true blocked = false := by
  simp [canReplace]

/-- A below-only cleaner retains a root witness but removes descendants.
    Use an EXACT residual, not the entire incoming correlated row. -/
theorem cleaner_root_cover (a b : Base) (p q s : List Acc) (t : Mark) :
    den (initial a p (.conc t)) ⟨b,q,.exact,.conc t⟩ (location a p s t) ⟨b,q,t⟩ := by
  exact ⟨rfl,rfl,rfl,rfl,trivial,s,[],rfl,by simp, empty_admits s,rfl⟩

def controls : List Bool := [
  decide ((seed 1 [] 7).fact.kind = .star Excl.empty),
  decide ((seed 1 [] 7).demand = true),
  decide (handoffEntry (seed 1 [10] 7).fact = anyFinal 1 [10] (.conc 7)),
  decide (canReplace true false false = true),
  decide (canReplace true true false = false),
  decide (canReplace true false true = false),
  decide (dropPrefix [10] [10,20] = some [20]),
  decide (trace [(1,[]),(2,[10]),(3,[20])] [30] 7 =
    [⟨1,[30],7⟩,⟨2,[10,30],7⟩,⟨3,[20,30],7⟩])
]

end ApSpec.Run1CorrelatedConcreteInitials
