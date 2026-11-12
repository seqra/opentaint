import Std

/- Executable selected-T candidate. NOT a retirement certificate. No probe
   outcome is an axiom. Native typed-input, arbitrary paired common-demand
   interaction, and complete caller suffix remain separate proof gates. -/
namespace Thing2RootDebtCandidate
inductive Tail where | exact | star | may | must
  deriving DecidableEq, Repr
inductive Layer where | normal | demand
  deriving DecidableEq, Repr
inductive Mark where | selected | flow
  deriving DecidableEq, Repr
inductive Role where | direct | opposite
  deriving DecidableEq, Repr
abbrev Path := List Nat
structure Fact where
  path : Path
  tail : Tail
  layer : Layer
  excluded : List Nat := []
  flag : Bool := true
  deriving DecidableEq, Repr
structure Initial where
  fact : Fact
  mark : Mark := .selected
  deriving DecidableEq, Repr
structure Offer where
  fact : Fact
  inputKept : Bool
  deriving DecidableEq, Repr

def Legal (a : Offer) : Prop :=
  ((a.fact.tail = .star ∨ a.fact.tail = .may) → a.fact.layer = .demand) ∧
  (a.fact.tail = .exact → a.fact.excluded = [])
def BackwardLegal (a : Offer) : Prop := Legal a ∧ a.fact.tail ≠ .must

/- Root ANY/T C2; all accessors here are counted nonstatic fields/elements. -/
def c2Any (a : Offer) : List Initial :=
  if !a.inputKept then [] else
  match a.fact.path with
  | [] => match a.fact.tail with
    | .exact => [⟨{ a.fact with excluded := [], flag := false }, .selected⟩]
    | .must => [⟨{ a.fact with flag := false }, .selected⟩]
    | .star | .may =>
      [⟨⟨[], .star, .demand, [], false⟩, .selected⟩,
       ⟨⟨[], .star, .normal, [], false⟩, .flow⟩]
  | f :: rest =>
    let exact := a.fact.tail == .exact && rest.isEmpty
    let primary : Initial := ⟨⟨[f], if exact then .exact else .star,
      if exact then a.fact.layer else .demand, [], false⟩, .selected⟩
    [primary] ++ (if exact then [] else [⟨⟨[f], .star, .normal, [], false⟩, .flow⟩]) ++
      [⟨⟨[], .exact, .normal, [], false⟩, .flow⟩]
def c2Exact (a : Offer) : List Initial :=
  if !a.inputKept || !a.fact.path.isEmpty then [] else
  [⟨⟨[], .exact, if a.fact.tail == .may then .demand else a.fact.layer,
      [], false⟩, .selected⟩]
def selected (xs : List Initial) : List Fact :=
  (xs.filter (fun x => x.mark == .selected)).map Initial.fact

theorem c2_child_stays_nonempty (a : Offer) (f : Nat) (rest : Path)
    (h : a.fact.path = f :: rest) :
    ∀ i ∈ selected (c2Any a), i.path = [f] := by
  cases a with | mk af kept =>
    cases af with | mk p t l e flag =>
      simp only at h
      subst p
      cases kept <;> cases t <;> cases rest <;>
        simp_all [c2Any, selected]
theorem c2_extra_exact_is_demand (a : Offer) (h : BackwardLegal a)
    (i : Fact) (hi : i ∈ selected (c2Exact a))
    (notShared : i ∉ selected (c2Any a)) : i.layer = .demand := by
  cases a with | mk af kept =>
    cases af with | mk p t l e flag =>
      cases kept <;> cases p <;> cases t <;>
        simp_all [BackwardLegal, Legal, c2Exact, c2Any, selected]

/- Prefix copies and guarded native local filters. Accept of a FieldAccessor
   keeps its full subtree; only Element uses a recursively changed filter.
   `other` remains arbitrary, not an assumed all-accept predicate. -/
def addPrefix (p : Path) (f : Fact) : Fact := { f with path := p ++ f.path }
theorem addPrefix_nonempty (p : Path) (f : Fact) (h : f.path ≠ []) :
    (addPrefix p f).path ≠ [] := by
  simp only [addPrefix]
  intro hh
  exact h (List.append_eq_nil_iff.mp hh).2
def filterPath (content : Nat) (other : Path → Bool) (f : Fact) : Option Fact :=
  if f.path.isEmpty || f.path.head? == some content || other f.path then some f else none
theorem root_filter_keeps (content : Nat) (other : Path → Bool) (f : Fact)
    (h : f.path = []) : filterPath content other f = some f := by
  simp [filterPath, h]
theorem content_filter_keeps (content : Nat) (other : Path → Bool) (f : Fact) :
    filterPath content other (addPrefix [content] f) = some (addPrefix [content] f) := by
  change (if false || (content == content) || other (content :: f.path) then some _ else none) = _
  have hh : (content == content) = true := by
    change decide (content = content) = true
    exact decide_eq_true rfl
  rw [hh]
  rfl

/- The source branch bypasses the ordinary exact-root selected reset. -/
def source (f : Fact) : Fact := ⟨[], .exact, f.layer, [], true⟩
def cleanExactRoot (f : Fact) : List Fact :=
  if f.path.isEmpty then match f.tail with
    | .exact => []
    | .star | .may => [⟨[], .may, .demand, [], true⟩]
    | .must => [⟨[], .must, .demand, f.excluded, true⟩]
  else [{ f with flag := true }]
structure PermissionIds where
  exactLeaf : Nat
  anyLeaf : Nat
  distinct : exactLeaf ≠ anyLeaf

def backwardHits (ids : PermissionIds) (i : Fact) : List Nat :=
  if i.path.isEmpty then [ids.exactLeaf, ids.anyLeaf] else []
def rootMayMasks (rows : List Fact) (s : Fact) : Bool :=
  rows.any (fun r => r.path.isEmpty && r.tail == .may && r.layer == s.layer)
structure Body where
  ordinary : List Fact
  exactSource : Fact
  sourceVisible : Bool
  deriving DecidableEq, Repr

def execute (content : Nat) (i : Fact) : Body :=
  let ordinary := cleanExactRoot i ++ cleanExactRoot (addPrefix [content] i)
  let exactSource := source i
  ⟨ordinary, exactSource, !rootMayMasks ordinary exactSource⟩
def bodyRows (b : Body) : List Fact :=
  b.ordinary ++ if b.sourceVisible then [b.exactSource] else []

/- Root exact C5 refines MAY/MUST, never strips an actual child. Broad C5
   retains this selected projection; unrelated output rows are left shared. -/
def c5Exact (rows : List Fact) : List Fact :=
  rows.filterMap (fun f => if f.path.isEmpty then
    some { f with tail := .exact, excluded := [] } else none)
def c5Broad (rows : List Fact) : List Fact := rows
def c5Full (rows : List Fact) : List Fact := c5Broad rows ++ c5Exact rows
def exactResult (l : Layer) : Fact := ⟨[], .exact, l, [], true⟩

theorem nonempty_source_not_masked (content : Nat) (i : Fact) (h : i.path ≠ []) :
    (execute content i).sourceVisible = true := by
  cases i with | mk path tail layer excluded flag =>
    cases path with
    | nil => exact False.elim (h rfl)
    | cons x xs => simp [execute, cleanExactRoot, addPrefix, rootMayMasks, source]
theorem nonempty_c5_exact_is_source (content : Nat) (i : Fact) (h : i.path ≠ []) :
    c5Exact (bodyRows (execute content i)) = [exactResult i.layer] := by
  cases i with | mk path tail layer excluded flag =>
    cases path with
    | nil => exact False.elim (h rfl)
    | cons x xs => simp [c5Exact, bodyRows, execute, cleanExactRoot, addPrefix,
        rootMayMasks, source, exactResult]
theorem nonempty_exact_already_broad (content : Nat) (i : Fact) (h : i.path ≠ [])
    (r : Fact) (hr : r ∈ c5Exact (bodyRows (execute content i))) :
    r ∈ c5Broad (bodyRows (execute content i)) := by
  rw [nonempty_c5_exact_is_source content i h] at hr
  simp only [List.mem_singleton] at hr
  subst r
  change exactResult i.layer ∈ (execute content i).ordinary ++
    (if (execute content i).sourceVisible then [(execute content i).exactSource] else [])
  rw [nonempty_source_not_masked content i h]
  apply List.mem_append_right
  simp [execute, source, exactResult]

theorem full_only_shape (content : Nat) (i r : Fact)
    (hr : r ∈ c5Full (bodyRows (execute content i)))
    (missing : r ∉ c5Broad (bodyRows (execute content i))) :
    i.path = [] ∧ r = exactResult .demand := by
  cases i with | mk p t l e flag =>
    cases p with
    | cons f fs =>
      simp only [c5Full, List.mem_append] at hr
      rcases hr with hb | he
      · exact False.elim (missing hb)
      · exact False.elim (missing (nonempty_exact_already_broad content _ (by simp) _ he))
    | nil =>
      cases t <;> cases l <;>
        simp_all [c5Full, c5Broad, c5Exact, bodyRows, execute, cleanExactRoot,
          addPrefix, rootMayMasks, source, exactResult]

/- Saved exact-root readers are available in both direct/opposite roles. -/
def currentSourceEffect (content : Nat) (a : Offer) : List Fact :=
  (selected (c2Any a)).flatMap (fun i =>
    (c5Broad (bodyRows (execute content i))).filter (fun r =>
      r.path.isEmpty && r.tail == .exact))
def replayExact (_role : Role) (a : Offer) : List Fact :=
  if a.inputKept && a.fact.path.isEmpty then [exactResult a.fact.layer] else []
def LayerCovers : Layer → Layer → Prop
  | .normal, _ => True
  | .demand, .demand => True
  | .demand, .normal => False
def FactCovers (a b : Fact) : Prop :=
  a.path = b.path ∧ a.tail = b.tail ∧ a.excluded = b.excluded ∧
  a.flag = b.flag ∧ LayerCovers a.layer b.layer
def reducedEffects (content : Nat) (role : Role) (a : Offer) : List Fact :=
  replayExact role a ++ currentSourceEffect content a

theorem every_kept_offer_has_replacement (content : Nat) (role : Role) (a : Offer)
    (kept : a.inputKept = true) :
    ∃ r ∈ reducedEffects content role a, FactCovers r (exactResult .demand) := by
  cases a with | mk af k =>
    cases af with | mk p t l e flag =>
      simp only at kept
      subst k
      cases p with
      | nil =>
        refine ⟨exactResult l, ?_, ?_⟩
        · simp [reducedEffects, replayExact]
        · cases l <;> simp [FactCovers, LayerCovers, exactResult]
      | cons f rest =>
        cases t <;> cases rest <;> cases l <;>
          simp [reducedEffects, replayExact, currentSourceEffect, c2Any, selected,
            c5Broad, bodyRows, execute, cleanExactRoot, addPrefix, rootMayMasks,
            source, exactResult, FactCovers, LayerCovers]

/- Critical backward branch, including the shared EXACT/NORMAL result. -/
def backRows (i : Fact) : List Fact :=
  if i.path.isEmpty then
    (if i.tail == .exact && i.layer == .normal then [exactResult .normal] else []) ++
      [⟨[], .may, .demand, [], true⟩]
  else []
def backHitsFor (ids : PermissionIds) (starts : List Initial) : List Nat :=
  (selected starts).flatMap (backwardHits ids)
def HitSetEq (xs ys : List Nat) : Prop := ∀ x, x ∈ xs ↔ x ∈ ys

theorem backward_permission_sets (ids : PermissionIds) (a : Offer)
    (h : BackwardLegal a) :
    HitSetEq (backHitsFor ids (c2Any a ++ c2Exact a)) (backHitsFor ids (c2Any a)) := by
  cases a with | mk af k =>
    cases af with | mk p t l e flag =>
      cases k <;> cases p <;> cases t <;>
        simp_all [BackwardLegal, Legal, HitSetEq, backHitsFor, selected,
          c2Any, c2Exact, backwardHits, or_left_comm, or_comm]

def normalOnly (rows : List Fact) : List Fact := rows.filter (fun r => r.layer == .normal)
theorem normal_persistence_unchanged (content : Nat) (i : Fact) :
    ∀ r, r ∈ normalOnly (c5Full (bodyRows (execute content i))) ↔
      r ∈ normalOnly (c5Broad (bodyRows (execute content i))) := by
  intro r
  simp only [normalOnly, List.mem_filter, beq_iff_eq]
  constructor
  · intro ⟨hr, hn⟩
    by_cases hb : r ∈ c5Broad (bodyRows (execute content i))
    · exact ⟨hb, hn⟩
    · have shape := full_only_shape content i r hr hb
      rw [shape.2] at hn
      contradiction
  · intro ⟨hr, hn⟩
    exact ⟨List.mem_append_left _ hr, hn⟩

/- These executable frontier maps encode the just-proved root shape, not an
   assumed future-preservation boolean. Their lift to all paired demand is
   explicitly NOT proved here. A live broad dependency is mandatory. -/
structure ForwardFrontier where
  broad : Bool
  extraExact : Bool
  deriving DecidableEq, Repr
structure BackwardFrontier where
  broadStar : Bool
  extraExact : Bool
  deriving DecidableEq, Repr

def RelatedF (full reduced : ForwardFrontier) : Prop :=
  full.broad = reduced.broad ∧ reduced.extraExact = false ∧
    (full.extraExact = true → full.broad = true)
def RelatedB (full reduced : BackwardFrontier) : Prop :=
  full.broadStar = reduced.broadStar ∧ reduced.extraExact = false ∧
    (full.extraExact = true → full.broadStar = true)
def backwardFrontier (d : ForwardFrontier) (coarse : Bool) : BackwardFrontier :=
  ⟨d.broad && coarse, d.broad && d.extraExact && coarse⟩
def forwardFrontier (d : BackwardFrontier) (debt : Bool) : ForwardFrontier :=
  ⟨d.broadStar && debt, d.broadStar && d.extraExact && debt⟩

theorem backward_closes (full reduced : ForwardFrontier) (h : RelatedF full reduced)
    (coarse : Bool) : RelatedB (backwardFrontier full coarse) (backwardFrontier reduced coarse) := by
  rcases full with ⟨f, fx⟩
  rcases reduced with ⟨r, rx⟩
  cases f <;> cases fx <;> cases r <;> cases rx <;> cases coarse <;>
    simp_all [RelatedF, RelatedB, backwardFrontier]
theorem forward_closes (full reduced : BackwardFrontier) (h : RelatedB full reduced)
    (debt : Bool) : RelatedF (forwardFrontier full debt) (forwardFrontier reduced debt) := by
  rcases full with ⟨f, fx⟩
  rcases reduced with ⟨r, rx⟩
  cases f <;> cases fx <;> cases r <;> cases rx <;> cases debt <;>
    simp_all [RelatedF, RelatedB, forwardFrontier]
def cycle (d : ForwardFrontier) (coarse debt : Bool) : ForwardFrontier :=
  forwardFrontier (backwardFrontier d coarse) debt
def cycles : ForwardFrontier → List (Bool × Bool) → ForwardFrontier
  | d, [] => d
  | d, (coarse, debt) :: more => cycles (cycle d coarse debt) more

theorem all_future_frontiers (full reduced : ForwardFrontier) (h : RelatedF full reduced)
    (offers : List (Bool × Bool)) : RelatedF (cycles full offers) (cycles reduced offers) := by
  induction offers generalizing full reduced with
  | nil => exact h
  | cons lane more ih =>
    exact ih _ _ (forward_closes _ _ (backward_closes _ _ h lane.1) lane.2)

/- Arbitrary shared rows/marks/context stores are retained as a type parameter.
   This preservation lemma does not prove their interaction with local C5. -/
structure State (Common : Type) where
  common : Common
  frontier : ForwardFrontier
def stepState {Common : Type} (stepCommon : Common → Common)
    (s : State Common) (coarse debt : Bool) : State Common :=
  ⟨stepCommon s.common, cycle s.frontier coarse debt⟩
theorem shared_state_preserved {Common : Type} (stepCommon : Common → Common)
    (full reduced : State Common) (commonEq : full.common = reduced.common)
    (h : RelatedF full.frontier reduced.frontier) (coarse debt : Bool) :
    (stepState stepCommon full coarse debt).common =
      (stepState stepCommon reduced coarse debt).common ∧
    RelatedF (stepState stepCommon full coarse debt).frontier
      (stepState stepCommon reduced coarse debt).frontier := by
  exact ⟨congrArg stepCommon commonEq,
    forward_closes _ _ (backward_closes _ _ h coarse) debt⟩

/- A typed route is executable. These selectors are arbitrary native accessor
   outcomes. Accepted full paths justify projected paths; rejection of a
   foreign field is not silently converted into acceptance. -/
inductive FilterDecision where | accept | reject | next (state : Nat)
  deriving DecidableEq, Repr
abbrev Selector := Nat → Nat → FilterDecision

def keepPath (check : Selector) (state : Nat) : Path → Bool
  | [] => true
  | a :: rest => match check state a with
    | .accept => true
    | .reject => false
    | .next next => keepPath check next rest

theorem filter_accepts_prefix (check : Selector) (state : Nat) (p suffix : Path)
    (h : keepPath check state (p ++ suffix) = true) :
    keepPath check state p = true := by
  induction p generalizing state with
  | nil => rfl
  | cons a rest ih =>
    cases step : check state a with
    | accept => simp [keepPath, step]
    | reject => simp [keepPath, step] at h
    | next n =>
      simp only [List.cons_append, keepPath, step] at h ⊢
      exact ih n h

def PathPrefix (p q : Path) : Prop := ∃ suffix, p ++ suffix = q

theorem prepend_preserves_prefix (before p q : Path) (h : PathPrefix p q) :
    PathPrefix (before ++ p) (before ++ q) := by
  rcases h with ⟨suffix, rfl⟩
  exact ⟨suffix, List.append_assoc _ _ _⟩

inductive RouteStep where
  | copy (add : Path)
  | filter (state : Nat)
  deriving DecidableEq, Repr

def runRoute (check : Selector) : List RouteStep → Path → Option Path
  | [], p => some p
  | .copy add :: rest, p => runRoute check rest (add ++ p)
  | .filter state :: rest, p =>
      if keepPath check state p then runRoute check rest p else none

theorem route_preserves_projected_witness (check : Selector)
    (steps : List RouteStep) (p q out : Path) (prefixOf : PathPrefix p q)
    (accepted : runRoute check steps q = some out) :
    ∃ projected, runRoute check steps p = some projected ∧ PathPrefix projected out := by
  induction steps generalizing p q out with
  | nil =>
    simp only [runRoute, Option.some.injEq] at accepted
    subst out
    exact ⟨p, rfl, prefixOf⟩
  | cons step more ih =>
    cases step with
    | copy add =>
      exact ih (add ++ p) (add ++ q) out (prepend_preserves_prefix add p q prefixOf) accepted
    | filter state =>
      have fullKept : keepPath check state q = true := by
        cases h : keepPath check state q <;> simp_all [runRoute]
      have projectedKept : keepPath check state p = true := by
        rcases prefixOf with ⟨suffix, rfl⟩
        exact filter_accepts_prefix check state p suffix fullKept
      have rest := ih p q out prefixOf (by simpa [runRoute, fullKept] using accepted)
      simpa [runRoute, projectedKept] using rest

def firstField (p : Path) : Path := p.take 1

def refinedChild (i : Fact) : Fact :=
  match i.path with
  | [] => i
  | f :: rest =>
    let exact := i.tail == .exact && rest.isEmpty
    ⟨[f], if exact then .exact else .star,
      if exact then i.layer else .demand, [], false⟩

theorem refined_child_is_actual_c2_start (i : Fact) (h : i.path ≠ []) :
    refinedChild i ∈ selected (c2Any ⟨i, true⟩) := by
  cases i with | mk path tail layer excluded flag =>
    cases path with
    | nil => exact False.elim (h rfl)
    | cons f rest =>
      cases tail <;> cases rest <;>
        simp [refinedChild, selected, c2Any]


theorem first_field_is_prefix (p : Path) : PathPrefix (firstField p) p := by
  exact ⟨p.drop 1, List.take_append_drop _ _⟩

theorem valid_first_field_route (check : Selector) (steps : List RouteStep)
    (p out : Path) (accepted : runRoute check steps p = some out) :
    ∃ projected, runRoute check steps (firstField p) = some projected ∧
      PathPrefix projected out :=
  route_preserves_projected_witness check steps _ _ _ (first_field_is_prefix p) accepted

/- C5 cap never turns a nonempty selected path into the root when cap >= 1.
   This is the geometry fact used before the nonempty-source C5 case. -/
def capFact (cap : Nat) (f : Fact) : Fact :=
  if f.path.length > cap then
    { f with path := f.path.take cap, tail := .may, layer := .demand }
  else f

theorem cap_keeps_nonempty (cap : Nat) (positive : cap > 0) (f : Fact)
    (h : f.path ≠ []) : (capFact cap f).path ≠ [] := by
  cases f with | mk p t l e flag =>
    cases p with
    | nil => exact False.elim (h rfl)
    | cons a rest =>
      cases cap with
      | zero => omega
      | succ n =>
        by_cases cut : n < rest.length <;> simp [capFact, cut]

/- Derive the recurrence's input bits from the executable C2/body results.
   They are not user-supplied proof-success flags. -/
def coarseRootOffers (offers : List Offer) : Bool :=
  offers.any (fun a => a.inputKept && a.fact.path.isEmpty &&
    (a.fact.tail == .star || a.fact.tail == .may))

def rootDebt (content : Nat) (offers : List Offer) : Bool :=
  offers.any (fun a => (selected (c2Any a)).any (fun i =>
    let rows := bodyRows (execute content i)
    (c5Exact rows).any (fun r => !(c5Broad rows).contains r)))

def runPair (content : Nat) (d : ForwardFrontier)
    (backwardOffers forwardOffers : List Offer) : ForwardFrontier :=
  cycle d (coarseRootOffers backwardOffers) (rootDebt content forwardOffers)

theorem executable_pair_closes (content : Nat) (full reduced : ForwardFrontier)
    (h : RelatedF full reduced) (backwardOffers forwardOffers : List Offer) :
    RelatedF (runPair content full backwardOffers forwardOffers)
      (runPair content reduced backwardOffers forwardOffers) :=
  forward_closes _ _ (backward_closes _ _ h _) _

/- `runPair` is an executable scoped recurrence. Its quotient correspondence
   to all native paired C2/C5 rows and caller application is not established
   merely by the closure theorem. In particular, common native rows must be
   interpreted, not replaced with empty rows or the Boolean frontier. -/


/- Scoped interpreter with actual deletion points and permission gating. Each
   route is a complete ordinary copy/filter branch of the extracted acyclic
   graph. It is not a generated set of observed endpoint summaries. -/
def runFactRoute (check : Selector) (steps : List RouteStep) (i : Fact) : Option Fact :=
  (runRoute check steps i.path).map (fun p => { i with path := p })

theorem route_nonempty (check : Selector) (steps : List RouteStep) (p out : Path)
    (nonempty : p ≠ []) (accepted : runRoute check steps p = some out) : out ≠ [] := by
  induction steps generalizing p out with
  | nil =>
    simp only [runRoute, Option.some.injEq] at accepted
    simpa only [← accepted] using nonempty
  | cons step more ih =>
    cases step with
    | copy add =>
      apply ih (add ++ p) out _ accepted
      intro empty
      exact nonempty (List.append_eq_nil_iff.mp empty).2
    | filter state =>
      cases keep : keepPath check state p with
      | false => simp [runRoute, keep] at accepted
      | true => exact ih p out nonempty (by simpa [runRoute, keep] using accepted)

structure SourcePlan where
  ordinaryRoutes : List (List RouteStep)
  sourceRoutes : List (List RouteStep)

def ordinaryPlanRows (check : Selector) (plan : SourcePlan) (i : Fact) : List Fact :=
  plan.ordinaryRoutes.flatMap (fun route =>
    (runFactRoute check route i).toList.flatMap cleanExactRoot)

def permitted (ids : PermissionIds) (permissions : List Nat) (i : Fact) : Bool :=
  permissions.contains ids.anyLeaf ||
    (i.path.isEmpty && permissions.contains ids.exactLeaf)

def sourceRouteAvailable (check : Selector) (plan : SourcePlan) (i : Fact) : Bool :=
  plan.sourceRoutes.any (fun route => (runFactRoute check route i).isSome)

def sourceRouteEnabled (check : Selector) (plan : SourcePlan) (ids : PermissionIds)
    (permissions : List Nat) (i : Fact) : Bool :=
  plan.sourceRoutes.any (fun route => match runFactRoute check route i with
    | none => false
    | some atSource => permitted ids permissions atSource)

def scopedRows (check : Selector) (plan : SourcePlan) (ids : PermissionIds)
    (permissions : List Nat) (i : Fact) : List Fact :=
  let ordinary := ordinaryPlanRows check plan i
  ordinary ++ if sourceRouteEnabled check plan ids permissions i &&
      !rootMayMasks ordinary (source i) then [source i] else []

theorem selected_any_permission (ids : PermissionIds) (permissions : List Nat)
    (i : Fact) (h : ids.anyLeaf ∈ permissions) : permitted ids permissions i = true := by
  simp [permitted, h]

theorem clean_nonempty (i r : Fact) (h : i.path ≠ []) (row : r ∈ cleanExactRoot i) :
    r.path ≠ [] := by
  cases i with | mk path tail layer excluded flag =>
    cases path with
    | nil => exact False.elim (h rfl)
    | cons f fs =>
      have eq : r = ⟨f :: fs, tail, layer, excluded, true⟩ := by
        simpa [cleanExactRoot] using row
      subst r
      simp

theorem ordinary_nonempty (check : Selector) (plan : SourcePlan) (i : Fact)
    (h : i.path ≠ []) : ∀ r ∈ ordinaryPlanRows check plan i, r.path ≠ [] := by
  intro r hr
  simp only [ordinaryPlanRows, List.mem_flatMap] at hr
  rcases hr with ⟨route, _, value, hv, cleaned⟩
  cases equation : runRoute check route i.path with
  | none => simp [runFactRoute, equation] at hv
  | some out =>
    have same : value = { i with path := out } := by
      simpa [runFactRoute, equation] using hv
    subst value
    exact clean_nonempty _ r (route_nonempty check route i.path out h equation) cleaned

theorem mask_false_of_nonempty (rows : List Fact) (s : Fact)
    (h : ∀ r ∈ rows, r.path ≠ []) : rootMayMasks rows s = false := by
  simp only [rootMayMasks, List.any_eq_false]
  intro r hr
  have hn := h r hr
  have empty : List.isEmpty r.path = false := by
    cases eq : r.path <;> simp_all
  simp [empty]

theorem any_permission_enables_available_route (check : Selector) (plan : SourcePlan)
    (ids : PermissionIds) (permissions : List Nat) (i : Fact)
    (permission : ids.anyLeaf ∈ permissions)
    (available : sourceRouteAvailable check plan i = true) :
    sourceRouteEnabled check plan ids permissions i = true := by
  simp only [sourceRouteAvailable, List.any_eq_true] at available
  rcases available with ⟨route, present, accepted⟩
  simp only [sourceRouteEnabled, List.any_eq_true]
  refine ⟨route, present, ?_⟩
  cases atSource : runFactRoute check route i with
  | none => simp [atSource] at accepted
  | some value => simp [selected_any_permission ids permissions value permission]

theorem exact_only_content_route_disabled (check : Selector) (content : Nat)
    (ids : PermissionIds) (permissions : List Nat) (i : Fact)
    (noAny : ids.anyLeaf ∉ permissions) :
    sourceRouteEnabled check ⟨[], [[.copy [content]]]⟩ ids permissions i = false := by
  simp [sourceRouteEnabled, runFactRoute, runRoute, permitted, noAny]

theorem scoped_nonempty_source (check : Selector) (plan : SourcePlan)
    (ids : PermissionIds) (permissions : List Nat) (i : Fact)
    (h : i.path ≠ []) (permission : ids.anyLeaf ∈ permissions)
    (route : sourceRouteAvailable check plan i = true) :
    exactResult i.layer ∈ scopedRows check plan ids permissions i := by
  have visible := mask_false_of_nonempty (ordinaryPlanRows check plan i) (source i)
    (ordinary_nonempty check plan i h)
  unfold scopedRows
  dsimp only
  rw [any_permission_enables_available_route check plan ids permissions i permission route, visible]
  apply List.mem_append_right
  simp [source, exactResult]

/- Both complete leaf IDs are generated by the retained Y root start. -/
theorem retained_root_admission_keeps_permissions (ids : PermissionIds) (a : Offer)
    (kept : a.inputKept = true) (root : a.fact.path = []) :
    ids.exactLeaf ∈ backHitsFor ids (c2Any a) ∧
      ids.anyLeaf ∈ backHitsFor ids (c2Any a) := by
  cases a with | mk af keep =>
    cases af with | mk path tail layer excluded flag =>
      simp only at kept root
      subst keep
      subst path
      cases tail <;> simp [backHitsFor, selected, c2Any, backwardHits]

/- A complete valid source route constructs its projected route witness. -/
theorem projected_source_route_available (check : Selector) (plan : SourcePlan)
    (route : List RouteStep) (i : Fact) (out : Path)
    (present : route ∈ plan.sourceRoutes)
    (accepted : runRoute check route i.path = some out) :
    sourceRouteAvailable check plan (refinedChild i) = true := by
  obtain ⟨projected, witness, _⟩ := valid_first_field_route check route i.path out accepted
  simp only [sourceRouteAvailable, List.any_eq_true]
  refine ⟨route, present, ?_⟩
  cases path : i.path with
  | nil => simpa [runFactRoute, refinedChild, path, firstField] using congrArg Option.isSome witness
  | cons f rest =>
    simpa [runFactRoute, refinedChild, path, firstField] using congrArg Option.isSome witness

/- This is the native source-route component needed for a strict child. The
   accepted route is an executable witness, and the permission is produced
   from Y by the theorem above; neither is an unconditional pass operation. -/
theorem valid_child_source_replacement (check : Selector) (plan : SourcePlan)
    (ids : PermissionIds) (permissions : List Nat) (i : Fact)
    (h : (refinedChild i).path ≠ []) (permission : ids.anyLeaf ∈ permissions)
    (route : List RouteStep) (out : Path) (present : route ∈ plan.sourceRoutes)
    (accepted : runRoute check route i.path = some out) :
    exactResult (refinedChild i).layer ∈ scopedRows check plan ids permissions
      (refinedChild i) := by
  apply scoped_nonempty_source check plan ids permissions _ h permission
  exact projected_source_route_available check plan route i out present accepted


/- Exact common-entry C2/C5 gate. This is the selected-T root projection of
   arbitrary complete demand rows. Other mark/owner/path lanes remain shared;
   a deeper demanded path cannot store a root selected-T initial. -/
inductive RequiredMark where | selected | flow | other (id : Nat)
  deriving DecidableEq, Repr
structure CommonEntry where
  path : Path
  tail : Tail
  mark : RequiredMark
  excluded : List Nat
  deriving DecidableEq, Repr

def canStoreRoot (d : CommonEntry) (tail : Tail) : Bool :=
  d.mark == .selected && d.path.isEmpty &&
    match tail with
    | .exact => d.tail != .must && (d.tail != .exact || d.excluded.isEmpty)
    | .star | .must => d.tail == .may
    | .may => false

def commonRootStarts (d : CommonEntry) (a : Offer) : List Fact :=
  if d.mark != .selected || !d.path.isEmpty then [] else
  match d.tail with
  | .exact => if d.excluded.isEmpty then selected (c2Exact a) else []
  | .star => selected (c2Exact a)
  | .may => selected (c2Any a)
  | .must => []

def exactDebtStart : Fact := ⟨[], .exact, .demand, [], false⟩
def broadDebtStart : Fact := ⟨[], .star, .demand, [], false⟩
def CoarseRoot (a : Offer) : Prop :=
  a.inputKept = true ∧ a.fact.path = [] ∧
    (a.fact.tail = .star ∨ a.fact.tail = .may) ∧ a.fact.layer = .demand

theorem coarse_root_y_starts_star (a : Offer) (h : CoarseRoot a) :
    broadDebtStart ∈ selected (c2Any a) := by
  cases a with | mk af kept =>
    cases af with | mk path tail layer excluded flag =>
      rcases h with ⟨rfl, rfl, tails, rfl⟩
      rcases tails with rfl | rfl <;> simp [c2Any, selected, broadDebtStart]

theorem common_row_exact_or_star (d : CommonEntry) (a : Offer)
    (coarse : CoarseRoot a) (accepts : canStoreRoot d .exact = true) :
    exactDebtStart ∈ commonRootStarts d a ∨ canStoreRoot d .star = true := by
  cases d with | mk path tail mark e =>
    cases path <;> cases tail <;> cases mark <;>
      simp_all [canStoreRoot, commonRootStarts]
    all_goals
      cases a with | mk af kept =>
        cases af with | mk path tail layer excluded flag =>
          rcases coarse with ⟨rfl, rfl, tails, rfl⟩
          rcases tails with rfl | rfl <;>
            simp_all [c2Exact, selected, exactDebtStart]

/- The common exit restriction is an arbitrary shared function. It may have
   any paths, field exclusions, mark exclusions or output cap. Both starts
   feed the identical source payload to that SAME function; it is not forced
   to return the empty set, nor assumed to preserve every raw row. -/
def backwardPayload : Fact := ⟨[], .may, .demand, [], true⟩
structure ScopedRow where
  initial : Fact
  output : Fact
  deriving DecidableEq, Repr

def restrictCommon (d : CommonEntry) (starts : List Fact)
    (restrictExit : Fact → List Fact) : List ScopedRow :=
  starts.flatMap (fun i => if canStoreRoot d i.tail then
    (restrictExit backwardPayload).map (fun out => ⟨i, out⟩) else [])

def HeaderRelated (full reduced : Fact) : Prop :=
  full = reduced ∨ (full = exactDebtStart ∧ reduced = broadDebtStart)

theorem common_paired_c5_witness (d : CommonEntry) (a : Offer)
    (coarse : CoarseRoot a) (accepts : canStoreRoot d .exact = true)
    (restrictExit : Fact → List Fact) (out : Fact)
    (observed : out ∈ restrictExit backwardPayload) (otherStarts : List Fact) :
    ∃ row ∈ restrictCommon d
      (selected (c2Any a) ++ commonRootStarts d a ++ otherStarts) restrictExit,
      HeaderRelated exactDebtStart row.initial ∧ row.output = out := by
  rcases common_row_exact_or_star d a coarse accepts with identical | paired
  · refine ⟨⟨exactDebtStart, out⟩, ?_, Or.inl rfl, rfl⟩
    simp only [restrictCommon, List.mem_flatMap]
    refine ⟨exactDebtStart, ?_, ?_⟩
    · simp [identical]
    · simp [exactDebtStart, accepts, observed]
  · refine ⟨⟨broadDebtStart, out⟩, ?_, Or.inr ⟨rfl, rfl⟩, rfl⟩
    simp only [restrictCommon, List.mem_flatMap]
    refine ⟨broadDebtStart, ?_, ?_⟩
    · simp only [List.mem_append]
      exact Or.inl (Or.inl (coarse_root_y_starts_star a coarse))
    · simp [broadDebtStart, paired, observed]

end Thing2RootDebtCandidate

#print axioms Thing2RootDebtCandidate.c2_child_stays_nonempty
#print axioms Thing2RootDebtCandidate.c2_extra_exact_is_demand
#print axioms Thing2RootDebtCandidate.addPrefix_nonempty
#print axioms Thing2RootDebtCandidate.root_filter_keeps
#print axioms Thing2RootDebtCandidate.content_filter_keeps
#print axioms Thing2RootDebtCandidate.nonempty_source_not_masked
#print axioms Thing2RootDebtCandidate.nonempty_c5_exact_is_source
#print axioms Thing2RootDebtCandidate.nonempty_exact_already_broad
#print axioms Thing2RootDebtCandidate.full_only_shape
#print axioms Thing2RootDebtCandidate.every_kept_offer_has_replacement
#print axioms Thing2RootDebtCandidate.backward_permission_sets
#print axioms Thing2RootDebtCandidate.normal_persistence_unchanged
#print axioms Thing2RootDebtCandidate.backward_closes
#print axioms Thing2RootDebtCandidate.forward_closes
#print axioms Thing2RootDebtCandidate.all_future_frontiers
#print axioms Thing2RootDebtCandidate.shared_state_preserved

#print axioms Thing2RootDebtCandidate.filter_accepts_prefix
#print axioms Thing2RootDebtCandidate.prepend_preserves_prefix
#print axioms Thing2RootDebtCandidate.route_preserves_projected_witness
#print axioms Thing2RootDebtCandidate.first_field_is_prefix
#print axioms Thing2RootDebtCandidate.valid_first_field_route
#print axioms Thing2RootDebtCandidate.cap_keeps_nonempty
#print axioms Thing2RootDebtCandidate.executable_pair_closes

#print axioms Thing2RootDebtCandidate.route_nonempty
#print axioms Thing2RootDebtCandidate.selected_any_permission
#print axioms Thing2RootDebtCandidate.clean_nonempty
#print axioms Thing2RootDebtCandidate.ordinary_nonempty
#print axioms Thing2RootDebtCandidate.mask_false_of_nonempty
#print axioms Thing2RootDebtCandidate.scoped_nonempty_source
#print axioms Thing2RootDebtCandidate.retained_root_admission_keeps_permissions
#print axioms Thing2RootDebtCandidate.projected_source_route_available
#print axioms Thing2RootDebtCandidate.valid_child_source_replacement

#print axioms Thing2RootDebtCandidate.coarse_root_y_starts_star
#print axioms Thing2RootDebtCandidate.common_row_exact_or_star
#print axioms Thing2RootDebtCandidate.common_paired_c5_witness

#print axioms Thing2RootDebtCandidate.refined_child_is_actual_c2_start

#print axioms Thing2RootDebtCandidate.any_permission_enables_available_route
#print axioms Thing2RootDebtCandidate.exact_only_content_route_disabled
