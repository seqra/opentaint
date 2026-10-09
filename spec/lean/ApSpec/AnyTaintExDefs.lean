/-
  ApSpec.AnyTaintExDefs — the DEFINITIONS of the EXCLUSION of the forward `[any-taint]`
  conclusion (decision F69, DESIGN §6, amendment A2).

  This module holds only definitions, small lemmas and `decide` vectors. The proof files import it.
  The design brief is `any-taint/DESIGN.md`; this file models §6 A2 (authoritative where it differs
  from §0).

  ## The meaning of the exclusion (DESIGN A2)

  A forward NORMAL `.any` conclusion with a concrete mark (the spec tail `[any-taint]`) can carry a
  finite EXCLUSION `E` of first accessors: `(b, P, [any-taint], E, T)`. An accessor `x ∈ E` cannot be
  the first accessor after `P`. As a location set it is
      `(b, P ++ τ, T)` for every `τ` that `E` admits (`Excl.admits`, `coversFX`).
  It is UNCORRELATED: every location of the premise relates to every admitted `τ` (`denX`). Only the
  forward `[any-taint]` carries it: a demand `.any` (`[any]`) never has one (the normal form `normX`
  drops it), and a `$` or `*` fact never has one (a `*` tail has its own exclusion in `Kind.star e`).
  A PREMISE can carry an exclusion too: a must-premise emitted from an `[any-taint]/E` added fact
  (`emitX`; the model also lets a `*/E'` premise emitted at the path of an `[any-taint]/E` fact keep
  `E`, see `emitX`).

  The exclusion REPLACES the demotion at an exclusion (decision 5, exclusion part): where the base
  model demotes an `[any-taint]` fact to the demand layer ONLY because an exclusion meets it (the keep
  edge of a strong write, a `*/E` summary or record; the cleaners `atAndBelow`/`below` one accessor
  below the fact), the refined result stays NORMAL and carries the exclusion.

  ## The relation to the base model

  The base model is `AnyTaintDefs.lean` (`D6T`, `DRT`, `TObj`). Every refined operation is the base
  operation plus the annotation rules (`annX`): the FACT of every result (forget `ex`) is a fact that
  the base operation gives, and the LAYER is the base layer except at the rows where the base demoted
  ONLY because of an exclusion (`annX` returns `keep = true`): there the result keeps the layer of the
  input (`layerX`). The one exception to "the same fact" is the `below` cleaner one accessor below an
  `[any-taint]/E` fact: it also keeps the position itself as `(b, P.f, $, T)`, a fact that the base
  does not have (`partX`; see the vector `Vec.below_new_fact`). The relations `Refines6`/`RefinesR`
  (the same base fact) and `Inside6`/`InsideR` (location inclusion) and the statements `Sim6X`,
  `SimRX`, `Sim6XIn`, `SimRXIn` are the simulation that the proof files prove.

  ## Contents

  1. The annotated fact: `concB`, `XFact`, `carriesB`, `normX`, `WFX`, `plain`; the location sets
     `coversX`, `coversFX`, the edge relation `denX`.
  2. Location tests with exclusions: `overlapX`, `insideExB`, `satX`, `normJ`.
  3. The refined operations: `keepB`, `annX`, `layerX`, `ResX`, `applyEdgeX`, `bindX`,
     `applySummaryX`, `w6tX`, `applyEdgeXT`, `applyAllXT`, `limitFX`, `transferX`, `cleanPosX`,
     `partX`, `cleanResX`, `checkX`, `startX`, `recLayerX`, `emitX`, `emitTX`, `restrictConcX`,
     `restrictX`.
  4. The closures: `XObj6` and `D6X` (run 1), `XObj` and `DRX` (the restricted forward run).
  5. The relation to the base: `XObj6.forget`, `XObj.forget`, `Refines6`, `RefinesR`, `Inside6`,
     `InsideR`, `RecsRefine`, `NoBelowCleaner`, `Sim6X`, `SimRX`, `Sim6XIn`, `SimRXIn`.
  6. The predicates of the exactness and confirmation files: `EdgeOK6X`, `EndExactX`, `EdgeOKX`,
     `RecsExactX`, `SatInsideX`, `EmitContractX`, `EmitCopiesMarkX`, `RestrictContractX`,
     `RestrictSubX`, `Sup6X`, `Confirmed6X`, `SupLinkX`, `SupX`, `ConfirmedX`.
  7. Small lemmas.
  8. Vectors (`Vec`).

  All proofs are constructive (only `propext`, `Quot.sound`; see the `#print axioms` lines).
-/
import ApSpec.AnyTaintDefs

namespace ApSpec.AnyTaintEx
open ApSpec ApSpec.AnyTaint

/-! ## 1. The annotated fact -/

/-- The mark is concrete (`T`). -/
def concB : MarkA → Bool
  | .conc _ => true
  | _       => false

/-- An ANNOTATED final fact (DESIGN A2): a final fact with the layer of its edge (`af`, the base
    `AFact`) and an EXCLUSION `ex` of first accessors. `ex` has a meaning only on a normal `.any`
    fact with a concrete mark (`carriesB`, the spec `[any-taint]/E`); the normal form `normX` drops it
    on every other fact. -/
structure XFact where
  af : AFact
  ex : Excl
deriving DecidableEq, Repr

/-- The fact can carry an exclusion: it is `[any-taint]`, a NORMAL `.any` fact with a CONCRETE mark
    (DESIGN A2: "a demand-layer `[any]` has NO exclusion"; a `$` or `*` fact has none). -/
def carriesB (f : AFact) : Bool := f.fact.kind.isAny && !f.demand && concB f.fact.mark

/-- The normal form (DESIGN A2): keep the exclusion only on a fact that can carry one. The fact and
    the layer do not change (`normX_af`). -/
def normX (x : XFact) : XFact := if carriesB x.af then x else ⟨x.af, Excl.empty⟩

/-- The well-formedness of an annotated fact: only a fact that can carry an exclusion has one. Every
    refined operation gives well-formed results (`applyEdgeX_wf`, …). -/
def WFX (x : XFact) : Prop := carriesB x.af = false → x.ex = Excl.empty

/-- A base fact with no annotation. -/
def plain (f : AFact) : XFact := ⟨f, Excl.empty⟩

/-- The location set of a fact `i` with an exclusion `ex`, read as a premise (ap.md §3.2 `covers`
    with DESIGN A2): the base, the paths `i.path ++ σ` that the tail AND the exclusion admit, the marks
    that the mark admits. With `ex = Excl.empty` it is `PFact.covers` (`covers_coversX`,
    `coversX_covers`). -/
def coversX (i : PFact) (ex : Excl) (l : Loc) : Prop :=
  l.base = i.base ∧ (∃ σ, l.path = i.path ++ σ ∧ tailI i.kind σ ∧ ex.admits σ = true) ∧
    i.mark.admits l.mark

/-- The location set of a conclusion with a concrete mark and an exclusion (`AnyTaint.coversF` with
    DESIGN A2): a normal `[any-taint]/E` conclusion says that EVERY such location carries the mark. -/
def coversFX (f : PFact) (ex : Excl) (l : Loc) : Prop :=
  l.base = f.base ∧ (∃ τ, l.path = f.path ++ τ ∧ tailI f.kind τ ∧ ex.admits τ = true) ∧
    ∃ t, f.mark = .conc t ∧ l.mark = t

/-- The pair relation of an annotated edge `(i, iex) → (f, fex)` (ap.md §3.2 `den` with DESIGN A2):
    `den i f`, and the premise continuation `σ` is admitted by the premise exclusion `iex` (a
    must-premise `[any-taint]/E`), the conclusion continuation `τ` by the conclusion exclusion `fex` (an
    `[any-taint]/E` conclusion). An `.any` conclusion is uncorrelated (`tailF .any σ τ = True`), so
    every admitted premise location relates to every admitted `τ`. -/
def denX (i : PFact) (iex : Excl) (f : PFact) (fex : Excl) (l0 l1 : Loc) : Prop :=
  l0.base = i.base ∧ l1.base = f.base ∧ i.mark.admits l0.mark ∧
  l1.mark = f.mark.out l0.mark ∧ f.mark.passes l0.mark ∧
  ∃ σ τ, l0.path = i.path ++ σ ∧ l1.path = f.path ++ τ ∧ tailI i.kind σ ∧ tailF f.kind σ τ ∧
    iex.admits σ = true ∧ fex.admits τ = true

/-! ## 2. Location tests with exclusions -/

/-- The overlap of two location sets with exclusions, marks ignored (ap.md §3.2 `overlapB` with
    DESIGN A2: "read `E` as part of the location set"). `overlapB a b`, and the deeper fact lies in the
    admitted part of the other one: for `b` at `a.path ++ r`, `aex` admits `r` (for `r = []` always);
    for `a` at `b.path ++ r`, `bex` admits `r`. -/
def overlapX (a : PFact) (aex : Excl) (b : PFact) (bex : Excl) : Bool :=
  overlapB a b &&
  match relate a.path b.path with
  | .below r => aex.admits r
  | .above r => bex.admits r
  | .apart   => false

/-- The exclusion part of "the premise `(j, jex)` lies INSIDE the added fact `(a, aex)`": `j` at the
    path of `a`: `aex` excludes at most what `j` excludes (`aex.subB (tailExcl j.kind ∪ jex)`; a `$`
    premise: always); `j` strictly below `a` at `a.path ++ r`: `aex` admits `r`; otherwise `false`. -/
def insideExB (j : PFact) (jex : Excl) (a : PFact) (aex : Excl) : Bool :=
  match relate a.path j.path with
  | .below []      => aex.subB ((tailExcl j.kind).union jex)
  | .below (x :: r) => aex.admits (x :: r)
  | _              => false

/-- The satisfaction of a restricted run with exclusions (ap.md §4.3 `inside` with DESIGN A2): the
    base `satI` (the location part of `a` covers `j`, the mark of `j` is a sub-mark of the mark of `a`)
    AND the exclusion part `insideExB`: the premise `j` with its exclusion `jex` lies inside the added
    fact `a` with its exclusion `aex`. So `satX` implies `satI` (`satX_satI`). -/
def satX (j : PFact) (jex : Excl) (a : PFact) (aex : Excl) : Bool :=
  satI j a && insideExB j jex a aex

/-- The normal form of a premise exclusion: a `$` premise has no continuation, so no exclusion. -/
def normJ (j : PFact) (jex : Excl) : Excl :=
  match j.kind with
  | .exact => Excl.empty
  | _      => jex

/-! ## 3. The refined operations -/

/-- The input can take the exclusion rows of DESIGN A2: an `.any` fact with a concrete mark. (Its
    layer decides the layer of the result, `layerX`.) -/
def keepB (c : XFact) : Bool := c.af.fact.kind.isAny && concB c.af.fact.mark

/-- THE ANNOTATION RULES of DESIGN A2 for one application of the edge `(fr, fex) → (to, tex)` to the
    annotated fact `c` (`fex`: the exclusion of a must-premise of a summary or a record; `tex`: the
    exclusion of an `[any-taint]/E` summary conclusion; both `Excl.empty` for a micro edge).
    The result is `none` when the exclusions remove every common location (then there is no result
    and no request), else `some (keep, ex)`:
    * `ex` is the exclusion of the result (`normX` drops it unless the result is `[any-taint]`);
    * `keep = true` marks the two rows where the base demotes ONLY because an exclusion meets an
      `.any` fact (`belowCase` `.any`/`r = []`/`*` target with a non-empty `tailExcl fk ∪ et`, and
      `aboveCase` `*` target with `!(ck.isAny && (tailExcl fk ∪ et).isEmptyB)`): there the refined
      result keeps the layer of `c` (`layerX`).
    The rows (`r` from `relate fr.path c.path`):
    * case `below []` (`c` at the premise): a `*/et` target gives `E ∪ tailExcl fk ∪ fex ∪ et`
      (`keep`: the exclusion edge "`[any-taint]/E` meets `*/E'`"); an `.any` target gives `tex` (a
      micro edge: `{}`; a may target is then demand by W6T); a `$` target gives `$`;
    * case `below r`, `r ≠ []` (`c` strictly below the premise): the premise exclusion `fex` must admit
      `r` (else no common location); a `*` target keeps `E` at the new path end `to.path ++ r`; an
      `.any` target gives `tex`; a `$` target `$`. The exclusion `E` of `c` restricts the continuation
      after `c.path`, not `r`, so it does not filter this case;
    * case `above r` (`c` above the premise): `E` must admit `r` (else no result); a `*/et` target
      gives `tailExcl fk ∪ fex ∪ et` (`keep`); an `.any` target gives `tex` (a source: `{}`); `$` gives
      `$`;
    * `apart`: the base gives nothing. -/
def annX (c : XFact) (fr : PFact) (fex : Excl) (to : PFact) (tex : Excl) : Option (Bool × Excl) :=
  match relate fr.path c.af.fact.path with
  | .below [] =>
    match to.kind with
    | .star et => some (keepB c, ((c.ex.union (tailExcl fr.kind)).union fex).union et)
    | .any     => some (false, tex)
    | .exact   => some (false, Excl.empty)
  | .below (x :: r) =>
    if fex.admits (x :: r) then
      match to.kind with
      | .star _ => some (false, c.ex)
      | .any    => some (false, tex)
      | .exact  => some (false, Excl.empty)
    else none
  | .above r =>
    if c.ex.admits r then
      match to.kind with
      | .star et => some (keepB c, ((tailExcl fr.kind).union fex).union et)
      | .any     => some (false, tex)
      | .exact   => some (false, Excl.empty)
    else none
  | .apart => some (false, Excl.empty)

/-- The layer of a refined result: at a `keep` row, the layer of the input `cd` (a normal input gives
    a normal result: the exclusion no longer demotes, DESIGN A2); elsewhere the base layer. -/
def layerX (keep cd : Bool) (y : AFact) : AFact :=
  if keep && !cd then ⟨y.fact, false⟩ else y

/-- The result of a refined operation: annotated facts and mark requests. -/
structure ResX where
  facts : List XFact
  reqs  : List Mark
deriving DecidableEq, Repr

def ResX.none : ResX := ⟨[], []⟩

def ResX.append (a b : ResX) : ResX := ⟨a.facts ++ b.facts, a.reqs ++ b.reqs⟩

/-- THE REFINED CORE OPERATION (ap.md §4.1 with DESIGN A2): the base `applyEdge` on the base fact,
    then the annotation rules `annX` on each result (its layer by `layerX`, its exclusion by `annX`,
    then `normX`). No result and no request if the exclusions remove every common location. So every
    result has the fact of a base result (`applyEdgeX_base`), and an input that cannot carry an
    exclusion, with an edge without annotation, gives exactly the base results (`applyEdgeX_plain`). -/
def applyEdgeX (c : XFact) (fr : PFact) (fex : Excl) (to : PFact) (tex : Excl) : ResX :=
  match annX c fr fex to tex with
  | none => ResX.none
  | some (keep, ex) =>
    ⟨(applyEdge c.af fr to).facts.map (fun y => normX ⟨layerX keep c.af.demand y, ex⟩),
     (applyEdge c.af fr to).reqs⟩

/-- A call binding edge or a statement micro edge (no annotation; no W6T for a binding, as the
    base rules `added`, `ret`). -/
def bindX (c : XFact) (e : MicroEdge) : ResX := applyEdgeX c e.1 Excl.empty e.2 Excl.empty

/-- The refined summary application (ap.md §4.3 with DESIGN A2): the summary `(j, jex) → g` (a
    must-premise can carry `jex`, an `[any-taint]` conclusion `g` carries `g.ex`), applied as the base
    `applySummary` does: `applyEdgeX`, then the layer of the summary edge and `norm`. The result has the
    exclusion of `g` when it has the `.any` tail of `g`; a `*` summary conclusion on an annotated `.any`
    input at `r = []` gives `E ∪ tailExcl j.kind ∪ jex ∪ et` (`annX`). -/
def applySummaryX (a : XFact) (j : PFact) (jex : Excl) (g : XFact) : ResX :=
  let r := applyEdgeX a j jex g.af.fact g.ex
  ⟨r.facts.map (fun x => normX ⟨AFact.norm ⟨x.af.fact, x.af.demand || g.af.demand⟩, x.ex⟩), r.reqs⟩

/-- W6T on an annotated fact (`AnyTaint.w6t`): a demoted result drops its exclusion. -/
def w6tX (taint : TaintEdges) (e : MicroEdge) (x : XFact) : XFact :=
  if e.2.kind.isAny && !taint e then ⟨⟨x.af.fact, true⟩, Excl.empty⟩ else x

/-- One statement micro edge with W6T on each result (`AnyTaint.applyEdgeT`). -/
def applyEdgeXT (taint : TaintEdges) (c : XFact) (e : MicroEdge) : ResX :=
  ⟨(bindX c e).facts.map (w6tX taint e), (bindX c e).reqs⟩

/-- `applyEdgeXT` on each micro edge of a statement (`AnyTaint.applyAllT`). -/
def applyAllXT (taint : TaintEdges) (c : XFact) : List MicroEdge → ResX
  | []      => ResX.none
  | e :: es => (applyEdgeXT taint c e).append (applyAllXT taint c es)

/-- The field limit (ap.md §4.4 with DESIGN A2): a cut gives the base cut fact (`.any`, demand) and
    DROPS the exclusion (the cut path is above the fact, so not every location below it carries the
    mark); a fact within the limit does not change. -/
def limitFX (counted : Acc → Bool) (L : Nat) (x : XFact) : XFact :=
  match cutPath counted L x.af.fact.path with
  | none   => x
  | some _ => ⟨limitF counted L x.af, Excl.empty⟩

/-- The refined statement transfer (`AnyTaint.transferT` with DESIGN A2): `applyEdgeXT` on each micro
    edge, then `limitFX`. A fact on an untouched base passes with its exclusion. -/
def transferX (taint : TaintEdges) (counted : Acc → Bool) (L : Nat) (s : Stmt) (c : XFact) : ResX :=
  if memB c.af.fact.base s.touched then
    let r := applyAllXT taint c s.edges
    ⟨r.facts.map (limitFX counted L), r.reqs⟩
  else ⟨[c], []⟩

/-- The position of an annotated fact against a cleaner (ap.md §4.7 `cleanPos` with DESIGN A2: "the
    excluded part read as absent"): a cleaner strictly below the fact at `c.path ++ r` with `r`
    excluded by `E` cleans no location of the fact (`disjoint`); every other row as `cleanPos`. -/
def cleanPosX (cl : Cleaner) (c : XFact) : CPos :=
  match relate cl.path c.af.fact.path with
  | .above r => if c.ex.admits r then cleanPos cl c.af.fact else .disjoint
  | _        => cleanPos cl c.af.fact

/-- The `part` result of a cleaner on a fact with a cleaned CONCRETE mark (ap.md §4.7 `concPart` with
    DESIGN A2). For an `[any-taint]/E` fact `c` at `P` (`carriesB`) and a cleaner one accessor below,
    at `P.f` (`f` admitted by `E`, else `cleanPosX` is `disjoint`):
    * `atAndBelow` at `P.f`: `c` with `E ∪ {f}`, in the layer of `c`;
    * `below` at `P.f`: `c` with `E ∪ {f}`, and the position itself `(b, P.f, $, T)` (the cleaner
      cleans only strictly below `P.f`), both in the layer of `c`;
    * `exact` at `P.f`, and every other row: the base `concPart` (no shape for "every location but
      one": the demand layer, the exclusion dropped). -/
def partX (cl : Cleaner) (c : XFact) : List XFact :=
  let base : List XFact := [⟨concPart cl c.af, Excl.empty⟩]
  if carriesB c.af then
    match cl.reach, relate cl.path c.af.fact.path with
    | .atAndBelow, .above [f] => [⟨c.af, c.ex.union (.set [f])⟩]
    | .below,      .above [f] =>
      [⟨c.af, c.ex.union (.set [f])⟩,
       ⟨⟨⟨c.af.fact.base, c.af.fact.path ++ [f], .exact, c.af.fact.mark⟩, c.af.demand⟩, Excl.empty⟩]
    | _, _ => base
  else base

/-- The refined cleaner (ap.md §4.7 `cleanRes` with DESIGN A2): the base rows on `cleanPosX`; a
    result that is the fact itself (or the fact with a mark exclusion) keeps the exclusion; the `part`
    row of a cleaned concrete mark is `partX`; the all-marks `part` row of an abstract mark is the base
    demand result (no exclusion). -/
def cleanResX (cl : Cleaner) (c : XFact) : ResX :=
  match cleanPosX cl c with
  | .disjoint => ⟨[c], []⟩
  | .inside =>
    match c.af.fact.mark, cl.mark with
    | .conc t, _      => if cl.markB t then ResX.none else ⟨[c], []⟩
    | m,       some t =>
      ⟨[⟨⟨⟨c.af.fact.base, c.af.fact.path, c.af.fact.kind, addEx m t⟩, c.af.demand⟩, c.ex⟩], []⟩
    | _,       none   => ResX.none
  | .part =>
    match c.af.fact.mark, cl.mark with
    | .conc t, _      => if cl.markB t then ⟨partX cl c, []⟩ else ⟨[c], []⟩
    | m,       some t =>
      ⟨[⟨⟨⟨c.af.fact.base, c.af.fact.path, c.af.fact.kind, addEx m t⟩, c.af.demand⟩, c.ex⟩], [t]⟩
    | _,       none   => ⟨[⟨AFact.norm ⟨c.af.fact, true⟩, Excl.empty⟩], []⟩

/-- The refined sink check (ap.md §4.9 with DESIGN A2): the base `check`, if the sink pattern
    overlaps the ADMITTED location set of the fact (`overlapX`); else no trigger and no request. -/
def checkX (i : PFact) (f : XFact) (s : PFact) : Check :=
  if overlapX f.af.fact f.ex s Excl.empty then check i f.af s else .none

/-- The refined start fact (ap.md §6.5 with DESIGN A2): a must-premise `(j, [any-taint], jex, T)`
    starts as itself, NORMAL, with its exclusion; every other premise starts with `startFact`, with no
    exclusion (`AnyTaint.startT`). -/
def startX (j : PFact) (must : Bool) (jex : Excl) : XFact :=
  if must then normX ⟨⟨j, false⟩, jex⟩ else ⟨startFact j, Excl.empty⟩

/-- The record demotion (`AnyTaint.recLayer`) on an annotated fact: a demoted result drops its
    exclusion. -/
def recLayerX (mj satOk : Bool) (x : XFact) : XFact :=
  if mj && !satOk then ⟨⟨x.af.fact, true⟩, Excl.empty⟩ else x

/-- The refined emission (ap.md §6.3 with DESIGN A2): the base `emitM d a` gives the premise `j`; the
    exclusion `aex` of the added fact gives its exclusion:
    * `a` above the pattern chain (`d.path = a.path ++ r`): the pattern chain with no exclusion, if
      `aex` admits the step down `r`; nothing if not (no common location);
    * `a` at the pattern chain: `aex` (`normJ`: none on a `$` premise). This also holds for a `*/e`
      pattern (backward only): the premise `*/e` with a concrete mark keeps `aex`, so it lies inside `a`
      (`satX`); DESIGN A2 names only the must-premise;
    * `a` below the chain: `j = a`, with its exclusion. -/
def emitX (d a : PFact) (aex : Excl) : Option (PFact × Excl) :=
  match emitM d a with
  | none   => none
  | some j =>
    match relate d.path a.path with
    | .above r => if aex.admits r then some (j, Excl.empty) else none
    | _        => some (j, normJ j aex)

/-- The emission with the must flag (`AnyTaint.emitTWith` with DESIGN A2), for a given annotated
    emission `emit`: the premise is a must-premise iff the added fact is `[any-taint]` (`am`) and the
    premise has the `.any` tail. -/
def emitTX (emit : PFact → PFact → Excl → Option (PFact × Excl)) (d a : PFact) (am : Bool)
    (aex : Excl) : Option (PFact × Bool × Excl) :=
  (emit d a aex).map (fun p => (p.1, am && p.1.kind.isAny, p.2))

/-- The restricted conclusion (`restrictConcU` with DESIGN A2): `g` at or below `D-p` keeps its
    exclusion; `g` above `D-p` (`D-p.path = g.path ++ r`) gives the chain `D-p` with no exclusion if the
    exclusion of `g` admits `r` (every location below `D-p` is in `g`), nothing if not. -/
def restrictConcX (sc : XFact) (dout : PFact) : Option XFact :=
  match restrictConcU sc.af dout with
  | none    => none
  | some g' =>
    match relate dout.path sc.af.fact.path with
    | .above r => if sc.ex.admits r then some ⟨g', Excl.empty⟩ else none
    | _        => some (normX ⟨g', sc.ex⟩)

/-- The refined restriction (`restrictU` with DESIGN A2): the premise `(sp, spex)` must overlap `D-c`
    with its exclusion (`overlapX`); the conclusion by `restrictConcX`. -/
def restrictX (sp : PFact) (spex : Excl) (sc : XFact) (d : DemandEdge) : Option XFact :=
  match d.dout with
  | none   => none
  | some p => if overlapX sp spex d.din Excl.empty then restrictConcX sc p else none

/-! ## 4. The closures -/

/-- The objects of run 1 with annotated facts: `Obj` with an `XFact` on each edge. Run 1 has no
    must-premise and no premise exclusion. An added fact is the base `PFact` (the run-1 policy and the
    answers read only it). -/
inductive XObj6 where
  | init  (M : MethodId) (i : PFact)
  | edge  (M : MethodId) (i : PFact) (n : Node) (f : XFact)
  | added (M : MethodId) (a : PFact)
  | req   (M : MethodId) (i : PFact) (t : Mark)
  | vuln  (M : MethodId) (n : Node) (s : PFact) (demand : Bool)

section Closure6X
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- RUN 1 WITH THE EXCLUSION (DESIGN A2): the rules of `AnyTaint.D6T` with the refined operations:
    `startX` (no must-premise: `startFact`), `transferX`, `bindX`, `applySummaryX`, `limitFX`,
    `checkX`, `cleanResX`; `reqUp` reads the overlap with the exclusion (`overlapX`). The summary
    application keeps the base `applicable` (run 1, policy premises; DESIGN §4.3), and `answer` the base
    `overlapB` (the added fact of run 1 is a `PFact`). -/
inductive D6X : XObj6 → Prop where
  | root {M} : M ∈ roots → D6X (.init M zeroFact)
  | start {M i} : D6X (.init M i) → D6X (.edge M i (P.entry M) (startX i false Excl.empty))
  | step {M i n f n' s f'} :
      D6X (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transferX taint counted L s f).facts → D6X (.edge M i n' f')
  | reqStmt {M i n f n' s t} :
      D6X (.edge M i n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transferX taint counted L s f).reqs → D6X (.req M i t)
  | pass {M i n f n' c} :
      D6X (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.af.fact.base c.touched = false → D6X (.edge M i n' f)
  | added {M i n f n' c e a} :
      D6X (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (bindX f e).facts →
      D6X (.added c.callee a.af.fact)
  | initA {m a} : D6X (.added m a) → D6X (.init m (α m a))
  | ret {M i n f n' c e1 a j g r e2 r'} :
      D6X (.edge M i n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (bindX f e1).facts →
      D6X (.init c.callee j) →
      applicable j a.af.fact = true →
      D6X (.edge c.callee j (P.exit c.callee) g) →
      r ∈ (applySummaryX a j Excl.empty g).facts →
      e2 ∈ c.fromCallee → r' ∈ (bindX r e2).facts →
      D6X (.edge M i n' (limitFX counted L r'))
  | reqSink {M i n f s t} :
      D6X (.edge M i n f) → (M, n, s) ∈ sinks → checkX i f s = .request t →
      D6X (.req M i t)
  | answer {M i t a} :
      D6X (.req M i t) → D6X (.added M a) → a.mark = .conc t →
      overlapB a i = true → D6X (.init M (answerInit i a t))
  | reqUp {m j t M ic n f n' c e a} :
      D6X (.req m j t) → D6X (.edge M ic n f) → (M, n, Instr.call c, n') ∈ P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (bindX f e).facts →
      climbsB a.af.fact.mark t = true → overlapX a.af.fact a.ex j Excl.empty = true →
      D6X (.req M ic t)
  | vuln {M i n f s} :
      D6X (.edge M i n f) → (M, n, s) ∈ sinks → checkX i f s = .triggered →
      D6X (.vuln M n s f.af.demand)
  | clean {M i n f n' cl f'} :
      D6X (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanResX cl f).facts → D6X (.edge M i n' f')
  | reqClean {M i n f n' cl t} :
      D6X (.edge M i n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanResX cl f).reqs → D6X (.req M i t)
  | filt {M i n f n' b may} :
      D6X (.edge M i n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.af.fact.base = b → may f.af.fact.path = true) → D6X (.edge M i n' f)

end Closure6X

/-- The objects of a restricted forward run with must-premises and exclusions (`AnyTaint.TObj` with
    DESIGN A2):
    * `init M j must jex`: a premise; `must = true` is `[any-taint]`; `jex` its exclusion (a
      must-premise emitted from an `[any-taint]/E` added fact; `Excl.empty` otherwise, except the
      `*/e` premise at the path of such a fact, `emitX`);
    * `edge M j must jex n f`: an edge of the premise `(j, must, jex)` with an annotated conclusion;
    * `added M a am aex`: an added fact; `am`: it is `[any-taint]` on its link; `aex`: its exclusion;
    * `req`, `vuln`: as `TObj`. -/
inductive XObj where
  | init  (M : MethodId) (j : PFact) (must : Bool) (jex : Excl)
  | edge  (M : MethodId) (j : PFact) (must : Bool) (jex : Excl) (n : Node) (f : XFact)
  | added (M : MethodId) (a : PFact) (am : Bool) (aex : Excl)
  | req   (M : MethodId) (j : PFact) (t : Mark)
  | vuln  (M : MethodId) (n : Node) (s : PFact) (demand : Bool)

section ClosureRX
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Excl → Option (PFact × Excl))
  (sat : PFact → Excl → PFact → Excl → Bool)
  (restrict : PFact → Excl → XFact → DemandEdge → Option XFact)
  (recs : MethodId → PFact × Bool × Excl × XFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- THE RESTRICTED FORWARD RUN WITH THE EXCLUSION (DESIGN A2): the rules of `AnyTaint.DRT` with the
    refined operations and annotated premises, added facts and records:
    * `start`: `startX` (a must-premise starts normal with its exclusion);
    * `step`, `reqStmt`: `transferX`; `added`, `ret`, `retRec`, `reqUp`: `bindX`;
    * `added`: the must flag of the added fact and its exclusion;
    * `initR`: the emission `emitTX emit` (the spec instance is `emit = emitX`);
    * `ret`: `restrict` (spec: `restrictX`), `sat` (spec: `satX`), `applySummaryX`, `limitFX`;
    * `retRec`: the records `recs m (j, mj, jex, g)`; `sat` or the base `applicable`; a must record by
      `applicable` only gives a demand result (`recLayerX`);
    * `reqSink`, `vuln`: `checkX`; `clean`, `reqClean`: `cleanResX`; `answer`, `reqUp`: `overlapX`. -/
inductive DRX : XObj → Prop where
  | root {M} : M ∈ roots → DRX (.init M zeroFact false Excl.empty)
  | start {M j mj jex} :
      DRX (.init M j mj jex) → DRX (.edge M j mj jex (P.entry M) (startX j mj jex))
  | step {M i mi iex n f n' s f'} :
      DRX (.edge M i mi iex n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      f' ∈ (transferX taint counted L s f).facts → DRX (.edge M i mi iex n' f')
  | reqStmt {M i mi iex n f n' s t} :
      DRX (.edge M i mi iex n f) → (M, n, Instr.stmt s, n') ∈ P.edges →
      t ∈ (transferX taint counted L s f).reqs → DRX (.req M i t)
  | pass {M i mi iex n f n' c} :
      DRX (.edge M i mi iex n f) → (M, n, Instr.call c, n') ∈ P.edges →
      memB f.af.fact.base c.touched = false → DRX (.edge M i mi iex n' f)
  | added {M i mi iex n f n' c e a} :
      DRX (.edge M i mi iex n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e ∈ c.toCallee → a ∈ (bindX f e).facts →
      DRX (.added c.callee a.af.fact (a.af.fact.kind.isAny && !a.af.demand) a.ex)
  | initR {m a am aex d j mj jex} :
      DRX (.added m a am aex) → demand m d → emitTX emit d.din a am aex = some (j, mj, jex) →
      DRX (.init m j mj jex)
  | ret {M i mi iex n f n' c e1 a j mj jex g d g' r e2 r'} :
      DRX (.edge M i mi iex n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (bindX f e1).facts →
      DRX (.init c.callee j mj jex) →
      DRX (.edge c.callee j mj jex (P.exit c.callee) g) →
      demand c.callee d → restrict j jex g d = some g' →
      sat j jex a.af.fact a.ex = true →
      r ∈ (applySummaryX a j jex g').facts →
      e2 ∈ c.fromCallee → r' ∈ (bindX r e2).facts →
      DRX (.edge M i mi iex n' (limitFX counted L r'))
  | retRec {M i mi iex n f n' c e1 a j mj jex g r e2 r'} :
      DRX (.edge M i mi iex n f) → (M, n, Instr.call c, n') ∈ P.edges →
      e1 ∈ c.toCallee → a ∈ (bindX f e1).facts →
      recs c.callee (j, mj, jex, g) →
      (sat j jex a.af.fact a.ex = true ∨ applicable j a.af.fact = true) →
      r ∈ (applySummaryX a j jex g).facts →
      e2 ∈ c.fromCallee → r' ∈ (bindX r e2).facts →
      DRX (.edge M i mi iex n' (limitFX counted L (recLayerX mj (sat j jex a.af.fact a.ex) r')))
  | reqSink {M i mi iex n f s t} :
      DRX (.edge M i mi iex n f) → (M, n, s) ∈ sinks → checkX i f s = .request t →
      DRX (.req M i t)
  | answer {M i t a am aex} :
      DRX (.req M i t) → DRX (.added M a am aex) → a.mark = .conc t →
      overlapX a aex i Excl.empty = true → DRX (.init M (answerInit i a t) false Excl.empty)
  | reqUp {m j t M ic mc icx n f n' c e a} :
      DRX (.req m j t) → DRX (.edge M ic mc icx n f) → (M, n, Instr.call c, n') ∈ P.edges →
      c.callee = m → e ∈ c.toCallee → a ∈ (bindX f e).facts →
      climbsB a.af.fact.mark t = true → overlapX a.af.fact a.ex j Excl.empty = true →
      DRX (.req M ic t)
  | vuln {M i mi iex n f s} :
      DRX (.edge M i mi iex n f) → (M, n, s) ∈ sinks → checkX i f s = .triggered →
      DRX (.vuln M n s f.af.demand)
  | clean {M i mi iex n f n' cl f'} :
      DRX (.edge M i mi iex n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      f' ∈ (cleanResX cl f).facts → DRX (.edge M i mi iex n' f')
  | reqClean {M i mi iex n f n' cl t} :
      DRX (.edge M i mi iex n f) → (M, n, Instr.clean cl, n') ∈ P.edges →
      t ∈ (cleanResX cl f).reqs → DRX (.req M i t)
  | filt {M i mi iex n f n' b may} :
      DRX (.edge M i mi iex n f) → (M, n, Instr.filt b may, n') ∈ P.edges →
      (f.af.fact.base = b → may f.af.fact.path = true) → DRX (.edge M i mi iex n' f)

end ClosureRX

/-- The spec instance of the restricted run with the exclusion: `emitX`, `satX`, `restrictX`. -/
abbrev DRXs (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
    (demand : MethodId → DemandEdge → Prop) (recs : MethodId → PFact × Bool × Excl × XFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : XObj → Prop :=
  DRX P taint counted L demand emitX satX restrictX recs sinks roots

/-! ## 5. The relation to the base model

  The refined runs are a REFINEMENT of the base runs `AnyTaint.D6T` and `AnyTaint.DRT`: every refined
  object has a base object (the statements `Sim6X`, `SimRX`). The relation of one refined object to
  its base object:
  * THE SAME BASE FACT (`Refines6`, `RefinesR`): the same object when the exclusions are forgotten
    and the layers are ignored. The refined location set then lies inside the base one (an exclusion
    only removes locations, `denX_den`).
  * THE LAYER: a refined DEMAND edge is a base demand edge (`x.af.demand = true → f.demand = true`).
    Where the refined edge is normal and the base edge is demand, the base demoted ONLY because of an
    exclusion (the `keep` rows of `annX` and the `partX` rows; the operation lemmas
    `applyEdgeX_base`, `applySummaryX_base`, `transferX_base` give the per-operation form). So an
    annotated edge (`ex ≠ {}`) is a base demand edge, and so is every edge of a premise that carries an
    exclusion or that is a refined must-premise but a base non-must premise (its base start is the
    demand `startFact` of an `.any` premise).
  * THE MUST FLAGS (restricted run): a base must-premise is a refined must-premise; a refined
    must-premise can be a base non-must premise (its added fact was demand in the base only because of
    an exclusion); a premise with an exclusion is a base non-must premise.
  The same base fact does NOT hold for the `below` cleaner one accessor below an `[any-taint]/E` fact:
  its result `(b, P.f, $, T)` is not a base fact (`Vec.below_new_fact`). For a program without a
  `below` cleaner (`NoBelowCleaner`) the statements `Sim6X`, `SimRX` are the expected theorems; in
  general the relation is the location inclusion `Inside6`, `InsideR` (`Sim6XIn`, `SimRXIn`). -/

/-- Forget the exclusions (run 1): the object of `D6T`. -/
def XObj6.forget : XObj6 → Obj
  | .init M i     => .init M i
  | .edge M i n f => .edge M i n f.af
  | .added M a    => .added M a
  | .req M i t    => .req M i t
  | .vuln M n s d => .vuln M n s d

/-- Forget the exclusions (restricted run): the object of `DRT`. -/
def XObj.forget : XObj → TObj
  | .init M j mj _     => .init M j mj
  | .edge M j mj _ n f => .edge M j mj n f.af
  | .added M a am _    => .added M a am
  | .req M j t         => .req M j t
  | .vuln M n s d      => .vuln M n s d

/-- THE REFINEMENT RELATION OF RUN 1 (the same base fact): the refined object and the base `D6T`
    object are the same up to the exclusion and the layer; a refined demand edge is a base demand
    edge; an annotated edge is a base demand edge; a refined demand vulnerability is a base demand
    vulnerability. -/
def Refines6 : XObj6 → Obj → Prop
  | .init M i,     .init M' i'       => M = M' ∧ i = i'
  | .edge M i n x, .edge M' i' n' f  => M = M' ∧ i = i' ∧ n = n' ∧ x.af.fact = f.fact ∧
      (x.af.demand = true → f.demand = true) ∧ (x.ex.isEmptyB = false → f.demand = true)
  | .added M a,    .added M' a'      => M = M' ∧ a = a'
  | .req M i t,    .req M' i' t'     => M = M' ∧ i = i' ∧ t = t'
  | .vuln M n s d, .vuln M' n' s' d' => M = M' ∧ n = n' ∧ s = s' ∧ (d = true → d' = true)
  | _,             _                 => False

/-- THE REFINEMENT RELATION OF THE RESTRICTED RUN (the same base fact): as `Refines6`, with the must
    flags and the premise exclusions: a base must flag is a refined must flag; a premise or an added
    fact with an exclusion is not must in the base; an edge whose premise carries an exclusion, or
    that is must only in the refined run, is a base demand edge. -/
def RefinesR : XObj → TObj → Prop
  | .init M j mj jex, .init M' j' mj' => M = M' ∧ j = j' ∧ (mj' = true → mj = true) ∧
      (jex.isEmptyB = false → mj' = false)
  | .edge M j mj jex n x, .edge M' j' mj' n' f => M = M' ∧ j = j' ∧ n = n' ∧ x.af.fact = f.fact ∧
      (mj' = true → mj = true) ∧ (jex.isEmptyB = false → mj' = false) ∧
      (x.af.demand = true → f.demand = true) ∧
      ((x.ex.isEmptyB = false ∨ jex.isEmptyB = false ∨ (mj = true ∧ mj' = false)) → f.demand = true)
  | .added M a am aex, .added M' a' am' => M = M' ∧ a = a' ∧ (am' = true → am = true) ∧
      (aex.isEmptyB = false → am' = false)
  | .req M j t, .req M' j' t' => M = M' ∧ j = j' ∧ t = t'
  | .vuln M n s d, .vuln M' n' s' d' => M = M' ∧ n = n' ∧ s = s' ∧ (d = true → d' = true)
  | _, _ => False

/-- The refined premise `(j, jex)` lies inside the base premise `j'` (as location sets, with marks). -/
def PremIn (j : PFact) (jex : Excl) (j' : PFact) : Prop := ∀ l, coversX j jex l → j'.covers l

/-- THE LOCATION-INCLUSION RELATION OF RUN 1 (the general form, for programs with a `below`
    cleaner): the refined premise lies inside the base premise, the refined pairs inside the base
    pairs, the layers as `Refines6`. -/
def Inside6 : XObj6 → Obj → Prop
  | .init M i,     .init M' i'       => M = M' ∧ PremIn i Excl.empty i'
  | .edge M i n x, .edge M' i' n' f  => M = M' ∧ n = n' ∧ PremIn i Excl.empty i' ∧
      (∀ l0 l, denX i Excl.empty x.af.fact x.ex l0 l → den i' f.fact l0 l) ∧
      (x.af.demand = true → f.demand = true) ∧ (x.ex.isEmptyB = false → f.demand = true)
  | .added M a,    .added M' a'      => M = M' ∧ PremIn a Excl.empty a'
  | .req M i t,    .req M' i' t'     => M = M' ∧ t = t' ∧ PremIn i Excl.empty i'
  | .vuln M n s d, .vuln M' n' s' d' => M = M' ∧ n = n' ∧ s = s' ∧ (d = true → d' = true)
  | _,             _                 => False

/-- THE LOCATION-INCLUSION RELATION OF THE RESTRICTED RUN: as `Inside6`, with the must flags and the
    premise exclusions of `RefinesR`. -/
def InsideR : XObj → TObj → Prop
  | .init M j mj jex, .init M' j' mj' => M = M' ∧ PremIn j jex j' ∧ (mj' = true → mj = true) ∧
      (jex.isEmptyB = false → mj' = false)
  | .edge M j mj jex n x, .edge M' j' mj' n' f => M = M' ∧ n = n' ∧ PremIn j jex j' ∧
      (∀ l0 l, denX j jex x.af.fact x.ex l0 l → den j' f.fact l0 l) ∧
      (mj' = true → mj = true) ∧ (jex.isEmptyB = false → mj' = false) ∧
      (x.af.demand = true → f.demand = true) ∧
      ((x.ex.isEmptyB = false ∨ jex.isEmptyB = false ∨ (mj = true ∧ mj' = false)) → f.demand = true)
  | .added M a am aex, .added M' a' am' => M = M' ∧ PremIn a aex a' ∧ (am' = true → am = true) ∧
      (aex.isEmptyB = false → am' = false)
  | .req M j t, .req M' j' t' => M = M' ∧ t = t' ∧ PremIn j Excl.empty j'
  | .vuln M n s d, .vuln M' n' s' d' => M = M' ∧ n = n' ∧ s = s' ∧ (d = true → d' = true)
  | _, _ => False

/-- The refined records refine the base records: each refined record `(j, mj, jex, g)` has a base
    record of the same premise in the relation `RefinesR` (as an exit edge). -/
def RecsRefine (P : Program) (recsX : MethodId → PFact × Bool × Excl × XFact → Prop)
    (recs : MethodId → PFact × Bool × AFact → Prop) : Prop :=
  ∀ m j mj jex g, recsX m (j, mj, jex, g) →
    ∃ mj' g', recs m (j, mj', g') ∧
      RefinesR (.edge m j mj jex (P.exit m) g) (.edge m j mj' (P.exit m) g')

/-- The location-inclusion form of `RecsRefine`. -/
def RecsInside (P : Program) (recsX : MethodId → PFact × Bool × Excl × XFact → Prop)
    (recs : MethodId → PFact × Bool × AFact → Prop) : Prop :=
  ∀ m j mj jex g, recsX m (j, mj, jex, g) →
    ∃ j' mj' g', recs m (j', mj', g') ∧
      InsideR (.edge m j mj jex (P.exit m) g) (.edge m j' mj' (P.exit m) g')

/-- The program has no `below` cleaner (the one rule whose result is not a base fact, `partX`). -/
def NoBelowCleaner (P : Program) : Prop :=
  ∀ M n cl n', (M, n, Instr.clean cl, n') ∈ P.edges → cl.reach ≠ .below

/-- THE SIMULATION OF RUN 1 (the statement; the proof file proves it): every object of `D6X` has a
    `D6T` object with the same base fact (`Refines6`). Expected hypothesis: `NoBelowCleaner P`. -/
def Sim6X (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
    (α : MethodId → PFact → PFact) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : Prop :=
  ∀ o, D6X P taint counted L α sinks roots o →
    ∃ o', D6T P taint counted L α sinks roots o' ∧ Refines6 o o'

/-- THE SIMULATION OF RUN 1, the general form: every object of `D6X` has a `D6T` object that
    contains it (`Inside6`). -/
def Sim6XIn (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
    (α : MethodId → PFact → PFact) (sinks : List (MethodId × Node × PFact))
    (roots : List MethodId) : Prop :=
  ∀ o, D6X P taint counted L α sinks roots o →
    ∃ o', D6T P taint counted L α sinks roots o' ∧ Inside6 o o'

/-- THE SIMULATION OF THE RESTRICTED RUN (the statement): every object of the spec instance `DRXs`
    has an object of the spec instance of `DRT` (`emitM`, `satI`, `restrictU`) with the same base fact
    (`RefinesR`). Expected hypotheses: `NoBelowCleaner P`, `RecsRefine P recsX recs`. -/
def SimRX (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
    (demand : MethodId → DemandEdge → Prop)
    (recsX : MethodId → PFact × Bool × Excl × XFact → Prop)
    (recs : MethodId → PFact × Bool × AFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Prop :=
  ∀ o, DRXs P taint counted L demand recsX sinks roots o →
    ∃ o', DRT P taint counted L demand emitM satI restrictU recs sinks roots o' ∧ RefinesR o o'

/-- THE SIMULATION OF THE RESTRICTED RUN, the general form (`InsideR`; expected hypothesis
    `RecsInside P recsX recs`). -/
def SimRXIn (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
    (demand : MethodId → DemandEdge → Prop)
    (recsX : MethodId → PFact × Bool × Excl × XFact → Prop)
    (recs : MethodId → PFact × Bool × AFact → Prop)
    (sinks : List (MethodId × Node × PFact)) (roots : List MethodId) : Prop :=
  ∀ o, DRXs P taint counted L demand recsX sinks roots o →
    ∃ o', DRT P taint counted L demand emitM satI restrictU recs sinks roots o' ∧ InsideR o o'

/-! ## 6. The predicates of the exactness and confirmation files -/

/-- THE EXACTNESS MOTIVE OF `D6X` (`Exact.EdgeOK` with DESIGN A2): an abstract premise mark gives an
    abstract final mark, and a normal edge is PAIR-EXACT on the ADMITTED locations: every pair of
    `denX` (the conclusion exclusion read) to a valid end location is a real flow from a valid start
    location. -/
def EdgeOK6X (P : Program) (ok : Loc → Prop) : XObj6 → Prop
  | .edge M i n f => (Exact.absB i.mark = true → Exact.absB f.af.fact.mark = true) ∧
      (f.af.demand = false → ∀ l0 l, denX i Excl.empty f.af.fact f.ex l0 l → ok l →
        Flow P M l0 n l ∧ ok l0)
  | _ => True

/-- END-EXACT on the ADMITTED locations (`AnyTaint.EndExact` with DESIGN A2): every valid admitted
    location of the conclusion `(f, fex)` at the node `n` gets the value of SOME valid admitted location
    of the premise `(i, iex)`. -/
def EndExactX (P : Program) (ok : Loc → Prop) (M : MethodId) (i : PFact) (iex : Excl) (n : Node)
    (f : PFact) (fex : Excl) : Prop :=
  ∀ l, coversFX f fex l → ok l → ∃ l0, coversX i iex l0 ∧ Flow P M l0 n l ∧ ok l0

/-- THE EXACTNESS MOTIVE OF `DRX` (`AnyTaint.EdgeOKT` with DESIGN A2), for a normal edge: a non-must
    premise: PAIR-EXACT on the admitted locations (`denX` with both exclusions); a must-premise:
    END-EXACT on the admitted locations (`EndExactX`). `True` for the other objects. -/
def EdgeOKX (P : Program) (ok : Loc → Prop) : XObj → Prop
  | .edge M i false iex n f => f.af.demand = false →
      (Exact.absB i.mark = true → Exact.absB f.af.fact.mark = true) ∧
      ∀ l0 l, denX i iex f.af.fact f.ex l0 l → ok l → Flow P M l0 n l ∧ ok l0
  | .edge M i true iex n f => f.af.demand = false →
      (Exact.absB i.mark = true → Exact.absB f.af.fact.mark = true) ∧
      EndExactX P ok M i iex n f.af.fact f.ex
  | _ => True

/-- The annotated records are exact (`AnyTaint.RecsExactT` with DESIGN A2). -/
def RecsExactX (P : Program) (ok : Loc → Prop)
    (recs : MethodId → PFact × Bool × Excl × XFact → Prop) : Prop :=
  ∀ m j mj jex g, recs m (j, mj, jex, g) → EdgeOKX P ok (.edge m j mj jex (P.exit m) g)

/-- The satisfaction reads the premise as INSIDE the added fact, exclusions included
    (`AnyTaint.SatInside` with DESIGN A2). `satX` has it (`satX_inside`). -/
def SatInsideX (sat : PFact → Excl → PFact → Excl → Bool) : Prop :=
  ∀ j jex a aex, sat j jex a aex = true →
    (∀ l, coversX j jex l → coversX ⟨a.base, a.path, a.kind, .star⟩ aex l) ∧
    markSubB j.mark a.mark = true

/-- The emission contract for concrete added facts with exclusions (`EmitContractConc` with
    DESIGN A2): a demanded location that the admitted part of the added fact carries is covered by an
    emitted premise (with its exclusion) that the added fact satisfies. -/
def EmitContractX (emit : PFact → PFact → Excl → Option (PFact × Excl))
    (sat : PFact → Excl → PFact → Excl → Bool) : Prop :=
  ∀ d a aex l t, a.mark = .conc t → d.covers l → coversX a aex l →
    ∃ j jex, emit d a aex = some (j, jex) ∧ coversX j jex l ∧ sat j jex a aex = true

/-- The emission copies the mark of the added fact (`EmitCopiesMark` with DESIGN A2). -/
def EmitCopiesMarkX (emit : PFact → PFact → Excl → Option (PFact × Excl)) : Prop :=
  ∀ d a aex j jex, emit d a aex = some (j, jex) → j.mark = a.mark

/-- The restriction contract with exclusions (`RestrictContract` with DESIGN A2). -/
def RestrictContractX (restrict : PFact → Excl → XFact → DemandEdge → Option XFact) : Prop :=
  ∀ j jex g d p l1 l2, denX j jex g.af.fact g.ex l1 l2 → d.din.coversLoc l1 → d.dout = some p →
    p.coversLoc l2 →
    ∃ g', restrict j jex g d = some g' ∧ denX j jex g'.af.fact g'.ex l1 l2 ∧
      g'.af.demand = g.af.demand

/-- The restriction only removes pairs and keeps the layer (`RestrictSub` with DESIGN A2). -/
def RestrictSubX (restrict : PFact → Excl → XFact → DemandEdge → Option XFact) : Prop :=
  ∀ j jex g d g', restrict j jex g d = some g' →
    g'.af.demand = g.af.demand ∧
    ∀ l1 l2, denX j jex g'.af.fact g'.ex l1 l2 → denX j jex g.af.fact g.ex l1 l2

section Support6X
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (α : MethodId → PFact → PFact)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The normal-layer SUPPORT of the premises of `D6X` (`AnyTaint.Sup6T` with `D6X`). -/
inductive Sup6X : MethodId → PFact → Prop where
  | root {M} : M ∈ roots → Sup6X M zeroFact
  | call {M i n f n' c e a j} :
      Sup6X M i → D6X P taint counted L α sinks roots (.edge M i n f) → f.af.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (bindX f e).facts → a.af.demand = false →
      D6X P taint counted L α sinks roots (.init c.callee j) →
      ((j = zeroFact ∧ a.af.fact = zeroFact) ∨
       (∃ k t, D6X P taint counted L α sinks roots (.req c.callee k t) ∧
          a.af.fact.kind = .exact ∧ a.af.fact.mark = .conc t ∧ j = answerInit k a.af.fact t ∧
          j = a.af.fact)) →
      Sup6X c.callee j

/-- A CONFIRMED vulnerability of `D6X` (`AnyTaint.ConfirmedT6` with DESIGN A2): a normal sink edge
    under a supported premise, with a triggered `checkX`. -/
def Confirmed6X (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i f, D6X P taint counted L α sinks roots (.edge M i n f) ∧
    Sup6X P taint counted L α sinks roots M i ∧
    f.af.demand = false ∧ (M, n, s) ∈ sinks ∧ checkX i f s = .triggered

end Support6X

/-- The link condition of the support with exclusions (`AnyTaint.SupLink` with DESIGN A2): the
    normal added fact `(a, aex)` gives the callee premise `(j, mj, jex)` if both are the zero fact; or
    `a` is exact concrete, `j = a`, not must; or `a` is `[any-taint]/aex`, `j` has the mark of `a` and
    lies inside `a` with the exclusions (`satX`), and `j` is exact and not must, or `.any` and must. -/
def SupLinkX (a : PFact) (aex : Excl) (j : PFact) (mj : Bool) (jex : Excl) : Prop :=
  (j = zeroFact ∧ a = zeroFact) ∨
  (a.kind = .exact ∧ (∃ t, a.mark = .conc t) ∧ j = a ∧ mj = false) ∨
  (a.kind = .any ∧ (∃ t, a.mark = .conc t) ∧ j.mark = a.mark ∧ satX j jex a aex = true ∧
    ((j.kind = .exact ∧ mj = false) ∨ (j.kind = .any ∧ mj = true)))

section SupportX
variable (P : Program) (taint : TaintEdges) (counted : Acc → Bool) (L : Nat)
  (demand : MethodId → DemandEdge → Prop)
  (emit : PFact → PFact → Excl → Option (PFact × Excl))
  (sat : PFact → Excl → PFact → Excl → Bool)
  (restrict : PFact → Excl → XFact → DemandEdge → Option XFact)
  (recs : MethodId → PFact × Bool × Excl × XFact → Prop)
  (sinks : List (MethodId × Node × PFact))
  (roots : List MethodId)

/-- The normal-layer SUPPORT of the premises of `DRX` (`AnyTaint.SupT` with DESIGN A2): the zero fact
    at a root; in a callee, a premise that a normal binding of a normal caller edge with a supported
    premise gives (`SupLinkX`). A supported must-premise `[any-taint]/jex` lies inside an
    `[any-taint]/aex` added fact, so every admitted location of it is real. -/
inductive SupX : MethodId → PFact → Bool → Excl → Prop where
  | root {M} : M ∈ roots → SupX M zeroFact false Excl.empty
  | call {M i mi iex n f n' c e a j mj jex} :
      SupX M i mi iex →
      DRX P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi iex n f) →
      f.af.demand = false →
      (M, n, Instr.call c, n') ∈ P.edges → e ∈ c.toCallee →
      a ∈ (bindX f e).facts → a.af.demand = false →
      DRX P taint counted L demand emit sat restrict recs sinks roots (.init c.callee j mj jex) →
      SupLinkX a.af.fact a.ex j mj jex →
      SupX c.callee j mj jex

/-- A CONFIRMED vulnerability of `DRX` (`AnyTaint.ConfirmedT` with DESIGN A2): a NORMAL sink edge
    (it can be `[any-taint]/E`) under a supported premise, with a triggered `checkX` (the sink pattern
    meets the ADMITTED location set). -/
def ConfirmedX (M : MethodId) (n : Node) (s : PFact) : Prop :=
  ∃ i mi iex f,
    DRX P taint counted L demand emit sat restrict recs sinks roots (.edge M i mi iex n f) ∧
    SupX P taint counted L demand emit sat restrict recs sinks roots M i mi iex ∧
    f.af.demand = false ∧ (M, n, s) ∈ sinks ∧ checkX i f s = .triggered

end SupportX

/-! ## 7. Small lemmas -/

/-- The empty exclusion admits every continuation. -/
theorem admits_empty (σ : List Acc) : Excl.empty.admits σ = true := by
  cases σ <;> rfl

#print axioms admits_empty

theorem isEmptyB_empty : Excl.empty.isEmptyB = true := rfl

#print axioms isEmptyB_empty

/-- `normX` keeps the base fact and the layer (DESIGN A2: the annotation only). -/
theorem normX_af (x : XFact) : (normX x).af = x.af := by
  unfold normX
  cases carriesB x.af <;> rfl

#print axioms normX_af

/-- `normX` keeps the base fact. -/
theorem normX_fact (x : XFact) : (normX x).af.fact = x.af.fact := by rw [normX_af]

#print axioms normX_fact

/-- An `[any-taint]` fact keeps its exclusion. -/
theorem normX_of_carries {x : XFact} (h : carriesB x.af = true) : normX x = x := by
  unfold normX; rw [h]; rfl

#print axioms normX_of_carries

/-- Every other fact drops its exclusion. -/
theorem normX_of_not {x : XFact} (h : carriesB x.af = false) : normX x = ⟨x.af, Excl.empty⟩ := by
  unfold normX; rw [h]; rfl

#print axioms normX_of_not

/-- A demand fact cannot carry an exclusion. -/
theorem carriesB_demand {f : AFact} (h : f.demand = true) : carriesB f = false := by
  unfold carriesB; rw [h]; cases f.fact.kind.isAny <;> rfl

#print axioms carriesB_demand

/-- A DEMAND result has no exclusion (DESIGN A2: "a demand-layer `[any]` has NO exclusion"). -/
theorem normX_demand_ex {x : XFact} (h : x.af.demand = true) : (normX x).ex = Excl.empty := by
  rw [normX_of_not (carriesB_demand h)]

#print axioms normX_demand_ex

/-- `normX` gives a well-formed annotated fact. -/
theorem normX_wf (x : XFact) : WFX (normX x) := by
  intro h
  rw [normX_af] at h
  rw [normX_of_not h]

#print axioms normX_wf

/-- A well-formed annotated fact is in normal form. -/
theorem normX_of_wf {x : XFact} (h : WFX x) : normX x = x := by
  cases hc : carriesB x.af with
  | true => exact normX_of_carries hc
  | false =>
    rw [normX_of_not hc]
    obtain ⟨af, ex⟩ := x
    have e : ex = Excl.empty := h hc
    rw [e]

#print axioms normX_of_wf

/-- A fact without exclusion is in normal form. -/
theorem normX_empty (f : AFact) : normX ⟨f, Excl.empty⟩ = ⟨f, Excl.empty⟩ := by
  unfold normX; cases carriesB f <;> rfl

#print axioms normX_empty

/-- A fact without exclusion is well formed. -/
theorem wf_empty (f : AFact) : WFX ⟨f, Excl.empty⟩ := fun _ => rfl

#print axioms wf_empty

/-- A well-formed demand fact has no exclusion. -/
theorem WFX.demand {x : XFact} (hw : WFX x) (h : x.af.demand = true) : x.ex = Excl.empty :=
  hw (carriesB_demand h)

#print axioms WFX.demand

/-- The annotated pair relation lies inside the base pair relation (an exclusion only removes
    pairs). -/
theorem denX_den {i f : PFact} {iex fex : Excl} {l0 l1 : Loc} (h : denX i iex f fex l0 l1) :
    den i f l0 l1 := by
  obtain ⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9, _, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9⟩

#print axioms denX_den

/-- With no exclusion, the annotated pair relation is the base one. -/
theorem den_denX {i f : PFact} {l0 l1 : Loc} (h : den i f l0 l1) :
    denX i Excl.empty f Excl.empty l0 l1 := by
  obtain ⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, σ, τ, h6, h7, h8, h9, admits_empty σ, admits_empty τ⟩

#print axioms den_denX

/-- With no exclusion, the annotated pair relation is the base one. -/
theorem denX_empty_iff {i f : PFact} {l0 l1 : Loc} :
    denX i Excl.empty f Excl.empty l0 l1 ↔ den i f l0 l1 := ⟨denX_den, den_denX⟩

#print axioms denX_empty_iff

/-- The annotated location set lies inside the base location set. -/
theorem coversX_covers {i : PFact} {ex : Excl} {l : Loc} (h : coversX i ex l) : i.covers l := by
  obtain ⟨h1, ⟨σ, h2, h3, _⟩, h4⟩ := h
  exact ⟨h1, ⟨σ, h2, h3⟩, h4⟩

#print axioms coversX_covers

/-- With no exclusion, the annotated location set is the base one. -/
theorem covers_coversX {i : PFact} {l : Loc} (h : i.covers l) : coversX i Excl.empty l := by
  obtain ⟨h1, ⟨σ, h2, h3⟩, h4⟩ := h
  exact ⟨h1, ⟨σ, h2, h3, admits_empty σ⟩, h4⟩

#print axioms covers_coversX

/-- The annotated conclusion location set lies inside `coversF`. -/
theorem coversFX_coversF {f : PFact} {ex : Excl} {l : Loc} (h : coversFX f ex l) : coversF f l := by
  obtain ⟨h1, ⟨τ, h2, h3, _⟩, h4⟩ := h
  exact ⟨h1, ⟨τ, h2, h3⟩, h4⟩

#print axioms coversFX_coversF

/-- With no exclusion, the annotated conclusion location set is `coversF`. -/
theorem coversF_coversFX {f : PFact} {l : Loc} (h : coversF f l) : coversFX f Excl.empty l := by
  obtain ⟨h1, ⟨τ, h2, h3⟩, h4⟩ := h
  exact ⟨h1, ⟨τ, h2, h3, admits_empty τ⟩, h4⟩

#print axioms coversF_coversFX

/-- `satX` implies the base satisfaction `satI`. -/
theorem satX_satI {j a : PFact} {jex aex : Excl} (h : satX j jex a aex = true) : satI j a = true :=
  RExact.bool_and_left h

#print axioms satX_satI

/-- `overlapX` implies the base overlap `overlapB`. -/
theorem overlapX_overlapB {a b : PFact} {aex bex : Excl} (h : overlapX a aex b bex = true) :
    overlapB a b = true :=
  RExact.bool_and_left h

#print axioms overlapX_overlapB

/-- A refined sink check that triggers or requests is the base check. -/
theorem checkX_ne_none {i : PFact} {f : XFact} {s : PFact} {r : Check} (h : checkX i f s = r)
    (hr : r ≠ .none) : check i f.af s = r := by
  unfold checkX at h
  cases ho : overlapX f.af.fact f.ex s Excl.empty with
  | true => rw [ho, if_pos rfl] at h; exact h
  | false => rw [ho, if_neg Bool.false_ne_true] at h; exact absurd h.symm hr

#print axioms checkX_ne_none

/-- A refined trigger is a base trigger. -/
theorem checkX_triggered {i : PFact} {f : XFact} {s : PFact} (h : checkX i f s = .triggered) :
    check i f.af s = .triggered :=
  checkX_ne_none h (fun h' => Check.noConfusion h')

#print axioms checkX_triggered

/-- A refined request is a base request. -/
theorem checkX_request {i : PFact} {f : XFact} {s : PFact} {t : Mark}
    (h : checkX i f s = .request t) : check i f.af s = .request t :=
  checkX_ne_none h (fun h' => Check.noConfusion h')

#print axioms checkX_request

/-- A `keep` row needs an `.any` input with a concrete mark. -/
theorem annX_keep {c : XFact} {fr to : PFact} {fex tex ex : Excl}
    (h : annX c fr fex to tex = some (true, ex)) : keepB c = true := by
  unfold annX at h
  split at h
  · split at h
    · exact congrArg Prod.fst (Option.some.inj h)
    · cases h
    · cases h
  · split at h
    · split at h <;> cases h
    · cases h
  · split at h
    · split at h
      · exact congrArg Prod.fst (Option.some.inj h)
      · cases h
      · cases h
    · cases h
  · cases h

#print axioms annX_keep

/-- `map` with a function that is the identity on the list. -/
theorem map_eq_self {α : Type} {f : α → α} : ∀ (l : List α), (∀ x, x ∈ l → f x = x) → l.map f = l
  | [], _ => rfl
  | x :: xs, h => by
    show f x :: xs.map f = x :: xs
    rw [h x (List.mem_cons_self ..), map_eq_self xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

#print axioms map_eq_self

/-- THE PER-OPERATION REFINEMENT of the core operation. -/
theorem applyEdgeX_base {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (h : x ∈ (applyEdgeX c fr fex to tex).facts) :
    ∃ y, y ∈ (applyEdge c.af fr to).facts ∧ x.af.fact = y.fact ∧
      (x.af.demand = y.demand ∨
        (x.af.demand = false ∧ c.af.demand = false ∧ keepB c = true ∧
          ∃ ex, annX c fr fex to tex = some (true, ex))) := by
  unfold applyEdgeX at h
  cases ha : annX c fr fex to tex with
  | none => rw [ha] at h; exact absurd h List.not_mem_nil
  | some p =>
    obtain ⟨keep, ex⟩ := p
    rw [ha] at h
    obtain ⟨y, hy, hx⟩ := List.mem_map.mp h
    subst hx
    refine ⟨y, hy, ?_, ?_⟩
    · rw [normX_af]; unfold layerX; cases keep && !c.af.demand <;> rfl
    · rw [normX_af]
      cases keep with
      | false => exact Or.inl rfl
      | true =>
        cases hd : c.af.demand with
        | true =>
          left; rfl
        | false =>
          right
          exact ⟨rfl, rfl, annX_keep ha, ex, rfl⟩

#print axioms applyEdgeX_base

/-- The requests of the refined core operation are base requests. -/
theorem applyEdgeX_reqs {c : XFact} {fr to : PFact} {fex tex : Excl} {t : Mark}
    (h : t ∈ (applyEdgeX c fr fex to tex).reqs) : t ∈ (applyEdge c.af fr to).reqs := by
  unfold applyEdgeX at h
  cases ha : annX c fr fex to tex with
  | none => rw [ha] at h; exact absurd h List.not_mem_nil
  | some p => obtain ⟨keep, ex⟩ := p; rw [ha] at h; exact h

#print axioms applyEdgeX_reqs

/-- Every result of the refined core operation is well formed. -/
theorem applyEdgeX_wf {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (h : x ∈ (applyEdgeX c fr fex to tex).facts) : WFX x := by
  unfold applyEdgeX at h
  cases ha : annX c fr fex to tex with
  | none => rw [ha] at h; exact absurd h List.not_mem_nil
  | some p =>
    obtain ⟨keep, ex⟩ := p
    rw [ha] at h
    obtain ⟨y, _, hx⟩ := List.mem_map.mp h
    rw [← hx]
    exact normX_wf _

#print axioms applyEdgeX_wf

/-- A demand result of the core operation has no exclusion (DESIGN A2). -/
theorem applyEdgeX_demand_ex {c x : XFact} {fr to : PFact} {fex tex : Excl}
    (h : x ∈ (applyEdgeX c fr fex to tex).facts) (hd : x.af.demand = true) : x.ex = Excl.empty :=
  (applyEdgeX_wf h).demand hd

#print axioms applyEdgeX_demand_ex

/-- An input without exclusion and an edge without premise exclusion: the exclusions remove no
    location. -/
theorem annX_plain {c : XFact} (hc : c.ex = Excl.empty) (fr to : PFact) (tex : Excl) :
    ∃ keep ex, annX c fr Excl.empty to tex = some (keep, ex) ∧ (keep = true → keepB c = true) := by
  unfold annX
  split
  · split
    · exact ⟨_, _, rfl, fun h => h⟩
    · exact ⟨_, _, rfl, fun h => Bool.noConfusion h⟩
    · exact ⟨_, _, rfl, fun h => Bool.noConfusion h⟩
  · rw [if_pos (admits_empty _)]
    split
    · exact ⟨_, _, rfl, fun h => Bool.noConfusion h⟩
    · exact ⟨_, _, rfl, fun h => Bool.noConfusion h⟩
    · exact ⟨_, _, rfl, fun h => Bool.noConfusion h⟩
  · rw [hc, if_pos (admits_empty _)]
    split
    · exact ⟨_, _, rfl, fun h => h⟩
    · exact ⟨_, _, rfl, fun h => Bool.noConfusion h⟩
    · exact ⟨_, _, rfl, fun h => Bool.noConfusion h⟩
  · exact ⟨_, _, rfl, fun h => Bool.noConfusion h⟩

#print axioms annX_plain

/-- "Inputs without annotation: exactly the base": an input that cannot carry an exclusion (not a
    normal `[any-taint]`), with no exclusion, and an edge without annotation (a micro edge) gives
    exactly the base results and requests. -/
theorem applyEdgeX_plain {c : XFact} (hc : c.ex = Excl.empty) (hcar : carriesB c.af = false)
    (fr to : PFact) :
    (applyEdgeX c fr Excl.empty to Excl.empty).facts.map XFact.af = (applyEdge c.af fr to).facts ∧
    (applyEdgeX c fr Excl.empty to Excl.empty).reqs = (applyEdge c.af fr to).reqs := by
  obtain ⟨keep, ex, ha, hk⟩ := annX_plain hc fr to Excl.empty
  unfold applyEdgeX
  rw [ha]
  refine ⟨?_, rfl⟩
  show List.map XFact.af (List.map _ _) = _
  rw [List.map_map]
  apply map_eq_self
  intro y _
  show (normX ⟨layerX keep c.af.demand y, ex⟩).af = y
  rw [normX_af]
  unfold layerX
  cases keep with
  | false => rfl
  | true =>
    have hkb := hk rfl
    have hd : c.af.demand = true := by
      unfold keepB at hkb
      unfold carriesB at hcar
      cases h1 : c.af.fact.kind.isAny <;> cases h2 : concB c.af.fact.mark <;> cases h3 : c.af.demand <;>
        simp_all
    rw [hd]; rfl

#print axioms applyEdgeX_plain

/-- A result of the base operation on an `.any` fact has no `*` tail. -/
theorem applyEdge_any_nonstar {c y : AFact} {fr to : PFact} (hc : c.fact.kind = .any)
    (hy : y ∈ (applyEdge c fr to).facts) : y.fact.kind.isStar = false := by
  obtain ⟨p, k, ap, m, hg, _, hr⟩ := Invariant.applyEdge_shape hy
  rw [hc] at hg
  have hk := Invariant.geo_nonstar rfl hg
  rw [hr, Invariant.norm_id_of_nonstar hk]
  exact hk

#print axioms applyEdge_any_nonstar

/-- A `keep` input has the `.any` tail. -/
theorem keepB_any {c : XFact} (h : keepB c = true) : c.af.fact.kind = .any :=
  isAny_eq (RExact.bool_and_left h)

#print axioms keepB_any

/-- THE PER-OPERATION REFINEMENT of the summary application: every result has the fact of a result
    of the base `applySummary`, and a refined demand result is a base demand result. -/
theorem applySummaryX_base {a g x : XFact} {j : PFact} {jex : Excl}
    (h : x ∈ (applySummaryX a j jex g).facts) :
    ∃ y, y ∈ (applySummary a.af j g.af).facts ∧ x.af.fact = y.fact ∧
      (x.af.demand = true → y.demand = true) := by
  obtain ⟨x0, hx0, hx⟩ := List.mem_map.mp h
  subst hx
  obtain ⟨y0, hy0, hf, hl⟩ := applyEdgeX_base hx0
  refine ⟨AFact.norm ⟨y0.fact, y0.demand || g.af.demand⟩, List.mem_map.mpr ⟨y0, hy0, rfl⟩, ?_, ?_⟩
  · rw [normX_af]
    show (AFact.norm ⟨x0.af.fact, x0.af.demand || g.af.demand⟩).fact = _
    rcases hl with hl | ⟨_, _, hk, _⟩
    · rw [hf, hl]
    · have hns := applyEdge_any_nonstar (keepB_any hk) hy0
      rw [Invariant.norm_id_of_nonstar (x := ⟨x0.af.fact, _⟩) (by rw [hf]; exact hns),
        Invariant.norm_id_of_nonstar (x := ⟨y0.fact, y0.demand || g.af.demand⟩) hns]
      exact hf
  · rw [normX_af]
    show (AFact.norm ⟨x0.af.fact, x0.af.demand || g.af.demand⟩).demand = true →
      (AFact.norm ⟨y0.fact, y0.demand || g.af.demand⟩).demand = true
    intro hd
    rcases hl with hl | ⟨hl0, _, hk, _⟩
    · rw [hf, hl] at hd; exact hd
    · have hns := applyEdge_any_nonstar (keepB_any hk) hy0
      rw [Invariant.norm_id_of_nonstar (x := ⟨x0.af.fact, _⟩) (by rw [hf]; exact hns)] at hd
      have hg : g.af.demand = true := by
        have hd' : (x0.af.demand || g.af.demand) = true := hd
        rw [hl0] at hd'; exact hd'
      apply Invariant.norm_demand
      show (y0.demand || g.af.demand) = true
      rw [hg]; cases y0.demand <;> rfl

#print axioms applySummaryX_base

/-- Every result of the refined summary application is well formed. -/
theorem applySummaryX_wf {a g x : XFact} {j : PFact} {jex : Excl}
    (h : x ∈ (applySummaryX a j jex g).facts) : WFX x := by
  obtain ⟨x0, _, hx⟩ := List.mem_map.mp h
  rw [← hx]; exact normX_wf _

#print axioms applySummaryX_wf

/-- The requests of the refined summary application are base requests. -/
theorem applySummaryX_reqs {a g : XFact} {j : PFact} {jex : Excl} {t : Mark}
    (h : t ∈ (applySummaryX a j jex g).reqs) : t ∈ (applySummary a.af j g.af).reqs :=
  applyEdgeX_reqs (fr := j) (to := g.af.fact) h

#print axioms applySummaryX_reqs

/-- `w6tX` is `w6t` on the base fact. -/
theorem w6tX_af (taint : TaintEdges) (e : MicroEdge) (x : XFact) :
    (w6tX taint e x).af = w6t taint e x.af := by
  unfold w6tX w6t; cases e.2.kind.isAny && !taint e <;> rfl

#print axioms w6tX_af

/-- `w6tX` keeps the well-formedness. -/
theorem w6tX_wf (taint : TaintEdges) (e : MicroEdge) {x : XFact} (h : WFX x) :
    WFX (w6tX taint e x) := by
  unfold w6tX; cases e.2.kind.isAny && !taint e
  · exact h
  · exact wf_empty _

#print axioms w6tX_wf

/-- `limitFX` is `limitF` on the base fact. -/
theorem limitFX_af (counted : Acc → Bool) (L : Nat) (x : XFact) :
    (limitFX counted L x).af = limitF counted L x.af := by
  unfold limitFX limitF; cases cutPath counted L x.af.fact.path <;> rfl

#print axioms limitFX_af

/-- `limitFX` keeps the well-formedness. -/
theorem limitFX_wf (counted : Acc → Bool) (L : Nat) {x : XFact} (h : WFX x) :
    WFX (limitFX counted L x) := by
  unfold limitFX; cases cutPath counted L x.af.fact.path
  · exact h
  · exact wf_empty _

#print axioms limitFX_wf

/-- The field limit of the same fact in a higher layer: the same fact, the layer stays higher. -/
theorem limitF_demand_le {counted : Acc → Bool} {L : Nat} {x y : AFact} (hf : x.fact = y.fact)
    (hl : x.demand = true → y.demand = true) :
    (limitF counted L x).demand = true → (limitF counted L y).demand = true := by
  unfold limitF; rw [hf]
  cases cutPath counted L y.fact.path
  · exact hl
  · exact fun _ => rfl

#print axioms limitF_demand_le

/-- The refinement of one statement micro edge with W6T. -/
theorem applyEdgeXT_base {taint : TaintEdges} {c x : XFact} {e : MicroEdge}
    (h : x ∈ (applyEdgeXT taint c e).facts) :
    ∃ y, y ∈ (applyEdgeT taint c.af e).facts ∧ x.af.fact = y.fact ∧
      (x.af.demand = true → y.demand = true) := by
  obtain ⟨x1, hx1, hx⟩ := List.mem_map.mp h
  subst hx
  obtain ⟨y1, hy1, hf, hl⟩ := applyEdgeX_base hx1
  refine ⟨w6t taint e y1, List.mem_map.mpr ⟨y1, hy1, rfl⟩, ?_, ?_⟩
  · rw [w6tX_af, w6t_fact, w6t_fact]; exact hf
  · rw [w6tX_af]
    unfold w6t
    cases e.2.kind.isAny && !taint e
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
      intro hd
      rcases hl with hl | ⟨hl0, _⟩
      · rw [← hl]; exact hd
      · exact absurd (hl0.symm.trans hd) Bool.false_ne_true
    · intro _; rfl

#print axioms applyEdgeXT_base

/-- Every result of one statement micro edge is well formed. -/
theorem applyEdgeXT_wf {taint : TaintEdges} {c x : XFact} {e : MicroEdge}
    (h : x ∈ (applyEdgeXT taint c e).facts) : WFX x := by
  obtain ⟨x1, hx1, hx⟩ := List.mem_map.mp h
  rw [← hx]; exact w6tX_wf taint e (applyEdgeX_wf hx1)

#print axioms applyEdgeXT_wf

/-- The refinement of all micro edges of a statement. -/
theorem applyAllXT_base {taint : TaintEdges} {c x : XFact} :
    ∀ {es : List MicroEdge}, x ∈ (applyAllXT taint c es).facts →
    ∃ y, y ∈ (applyAllT taint c.af es).facts ∧ x.af.fact = y.fact ∧
      (x.af.demand = true → y.demand = true)
  | [], h => absurd h List.not_mem_nil
  | e :: es, h => by
    have h' : x ∈ (applyEdgeXT taint c e).facts ++ (applyAllXT taint c es).facts := h
    rcases List.mem_append.mp h' with h1 | h2
    · obtain ⟨y, hy, h3⟩ := applyEdgeXT_base h1
      exact ⟨y, List.mem_append_left _ hy, h3⟩
    · obtain ⟨y, hy, h3⟩ := applyAllXT_base h2
      exact ⟨y, List.mem_append_right _ hy, h3⟩

#print axioms applyAllXT_base

/-- Every result of the micro edges of a statement is well formed. -/
theorem applyAllXT_wf {taint : TaintEdges} {c x : XFact} :
    ∀ {es : List MicroEdge}, x ∈ (applyAllXT taint c es).facts → WFX x
  | [], h => absurd h List.not_mem_nil
  | e :: es, h => by
    have h' : x ∈ (applyEdgeXT taint c e).facts ++ (applyAllXT taint c es).facts := h
    rcases List.mem_append.mp h' with h1 | h2
    · exact applyEdgeXT_wf h1
    · exact applyAllXT_wf h2

#print axioms applyAllXT_wf

/-- The requests of the micro edges of a statement are base requests. -/
theorem applyAllXT_reqs {taint : TaintEdges} {c : XFact} {t : Mark} :
    ∀ {es : List MicroEdge}, t ∈ (applyAllXT taint c es).reqs → t ∈ (applyAllT taint c.af es).reqs
  | [], h => absurd h List.not_mem_nil
  | e :: es, h => by
    have h' : t ∈ (bindX c e).reqs ++ (applyAllXT taint c es).reqs := h
    show t ∈ (applyEdge c.af e.1 e.2).reqs ++ (applyAllT taint c.af es).reqs
    rcases List.mem_append.mp h' with h1 | h2
    · exact List.mem_append_left _ (applyEdgeX_reqs h1)
    · exact List.mem_append_right _ (applyAllXT_reqs h2)

#print axioms applyAllXT_reqs

/-- THE PER-OPERATION REFINEMENT of the statement transfer: every result has the fact of a result of
    the base `transferT`, and a refined demand result is a base demand result. -/
theorem transferX_base {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} (h : x ∈ (transferX taint counted L s c).facts) :
    ∃ y, y ∈ (transferT taint counted L s c.af).facts ∧ x.af.fact = y.fact ∧
      (x.af.demand = true → y.demand = true) := by
  unfold transferX at h
  unfold transferT
  cases hm : memB c.af.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at h
    rw [if_neg Bool.false_ne_true]
    have hx : x = c := List.mem_singleton.mp h
    subst hx
    exact ⟨x.af, List.mem_singleton.mpr rfl, rfl, id⟩
  | true =>
    rw [hm, if_pos rfl] at h
    rw [if_pos rfl]
    obtain ⟨x0, hx0, hx⟩ := List.mem_map.mp h
    subst hx
    obtain ⟨y0, hy0, hf, hl⟩ := applyAllXT_base hx0
    refine ⟨limitF counted L y0, List.mem_map.mpr ⟨y0, hy0, rfl⟩, ?_, ?_⟩
    · rw [limitFX_af]; exact limitF_fact_eq hf
    · rw [limitFX_af]; exact limitF_demand_le hf hl

#print axioms transferX_base

/-- The refined statement transfer keeps the well-formedness. -/
theorem transferX_wf {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c x : XFact} (hc : WFX c) (h : x ∈ (transferX taint counted L s c).facts) : WFX x := by
  unfold transferX at h
  cases hm : memB c.af.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at h
    rw [List.mem_singleton.mp h]; exact hc
  | true =>
    rw [hm, if_pos rfl] at h
    obtain ⟨x0, hx0, hx⟩ := List.mem_map.mp h
    rw [← hx]; exact limitFX_wf counted L (applyAllXT_wf hx0)

#print axioms transferX_wf

/-- The requests of the refined transfer are base requests. -/
theorem transferX_reqs {taint : TaintEdges} {counted : Acc → Bool} {L : Nat} {s : Stmt}
    {c : XFact} {t : Mark} (h : t ∈ (transferX taint counted L s c).reqs) :
    t ∈ (transferT taint counted L s c.af).reqs := by
  unfold transferX at h
  unfold transferT
  cases hm : memB c.af.fact.base s.touched with
  | false =>
    rw [hm, if_neg Bool.false_ne_true] at h; exact absurd h List.not_mem_nil
  | true =>
    rw [hm, if_pos rfl] at h; rw [if_pos rfl]; exact applyAllXT_reqs h

#print axioms transferX_reqs

/-- The refinement of a call binding: the fact of a base result, a refined demand result is a base
    demand result. -/
theorem bindX_base {c x : XFact} {e : MicroEdge} (h : x ∈ (bindX c e).facts) :
    ∃ y, y ∈ (applyEdge c.af e.1 e.2).facts ∧ x.af.fact = y.fact ∧
      (x.af.demand = true → y.demand = true) := by
  obtain ⟨y, hy, hf, hl⟩ := applyEdgeX_base h
  refine ⟨y, hy, hf, fun hd => ?_⟩
  rcases hl with hl | ⟨hl0, _⟩
  · rw [← hl]; exact hd
  · exact absurd (hl0.symm.trans hd) Bool.false_ne_true

#print axioms bindX_base

/-- The refined start fact is `AnyTaint.startT` on the base fact. -/
theorem startX_af (j : PFact) (mj : Bool) (jex : Excl) : (startX j mj jex).af = startT j mj := by
  unfold startX
  cases mj
  · rfl
  · exact normX_af _

#print axioms startX_af

/-- The refined start fact is well formed. -/
theorem startX_wf (j : PFact) (mj : Bool) (jex : Excl) : WFX (startX j mj jex) := by
  unfold startX
  cases mj
  · exact wf_empty _
  · exact normX_wf _

#print axioms startX_wf

/-- `recLayerX` is `recLayer` on the base fact. -/
theorem recLayerX_af (mj s : Bool) (x : XFact) : (recLayerX mj s x).af = recLayer mj s x.af := by
  unfold recLayerX recLayer; cases mj && !s <;> rfl

#print axioms recLayerX_af

/-- `recLayerX` keeps the well-formedness. -/
theorem recLayerX_wf (mj s : Bool) {x : XFact} (h : WFX x) : WFX (recLayerX mj s x) := by
  unfold recLayerX; cases mj && !s
  · exact h
  · exact wf_empty _

#print axioms recLayerX_wf

/-- The refined emission gives the premise of the base `emitM`. -/
theorem emitX_base {d a j : PFact} {aex jex : Excl} (h : emitX d a aex = some (j, jex)) :
    emitM d a = some j := by
  unfold emitX at h
  cases he : emitM d a with
  | none => rw [he] at h; cases h
  | some j0 =>
    rw [he] at h
    dsimp only at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h; rfl

#print axioms emitX_base

/-- The refined emission with the must flag gives the premise and the flag of the base `emitT`. -/
theorem emitTX_base {d a j : PFact} {am mj : Bool} {aex jex : Excl}
    (h : emitTX emitX d a am aex = some (j, mj, jex)) : emitT d a am = some (j, mj) := by
  unfold emitTX at h
  cases he : emitX d a aex with
  | none => rw [he] at h; cases h
  | some p =>
    obtain ⟨j0, jex0⟩ := p
    rw [he] at h
    cases h
    unfold emitT
    rw [emitX_base he]
    rfl

#print axioms emitTX_base

/-- The refined emission copies the mark of the added fact. -/
theorem emitX_copies : EmitCopiesMarkX emitX := by
  intro d a aex j jex h
  exact RExact.emitM_copies d a j (emitX_base h)

#print axioms emitX_copies

/-- The refined restriction gives the fact and the layer of the base `restrictU`. -/
theorem restrictX_base {sp : PFact} {spex : Excl} {sc g' : XFact} {d : DemandEdge}
    (h : restrictX sp spex sc d = some g') : restrictU sp sc.af d = some g'.af := by
  unfold restrictX at h
  show restrictWith restrictConcU sp sc.af d = some g'.af
  unfold restrictWith
  cases hd : d.dout with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    dsimp only at h ⊢
    cases ho : overlapX sp spex d.din Excl.empty with
    | false => rw [ho, if_neg Bool.false_ne_true] at h; cases h
    | true =>
      rw [ho, if_pos rfl] at h
      rw [if_pos (overlapX_overlapB ho)]
      unfold restrictConcX at h
      cases hr : restrictConcU sc.af p with
      | none => rw [hr] at h; cases h
      | some g0 =>
        rw [hr] at h
        dsimp only at h
        split at h
        · split at h
          · cases h; rfl
          · cases h
        · cases h; rw [normX_af]

#print axioms restrictX_base

/-- A continuation that a premise tail admits is admitted by its `tailExcl`. -/
theorem tailExcl_admits {k : Kind} {σ : List Acc} (h : tailI k σ) : (tailExcl k).admits σ = true := by
  cases k with
  | star e => exact h
  | any => exact admits_empty σ
  | exact => have h' : σ = [] := h; subst h'; rfl

#print axioms tailExcl_admits

/-- An exclusion reads only the first accessor. -/
theorem admits_cons_append (e : Excl) (x : Acc) (r s : List Acc) :
    e.admits (x :: r ++ s) = e.admits (x :: r) := by cases e <;> rfl

#print axioms admits_cons_append

/-- `satX` reads the premise as inside the added fact, exclusions included. -/
theorem satX_inside : SatInsideX satX := by
  intro j jex a aex h
  have hsat := satX_satI h
  have hex : insideExB j jex a aex = true := RExact.bool_and_right h
  refine ⟨?_, RExact.bool_and_right hsat⟩
  intro l hl
  have hcov := coversB_sound (RExact.bool_and_left hsat) (coversX_covers hl)
  obtain ⟨hb, ⟨σ, hp, ht⟩, hm⟩ := hcov
  refine ⟨hb, ⟨σ, hp, ht, ?_⟩, hm⟩
  obtain ⟨_, ⟨σj, hpj, htj, hej⟩, _⟩ := hl
  unfold insideExB at hex
  cases hrel : relate a.path j.path with
  | below r =>
    rw [hrel] at hex
    have hjp : j.path = a.path ++ r := Exact.relate_below hrel
    have hσ : σ = r ++ σj := by
      have e1 : a.path ++ σ = a.path ++ (r ++ σj) := by
        rw [← hp, hpj, hjp, List.append_assoc]
      exact List.append_cancel_left e1
    cases r with
    | nil =>
      have hσ' : σ = σj := hσ
      rw [hσ']
      apply CoreAux.Excl.subB_sound hex
      rw [CoreAux.Excl.admits_union, tailExcl_admits htj, hej]; rfl
    | cons x r' =>
      rw [hσ, admits_cons_append]; exact hex
  | above r => rw [hrel] at hex; cases hex
  | apart => rw [hrel] at hex; cases hex

#print axioms satX_inside

/-- `cleanPosX` is `cleanPos`, or `disjoint` for a cleaner in the excluded part. -/
theorem cleanPosX_cases (cl : Cleaner) (c : XFact) :
    cleanPosX cl c = cleanPos cl c.af.fact ∨
    (cleanPosX cl c = .disjoint ∧ ∃ r, relate cl.path c.af.fact.path = .above r ∧
      c.ex.admits r = false) := by
  unfold cleanPosX
  cases hr : relate cl.path c.af.fact.path with
  | above r =>
    dsimp only
    cases ha : c.ex.admits r with
    | true => left; rw [if_pos rfl]
    | false => right; exact ⟨if_neg Bool.false_ne_true, r, rfl, ha⟩
  | below r => left; rfl
  | apart => left; rfl

#print axioms cleanPosX_cases

/-- A well-formed fact with a non-empty exclusion is `[any-taint]`. -/
theorem carriesB_of_ex {c : XFact} (hc : WFX c) {r : List Acc} (h : c.ex.admits r = false) :
    carriesB c.af = true := by
  cases hcar : carriesB c.af with
  | true => rfl
  | false => rw [hc hcar, admits_empty] at h; cases h

#print axioms carriesB_of_ex

/-- An `[any-taint]` fact: the `.any` tail, the normal layer, a concrete mark. -/
theorem carriesB_parts {f : AFact} (h : carriesB f = true) :
    f.fact.kind = .any ∧ f.demand = false ∧ ∃ t, f.fact.mark = .conc t := by
  unfold carriesB at h
  cases hk : f.fact.kind with
  | star e => rw [hk] at h; cases h
  | exact => rw [hk] at h; cases h
  | any =>
    rw [hk] at h
    cases hd : f.demand with
    | true => rw [hd] at h; cases h
    | false =>
      rw [hd] at h
      cases hm : f.fact.mark with
      | conc t => exact ⟨rfl, rfl, t, rfl⟩
      | star => rw [hm] at h; cases h
      | starEx xs => rw [hm] at h; cases h

#print axioms carriesB_parts

/-- The cleaner on the excluded part: the base result of an `[any-taint]` fact `c` against a cleaner
    strictly below it at `c.path ++ r` (the base `part` row) has the fact of `c`. -/
theorem cleanRes_above_any {cl : Cleaner} {c : AFact} {r : List Acc}
    (hcar : carriesB c = true) (hr : relate cl.path c.fact.path = .above r) :
    ∃ y, y ∈ (cleanRes cl c).facts ∧ c.fact = y.fact ∧ (c.demand = true → y.demand = true) := by
  obtain ⟨hk, _, t, hm⟩ := carriesB_parts hcar
  unfold cleanRes
  have hpos : cleanPos cl c.fact = .disjoint ∨ cleanPos cl c.fact = .part := by
    unfold cleanPos
    cases Nat.beq c.fact.base cl.base
    · left; rfl
    · rw [if_pos rfl, hr]; dsimp only; rw [hk]; right; rfl
  rcases hpos with hp | hp
  · rw [hp]; exact ⟨c, List.mem_singleton.mpr rfl, rfl, id⟩
  · rw [hp]; dsimp only
    rw [hm]; dsimp only
    cases hb : cl.markB t with
    | false => rw [if_neg Bool.false_ne_true]; exact ⟨c, List.mem_singleton.mpr rfl, rfl, id⟩
    | true =>
      rw [if_pos rfl]
      refine ⟨concPart cl c, List.mem_singleton.mpr rfl, ?_, ?_⟩
      · unfold concPart; rw [hk, hr]; cases cl.reach <;> rfl
      · intro _; unfold concPart; rw [hk, hr]; cases cl.reach <;> rfl

#print axioms cleanRes_above_any

/-- THE PER-OPERATION REFINEMENT of the cleaner: every result has the fact of a result of the base
    `cleanRes` in the same or a higher base layer, EXCEPT the position `(b, P.f, $, T)` that the `below`
    cleaner at `P.f` keeps on an `[any-taint]` fact at `P` (`partX`). -/
theorem cleanResX_base {cl : Cleaner} {c x : XFact} (hc : WFX c)
    (h : x ∈ (cleanResX cl c).facts) :
    (∃ y, y ∈ (cleanRes cl c.af).facts ∧ x.af.fact = y.fact ∧
      (x.af.demand = true → y.demand = true)) ∨
    (cl.reach = .below ∧ carriesB c.af = true ∧ ∃ f, relate cl.path c.af.fact.path = .above [f] ∧
      x = ⟨⟨⟨c.af.fact.base, c.af.fact.path ++ [f], .exact, c.af.fact.mark⟩, c.af.demand⟩,
        Excl.empty⟩) := by
  unfold cleanResX at h
  rcases cleanPosX_cases cl c with hp | ⟨hp, r, hr, ha⟩
  · rw [hp] at h
    unfold cleanRes
    cases hq : cleanPos cl c.af.fact with
    | disjoint =>
      rw [hq] at h
      left; rw [List.mem_singleton.mp h]; exact ⟨c.af, List.mem_singleton.mpr rfl, rfl, id⟩
    | inside =>
      rw [hq] at h
      left
      dsimp only at h ⊢
      revert h
      cases hm : c.af.fact.mark with
      | conc t =>
        intro h
        dsimp only at h ⊢
        cases hb : cl.markB t with
        | true => rw [hb, if_pos rfl] at h; exact absurd h List.not_mem_nil
        | false =>
          rw [hb, if_neg Bool.false_ne_true] at h
          rw [if_neg Bool.false_ne_true, List.mem_singleton.mp h]
          exact ⟨c.af, List.mem_singleton.mpr rfl, rfl, id⟩
      | star =>
        cases hcm : cl.mark with
        | none => intro h; exact absurd h List.not_mem_nil
        | some t =>
          intro h
          rw [List.mem_singleton.mp h]
          exact ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
      | starEx xs =>
        cases hcm : cl.mark with
        | none => intro h; exact absurd h List.not_mem_nil
        | some t =>
          intro h
          rw [List.mem_singleton.mp h]
          exact ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
    | part =>
      rw [hq] at h
      dsimp only at h ⊢
      revert h
      cases hm : c.af.fact.mark with
      | conc t =>
        intro h
        dsimp only at h ⊢
        cases hb : cl.markB t with
        | false =>
          rw [hb, if_neg Bool.false_ne_true] at h
          rw [if_neg Bool.false_ne_true, List.mem_singleton.mp h]
          exact Or.inl ⟨c.af, List.mem_singleton.mpr rfl, rfl, id⟩
        | true =>
          rw [hb, if_pos rfl] at h
          rw [if_pos rfl]
          unfold partX at h
          cases hcar : carriesB c.af with
          | false =>
            rw [hcar, if_neg Bool.false_ne_true] at h
            rw [List.mem_singleton.mp h]
            exact Or.inl ⟨concPart cl c.af, List.mem_singleton.mpr rfl, rfl, id⟩
          | true =>
            rw [hcar, if_pos rfl] at h
            -- the special rows
            have hbase : ∀ r, relate cl.path c.af.fact.path = .above r →
                ∃ y, y ∈ [concPart cl c.af] ∧ c.af.fact = y.fact ∧
                  (c.af.demand = true → y.demand = true) := by
              intro r hr
              obtain ⟨hk, _⟩ := carriesB_parts hcar
              refine ⟨concPart cl c.af, List.mem_singleton.mpr rfl, ?_, fun _ => ?_⟩
              · unfold concPart; rw [hk, hr]; cases cl.reach <;> rfl
              · unfold concPart; rw [hk, hr]; cases cl.reach <;> rfl
            revert h
            cases hrch : cl.reach with
            | atAndBelow =>
              cases hr : relate cl.path c.af.fact.path with
              | above r =>
                cases r with
                | nil => intro h; rw [List.mem_singleton.mp h]; exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
                | cons f r' =>
                  cases r' with
                  | nil =>
                    intro h
                    rw [List.mem_singleton.mp h]
                    exact Or.inl (hbase [f] hr)
                  | cons g r'' =>
                    intro h; rw [List.mem_singleton.mp h]
                    exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
              | below r =>
                intro h; rw [List.mem_singleton.mp h]
                exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
              | apart =>
                intro h; rw [List.mem_singleton.mp h]
                exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
            | below =>
              cases hr : relate cl.path c.af.fact.path with
              | above r =>
                cases r with
                | nil => intro h; rw [List.mem_singleton.mp h]; exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
                | cons f r' =>
                  cases r' with
                  | nil =>
                    intro h
                    rcases List.mem_cons.mp h with h1 | h1
                    · rw [h1]; exact Or.inl (hbase [f] hr)
                    · rw [List.mem_singleton.mp h1]
                      exact Or.inr ⟨rfl, rfl, f, rfl, by rw [hm]⟩
                  | cons g r'' =>
                    intro h; rw [List.mem_singleton.mp h]
                    exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
              | below r =>
                intro h; rw [List.mem_singleton.mp h]
                exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
              | apart =>
                intro h; rw [List.mem_singleton.mp h]
                exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
            | exact =>
              intro h; rw [List.mem_singleton.mp h]
              exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
      | star =>
        cases hcm : cl.mark with
        | none =>
          intro h; rw [List.mem_singleton.mp h]
          exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
        | some t =>
          intro h; rw [List.mem_singleton.mp h]
          exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
      | starEx xs =>
        cases hcm : cl.mark with
        | none =>
          intro h; rw [List.mem_singleton.mp h]
          exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
        | some t =>
          intro h; rw [List.mem_singleton.mp h]
          exact Or.inl ⟨_, List.mem_singleton.mpr rfl, rfl, id⟩
  · rw [hp] at h
    left
    rw [List.mem_singleton.mp h]
    exact cleanRes_above_any (carriesB_of_ex hc ha) hr

#print axioms cleanResX_base

/-- A fact with an abstract mark cannot carry an exclusion. -/
theorem carriesB_of_mark {f : AFact} (h : ∀ t, f.fact.mark = .conc t → False) :
    carriesB f = false := by
  unfold carriesB
  cases hm : f.fact.mark with
  | conc t => exact absurd hm (h t)
  | star => cases f.fact.kind.isAny && !f.demand <;> rfl
  | starEx xs => cases f.fact.kind.isAny && !f.demand <;> rfl

#print axioms carriesB_of_mark

/-- Every result of the refined cleaner on a well-formed fact is well formed. -/
theorem cleanResX_wf {cl : Cleaner} {c x : XFact} (hc : WFX c)
    (h : x ∈ (cleanResX cl c).facts) : WFX x := by
  unfold cleanResX at h
  split at h
  · rw [List.mem_singleton.mp h]; exact hc
  · split at h
    · split at h
      · exact absurd h List.not_mem_nil
      · rw [List.mem_singleton.mp h]; exact hc
    · rw [List.mem_singleton.mp h]
      intro _
      rename_i hne _
      exact hc (carriesB_of_mark hne)
    · exact absurd h List.not_mem_nil
  · split at h
    · split at h
      · unfold partX at h
        split at h
        · rename_i hcar
          split at h
          · rw [List.mem_singleton.mp h]
            intro h'; rw [hcar] at h'; cases h'
          · rcases List.mem_cons.mp h with h1 | h1
            · rw [h1]; intro h'; rw [hcar] at h'; cases h'
            · rw [List.mem_singleton.mp h1]; exact wf_empty _
          · rw [List.mem_singleton.mp h]; exact wf_empty _
        · rw [List.mem_singleton.mp h]; exact wf_empty _
      · rw [List.mem_singleton.mp h]; exact hc
    · rw [List.mem_singleton.mp h]
      intro _
      rename_i hne _
      exact hc (carriesB_of_mark hne)
    · rw [List.mem_singleton.mp h]; exact wf_empty _

#print axioms cleanResX_wf

/-! ### The relations -/

/-- The same base fact gives the location inclusion (run 1): `Refines6` implies `Inside6`. -/
theorem refines6_inside {o : XObj6} {o' : Obj} (h : Refines6 o o') : Inside6 o o' := by
  cases o with
  | init M i =>
    cases o' with
    | init M' i' => obtain ⟨h1, rfl⟩ := h; exact ⟨h1, fun _ hl => coversX_covers hl⟩
    | _ => cases h
  | edge M i n x =>
    cases o' with
    | edge M' i' n' f =>
      obtain ⟨h1, rfl, h3, hf, h5, h6⟩ := h
      refine ⟨h1, h3, fun _ hl => coversX_covers hl, fun l0 l hd => ?_, h5, h6⟩
      rw [← hf]; exact denX_den hd
    | _ => cases h
  | added M a =>
    cases o' with
    | added M' a' => obtain ⟨h1, rfl⟩ := h; exact ⟨h1, fun _ hl => coversX_covers hl⟩
    | _ => cases h
  | req M i t =>
    cases o' with
    | req M' i' t' => obtain ⟨h1, rfl, h3⟩ := h; exact ⟨h1, h3, fun _ hl => coversX_covers hl⟩
    | _ => cases h
  | vuln M n s d =>
    cases o' with
    | vuln M' n' s' d' => exact h
    | _ => cases h

#print axioms refines6_inside

/-- The same base fact gives the location inclusion (restricted run): `RefinesR` implies
    `InsideR`. -/
theorem refinesR_inside {o : XObj} {o' : TObj} (h : RefinesR o o') : InsideR o o' := by
  cases o with
  | init M j mj jex =>
    cases o' with
    | init M' j' mj' =>
      obtain ⟨h1, rfl, h3, h4⟩ := h; exact ⟨h1, fun _ hl => coversX_covers hl, h3, h4⟩
    | _ => cases h
  | edge M j mj jex n x =>
    cases o' with
    | edge M' j' mj' n' f =>
      obtain ⟨h1, rfl, h3, hf, h5, h6, h7, h8⟩ := h
      refine ⟨h1, h3, fun _ hl => coversX_covers hl, fun l0 l hd => ?_, h5, h6, h7, h8⟩
      rw [← hf]; exact denX_den hd
    | _ => cases h
  | added M a am aex =>
    cases o' with
    | added M' a' am' =>
      obtain ⟨h1, rfl, h3, h4⟩ := h; exact ⟨h1, fun _ hl => coversX_covers hl, h3, h4⟩
    | _ => cases h
  | req M j t =>
    cases o' with
    | req M' j' t' => obtain ⟨h1, rfl, h3⟩ := h; exact ⟨h1, h3, fun _ hl => coversX_covers hl⟩
    | _ => cases h
  | vuln M n s d =>
    cases o' with
    | vuln M' n' s' d' => exact h
    | _ => cases h

#print axioms refinesR_inside

theorem sim6X_in {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {α : MethodId → PFact → PFact} {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (h : Sim6X P taint counted L α sinks roots) : Sim6XIn P taint counted L α sinks roots :=
  fun o ho => match h o ho with
    | ⟨o', h1, h2⟩ => ⟨o', h1, refines6_inside h2⟩

#print axioms sim6X_in

theorem simRX_in {P : Program} {taint : TaintEdges} {counted : Acc → Bool} {L : Nat}
    {demand : MethodId → DemandEdge → Prop}
    {recsX : MethodId → PFact × Bool × Excl × XFact → Prop}
    {recs : MethodId → PFact × Bool × AFact → Prop}
    {sinks : List (MethodId × Node × PFact)} {roots : List MethodId}
    (h : SimRX P taint counted L demand recsX recs sinks roots) :
    SimRXIn P taint counted L demand recsX recs sinks roots :=
  fun o ho => match h o ho with
    | ⟨o', h1, h2⟩ => ⟨o', h1, refinesR_inside h2⟩

#print axioms simRX_in

/-! ## 8. Vectors

  Bases: `1` (`this`, `x`), `2` (`y`); accessors: `3` (`name`, `f`), `4` (`g`), `6`, `7`; mark `5`
  (`T`). Every vector is checked by `decide` (or by a term). -/
namespace Vec

/-- `(this, [], [any-taint], {}, T)`, normal. -/
def cIn : XFact := ⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, Excl.empty⟩
/-- `(this, [], [any-taint], {name}, T)`, normal. -/
def cAnn : XFact := ⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, .set [3]⟩
/-- The keep edge of the strong write `this.name = v`: `this.* →_{name} this.*`. -/
def keepEdge : MicroEdge := (⟨1, [], .star (.set []), .star⟩, ⟨1, [], .star (.set [3]), .star⟩)
/-- The write edge of `this.name = v`: `v.* → this.name.*`. -/
def writeEdge : MicroEdge := (⟨2, [], .star (.set []), .star⟩, ⟨1, [3], .star (.set []), .star⟩)
/-- The statement `this.name = v`. -/
def setter : Stmt := ⟨[1], [keepEdge, writeEdge]⟩
def noTaint : TaintEdges := fun _ => false
def cnt : Acc → Bool := fun _ => true

/-! ### THE SETTER VECTOR -/

/-- The keep edge on a normal `[any-taint]` fact gives the NORMAL `[any-taint]/{name}`. -/
theorem setter_keep :
    bindX cIn keepEdge = ⟨[⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, .set [3]⟩], []⟩ := by decide

#print axioms setter_keep

/-- The base gives the demand layer (decision 5, the demotion that A2 replaces). -/
theorem setter_keep_base :
    (applyEdge cIn.af keepEdge.1 keepEdge.2).facts = [⟨⟨1, [], .any, .conc 5⟩, true⟩] := by decide

#print axioms setter_keep_base

/-- The whole statement (W6T and the field limit included): the same. -/
theorem setter_transfer :
    transferX noTaint cnt 3 setter cIn = ⟨[⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, .set [3]⟩], []⟩ := by
  decide

#print axioms setter_transfer

theorem setter_transfer_base :
    (transferT noTaint cnt 3 setter cIn.af).facts = [⟨⟨1, [], .any, .conc 5⟩, true⟩] := by decide

#print axioms setter_transfer_base

/-! ### Reads -/

/-- `y = this.name`. -/
def readName : MicroEdge := (⟨1, [3], .star (.set []), .star⟩, ⟨2, [], .star (.set []), .star⟩)
/-- `y = this.g`. -/
def readG : MicroEdge := (⟨1, [4], .star (.set []), .star⟩, ⟨2, [], .star (.set []), .star⟩)

/-- A read through an EXCLUDED accessor gives nothing (no result, no request). -/
theorem read_excluded : bindX cAnn readName = ResX.none := by decide

#print axioms read_excluded

/-- (The base gives a result: on the base fact the exclusion does not exist.) -/
theorem read_excluded_base :
    (applyEdge cAnn.af readName.1 readName.2).facts = [⟨⟨2, [], .any, .conc 5⟩, false⟩] := by decide

#print axioms read_excluded_base

/-- A read through an ADMITTED accessor gives `[any-taint]` with `ex = {}`, normal. -/
theorem read_admitted :
    bindX cAnn readG = ⟨[⟨⟨⟨2, [], .any, .conc 5⟩, false⟩, Excl.empty⟩], []⟩ := by decide

#print axioms read_admitted

/-! ### The case above with a `*` target and an edge exclusion -/

/-- `this.g.*/{7} →_{6} y.*`: the premise exclusion `{7}` and the target exclusion `{6}`. -/
def readEx : MicroEdge := (⟨1, [4], .star (.set [7]), .star⟩, ⟨2, [], .star (.set [6]), .star⟩)

/-- The case `above` with a `*` target gives the exclusion of the edge (`{7} ∪ {6}`), normal. -/
theorem above_star_excl :
    bindX cIn readEx = ⟨[⟨⟨⟨2, [], .any, .conc 5⟩, false⟩, .set [7, 6]⟩], []⟩ := by decide

#print axioms above_star_excl

theorem above_star_excl_base :
    (applyEdge cIn.af readEx.1 readEx.2).facts = [⟨⟨2, [], .any, .conc 5⟩, true⟩] := by decide

#print axioms above_star_excl_base

/-- A source with an `[any]` target (a taint edge) on an annotated fact: `ex = {}`, normal. -/
def condSrc : MicroEdge := (⟨1, [], .exact, .conc 5⟩, ⟨2, [], .any, .conc 6⟩)
theorem source_any_target :
    applyEdgeXT (fun e => decide (e = condSrc)) cAnn condSrc =
      ⟨[⟨⟨⟨2, [], .any, .conc 6⟩, false⟩, Excl.empty⟩], []⟩ := by decide

#print axioms source_any_target

/-! ### The cleaners one accessor below the fact (`P.f` with `f = 4`) -/

def clAB : Cleaner := ⟨1, [4], .atAndBelow, some 5⟩
def clB  : Cleaner := ⟨1, [4], .below, some 5⟩
def clE  : Cleaner := ⟨1, [4], .exact, some 5⟩

/-- `atAndBelow` at `P.f`: `E ∪ {f}`, normal. -/
theorem clean_atAndBelow :
    cleanResX clAB cIn = ⟨[⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, .set [4]⟩], []⟩ := by decide

#print axioms clean_atAndBelow

/-- `below` at `P.f`: `E ∪ {f}` and `(b, P.f, $, T)`, both normal. -/
theorem clean_below :
    cleanResX clB cIn = ⟨[⟨⟨⟨1, [], .any, .conc 5⟩, false⟩, .set [4]⟩,
      ⟨⟨⟨1, [4], .exact, .conc 5⟩, false⟩, Excl.empty⟩], []⟩ := by decide

#print axioms clean_below

/-- `exact` at `P.f`: the base `concPart`, demand, no exclusion. -/
theorem clean_exact :
    cleanResX clE cIn = ⟨[⟨⟨⟨1, [], .any, .conc 5⟩, true⟩, Excl.empty⟩], []⟩ := by decide

#print axioms clean_exact

/-- The base gives the demand layer for each of the three. -/
theorem clean_base :
    (cleanRes clAB cIn.af).facts = [⟨⟨1, [], .any, .conc 5⟩, true⟩] ∧
    (cleanRes clB cIn.af).facts = [⟨⟨1, [], .any, .conc 5⟩, true⟩] ∧
    (cleanRes clE cIn.af).facts = [⟨⟨1, [], .any, .conc 5⟩, true⟩] := by decide

#print axioms clean_base

/-- A cleaner in the excluded part (`this.name.*`, `name ∈ E`) cleans nothing: the fact passes. -/
theorem clean_excluded : cleanResX ⟨1, [3], .atAndBelow, some 5⟩ cAnn = ⟨[cAnn], []⟩ := by decide

#print axioms clean_excluded

/-- THE ONE NEW FACT: `(b, P.f, $, T)` of the `below` row is not a fact of the base cleaner (so the
    relation "the same base fact" fails for it; `Inside6`/`InsideR` is the general relation). -/
theorem below_new_fact :
    ⟨⟨⟨1, [4], .exact, .conc 5⟩, false⟩, Excl.empty⟩ ∈ (cleanResX clB cIn).facts ∧
    ∀ y, y ∈ (cleanRes clB cIn.af).facts → y.fact ≠ ⟨1, [4], .exact, .conc 5⟩ := by decide

#print axioms below_new_fact

/-! ### The cut -/

/-- The cut drops the exclusion and gives the demand layer. -/
theorem cut_drops :
    limitFX cnt 0 ⟨⟨⟨1, [4], .any, .conc 5⟩, false⟩, .set [3]⟩ =
      ⟨⟨⟨1, [], .any, .conc 5⟩, true⟩, Excl.empty⟩ := by decide

#print axioms cut_drops

/-! ### The emission: the added fact `(x, [], [any-taint], {g}, T)` (`g = 4`) -/

def aAnn : PFact := ⟨1, [], .any, .conc 5⟩

/-- Pattern `(x, [], [any])` (the same path): the must-premise `(x, [], [any-taint], {g}, T)`. -/
theorem emit_at :
    emitTX emitX ⟨1, [], .any, .conc 5⟩ aAnn true (.set [4]) =
      some (⟨1, [], .any, .conc 5⟩, true, .set [4]) := by decide

#print axioms emit_at

/-- Pattern `(x, [g, 6], [any])`: the step down `g` is excluded: nothing. -/
theorem emit_above_excluded : emitTX emitX ⟨1, [4, 6], .any, .conc 5⟩ aAnn true (.set [4]) = none := by
  decide

#print axioms emit_above_excluded

/-- (The base emits the chain: on the base fact the exclusion does not exist.) -/
theorem emit_above_excluded_base :
    emitT ⟨1, [4, 6], .any, .conc 5⟩ aAnn true = some (⟨1, [4, 6], .any, .conc 5⟩, true) := by decide

#print axioms emit_above_excluded_base

/-- Pattern `(x, [7], $)`: the step down `7` is admitted: `(x, [7], $, T)`. -/
theorem emit_above_exact :
    emitTX emitX ⟨1, [7], .exact, .conc 5⟩ aAnn true (.set [4]) =
      some (⟨1, [7], .exact, .conc 5⟩, false, Excl.empty) := by decide

#print axioms emit_above_exact

/-- The added fact below the chain: the added fact itself, with its exclusion. -/
theorem emit_below :
    emitTX emitX ⟨1, [], .any, .conc 5⟩ ⟨1, [7], .any, .conc 5⟩ true (.set [4]) =
      some (⟨1, [7], .any, .conc 5⟩, true, .set [4]) := by decide

#print axioms emit_below

/-! ### The start, the satisfaction, the summary, the restriction, the sink -/

/-- A must-premise with an exclusion starts as itself, normal, with its exclusion. -/
theorem start_must : startX aAnn true (.set [4]) = ⟨⟨aAnn, false⟩, .set [4]⟩ := by decide

#print axioms start_must

/-- The satisfaction reads the exclusion of the added fact `(x, [], [any-taint], {name}, T)`: a premise
    at the same path with no exclusion is not inside it (`satI` accepts it), a premise below an
    admitted accessor is, a premise below the excluded accessor is not, a premise with the same
    exclusion is. -/
theorem sat_vectors :
    satX ⟨1, [], .any, .conc 5⟩ Excl.empty aAnn (.set [3]) = false ∧
    satI ⟨1, [], .any, .conc 5⟩ aAnn = true ∧
    satX ⟨1, [4], .any, .conc 5⟩ Excl.empty aAnn (.set [3]) = true ∧
    satX ⟨1, [3], .any, .conc 5⟩ Excl.empty aAnn (.set [3]) = false ∧
    satX ⟨1, [], .any, .conc 5⟩ (.set [3]) aAnn (.set [3]) = true := by decide

#print axioms sat_vectors

/-- An annotated summary conclusion `(y, [], [any-taint], {name}, T)` gives its exclusion to the
    result. -/
theorem summary_ann :
    applySummaryX cIn aAnn Excl.empty ⟨⟨⟨2, [], .any, .conc 5⟩, false⟩, .set [3]⟩ =
      ⟨[⟨⟨⟨2, [], .any, .conc 5⟩, false⟩, .set [3]⟩], []⟩ := by decide

#print axioms summary_ann

/-- The restriction of the annotated conclusion `(y, [], [any-taint], {name}, T)`: a `D-p` below the
    excluded accessor gives nothing; below an admitted one, the chain `D-p` with no exclusion. -/
theorem restrict_vectors :
    restrictConcX ⟨⟨⟨2, [], .any, .conc 5⟩, false⟩, .set [3]⟩ ⟨2, [3], .any, .star⟩ = none ∧
    restrictConcX ⟨⟨⟨2, [], .any, .conc 5⟩, false⟩, .set [3]⟩ ⟨2, [4], .any, .star⟩ =
      some ⟨⟨⟨2, [4], .any, .conc 5⟩, false⟩, Excl.empty⟩ := by decide

#print axioms restrict_vectors

/-- The sink check reads the exclusion: a sink on the excluded `this.name` does not trigger (the base
    check does); a sink on the admitted `this.g` triggers. -/
theorem check_vectors :
    checkX zeroFact cAnn ⟨1, [3], .exact, .conc 5⟩ = .none ∧
    check zeroFact cAnn.af ⟨1, [3], .exact, .conc 5⟩ = .triggered ∧
    checkX zeroFact cAnn ⟨1, [4], .exact, .conc 5⟩ = .triggered := by decide

#print axioms check_vectors

/-! ### CEGAR: the case `below` is not filtered by the exclusion of the fact

  The brief says "case `below r`: if `r ≠ []` then `E` must admit `r` (else no result)". That rule is
  not sound: `E` restricts the continuation AFTER the path of the fact, and in the case `below` the
  part `r` is ABOVE that path. The fact `(x, [7], [any-taint], {7}, T)` has the location `x.7` (the
  continuation `[]`); the copy `y = x` (`x.* → y.*`, the case `below [7]`) takes it to `y.7`. The
  brief's rule would give nothing (`{7}` does not admit `[7]`), and lose the real flow. The model
  (DESIGN A2: "the result keeps `E` at its new path end") gives `(y, [7], [any-taint], {7}, T)`. -/

def cDeep : XFact := ⟨⟨⟨1, [7], .any, .conc 5⟩, false⟩, .set [7]⟩
def copyE : MicroEdge := (⟨1, [], .star (.set []), .star⟩, ⟨2, [], .star (.set []), .star⟩)

theorem below_keeps :
    bindX cDeep copyE = ⟨[⟨⟨⟨2, [7], .any, .conc 5⟩, false⟩, .set [7]⟩], []⟩ := by decide

#print axioms below_keeps

theorem below_brief_rule_drops : (Excl.set [7]).admits [7] = false := by decide

#print axioms below_brief_rule_drops

/-- The real flow `x.7 → y.7` that the brief's rule would lose: `x.7` is a location of the fact, the
    copy takes it to `y.7`, and `y.7` is a location of the model's result. -/
theorem below_keeps_loc :
    coversFX cDeep.af.fact cDeep.ex ⟨1, [7], 5⟩ ∧
    den copyE.1 copyE.2 ⟨1, [7], 5⟩ ⟨2, [7], 5⟩ ∧
    coversFX ⟨2, [7], .any, .conc 5⟩ (.set [7]) ⟨2, [7], 5⟩ :=
  ⟨⟨rfl, ⟨[], rfl, trivial, rfl⟩, 5, rfl, rfl⟩,
   ⟨rfl, rfl, trivial, rfl, trivial, [7], [7], rfl, rfl, rfl, rfl, rfl⟩,
   ⟨rfl, ⟨[], rfl, trivial, rfl⟩, 5, rfl, rfl⟩⟩

#print axioms below_keeps_loc

end Vec

end ApSpec.AnyTaintEx
