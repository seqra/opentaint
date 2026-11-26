# Backward condition progress: MUST requirements and refined MAY seeds

26 November 2026, branch `saloed/bidirectional`. **Spec and proofs only**
(user decision): no ablation, no prototype, no measurement, no WI rule.

## Overview

> The backward run seeds requirements from the rule conditions of provisional
> findings. Today the layer of a seed depends only on its tail. So an `[any]`
> requirement is always DEMAND, the next forward run gets it again, and the
> demand rows of its method do not go to zero (§II.1). This spec gives the
> rules that let the backward run progress, and their proofs.

**Parts.**

* [Notation](#notation): the names that both parts use. No behaviour.
* [Part I, forward run](#part-i-forward-run): the operations as the forward
  run uses them today, and the two new forward steps.
* [Part II, backward run](#part-ii-backward-run): the seed rules, the
  backward use of the operations, the new rules and decision D1.
* [Gate and checklist](#gate-and-checklist).

**Status labels.** Each rule, table row and example table has one.

| Label | Meaning |
| --- | --- |
| **CURRENT** | `saloed/bidirectional` does this today (source: ap.md, interpreter.md, or the cited code) |
| **CHANGED** | the proposal replaces a CURRENT behaviour; the row gives the CURRENT behaviour too |
| **NEW** | the proposal adds this behaviour; it replaces nothing |
| **OPEN** | needs a user decision |

**Proposed rules.**

| Rule | What it does | Where | Status |
| --- | --- | --- | --- |
| B1 MUST seeds | a requirement from a literal is NORMAL if and only if the literal alone fires the rule (a unary literal): unary `[any]` literals become NORMAL `[any-taint]`, ND `$` literals become DEMAND | §II.2–§II.5 | **CHANGED** |
| B2 backward MUST records | a NORMAL backward summary with a MUST premise is a record; the forward run reads it as a DEMAND view | §II.6, §I.8 | **CHANGED** (backward R1), **NEW** (forward view) |
| B3 refined ND seeds | an ND `[any]` literal is seeded with its meets with the inputs that the forward run captured | §I.3, §II.10 | **CHANGED** (ND `[any]` seeds), **NEW** (capture) |
| D1 hand-off of backward MUST records | does a backward MUST record still give demand to the forward run? | §II.11 | **OPEN** |

**Lean.** [BackCondRules](lean/ApSpec/BackCondRules.lean) (`BackCond`),
[BackMustRun](lean/ApSpec/BackMustRun.lean) (`BackMust`),
[BackMustView](lean/ApSpec/BackMustView.lean) (`BackMustView`),
[BackNDRefine](lean/ApSpec/BackNDRefine.lean) (`BackND`),
[BackCondExamples](lean/ApSpec/BackCondExamples.lean) (`BackCondEx`).
All constructive (`propext`, `Quot.sound` only).

**Examples.** Bases `x y z ret arg0 a b`, fields `f g h k`, marks `T U`.
`zero` is the zero fact: it holds at every reached node. An example id with ✓
(for example `e1 ✓`) is the Lean theorem `BackCondEx.ex_e1`: the executable
model computes the result shown, checked by `decide`.

## Notation

> Locations, facts, rule conditions, summary edges and demand edges. These
> are names only; Part I and Part II give the behaviour.

### N.1 Locations and facts

```text
location        base.path(mark)                a value: base variable, field path, concrete taint mark
fact            base.path.tail(markPattern)
  tail            $                             the location base.path only
                  */exclusion                   base.path·suffix, every admitted suffix, correlated with the premise suffix
                  [any]                         base.path·suffix, every admitted suffix, not correlated
  markPattern     T                             the concrete mark T
                  *                             abstract: the mark of the premise passes through
exclusion       a set of fields
admits(exclusion, suffix)  ⇔  suffix = [] ∨ first(suffix) ∉ exclusion
layer           NORMAL | DEMAND               join: NORMAL ⊔ NORMAL = NORMAL, otherwise DEMAND
annotated fact  (fact, exclusion, layer)

covered(fact, exclusion) = { base.(path·suffix)(mark) | tail admits suffix ∧ admits(exclusion, suffix) ∧ markPattern admits mark }
                           $ admits only [];  */E and [any] admit every suffix;  * admits every mark
inside(fact1, fact2)     ⇔ covered(fact1) ⊆ covered(fact2)            (each with its exclusion)

x.[any-taint]/E(T)  ≝  (x.[any](T), E, NORMAL)         W6: a NORMAL [any] fact is [any-taint]
x.[any](T)          ≝  (x.[any](T), ∅, DEMAND)
```

Placeholders in patterns and rules: `E`, `E1`, `E2` are exclusions; `P`, `Q`
are rule arguments (bases with paths); `T`, `T'`, `U` are marks; `A` is an
alternative of a condition.

### N.2 Rule conditions

```text
literal              a pattern of a condition:  ContainsMark(P, T) is P.$(T);  ContainsMarkOnAnyField(P, T) is P.[any](T)
positive(condition)  the condition with each negated literal replaced by true, in DNF:
                     a set of alternatives, each alternative a set of literals
taintedLocations     a set of locations: the taint at the rule
fires(condition, taintedLocations)  ⇔  ∃ alternative ∈ positive(condition). ∀ literal ∈ alternative.
                                         ∃ location ∈ taintedLocations. location ∈ covered(literal)
sufficient(condition, location)     ⇔  fires(condition, {location})
                                    ⇔  every taintedLocations that contains location fires        [BackCond.suff_iff]
unary literal        {literal} ∈ positive(condition)            code: RulePredicate.isUnary (RulePredicate.kt:199-201);
                                                                legacy sink with one pattern
ND literal           literal ∈ alternative, |alternative| ≥ 2   code: RulePredicate.isMulti; legacy sink with ≥ 2 patterns
```

A literal can be unary and ND (row K5). The classification code is **CURRENT**.

| Claim | Lean (`BackCond`) |
| --- | --- |
| unary literal ⇒ every covered location is sufficient | `unary_seed_must` |
| all literals unary ⇒ the covered locations are exactly the sufficient locations | `unary_cond_exact` |
| ND literal only ⇒ some covered location is not sufficient | `nd_suff_iff`, `nd_seed_not_must` |
| each location of a minimal firing set is covered by some literal (MAY cover) | `seed_may_cover`, `core_spec` |
| sufficiency uses `positive(condition)`, not the signed condition | `firesS_proj`, `signed_not_must` |

| Ex | condition | taintedLocations | fires | Consequence |
| --- | --- | --- | --- | --- |
| c1 ✓ | `ContainsMarkOnAnyField(ret, T)` (unary) | `{ret.f(T)}` | yes | `ret.f(T)` is sufficient: seed `ret.[any-taint](T)` NORMAL (B1, **CHANGED**) |
| c2 ✓ | `a.$(T) ∧ b.[any](U)` (ND) | `{b.f(U)}` | no | `b.f(U)` is not sufficient: both seeds DEMAND (B1, **CHANGED** for `a.$(T)`) |
| c3 ✓ | as c2 | `{a(T), b.f(U)}` | yes | `b.f(U)` is on a route: the DEMAND seeds must cover it |

### N.3 Summary edges

```text
summary  = (direction, method, premise, premiseExclusion, mustPremise, conclusion, conclusionExclusion, layer)
  direction           forward | backward
  program(forward)    = P;   program(backward) = reverse(P): entry and exit swapped, CFG edges reversed
  premise             a fact at the entry of method in program(direction)
  conclusion          a fact at the exit of method in program(direction)
  mustPremise         ⇔ the premise is [any-taint]: emitted from a MUST added fact (§I.4)
written:  direction: premise → conclusion layer     (→must if mustPremise)

flows(direction, method)(entryLocation, exitLocation):
  taint at entryLocation at the entry reaches exitLocation at the exit, in program(direction)
flows(backward, method)(entryLocation, exitLocation)  ⇔  flows(forward, method)(exitLocation, entryLocation)   [Reverse.flow_rev_iff_calls]

pairs(summary) = { (entryLocation, exitLocation) | entryLocation = premise.base.(premise.path·suffix)(mark) ∈ covered(premise),
                   exitLocation ∈ covered(conclusion) at conclusion.path·suffix2, with
                   suffix2 = [] for a $ conclusion, = suffix for a */E conclusion, any for an [any] conclusion;
                   mark carried for a * conclusion, the conclusion mark otherwise }

a NORMAL summary is
  pair-exact  (mustPremise false):  pairs(summary) ⊆ flows(direction, method)
  end-exact   (mustPremise true):   ∀ exitLocation ∈ covered(conclusion). ∃ entryLocation ∈ covered(premise).
                                      flows(direction, method)(entryLocation, exitLocation)
a DEMAND summary covers: every real flow from a covered premise location is in some summary
record           a NORMAL summary that the persistent record store keeps (rule R1: §I.5 forward, §II.6 backward)
```

### N.4 Demand edges

```text
demand edge of a method = (entryDemand, exitDemand)          ap.md names: D-c = entryDemand, D-p = exitDemand
  the previous run hands it off (§I.9); a restricted run analyses the method only for its demand edges
  entryDemand  a pattern at the entry of the method in program(direction)
  exitDemand   a pattern at the exit, or none
```

## Part I. Forward run

> The forward run propagates taint from the sources, checks the sinks and
> builds summaries. The proposal adds two forward steps: the capture of ND
> inputs (§I.3, B3) and the read view of a backward MUST record (§I.8, B2).
> All other forward behaviour is **CURRENT** and is the reference for Part II.

### I.1 Forward facts

> What the two layers mean in the forward run. **CURRENT** (ap.md §4.2, W6).

```text
NORMAL fact        no access-path operation of its derivation over-approximated
[any-taint]/E(T)   a NORMAL [any] fact: every covered location carries T
DEMAND fact        some operation over-approximated; the fact covers the real taint
```

### I.2 Sink check and DEMAND witnesses

> The forward run checks each sink. A finding that needs a DEMAND fact is
> provisional, and its occurrence is a DEMAND witness for the next backward
> run. **CURRENT** (ap.md §9.2).

```text
at a sink statement of method, for each occurrence of the rule:
  fires(condition, the locations of the facts at the statement)
  each fact of the firing combination NORMAL  ⇒  CONFIRMED finding
  otherwise                                  ⇒  provisional finding; DEMAND witness (method, statement, occurrence)
the next backward run seeds each DEMAND witness (§II.3)
```

### I.3 Capture of ND inputs (B3)

> For B3, the forward run keeps the facts that satisfied each ND literal at
> each DEMAND witness. The next backward run meets the ND seeds with them
> (§II.10). **NEW**.

```text
captured(literal; method, statement, occurrence) =
  { (input, inputExclusion) | input satisfied literal in a COMPLETED combination (NORMAL or DEMAND) of the occurrence }
normal form:   input mark    := the concrete mark that the check matched   (a FLOW input: the mark of the literal)
               input */E     := input [any] with exclusion E
```

| Part | Status |
| --- | --- |
| completed combinations: `CompletePredicateBinding(proof, layer, leaves, inputs)` (`RulePredicateStore.kt:99-104`), legacy `ConjunctionStore.CompleteBinding` | **CURRENT** |
| keep the inputs after `freeze()` as a hand-off side table, outside `Seed` equality | **NEW** |
| capture ALL completed combinations, not only the selected proof (`BackND.Vec.cex_selected_only`) | **NEW** |
| the normal form (`Vec.cex_abstract_mark`, `Vec.cex_star_capture`) | **NEW** |

### I.4 Initial fact emission

> A fact that enters a callee is the added fact. The entry demand of the
> callee cuts it into the premise of the callee analysis and gives the start
> fact. **CURRENT** (ap.md §6.3, §6.5). The backward run uses the same
> operation (§II.5).

```text
added fact      the annotated fact that enters the callee by a binding b.* → b'.*:  (added, addedExclusion, addedLayer)
isMust(added)   ⇔  added.tail = [any] ∧ addedLayer = NORMAL           (the added fact is [any-taint])
emit(entryDemand, added)  =  (premise, premiseExclusion, mustPremise, startFact)  or  none
```

| entryDemand mark | added mark | premise | mustPremise | startFact |
| --- | --- | --- | --- | --- |
| `*` (abstract) | any | FLOW form of entryDemand: tail `$`→`$`, `[any]`→`*/{}`, `*/E`→`*/E`; mark `*` | false | the premise, NORMAL (identity) |
| `T` (concrete) | `T` | `meet(added, entryDemand)` | `isMust(added) ∧ premise.tail = [any]` | if mustPremise: the premise with premiseExclusion, NORMAL; else by tail: `$` → NORMAL; `[any]`, `*/E` → `[any]` DEMAND |
| `T` (concrete) | other | none | — | — |

```text
meet(added, entryDemand),   demandPath = entryDemand.path,   demandTail = entryDemand.tail:
  added below   added.path = demandPath·suffix, suffix ≠ []    added                                         if demandTail admits suffix
  added at      added.path = demandPath                        demandPath with meetTail(added.tail, demandTail)
  added above   demandPath = added.path·suffix, suffix ≠ []    demandPath with meetTail(added.tail, demandTail)
                                                               if added.tail and addedExclusion admit suffix
  otherwise none
premiseExclusion = addedExclusion if the premise path is the added path;  ∅ at a deeper demand path
```

| meetTail(added tail, demand tail) | demand `$` | demand `[any]` | demand `*/E2` |
| --- | --- | --- | --- |
| `$` | `$` | `$` | `$` |
| `[any]` | `$` | `[any]` | `*/E2` |
| `[any-taint]/E1` | `$` | `[any-taint]/E1` | no canonical case |

Contract: each common location with its mark is covered by the premise, the
added fact satisfies the premise, and the premise is inside entryDemand
(`AnyTaintExCov.emitX_contract`).

Examples (forward, all **CURRENT**; the must rows e3, e5, e6 are **NEW** in the backward run, §II.5):

| Ex | entryDemand | added fact | premise, mustPremise, premiseExclusion | startFact | Case |
| --- | --- | --- | --- | --- | --- |
| e1 ✓ | `x.[any](T)` | `x.f.$(T)` NORMAL | `x.f.$(T)`, false | `x.f.$(T)` NORMAL | added below |
| e2 ✓ | `x.f.[any](T)` | `x.[any](T)` DEMAND | `x.f.[any](T)`, false | `x.f.[any](T)` DEMAND | added above |
| e3 ✓ | `x.f.[any](T)` | `x.[any-taint]/{g}(T)` NORMAL | `x.f.[any-taint](T)`, true, `∅` | `x.f.[any-taint](T)` NORMAL | above: the exclusion is not kept at the deeper path |
| e4 ✓ | `x.f.[any](T)` | `x.[any-taint]/{f}(T)` NORMAL | none | — | the exclusion rejects `f` |
| e5 ✓ | `x.[any](T)` | `x.[any-taint]/{g}(T)` NORMAL | `x.[any-taint]/{g}(T)`, true, `{g}` | `x.[any-taint]/{g}(T)` NORMAL | added at |
| e6 ✓ | `x.$(T)` | `x.[any-taint]/{g}(T)` NORMAL | `x.$(T)`, false | `x.$(T)` NORMAL | `meetTail([any-taint], $) = $` |
| e7 ✓ | `x.[any](*)` | `x.[any-taint](T)` NORMAL | `x.*/{}(*)`, false (FLOW) | identity, NORMAL | abstract entryDemand (`Abs.emitW`) |
| e8 ✓ | `x.[any](T)` | `x.f.$(U)` NORMAL | none | — | the marks differ |

### I.5 Forward summaries and records

> Which forward summaries the record store keeps (rule R1). **CURRENT**
> (ap.md §8.7 R1).

```text
record(forward summary)  ⇔  layer = NORMAL ∧ one premise (the zero premise is allowed)
                            also with [any-taint] leaves, also with a must premise (a MUST record: end-exact)
```

| Ex | method | summary | Meaning | Record | Status |
| --- | --- | --- | --- | --- | --- |
| m1 | `ret.f = arg0` | `forward: arg0.$(T) → ret.f.$(T)` NORMAL | `pairs = {(arg0(T), ret.f(T))}` ⊆ flows: pair-exact | yes | **CURRENT** |
| m2 | `ret.f = arg0` | `forward: arg0.*/{}(*) → ret.f.*/{}(*)` NORMAL (FLOW) | `pairs = {(arg0.suffix(mark), ret.f.suffix(mark))}`: pair-exact | yes | **CURRENT** |
| m3 | `ret.g = arg0` | `forward: arg0.[any-taint](T) →must ret.g.[any-taint](T)` NORMAL | each `ret.g.suffix(T)` comes from some `arg0` location: end-exact | yes | **CURRENT** |

### I.6 Restriction by the demand edge

> In a restricted run, each new summary is cut to the demand edges of its
> method. The cut keeps exactly the demanded pairs. Record persistence (R1)
> and selection (§I.9) read the raw summary, before the cut. **CURRENT**
> (ap.md §6.4).

```text
restrict(summary, (entryDemand, exitDemand)) =
  none  if exitDemand = none
        ∨ ¬inside(premise, entryDemand)                          locations and marks; reads premiseExclusion
        ∨ ¬marksMeet(conclusion mark, exitDemand mark)           T and U meet ⇔ T = U;  * meets each mark
        ∨ conclusion.base ≠ exitDemand.base
  else  the summary with conclusion := cutConclusion(conclusion, exitDemand)      premise, mustPremise, layer kept
```

| conclusion against exitDemand (`demandPath = exitDemand.path`) | cutConclusion |
| --- | --- |
| at `demandPath` | at `demandPath`, tail by the table below |
| below: `conclusion.path = demandPath·suffix` | the conclusion if `exitDemand.tail` admits `suffix`; else none |
| above: `demandPath = conclusion.path·suffix`, tail `[any]` | at `demandPath`: `$` for a `$` demand, else `[any]` |
| above, tail `[any-taint]/E` | none if `E` rejects `suffix`; else at `demandPath`: `$`, `[any-taint]/E2`, `[any-taint]/∅` for a `$`, `*/E2`, `[any]` demand |
| above, tail `*/E` | the conclusion if `E` admits `suffix`; else none |
| above with tail `$`; apart; other base | none |

| tail at `demandPath` | demand `$` | demand `*/E2` | demand `[any]` |
| --- | --- | --- | --- |
| `$` | `$` | `$` | `$` |
| `[any]` | `$` | `[any]` | `[any]` |
| `[any-taint]/E` | `$` | `[any-taint]/(E ∪ E2)` | `[any-taint]/E` |
| `*/E` | `*/E` | `*/E` | `*/E` |

Contract: each pair of the summary whose exit location is covered by
exitDemand (with its mark) is a pair of the result, and the result adds no
pair (`HandoffRestrict.restrictI_contract`, `restrictI_sub`;
`CurrentDemand.restrictCertificate`). Limits: `[any]` at a `*/E2` demand
loses `E2`; a `*` conclusion stays whole; an abstract mark passes through.

Examples (all **CURRENT**):

| Ex | summary | demand edge | restrict | Case |
| --- | --- | --- | --- | --- |
| r1 ✓ | `arg0.$(T) → ret.f.g.$(T)` NORMAL | `(arg0.[any](T), ret.[any](T))` | `ret.f.g.$(T)` NORMAL | below, kept |
| r2 ✓ | `arg0.$(T) → ret.[any](T)` DEMAND | `(arg0.[any](T), ret.f.$(T))` | `ret.f.$(T)` DEMAND | above, `[any]` at a `$` demand |
| r3 ✓ | `arg0.$(T) → ret.f.$(T)` NORMAL | `(arg0.[any](T), none)` | none | no exitDemand |
| r4 ✓ | `arg0.$(T) → ret.$(U)` NORMAL | `(arg0.$(T), ret.$(T))` | none | the marks do not meet |
| r5 ✓ | `arg0.[any](T) → ret.$(T)` NORMAL | `(arg0.f.[any](T), ret.[any](T))` | none | the premise is not inside entryDemand |
| r6 ✓ | `… → ret.f.$(T)` NORMAL | exitDemand `ret.*/{}(T)` | `ret.f.$(T)` NORMAL | below, `*/{}` admits `f` |
| r7 ✓ | `… → ret.f.$(T)` NORMAL | exitDemand `ret.$(T)` | none | below, `$` rejects `f` |
| r8 ✓ | `… → ret.[any-taint]/{h}(T)` NORMAL | exitDemand `ret.f.[any](T)` | `ret.f.[any-taint](T)` NORMAL, exclusion `∅` | above, `[any]` demand |
| r9 ✓ | `… → ret.[any-taint]/{h}(T)` NORMAL | exitDemand `ret.h.[any](T)` | none | the exclusion rejects `h` |
| r10 ✓ | `… → ret.[any-taint]/{h}(T)` NORMAL | exitDemand `ret.f.$(T)` | `ret.f.$(T)` NORMAL | above, `$` demand |
| r11 | `… → ret.[any-taint]/{h}(T)` NORMAL | exitDemand `ret.*/{k}(T)` | `ret.[any-taint]/{h,k}(T)` NORMAL | at; the Lean model keeps `/{h}` (wider, `ex_r11_model`) |

r1–r5: `Handoff.restrictI` (gates and cut). r6–r11: `restrictConcX` (cut with exclusion).

### I.7 Applying summaries and records

> A summary of the callee gives results for an added fact in the caller.
> A summary of this run needs the premise inside the added fact; a record
> of an earlier run also accepts an applicable premise. A must premise that
> is not inside gives a DEMAND result (the MUST rule). **CURRENT** (ap.md
> §8.7 R4).

```text
inside(premise, added)       ⇔  covered(premise, premiseExclusion) ⊆ covered(added, addedExclusion), marks too   [AnyTaintEx.satX]
applicable(premise, added)   ⇔  covered(added) ⊆ covered(premise) ∧ (premise.tail = [any] ⇒ added.tail = [any])   [Basic.applicable]
summary of this run (restricted piece):   used if inside(premise, added)
record (R4, later runs):                  used if inside(premise, added) ∨ applicable(premise, added)
result layer = addedLayer ⊔ conclusion layer
MUST rule:  mustPremise ∧ ¬inside(premise, added)  ⇒  result layer := DEMAND, result exclusion := ∅     [AnyTaintEx.recLayerX]
```

An end-exact summary gives each exit location SOME source in the premise.
Only `inside` puts each source in the added fact
(`AnyTaintExact.CexApp.cex_app`). Proof that the NORMAL results are exact:
`AnyTaintExExact.DRX_edgeOK`.

Examples (all **CURRENT**):

| Ex | added fact | summary | inside | applicable | Result |
| --- | --- | --- | --- | --- | --- |
| a1 ✓ | `arg0.$(T)` NORMAL | `forward: arg0.$(T) → ret.f.$(T)` NORMAL | yes | yes | `ret.f.$(T)` NORMAL |
| a2 ✓ | `arg0.h.$(T)` NORMAL | `forward: arg0.*/{}(*) → ret.f.*/{}(*)` NORMAL | no | yes | `ret.f.h.$(T)` NORMAL (as a record only) |
| a3 ✓ | `arg0.$(T)` DEMAND | as a1 | yes | yes | `ret.f.$(T)` DEMAND (layer join) |
| a4 ✓ | `arg0.[any-taint](T)` NORMAL | `forward: arg0.[any-taint](T) →must ret.g.[any-taint](T)` NORMAL | yes | yes | `ret.g.[any-taint](T)` NORMAL |
| a5 ✓ | `arg0.h.[any-taint](T)` NORMAL | as a4 | no | yes | `ret.g.[any](T)` DEMAND (MUST rule) |
| a6 ✓ | `arg0.h.$(T)` NORMAL | as a4 | no | no | not used; the run analyses the callee for the added fact |

### I.8 Reading backward records

> A forward fact at the forward entry of a method reads the backward records
> of that method in the opposite orientation (ap.md §8.7 R2, R3). A backward
> record with `$` or `*` leaves is an exact forward record (**CURRENT**). A
> backward MUST record exists only with B2; its view gives a DEMAND result
> (**NEW**).

```text
backward record   premise at the backward entry (= forward exit)  →  conclusion at the backward exit (= forward entry)
forward view      new premise = the old conclusion;  new conclusion = the old premise

  old premise $ or */E, mark reversible      generic leaf reversal (ap.md §9.1): exact forward record
  old premise x.[any-taint]/E(T), must (B2)  if the added fact meets the old conclusion (locations and marks):
                                             new conclusion x.[any](T) DEMAND, E forgotten        [BackMustView.viewF]
result layer = addedLayer ⊔ new conclusion layer
```

| Backward record | View | Status | Lean |
| --- | --- | --- | --- |
| `$`/`*` leaves, may premise | exact forward record | **CURRENT** | `AnyTaintSim.backRec_exact`, `BExact.revRecs_exact` |
| must premise (B2) | sound, DEMAND only, not exact | **NEW** | `BackMustView.viewF_demand`, `viewF_stays_demand`, `viewF_sound`, `Cex.viewF_not_exact` |

| Ex | backward record | added fact (forward) | Result | Status |
| --- | --- | --- | --- | --- |
| v4 ✓ | `backward: ret.[any-taint](T) →must arg0.[any-taint](T)` NORMAL | `arg0.h.$(T)` NORMAL | `ret.[any](T)` DEMAND | **NEW** (B2) |
| v5 ✓ | as v4 | `arg0.h.$(U)` NORMAL | none (the marks do not meet) | **NEW** (B2) |

### I.9 Hand-off selection

> At the end of a run, the selected summaries give the demand edges of the
> next run; the other summaries are records and give no demand (F77).
> **CURRENT** (ap.md §8.5, `HandOff.kt:221-237`).

```text
selected(summary)  ⇔  layer = DEMAND ∨ |premises| ≥ 2 ∨ (direction = backward ∧ premise = zero)
selected      ⇒  each restricted piece  premise → conclusion2  gives the next run the demand edge
                 (entryDemand = conclusion2, exitDemand = premise);  [any-taint]/E tails become [any], exclusions dropped
not selected  ⇒  the summary is a record (R1): no demand; the next run reads the record (§I.8, §II.9)
```

| Ex | summary | selected | Next run (backward) | Status |
| --- | --- | --- | --- | --- |
| q1 | `forward: arg0.$(T) → ret.f.$(T)` NORMAL | no | reads the record (v1 type, §II.9) | **CURRENT** |
| q2 | `forward: arg0.[any](T) → ret.[any](T)` DEMAND | yes | callee demand edge `(ret.[any](T), arg0.[any](T))` | **CURRENT** |

### I.10 Proofs and model notes (forward)

> Where the forward claims are proved, and where the model differs from the
> code.

| Claim | Lean |
| --- | --- |
| NORMAL forward summaries are pair-exact or end-exact | `AnyTaintExExact.DRX_edgeOK` |
| emission contract | `AnyTaintExCov.emitX_contract`, `Abs.emitW_contract` |
| restriction keeps exactly the demanded pairs | `HandoffRestrict.restrictI_contract`, `restrictI_sub`, `restrictI_inter`; `CurrentDemand.restrictCertificate` |
| the MUST rule is necessary | `AnyTaintExact.CexApp.cex_app` |
| the forward view of a backward MUST record (B2) | `BackMustView` (§I.8) |
| the examples | `BackCondEx` |

* `restrictConcX` keeps `[any-taint]/E` at the same path for a `*/E2`
  demand and gives `[any-taint]/∅` above it; ap.md gives `/(E ∪ E2)` and
  `/E2`. The model is wider and sound (r11).
* `BackMustView`: one record, one leaf; no store lookup, statics, cleaners
  or type filters.

## Part II. Backward run

> The backward run starts at the DEMAND witnesses of the previous forward
> run (§I.2) and walks `reverse(P)`. A backward fact is a requirement: where
> taint must be for the sink to fire. The run hands demand to the next
> forward run (§II.11). B1, B2, B3 and D1 are in this part.

Run numbering: run `n` is the backward run; run `n−1` is the forward run
before it; run `n+1` is the forward run after it.

### II.1 Problem

> Why the backward run does not progress today. **CURRENT** behaviour.

The layer of a seed does not depend on the forward facts or on the MUST
status of the literal. An `[any]` requirement is DEMAND (W6). A callee that
it enters gets a DEMAND start fact, DEMAND summaries, no record, and a
selected hand-off row. Forward run `n+1` gets an `[any]` entryDemand; the
emission makes a `*` start fact that is DEMAND by itself; the DEMAND witness
stays; backward run `n+2` seeds it again.

| Real instance (after AO-C5) | Demand rows | Source |
| --- | --- | --- |
| Stirling-PDF `AuthController#login` and its entry point | 1 + 2 | acyclic-convergence §6, §7 item 2 |
| Stirling-PDF `bytesToWebResponse` arms | not counted | natural-termination §3 |

Not measured: the rows per run from `[any]` seeds, reversed `[any]`
literals and ND seeds.

### II.2 Requirements and their layer (B1)

> A NORMAL requirement must mean MUST: taint at any covered location fires
> the sink. B1 gives a requirement NORMAL exactly when its literal is unary.
> **CHANGED**.

```text
requirement (fact, exclusion, layer) at a node of reverse(P):
  NORMAL (MUST)   ∀ location ∈ covered(fact, exclusion): taint at location at the node ⇒ the seeded sink fires
  DEMAND (MAY)    the DEMAND requirements cover each location of a real route to the sink

layer of the requirement from a literal:
  CURRENT   NORMAL ⇔ literal.tail = $          seedFact (RunMethodLocalServices.kt:437-449) seeds NORMAL; W6 makes [any] DEMAND
  B1        NORMAL ⇔ literal is unary          [BackCond.reqs_normal_must, reqs_nd_demand]
```

| Literal | CURRENT layer | B1 layer | Status |
| --- | --- | --- | --- |
| unary `$` | NORMAL | NORMAL | **CURRENT** |
| unary `[any]` | DEMAND (`[any]`) | NORMAL (`[any-taint]`) | **CHANGED** |
| ND `$` | NORMAL (not MUST: breaks the meaning) | DEMAND | **CHANGED** |
| ND `[any]` | DEMAND | DEMAND, refined (B3) | **CHANGED** (B3) |

With B1, a CURRENT ND `$` seed would make false MUST facts. Example: the
reversed source rule S3 turns `P.$(T)` NORMAL into `Q.[any-taint](T')`
NORMAL.

### II.3 Sink seeds

> The seeds of each rule literal at a DEMAND witness. The last column is
> what the seed reads from forward run `n−1`.

| # | Rule condition | Seed | Status | Input from forward run `n−1` |
| --- | --- | --- | --- | --- |
| K1 | `ContainsMark(P, T)`, unary | `P.$(T)` NORMAL | **CURRENT** | DEMAND witness (method, statement, occurrence) |
| K2 | `ContainsMarkOnAnyField(P, T)`, unary | `P.[any-taint](T)` NORMAL, exclusion `∅` | **CHANGED**: CURRENT `P.[any](T)` DEMAND | DEMAND witness |
| K3 | `ContainsMark(P, T)`, ND | `P.$(T)` DEMAND | **CHANGED**: CURRENT `P.$(T)` NORMAL | DEMAND witness (refinement is the identity) |
| K4 | `ContainsMarkOnAnyField(P, T)`, ND | `refinedSeeds(literal)` DEMAND (§II.10) | **CHANGED**: CURRENT `P.[any](T)` DEMAND | DEMAND witness and `captured(literal)` (§I.3) |
| K5 | a literal that is unary and ND | as K1 or K2 | **CHANGED** with K2 | DEMAND witness |
| K6 | no positive literal; unconditional sink | none: the zero demand covers it | **CURRENT** | DEMAND witness |
| K7 | end-fact trigger of alternative `A` (row S8 fired) | K1–K4 with no capture | as K1–K4 | none |
| K8 | GROUP-projected sink (`fullSinkSeedsFor`) | K1–K4 with no capture | as K1–K4 | DEMAND witness |

### II.4 Reversed statement rules

> A reversed rule turns a requirement on the rule target (layer
> `targetLayer`) into requirements on the rule inputs. The MAY class gives
> DEMAND results only.

| # | Rule | Backward result | Status | Input from forward run `n−1` |
| --- | --- | --- | --- | --- |
| S1 | unconditional source `zero → P.tail(T)`, tail `$` or `[any-taint]` | zero (zero demand); a source hit | **CURRENT** | none (run `n+1` fires the source only if hit) |
| S2 | conditional source, unary `ContainsMark(Q, T')` | `Q.$(T')` in targetLayer | **CURRENT** | none |
| S3 | conditional source, unary `ContainsMarkOnAnyField(Q, T')` | `Q.[any-taint](T')` in targetLayer | **CHANGED**: CURRENT `Q.[any](T')` DEMAND | none |
| S4 | conditional source, ND `ContainsMark(Q, T')` | `Q.$(T')` DEMAND | **CURRENT** | none (refinement is the identity) |
| S5 | conditional source, ND `ContainsMarkOnAnyField(Q, T')` | `refinedSeeds(literal)` DEMAND (§II.10) | **CHANGED**: CURRENT `Q.[any](T')` DEMAND | `captured(literal)` at the source occurrence |
| S6 | pass rule `P → Q` (no `AnyField`) | the reversed result in targetLayer | **CURRENT** | none |
| S7 | pass rule `P → Q.AnyField` | each result DEMAND | **CURRENT** | none |
| S8 | end-fact action of sink alternative `A` | zero; fires K7 at (method, statement, `A`) once | **CURRENT** | none (also if `A` is CONFIRMED) |
| S9 | cleaner, type filter | unchanged rule | **CURRENT** (see S-H2) | none |

MAY class: K3, K4, S4, S5, S7. Each result is DEMAND, also a `$` result
(DES-3, D18). The DEMAND layer is **CURRENT** for K4, S4, S5, S7 and
**CHANGED** for K3.

A MUST requirement gets an exclusion at a strong update. A DEMAND `[any]`
requirement has no exclusion (`BackMust.transferXB`). Program:
`x.f = z; …; x.f = y; sink(x)`, walked backward.

| Ex | at `sink(x)` | after reversed `x.f = y` | after reversed `x.f = z` | Status |
| --- | --- | --- | --- | --- |
| t1 ✓ | `x.[any-taint](T)` NORMAL | `y.[any-taint](T)`, `x.[any-taint]/{f}(T)` NORMAL | `y.[any-taint](T)`, `x.[any-taint]/{f}(T)` NORMAL: no requirement on `z` | **NEW** (B1) |
| t2 ✓ | `x.[any](T)` DEMAND | `y.[any](T)`, `x.[any](T)` DEMAND | `y.[any](T)`, `z.[any](T)`, `x.[any](T)` DEMAND | **CURRENT** |

### II.5 Calls into callees

> A requirement enters a callee as the added fact of the emission (§I.4,
> ap.md §9.2). Today no backward added fact is MUST (W8 (d)), so the must
> rows of §I.4 do not occur; with B1 they do.

entryDemand: from the demand edge that forward run `n−1` handed off for the callee.

| # | requirement | entryDemand | premise, mustPremise | startFact | callee summary | Status |
| --- | --- | --- | --- | --- | --- | --- |
| C1 | `x.[any-taint]/E(T)` NORMAL | concrete `x.[any](T)` | `x.[any-taint]/E(T)`, true (e5) | NORMAL | end-exact; a record (B2); hand-off: D1 | **NEW**: CURRENT requirement `x.[any](T)` DEMAND → C4 |
| C2 | `x.[any-taint]/E(T)` NORMAL | concrete `x.$(T)` | `x.$(T)`, false (e6) | NORMAL | pair-exact record; caller results NORMAL | **CHANGED**: CURRENT same summary, caller results DEMAND |
| C3 | `x.[any-taint]/E(T)` NORMAL | abstract `x.[any](*)` | `x.*/{}(*)`, false (e7) | identity, NORMAL | pair-exact FLOW record; caller results NORMAL | **CHANGED**: CURRENT caller results DEMAND |
| C4 | `x.[any](T)` DEMAND | concrete `x.[any](T)` | `x.[any](T)`, false (e2 type) | DEMAND | DEMAND, selected | **CURRENT** |
| C5 | `x.$(T)` NORMAL | concrete | `x.$(T)`, false (e1 type) | NORMAL | pair-exact record | **CURRENT** |

The results return to the caller by §II.8 (backward summaries and records)
and §II.9 (forward records).

### II.6 Backward summaries and records (B2)

> Which backward summaries the record store keeps. B2 adds the MUST
> records. **CHANGED** (ap.md §8.7 R1, `RecordStore.kt:274-277`).

```text
record(backward summary):
  CURRENT   layer = NORMAL ∧ one premise ∧ premise ≠ zero ∧ ¬mustPremise ∧ no [any-taint] leaf
  B2        layer = NORMAL ∧ one premise ∧ premise ≠ zero
```

A backward MUST record is end-exact on `reverse(P)` and not pair-exact
(`BackMust.recsB_must_end`, `CexMustPair.cex_must_pair`). A zero-premise
backward summary is never a record: a seed relates `zero` to each seed
location, which is not a flow.

| Ex | method | summary | Meaning | Record | Status |
| --- | --- | --- | --- | --- | --- |
| m4 | identity `M(arg0)` | `backward: arg0.[any-taint](T) →must arg0.[any-taint](T)` NORMAL | end-exact (the source of `arg0.f` is `arg0.f`); `(arg0.f, arg0.g)` is a pair and no flow: not pair-exact | B2: yes | **NEW**: CURRENT no |
| m5 | `sink(arg0)` in `M` | `backward: zero → arg0.[any-taint](T)` NORMAL | a seed path, not a flow | no | **CURRENT** rule (the `[any-taint]` seed is B1) |

### II.7 Restriction in the backward run

> The backward run cuts its summaries by the operation of §I.6. **CURRENT**
> for may summaries. The `[any-taint]` rows of §I.6 now apply to backward
> summaries: **NEW** (B1, B2).

| Ex | summary | demand edge | restrict | Status |
| --- | --- | --- | --- | --- |
| r12 ✓ | `backward: ret.[any-taint](T) →must arg0.[any-taint](T)` NORMAL | `(ret.[any](T), arg0.h.$(T))` | `arg0.h.$(T)` NORMAL | **NEW** (B1, B2) |

### II.8 Applying backward summaries and records

> The backward run applies callee summaries and records by the rules of
> §I.7. The MUST rule now also applies to backward MUST records: **NEW**
> (B2).

| Ex | requirement | backward summary | inside | applicable | Result | Status |
| --- | --- | --- | --- | --- | --- | --- |
| a7 ✓ | `ret.[any-taint](T)` NORMAL | `ret.[any-taint](T) →must arg0.[any-taint](T)` NORMAL | yes | yes | `arg0.[any-taint](T)` NORMAL | **NEW** (B2) |
| a8 ✓ | `ret.f.[any-taint](T)` NORMAL | as a7 | no | yes | `arg0.[any](T)` DEMAND (MUST rule) | **NEW** (B2) |

In a8, end-exactness gives each `arg0` location SOME source under `ret`;
that source can be outside `ret.f`.

### II.9 Reading forward records

> A requirement at the forward exit of a method reads the forward records of
> that method in the opposite orientation (ap.md §8.7 R3). **CURRENT**.

```text
special must view: guard  both marks concrete; each tail $ or [any-taint]; at least one [any-taint]; a $ side has exclusion ∅
  new premise from the old conclusion:   x.p.$(T) kept;            x.p.[any-taint]/E(T)  →  x.p.*/E(T)
  new conclusion from the old premise:   P.$(U) kept, NORMAL;      P.[any-taint]/E2(U)   →  P.[any](U) DEMAND, E2 forgotten
other shapes: generic leaf reversal (ap.md §9.1)
result layer = requirement layer ⊔ new conclusion layer
```

| Forward record | View | Lean |
| --- | --- | --- |
| `$` premise | exact converse, NORMAL | `CurrentMustReverse.exact_converse` |
| must premise | sound, DEMAND only, not exact | `CurrentMustReverse.must_application_demand`, `AnyTaintExact.CexRev.cex_rev` |

Examples (all **CURRENT**):

| Ex | forward record | view | requirement | Result |
| --- | --- | --- | --- | --- |
| v1 ✓ | `forward: arg0.$(T) → ret.[any-taint](T)` NORMAL | `ret.*/{}(T) → arg0.$(T)` NORMAL | `ret.h.$(T)` NORMAL | `arg0.$(T)` NORMAL (exact) |
| v2 ✓ | `forward: arg0.[any-taint](T) →must ret.g.[any-taint](T)` NORMAL | `ret.g.*/{}(T) → arg0.[any](T)` DEMAND | `ret.g.h.$(T)` NORMAL | `arg0.[any](T)` DEMAND |
| v3 ✓ | `forward: arg0.[any-taint](T) →must ret.f.$(T)` NORMAL | `ret.f.$(T) → arg0.[any](T)` DEMAND | `ret.f.$(T)` NORMAL | `arg0.[any](T)` DEMAND |

### II.10 ND refinement (B3)

> An ND `[any]` literal is seeded with its meets with the captured inputs
> of forward run `n−1`, not with the whole literal. **NEW**.

```text
refinedSeeds(literal) =
  { meet(input, literal) | (input, inputExclusion) ∈ captured(literal) } minus none     if captured(literal) ≠ ∅
  { literal }                                                                          if captured(literal) = ∅   (fallback)
meet: the concrete row of §I.4
layer: DEMAND;  the meet exclusion is forgotten;  a $ literal: meet(input, literal) = literal (no change)
```

| Claim | Lean (`BackND`) |
| --- | --- |
| `covered(meet(input, literal)) = covered(input) ∩ covered(literal)` for a concrete input | `meetLit_inter` |
| each refined seed is inside the literal, also without its exclusion | `refine_inside`, `meetLit_forget_inside` |
| real route locations ⊆ `covered(literal) ∩ covered(captured)` ⇒ they are covered by the refined seeds | `refine_sound`, `refine_sound_strict`, `forwardCaptured_of_combos` |
| smaller captures with the same literals give smaller seeds | `refine_mono`, `refine_mono_seq` |
| deterministic; paths from the literal or the capture; `≤ |captured| + |literals|` seeds; legal seeds | `refine_det`, `refine_det_set`, `refine_shape`, `refine_length`, `refine_legal` |
| the backward contract and the iteration theorem with refined seeds | `B_general_refined`, `iteration_general_refined` |
| capture of the selected proof only loses a real location | `Vec.cex_selected_only` |
| a `*` mark capture gives no seed; a `*/E` capture gives an illegal seed | `Vec.cex_abstract_mark`, `Vec.cex_star_capture` |
| if a literal loses all its captures, the fallback makes its seed larger | `Vec.cex_mono_fallback` |

Literals of c2: literal 0 is `a.$(T)`, literal 1 is `b.[any](U)`.

| Ex | captured | Seeds | Note | Status |
| --- | --- | --- | --- | --- |
| n1 ✓ | 0: `a.$(T)`; 1: `b.f.$(U)`, `b.g.h.$(U)` | `a.$(T)`, `b.f.$(U)`, `b.g.h.$(U)` DEMAND | two field chains replace `b.[any](U)` | **NEW** |
| n2 ✓ | 1: `b.g.[any]/{k}(U)` | `a.$(T)` (fallback), `b.g.[any](U)` DEMAND | the code forgets `{k}`; the model keeps it | **NEW** |
| n3 ✓ | none | `a.$(T)`, `b.[any](U)` DEMAND | the fallback | **CURRENT** except the K3 layer |
| n4 ✓ | 1: `b.f.*/{}(*)`, not in normal form | `a.$(T)` DEMAND only | literal 1 gets no seed: the normal form is necessary | excluded by the **NEW** normal form |

Not selected: B3-P (fallback = the previous seed, and each seed met with
it). It is monotone by construction, but it keeps seed state across runs and
can remove a demand that the CURRENT behaviour keeps (S-H6).

### II.11 Hand-off of backward summaries and D1

> The selection rule of §I.9 decides which backward summaries give demand
> to forward run `n+1`. With B2 a backward MUST summary is a NORMAL
> singleton, so F77 does not select it. This can lose a confirmation.
> **OPEN** (D1).

```text
CURRENT   backward NORMAL non-zero singleton summaries: records, not selected; zero-premise summaries: selected
B2 + F77  selected(backward: premise →must conclusion NORMAL) = false
          ⇒ run n+1 does not analyse the callee again; it reads only the view of §I.8, which is DEMAND
```

Counterexample `BackMustView.Cex.cex_drop_forward_demand`:

```text
callee:      ret.f.g = arg0;        sink rule ContainsMarkOnAnyField(ret, T) on the call result
caller fact: arg0.h.$(T) NORMAL enters the callee
forward run 1, field limit 1:                          ret.f.[any](T) DEMAND   → provisional, DEMAND witness
backward run 2 (B1, B2):   record  ret.[any-taint](T) →must arg0.[any-taint](T) NORMAL;  F77: not selected
forward run 3, field limit 3, CURRENT callee demand:   ret.f.g.h.$(T) NORMAL   → CONFIRMED
forward run 3, field limit 3, H1 (view only):          ret.[any](T) DEMAND     → stays provisional
```

Only a backward MUST record has this defect. A forward must record goes to
the backward run, which confirms nothing; a `$`-premise record has an exact
view.

| Option | selected(backward must summary) | Results | Demand rows removed | Status |
| --- | --- | --- | --- | --- |
| H1 omit | false (F77 unchanged) | can lose a confirmation | yes | **OPEN** |
| H1g omit if covered | true, unless a NORMAL, pair-exact, complete forward record of the callee covers the conclusion | kept (`BackMustView.guard_keeps_normal`, canonical FLOW records; `Cex.guard_instance`) | few: F77 already drops that demand | **OPEN** |
| H2 select | true | kept, except S-H1 | none | **OPEN** |
| H3 forward MUST meet | false, and a new forward rule: an exists-any tail, or a confirmation where a forward NORMAL fact meets a backward MUST requirement, with a trace | can keep it | yes; changes the forward run, the sink check, trace resolution; not designed | **OPEN**, unselected major change |

Recommendation: prototype B1 + B2 + B3 with H2, and log in shadow mode the
callee demands that H1 would drop, and whether the CURRENT forward run gets a
NORMAL callee summary under them. No case on all projects and suites ⇒ gate
H1. A case ⇒ withdraw H1; the owners of §II.1 then need H3.

| Ex | summary | selected | Run `n+1` (forward) | Status |
| --- | --- | --- | --- | --- |
| q3 | `backward: zero → arg0.[any-taint](T)` NORMAL | yes | demand from the zero row | **CURRENT** rule |
| q4 | `backward: ret.[any-taint](T) →must arg0.[any-taint](T)` NORMAL | F77: no | H1: no callee demand, only v4; H2: callee demand edge `(arg0.[any](T), ret.[any](T))` | **OPEN** |

### II.12 Semantic scope

> What the proposal changes, what it keeps, which documented invariants
> change, and the changes that are not yet proved or measured.

| Change | Rows | Status |
| --- | --- | --- |
| unary `[any]` sink seed: DEMAND → NORMAL MUST | K2 | **CHANGED** |
| ND `$` sink seed: NORMAL → DEMAND (user correction, 26 Nov) | K3 | **CHANGED** |
| reversed unary `[any]` source literal: DEMAND → targetLayer MUST | S3 | **CHANGED** |
| caller results through C2/C3 records: DEMAND → NORMAL | C2, C3 | **CHANGED** |
| backward MUST added fact, must premise, NORMAL start | C1 | **NEW** |
| backward MUST records: R1, R4, forward view | C1, §II.6, §II.8, §I.8 | **NEW** |
| ND `[any]` seeds and reversed ND `[any]` literals refined; capture | K4, S5, §II.10, §I.3 | **NEW** |
| hand-off of a backward MUST record | §II.11 | **OPEN** |

Unchanged (**CURRENT**): the forward run except §I.3 and §I.8 (transfer,
sink check, layers, records, views of forward records, confirmation,
traces); S4, S5 layer, S7; unary `$` seeds (K1); zero rows; source hits;
C4, C5; the operations of §I.4, §I.6, §I.7; field limits and FL+1 caps;
hand-off normalization; W8 (d) for demand patterns (`Demand.kt:41`,
`DemandStore.kt:449`); confirmed and provisional results (the gate).

| Documented invariant | Change |
| --- | --- |
| interpreter.md I11 (f), I14 ("the backward run has no `[any-taint]`"), §4.9 | K2, S3; "no micro edge has the premise tail `[any-taint]`" stays |
| `MicroEdge.kt:23-25` A1 | a reversed micro edge can have a must target (S3), never a must premise |
| ap.md §6.5 ("the backward run has no `[any-taint]` premise") | C1 |
| ap.md §9.2 ("an `[any]` seed is demand-layer") | a seed is NORMAL ⇔ its literal is unary (K1–K4) |
| ap.md §8.7 R1, `RecordStore.kt:274-277` | §II.6 |
| ap.md §9.1 backward W6 | applies only to the MAY class and to `[any]` results not made by B1 |
| ap.md §8.5 F77 | H1: none; H1g, H2: one condition |
| Lean iteration theorems (`Backward.B_general`, `W6.iteration_general6`, `Handoff*`) | not proved again with B2 records; `Handoff.CrossK .any = False`, so `Handoff.demOfN` hands a must record off (= H2) |

| Hidden-change candidate | Rule | Evidence |
| --- | --- | --- |
| S-H1 strong-update exclusion: a backward `[any-taint]/E` gets an exclusion, `[any]` DEMAND does not (t1, t2); the forward demand can get narrower | B1 | base model: same facts (`W6.D6_same_shape`, `summaryDemand_iff`); refined model: not proved; shadow-compare the normalized pieces |
| S-H2 EXACT cleaner on a MUST leaf (`Clean.kt:187-192`) now runs backward | B1 | not modelled |
| S-H3 a must premise and an `[any]` premise at one path are separate keys | B1 | cost only |
| S-H4 MUST is relative to `positive(condition)` | B1 | the forward run uses it too |
| S-H5 B1 under-approximates MUST (`nd_overlap_suff`) | B1 | sound |
| S-H6 refined seeds narrow the forward demand | B3 | not proved; measure |
| S-H7 new record shape `(backward, [any-taint] premise)` | B2 | no dedup change for the existing shapes |
| S-H8 traces through a backward must view | B2 with H1 | check in the prototype |
| S-H9 the callee summaries of an ND `$` seed become DEMAND: no backward `$` record, selected rows (q2 type) instead of the exact view; forward run `n+1` analyses those callees under a `$` demand | B1 (K3) | results expected equal, not proved; more rows per backward run while the witness is DEMAND; measure |

### II.13 Proofs and model notes (backward)

> Where the backward claims are proved, the hypotheses, and where the model
> differs from the code.

| Claim | Lean |
| --- | --- |
| a NORMAL result of the backward transfer is a forward refined result | `BackMust.transferXB_normal` |
| K2 seed is NORMAL; bound: MUST added fact; must premise with NORMAL start; CURRENT: DEMAND start | `must_seed_normal`, `bindX_star_any`, `must_seed_bound`, `must_premise_normal`, `demand_seed_contrast`, `demand_premise_start` |
| each NORMAL backward summary with a non-zero premise is pair-exact (may) or end-exact (must) on `reverse(P)` | `DBX_edgeOK_nz`, `edge_exactBX_gen`, `no_zero_summaryX` |
| backward records are exact, also over a run sequence | `recsB_exact`, `recsB_must_end`, `recsB_pair`, `recsB_next`, `recsBSeq_ok` |
| in `P`: each location of the conclusion flows forward to some location of the premise | `backMust_forward`, `backPair_forward`, `backMust_forward_valid`, `backMust_forward_seq` |
| S3 is MUST for each target kind; S4, S7 are not MUST, sound MAY | `BackCond.rev_unary_source_must`, `rev_nd_source_not_must`, `rev_pass_any_not_must`, `rev_pass_may_sound` |
| the seed layer is the MUST status (B1, K3 included) | `BackCond.reqs_normal_must`, `reqs_nd_demand` |
| D1 counterexample and H1g guard | `BackMustView.Cex.cex_drop_forward_demand`, `guard_keeps_normal` |

Hypotheses of `DBX_edgeOK_nz`: those of `DRX_edgeOK` on `reverse(P)`, plus
`NoZeroIn` (= `NoZeroBack P`, I11 (c); necessary: `BExact.CexZeroBack`) and
`SeedsConcB` (necessary: `BExact.CexSeed`); record hypotheses only off the
zero base, discharged by `recsBSeq_ok`.

* The run-level model gives the forward `AnyField` target the meaning "each
  location", so its reversal is exact there and the theorems hold for each
  MAY class. The rule level proves that the MAY class is not MUST. Link
  (argued, not proved): a NORMAL backward fact never crosses a MAY-class
  edge.
* The must flag of a seed is an input of `BackMust`, and the seed layer is
  `!must` (rule `DBX.seed`). `BackCond.reqs` decides the flag on
  `positive(condition)` in DNF: unary NORMAL, ND DEMAND for each tail. So the
  model already has K3 DEMAND. The code has an NNF DAG.
* `BackND`: the base model has no ND sink; each literal is its own sink. The
  ND form of the backward contract is not proved. `refine_mono` keeps the
  meet exclusions; the code forgets them.
* Not modelled: S-H2, GROUP projection, end-fact triggers, statics.

## Gate and checklist

> The acceptance test of each rule, the withdrawal conditions and the state
> of the proposal against spec/proof-guide.md.

Gate per rule, alone, per project (OWASP, Stirling-PDF, Conductor,
ThingsBoard) and the module, jvm and rule suites: identical confirmed and
provisional results; wall time and peak memory not worse. Withdraw a rule
that fails. H1: withdraw also on one shadow case (§II.11). B3: withdraw also
if the capture makes peak memory worse.

```text
[x] Failure class and real trace        §II.1 (per-run counts not measured)
[ ] Ablation                            not done (spec only)
[ ] Native prototype                    not done (spec only)
[ ] Execution site and measured volume  sites: seeds per run, transfer per backward fact, records per barrier,
                                        replay per call offer, capture per completed combination; volumes not measured
[x] Semantic scope                      §II.12; D1 open
[x] Proof scope, model vs production    §I.10, §II.13
[x] Withdrawal condition                this section
[ ] WI classification                   none
[x] Proofs                              Notation, Part I, Part II
```

Blind spots: nothing ran natively; with H2, B1 and B2 remove no forward
row; the H1 risk is a reduction, not a measured case; S-H1, S-H2, S-H6,
S-H8, S-H9 and the capture heap cost are not measured.
