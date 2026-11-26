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
  run uses them today, the record reversal of both directions, and the two
  new forward steps.
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
| B1 MUST seeds | a requirement from a literal is NORMAL if and only if the literal alone fires the rule (a unary literal): unary `[any]` literals give `[any-taint]`, ND `$` literals give DEMAND | §II.2–§II.5 | **CHANGED** |
| B2 backward MUST records | a NORMAL backward summary with an `[any-taint]` premise or leaf is a record; the forward run reads it by §I.8 cases 3 and 4 | §II.6, §I.8 | **CHANGED** (backward R1), **NEW** (forward views) |
| B3 refined ND seeds | an ND `[any]` literal is seeded with its meets with the inputs that the forward run captured | §I.3, §II.10 | **CHANGED** (ND `[any]` seeds), **NEW** (capture) |
| D1 hand-off of backward MUST records | does a backward MUST record still give demand to the forward run? | §II.11 | **OPEN** |

**Lean.** [BackCondRules](lean/ApSpec/BackCondRules.lean) (`BackCond`),
[BackMustRun](lean/ApSpec/BackMustRun.lean) (`BackMust`),
[BackMustView](lean/ApSpec/BackMustView.lean) (`BackMustView`),
[BackRecordViews](lean/ApSpec/BackRecordViews.lean) (`BackView`),
[BackNDRefine](lean/ApSpec/BackNDRefine.lean) (`BackND`),
[BackCondExamples](lean/ApSpec/BackCondExamples.lean) (`BackCondEx`).
All constructive (`propext`, `Quot.sound` only).

**Examples.** Bases `x y z ret arg0 a b`, fields `f g h k`, marks `T U`.
`zero` is the zero fact: it holds at every reached node. An example id with ✓
(for example `e1 ✓`) is the Lean theorem `BackCondEx.ex_e1`: the executable
model computes the result shown, checked by `decide`.

## Notation

> Locations, facts, patterns, rule conditions, summary edges and demand
> edges. These are names only; Part I and Part II give the behaviour.

### N.1 Locations, facts and patterns

```text
location        base.path(mark)                a value: base variable, field path, concrete taint mark
fact            base.path.tail(mark)  in a layer
pattern         base.path.tail(mark)  with no layer: a literal, a premise, a demand pattern
  tail            $                  the location base.path only
                  */E                base.path·suffix for each suffix that E admits; correlated with the premise suffix (FLOW)
                  [any]              base.path·suffix for each suffix; MAY: covers the locations that can carry the mark
                  [any-taint]/E      base.path·suffix for each suffix that E admits; MUST: each covered location carries the mark
  mark            T                  a concrete mark
                  *                  abstract: the mark of the premise passes through
E               an exclusion: a set of fields;  admits(E, suffix) ⇔ suffix = [] ∨ first(suffix) ∉ E
                only the tails */E and [any-taint]/E have one
layer           NORMAL | DEMAND;   join: NORMAL ⊔ NORMAL = NORMAL, otherwise DEMAND

W6 (tail and layer of a fact):   [any] ⇒ DEMAND;   [any-taint] ⇒ NORMAL
  a step that puts an [any-taint] fact in DEMAND writes it as [any] and drops E

covered(fact)        = { base.(path·suffix)(mark2) | tail admits suffix ∧ mark admits mark2 }
                       $ admits only [];  */E and [any-taint]/E admit what E admits;  [any] admits each suffix;  * admits each mark
inside(fact1, fact2) ⇔ covered(fact1) ⊆ covered(fact2)
```

Placeholders in patterns and rules: `E`, `E1`, `E2` are exclusions; `P`, `Q`
are rule arguments (bases with paths); `T`, `T'`, `U` are marks; `A` is an
alternative of a condition.

| Item | Status |
| --- | --- |
| four tails: `Tail { EXACT, STAR, ANY, ANY_TAINT }` (`Facts.kt:7`) | **CURRENT** |
| W6 `[any]` ⇒ DEMAND: `Conclusion` check (`Reference.kt:12`) | **CURRENT** |
| W6 `[any-taint]` ⇒ NORMAL: a stored any-leaf takes its tail from the layer, NORMAL `ANY_TAINT`, DEMAND `ANY` (`Conclusions.kt:49,78`) | **CURRENT** |
| a demand pattern has no `[any-taint]` tail (W8 (d), `Demand.kt:41`, `RestrictedInitialPolicy.kt:38`) | **CURRENT** |
| Lean encoding: one kind `any` and the layer flag: `any` NORMAL is `[any-taint]`, `any` DEMAND is `[any]` (`AnyTaintEx.XFact`, `carriesB`) | model only |

So no fact is NORMAL `[any]`: the `[any-taint]` tail takes that place. The
Lean model encodes the two tails as one kind and the layer, which is why
older text defined `[any-taint]` as "a NORMAL `[any]`".

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
summary  = (direction, method, premise, conclusion, layer)
  direction           forward | backward
  program(forward)    = P;   program(backward) = reverse(P): entry and exit swapped, CFG edges reversed
  premise             a pattern at the entry of method in program(direction)
  conclusion          a fact at the exit of method in program(direction)
  must premise        ⇔ premise.tail = [any-taint]: emitted from a MUST added fact (§I.4)
written:  direction: premise → conclusion layer     (→must for a must premise)

flows(direction, method)(entryLocation, exitLocation):
  taint at entryLocation at the entry reaches exitLocation at the exit, in program(direction)
flows(backward, method)(entryLocation, exitLocation)  ⇔  flows(forward, method)(exitLocation, entryLocation)   [Reverse.flow_rev_iff_calls]

pairs(summary) = { (entryLocation, exitLocation) | entryLocation = premise.base.(premise.path·suffix)(mark) ∈ covered(premise),
                   exitLocation ∈ covered(conclusion) at conclusion.path·suffix2, with
                   suffix2 = [] for a $ conclusion, = suffix for a */E conclusion, any for an [any] or [any-taint] conclusion;
                   mark carried for a * conclusion, the conclusion mark otherwise }

a NORMAL summary is
  pair-exact  (premise not must):  pairs(summary) ⊆ flows(direction, method)
  end-exact   (must premise):      ∀ exitLocation ∈ covered(conclusion). ∃ entryLocation ∈ covered(premise).
                                     flows(direction, method)(entryLocation, exitLocation)
a DEMAND summary covers: every real flow from a covered premise location is in some summary
record           a NORMAL summary that the persistent record store keeps (rule R1: §I.5 forward, §II.6 backward)
```

### N.4 Demand edges

```text
demand edge of a method = (entryDemand, exitDemand)          ap.md names: D-c = entryDemand, D-p = exitDemand
  entryDemand  a pattern at the entry of the method in program(direction); from the conclusion of a summary of the previous run
  exitDemand   a pattern at the exit, or none;                              from the premise of that summary
  demand patterns have no layer and no [any-taint] tail; a restricted run analyses the method only for its demand edges
  how the hand-off builds them: §I.9
```

## Part I. Forward run

> The forward run propagates taint from the sources, checks the sinks and
> builds summaries. The proposal adds two forward steps: the capture of ND
> inputs (§I.3, B3) and the reading of backward MUST records (§I.8 cases 3,
> 4, B2). All other forward behaviour is **CURRENT** and is the reference for
> Part II.

### I.1 Forward facts

> What the tails and layers mean in the forward run. **CURRENT** (ap.md §4.2,
> W6).

```text
NORMAL fact        no access-path operation of its derivation over-approximated
[any-taint]/E(T)   NORMAL: every covered location carries T
[any](T)           DEMAND: the covered locations include the tainted ones
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
  { input | input satisfied literal in a COMPLETED combination (NORMAL or DEMAND) of the occurrence }
normal form (a pattern):   mark  := the concrete mark that the check matched   (a FLOW input: the mark of the literal)
                           */E   := [any-taint]/E                              (the same locations)
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
added       the fact that enters the callee by a binding b.* → b'.*, with its layer
MUST added  ⇔  added.tail = [any-taint]
emit(entryDemand, added)  =  (premise, startFact)  or  none
```

| entryDemand mark | added mark | premise | must premise | startFact |
| --- | --- | --- | --- | --- |
| `*` (abstract) | any | FLOW form of entryDemand: tail `$`→`$`, `[any]`→`*/{}`, `*/E`→`*/E`; mark `*` | no | the premise, NORMAL (identity) |
| `T` (concrete) | `T` | `meet(added, entryDemand)` | ⇔ MUST added ∧ premise tail `[any-taint]` | must premise: the premise, NORMAL; else by tail: `$` → NORMAL; `[any]`, `*/E` → `[any]` DEMAND |
| `T` (concrete) | other | none | — | — |

```text
meet(added, entryDemand),   demandPath = entryDemand.path,   demandTail = entryDemand.tail:
  added below   added.path = demandPath·suffix, suffix ≠ []    added                                         if demandTail admits suffix
  added at      added.path = demandPath                        demandPath with meetTail(added.tail, demandTail)
  added above   demandPath = added.path·suffix, suffix ≠ []    demandPath with meetTail(added.tail, demandTail)
                                                               if added.tail admits suffix
  otherwise none
```

| meetTail(added tail, demand tail) | demand `$` | demand `[any]` | demand `*/E2` |
| --- | --- | --- | --- |
| `$` | `$` | `$` | `$` |
| `[any]` | `$` | `[any]` | `*/E2` |
| `[any-taint]/E1` | `$` | `[any-taint]/E1` at the added path; `[any-taint]/∅` at a deeper demand path | no canonical case |

Contract: each common location with its mark is covered by the premise, the
added fact satisfies the premise, and the premise is inside entryDemand
(`AnyTaintExCov.emitX_contract`).

Code form (**CURRENT**): no summary premise has the `[any]` tail
(`RunSummaries.kt:58`). The code keys the may `[any]` premise as the
concrete-mark premise `*/{}(T)` (`RestrictedInitialPolicy.kt:34`), with the
same DEMAND start fact. ap.md and the Lean model write it as `[any](T)`.

Examples (forward, all **CURRENT**; the must rows e3, e5, e6 are **NEW** in the backward run, §II.5):

| Ex | entryDemand | added fact | premise, must premise | startFact | Case |
| --- | --- | --- | --- | --- | --- |
| e1 ✓ | `x.[any](T)` | `x.f.$(T)` NORMAL | `x.f.$(T)`, no | `x.f.$(T)` NORMAL | added below |
| e2 ✓ | `x.f.[any](T)` | `x.[any](T)` DEMAND | `x.f.[any](T)`, no | `x.f.[any](T)` DEMAND | added above |
| e3 ✓ | `x.f.[any](T)` | `x.[any-taint]/{g}(T)` NORMAL | `x.f.[any-taint](T)`, yes | `x.f.[any-taint](T)` NORMAL | above: `{g}` is not kept at the deeper path |
| e4 ✓ | `x.f.[any](T)` | `x.[any-taint]/{f}(T)` NORMAL | none | — | `{f}` rejects `f` |
| e5 ✓ | `x.[any](T)` | `x.[any-taint]/{g}(T)` NORMAL | `x.[any-taint]/{g}(T)`, yes | `x.[any-taint]/{g}(T)` NORMAL | added at |
| e6 ✓ | `x.$(T)` | `x.[any-taint]/{g}(T)` NORMAL | `x.$(T)`, no | `x.$(T)` NORMAL | `meetTail([any-taint], $) = $` |
| e7 ✓ | `x.[any](*)` | `x.[any-taint](T)` NORMAL | `x.*/{}(*)`, no (FLOW) | identity, NORMAL | abstract entryDemand (`Abs.emitW`) |
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
        ∨ ¬inside(premise, entryDemand)                          locations and marks
        ∨ ¬marksMeet(conclusion mark, exitDemand mark)           T and U meet ⇔ T = U;  * meets each mark
        ∨ conclusion.base ≠ exitDemand.base
  else  the summary with conclusion := cutConclusion(conclusion, exitDemand)      premise and layer kept
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
| r8 ✓ | `… → ret.[any-taint]/{h}(T)` NORMAL | exitDemand `ret.f.[any](T)` | `ret.f.[any-taint](T)` NORMAL | above, `[any]` demand |
| r9 ✓ | `… → ret.[any-taint]/{h}(T)` NORMAL | exitDemand `ret.h.[any](T)` | none | `{h}` rejects `h` |
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
inside(premise, added)       ⇔  covered(premise) ⊆ covered(added), marks too                      [AnyTaintEx.satX]
applicable(premise, added)   ⇔  covered(added) ⊆ covered(premise) ∧ (must premise ⇒ added.tail ∈ {[any], [any-taint]})   [Basic.applicable]
summary of this run (restricted piece):   used if inside(premise, added)
record (R4, later runs):                  used if inside(premise, added) ∨ applicable(premise, added)
result layer = added layer ⊔ conclusion layer
MUST rule:  must premise ∧ ¬inside(premise, added)  ⇒  result layer := DEMAND (an [any-taint] result becomes [any], W6)   [AnyTaintEx.recLayerX]
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

### I.8 Record reversal (read views, both directions)

> A record of one direction is read by the run of the other direction, end
> for end (ap.md §8.7 R2–R4). There are four cases. Cases 1 and 2 are
> forward records that the backward run reads (**CURRENT**). Cases 3 and 4
> are backward records that the forward run reads; they exist only with B1
> and B2 (**NEW**). The backward run uses this section for forward records
> (§II.9).

```text
record      direction: premise → conclusion,  NORMAL, one premise
reader      a fact of the other direction at the conclusion end of the record:
              a backward requirement at the forward exit reads the forward records of the method;
              a forward fact at the forward entry reads the backward records of the method
view        one view for each conclusion leaf; it swaps the two ends:
              viewPremise    = endPattern(conclusion leaf)
              viewConclusion = startResult(premise)

  endPattern(base.path.$(T))                 = base.path.$(T)
  endPattern(base.path.[any-taint]/E(T))     = base.path.*/E(T)                a field tail; the mark T stays concrete; E kept
  startResult(base.path.$(U))                = base.path.$(U)       NORMAL
  startResult(base.path.[any-taint]/E2(U))   = base.path.[any](U)   DEMAND     E2 forgotten (W6)

guard       both marks concrete; each end $ or [any-taint]; at least one end [any-taint]; a $ end has no exclusion
            other shapes ($ → $, a canonical * premise → */E): generic leaf reversal (ap.md §9.1), CURRENT
apply       to a reader fact r: used if inside(viewPremise, r) ∨ applicable(viewPremise, r) (R4)
            result = viewConclusion;  result layer = r layer ⊔ viewConclusion layer
            a $ viewConclusion does not take the suffix of r (ret.h.$ gives arg0.$, not arg0.h.$)
```

| Case | Record | Record meaning | View: viewPremise → viewConclusion | View meaning | Status | Lean |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `forward: arg.$(U) → ret.[any-taint]/E(T)` | pair-exact | `ret.*/E(T) → arg.$(U)` NORMAL | exact converse | **CURRENT** | `CurrentMustReverse.exact_converse` |
| 2 | `forward: arg.[any-taint]/E2(U) →must ret.[any-taint]/E(T)` | end-exact | `ret.*/E(T) → arg.[any](U)` DEMAND | sound, not exact | **CURRENT** | `CurrentMustReverse.must_any_converse_covers`, `must_application_demand`; `AnyTaintExact.CexRev.cex_rev` |
| 2' | `forward: arg.[any-taint]/E2(U) →must ret.f.$(T)` | end-exact | `ret.f.$(T) → arg.[any](U)` DEMAND | sound, not exact | **CURRENT** | `CurrentMustReverse.must_exact_converse_covers` |
| 3 | `backward: ret.[any-taint]/E2(T) →must arg.[any-taint]/E(U)` | end-exact on `reverse(P)` | `arg.*/E(U) → ret.[any](T)` DEMAND | sound, not exact | **NEW** (B2) | `BackMustView.viewF_demand`, `viewF_stays_demand`, `viewF_sound`, `Cex.viewF_not_exact` |
| 3' | `backward: ret.[any-taint]/E2(T) →must arg.$(U)` | end-exact on `reverse(P)` | `arg.$(U) → ret.[any](T)` DEMAND | sound, not exact | **NEW** (B2) | `BackMustView.viewF_sound` |
| 4 | `backward: ret.$(T) → arg.[any-taint]/E(U)` (row S3 with B1) | pair-exact on `reverse(P)` | `arg.*/E(U) → ret.$(T)` NORMAL | exact converse | **NEW** (B1, B2) | `BackView.backExactView_forward` |

Why the view meanings differ:

* A pair-exact record (cases 1, 4) relates each covered location of one end
  to each covered location of the other end by a real flow. The view relates
  the same pairs in the other order, so it is exact and stays NORMAL. Case 4
  composes `exact_converse` with `BackMust.backPair_forward`.
* An end-exact record (cases 2, 3) gives each conclusion location SOME source
  in the premise, not a known one. So the view result is the whole premise
  as `[any]`, DEMAND (`cex_rev`, `viewF_not_exact`).

The guard and the two conversions are the CURRENT rule for forward records
(ap.md §8.7 R3, `CurrentMustReverse.readView`). Applying the same rule to
backward records is **NEW**: today the code reads backward records only by
generic leaf reversal, because a backward record has no `[any-taint]` end
(`RecordStore.kt:274-277`). Model note: `BackMustView.viewF` tests overlap
instead of R4; overlap accepts more readers, and the view is sound for each.

Examples:

| Ex | Case | record | reader | Result | Status |
| --- | --- | --- | --- | --- | --- |
| v1 ✓ | 1 | `forward: arg0.$(T) → ret.[any-taint](T)` | backward `ret.h.$(T)` NORMAL | `arg0.$(T)` NORMAL (exact) | **CURRENT** |
| v2 ✓ | 2 | `forward: arg0.[any-taint](T) →must ret.g.[any-taint](T)` | backward `ret.g.h.$(T)` NORMAL | `arg0.[any](T)` DEMAND | **CURRENT** |
| v6 ✓ | 2 | `forward: arg0.[any-taint](T) →must ret.g.[any-taint]/{h}(T)` | backward `ret.g.h.$(T)` NORMAL | none: the view premise `ret.g.*/{h}(T)` excludes `h` | **CURRENT** |
| v3 ✓ | 2' | `forward: arg0.[any-taint](T) →must ret.f.$(T)` | backward `ret.f.$(T)` NORMAL | `arg0.[any](T)` DEMAND | **CURRENT** |
| v4 ✓ | 3 | `backward: ret.[any-taint](T) →must arg0.[any-taint](T)` | forward `arg0.h.$(T)` NORMAL | `ret.[any](T)` DEMAND | **NEW** (B2) |
| v5 ✓ | 3 | as v4 | forward `arg0.h.$(U)` NORMAL | none: the marks do not meet | **NEW** (B2) |
| v7 ✓ | 3' | `backward: ret.[any-taint](T) →must arg0.$(U)` | forward `arg0.$(U)` NORMAL | `ret.[any](T)` DEMAND | **NEW** (B2) |
| v8 ✓ | 4 | `backward: ret.$(T) → arg0.[any-taint](U)` | forward `arg0.g.$(U)` NORMAL | `ret.$(T)` NORMAL (exact) | **NEW** (B1, B2) |

### I.9 Hand-off: selection and demand edges

> At the end of a run, the selected summaries give the demand edges of the
> next run; the other summaries are records and give no demand (F77). A
> demand edge is a pair of patterns with no layer: the MUST or MAY status of
> the summary does not go to the next run. **CURRENT** (ap.md §8.5,
> `HandOff.kt`, `HandoffCompactor.kt:111-124`, `StaticGuidance.kt:50-57`).

```text
selected(summary)  ⇔  layer = DEMAND ∨ |premises| ≥ 2 ∨ (direction = backward ∧ premise = zero)
selected      ⇒  for each restricted piece premise → conclusion, each conclusion leaf and each premise member:
                   demand edge of the method in the next run
                   (entryDemand = pattern(conclusion leaf), exitDemand = pattern(premise member))
                 pattern:  [any-taint]/E → [any] (E dropped);  $, */E, [any] kept;  mark kept
not selected  ⇒  the summary is a record (R1): no demand edge; the next run reads the record (§I.8)
```

| Summary end | Its demand pattern | Selected summaries that have it | Status |
| --- | --- | --- | --- |
| conclusion `$`, `*/E` | the same | each selected kind | **CURRENT** |
| conclusion `[any]` (MAY) | entryDemand `[any]` | DEMAND summaries | **CURRENT** |
| conclusion `[any-taint]/E` (MUST) | entryDemand `[any]`, `E` dropped | NORMAL multi-premise summaries; backward zero-premise summaries (q3, with B1); backward must summaries (H2) | **CURRENT** rule; the backward rows are **NEW** with B1, B2 |
| premise `$`, `*/E` | exitDemand the same | each selected kind | **CURRENT** |
| premise `[any-taint]/E` (must) | exitDemand `[any]`, `E` dropped | DEMAND must summaries, for example `arg0.[any-taint] →must ret.[any]`; H2 | **CURRENT** |

So entryDemand MAY with exitDemand from a MUST premise is a normal case:
§II.7 gives the intersection rules for it.

| Ex | summary | selected | Demand edge for the next run (backward) | Status |
| --- | --- | --- | --- | --- |
| q1 | `forward: arg0.$(T) → ret.f.$(T)` NORMAL | no | none; the next run reads the record (case 1 type) | **CURRENT** |
| q2 | `forward: arg0.[any](T) → ret.[any](T)` DEMAND | yes | `(ret.[any](T), arg0.[any](T))` | **CURRENT** |
| q5 | `forward: arg0.[any-taint]/{g}(U) →must ret.[any](T)` DEMAND | yes | `(ret.[any](T), arg0.[any](U))`: `{g}` dropped | **CURRENT** |

### I.10 Proofs and model notes (forward)

> Where the forward claims are proved, and where the model differs from the
> code.

| Claim | Lean |
| --- | --- |
| NORMAL forward summaries are pair-exact or end-exact | `AnyTaintExExact.DRX_edgeOK` |
| emission contract | `AnyTaintExCov.emitX_contract`, `Abs.emitW_contract` |
| restriction keeps exactly the demanded pairs | `HandoffRestrict.restrictI_contract`, `restrictI_sub`, `restrictI_inter`; `CurrentDemand.restrictCertificate` |
| the MUST rule is necessary | `AnyTaintExact.CexApp.cex_app` |
| record reversal, cases 1–4 | §I.8 table |
| the examples | `BackCondEx` |

* `restrictConcX` keeps `[any-taint]/E` at the same path for a `*/E2`
  demand and gives `[any-taint]/∅` above it; ap.md gives `/(E ∪ E2)` and
  `/E2`. The model is wider and sound (r11).
* The Lean hand-off (`Handoff.demOfN`) uses patterns with no layer and no
  exclusion, so a must premise is an `[any]` exitDemand there too.
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
requirement  a fact at a node of reverse(P):
  NORMAL (MUST)   ∀ location ∈ covered(requirement): taint at location at the node ⇒ the seeded sink fires
  DEMAND (MAY)    the DEMAND requirements cover each location of a real route to the sink

layer of the requirement from a literal:
  CURRENT   NORMAL ⇔ literal.tail = $          seedFact (RunMethodLocalServices.kt:437-449) seeds NORMAL; W6 makes [any] DEMAND
  B1        NORMAL ⇔ literal is unary          [BackCond.reqs_normal_must, reqs_nd_demand]
            a unary [any] literal gives the [any-taint] tail (W6)
```

| Literal | CURRENT requirement | B1 requirement | Status |
| --- | --- | --- | --- |
| unary `P.$(T)` | `P.$(T)` NORMAL | `P.$(T)` NORMAL | **CURRENT** |
| unary `P.[any](T)` | `P.[any](T)` DEMAND | `P.[any-taint](T)` NORMAL | **CHANGED** |
| ND `P.$(T)` | `P.$(T)` NORMAL (not MUST: breaks the meaning) | `P.$(T)` DEMAND | **CHANGED** |
| ND `P.[any](T)` | `P.[any](T)` DEMAND | refined seeds, DEMAND (B3) | **CHANGED** (B3) |

With B1, a CURRENT ND `$` seed would make false MUST facts. Example: the
reversed source rule S3 turns `P.$(T)` NORMAL into `Q.[any-taint](T')`.

### II.3 Sink seeds

> The seeds of each rule literal at a DEMAND witness. The last column is
> what the seed reads from forward run `n−1`.

| # | Rule condition | Seed | Status | Input from forward run `n−1` |
| --- | --- | --- | --- | --- |
| K1 | `ContainsMark(P, T)`, unary | `P.$(T)` NORMAL | **CURRENT** | DEMAND witness (method, statement, occurrence) |
| K2 | `ContainsMarkOnAnyField(P, T)`, unary | `P.[any-taint](T)` NORMAL, exclusion `∅` | **CHANGED**: CURRENT `P.[any](T)` DEMAND | DEMAND witness |
| K3 | `ContainsMark(P, T)`, ND | `P.$(T)` DEMAND | **CHANGED**: CURRENT `P.$(T)` NORMAL | DEMAND witness (refinement is the identity) |
| K4 | `ContainsMarkOnAnyField(P, T)`, ND | `refinedSeeds(literal)` DEMAND (§II.10) | **CHANGED**: CURRENT `P.[any](T)` DEMAND | DEMAND witness and `captured(literal)` (§I.3) |
| K5 | a literal that is unary and ND | as K1 or K2 | as K1 or K2 | DEMAND witness |
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
| S3 | conditional source, unary `ContainsMarkOnAnyField(Q, T')` | `Q.[any-taint](T')` NORMAL if targetLayer is NORMAL; `Q.[any](T')` DEMAND otherwise | **CHANGED**: CURRENT `Q.[any](T')` DEMAND | none |
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
> ap.md §9.2). Today no backward added fact has the `[any-taint]` tail (W8
> (d)), so the must rows of §I.4 do not occur; with B1 they do.

entryDemand: from the demand edge that forward run `n−1` handed off for the callee (§I.9).

| # | requirement | entryDemand | premise, must premise | startFact | callee summary | Status |
| --- | --- | --- | --- | --- | --- | --- |
| C1 | `x.[any-taint]/E(T)` NORMAL | concrete `x.[any](T)` | `x.[any-taint]/E(T)`, yes (e5) | NORMAL | end-exact; a record (B2); hand-off: D1 | **NEW**: CURRENT requirement `x.[any](T)` DEMAND → C4 |
| C2 | `x.[any-taint]/E(T)` NORMAL | concrete `x.$(T)` | `x.$(T)`, no (e6) | NORMAL | pair-exact record; caller results NORMAL | **CHANGED**: CURRENT same summary, caller results DEMAND |
| C3 | `x.[any-taint]/E(T)` NORMAL | abstract `x.[any](*)` | `x.*/{}(*)`, no (e7) | identity, NORMAL | pair-exact FLOW record; caller results NORMAL | **CHANGED**: CURRENT caller results DEMAND |
| C4 | `x.[any](T)` DEMAND | concrete `x.[any](T)` | may `[any]` premise (e2 type) | DEMAND | DEMAND, selected | **CURRENT** |
| C5 | `x.$(T)` NORMAL | concrete | `x.$(T)`, no (e1 type) | NORMAL | pair-exact record | **CURRENT** |

The results return to the caller by §II.8 (backward summaries and records)
and §II.9 (forward records).

### II.6 Backward summaries and records (B2)

> Which backward summaries the record store keeps. B2 adds the summaries
> with an `[any-taint]` premise or leaf. **CHANGED** (ap.md §8.7 R1,
> `RecordStore.kt:274-277`).

```text
record(backward summary):
  CURRENT   layer = NORMAL ∧ one premise ∧ premise ≠ zero ∧ premise.tail ≠ [any-taint] ∧ no [any-taint] leaf
  B2        layer = NORMAL ∧ one premise ∧ premise ≠ zero
```

A backward MUST record is end-exact on `reverse(P)` and not pair-exact
(`BackMust.recsB_must_end`, `CexMustPair.cex_must_pair`). A backward record
whose premise is not must is pair-exact, also with `[any-taint]` leaves
(`BackMust.recsB_pair`). A zero-premise backward summary is never a record:
a seed relates `zero` to each seed location, which is not a flow.

| Ex | method | summary | Meaning | Record | Status |
| --- | --- | --- | --- | --- | --- |
| m4 | identity `M(arg0)` | `backward: arg0.[any-taint](T) →must arg0.[any-taint](T)` NORMAL | end-exact (the source of `arg0.f` is `arg0.f`); `(arg0.f, arg0.g)` is a pair and no flow: not pair-exact | B2: yes (§I.8 case 3) | **NEW**: CURRENT no |
| m6 | `ret = source(T) if ContainsMarkOnAnyField(arg0, U)` | `backward: ret.$(T) → arg0.[any-taint](U)` NORMAL | pair-exact: each `arg0.suffix(U)` flows to `ret(T)` | B2: yes (§I.8 case 4) | **NEW**: CURRENT the leaf is `[any]` DEMAND, no record |
| m5 | `sink(arg0)` in `M` | `backward: zero → arg0.[any-taint](T)` NORMAL | a seed path, not a flow | no | **CURRENT** rule (the `[any-taint]` seed is B1) |

### II.7 Restriction in the backward run

> The backward run cuts its summaries by the demand edges of §I.9 with the
> operation of §I.6. A demand edge has no layer, so it does not decide MUST
> or MAY: the backward facts do (B1). **CURRENT** for may summaries; the
> `[any-taint]` rows are **NEW** (B1, B2).

| Ex | summary | demand edge | restrict | Status |
| --- | --- | --- | --- | --- |
| r12 ✓ | `backward: ret.[any-taint](T) →must arg0.[any-taint](T)` NORMAL | `(ret.[any](T), arg0.h.$(T))` | `arg0.h.$(T)` NORMAL | **NEW** (B1, B2) |

**Case: entryDemand from a MAY conclusion, exitDemand from a MUST premise.**
Forward run `n−1` has the DEMAND summary q5:

```text
forward:  arg0.[any-taint]/{g}(U) →must ret.[any](T)   DEMAND      selected (§I.9)
demand edge in backward run n:   entryDemand = ret.[any](T)     from the MAY conclusion
                                 exitDemand  = arg0.[any](U)    from the MUST premise; {g} dropped
```

| Ex | Side | backward fact | Result | Rule | Status |
| --- | --- | --- | --- | --- | --- |
| dm1 ✓ | entry: emission (§I.4) | requirement `ret.f.$(T)` NORMAL | premise `ret.f.$(T)`, start NORMAL | added below `[any]` | **CURRENT** |
| — | entry | requirement `ret.[any](T)` DEMAND | may `[any]` premise, start DEMAND | e2 type | **CURRENT** |
| dm2 ✓ | entry | requirement `ret.[any-taint]/{h}(T)` NORMAL | must premise `ret.[any-taint]/{h}(T)`, start NORMAL | added at `[any]`, MUST added fact | **NEW** (B1) |
| dm3 ✓ | exit: restriction (§I.6) | conclusion `arg0.g.$(U)` NORMAL | `arg0.g.$(U)` NORMAL | below `[any]`: kept, although the forward premise excluded `g` | **CURRENT** |
| dm4 ✓ | exit | conclusion `arg0.[any-taint]/{h}(U)` NORMAL | `arg0.[any-taint]/{h}(U)` NORMAL | at, `[any]` demand keeps `{h}` | **NEW** (B1) |
| dm5 ✓ | exit | conclusion `arg0.g.$(T)` NORMAL | none | the marks do not meet | **CURRENT** |
| dm6 ✓ | exit, with exitDemand `arg0.*/{g}(U)` | conclusion `arg0.g.$(U)` NORMAL | none | the exclusion kept | not proposed |

* The MAY entryDemand does not make a MUST requirement MAY (dm2), and the MUST
  exitDemand does not make a backward conclusion MUST (dm3). Only the
  backward facts and the rules of §I.7 decide the layer.
* The hand-off drops `{g}`, so the cut keeps more pairs than the exact
  intersection (dm3). This is sound. Keeping the exclusion (dm6) is narrower;
  it is not proposed: it can remove demand, a result change outside B1–B3.
* The opposite case, entryDemand from a MUST conclusion: a backward
  zero-premise summary `zero → arg0.[any-taint](T)` (q3) gives forward run
  `n+1` the entryDemand `arg0.[any](T)`. A forward MUST added fact
  `arg0.[any-taint](T)` then gets a must premise (e5). **CURRENT** rule.

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

> A requirement at the forward exit of a method reads the forward records
> of that method: §I.8 cases 1, 2 and 2' (examples v1, v2, v3, v6).
> **CURRENT**.

### II.10 ND refinement (B3)

> An ND `[any]` literal is seeded with its meets with the captured inputs
> of forward run `n−1`, not with the whole literal. **NEW**.

```text
refinedSeeds(literal) =
  { meet(input, literal) | input ∈ captured(literal) } minus none     if captured(literal) ≠ ∅
  { literal }                                                        if captured(literal) = ∅   (fallback)
meet: the concrete row of §I.4
each seed DEMAND (W6: an [any] or [any-taint] meet becomes [any], its exclusion forgotten)
a $ literal: meet(input, literal) = literal (no change)
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
| n2 ✓ | 1: `b.g.[any-taint]/{k}(U)` | `a.$(T)` (fallback), `b.g.[any](U)` DEMAND | the code forgets `{k}`; the model keeps it | **NEW** |
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
          ⇒ run n+1 does not analyse the callee again; it reads only the view of §I.8 case 3, which is DEMAND
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
the backward run, which confirms nothing; a record with a `$` premise has an
exact view (cases 1, 4).

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
| q3 | `backward: zero → arg0.[any-taint](T)` NORMAL | yes | demand edge `(arg0.[any](T), zero)` | **CURRENT** rule |
| q4 | `backward: ret.[any-taint](T) →must arg0.[any-taint](T)` NORMAL | F77: no | H1: no callee demand, only v4; H2: demand edge `(arg0.[any](T), ret.[any](T))` | **OPEN** |

### II.12 Semantic scope

> What the proposal changes, what it keeps, which documented invariants
> change, and the changes that are not yet proved or measured.

| Change | Rows | Status |
| --- | --- | --- |
| unary `[any]` sink seed: `[any]` DEMAND → `[any-taint]` NORMAL | K2 | **CHANGED** |
| ND `$` sink seed: NORMAL → DEMAND (user correction, 26 Nov) | K3 | **CHANGED** |
| reversed unary `[any]` source literal: `[any]` DEMAND → `[any-taint]` in targetLayer | S3 | **CHANGED** |
| caller results through C2/C3 records: DEMAND → NORMAL | C2, C3 | **CHANGED** |
| backward MUST added fact, must premise, NORMAL start | C1 | **NEW** |
| backward records with an `[any-taint]` premise or leaf; R4 and the MUST rule; forward views | §II.6, §II.8, §I.8 cases 3, 4 | **NEW** |
| ND `[any]` seeds and reversed ND `[any]` literals refined; capture | K4, S5, §II.10, §I.3 | **NEW** |
| hand-off of a backward MUST record | §II.11 | **OPEN** |

Unchanged (**CURRENT**): the forward run except §I.3 and §I.8 cases 3, 4
(transfer, sink check, layers, records, views of forward records,
confirmation, traces); the four tails and W6; S4, S5 layer, S7; unary `$`
seeds (K1); zero rows; source hits; C4, C5; the operations of §I.4, §I.6,
§I.7; the demand patterns of §I.9; field limits and FL+1 caps; confirmed
and provisional results (the gate).

| Documented invariant | Change |
| --- | --- |
| interpreter.md I11 (f), I14 ("the backward run has no `[any-taint]`"), §4.9 | K2, S3; "no micro edge has the premise tail `[any-taint]`" stays |
| `MicroEdge.kt:23-25` A1 | a reversed micro edge can have a must target (S3), never a must premise |
| ap.md §6.5 ("the backward run has no `[any-taint]` premise") | C1 |
| ap.md §9.2 ("an `[any]` seed is demand-layer") | a seed is NORMAL ⇔ its literal is unary (K1–K4) |
| ap.md §8.7 R1, `RecordStore.kt:274-277` | §II.6 |
| ap.md §8.7 R3 (the special view is for forward records) | also backward records: §I.8 cases 3, 4 |
| ap.md §9.1 backward W6 | applies only to the MAY class and to `[any]` results not made by B1 |
| ap.md §8.5 F77 | H1: none; H1g, H2: one condition |
| Lean iteration theorems (`Backward.B_general`, `W6.iteration_general6`, `Handoff*`) | not proved again with B2 records; `Handoff.CrossK .any = False`, so `Handoff.demOfN` hands a must record off (= H2) |

| Hidden-change candidate | Rule | Evidence |
| --- | --- | --- |
| S-H1 strong-update exclusion: a backward `[any-taint]/E` gets an exclusion, `[any]` DEMAND does not (t1, t2); the forward demand can get narrower | B1 | base model: same facts (`W6.D6_same_shape`, `summaryDemand_iff`); refined model: not proved; shadow-compare the normalized pieces |
| S-H2 EXACT cleaner on a MUST leaf (`Clean.kt:187-192`) now runs backward | B1 | not modelled |
| S-H3 a must premise and a may `[any]` premise at one path are separate keys | B1 | cost only |
| S-H4 MUST is relative to `positive(condition)` | B1 | the forward run uses it too |
| S-H5 B1 under-approximates MUST (`nd_overlap_suff`) | B1 | sound |
| S-H6 refined seeds narrow the forward demand | B3 | not proved; measure |
| S-H7 new record shapes `(backward, [any-taint] premise or leaf)` | B2 | no dedup change for the existing shapes |
| S-H8 traces through a backward record view (cases 3, 4) | B2 | case 4 is exact; case 3 only with H1; check in the prototype |
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
| in `P`: each location of the conclusion flows forward to some location of the premise (must), each pair is a forward flow (may) | `backMust_forward`, `backPair_forward`, `backMust_forward_valid`, `backMust_forward_seq` |
| §I.8 case 4: the forward view is exact | `BackView.backExactView_forward` |
| S3 is MUST for each target kind; S4, S7 are not MUST, sound MAY | `BackCond.rev_unary_source_must`, `rev_nd_source_not_must`, `rev_pass_any_not_must`, `rev_pass_may_sound` |
| the seed layer is the MUST status (B1, K3 included) | `BackCond.reqs_normal_must`, `reqs_nd_demand` |
| D1 counterexample and H1g guard | `BackMustView.Cex.cex_drop_forward_demand`, `guard_keeps_normal` |

Hypotheses of `DBX_edgeOK_nz` and `backExactView_forward`: those of
`DRX_edgeOK` on `reverse(P)`, plus `NoZeroIn` (= `NoZeroBack P`, I11 (c);
necessary: `BExact.CexZeroBack`) and `SeedsConcB` (necessary:
`BExact.CexSeed`); record hypotheses only off the zero base, discharged by
`recsBSeq_ok`.

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
