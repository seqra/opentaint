# Backward condition progress: MUST requirements, field quantifiers and refined MAY seeds

26 November 2026, branch `saloed/bidirectional`. **Spec and proofs only**
(user decision): no ablation, no prototype, no measurement, no WI rule.

## Overview

> The backward run seeds requirements from the rule conditions of provisional
> findings. Today the layer of a seed depends only on its tail. So an `[any]`
> requirement is always DEMAND, the next forward run gets it again, and the
> demand rows of its method do not go to zero (§II.1). This spec gives the
> rules that let the backward run progress, and their proofs.

**Parts.**

* [Notation](#notation): the names that both parts use, the implication
  between ends and the meaning of a summary edge. No run behaviour.
* [Part I, forward run](#part-i-forward-run): the operations as the forward
  run uses them, the summary application of both runs, and the new forward
  steps.
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
| F field kinds | the CURRENT `[any-taint]` tail has two names: `[all-fields]` in the forward run (every covered location carries the mark) and `[any-field]` in the backward run (taint at any covered location fires the sink). Both act like `[any-taint]` in transfer, emission and restriction | §N.1 | **CURRENT** (names only) |
| B1 MUST seeds | a requirement from a literal is NORMAL if and only if the literal alone fires the rule (a unary literal): unary `[any]` literals give `[any-field]`, ND `$` literals give DEMAND | §II.2–§II.5 | **CHANGED** |
| B2 backward MUST records | a NORMAL backward summary with a field premise or a field leaf is a record | §II.6 | **CHANGED** |
| B3 refined ND seeds | an ND `[any]` literal is seeded with its meets with the inputs that the forward run captured | §I.3, §II.10 | **CHANGED** (ND `[any]` seeds), **NEW** (capture) |
| B4 application by implication | a summary edge gives a NORMAL result if and only if the reader and the edge end at the reader imply each other in the direction of the run (§N.5); the result keeps the kind of the other end, also for a record of the other direction | §I.7, §I.8 | **CHANGED** (forward must records read backward), **NEW** |
| D1 hand-off of backward MUST records | does a backward MUST record still give demand to the forward run? | §II.11 | **OPEN** |
| D2 transfer of foreign kinds | B4 makes forward `[any-field]` facts and backward `[all-fields]` requirements. They cannot act like `[any-taint]` in transfer (a strong update or a narrower demand breaks them) | §I.9, §II.12 | **OPEN** |

**Lean.** [FieldQuant](lean/ApSpec/FieldQuant.lean) (`FieldQuant`),
[BackCondRules](lean/ApSpec/BackCondRules.lean) (`BackCond`),
[BackMustRun](lean/ApSpec/BackMustRun.lean) (`BackMust`),
[BackMustView](lean/ApSpec/BackMustView.lean) (`BackMustView`),
[BackRecordViews](lean/ApSpec/BackRecordViews.lean) (`BackView`),
[BackNDRefine](lean/ApSpec/BackNDRefine.lean) (`BackND`),
[BackCondExamples](lean/ApSpec/BackCondExamples.lean) (`BackCondEx`).
All constructive (`propext`, `Quot.sound` only; `FieldQuant` uses no axiom).

**Examples.** Bases `x y z ret arg0 a b`, fields `f g h k`, marks `T U`.
`zero` is the zero fact: it holds at every reached node. An example id with ✓
(for example `e1 ✓`) is the Lean theorem `BackCondEx.ex_e1`: the executable
model computes the result shown, checked by `decide`. In §I.8 the ✓ checks
the CURRENT column; the B4 column follows from the cited theorems.

## Notation

> Locations, ends, facts, rule conditions, summary edges, demand edges, the
> implication between ends and the meaning of an edge. Part I and Part II
> give the run behaviour.

### N.1 Locations, ends and facts

> A pattern covers a set of locations. Its tail tells how it reads the set:
> one location, all of them, or one of them. The two field tails are the
> CURRENT `[any-taint]` tail, read by the forward run and by the backward
> run.

```text
location        base.path(mark)                 a value: base variable, field path, concrete taint mark
pattern         base.path.tail(mark)            a fact, a requirement, a literal, a premise, a conclusion
  tail            $                  the location base.path                                 end: $ location
                  [all-fields]/E     base.path·suffix for each suffix that E admits, ALL    end: [all-fields] set
                  [any-field]/E      base.path·suffix for each suffix that E admits, ONE    end: [any-field] set
                  */E                FLOW: base.path·suffix, correlated with the premise suffix (abstract mark)
                  [any]              MAY: covers the locations that can carry the mark (DEMAND only)
  mark            T                  a concrete mark
                  *                  abstract: the mark of the premise passes through (FLOW)
E               an exclusion: a set of fields;  admits(E, suffix) ⇔ suffix = [] ∨ first(suffix) ∉ E
layer           NORMAL | DEMAND;   join: NORMAL ⊔ NORMAL = NORMAL, otherwise DEMAND
covered(pattern) the location set;  inside(pattern1, pattern2) ⇔ covered(pattern1) ⊆ covered(pattern2)

holds(σ, end)   σ is a taint state: the set of tainted locations at a node
  holds(σ, $ ℓ)               ⇔  ℓ ∈ σ
  holds(σ, [all-fields] S)    ⇔  S ⊆ σ
  holds(σ, [any-field] S)     ⇔  S ∩ σ ≠ ∅

NORMAL forward fact e at node n          holds(taint at n, e)                                   a claim
NORMAL backward requirement e at node n  ∀ σ: holds(σ, e) at n ⇒ the seeded sink fires         a sufficient condition

native kinds    forward [all-fields],  backward [any-field]          one universal statement over the covered set
foreign kinds   forward [any-field],   backward [all-fields]         made only by B4 (§I.7, §I.8); transfer: D2
W6              [any] ⇒ DEMAND;  [all-fields], [any-field] ⇒ NORMAL
                a step that puts a field-tail fact in DEMAND writes it as [any] and drops E
```

Placeholders in patterns and rules: `E`, `E1`, `E2` are exclusions; `P`, `Q`
are rule arguments (bases with paths); `T`, `T'`, `U` are marks; `A` is an
alternative of a condition; `S`, `X`, `Y`, `R` are location sets.

| Item | Status |
| --- | --- |
| the tails `Tail { EXACT, STAR, ANY, ANY_TAINT }` (`Facts.kt:7`); `ANY_TAINT` is the native field tail of the run | **CURRENT** (`[all-fields]`, `[any-field]` are names) |
| a record keeps its direction, so the other run knows how to read its `ANY_TAINT` ends | **CURRENT** |
| a foreign kind in a run: a new code tail or flag | **NEW** (B4, D2) |
| W6 `[any]` ⇒ DEMAND: `Conclusion` check (`Reference.kt:12`) | **CURRENT** |
| W6 field tail ⇒ NORMAL: a stored any-leaf takes its tail from the layer, NORMAL `ANY_TAINT`, DEMAND `ANY` (`Conclusions.kt:49,78`) | **CURRENT** |
| a demand pattern has no field tail (W8 (d), `Demand.kt:41`, `RestrictedInitialPolicy.kt:38`) | **CURRENT** |
| Lean: the run model encodes the native field tail as kind `any` with the NORMAL flag (`AnyTaintEx.XFact`, `carriesB`); `FieldQuant.End` gives the quantifier reading | model only |

Why both native kinds act alike: each is a universal statement over the
covered set, "every location carries the mark" or "every location is
sufficient". Transfer, emission and restriction narrow the set (an exclusion
grows, a demand cuts a deeper path), and a universal statement survives
narrowing (`FieldQuant.all_sub`, `all_kill`, `req_any_sub`). The kinds differ
when an edge carries the statement to the other end of a method (§N.5, §I.7).

### N.2 Rule conditions

> Literals, alternatives and the classification of a literal as unary or ND.
> A literal is an end: `$` or `[any-field]`.

```text
literal              a pattern of a condition:  ContainsMark(P, T) is P.$(T) (end $);
                     ContainsMarkOnAnyField(P, T) is P.[any](T) (end [any-field] on P and its fields: some location carries T)
positive(condition)  the condition with each negated literal replaced by true, in DNF:
                     a set of alternatives, each alternative a set of literals
taintedLocations     a set of locations: the taint at the rule
fires(condition, taintedLocations)  ⇔  ∃ alternative ∈ positive(condition). ∀ literal ∈ alternative.
                                         holds(taintedLocations, literal)
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
| c1 ✓ | `ContainsMarkOnAnyField(ret, T)` (unary) | `{ret.f(T)}` | yes | `ret.f(T)` is sufficient: seed `ret.[any-field](T)` NORMAL (B1, **CHANGED**) |
| c2 ✓ | `a.$(T) ∧ b.[any](U)` (ND) | `{b.f(U)}` | no | `b.f(U)` is not sufficient: both seeds DEMAND (B1, **CHANGED** for `a.$(T)`) |
| c3 ✓ | as c2 | `{a(T), b.f(U)}` | yes | `b.f(U)` is on a route: the DEMAND seeds must cover it |

### N.3 Summary edges

> A summary relates a premise at the entry of a method to a conclusion at
> its exit, in the program of its direction.

```text
summary  = (direction, method, premise, conclusion, layer)
  direction           forward | backward
  program(forward)    = P;   program(backward) = reverse(P): entry and exit swapped, CFG edges reversed
  premise             a pattern at the entry of method in program(direction)
  conclusion          a fact at the exit of method in program(direction)
  must premise        ⇔ premise.tail is a field tail: emitted from a field added fact (§I.4)
written:  direction: premise → conclusion layer     (→must for a must premise)

flows(direction, method)(entryLocation, exitLocation):
  taint at entryLocation at the entry reaches exitLocation at the exit, in program(direction)
flows(backward, method)(entryLocation, exitLocation)  ⇔  flows(forward, method)(exitLocation, entryLocation)   [Reverse.flow_rev_iff_calls]

a NORMAL summary with concrete marks   is valid (§N.6)
  pair-exact   shapes s1, s2, s7: each pair of an entry location and an exit location is a flow
  end-exact    forward s4, s5: each exit location has a source in the premise;
               backward s3, s9: each forward-entry location reaches some location of the premise
a NORMAL FLOW summary (*/E, mark *)    pairs(summary) ⊆ flows(direction, method)                 CURRENT, outside §N.6
  pairs: the premise location base.(path·suffix)(mark) with the conclusion location at conclusion.path·suffix, same mark
a DEMAND summary covers: every real flow from a covered premise location is in some summary
record           a NORMAL summary that the persistent record store keeps (rule R1: §I.5 forward, §II.6 backward)
```

### N.4 Demand edges

```text
demand edge of a method = (entryDemand, exitDemand)          ap.md names: D-c = entryDemand, D-p = exitDemand
  entryDemand  a pattern at the entry of the method in program(direction); from the conclusion of a summary of the previous run
  exitDemand   a pattern at the exit, or none;                              from the premise of that summary
  demand patterns have no layer and no field tail; a restricted run analyses the method only for its demand edges
  how the hand-off builds them: §I.10
```

### N.5 Implication between ends

> One end implies another when every taint state that makes the first hold
> makes the second hold. The application rule (§I.7), the sink check (§I.2)
> and the source hit (§II.12) use this table. Each cell is exact (an "if and
> only if").

```text
impl(end1, end2)  ⇔  ∀ σ: holds(σ, end1) ⇒ holds(σ, end2)
```

| end1 \ end2 | `$ ℓ2` | `[all-fields] S2` | `[any-field] S2` |
| --- | --- | --- | --- |
| `$ ℓ1` | `ℓ1 = ℓ2` | never | `ℓ1 ∈ S2` |
| `[all-fields] S1` | `ℓ2 ∈ S1` | `S2 ⊆ S1`: inside(end2, end1) | `S1 ∩ S2 ≠ ∅`: overlap |
| `[any-field] S1` | never | never | `S1 ⊆ S2`: inside(end1, end2) |

"never": a field tail covers two different locations or more
(`FieldQuant.not_impl_one_all`, `not_impl_any_one`, `not_impl_any_all`).
Cells: `impl_one`, `impl_all_one`, `impl_all_all`, `impl_all_any`,
`impl_any_one`, `impl_any_all`, `impl_any_any`. The marks are part of the
locations, so the cells compare marks too. Code: inside is `satX`/`insideExB`,
overlap is `overlapB` with exclusions (`AnyTaintEx.overlapX`), **CURRENT**.

### N.6 Edge meaning

> A summary edge has one meaning for both directions: the end at the forward
> entry of the method gives the end at the forward exit. The direction only
> tells which end is the premise. There are nine shapes.

```text
entryEnd   the end of the summary at the forward entry of the method;   exitEnd   the end at the forward exit
  forward summary   premise → conclusion:   entryEnd = premise,      exitEnd = conclusion
  backward summary  premise → conclusion:   entryEnd = conclusion,   exitEnd = premise
post(σ)          = { r | ∃ a ∈ σ: flows(forward, method)(a, r) }                       taint at the exit from σ at the entry
valid(summary)   ⇔  ∀ σ: holds(σ, entryEnd) ⇒ holds(post(σ), exitEnd)
```

| Shape | entryEnd | exitEnd | valid ⇔ | forward form | backward form | NORMAL from native facts | Lean |
| --- | --- | --- | --- | --- | --- | --- | --- |
| s1 | `$ a` | `$ r` | `flows(a, r)` | `arg.$ → ret.$` | `ret.$ → arg.$` | both runs, **CURRENT** | `valid_one` |
| s2 | `$ a` | `[all-fields] X` | `∀ r ∈ X: flows(a, r)` | `arg.$ → ret.[all-fields]` | `ret.[all-fields] →must arg.$` | forward, **CURRENT** | `valid_one`, `BackView.fwd_pair_valid` |
| s3 | `$ a` | `[any-field] X` | `∃ r ∈ X: flows(a, r)` | `arg.$ → ret.[any-field]` | `ret.[any-field] →must arg.$` | backward, **NEW** (B1, B2) | `valid_one`, `BackView.bwd_must_valid` |
| s4 | `[all-fields] Y` | `$ r` | `∃ a ∈ Y: flows(a, r)` | `arg.[all-fields] →must ret.$` | `ret.$ → arg.[all-fields]` | forward, **CURRENT** | `valid_all`, `BackView.fwd_must_valid` |
| s5 | `[all-fields] Y` | `[all-fields] X` | `∀ r ∈ X ∃ a ∈ Y: flows(a, r)` | `arg.[all-fields] →must ret.[all-fields]` | `ret.[all-fields] →must arg.[all-fields]` | forward, **CURRENT** | `valid_all_all`, `BackView.fwd_must_valid` |
| s6 | `[all-fields] Y` | `[any-field] X` | `∃ a ∈ Y ∃ r ∈ X: flows(a, r)` | `arg.[all-fields] →must ret.[any-field]` | `ret.[any-field] →must arg.[all-fields]` | none: only from a foreign fact (D2) | `valid_all_any` |
| s7 | `[any-field] Y` | `$ r` | `∀ a ∈ Y: flows(a, r)` | `arg.[any-field] →must ret.$` | `ret.$ → arg.[any-field]` | backward, **NEW** (B1, B2) | `valid_any`, `BackView.bwd_pair_valid` |
| s8 | `[any-field] Y` | `[all-fields] X` | `∀ a ∈ Y ∀ r ∈ X: flows(a, r)` | `arg.[any-field] →must ret.[all-fields]` | `ret.[all-fields] →must arg.[any-field]` | none: only from a foreign fact (D2) | `valid_any_all` |
| s9 | `[any-field] Y` | `[any-field] X` | `∀ a ∈ Y ∃ r ∈ X: flows(a, r)` | `arg.[any-field] →must ret.[any-field]` | `ret.[any-field] →must arg.[any-field]` | backward, **NEW** (B1, B2) | `valid_any_any`, `BackView.bwd_must_valid` |

A forward run makes the forward forms of s3, s7, s9 and a backward run makes
the backward forms of s2, s4, s5 only from a foreign fact (D2). The CURRENT
words: pair-exact is s1, s2, s7; end-exact is s4, s5 (forward) and s3, s9
(backward, "end-exact on `reverse(P)`").

## Part I. Forward run

> The forward run propagates taint from the sources, checks the sinks and
> builds summaries. The proposal adds the capture of ND inputs (§I.3, B3),
> the application by implication (§I.7, §I.8, B4) and the foreign forward
> facts (§I.9, D2). The other forward behaviour is **CURRENT** and is the
> reference for Part II.

### I.1 Forward facts

> What the tails and layers mean in the forward run. **CURRENT** (ap.md §4.2,
> W6) except the foreign kind.

```text
NORMAL fact         no access-path operation of its derivation over-approximated
[all-fields]/E(T)   NORMAL: every covered location carries T                       native, CURRENT ([any-taint])
[any-field]/E(T)    NORMAL: some covered location carries T                        foreign, NEW (B4); transfer: D2
[any](T)            DEMAND: the covered locations include the tainted ones
DEMAND fact         some operation over-approximated; the fact covers the real taint
```

### I.2 Sink check and DEMAND witnesses

> The forward run checks each sink. A finding that needs a DEMAND fact is
> provisional, and its occurrence is a DEMAND witness for the next backward
> run. **CURRENT** (ap.md §9.2) except the foreign row.

```text
at a sink statement of method, for each occurrence of the rule:
  fires(condition, the facts at the statement)
    a NORMAL fact satisfies a literal  ⇔  impl(fact, literal)   (§N.5)
    a DEMAND fact satisfies a literal  ⇔  they overlap           (MAY)
  each fact of the firing combination NORMAL  ⇒  CONFIRMED finding
  otherwise                                  ⇒  provisional finding; DEMAND witness (method, statement, occurrence)
the next backward run seeds each DEMAND witness (§II.3)
```

| NORMAL fact | satisfies `P.$(T)` | satisfies `P.[any](T)` | Status |
| --- | --- | --- | --- |
| `$ ℓ` | `ℓ = P(T)` | `ℓ ∈ covered(P.[any](T))` | **CURRENT** |
| `[all-fields] S` | `P(T) ∈ S` | `S ∩ covered(P.[any](T)) ≠ ∅` | **CURRENT** |
| `[any-field] S` (foreign) | never | `S ⊆ covered(P.[any](T))` | **NEW** (B4, D2) |

### I.3 Capture of ND inputs (B3)

> For B3, the forward run keeps the facts that satisfied each ND literal at
> each DEMAND witness. The next backward run meets the ND seeds with them
> (§II.10). **NEW**.

```text
captured(literal; method, statement, occurrence) =
  { input | input satisfied literal in a COMPLETED combination (NORMAL or DEMAND) of the occurrence }
normal form (a pattern):   mark  := the concrete mark that the check matched   (a FLOW input: the mark of the literal)
                           */E   := [all-fields]/E                             (the same locations)
                           a foreign [any-field]/E input is kept as it is      (its set covers the tainted location)
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
> operation with `[any-field]` in place of `[all-fields]` (§II.5).

```text
added         the fact that enters the callee by a binding b.* → b'.*, with its layer
field added   ⇔  added.tail is the native field tail ([all-fields] forward, [any-field] backward)
emit(entryDemand, added)  =  (premise, startFact)  or  none
```

| entryDemand mark | added mark | premise | must premise | startFact |
| --- | --- | --- | --- | --- |
| `*` (abstract) | any | FLOW form of entryDemand: tail `$`→`$`, `[any]`→`*/{}`, `*/E`→`*/E`; mark `*` | no | the premise, NORMAL (identity) |
| `T` (concrete) | `T` | `meet(added, entryDemand)` | ⇔ field added ∧ premise tail is a field tail | must premise: the premise, NORMAL; else by tail: `$` → NORMAL; `[any]`, `*/E` → `[any]` DEMAND |
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
| native field tail `F/E1` | `$` | `F/E1` at the added path; `F/∅` at a deeper demand path | no canonical case |

`F` is `[all-fields]` in the forward run and `[any-field]` in the backward
run. A foreign added fact: §I.9 (D2). Contract: each common location with its
mark is covered by the premise, the added fact satisfies the premise, and the
premise is inside entryDemand (`AnyTaintExCov.emitX_contract`).

Code form (**CURRENT**): no summary premise has the `[any]` tail
(`RunSummaries.kt:58`). The code keys the may `[any]` premise as the
concrete-mark premise `*/{}(T)` (`RestrictedInitialPolicy.kt:34`), with the
same DEMAND start fact. ap.md and the Lean model write it as `[any](T)`.

Examples (forward, all **CURRENT**; the must rows e3, e5, e6 are **NEW** in the backward run, §II.5):

| Ex | entryDemand | added fact | premise, must premise | startFact | Case |
| --- | --- | --- | --- | --- | --- |
| e1 ✓ | `x.[any](T)` | `x.f.$(T)` NORMAL | `x.f.$(T)`, no | `x.f.$(T)` NORMAL | added below |
| e2 ✓ | `x.f.[any](T)` | `x.[any](T)` DEMAND | `x.f.[any](T)`, no | `x.f.[any](T)` DEMAND | added above |
| e3 ✓ | `x.f.[any](T)` | `x.[all-fields]/{g}(T)` NORMAL | `x.f.[all-fields](T)`, yes | `x.f.[all-fields](T)` NORMAL | above: `{g}` is not kept at the deeper path |
| e4 ✓ | `x.f.[any](T)` | `x.[all-fields]/{f}(T)` NORMAL | none | — | `{f}` rejects `f` |
| e5 ✓ | `x.[any](T)` | `x.[all-fields]/{g}(T)` NORMAL | `x.[all-fields]/{g}(T)`, yes | `x.[all-fields]/{g}(T)` NORMAL | added at |
| e6 ✓ | `x.$(T)` | `x.[all-fields]/{g}(T)` NORMAL | `x.$(T)`, no | `x.$(T)` NORMAL | `meetTail(F, $) = $` |
| e7 ✓ | `x.[any](*)` | `x.[all-fields](T)` NORMAL | `x.*/{}(*)`, no (FLOW) | identity, NORMAL | abstract entryDemand (`Abs.emitW`) |
| e8 ✓ | `x.[any](T)` | `x.f.$(U)` NORMAL | none | — | the marks differ |

### I.5 Forward summaries and records

> Which forward summaries the record store keeps (rule R1). **CURRENT**
> (ap.md §8.7 R1).

```text
record(forward summary)  ⇔  layer = NORMAL ∧ one premise (the zero premise is allowed)
                            also with [all-fields] leaves, also with a must premise
```

| Ex | method | summary | Shape, meaning | Record | Status |
| --- | --- | --- | --- | --- | --- |
| m1 | `ret.f = arg0` | `forward: arg0.$(T) → ret.f.$(T)` NORMAL | s1: `flows(arg0(T), ret.f(T))` | yes | **CURRENT** |
| m2 | `ret.f = arg0` | `forward: arg0.*/{}(*) → ret.f.*/{}(*)` NORMAL (FLOW) | `pairs = {(arg0.suffix(mark), ret.f.suffix(mark))}` ⊆ flows | yes | **CURRENT** |
| m3 | `ret.g = arg0` | `forward: arg0.[all-fields](T) →must ret.g.[all-fields](T)` NORMAL | s5: each `ret.g.suffix(T)` has a source in `arg0` and its fields | yes | **CURRENT** |

### I.6 Restriction by the demand edge

> In a restricted run, each new summary is cut to the demand edges of its
> method. The cut keeps exactly the demanded pairs. Record persistence (R1)
> and selection (§I.10) read the raw summary, before the cut. **CURRENT**
> (ap.md §6.4) for the native kinds.

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
| above, native field tail `F/E` | none if `E` rejects `suffix`; else at `demandPath`: `$`, `F/E2`, `F/∅` for a `$`, `*/E2`, `[any]` demand |
| above, tail `*/E` | the conclusion if `E` admits `suffix`; else none |
| above with tail `$`; apart; other base | none |

| tail at `demandPath` | demand `$` | demand `*/E2` | demand `[any]` |
| --- | --- | --- | --- |
| `$` | `$` | `$` | `$` |
| `[any]` | `$` | `[any]` | `[any]` |
| native field tail `F/E` | `$` | `F/(E ∪ E2)` | `F/E` |
| `*/E` | `*/E` | `*/E` | `*/E` |

`F` is `[all-fields]` forward and `[any-field]` backward. Both are sound,
because the cut narrows the set and a native kind survives narrowing. A
foreign conclusion: §I.9 (D2). Contract: each pair of the summary whose exit
location is covered by exitDemand (with its mark) is a pair of the result,
and the result adds no pair (`HandoffRestrict.restrictI_contract`,
`restrictI_sub`; `CurrentDemand.restrictCertificate`). Limits: `[any]` at a
`*/E2` demand loses `E2`; a `*` conclusion stays whole; an abstract mark
passes through.

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
| r8 ✓ | `… → ret.[all-fields]/{h}(T)` NORMAL | exitDemand `ret.f.[any](T)` | `ret.f.[all-fields](T)` NORMAL | above, `[any]` demand |
| r9 ✓ | `… → ret.[all-fields]/{h}(T)` NORMAL | exitDemand `ret.h.[any](T)` | none | `{h}` rejects `h` |
| r10 ✓ | `… → ret.[all-fields]/{h}(T)` NORMAL | exitDemand `ret.f.$(T)` | `ret.f.$(T)` NORMAL | above, `$` demand |
| r11 | `… → ret.[all-fields]/{h}(T)` NORMAL | exitDemand `ret.*/{k}(T)` | `ret.[all-fields]/{h,k}(T)` NORMAL | at; the Lean model keeps `/{h}` (wider, `ex_r11_model`) |

r1–r5: `Handoff.restrictI` (gates and cut). r6–r11: `restrictConcX` (cut with exclusion).

### I.7 Summary application, both runs (B4)

> A summary of the callee, or a record, gives results for a reader: an added
> fact in the forward run, a requirement in the backward run. Which edges
> the run uses is **CURRENT**. B4 decides the result: NORMAL if and only if
> the implication of §N.5 holds, with the kind of the other end of the edge.
> For the edges that the CURRENT code applies, B4 gives the CURRENT result,
> except for the forward must records that the backward run reads (§I.8
> cases 2, 2', **CHANGED**).

```text
reader       forward run: an added fact at the forward entry of the callee;  backward run: a requirement at the forward exit
inputEnd     the end of the edge at the reader:     forward run: entryEnd;   backward run: exitEnd
outputEnd    the other end
use          summary of this run (restricted piece): inside(premise, reader)                                    CURRENT
             record (R4): inside(inputEnd, reader) ∨ applicable(inputEnd, reader)                                  CURRENT
               applicable(end, reader) ⇔ covered(reader) ⊆ covered(end) ∧ (must premise ⇒ reader has a field tail or [any])
               a record of the other direction: R4 on its CURRENT view premise (a field tail read as */E, §I.8)
result       NORMAL outputEnd (its tail, path, mark and exclusion)   if   forward run:   impl(reader, inputEnd)
                                                                         backward run:  impl(inputEnd, reader)
             DEMAND outputEnd otherwise: a field tail is written [any] (W6), $ stays $
             then layer join with the reader layer and the edge layer
```

Why the implication turns around: a forward reader is a claim, and the claim
must give the input end. A backward reader is a sufficient condition, and the
input end must give it. Then the valid edge carries the result to the other
end (`FieldQuant.fwd_apply`, `bwd_apply`, `bwd_apply_mono`). No weaker
condition is sound for every edge (`fwd_apply_exact`, `bwd_apply_exact`: the
identity edge `Y → Y`). The CURRENT MUST rule is the forward s4, s5 row:
`impl([all-fields] A, [all-fields] Y) ⇔ Y ⊆ A` (inside).

**Forward run** (reader at the forward entry; inputEnd = entryEnd; the result is exitEnd):

| Shape | inputEnd → outputEnd | Edges of this shape | reader `$ a0` | reader `[all-fields] A` | reader `[any-field] A` (foreign) | Status |
| --- | --- | --- | --- | --- | --- | --- |
| s1 | `$ a` → `$ r` | forward `$ → $`; backward `$ → $` record | `a0 = a` | `a ∈ A` | never | **CURRENT**; foreign reader **NEW** |
| s2 | `$ a` → `[all-fields] X` | forward `$ → [all-fields]`; backward from a foreign start | `a0 = a` | `a ∈ A` | never | **CURRENT** (forward); **NEW** (backward, D2) |
| s3 | `$ a` → `[any-field] X` | backward `[any-field] →must $` record (case 3'); forward from a foreign start | `a0 = a` | `a ∈ A` | never | **NEW** (B2, B4): result foreign |
| s4 | `[all-fields] Y` → `$ r` | forward `[all-fields] →must $` | never | `Y ⊆ A` | never | **CURRENT** (MUST rule) |
| s5 | `[all-fields] Y` → `[all-fields] X` | forward `[all-fields] →must [all-fields]` | never | `Y ⊆ A` | never | **CURRENT** (MUST rule) |
| s6 | `[all-fields] Y` → `[any-field] X` | from a foreign fact only | never | `Y ⊆ A` | never | **NEW** (D2) |
| s7 | `[any-field] Y` → `$ r` | backward `$ → [any-field]` record (case 4); forward from a foreign start | `a0 ∈ Y` | `A ∩ Y ≠ ∅` | `A ⊆ Y` | **NEW** (B1, B2) |
| s8 | `[any-field] Y` → `[all-fields] X` | from a foreign fact only | `a0 ∈ Y` | `A ∩ Y ≠ ∅` | `A ⊆ Y` | **NEW** (D2) |
| s9 | `[any-field] Y` → `[any-field] X` | backward `[any-field] →must [any-field]` record (case 3); forward from a foreign start | `a0 ∈ Y` | `A ∩ Y ≠ ∅` | `A ⊆ Y` | **NEW** (B2, B4): result foreign |

**Backward run** (reader at the forward exit; inputEnd = exitEnd; the result is entryEnd):

| Shape | inputEnd → outputEnd | Edges of this shape | reader `$ r0` | reader `[any-field] R` | reader `[all-fields] R` (foreign) | Status |
| --- | --- | --- | --- | --- | --- | --- |
| s1 | `$ r` → `$ a` | backward `$ → $`; forward `$ → $` record | `r = r0` | `r ∈ R` | never | **CURRENT**; `[any-field]` reader **NEW** (B1) |
| s2 | `[all-fields] X` → `$ a` | forward `$ → [all-fields]` record (case 1); backward from a foreign start | `r0 ∈ X` | `X ∩ R ≠ ∅` | `R ⊆ X` | **CURRENT** (`$` reader); others **NEW** |
| s3 | `[any-field] X` → `$ a` | backward `[any-field] →must $` | never | `X ⊆ R` | never | **NEW** (B1, B2) |
| s4 | `$ r` → `[all-fields] Y` | forward `[all-fields] →must $` record (case 2') | `r = r0` | `r ∈ R` | never | **CHANGED**: CURRENT `[any]` DEMAND; result foreign |
| s5 | `[all-fields] X` → `[all-fields] Y` | forward `[all-fields] →must [all-fields]` record (case 2) | `r0 ∈ X` | `X ∩ R ≠ ∅` | `R ⊆ X` | **CHANGED**: CURRENT `[any]` DEMAND; result foreign |
| s6 | `[any-field] X` → `[all-fields] Y` | from a foreign fact only | never | `X ⊆ R` | never | **NEW** (D2) |
| s7 | `$ r` → `[any-field] Y` | backward `$ → [any-field]` (row S3) | `r = r0` | `r ∈ R` | never | **NEW** (B1) |
| s8 | `[all-fields] X` → `[any-field] Y` | from a foreign fact only | `r0 ∈ X` | `X ∩ R ≠ ∅` | `R ⊆ X` | **NEW** (D2) |
| s9 | `[any-field] X` → `[any-field] Y` | backward `[any-field] →must [any-field]` | never | `X ⊆ R` | never | **NEW** (B1, B2): a7, a8 |

Examples, forward native edges (all **CURRENT**):

| Ex | added fact | summary | inside | applicable | Result |
| --- | --- | --- | --- | --- | --- |
| a1 ✓ | `arg0.$(T)` NORMAL | `forward: arg0.$(T) → ret.f.$(T)` NORMAL | yes | yes | `ret.f.$(T)` NORMAL (s1) |
| a2 ✓ | `arg0.h.$(T)` NORMAL | `forward: arg0.*/{}(*) → ret.f.*/{}(*)` NORMAL | no | yes | `ret.f.h.$(T)` NORMAL (FLOW, as a record only) |
| a3 ✓ | `arg0.$(T)` DEMAND | as a1 | yes | yes | `ret.f.$(T)` DEMAND (layer join) |
| a4 ✓ | `arg0.[all-fields](T)` NORMAL | `forward: arg0.[all-fields](T) →must ret.g.[all-fields](T)` NORMAL | yes | yes | `ret.g.[all-fields](T)` NORMAL (s5, `Y ⊆ A`) |
| a5 ✓ | `arg0.h.[all-fields](T)` NORMAL | as a4 | no | yes | `ret.g.[any](T)` DEMAND (s5, `Y ⊄ A`) |
| a6 ✓ | `arg0.h.$(T)` NORMAL | as a4 | no | no | not used; the run analyses the callee for the added fact |

The records of the other direction: §I.8. The backward edges in the backward
run: §II.8 (a7, a8).

### I.8 Records of the other direction

> A record of one direction is applied by the run of the other direction with
> the rule of §I.7. B4 keeps the kind of the record premise in the result, so
> the results of must records stay NORMAL, with the foreign kind. Cases 1 and
> 4 give the same result as before; cases 2, 2' are **CHANGED**; cases 3, 3'
> are **NEW**.

```text
record ends      read by the record direction: a forward ANY_TAINT end is [all-fields], a backward one [any-field]
reader           a fact of the other direction at the record conclusion end:
                   a backward requirement at the forward exit reads the forward records of the method;
                   a forward fact at the forward entry reads the backward records of the method
inputEnd         the record conclusion leaf;   outputEnd   the record premise
guard            both marks concrete (CURRENT); an abstract-mark (FLOW) record: generic leaf reversal (ap.md §9.1), CURRENT
CURRENT view     (ap.md §8.7 R3, CurrentMustReverse.readView)  premise: endPattern(conclusion leaf), a field tail read as */E;
                 result: startResult(premise), $ NORMAL, a field tail [any] DEMAND (E forgotten)
B4               the use rule keeps the CURRENT view premise; the result is the record premise with its kind and exclusion,
                 NORMAL if the implication of §I.7 holds
```

| Case | Record | Shape | B4 result for an implying reader | CURRENT / without B4 | Status | Lean |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `forward: arg.$(U) → ret.[all-fields]/E(T)` | s2 | `arg.$(U)` NORMAL | the same | **CURRENT** | `CurrentMustReverse.exact_converse`, `BackView.fwd_pair_valid` |
| 2 | `forward: arg.[all-fields]/E2(U) →must ret.[all-fields]/E(T)` | s5 | `arg.[all-fields]/E2(U)` NORMAL, a foreign backward requirement | `arg.[any](U)` DEMAND | **CHANGED** | `BackView.fwd_must_valid`, `fwdMust_backward_normal` |
| 2' | `forward: arg.[all-fields]/E2(U) →must ret.f.$(T)` | s4 | `arg.[all-fields]/E2(U)` NORMAL, foreign | `arg.[any](U)` DEMAND | **CHANGED** | as case 2 |
| 3 | `backward: ret.[any-field]/E2(T) →must arg.[any-field]/E(U)` | s9 | `ret.[any-field]/E2(T)` NORMAL, a foreign forward fact | `ret.[any](T)` DEMAND (no backward must record today) | **NEW** (B2, B4) | `BackView.bwd_must_valid`, `backMust_forward_normal` |
| 3' | `backward: ret.[any-field]/E2(T) →must arg.$(U)` | s3 | `ret.[any-field]/E2(T)` NORMAL, foreign | `ret.[any](T)` DEMAND | **NEW** (B2, B4) | as case 3 |
| 4 | `backward: ret.$(T) → arg.[any-field]/E(U)` (row S3 with B1) | s7 | `ret.$(T)` NORMAL | the same | **NEW** (B1, B2) | `BackView.bwd_pair_valid`, `backExactView_forward` |

Why a NORMAL result of a must record has the foreign kind:

* Case 2: the record gives each `ret` location SOME source in `arg`, not a
  known one. So taint on all of `arg` makes the reader location tainted, and
  no smaller set does. The result says "all of `arg` is sufficient":
  `[all-fields]`. The native result "any `arg` location is sufficient" is
  false (`AnyTaintExact.CexRev.cex_rev`).
* Case 3: the record gives each `arg` location SOME target in `ret`. So one
  tainted `arg` location makes some `ret` location tainted, not a known one.
  The result is `[any-field]` on `ret`. A native `$` or `[all-fields]` result
  is false (`BackMustView.Cex.viewF_not_exact`).
* Cases 1, 4 are pair-exact: each pair is a flow, so the `$` result is exact
  and native.

Examples (✓: the CURRENT / without-B4 column is the Lean theorem):

| Ex | Case | record | reader | CURRENT / without B4 | B4 | Status |
| --- | --- | --- | --- | --- | --- | --- |
| v1 ✓ | 1 | `forward: arg0.$(T) → ret.[all-fields](T)` | backward `ret.h.$(T)` NORMAL | `arg0.$(T)` NORMAL | the same (`ret.h ∈ X`) | **CURRENT** |
| v2 ✓ | 2 | `forward: arg0.[all-fields](T) →must ret.g.[all-fields](T)` | backward `ret.g.h.$(T)` NORMAL | `arg0.[any](T)` DEMAND | `arg0.[all-fields](T)` NORMAL (`ret.g.h ∈ X`) | **CHANGED** |
| v6 ✓ | 2 | `forward: arg0.[all-fields](T) →must ret.g.[all-fields]/{h}(T)` | backward `ret.g.h.$(T)` NORMAL | none: `{h}` excludes `h` | none: the use rule rejects it | **CURRENT** |
| v3 ✓ | 2' | `forward: arg0.[all-fields](T) →must ret.f.$(T)` | backward `ret.f.$(T)` NORMAL | `arg0.[any](T)` DEMAND | `arg0.[all-fields](T)` NORMAL | **CHANGED** |
| v4 ✓ | 3 | `backward: ret.[any-field](T) →must arg0.[any-field](T)` | forward `arg0.h.$(T)` NORMAL | `ret.[any](T)` DEMAND | `ret.[any-field](T)` NORMAL (`arg0.h ∈ Y`) | **NEW** |
| v5 ✓ | 3 | as v4 | forward `arg0.h.$(U)` NORMAL | none: the marks do not meet | none | **NEW** |
| v7 ✓ | 3' | `backward: ret.[any-field](T) →must arg0.$(U)` | forward `arg0.$(U)` NORMAL | `ret.[any](T)` DEMAND | `ret.[any-field](T)` NORMAL | **NEW** |
| v8 ✓ | 4 | `backward: ret.$(T) → arg0.[any-field](U)` | forward `arg0.g.$(U)` NORMAL | `ret.$(T)` NORMAL | the same | **NEW** |

Today the code reads backward records only by generic leaf reversal, because
a backward record has no field end (`RecordStore.kt:274-277`). Model note:
`BackMustView.viewF` tests overlap instead of R4; overlap accepts more
readers, and the view is sound for each.

### I.9 Foreign forward facts and D2

> B4 makes forward `[any-field]` facts (cases 3, 3') and backward
> `[all-fields]` requirements (cases 2, 2'). A foreign kind holds its
> statement for the whole location set only. A step that narrows the set
> breaks it, so a foreign kind cannot act like `[any-taint]` in transfer.
> D2 decides their transfer. **OPEN**.

```text
foreign forward fact   x.p.[any-field]/E(T): some location of x.p·suffix (E admits suffix) carries T
narrowing step         the result covers a proper subset of the set: the exclusion grows at a strong update,
                       a field read below x.p, an emission or a restriction at a deeper path or at $
native kinds survive narrowing      FieldQuant.all_sub, all_kill, req_any_sub
foreign kinds do not                FieldQuant.Cex.any_not_sub, any_not_kill, all_req_not_sub
```

Forward steps under option D2-a:

| Step | `[all-fields]` (native, CURRENT) | `[any-field]` (foreign, D2-a) |
| --- | --- | --- |
| a statement that writes no location of the set | kept | kept |
| a copy of the whole set, `y.q = x.p` | `y.q.[all-fields]/E` | `y.q.[any-field]/E` |
| a strong update in the set, `x.p.f = …` with `E` admitting `f` | `x.p.[all-fields]/(E ∪ {f})` | `x.p.[any]` DEMAND (`Cex.any_not_kill`) |
| a field read below the set, `y = x.p.f` | `y.[all-fields]` | `y.[any]` DEMAND |
| emission: added at or added below, `[any]` entryDemand | the premise is the fact (e5) | the premise is the fact; start NORMAL; callee shapes s7, s8, s9 |
| emission: added above, or a `$` or `*/E2` entryDemand | a narrower premise, NORMAL (e3, e6) | DEMAND start (`Cex.any_not_sub`) |
| restriction: exitDemand `[any]` at the same path or above | kept | kept |
| restriction: a deeper or `$` exitDemand (r8, r10) | narrower, NORMAL | DEMAND |
| sink check (§I.2) | `$` and `[any]` literals | only `[any]` literals that cover the set |
| reader in §I.7 | column `[all-fields]` | column `[any-field]` |
| hand-off pattern (§I.10) | `[any]`, `E` dropped | the same |

| Option | Foreign kinds in transfer | Effect | Status |
| --- | --- | --- | --- |
| D2-a | NORMAL while the whole set stays or moves; a narrowing step makes them DEMAND `[any]` (table above; backward: §II.12) | cases 2, 3 results reach later sinks, sources and calls through copies, returns and untouched statements | **OPEN**, recommended |
| D2-b | NORMAL only at the node where B4 makes them (sink check, source hit, the next application); each transfer step makes them DEMAND | smaller change; a sink at the next statement keeps the result, a longer route loses it | **OPEN** |
| D2-c | like `[any-taint]` in each step (the literal reading of "act like `[any-taint]` everywhere") | unsound: `Cex.any_not_kill` (strong update), `Cex.any_not_sub` (emission, restriction), `Cex.all_req_not_sub` (backward) | rejected |

Unselected major changes that B4 with D2-a or D2-b brings (§II.13): a forward
NORMAL fact that claims "some location" (a new forward invariant and a new
code tail), new transfer rows, a sink check that confirms with it (S-H10),
and NORMAL backward requirements in place of DEMAND ones (S-H11).

### I.10 Hand-off: selection and demand edges

> At the end of a run, the selected summaries give the demand edges of the
> next run; the other summaries are records and give no demand (F77). A
> demand edge is a pair of patterns with no layer: the kind and the layer of
> the summary do not go to the next run. **CURRENT** (ap.md §8.5,
> `HandOff.kt`, `HandoffCompactor.kt:111-124`, `StaticGuidance.kt:50-57`).

```text
selected(summary)  ⇔  layer = DEMAND ∨ |premises| ≥ 2 ∨ (direction = backward ∧ premise = zero)
selected      ⇒  for each restricted piece premise → conclusion, each conclusion leaf and each premise member:
                   demand edge of the method in the next run
                   (entryDemand = pattern(conclusion leaf), exitDemand = pattern(premise member))
                 pattern:  a field tail F/E → [any] (E dropped);  $, */E, [any] kept;  mark kept
not selected  ⇒  the summary is a record (R1): no demand edge; the next run reads the record (§I.8)
```

| Summary end | Its demand pattern | Selected summaries that have it | Status |
| --- | --- | --- | --- |
| conclusion `$`, `*/E` | the same | each selected kind | **CURRENT** |
| conclusion `[any]` | entryDemand `[any]` | DEMAND summaries | **CURRENT** |
| conclusion field tail `[all-fields]/E` or `[any-field]/E` | entryDemand `[any]`, `E` dropped | NORMAL multi-premise summaries; backward zero-premise summaries (q3, with B1); backward must summaries (H2) | **CURRENT** rule; the backward rows are **NEW** with B1, B2 |
| premise `$`, `*/E` | exitDemand the same | each selected kind | **CURRENT** |
| premise field tail (must) | exitDemand `[any]`, `E` dropped | DEMAND must summaries, for example `arg0.[all-fields] →must ret.[any]`; H2 | **CURRENT** |

So entryDemand from a MAY conclusion with exitDemand from a must premise is
a normal case: §II.7 gives the intersection rules for it.

| Ex | summary | selected | Demand edge for the next run (backward) | Status |
| --- | --- | --- | --- | --- |
| q1 | `forward: arg0.$(T) → ret.f.$(T)` NORMAL | no | none; the next run reads the record (s1) | **CURRENT** |
| q2 | `forward: arg0.[any](T) → ret.[any](T)` DEMAND | yes | `(ret.[any](T), arg0.[any](T))` | **CURRENT** |
| q5 | `forward: arg0.[all-fields]/{g}(U) →must ret.[any](T)` DEMAND | yes | `(ret.[any](T), arg0.[any](U))`: `{g}` dropped | **CURRENT** |

### I.11 Proofs and model notes (forward)

> Where the forward claims are proved, and where the model differs from the
> code.

| Claim | Lean |
| --- | --- |
| the implication table, each cell exact | `FieldQuant.impl_*`, `not_impl_*` |
| the nine edge shapes | `FieldQuant.valid_one`, `valid_all`, `valid_any`, `valid_all_all`, `valid_all_any`, `valid_any_all`, `valid_any_any` |
| B4 is sound in both runs, and exact | `FieldQuant.fwd_apply`, `bwd_apply`, `bwd_apply_mono`, `fwd_apply_exact`, `bwd_apply_exact` |
| the NORMAL records of both runs are valid edges | `BackView.fwd_pair_valid`, `fwd_must_valid`, `bwd_pair_valid`, `bwd_must_valid` |
| §I.8 cases 2, 3 with B4 | `BackView.fwdMust_backward_normal`, `backMust_forward_normal` |
| native kinds survive narrowing, foreign kinds do not | `FieldQuant.all_sub`, `all_kill`, `req_any_sub`; `FieldQuant.Cex.*` |
| NORMAL forward summaries are pair-exact or end-exact | `AnyTaintExExact.DRX_edgeOK` |
| emission contract | `AnyTaintExCov.emitX_contract`, `Abs.emitW_contract` |
| restriction keeps exactly the demanded pairs | `HandoffRestrict.restrictI_contract`, `restrictI_sub`, `restrictI_inter`; `CurrentDemand.restrictCertificate` |
| the MUST rule is necessary | `AnyTaintExact.CexApp.cex_app` |
| the examples | `BackCondEx` |

* `FieldQuant` is a location-set model: a state is a set of locations, a
  method is a flow relation, and taint is distributive (`post`). The
  `BackView` bridges instantiate it with `Loc` and `Flow` of the run model.
  The run model has no foreign fact: the D2 rows and the foreign sink check
  are proved at the location-set level only.
* `restrictConcX` keeps the field tail `/E` at the same path for a `*/E2`
  demand and gives `/∅` above it; ap.md gives `/(E ∪ E2)` and `/E2`. The
  model is wider and sound (r11).
* The Lean hand-off (`Handoff.demOfN`) uses patterns with no layer and no
  exclusion, so a must premise is an `[any]` exitDemand there too.
* `BackMustView`: one record, one leaf; no store lookup, statics, cleaners
  or type filters.

## Part II. Backward run

> The backward run starts at the DEMAND witnesses of the previous forward
> run (§I.2) and walks `reverse(P)`. A backward fact is a requirement: a
> sufficient condition for the sink to fire. The run hands demand to the
> next forward run (§II.11). B1, B2, B3 and D1 are in this part.

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
  NORMAL (MUST)   ∀ σ: holds(σ, requirement) at the node ⇒ the seeded sink fires
                  native [any-field]: taint at any covered location fires;  $: taint at the location fires
  DEMAND (MAY)    the DEMAND requirements cover each location of a real route to the sink

layer of the requirement from a literal:
  CURRENT   NORMAL ⇔ literal.tail = $          seedFact (RunMethodLocalServices.kt:437-449) seeds NORMAL; W6 makes [any] DEMAND
  B1        NORMAL ⇔ literal is unary          [BackCond.reqs_normal_must, reqs_nd_demand]
            a unary [any] literal gives the [any-field] tail: the literal is the end [any-field] (§N.2)
```

| Literal | CURRENT requirement | B1 requirement | Status |
| --- | --- | --- | --- |
| unary `P.$(T)` | `P.$(T)` NORMAL | `P.$(T)` NORMAL | **CURRENT** |
| unary `P.[any](T)` | `P.[any](T)` DEMAND | `P.[any-field](T)` NORMAL | **CHANGED** |
| ND `P.$(T)` | `P.$(T)` NORMAL (not MUST: breaks the meaning) | `P.$(T)` DEMAND | **CHANGED** |
| ND `P.[any](T)` | `P.[any](T)` DEMAND | refined seeds, DEMAND (B3) | **CHANGED** (B3) |

With B1, a CURRENT ND `$` seed would make false MUST facts. Example: the
reversed source rule S3 turns `P.$(T)` NORMAL into `Q.[any-field](T')`.

### II.3 Sink seeds

> The seeds of each rule literal at a DEMAND witness. The last column is
> what the seed reads from forward run `n−1`.

| # | Rule condition | Seed | Status | Input from forward run `n−1` |
| --- | --- | --- | --- | --- |
| K1 | `ContainsMark(P, T)`, unary | `P.$(T)` NORMAL | **CURRENT** | DEMAND witness (method, statement, occurrence) |
| K2 | `ContainsMarkOnAnyField(P, T)`, unary | `P.[any-field](T)` NORMAL, exclusion `∅` | **CHANGED**: CURRENT `P.[any](T)` DEMAND | DEMAND witness |
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
| S1 | unconditional source `zero → P.tail(T)`, tail `$` or `[all-fields]` | zero (zero demand); a source hit if impl(source fact, requirement) | **CURRENT** | none (run `n+1` fires the source only if hit) |
| S2 | conditional source, unary `ContainsMark(Q, T')` | `Q.$(T')` in targetLayer | **CURRENT** | none |
| S3 | conditional source, unary `ContainsMarkOnAnyField(Q, T')` | `Q.[any-field](T')` NORMAL if targetLayer is NORMAL; `Q.[any](T')` DEMAND otherwise | **CHANGED**: CURRENT `Q.[any](T')` DEMAND | none |
| S4 | conditional source, ND `ContainsMark(Q, T')` | `Q.$(T')` DEMAND | **CURRENT** | none (refinement is the identity) |
| S5 | conditional source, ND `ContainsMarkOnAnyField(Q, T')` | `refinedSeeds(literal)` DEMAND (§II.10) | **CHANGED**: CURRENT `Q.[any](T')` DEMAND | `captured(literal)` at the source occurrence |
| S6 | pass rule `P → Q` (no `AnyField`) | the reversed result in targetLayer | **CURRENT** | none |
| S7 | pass rule `P → Q.AnyField` | each result DEMAND | **CURRENT** | none |
| S8 | end-fact action of sink alternative `A` | zero; fires K7 at (method, statement, `A`) once | **CURRENT** | none (also if `A` is CONFIRMED) |
| S9 | cleaner, type filter | unchanged rule | **CURRENT** (see S-H2) | none |

MAY class: K3, K4, S4, S5, S7. Each result is DEMAND, also a `$` result
(DES-3, D18). The DEMAND layer is **CURRENT** for K4, S4, S5, S7 and
**CHANGED** for K3. A foreign `[all-fields]` requirement on the rule target:
§II.12.

A MUST requirement gets an exclusion at a strong update. A DEMAND `[any]`
requirement has no exclusion (`BackMust.transferXB`). Program:
`x.f = z; …; x.f = y; sink(x)`, walked backward.

| Ex | at `sink(x)` | after reversed `x.f = y` | after reversed `x.f = z` | Status |
| --- | --- | --- | --- | --- |
| t1 ✓ | `x.[any-field](T)` NORMAL | `y.[any-field](T)`, `x.[any-field]/{f}(T)` NORMAL | `y.[any-field](T)`, `x.[any-field]/{f}(T)` NORMAL: no requirement on `z` | **NEW** (B1) |
| t2 ✓ | `x.[any](T)` DEMAND | `y.[any](T)`, `x.[any](T)` DEMAND | `y.[any](T)`, `z.[any](T)`, `x.[any](T)` DEMAND | **CURRENT** |

### II.5 Calls into callees

> A requirement enters a callee as the added fact of the emission (§I.4,
> ap.md §9.2), with `[any-field]` as the native field tail. Today no
> backward added fact has a field tail (W8 (d)), so the must rows of §I.4
> do not occur; with B1 they do.

entryDemand: from the demand edge that forward run `n−1` handed off for the callee (§I.10).

| # | requirement | entryDemand | premise, must premise | startFact | callee summary | Status |
| --- | --- | --- | --- | --- | --- | --- |
| C1 | `x.[any-field]/E(T)` NORMAL | concrete `x.[any](T)` | `x.[any-field]/E(T)`, yes (e5) | NORMAL | s3 or s9 (end-exact); a record (B2); hand-off: D1 | **NEW**: CURRENT requirement `x.[any](T)` DEMAND → C4 |
| C2 | `x.[any-field]/E(T)` NORMAL | concrete `x.$(T)` | `x.$(T)`, no (e6) | NORMAL | s1 or s7 record; caller results NORMAL | **CHANGED**: CURRENT same summary, caller results DEMAND |
| C3 | `x.[any-field]/E(T)` NORMAL | abstract `x.[any](*)` | `x.*/{}(*)`, no (e7) | identity, NORMAL | FLOW record; caller results NORMAL | **CHANGED**: CURRENT caller results DEMAND |
| C4 | `x.[any](T)` DEMAND | concrete `x.[any](T)` | may `[any]` premise (e2 type) | DEMAND | DEMAND, selected | **CURRENT** |
| C5 | `x.$(T)` NORMAL | concrete | `x.$(T)`, no (e1 type) | NORMAL | s1 record | **CURRENT** |

The results return to the caller by §II.8 (backward summaries and records)
and §II.9 (forward records).

### II.6 Backward summaries and records (B2)

> Which backward summaries the record store keeps. B2 adds the summaries
> with a field premise or a field leaf. **CHANGED** (ap.md §8.7 R1,
> `RecordStore.kt:274-277`).

```text
record(backward summary):
  CURRENT   layer = NORMAL ∧ one premise ∧ premise ≠ zero ∧ premise.tail is not a field tail ∧ no field leaf
  B2        layer = NORMAL ∧ one premise ∧ premise ≠ zero
```

A backward must record is end-exact on `reverse(P)` (shapes s3, s9) and not
pair-exact (`BackMust.recsB_must_end`, `CexMustPair.cex_must_pair`). A
backward record whose premise is not must is pair-exact, also with
`[any-field]` leaves (s1, s7; `BackMust.recsB_pair`). A zero-premise backward
summary is never a record: a seed relates `zero` to each seed location, which
is not a flow.

| Ex | method | summary | Shape, meaning | Record | Status |
| --- | --- | --- | --- | --- | --- |
| m4 | identity `M(arg0)` | `backward: arg0.[any-field](T) →must arg0.[any-field](T)` NORMAL | s9: each `arg0` location reaches some `arg0` location (itself); `(arg0.f, arg0.g)` is a pair and no flow: not pair-exact | B2: yes (§I.8 case 3) | **NEW**: CURRENT no |
| m6 | `ret = source(T) if ContainsMarkOnAnyField(arg0, U)` | `backward: ret.$(T) → arg0.[any-field](U)` NORMAL | s7: each `arg0.suffix(U)` flows to `ret(T)` | B2: yes (§I.8 case 4) | **NEW**: CURRENT the leaf is `[any]` DEMAND, no record |
| m5 | `sink(arg0)` in `M` | `backward: zero → arg0.[any-field](T)` NORMAL | a seed path, not a flow | no | **CURRENT** rule (the `[any-field]` seed is B1) |

### II.7 Restriction in the backward run

> The backward run cuts its summaries by the demand edges of §I.10 with the
> operation of §I.6. A demand edge has no layer, so it does not decide the
> kind or the layer: the backward facts do (B1). **CURRENT** for may
> summaries; the field-tail rows are **NEW** (B1, B2).

| Ex | summary | demand edge | restrict | Status |
| --- | --- | --- | --- | --- |
| r12 ✓ | `backward: ret.[any-field](T) →must arg0.[any-field](T)` NORMAL | `(ret.[any](T), arg0.h.$(T))` | `arg0.h.$(T)` NORMAL | **NEW** (B1, B2) |

**Case: entryDemand from a MAY conclusion, exitDemand from a must premise.**
Forward run `n−1` has the DEMAND summary q5:

```text
forward:  arg0.[all-fields]/{g}(U) →must ret.[any](T)   DEMAND      selected (§I.10)
demand edge in backward run n:   entryDemand = ret.[any](T)     from the MAY conclusion
                                 exitDemand  = arg0.[any](U)    from the must premise; {g} dropped
```

| Ex | Side | backward fact | Result | Rule | Status |
| --- | --- | --- | --- | --- | --- |
| dm1 ✓ | entry: emission (§I.4) | requirement `ret.f.$(T)` NORMAL | premise `ret.f.$(T)`, start NORMAL | added below `[any]` | **CURRENT** |
| — | entry | requirement `ret.[any](T)` DEMAND | may `[any]` premise, start DEMAND | e2 type | **CURRENT** |
| dm2 ✓ | entry | requirement `ret.[any-field]/{h}(T)` NORMAL | must premise `ret.[any-field]/{h}(T)`, start NORMAL | added at `[any]`, field added fact | **NEW** (B1) |
| dm3 ✓ | exit: restriction (§I.6) | conclusion `arg0.g.$(U)` NORMAL | `arg0.g.$(U)` NORMAL | below `[any]`: kept, although the forward premise excluded `g` | **CURRENT** |
| dm4 ✓ | exit | conclusion `arg0.[any-field]/{h}(U)` NORMAL | `arg0.[any-field]/{h}(U)` NORMAL | at, `[any]` demand keeps `{h}` | **NEW** (B1) |
| dm5 ✓ | exit | conclusion `arg0.g.$(T)` NORMAL | none | the marks do not meet | **CURRENT** |
| dm6 ✓ | exit, with exitDemand `arg0.*/{g}(U)` | conclusion `arg0.g.$(U)` NORMAL | none | the exclusion kept | not proposed |

* The MAY entryDemand does not make a NORMAL requirement DEMAND (dm2), and
  the must exitDemand does not make a backward conclusion a field tail
  (dm3). Only the backward facts and the rules of §I.7 decide the result.
* The hand-off drops `{g}`, so the cut keeps more pairs than the exact
  intersection (dm3). This is sound. Keeping the exclusion (dm6) is
  narrower; it is not proposed: it can remove demand, a result change
  outside B1–B4.
* The opposite case, entryDemand from a field conclusion: a backward
  zero-premise summary `zero → arg0.[any-field](T)` (q3) gives forward run
  `n+1` the entryDemand `arg0.[any](T)`. A forward field added fact
  `arg0.[all-fields](T)` then gets a must premise (e5). **CURRENT** rule.

### II.8 Applying backward summaries and records

> The backward run applies callee summaries and records by §I.7 (backward
> run table). For the backward must records (shapes s3, s9) this is **NEW**
> (B2).

| Ex | requirement | backward summary | Shape, reader | Result | Status |
| --- | --- | --- | --- | --- | --- |
| a7 ✓ | `ret.[any-field](T)` NORMAL | `ret.[any-field](T) →must arg0.[any-field](T)` NORMAL | s9, `X ⊆ R` | `arg0.[any-field](T)` NORMAL | **NEW** (B2) |
| a8 ✓ | `ret.f.[any-field](T)` NORMAL | as a7 | s9, `X ⊄ R` | `arg0.[any](T)` DEMAND | **NEW** (B2) |

In a8, the summary gives each `arg0` location SOME target under `ret`; that
target can be outside `ret.f`.

### II.9 Reading forward records

> A requirement at the forward exit of a method reads the forward records
> of that method: §I.8 cases 1, 2 and 2' (examples v1, v2, v3, v6). Case 1
> is **CURRENT**; cases 2, 2' are **CHANGED** by B4: the result is a NORMAL
> foreign `[all-fields]` requirement (§II.12), not `[any]` DEMAND.

### II.10 ND refinement (B3)

> An ND `[any]` literal is seeded with its meets with the captured inputs
> of forward run `n−1`, not with the whole literal. **NEW**.

```text
refinedSeeds(literal) =
  { meet(input, literal) | input ∈ captured(literal) } minus none     if captured(literal) ≠ ∅
  { literal }                                                        if captured(literal) = ∅   (fallback)
meet: the concrete row of §I.4
each seed DEMAND (W6: a field-tail meet becomes [any], its exclusion forgotten)
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
| n2 ✓ | 1: `b.g.[all-fields]/{k}(U)` | `a.$(T)` (fallback), `b.g.[any](U)` DEMAND | the code forgets `{k}`; the model keeps it | **NEW** |
| n3 ✓ | none | `a.$(T)`, `b.[any](U)` DEMAND | the fallback | **CURRENT** except the K3 layer |
| n4 ✓ | 1: `b.f.*/{}(*)`, not in normal form | `a.$(T)` DEMAND only | literal 1 gets no seed: the normal form is necessary | excluded by the **NEW** normal form |

Not selected: B3-P (fallback = the previous seed, and each seed met with
it). It is monotone by construction, but it keeps seed state across runs and
can remove a demand that the CURRENT behaviour keeps (S-H6).

### II.11 Hand-off of backward summaries and D1

> The selection rule of §I.10 decides which backward summaries give demand
> to forward run `n+1`. With B2 a backward must summary is a NORMAL
> singleton, so F77 does not select it. This can lose a confirmation.
> **OPEN** (D1).

```text
CURRENT   backward NORMAL non-zero singleton summaries: records, not selected; zero-premise summaries: selected
B2 + F77  selected(backward: premise →must conclusion NORMAL) = false
          ⇒ run n+1 does not analyse the callee again; it reads only the record (§I.8 case 3)
```

Counterexample `BackMustView.Cex.cex_drop_forward_demand`:

```text
callee:      ret.f.g = arg0;        sink rule ContainsMarkOnAnyField(ret, T) on the call result
caller fact: arg0.h.$(T) NORMAL enters the callee
forward run 1, field limit 1:                          ret.f.[any](T) DEMAND     → provisional, DEMAND witness
backward run 2 (B1, B2):   record  ret.[any-field](T) →must arg0.[any-field](T) NORMAL;  F77: not selected
forward run 3, field limit 3, CURRENT callee demand:   ret.f.g.h.$(T) NORMAL     → CONFIRMED
forward run 3, field limit 3, H1, without B4:          ret.[any](T) DEMAND       → stays provisional
forward run 3, field limit 3, H1, with B4 and D2:      ret.[any-field](T) NORMAL → satisfies the literal (§I.2): CONFIRMED,
                                                       if its trace builds (S-H8); argued, not proved in the run model
```

Only a backward must record has this defect. A forward must record goes to
the backward run, which confirms nothing; a record with a `$` premise gives a
native `$` result (cases 1, 4). B4 removes the known H1 counterexample, but
H1 still needs the shadow check below: the CURRENT callee analysis can give
a NORMAL fact that a later step needs and that a foreign `[any-field]` fact
loses at a narrowing step (§I.9).

| Option | selected(backward must summary) | Results | Demand rows removed | Status |
| --- | --- | --- | --- | --- |
| H1 omit | false (F77 unchanged) | without B4: can lose a confirmation; with B4: the known case kept, others not proved | yes | **OPEN** |
| H1g omit if covered | true, unless a NORMAL, pair-exact, complete forward record of the callee covers the conclusion | kept (`BackMustView.guard_keeps_normal`, canonical FLOW records; `Cex.guard_instance`) | few: F77 already drops that demand | **OPEN** |
| H2 select | true | kept, except S-H1 | none | **OPEN** |
| H3 forward MUST meet | false, and a new forward rule: a forward "some location" fact, or a confirmation where a forward NORMAL fact meets a backward MUST requirement, with a trace | B4 with D2 is the first variant of H3 | yes; changes the forward run, the sink check, trace resolution | **OPEN**: B4 + D2 is now the concrete design |

Recommendation: prototype B1 + B2 + B3 with H2, and log in shadow mode the
callee demands that H1 would drop, and whether the CURRENT forward run gets a
NORMAL callee summary under them that B4 does not give. No case on all
projects and suites ⇒ gate H1. A case ⇒ withdraw H1.

| Ex | summary | selected | Run `n+1` (forward) | Status |
| --- | --- | --- | --- | --- |
| q3 | `backward: zero → arg0.[any-field](T)` NORMAL | yes | demand edge `(arg0.[any](T), zero)` | **CURRENT** rule |
| q4 | `backward: ret.[any-field](T) →must arg0.[any-field](T)` NORMAL | F77: no | H1: no callee demand, only the record (v4); H2: demand edge `(arg0.[any](T), ret.[any](T))` | **OPEN** |

### II.12 Foreign backward requirements and D2

> B4 makes backward `[all-fields]` requirements (§I.8 cases 2, 2'): "taint
> at every location of the set fires the sink". The statement needs the
> whole set, so a step that splits the set breaks it. D2 (§I.9) decides
> their transfer. **OPEN**.

Backward steps under option D2-a (walked backward):

| Step | `[any-field]` (native, B1) | `[all-fields]` (foreign, D2-a) |
| --- | --- | --- |
| a statement that writes no location of the set | kept | kept |
| a write that replaces the whole set from one source (`x.p = y.q`; `x.f = y` for a set at `x.f.q`; `x = y.f`) | the source path with `[any-field]/E` | the source path with `[all-fields]/E` |
| a store into part of the set, `x.p.f = y` with `E` admitting `f` (t1) | `y.[any-field]`, `x.p.[any-field]/(E ∪ {f})` | `y.[any]`, `x.p.[any]` DEMAND: the condition is a conjunction of two facts (`Cex.all_req_not_sub`) |
| emission: added at or added below, `[any]` entryDemand | the premise is the fact (dm2) | the premise is the fact; start NORMAL |
| emission: added above, `$` or `*/E2` entryDemand; restriction at a deeper or `$` exitDemand | narrower, NORMAL | DEMAND |
| source hit by a source fact `s` | `impl(s, requirement)`: `s` overlaps the set | `impl(s, requirement)`: only an `[all-fields]` source that covers the set |
| reversed conditional source (S2–S5) on the requirement target | as §II.4 | NORMAL only if impl(target fact, requirement) and the literal is unary; else DEMAND |
| reader in §I.7 | column `[any-field]` | column `[all-fields]` |
| hand-off pattern | `[any]`, `E` dropped | the same |

The options D2-a, D2-b, D2-c are in §I.9; the same option applies to both
foreign kinds.

### II.13 Semantic scope

> What the proposal changes, what it keeps, which documented invariants
> change, and the changes that are not yet proved or measured.

| Change | Rows | Status |
| --- | --- | --- |
| `[any-taint]` named `[all-fields]` (forward) and `[any-field]` (backward) | §N.1 | **CURRENT** (names only) |
| unary `[any]` sink seed: `[any]` DEMAND → `[any-field]` NORMAL | K2 | **CHANGED** |
| ND `$` sink seed: NORMAL → DEMAND (user correction, 26 Nov) | K3 | **CHANGED** |
| reversed unary `[any]` source literal: `[any]` DEMAND → `[any-field]` in targetLayer | S3 | **CHANGED** |
| caller results through C2/C3 records: DEMAND → NORMAL | C2, C3 | **CHANGED** |
| forward must records read by the backward run: `[any]` DEMAND → `[all-fields]` NORMAL | §I.8 cases 2, 2' | **CHANGED** (B4) |
| backward field added fact, must premise, NORMAL start | C1 | **NEW** |
| backward records with a field premise or leaf; their application in both runs | §II.6, §II.8, §I.8 cases 3, 3', 4 | **NEW** |
| foreign kinds: forward `[any-field]` facts, backward `[all-fields]` requirements; sink check and source hit with them | §I.2, §I.9, §II.12 | **NEW**, transfer **OPEN** (D2) |
| ND `[any]` seeds and reversed ND `[any]` literals refined; capture | K4, S5, §II.10, §I.3 | **NEW** |
| hand-off of a backward must record | §II.11 | **OPEN** (D1) |

Unchanged (**CURRENT**): the forward run except §I.2 (foreign row), §I.3,
§I.8 and §I.9 (transfer, sink check for native facts, layers, records, case
1, confirmation, traces); the native field tails and W6; S4, S5 layer, S7;
unary `$` seeds (K1); zero rows; source hits of native requirements; C4, C5;
the operations of §I.4, §I.6 for the native kinds; the use rule of §I.7; the
results of §I.7 for the edges that the CURRENT code applies, except §I.8
cases 2, 2'; the demand patterns of §I.10; field limits and FL+1 caps;
confirmed and provisional results (the gate).

| Documented invariant | Change |
| --- | --- |
| interpreter.md I11 (f), I14 ("the backward run has no `[any-taint]`"), §4.9 | K2, S3; "no micro edge has a premise with a field tail" stays |
| `MicroEdge.kt:23-25` A1 | a reversed micro edge can have a field target (S3), never a field premise |
| ap.md §4.2 (a NORMAL `[any-taint]` fact: every covered location carries the mark) | also a foreign forward fact "some covered location" (§I.9) |
| ap.md §6.5 ("the backward run has no `[any-taint]` premise") | C1 |
| ap.md §9.2 ("an `[any]` seed is demand-layer") | a seed is NORMAL ⇔ its literal is unary (K1–K4) |
| ap.md §8.7 R1, `RecordStore.kt:274-277` | §II.6 |
| ap.md §8.7 R3 (the view result of a must record is `[any]` DEMAND; the view is for forward records) | B4: the premise kind, NORMAL if implied; also backward records (§I.8) |
| ap.md §8.7 R4, MUST rule | the special case s4, s5 of §I.7 |
| ap.md §9.1 backward W6 | applies only to the MAY class and to `[any]` results not made by B1 or B4 |
| ap.md §8.5 F77 | H1: none; H1g, H2: one condition |
| Lean iteration theorems (`Backward.B_general`, `W6.iteration_general6`, `Handoff*`) | not proved again with B2 records or B4 results; `Handoff.CrossK .any = False`, so `Handoff.demOfN` hands a must record off (= H2) |

| Hidden-change candidate | Rule | Evidence |
| --- | --- | --- |
| S-H1 strong-update exclusion: a backward `[any-field]/E` gets an exclusion, `[any]` DEMAND does not (t1, t2); the forward demand can get narrower | B1 | base model: same facts (`W6.D6_same_shape`, `summaryDemand_iff`); refined model: not proved; shadow-compare the normalized pieces |
| S-H2 EXACT cleaner on a field leaf (`Clean.kt:187-192`) now runs backward | B1 | not modelled |
| S-H3 a must premise and a may `[any]` premise at one path are separate keys | B1 | cost only |
| S-H4 MUST is relative to `positive(condition)` | B1 | the forward run uses it too |
| S-H5 B1 under-approximates MUST (`nd_overlap_suff`) | B1 | sound |
| S-H6 refined seeds narrow the forward demand | B3 | not proved; measure |
| S-H7 new record shapes `(backward, field premise or leaf)` | B2 | no dedup change for the existing shapes |
| S-H8 traces through a record of the other direction (§I.8 cases 2, 3, 4), now with NORMAL results | B2, B4 | not modelled; check in the prototype |
| S-H9 the callee summaries of an ND `$` seed become DEMAND: no backward `$` record, selected rows (q2 type) instead of the exact view; forward run `n+1` analyses those callees under a `$` demand | B1 (K3) | results expected equal, not proved; more rows per backward run while the witness is DEMAND; measure |
| S-H10 a foreign forward `[any-field]` fact confirms a `ContainsMarkOnAnyField` sink that is provisional today: a result change | B4, D2 | not measured; the gate fails on each such case |
| S-H11 a NORMAL backward `[all-fields]` requirement (cases 2, 2') replaces a DEMAND `[any]` one: caller summaries can become records and leave the hand-off (F77), so forward run `n+1` gets less demand and can lose a confirmation (the D1 class) | B4 | not proved; shadow-compare the hand-off rows |

### II.14 Proofs and model notes (backward)

> Where the backward claims are proved, the hypotheses, and where the model
> differs from the code.

| Claim | Lean |
| --- | --- |
| a NORMAL result of the backward transfer is a forward refined result | `BackMust.transferXB_normal` |
| K2 seed is NORMAL; bound: field added fact; must premise with NORMAL start; CURRENT: DEMAND start | `must_seed_normal`, `bindX_star_any`, `must_seed_bound`, `must_premise_normal`, `demand_seed_contrast`, `demand_premise_start` |
| each NORMAL backward summary with a non-zero premise is pair-exact (may) or end-exact (must) on `reverse(P)` | `DBX_edgeOK_nz`, `edge_exactBX_gen`, `no_zero_summaryX` |
| backward records are exact, also over a run sequence | `recsB_exact`, `recsB_must_end`, `recsB_pair`, `recsB_next`, `recsBSeq_ok` |
| in `P`: each location of the conclusion flows forward to some location of the premise (must), each pair is a forward flow (may) | `backMust_forward`, `backPair_forward`, `backMust_forward_valid`, `backMust_forward_seq` |
| backward records are the valid edges s3, s7, s9 | `BackView.bwd_pair_valid`, `bwd_must_valid` |
| §I.8 case 4: the forward result is exact | `BackView.backExactView_forward` |
| §I.8 cases 2, 3 with B4 | `BackView.fwdMust_backward_normal`, `backMust_forward_normal` |
| foreign kinds and narrowing | `FieldQuant.Cex.any_not_sub`, `any_not_kill`, `all_req_not_sub` |
| S3 is MUST for each target kind; S4, S7 are not MUST, sound MAY | `BackCond.rev_unary_source_must`, `rev_nd_source_not_must`, `rev_pass_any_not_must`, `rev_pass_may_sound` |
| the seed layer is the MUST status (B1, K3 included) | `BackCond.reqs_normal_must`, `reqs_nd_demand` |
| D1 counterexample and H1g guard | `BackMustView.Cex.cex_drop_forward_demand`, `guard_keeps_normal` |

Hypotheses of `DBX_edgeOK_nz`, `bwd_pair_valid`, `bwd_must_valid` and
`backExactView_forward`: those of `DRX_edgeOK` on `reverse(P)`, plus
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
* The run models (`DRX`, `DBX`) have no foreign fact and no B4 result: B4 is
  proved per edge (`FieldQuant` with the `BackView` bridges), not over a run.
* Not modelled: S-H2, GROUP projection, end-fact triggers, statics.

## Gate and checklist

> The acceptance test of each rule, the withdrawal conditions and the state
> of the proposal against spec/proof-guide.md.

Gate per rule, alone, per project (OWASP, Stirling-PDF, Conductor,
ThingsBoard) and the module, jvm and rule suites: identical confirmed and
provisional results; wall time and peak memory not worse. Withdraw a rule
that fails. H1: withdraw also on one shadow case (§II.11). B3: withdraw also
if the capture makes peak memory worse. B4: withdraw also on one S-H10 or
S-H11 case.

```text
[x] Failure class and real trace        §II.1 (per-run counts not measured)
[ ] Ablation                            not done (spec only)
[ ] Native prototype                    not done (spec only)
[ ] Execution site and measured volume  sites: seeds per run, transfer per backward fact, records per barrier,
                                        replay per call offer, capture per completed combination,
                                        foreign facts per run; volumes not measured
[x] Semantic scope                      §II.13; D1, D2 open
[x] Proof scope, model vs production    §I.11, §II.14
[x] Withdrawal condition                this section
[ ] WI classification                   none
[x] Proofs                              Notation, Part I, Part II
```

Blind spots: nothing ran natively; with H2, B1 and B2 remove no forward
row; the H1 risk is a reduction, not a measured case; the D2 rows are proved
at the location-set level only; S-H1, S-H2, S-H6, S-H8, S-H9, S-H10, S-H11
and the capture heap cost are not measured.
