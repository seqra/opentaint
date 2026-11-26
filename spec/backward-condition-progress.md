# Backward condition progress: refined MAY seeds

26 November 2026, branch `saloed/bidirectional`. **Spec and proofs only**
(user decision): no ablation, no prototype, no measurement, no WI rule.

**Landed** (26 November 2026): R1, the seed layer (§II.2), in `4af723e80`;
R2, the capture tree and the refined seeds (§I.3, §II.4), in `ba69bbb72`.
Implementation: [backward-condition-progress-implementation.md](backward-condition-progress-implementation.md).
Measurement: [bidirectional-backcond-landing-20261126.md](../docs/reports/bidirectional-backcond-landing-20261126.md).
No confirmed or provisional result changed on the four projects. The
example PG of §I.2 does not need R2 in the code (see the note in §I.2).

## Overview

> The backward run seeds requirements from the rule conditions of
> provisional findings. Today the seed of an `[any]` literal is the whole
> literal in every run. It gives the next forward run the same shallow
> `[any]` demand, the forward run cuts the fact one field below it again,
> and the finding stays provisional (§II.1). This spec keeps the backward
> run MAY for `[any]` literals and makes the seeds follow the forward facts,
> so each round asks one field deeper (§II.5).

**Parts.**

* [Notation](#notation): the names that both parts use. No run behaviour.
* [Part I, forward run](#part-i-forward-run): the sink check, the cut that
  keeps the finding provisional, and the new capture tree.
* [Part II, backward run](#part-ii-backward-run): the seed layer, the
  refined seeds and the progress guarantee.
* [Gate and checklist](#gate-and-checklist).

**Status labels.** Each rule, table row and example table has one.

| Label | Meaning |
| --- | --- |
| **CURRENT** | `saloed/bidirectional` does this today (source: ap.md, interpreter.md, acyclic-convergence-proposal.md, or the cited code) |
| **CHANGED** | the proposal replaces a CURRENT behaviour; the row gives the CURRENT behaviour too |
| **NEW** | the proposal adds this behaviour; it replaces nothing |

**Proposed rules.**

| Rule | What it does | Where | Status |
| --- | --- | --- | --- |
| seed layer | a requirement is NORMAL if and only if its literal is unary and has the `$` tail. An ND `$` literal gives DEMAND. An `[any]` literal gives DEMAND, as today: the backward run has no `[any-taint]` | §II.2 | **CHANGED** (ND `$` only) |
| capture tree | for each `[any]` literal at a DEMAND witness or a conditional source, the forward run stores one merged field tree: the meet of each input with the literal, as a `$` leaf or an `[any]` leaf. No `$` or `[any-taint]` fact is stored | §I.3 | **NEW** |
| refinement | each `[any]` literal of a sink (unary or ND) and of a reversed conditional source is seeded with its capture tree, as one DEMAND tree fact | §II.4 | **CHANGED** (the seed shape) |
| progress guarantee | each leaf lies inside its captured input and keeps its path, so the next demand is at least as deep as the forward cut | §II.5 | proved per operation; argued over rounds |

**History.** Earlier revisions (commits 531e87d3c to fddd06d8d) made the
seed of a unary `[any]` literal a NORMAL `[any-taint]` requirement and
added backward MUST records, application by implication, two field tails
and decisions D1, D2. The user withdrew them on 26 November: too complex.
Their Lean modules (`BackMustRun`, `BackMustView`, `BackRecordViews`,
`FieldQuant`) are removed; they stay in the git history.

**Lean.** [BackCondRules](lean/ApSpec/BackCondRules.lean) (`BackCond`),
[BackNDRefine](lean/ApSpec/BackNDRefine.lean) (`BackND`),
[BackCondExamples](lean/ApSpec/BackCondExamples.lean) (`BackCondEx`),
[BackCondImpl](lean/ApSpec/BackCondImpl.lean) (`BackCondImpl`, the
implementation level).
All constructive (`propext`, `Quot.sound` only).

**Examples.** Bases `x ret arg0 a b`, fields `f g h k`, marks `T U`. An
example id with ✓ (for example `p1 ✓`) is the Lean theorem
`BackCondEx.ex_p1`: the executable model computes the result shown, checked
by `decide`.

## Notation

> Locations, patterns, layers, rule conditions and demand edges. Part I and
> Part II give the run behaviour. All of it is **CURRENT**.

### N.1 Locations, patterns and layers

```text
location        base.path(mark)                  a value: base variable, field path, concrete taint mark
pattern         base.path.tail(mark)             a fact, a requirement, a literal, a captured input, a demand
  tail            $                 the location base.path
                  [any-taint]/E     NORMAL: base.path·suffix for each suffix that E admits; each carries the mark
                                    (forward run only: interpreter.md I14, ap.md S15)
                  */E               FLOW: base.path·suffix, correlated with the premise suffix
                  [any]             MAY: covers the locations that can carry the mark (DEMAND only, W6)
  mark            T                 a concrete mark;    * abstract (FLOW)
E               an exclusion: a set of fields;  admits(E, suffix) ⇔ suffix = [] ∨ first(suffix) ∉ E
depth(pattern)  the number of fields in its path (FL in acyclic-convergence §2)
layer           NORMAL | DEMAND;   join: NORMAL ⊔ NORMAL = NORMAL, otherwise DEMAND
covered(pattern) the location set;  inside(pattern1, pattern2) ⇔ covered(pattern1) ⊆ covered(pattern2)

NORMAL forward fact          no operation of its derivation over-approximated
NORMAL backward requirement  MUST: taint at each covered location fires the seeded sink
DEMAND backward requirement  MAY: the DEMAND requirements cover each location of a real route to the sink
```

### N.2 Rule conditions

> Literals, alternatives, and the classification of a literal as unary or ND.

```text
literal              ContainsMark(P, T) is P.$(T);  ContainsMarkOnAnyField(P, T) is P.[any](T)
positive(condition)  the condition with each negated literal replaced by true, in DNF:
                     a set of alternatives, each alternative a set of literals
fires(condition, taintedLocations)  ⇔  ∃ alternative ∈ positive(condition). ∀ literal ∈ alternative.
                                         some location of taintedLocations is covered by literal
sufficient(condition, location)     ⇔  fires(condition, {location})
unary literal        {literal} ∈ positive(condition)            code: RulePredicate.isUnary (RulePredicate.kt:199-201);
                                                                legacy sink with one pattern
ND literal           literal ∈ alternative, |alternative| ≥ 2   code: RulePredicate.isMulti; legacy sink with ≥ 2 patterns
```

A literal can be unary and ND (row K5).

| Claim | Lean (`BackCond`) |
| --- | --- |
| unary literal ⇒ each covered location is sufficient (also `[any]`) | `unary_seed_must`, `any_seed_exact` |
| ND literal only ⇒ some covered location is not sufficient | `nd_suff_iff`, `nd_seed_not_must` |
| each location of a minimal firing set is covered by some literal (MAY cover) | `seed_may_cover`, `core_spec` |
| sufficiency uses `positive(condition)`, not the signed condition | `firesS_proj`, `signed_not_must` |

| Ex | condition | taintedLocations | fires | Consequence |
| --- | --- | --- | --- | --- |
| c1 ✓ | `ContainsMarkOnAnyField(ret, T)` (unary) | `{ret.f(T)}` | yes | `ret.f(T)` is sufficient |
| c2 ✓ | `a.$(T) ∧ b.[any](U)` (ND) | `{b.f(U)}` | no | `b.f(U)` is not sufficient: both seeds are MAY |
| c3 ✓ | as c2 | `{a(T), b.f(U)}` | yes | `b.f(U)` is on a route: the seeds must cover it |

### N.3 Demand edges and the start cap

> The backward run hands demand edges to the next forward run. The forward
> run starts a callee fact only as deep as the demand allows (C2).

```text
demand edge of a method = (entryDemand, exitDemand)       patterns with no layer and no field tail (W8 (d))
  made from the selected summaries of the backward run (ap.md §8.5)
C2   a start under entryDemand has a depth of at most min(K, depth(entryDemand) + 1)      acyclic-convergence §2
     a deeper actual fact is cut: a STAR start with the concrete mark, DEMAND
C5   a conclusion against exitDemand is cut at min(K, depth(exitDemand) + 1)             acyclic-convergence §2
K    the field limit of the run; it grows from run to run
```

The relative caps of C2 and C5 stay (robustness rule, acyclic-convergence
§0): a deep fact waits for a demand that asks for it.

## Part I. Forward run

> The forward run checks the sinks and reports provisional findings. A cut
> at a callee entry makes a fact DEMAND and keeps the finding provisional.
> The proposal adds the capture tree of `[any]` literals (§I.3).

### I.1 Sink check and DEMAND witnesses

> **CURRENT** (ap.md §9.2).

```text
at a sink statement of method, for each occurrence of the rule:
  fires(condition, the facts at the statement)      a fact satisfies a literal if they overlap
  some firing combination with only NORMAL facts  ⇒  CONFIRMED finding
  otherwise                                        ⇒  provisional finding; DEMAND witness (method, statement, occurrence)
the next backward run seeds each DEMAND witness (§II.3)
```

### I.2 The cut below an `[any]` entry

> An `[any]` entryDemand has depth 0 below its path. C2 then starts a
> deeper actual fact one field below the entry, as a DEMAND STAR start. The
> fact at the sink is DEMAND, whatever K is. acyclic-convergence §7 item 2
> calls this the "DEMAND STAR start" anchor. **CURRENT**.

Running example, program PG:

```text
main():   v = source()      the source taints v.f.g (T): forward fact v.f.g.$(T) NORMAL
          use(v)
use(x):   sink(x)           rule ContainsMarkOnAnyField(x, T): unary
```

| Run | Demand of `use` | Start in `use` | Fact at `sink(x)` | Finding | Status |
| --- | --- | --- | --- | --- | --- |
| 1, K = 1 | none (run 1) | `x.f.[any](T)` DEMAND: K cut | `x.f.[any](T)` DEMAND | provisional | **CURRENT** |
| 3, K = 3 | `(x.[any](T), zero)` from the seed of run 2 | `x.f.*(T)` DEMAND: C2 cut at depth 1 | `x.f.[any](T)` DEMAND | provisional | **CURRENT** |
| 5, 7, … | the same | the same | the same | provisional | **CURRENT**: no progress |

**Measured in the code (26 November 2026, landing report §6.2).** The table
above does not hold for PG. Run 1 starts `use` with the abstract `x.*`
(depth 0). Under the demand `x.[any](T)`, the later forward starts follow
the field-limit schedule, not a cut at depth 1: run 3 starts at `x.f.*`,
run 5 at `x.f.g.*`. So CURRENT (R1 without R2) confirms the finding of PG
at run 2d+1, the same run as R1 + R2 (`RefinedSeedIterationTest`). A
program where the C2 cut binds is not known yet (next iteration, B1).

### I.3 Capture tree (NEW)

> For the refinement, the forward run keeps the part of each input that the
> `[any]` literal needs. It meets the input with the literal first, and it
> stores the meet as a leaf of one field tree per literal. The next
> backward run seeds that tree (§II.4). **NEW**.

```text
occurrences   each DEMAND witness (sink literals, K2, K4);
              each occurrence of a conditional source with an [any] literal (S3, S5)
inputs        each input that satisfied the literal in a COMPLETED combination (NORMAL or DEMAND) of the occurrence

for each input:
  normal form   mark := the concrete mark that the check matched     (only TaintTree inputs: a FLOW fact never satisfies a literal)
                each field tail ([any-taint]/E, */E, [any]) := [any], E dropped;   $ stays $
  meet first    leaf := meet(normal form, literal)                   (§II.4 table: below, at, above)
                the leaf is base.literalPath·σ with the tail $ or [any] and the mark of the literal
  one tree      tree(literal, occurrence).insert(σ, tail of leaf)
                an [any] leaf at σ subsumes each leaf at σ·τ (τ = [] included); an equal leaf is kept once
```

Rules of the capture tree (user decisions, 26 November):

| Rule | What it does | Why | Status |
| --- | --- | --- | --- |
| meet first | store `meet(input, literal)`, not the input | keeps only the part inside the literal | **NEW** |
| leaves only | no `$` or `[any-taint]` fact is stored: a `$` meet is a `$` leaf, a field meet an `[any]` leaf | the backward run has no `[any-taint]`; a `$` or `[any-taint]` input can be the only real route, so it stays as a leaf (dropping it loses the route: the next forward run gets no demand for it) | **NEW** |
| one tree | merge the leaves of a literal into one field tree | all leaves of a literal have the base and the mark of the literal and a path below the literal path (`RCore.emitM_base`, `emitM_mark`, `BackND.meet_deepens`); only the field tree differs | **NEW** |

Dropping the exclusion before the meet gives the same leaf as dropping it
after the meet, for each input that satisfied the literal (an input whose
exclusion rejects the literal path does not overlap the literal). The Lean
model drops it after the meet (`BackND.capMeets`).

| Part | Status |
| --- | --- |
| completed combinations: `CompletePredicateBinding(proof, layer, leaves, inputs)` (`RulePredicateStore.kt:99-104`), legacy `ConjunctionStore.CompleteBinding` | **CURRENT** |
| the tree: a `TaintTree` (`Conclusions.kt:44`) with `TaintLeaves(exact, any)` at each node (`Trie.kt:19`): `$` leaves and `[any]` leaves of one mark | **CURRENT** representation |
| keep one tree per (occurrence, literal) after `freeze()` as a hand-off side table, outside `Seed` equality | **NEW** |
| insert from ALL completed combinations, not only the selected proof (`BackND.Vec.cex_selected_only`) | **NEW** |
| the normal form: only a `TaintTree` input is stored. A FLOW fact never satisfies a literal (implementation proposal F4), so it is never the input of a completed combination; an abstract-mark input gives no leaf (`BackCondEx.ex_t6`, `BackCondImpl.Vec.flow_none`), and the capture is concrete (`BackND.CapConc`, a hypothesis of `BackCondImpl.codeSeeds_sound`) | **NEW** |
| only `[any]` literals: the seed of a `$` literal is the literal | **NEW** |

| Ex | literal | inputs | stored leaves → merged tree | Rule |
| --- | --- | --- | --- | --- |
| t1 ✓ | `x.[any](T)` | `x.f.g.$(T)`, `x.h.[any-taint]/{g}(T)` | `x.f.g.$`, `x.h.[any]` | meet first; leaves only (`{g}` dropped) |
| t2 ✓ | `x.f.[any](T)` | `x.[any](T)` | `x.f.[any]` | meet first: an input above the literal gives the literal path |
| t3 ✓ | `x.[any](T)` | leaves `x.f.[any]`, `x.f.g.$`, `x.h.$` | `x.f.[any]`, `x.h.$` | one tree: `x.f.[any]` subsumes `x.f.g.$` |
| t4 ✓ | `x.[any](T)` | leaves `x.g.$`, `x.g.$` | `x.g.$` | one tree: an equal leaf once |

| Claim | Lean (`BackND`) |
| --- | --- |
| the merged tree serves exactly the locations of its leaves: merging loses nothing and adds nothing | `mergeLeaves_cov`, `insertLeaf_cov`, `subsumes_cov` |
| each leaf of the merged tree is a stored meet; at most one leaf per stored meet | `mergeLeaves_sub`, `mergeLeaves_length` |
| each real route location of the literal is served by a leaf | `tree_sound` |

In PG, forward run 1 stores the tree `{f: [any]}` below `x` for the
literal `x.[any](T)`.

## Part II. Backward run

> The backward run starts at the DEMAND witnesses of the previous forward
> run and walks `reverse(P)`. It hands demand to the next forward run. The
> seed layer and the refinement are in this part.

Run numbering: run `n` is the backward run; run `n−1` is the forward run
before it; run `n+1` is the forward run after it.

### II.1 Problem

> Why the backward run does not progress today. **CURRENT** behaviour.

The seed of an `[any]` literal is the whole literal, in every run. It does
not read the forward facts. In PG, backward run 2 seeds `x.[any](T)`. The
backward summary of `use` is `zero → x.[any](T)`, which is selected, so
forward run 3 gets the demand edge `(x.[any](T), zero)`. C2 cuts the actual
fact one field below it (§I.2), the witness stays DEMAND, and backward run
4 seeds `x.[any](T)` again. The rows of `use` never go to zero, so
requirement AC (acyclic-convergence §1) fails for `use`.

| Real instance (after AO-C5) | Demand rows | Source |
| --- | --- | --- |
| Stirling-PDF `AuthController#login` and its entry point | 1 + 2 | acyclic-convergence §6, §7 item 2 |
| Stirling-PDF `bytesToWebResponse` arms | not counted | natural-termination §3 |

Not measured: the rows per run from `[any]` seeds and from reversed `[any]`
literals.

### II.2 Seed layer

> A NORMAL requirement must be MUST. The backward run has no
> `[any-taint]`, so only a `$` requirement can be NORMAL, and only a unary
> literal is MUST. **CHANGED** for ND `$` literals only.

```text
layer of the requirement from a literal:
  CURRENT   NORMAL ⇔ literal.tail = $                  seedFact (RunMethodLocalServices.kt:437-449); W6 makes [any] DEMAND
  NEW       NORMAL ⇔ literal is unary ∧ literal.tail = $
```

| Literal | CURRENT requirement | Proposed requirement | Status |
| --- | --- | --- | --- |
| unary `P.$(T)` | `P.$(T)` NORMAL | `P.$(T)` NORMAL | **CURRENT** |
| unary `P.[any](T)` | `P.[any](T)` DEMAND | refined seeds, DEMAND (§II.4) | **CHANGED** (shape) |
| ND `P.$(T)` | `P.$(T)` NORMAL: not MUST | `P.$(T)` DEMAND | **CHANGED** (layer; user correction, 26 Nov) |
| ND `P.[any](T)` | `P.[any](T)` DEMAND | refined seeds, DEMAND (§II.4) | **CHANGED** (shape) |

A unary `[any]` literal is MUST as a set (`BackCond.any_seed_exact`). Its
seed stays DEMAND because the backward run has no `[any-taint]`. The
refinement gives the progress instead (§II.5).

| Claim | Lean (`BackCond`) |
| --- | --- |
| a literal has a NORMAL requirement ⇔ it is unary with the `$` tail | `reqs_normal_iff` |
| each NORMAL requirement is MUST, as a seed and as a reversed source literal | `reqs_normal_must`, `reqs_normal_rev_must` |
| each literal of an ND alternative gives DEMAND | `reqs_nd_demand` |
| the requirements of both layers are a sound MAY cover; all-unary: exactly the sufficient set | `reqs_may_cover`, `reqs_unary_exact` |

| Ex | condition | requirements `(pattern, layer)` | Status |
| --- | --- | --- | --- |
| k1 ✓ | `ContainsMark(ret, T)` | `ret.$(T)` NORMAL | **CURRENT** |
| k2 ✓ | `ContainsMarkOnAnyField(ret, T)` | `ret.[any](T)` DEMAND, before refinement | **CURRENT** |
| k3 ✓ | `a.$(T) ∧ b.[any](U)` | `a.$(T)` DEMAND, `b.[any](U)` DEMAND, before refinement | **CHANGED** (`a.$(T)`) |

### II.3 Seeds and reversed rules

> The seeds of each rule literal at a DEMAND witness, and the reversed
> statement rules. The last column is what the rule reads from forward run
> `n−1`.

| # | Rule condition | Seed | Status | Input from forward run `n−1` |
| --- | --- | --- | --- | --- |
| K1 | `ContainsMark(P, T)`, unary | `P.$(T)` NORMAL | **CURRENT** | DEMAND witness |
| K2 | `ContainsMarkOnAnyField(P, T)`, unary | its capture tree, DEMAND (§II.4) | **CHANGED**: CURRENT `P.[any](T)` DEMAND | DEMAND witness and its capture tree |
| K3 | `ContainsMark(P, T)`, ND | `P.$(T)` DEMAND | **CHANGED**: CURRENT `P.$(T)` NORMAL | DEMAND witness |
| K4 | `ContainsMarkOnAnyField(P, T)`, ND | its capture tree, DEMAND (§II.4) | **CHANGED**: CURRENT `P.[any](T)` DEMAND | DEMAND witness and its capture tree |
| K5 | a literal that is unary and ND | as K1 or K2 | as K1 or K2 | as K1 or K2 |
| K6 | no positive literal; unconditional sink | none: the zero demand covers it | **CURRENT** | DEMAND witness |
| K7 | end-fact trigger of alternative `A` (row S8 fired) | K1–K4; no capture tree, so the fallback | as K1–K4 | none |
| K8 | GROUP-projected sink (`fullSinkSeedsFor`) | K1–K4; no capture tree, so the fallback | as K1–K4 | DEMAND witness |

| # | Rule | Backward result | Status | Input from forward run `n−1` |
| --- | --- | --- | --- | --- |
| S1 | unconditional source `zero → P.tail(T)` | zero; a source hit when its reversed edge applies (interpreter.md §4.9) | **CURRENT** | none |
| S2 | conditional source, unary `ContainsMark(Q, T')` | `Q.$(T')` in targetLayer | **CURRENT** | none |
| S3 | conditional source, unary `ContainsMarkOnAnyField(Q, T')` | its capture tree, DEMAND (§II.4) | **CHANGED**: CURRENT `Q.[any](T')` DEMAND | the capture tree of the source occurrence |
| S4 | conditional source, ND `ContainsMark(Q, T')` | `Q.$(T')` DEMAND | **CURRENT** | none |
| S5 | conditional source, ND `ContainsMarkOnAnyField(Q, T')` | its capture tree, DEMAND (§II.4) | **CHANGED**: CURRENT `Q.[any](T')` DEMAND | the capture tree of the source occurrence |
| S6 | pass rule `P → Q` (no `AnyField`) | the reversed result in targetLayer | **CURRENT** | none |
| S7 | pass rule `P → Q.AnyField` | each result DEMAND | **CURRENT** (outside the assumption of AC: JVM pass rules have no `[any]`) | none |
| S8 | end-fact action of sink alternative `A` | zero; fires K7 at (method, statement, `A`) once | **CURRENT** | none |
| S9 | cleaner, type filter | unchanged rule | **CURRENT** | none |

### II.4 Refinement

> An `[any]` literal is seeded with the capture tree that forward run `n−1`
> stored for it (§I.3), not with the whole literal. The seed is one DEMAND
> tree fact. **CHANGED** (was proposed for ND literals only; now for each
> `[any]` literal).

```text
seed(literal, occurrence) =
  literal.base . literalPath . tree(literal, occurrence) (mark)    one DEMAND tree fact      if the tree has a leaf
  literal                                                          (fallback = CURRENT seed)  if the tree is empty
a $ literal: the literal (no tree)
code: seedFact builds the seed from one pattern (RunMethodLocalServices.kt:437-449, ApOps.kt:169 targetTree);
      for a tree it emits the stored TaintTree in the DEMAND layer
```

The meet (**CURRENT** operation: ap.md §6.3 emission, concrete row):

| meet(input, literal), `literalPath = literal.path` | Result |
| --- | --- |
| input below: `input.path = literalPath·suffix`, `suffix ≠ []` | the input |
| input at: `input.path = literalPath` | `literalPath` with the meet of the tails (`$` if one is `$`) |
| input above: `literalPath = input.path·suffix`, and the input tail admits `suffix` | the literal |
| other path, other base, the marks differ | none |

| Ex | literal | input | meet | Case |
| --- | --- | --- | --- | --- |
| m1 ✓ | `ret.[any](T)` | `ret.f.$(T)` | `ret.f.$(T)` | below |
| m2 ✓ | `ret.[any](T)` | `ret.f.[any](T)` | `ret.f.[any](T)` | below |
| m3 ✓ | `ret.f.[any](T)` | `ret.[any](T)` | `ret.f.[any](T)` | above |
| m4 ✓ | `ret.[any](T)` | `ret.f.$(U)` | none | the marks differ |

Literals of c2: literal 0 is `a.$(T)`, literal 1 is `b.[any](U)`.

| Ex | inputs | Seeds | Note | Status |
| --- | --- | --- | --- | --- |
| t5 ✓ | 1: `b.f.$(U)`, `b.g.h.$(U)` | `a.$(T)`; tree of `b` with leaves `f: $`, `g.h: $` | two field chains replace `b.[any](U)` | **CHANGED** |
| t6 ✓ | 1: `b.f.*/{}(*)`, abstract mark | `a.$(T)`, `b.[any](U)` | not stored (the code never meets it: a FLOW fact never satisfies a literal); literal 1 keeps the CURRENT seed | **CURRENT** except the K3 layer |
| s1 ✓ | S3 literal `arg0.[any](U)`; input `arg0.h.$(U)` | tree of `arg0` with the leaf `h: $` | a reversed source literal | **CHANGED** |

| Claim | Lean (`BackND`) |
| --- | --- |
| `covered(meet(input, literal)) = covered(input) ∩ covered(literal)` for a concrete input | `meetLit_inter` |
| each real route location of the literal is served by the seed | `tree_sound` (tree), `refine_sound`, `forwardCaptured_of_combos` |
| the tree serves exactly the union of its meets; each leaf is inside its literal | `mergeLeaves_cov`, `tree_deepens` |
| the backward contract and the iteration theorem, and monotonicity in the capture: proved for the list of meets with exclusions, and for the code seeds (the merged tree without exclusions, in arrival order, with the fallback) | `B_general_refined`, `iteration_general_refined`, `refine_mono`, `refine_mono_seq`; `BackCondImpl.B_general_code`, `iteration_general_code` |
| deterministic; legal leaves (`$` or `[any]`, concrete mark); at most one leaf per stored meet | `refine_det`, `refine_legal`, `mergeLeaves_length` |
| inserting only the selected proof loses a real location | `Vec.cex_selected_only` |
| if a literal loses all its leaves, the fallback makes its seed larger | `Vec.cex_mono_fallback` |

Soundness needs leaves that serve each real route location of the
literal. The forward run over-approximates the real taint, so each real
route location at the witness is covered by an input of a completed
combination (`forwardCaptured_of_combos`). For a unary literal each
overlapping fact is a completed combination by itself. A `$` or
`[any-taint]` input can be the only real route, so it stays as a leaf
(rule "leaves only", §I.3).

Not selected: B3-P (fallback = the previous seed, and each seed met with
it). It is monotone by construction, but it keeps seed state across runs and
can remove a demand that the CURRENT behaviour keeps.

### II.5 Progress guarantee

> The seed tree follows the forward facts. Each leaf is never wider than
> its captured input and never shallower. So a field that a cut added to
> the forward fact stays in the next demand, and the next start can go one
> field deeper. Per operation: proved. Over rounds: argued.

| Guarantee | Statement | Lean (`BackND`) |
| --- | --- | --- |
| G1 inside | each leaf lies inside the captured input it comes from and inside its literal (exclusions forgotten) | `tree_deepens`, `refine_deepens` |
| G2 deeper | each leaf path extends the captured path and the literal path: `depth(leaf) = max(depth(input), depth(literal))` | `meet_deepens`, `tree_deepens`, `refine_depth` |
| G3 no constant seed | the tree is a function of the literal and of the inputs of run `n−1`; only the fallback (empty tree) is the CURRENT constant seed | `refine_det`, `ex_p0` |

Round argument (argued, not proved):

```text
round           backward run n and forward run n+1
cut point       a callee entry or exit where forward run n−1 cut the witness input: C2 or C5 at demand depth c,
                so the input carries a path of depth c+1 below the cut point
G2              the leaf keeps that path
backward run n  carries the leaf back to the cut point: the demand there has depth ≥ c+1
run n+1         the cap at the cut point is c+2: one field deeper
bound           acyclic code: the depth of real access paths is bounded (acyclic-convergence §1), and K grows
⇒               after a bounded number of rounds no cut remains on the route; the witness input is NORMAL,
                unless another maker makes it DEMAND; the finding is CONFIRMED, the witness and its seeds go away,
                and the route gives no more demand rows
```

Hypotheses of the argument: the backward transfer between the witness and
the cut point keeps the path (no MAY rule edge or DEMAND `[any]` callee
summary on the way that drops it); the witness is DEMAND only by cuts.

PG with the refinement:

| Run | Seed or demand | Start in `use` | Fact at `sink(x)` | Finding | Ex |
| --- | --- | --- | --- | --- | --- |
| 1, K = 1 | — | `x.f.[any](T)` DEMAND: K cut | `x.f.[any](T)` DEMAND; tree `{f: [any]}` stored | provisional | — |
| 2 (backward) | seed `x.f.[any](T)` DEMAND (the tree), demand edge `(x.f.[any](T), zero)` | — | — | — | p1 ✓ |
| 3, K = 3 | `(x.f.[any](T), zero)`: C2 cap 2 | `x.f.g.$(T)` NORMAL: no cut | `x.f.g.$(T)` NORMAL | CONFIRMED | — |
| 4 (backward) | no witness: no seed | — | — | — | — |

CURRENT: the seed is `x.[any](T)` in each round (p0 ✓), and the finding
stays provisional (§I.2).

| Ex | inputs for `x.[any](T)` | Seed tree below `x` | Note |
| --- | --- | --- | --- |
| p0 ✓ | none | the literal `x.[any](T)` | CURRENT seed, and the fallback |
| p1 ✓ | `x.f.[any](T)` | `f: [any]` | cut at depth 1: the leaf keeps `f` |
| p2 ✓ | `x.f.g.[any](T)` | `f.g: [any]` | a deeper actual fact (`x.f.g.h`): one round more |
| p3 ✓ | `x.f.g.h.$(T)` | `f.g.h: $` | a `$` input (DEMAND by another cause): a `$` leaf, no `[any]` entry, no C2 cut |
| p4 ✓ | `x.f.[any](T)`, `x.g.$(T)` | `f: [any]`, `g: $` | two completed combinations: one tree, two leaves |

Limits:

* The fallback seed is the CURRENT seed: K7, K8, and a literal of an
  alternative that never completed at the occurrence. For the last case,
  the forward run is sound, so no real route uses that literal there; if the
  fallback demand later makes facts that satisfy the literal, the next
  forward run captures them and the refinement takes over.
* The implementation keeps the CURRENT seed for a source literal with a
  GROUP mark in run 1, a literal with a non-empty exclusion, and the legacy
  statement conjunctions (`ConjunctiveEdge`, test-only): implementation
  proposal C7, C8.
* Other makers stay: the inside read (acyclic-convergence §7 item 1), alias
  self cycles (§7 item 3), S7, and the `[any]` result of a forward must
  record that the backward run reads (ap.md §8.7 R3, **CURRENT**).

### II.6 Semantic scope

> What the proposal changes, what it keeps, and the changes that are not
> yet proved or measured.

| Change | Rows | Status |
| --- | --- | --- |
| ND `$` sink seed: NORMAL → DEMAND (user correction, 26 Nov) | K3 | **CHANGED** |
| `[any]` sink seeds and reversed `[any]` source literals: the literal → its capture tree | K2, K4, S3, S5 | **CHANGED** |
| capture tree of `[any]` literals (meet first, leaves only, one tree) | §I.3 | **NEW** |

Unchanged (**CURRENT**): the forward run except the capture; the backward
run has no `[any-taint]` (interpreter.md I14, ap.md S15); W6; unary `$` seeds
(K1); S1, S2, S4, S6–S9; records (ap.md §8.7 R1), their application and
views (R3, R4, the MUST rule); the hand-off and its selection (ap.md §8.5,
F77); C2, C5 and the relative caps; the field limits and the FL+1 caps;
confirmed and provisional results (the gate).

| Documented invariant | Change |
| --- | --- |
| ap.md §9.2: "each literal gives its concrete sink pattern" | an `[any]` literal gives its refined seeds; an ND `$` seed is DEMAND |
| ap.md §9.2: an `[any]` seed is demand-layer | unchanged |
| interpreter.md §4.9: the reversed `[any]` literal of a conditional source gives `Q.[any](T')` DEMAND | its refined seeds, DEMAND |
| ap.md §9.1 backward W6 | unchanged; applies to the refined seeds |

| Hidden-change candidate | Rule | Evidence |
| --- | --- | --- |
| S-H1 the refined seeds narrow the forward demand (G1: inside the CURRENT demand). Forward run `n+1` analyses less; a provisional result that only the wider demand made can go away (a result change) | refinement | not proved; measure |
| S-H2 the callee summaries of an ND `$` seed become DEMAND: selected rows (q2 type) in place of records while the witness is DEMAND | seed layer (K3) | results expected equal, not proved; more rows per backward run; measure |
| S-H3 the capture keeps one merged tree per (occurrence, `[any]` literal) after `freeze()`: at most one leaf per input of a completed combination, fewer after merging | capture tree | heap cost not measured |

### II.7 Proofs and model notes

> Where the backward claims are proved, and where the model differs from
> the code.

| Claim | Lean |
| --- | --- |
| the seed layer (§II.2) | `BackCond.reqs_normal_iff`, `reqs_normal_must`, `reqs_normal_rev_must`, `reqs_nd_demand`, `reqs_may_cover`, `reqs_unary_exact`, `any_seed_exact` |
| the capture tree: merging is exact, the tree is sound (§I.3, §II.4) | `BackND.mergeLeaves_cov`, `mergeLeaves_sub`, `mergeLeaves_length`, `tree_sound` |
| the refinement on the list of meets: sound, inside, monotone, the backward contract (§II.4) | `BackND.refine_sound`, `refine_inside`, `refine_mono`, `B_general_refined`, `iteration_general_refined` |
| the progress guarantee G1–G3 (§II.5) | `BackND.meet_deepens`, `tree_deepens`, `refine_deepens`, `refine_depth`, `refine_det` |
| the examples | `BackCondEx` |
| the implementation: the code layer is the rule layer, `isUnary` is the DNF reading, the normal form, the arrival order, the code seeds (sound, inside, legal, G1, G2) and the contract | `BackCondImpl` ([implementation proposal](backward-condition-progress-implementation.md) §4.4, §5.4) |

* `BackCond` is rule-level: it does not model the propagation of a
  requirement through later reversed edges, the field limit, the cleaners,
  the mark modes of the backward run (F72) or the end-fact trigger. It
  decides the layer on `positive(condition)` in DNF; the code has an NNF
  DAG.
* `BackND`: the base model has no ND sink; each literal is its own sink.
  The ND form of the backward contract is not proved. `refine_mono` keeps
  the meet exclusions; the code forgets them.
* The capture tree is a list of leaves in the model (`BackND.Leaf`,
  `mergeLeaves`); the code holds it as one `TaintTree`. The model merges
  the leaves of all literals in one list; subsumption needs the same
  literal index, so this is the same as one tree per literal.
* The model drops the exclusion after the meet (`capMeets`); the rule
  drops it before (§I.3). For an input that satisfied the literal the leaf
  is the same.
* The backward contract (`B_general_refined`) is proved for the list of
  meets with exclusions. The code seeds (the merged tree without
  exclusions, in arrival order, with the fallback) satisfy it too:
  `BackCondImpl.seedsCover_code`, `B_general_code`, `iteration_general_code`.
* The round argument of §II.5 is not proved: the model has no multi-run
  form of C2 and C5.
* Not modelled: GROUP projection, end-fact triggers, statics.

## Gate and checklist

> The acceptance test of each rule, the withdrawal conditions and the state
> of the proposal against spec/proof-guide.md.

Gate per rule, alone, per project (OWASP, Stirling-PDF, Conductor,
ThingsBoard) and the module, jvm and rule suites: identical confirmed and
provisional results; wall time and peak memory not worse. Withdraw a rule
that fails. The refinement: withdraw also if the capture makes peak memory
worse. Expected effect, to measure: the acyclic owners whose rows come from
`[any]` seeds or reversed `[any]` literals (Stirling-PDF
`AuthController#login`) reach zero forward handoff rows (requirement AC).

```text
[x] Failure class and real trace        §II.1 (per-run counts not measured)
[ ] Ablation                            not done (spec only)
[ ] Native prototype                    not done (spec only)
[ ] Execution site and measured volume  sites: tree insert per input of a completed combination, one tree
                                        seed per (witness, literal); volumes not measured
[x] Semantic scope                      §II.6
[x] Proof scope, model vs production    §II.7
[x] Withdrawal condition                this section
[ ] WI classification                   none
[x] Proofs                              Notation, Part II
```

Blind spots: nothing ran natively; the round argument is not proved;
S-H1, S-H2, S-H3 are not measured.

**Gate result (26 November 2026, `4af723e80` R1, `ba69bbb72` R2).** Report:
[bidirectional-backcond-landing-20261126.md](../docs/reports/bidirectional-backcond-landing-20261126.md).

- Suites: module 2,807 tests, jvm 474 tests, 0 failures; rule suite in
  bidirectional mode OK 786, FP 0, FN 0, disabled 22.
- Results: identical confirmed and provisional results on OWASP,
  Conductor, Stirling-PDF (three launches); ThingsBoard has no report in
  both builds (run-1 OOM, pre-existing).
- Time and memory: a paired control on the same machine state gives the
  same engine time, heap after GC and GC time for OWASP and Conductor
  (report §4.2). R2 is at most 0.66% of the samples of a run.
- Expected effect: not shown. The demand rows of Stirling-PDF
  `AuthController#login` do not reach zero; from run 3 on the hand-off
  rows per method key are those of the parent. On PG, CURRENT already
  converges (§I.2 note).
- S-H1: no result went away. S-H2: the hand-off rows of Conductor
  differ by 0.0-1.8%, the same as two parent launches. S-H3: 10,630
  `CaptureKey` objects (0.34 MB) 10 s into OWASP run 2.
- The rules stay: no withdrawal condition occurred.
