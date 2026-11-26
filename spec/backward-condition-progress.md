# Backward condition progress: MUST requirements and refined MAY seeds

Date: 26 November 2026. Branch: `saloed/bidirectional`.

Status: SPEC AND PROOFS ONLY. The user selected this order (26 November):
"we need a spec only for now, not a prototype". So the design-guide items
"ablation", "native prototype" and "measurement" are NOT DONE (§11). No
rule of this spec is WI yet.

Lean modules (new):
[BackCondRules.lean](lean/ApSpec/BackCondRules.lean),
[BackMustRun.lean](lean/ApSpec/BackMustRun.lean),
[BackMustView.lean](lean/ApSpec/BackMustView.lean),
[BackNDRefine.lean](lean/ApSpec/BackNDRefine.lean).

## 0. Summary

A backward run evaluates the rule conditions of sinks and of conditional
sources. Today every `[any]` literal (`ContainsMarkOnAnyField`) gives a
DEMAND (MAY) requirement in the backward run, and every literal of a
conjunction (an ND rule) gives a DEMAND requirement with the FULL literal
pattern. A DEMAND requirement never makes a record. So the backward run
gives the same DEMAND rows in each iteration. The seeds and the layers of
these requirements do not depend on the facts that the forward runs found.

This spec adds three rules:

* **B1 (MUST requirement).** A literal that is alone sufficient (a UNARY
  literal) gives a MUST requirement, also with the `[any]` pattern: the
  backward counterpart of the forward `[any-taint]`.
* **B2 (backward MUST records).** A callee that a MUST requirement enters
  gets a must-premise. Its normal summaries are complete and go into the
  record store. Later backward runs apply them.
* **B3 (refined MAY).** A literal of an ND rule stays MAY. Its seed is the
  meet of the literal pattern with the forward facts that satisfied the
  literal (captured in the forward run). With no captured fact, the seed
  is the full pattern, as today.

The proofs show: B1 is MUST for unary literals (and only a MAY for ND
literals and reversed pass rules with an `AnyField` target); B2 records
are exact (end-exact for a must-premise); B3 keeps every real location,
lies inside today's seed, and does not grow while no literal loses all its
captured inputs.

**One design defect is open (§4, decision D1).** The current hand-off rule
F77 gives no callee demand for a record. A backward MUST record has only a
DEMAND forward read view. So, with F77 unchanged, B2 removes a forward
re-analysis that can CONFIRM a finding. A proved counterexample shows a
CONFIRMED result that becomes provisional. A selection condition (H2)
keeps every result, but then B1 and B2 remove no forward demand. To keep
every result AND remove the forward demand, a new forward rule (H3) is
necessary. H3 is outside the selected scope. This spec does not select
it.

## 1. Problem and real trace

The acyclic-convergence work (`acyclic-convergence-proposal.md` §4, §6,
§7 item 2) lists the maker "DEMAND STAR start from a backward MAY row":

| Project | Owner (rows after AO-C5) | Maker |
| --- | --- | --- |
| Stirling-PDF | `AuthController#login` (1) and its entry point (2) | a backward MAY row: an any-field sink seed or a reversed MAY rule edge |
| module suite | 10 fixtures | an ANY demand over a deeper NORMAL actual (not in the scope of this spec) |

`natural-termination-proposal.md` §3 also names the Stirling-PDF
`bytesToWebResponse` arms for the same maker.

The cycle, from the code:

1. A forward run reports a DEMAND witness of a sink. It adds the sink
   seeds (`RunMethodLocalServices.kt:383-389`, `HandOff.kt:221-226`).
2. The backward run seeds every positive literal pattern of the sink
   (`fireSinkSeeds`, `seedFact`, `RunMethodLocalServices.kt:409-449`). An
   `[any]` seed is DEMAND by W6 (`Reference.kt:283-286, 316, 378`).
3. A DEMAND requirement that binds into a callee gives a DEMAND added fact,
   a DEMAND start and DEMAND summaries. §8.5 selects every DEMAND summary
   for the hand-off. So the next forward run gets an ANY demand entry.
4. C2 starts a STAR fact with a concrete mark below the ANY entry. This
   start is DEMAND by itself. The forward witness stays DEMAND. Go to 1.

Steps 2 and 3 do not read any fact of the forward run. Their output is the
same in each iteration. The ND case has the same property: the seed of an
ND literal is the full pattern in each iteration.

NOT MEASURED: the number of backward rows per run that come from `[any]`
seeds, from reversed `[any]` literals and from ND seeds, on any project.
The rows of the table above are the only real instances (§11).

## 2. Current behavior

### 2.1 Literal classes

A positive literal of a rule condition is:

* UNARY: the literal alone satisfies the condition (after the projection of
  negated literals to true, as the forward run does). Production:
  `RulePredicate.isUnary(leaf)` (a singleton cube of the root,
  `RulePredicate.kt:199-201`); a legacy sink with one pattern
  (`SinkRule.conjunctive == false`).
* ND: the literal takes part in an alternative with two or more distinct
  positive literals. Production: `RulePredicate.isMulti(leaf)`; every
  pattern of a legacy sink with two or more patterns.

A literal can be both. B1 treats such a literal as unary (§3.1).

### 2.2 Layers of the backward requirements today

| Literal | Sink seed | Reversed conditional source literal |
| --- | --- | --- |
| unary `$` | `P.$(T)` NORMAL | keeps the layer of the input requirement |
| unary `[any]` | `P.[any](T)` DEMAND (W6) | `Q.[any](T')` DEMAND (W6) |
| ND `$` | `P.$(T)` NORMAL (zero premise, never a record) | DEMAND (`MicroEdge.conjunctive`, DES-3) |
| ND `[any]` | `P.[any](T)` DEMAND | DEMAND |
| pass rule with an `AnyField` target (reversed) | — | every result DEMAND (`MicroEdge.may`) |

Code: `MicroEdge.may = forward.to.tail == ANY || conjunctive`
(`MicroEdge.kt:32`); `SourceRuleOccurrence.transfer` (`:35-39`);
`sourcePredicateActionsAt` backward branch
(`RunMethodLocalServices.kt:182-189`); invariants I14 and A1
(`MicroEdge.kt:21-26`), W8 (d) and W6 for backward records
(`RecordStore.kt:274-277`); interpreter.md I11 (f), I14, §4.9; ap.md §8.7
R1 ("a backward record has no any tail").

### 2.3 Why the layers are as they are

* DES-3: the reversal of a conjunction must be DEMAND. A one-literal
  backward record of an ND rule would give a false CONFIRMED.
* W6 in the backward run: the reversal of a pass rule with an `AnyField`
  target is a MAY. The rule does not know the field.
* F69 amendment A1: "the backward run has no `[any-taint]`". This was a
  simplification. It is not necessary for soundness: for a unary literal
  the requirement is a MUST (§6.1, `BackCond.unary_seed_must`).

## 3. Rules

### 3.1 B1: MUST requirement of a unary literal

B1.1 SINK SEED. For a unary sink literal with the pattern `P.[any](T)`, the
backward seed is `P.[any-taint](T)` with the Empty exclusion, in the
NORMAL layer. A unary `$` literal keeps its seed `P.$(T)` NORMAL. A
literal that is unary and ND gets only the B1 seed (it covers every
location of the literal in the normal layer; a B3 seed lies inside it).

B1.2 REVERSED UNARY SOURCE LITERAL. For a unary literal `Q.[any](T')` of a
conditional source with the target `P.t(T)`, the reversed edge
`P.t(T) → Q.[any-taint](T')` gives its result in the layer of the input
requirement. Today W6 makes it DEMAND. The reversed edge of a unary `$`
literal does not change.

B1.3 WHAT STAYS MAY. These reversed micro edges are the MAY CLASS. Every
result of an edge of the MAY class is DEMAND, also a `$` result
(unchanged):

* the reversal of a pass rule with an `AnyField` target (D18);
* every reversed literal edge of an ND conjunction (DES-3).

Every other `[any]` result of the backward run is DEMAND by W6, as today.
So the only NORMAL `[any-taint]` facts of a backward run come from B1.1,
B1.2 and the AP rules that transfer them (B1.4).

B1.4 TRANSFER. A backward `[any-taint]` fact uses the AP rows of the
forward `[any-taint]` fact (ap.md W8, §4.1, S14): it keeps its layer
through a reversed micro edge that is not of the MAY class, it gets an
exclusion at a strong update, and the field limit cuts it as in a forward
run. The FL+1 caps do not change. A NORMAL `[any-taint]` requirement that
binds into a callee gives a MUST added fact. Emission (ap.md §6.3, the
must rows) gives a must-premise. Its start is NORMAL.

B1.5 REPRESENTATION. The reversed edge of B1.2 has the target tail
`[any-taint]`, as a forward source edge has. So invariant A1 changes: "a
reversed micro edge cannot have a must PREMISE". No micro edge has the
premise tail `[any-taint]` (I14, unchanged). The forms need no flag: the
interpreter reads `isUnary(leaf)` and the legacy `conjunctive` property
that it reads today.

### 3.2 B2: backward MUST records

B2.1 RECORDS (ap.md §8.7 R1, amended). A backward run persists a normal
singleton summary with a non-zero premise, also when:

* its premise is a must-premise `x.[any-taint]/E(T)` (a BACKWARD MUST
  RECORD, with the exclusion of its premise);
* its conclusion has `[any-taint]/E` leaves.

Its meaning, on the reversed program `Pb`, is the meaning of a forward
record on `P` (`BackMust.recsB_exact`, the mirror of
`AnyTaintExExact.recs_of_DRX`): a non-must premise is PAIR-EXACT; a
must-premise is END-EXACT. In terms of the forward program `P`: for a
backward MUST record `jb → gb` of the method `M`, every admitted location
of `gb` at the forward entry of `M` flows in `P` to SOME admitted location
of `jb` at the forward exit (`BackMust.backMust_forward`). A backward MUST
record is not pair-exact (`BackMust.CexMustPair.cex_must_pair`), so every
reader (R3, R4) reads it end-exact.

A zero-premise backward edge stays outside the record store (unchanged).
This is now necessary for one more reason: the NORMAL zero-premise
`[any-taint]` edge of a must seed relates the zero location to every
location of the seed, which is not a flow (`cex_must_pair`, second part).

B2.2 REUSE IN THE BACKWARD DIRECTION (R4). A backward must record applies
as a forward must record applies: its `inside` part keeps the layer; its
`applicable`-only part gives DEMAND results with the must exclusion
forgotten.

B2.3 READ VIEW IN THE FORWARD DIRECTION (R3). The forward read view of a
backward must record `jb(must, Ej) → gb` is the mirror of
`CurrentMustReverse.readView`: the new premise comes from `gb`
(`[any-taint]/E` becomes `*/E` with its concrete mark); the new conclusion
comes from `jb`: `[any-taint]/Ej(T)` becomes `[any](T)` in the DEMAND
layer, without `Ej`. The view is sound (`BackMustView.viewF_sound`) and
cannot be NORMAL (`BackMustView.viewF_not_exact`). A backward record with
a `$` premise and an `[any-taint]` conclusion has the ordinary exact view
(`CurrentMustReverse.exact_converse`).

B2.4 HAND-OFF. Open: decision D1 (§4).

### 3.3 B3: ND literal seeds refined by captured forward facts

B3.1 CAPTURE. In a forward run, at a sink check, keep every input fact
that satisfies a literal in a COMPLETED combination (NORMAL or DEMAND),
with its literal index. The key is (method key, statement, rule occurrence
id, literal). Production site: the combination of `checkSinksAt`
(`CompletePredicateBinding.leaves` and `.inputs`,
`RulePredicateStore.kt:99-104`; the legacy `ConjunctionStore.CompleteBinding`
keeps the literal order). For a conditional source, keep the inputs of
its completed combinations (the predicate and conjunction stores of the
forward run). The capture is a side table of the hand-off. It is not part
of `Seed` equality or hashing (`Seeds.kt:20`), so seed deduplication does
not change.

Collect ALL inputs of ALL completed combinations, not only the inputs of
the selected proof. With the selected proof only, a real route is lost
(`BackND.Vec.cex_selected_only`).

Store each input in this form (the proofs found both rules):

* with the CONCRETE mark that the check matched. A restricted run has
  abstract (FLOW, mark `*`) facts (F72). The meet of a `*` input with a
  concrete literal is empty, so the literal would get no seed at all
  (`BackND.Vec.cex_abstract_mark`). For a FLOW input the matched mark is
  the literal mark.
* a `*/E` tail as `[any]` with the exclusion `E` (the same locations). A
  `*` tail with a concrete mark is not a legal backward seed
  (`BackND.Vec.cex_star_capture`, `Backward.legal_seed`).

B3.2 REFINED SINK SEED. The backward seed of an ND literal `j` with the
pattern `p_j`:

* if the capture has inputs for `j`: for each input `a`, the emission meet
  of ap.md §6.3 with `D-c = p_j` (`a ∩ p_j`, the location intersection
  with the concrete literal mark); drop an empty meet;
* else: the full pattern `p_j` (today's seed).

The layer of a refined seed is the layer of today's seed of the literal:
DEMAND for an `[any]` literal. For a `$` literal the meet with a covering
input is the pattern itself, so the seed does not change. A DEMAND `[any]`
seed has no exclusion (`Reference.kt:13`), so the seed forgets the
exclusion of the meet. It stays inside the literal
(`BackND.meetLit_forget_inside`) but is wider than the meet.

THE FALLBACK IS NOT MONOTONE. A literal that had captured inputs in run
`n` and has none in run `n+2` gets the full pattern again
(`BackND.Vec.cex_mono_fallback`). This occurs, for example, when another
alternative of the same occurrence completes in a later run and the first
one does not. So the seeds are non-increasing only while the set of
literals with captured inputs does not shrink. Two forms are possible:

* B3-F (selected here): the fallback is the full pattern, as today. It
  keeps today's seeds for a literal with no witness.
* B3-P (not selected): the fallback is the seed of the preceding backward
  run, and each refined seed is also met with it. This is monotone by
  construction. It keeps per-literal seed state across runs. It can
  remove a demand that today's seeds keep, so it is a candidate result
  change (S-H6).

B3.3 REFINED REVERSED SOURCE LITERAL. The reversed edge of an ND source
literal gives its DEMAND result at the literal position (DES-3,
unchanged). Its result is the meet with the inputs captured for that
literal at the source statement in the preceding forward run; with no
captured input, the full pattern (today).

B3.4 WHAT DOES NOT CHANGE. The trigger seeds of an end fact
(`fireTriggerSeeds`) have no capture and keep the full patterns. A sink
whose seeds the GROUP projection replaces (`fullSinkSeedsFor`,
`RunMethodLocalServices.kt:384-388`) keeps the full patterns. The layer of
every ND result stays DEMAND (DES-3).

### 3.4 Progress: what the rules give and what they do not give

Proved:

* B1: a callee that a unary `[any]` requirement enters gets a must-premise
  and a NORMAL start (`BackMust.must_premise_normal`); today it gets a
  DEMAND start (`BackMust.demand_seed_contrast`,
  `demand_premise_start`).
* B2: its normal exit edges with a non-zero premise are exact records
  (`BackMust.recsB_exact`). R1 can persist them; R4 applies them in later
  backward runs.
* B3: the refined seed is a function of the captured facts
  (`BackND.refine_det`), lies inside today's seed (`refine_inside`),
  keeps every real location (`refine_sound`), and does not grow when the
  captured facts get narrower and no literal loses all its captured
  inputs (`refine_mono`, `refine_mono_seq`). The seeds stay in a finite
  set when the captured depths are bounded (`refine_shape`,
  `refine_length`). The backward contract and the iteration theorem of the
  base model hold with refined seeds (`BackND.B_general_refined`,
  `iteration_general_refined`).

Not proved and not measured:

* that an owner of §1 reaches zero demand rows (requirement AC);
* how many rows go away. With D1 = H2 (§4) the forward hand-off does not
  change, so B1 and B2 remove no forward demand. With D1 = H1 the callee
  demand goes away, at the risk of §4.

## 4. Open decision D1: the forward hand-off of a backward MUST record

THIS IS AN UNSELECTED MAJOR CHANGE. IT NEEDS THE USER'S DECISION BEFORE
IMPLEMENTATION.

Facts:

1. F77 (ap.md §8.5): the hand-off keeps every demand-layer summary, every
   normal multi-premise summary and every normal backward zero-premise
   summary. It omits every other native normal singleton summary; R1
   persists it. "Tail, mark, exclusion, and read-view layer do not add a
   selection condition." Lean: `CurrentSummarySelection.normal_backward_nonzero_omitted`.
2. B2.1 makes a backward MUST summary a native normal singleton summary.
   So, with F77 unchanged, it gives NO forward demand for its callee.
3. The next forward run then reads only the read view of B2.3. The view is
   DEMAND (`BackMustView.viewF_demand`). It is not exact: it relates pairs
   that are not flows (`BackMustView.viewF_not_exact`).
4. Today the same summary is DEMAND, F77 selects it, and the next forward
   run analyses the callee again with a larger field limit. That analysis
   can give a NORMAL result and a CONFIRMED finding.
5. Counterexample `BackMustView.cex_drop_forward_demand`: the callee
   `ret.f.g = arg0`, the caller fact `arg0.x $ (T)` NORMAL, the sink
   `ContainsMarkOnAnyField(ret, T)`. With field limit 1 the forward result
   is cut to DEMAND. With field limit 3 the forward result is
   `ret.f.g.x $` NORMAL and the sink check triggers in the normal layer.
   The read view of the backward MUST record `ret.[any-taint] →
   arg0.[any-taint]` gives `ret.[any]` DEMAND, and the sink triggers only
   in the demand layer. So, if the hand-off drops the callee demand, a
   finding that is CONFIRMED today stays provisional.

The same omission is safe for a FORWARD must record (F77 today): the
backward run makes no confirmation, and its DEMAND view keeps coverage.
For a backward record with a non-must premise the forward view is the
exact converse, so its omission is safe too. Only a backward MUST record
has this defect.

Options:

| Option | Rule | Results | Progress |
| --- | --- | --- | --- |
| H1 | F77 unchanged: a backward MUST record gives no callee demand | can lose a confirmation (item 5): fails the gate when it occurs | the callee rows go away in both directions |
| H1g | H1 with a guard: omit the callee demand only when a normal, pair-exact, complete forward record of the callee has a premise that covers `gb` | keeps the confirmation: the forward record gives the NORMAL result (`BackMustView.guard_keeps_normal`, proved for canonical FLOW records `b.p.*/{} → b'.q.*/{}`; `Cex.guard_instance`) | small: when such a forward record exists, F77 already removes the callee demand of the forward summary today, so the backward run does not start the callee again |
| H2 | add one selection condition to §8.5: "a backward summary with a must-premise is selected, as a demand-layer summary is" | the forward demand of the callee is today's demand, up to the hidden change S-H1 (§5.3) | none in the hand-off; the records exist for later use |
| H3 | a new forward rule that reads a backward MUST chain as a NORMAL fact: an "exists-any" tail (some location under `P` has `T`), or a confirmation at the point where a forward NORMAL fact meets a backward MUST requirement, with a trace for it | can keep the confirmation of item 5 | the callee rows go away |

H3 is a new forward fact kind or a new confirmation rule. It changes the
forward run, the sink check and trace resolution. It is outside the
selected scope. This spec does not design it.

Recommendation: implement B1, B2 and B3 with H2 first. H2 keeps every
result by construction, except the hidden change S-H1, which a shadow
comparison measures. In the same prototype, log in shadow mode what H1
would omit: for each backward MUST summary, the callee demand edge, and
whether the status-quo forward run gets a NORMAL callee summary under it
(design guide rule 4). If no reference project and no test suite has such
a case, H1 can go to its own gate. If a case exists, H1 is withdrawn, and
progress for these owners needs H3.

## 5. Semantic scope

### 5.1 Selected changes

| # | Change | Current | New | Selected by |
| --- | --- | --- | --- | --- |
| S1 | unary `[any]` sink seed | `P.[any](T)` DEMAND | `P.[any-taint](T)` NORMAL | user (26 Nov, item 1) |
| S2 | reversed unary `[any]` source literal | `Q.[any](T')` DEMAND | `Q.[any-taint](T')` in the input layer | user (item 1) |
| S3 | backward must-premise in a callee | none (the added fact is DEMAND) | must-premise, NORMAL start | user (item 1: "emit something like forward MUST") |
| S4 | backward MUST records | none (W8 (d)) | R1 persists them; R4 applies them; R3 reads them as DEMAND | user ("the new MUST should reach the record store") |
| S5 | ND sink seed | the full pattern | the meet with the captured inputs; the full pattern if none | user (item 2) |
| S6 | reversed ND source literal | the full pattern, DEMAND | the meet with the captured inputs, DEMAND | user (item 2) |
| S7 | hand-off of a backward MUST record | — | D1: H1, H1g, H2 or H3 | OPEN (§4) |

### 5.2 Behavior that must not change

* The forward run: transfer, sink check, layers, conjunctions, cleaners,
  records, read views of forward records, confirmation, trace resolution.
  With H2, no forward input changes either, except S-H1.
* DES-3: every reversed ND literal edge gives DEMAND results.
* The reversal of a pass rule with an `AnyField` target gives DEMAND
  results.
* `$` seeds; zero rows; source hits (`sourceHits`, recorded when a
  reversed source edge applies; the layer does not take part).
* C1-C5, the C2 entry-tail guard, the restriction (§6.4), the field limits
  and the FL+1 caps.
* Hand-off normalization: a must demand piece becomes an `[any]` pattern
  without an exclusion (ap.md §8.5, §9.2). W8 (d) for demand entries and
  demand patterns (`Demand.kt:41`, `DemandStore.kt:449`) stays.
* Confirmed and provisional results on every reference project and every
  test suite (the gate, §10).

### 5.3 Hidden-change check

| # | Candidate | Status |
| --- | --- | --- |
| S-H1 | A backward `[any-taint]` fact gets an exclusion at a strong update; a DEMAND `[any]` fact has no exclusion. Example: `x.f = z; …; x.f = y; sink(x)`. Backward, the MUST fact is `x.[any-taint]/{f}` before `x.f = y`, so `x.f = z` gives no requirement on `z`; the DEMAND fact `x.[any]` gives one. The hand-off normalization drops the exclusion of a must piece but does not restore the requirement on `z`. So the forward demand can be NARROWER than today, and a narrower demand can remove a provisional result. | Not proved equal. In the base model (no exclusions) W6 changes only layers (`W6.D6_same_shape`, `DR6_same_shape`) and the hand-off demand is the same (`W6.summaryDemand_iff`, `revSummaryDemand_iff`). The refined model with exclusions has no such theorem. In the example the removed route is not real (the strong update kills it), so only a provisional result can change. Needs a shadow comparison of the normalized hand-off pieces per run. |
| S-H2 | Cleaners act on a backward MUST leaf: the EXACT-cleaner rule for a MUST leaf (`Clean.kt:187-192`, acyclic-convergence §5.5) now runs in backward runs. | Not analysed in the model. The model has cleaners (`cleanResX`) but no backward cleaner semantics proof for must leaves. Check in the prototype. |
| S-H3 | Summary keys: a must-premise and an `[any]` premise at the same path have separate summaries (ap.md §8.5). A literal that is unary in one rule and ND in another gives both. | More summaries (cost). No result change: the two premises are separate today too. |
| S-H4 | Negated literals: MUST means "sufficient for the condition after the projection of negated literals to true" (`BackCond.firesS_proj`, `BackCond.signed_not_must`). | No change: the forward run uses the same projection. State it in interpreter.md §4.9. |
| S-H5 | B1 is not the largest MUST set: two literals of one alternative that cover the same location make it sufficient, but B1 gives MAY there (`BackCond.nd_overlap_suff`). | No change of results: B1 is an under-approximation of MUST, so it is sound. |
| S-H6 | B3 narrows the forward demand. A provisional result whose witness used a fact outside the captured inputs can go away. | Argued: in later runs a forward fact at the sink lies inside an earlier fact (a deeper field limit refines a cut). Not proved for the whole iteration. Needs measurement. |
| S-H7 | Record equality: a backward MUST record is a new record shape (`Record(direction, premise with ANY_TAINT and E, facts)`). | No dedup change for the existing shapes: the new key has a tail that no current backward record has. |
| S-H8 | Trace resolution through a forward read view of a backward MUST record (H1 only). A finding with no trace is dropped. | H1 only. Today forward views of backward records exist (non-must), so trace resolution already reads views. Check in the prototype. |

### 5.4 Affected invariants and proofs

| Invariant or text | Change |
| --- | --- |
| interpreter.md I11 (f): the backward seed of an `[any]` pattern is `[any]` DEMAND | B1.1: unary literal gives `[any-taint]` NORMAL |
| interpreter.md I14: "the BACKWARD run has no `[any-taint]`" | B1: the backward run has `[any-taint]` facts from B1.1, B1.2 and their transfer. "No micro edge has the premise tail `[any-taint]`" stays. |
| interpreter.md §4.9 RULE ROLES, SEEDS, CURRENT PREDICATE REVERSAL | B1.1, B1.2, B3 |
| `MicroEdge.kt:23-25` A1 | a reversed micro edge can have a must target (B1.2), never a must premise |
| ap.md §8.7 R1 (backward), `RecordStore.kt:274-277` (W8 (d), W6 for backward records) | B2.1 |
| ap.md §8.7 R3, R4 | B2.2, B2.3 |
| ap.md §9.1 backward W6 | narrowed to the MAY class and to non-B1 `[any]` results |
| ap.md §8.5 (F77) | H1: no change. H2: one selection condition. |
| Lean `Backward.DB` | unchanged. Its seed rule already makes an `[any]` seed normal (`limitF counted L ⟨s,false⟩`, no W6 in the backward base run, W6.lean header); its `startFact` of an `[any]` premise is DEMAND, so it has no must-premise. B2 is proved on the refined model instead (`BackMust.DBX`). |
| Lean iteration theorems (`Backward.B_general`, `W6.iteration_general6`, `Handoff*`) | not re-proved with B2 records. Their record hypotheses (`RecsExactNZ`, `Cross`) cover non-must records only. A backward MUST record is not crossable (`Handoff.CrossK .any = False`), so `Handoff.demOfN` hands it off, which is H2. The F77 no-loss iteration is open today (proof-status.md, "Full current no-loss iteration with F77 selection"); with H1 it is false for confirmations (§4 item 5). |

## 6. Proof map

All modules are constructive: `#print axioms` shows only `propext` and
`Quot.sound`. Every counterexample is a concrete value checked by
`decide` or `rfl`.

### 6.1 Rule level: `BackCondRules.lean` (`ApSpec.BackCond`)

Model: a state is a list of tainted locations; a condition is a DNF over
positive literals (the projection of negated literals is
`firesS_proj`); `Suff c l` = every state with `l` fires `c`.

| Theorem | Statement |
| --- | --- |
| `suff_iff`, `fires_mono` | `Suff` is decidable; firing is monotone |
| `unary_seed_must` | a literal that is an alternative alone: every covered location is sufficient (B1.1) |
| `unary_cond_exact` | for an all-unary condition the union of the seeds is exactly the sufficient set |
| `nd_suff_iff`, `nd_seed_not_must` | an ND literal: a covered location is not sufficient (cex) |
| `seed_may_cover`, `core_spec` | every location of a minimal firing state is covered by a literal: the per-literal seeds are a sound MAY cover |
| `rev_unary_source_must`, `rev_unary_source_must_exact` | the reversed unary source literal is MUST for every target kind (B1.2) |
| `rev_nd_source_not_must`, `rev_nd_source_not_must_gen` | the reversed ND literal is not MUST (cex, DES-3) |
| `rev_pass_any_not_must`, `rev_pass_may_sound` | the reversed pass rule with an `AnyField` target is not MUST (cex), but it is a sound MAY |
| `reqs_normal_must`, `reqs_normal_rev_must`, `reqs_may_cover`, `reqs_unary_exact`, `reqs_nd_demand`, `any_seed_exact` | the B1 layer assignment in AP form: normal means MUST; all requirements together are a sound MAY cover |
| `firesS_proj`, `signed_not_must`, `nd_overlap_suff` | S-H4, S-H5 |

### 6.2 Run level: `BackMustRun.lean` (`ApSpec.BackMust`)

Model: `DBX` = the rules of the forward refined restricted run
`AnyTaintEx.DRX` on the reversed program `Pb`, with the backward transfer
`transferXB bmay` (no W6T; the MAY class `bmay` demotes to DEMAND), plus
the zero rules of `Backward.DB` (`zpass`, `zin`, `seed` with a must flag,
`zret`).

| Theorem | Statement |
| --- | --- |
| `transferXB_normal`, `transferXB_cases`, `transferXB_wf`, `transferXB_reqs` | a NORMAL result of the backward transfer is a result of the forward refined transfer (so its exactness lemmas apply) |
| `DBX_wf`, `DBX_mustAny`, `DBX_conc` | the invariants of the closure |
| `must_seed_normal` | B1.1: a must `[any]` seed with a concrete mark gives a NORMAL `[any]` edge |
| `must_added`, `bindX_star_any`, `must_seed_bound` | B1.4: bound into a callee by `b.* → b'.*`, it is a MUST added fact |
| `must_premise_normal`, `must_premise_endExact` | B1.4: emission gives a must-premise with a NORMAL start, and its edges are end-exact |
| `demand_seed_contrast`, `demand_premise_start` | today: a DEMAND seed gives a non-must premise and a DEMAND start |
| `DBX_edgeOK_nz`, `edge_exactBX_gen`, `no_zero_summaryX` | MAIN: every edge with a non-zero premise satisfies `EdgeOKX Pb ok`: pair-exact for a non-must premise, end-exact for a must-premise. A full mirror of `AnyTaintExExact.DRX_edgeOK`. |
| `recsB_exact`, `recsB_must_end`, `recsB_pair` | B2.1: the exit edges with a non-zero premise are exact records on `Pb` |
| `recsB_next`, `recsBSeq_ok` | over a sequence of backward runs the records satisfy the record hypotheses again (R4 reuse; no record hypothesis is left) |
| `backMust_forward`, `backPair_forward`, `backMust_forward_valid`, `backMust_forward_seq` | B2.1 in forward terms: every admitted location of `gb` at the forward entry flows in `P` to SOME admitted location of `jb` at the forward exit; the pair form for a non-must premise |
| `CexMustPair.cex_must_pair` | executable, every hypothesis of `recsB_exact` holds: a B2 record is end-exact but NOT pair-exact (so R3 and R4 must read it end-exact); the NORMAL zero-premise `[any-taint]` exit edge of a must seed is not exact (so R1 must keep the zero premise out, as today) |

Hypotheses of `DBX_edgeOK_nz` and `recsB_exact`: those of `DRX_edgeOK` on
`Pb` (`MarkWF`, `FiltOK`/`BackOK`, `SatInsideX`, `RestrictOKX`,
`EmitCopiesMarkX`), and:

* `NoZeroIn Pb`: for `Pb = Program.rev P` it is `Backward.NoZeroBack P`
  (`noZeroIn_rev`, interpreter.md I11 (c)). Necessary:
  `BExact.CexZeroBack`.
* `SeedsConcB seeds`: a seed has a concrete mark (a sink pattern,
  `SinkRule.init`). Necessary: `BExact.CexSeed`.
* the record hypotheses only for records with a premise off the zero base
  (weaker than `DRX_edgeOK`); `recsBSeq_ok` discharges them for B2 records.

`backMust_forward` adds `RevStmts P`, `RevCalls P` (`Reverse.flow_rev_iff_calls`).

### 6.3 Forward reading: `BackMustView.lean` (`ApSpec.BackMustView`)

Model: one singleton backward MUST record `BRec` (`jb` must, `jex`; `gb`
normal at the forward entry), its forward view `viewF` (B2.3), the base
operations for the counterexample.

| Theorem | Statement |
| --- | --- |
| `viewF_demand` | every view result is DEMAND, with no exclusion: `jb` with the `[any]` tail and the mark of `jb` |
| `viewF_stays_demand` | `applyEdge`, `applySummary`, `transfer` on a view result give only DEMAND results |
| `viewF_sound`, `viewF_sound_pair` | under `BComplete` (the soundness of the backward run for the record): a real flow from an added location to an admitted `jb` location is covered (and related, with a concrete `jb` mark) by the view |
| `Cex.viewF_not_exact` | a well-formed, end-exact record of a real one-statement `Program` whose view relates a pair that is not a flow (`Cex.no_flow_to_ret`, `Cex.flow_inv`): a NORMAL view would break `EdgeOKX` |
| `Cex.cex_drop_forward_demand` | §4 item 5: (a) field limit 1: DEMAND; (b) field limit 3 with the callee demand: `ret.f.g.x $` NORMAL, the sink triggers from a normal edge; (c) the view: `ret.[any]` DEMAND, the sink triggers only in DEMAND |
| `Cex.back_derives_gb` | one backward step on the normal must start `ret.[any-taint](T)` gives exactly `gb` (the record of the counterexample is a B2 record) |
| `guard_keeps_normal`, `Cex.guard_instance` | H1g: a pair-exact, complete forward FLOW record whose premise covers `gb`, applied to a normal `$`/`[any]` added fact with a concrete mark inside `gb`: every result is NORMAL, every real pair into `jb` is related, every result pair is a real flow. After run 1 of the counterexample no such record exists, so the guard keeps the demand. |

### 6.4 ND refinement: `BackNDRefine.lean` (`ApSpec.BackND`)

Model: literal patterns `lits`; a capture `cap : List (Nat × PFact × Excl)`;
`refine lits cap` (B3.2); the meet `meetLit := AnyTaintEx.emitX` (ap.md
§6.3, `AnyTaintExCov.emitX_contract`).

| Theorem | Statement |
| --- | --- |
| `meetLit_inter` | for a concrete captured input the meet covers exactly the common locations (exclusions and marks included) |
| `meetLit_forget_inside` | the meet with its exclusion forgotten (the DEMAND seed form) lies inside the literal |
| `refine_cover` | a literal location that a concrete captured input covers is covered by a refined seed |
| `refine_fallback` | no captured input: the only seed is today's seed |
| `refine_inside` | every seed lies inside the literal, and a meet lies inside its input |
| `refine_sound`, `refine_sound_strict`, `forwardCaptured_of_combos` | with the inputs of all completed combinations (`CombosCover`, the forward coverage), every real location of the literal is covered |
| `refine_mono`, `refine_mono_seq` | narrower captured inputs and no new fallback give seeds inside the earlier seeds; over a sequence of runs |
| `refine_det`, `refine_det_set`, `refine_shape`, `refine_length`, `refine_legal` | the seed is a function of the inputs; paths are literal or captured paths; at most `cap.length + lits.length` seeds; legal `$`/`[any]` seeds with concrete marks |
| `SeedsCover`, `seedsCover_full`, `seedsCover_refined`, `B_general_cov`, `B_fragment_rep_cov`, `B_general_refined`, `iteration_general_refined` | the backward contract B and the general iteration theorem read the seeds only through `demanded_gen`/`demanded_fragment`; refined seeds satisfy that contract |
| `Vec.cex_selected_only`, `Vec.all_combos_cover` | the selected proof only: a real location is lost; all combinations: covered |
| `Vec.cex_abstract_mark`, `Vec.cex_star_capture`, `Vec.cex_mono_fallback` | the three design points of B3.1 and B3.2 |

## 7. Proof scope and differences between model and production

1. THE MAY CLASS IS INVISIBLE TO THE RUN-LEVEL MODEL. In the base model a
   forward `AnyField` target `x.* → y.[any]` relates each `x.σ` to EVERY
   `y.τ`, so its reversal is exact in the model, and the theorems of
   `BackMustRun.lean` hold for every `bmay`, also for no demotion. The
   real rule writes ONE unknown field. The rule-level model shows that
   the reversal is not MUST (`BackCond.rev_pass_any_not_must`) and that
   the reversed ND literal is not MUST (`BackCond.rev_nd_source_not_must`).
   The link between the two levels is argued, not proved: a NORMAL
   backward fact never passes through an edge of the MAY class (B1.3), so
   its derivation uses only edges whose model meaning is the real meaning.
   A precision note (not selected): on an input requirement that covers
   the whole `y.[any]`, the reversed pass-rule edge is MUST too. B1.3
   keeps today's DEMAND.
2. THE MUST FLAG OF A SEED IS AN INPUT of the run-level model. The
   rule-level model decides it (`BackCond.reqs_normal_must`,
   `any_seed_exact`). The rule-level model has a DNF over positive literals
   after the projection of negated literals; production has an NNF DAG
   (`RulePredicate`) and reads `isUnary`.
3. The rule-level model of B1.2 reads the source statement as "if the
   condition fires, the targets get taint" (`BackCond.post`) with finite
   target lists. An `[any-taint]` target is a finite list of locations.
4. `BackMustRun.lean` persists ALL non-zero-premise exit edges as records.
   A production policy that persists a subset (R1: singleton premise sets,
   the field limit) satisfies the same record hypotheses.
5. `BackMustRun.lean` fixes `zbind = true` (the selected zero binding back,
   ap.md §9.2). It keeps the rules `reqSink`, `answer`, `reqUp`, `vuln` for
   the mirror of `DRX`; the backward run gets no forward sink. That the
   backward run makes no request is proved for the base run
   (`BExact.DB_no_request`), not again for `DBX`.
6. `BackMustView.lean` has one singleton record and one leaf: no store
   lookup (R2), no statics (F78), no cleaner, no type filter. Its
   counterexample checks the sink on the callee exit fact (the return
   binding is the identity). `guard_keeps_normal` is proved only for
   canonical FLOW records `b.p.*/{} (*) → b'.q.*/{} (*)` and for the
   summary application, not for the R4 selection `applicable || inside`.
7. `BackNDRefine.lean`: the base model has no ND sink. The iteration
   theorem with refined seeds (`iteration_general_refined`) reads each
   literal as its own sink, so its contract asks every witness location of
   the literal. A real ND capture covers only the locations that take part
   in a completed combination. An ND form of `BackwardContractD`,
   `vuln_foundR` and `iteration_invariant_D` is not proved; `demanded_gen`
   needs no change. The production seed forgets the exclusion of the meet
   (`meetLit_forget_inside`); `refine_mono` is proved for meets that keep
   their exclusions.
8. No module models the cleaner rows on a backward must leaf (S-H2), the
   group projection of seeds, end-fact triggers, statics, or the forward
   hand-off normalization of a must demand piece.
9. No theorem proves that the normalized hand-off of B1 equals today's
   hand-off (S-H1), or that B3 keeps the provisional results (S-H6).

## 8. Cost

| Operation | Where it executes | Measured volume |
| --- | --- | --- |
| B1: `[any-taint]` transfer instead of W6 `[any]` | per backward fact on a must path | not measured |
| B2: persist backward MUST records | per backward summary at the barrier | not measured |
| B2: R4 replay of backward MUST records | per call offer in later backward runs (`replayPersistedSummaries`) | not measured |
| B2 + H2: one more selection test | per backward summary delta | not measured |
| B3: capture | per completed sink or source combination in a forward run; held until the next backward run (today the predicate stores are cleared at `freeze()`, `RunMethodLocalServices.kt:451`) | not measured; the heap cost is a risk (ThingsBoard runs out of memory in run 1) |
| B3: meet per captured input | per seed per backward run | not measured |

Design guide rule 5 asks for a measured volume of each site on the largest
project. None exists (§11).

## 9. Withdrawal condition

Withdraw a rule when its gate (§10) fails:

* B1/B2 with H2: any change of a confirmed or provisional result, or worse
  wall time or peak memory on a reference project.
* H1: one case of the shadow log of §4 (a NORMAL callee summary that the
  omission removes), or any result change.
* B3: any result change (S-H6), or a capture heap cost that makes a launch
  run out of memory or worse in peak memory.

If a rule fails and the failure needs a repair rule, stop (design guide
rule 7).

## 10. Gate and WI classification

Gate per rule, alone, per project (design guide rule 6): confirmed and
provisional results identical to the pinned baseline (OWASP, Stirling-PDF,
Conductor, ThingsBoard), the analysis test suites (module, jvm, rule
suites), wall time and peak memory not worse.

WI: none. A rule becomes WI only after its native prototype passes its
gate.

## 11. Checklist and blind spots

```text
[x] Failure class and real trace (project, run, owner, count)
      Stirling-PDF AuthController#login (1 row) and its entry point (2 rows)
      after AO-C5; Stirling-PDF bytesToWebResponse arms. The per-run count of
      rows from [any] seeds, reversed [any] literals and ND seeds: NOT MEASURED.
      ND (B3): no real instance with a count.
[ ] Ablation result on the real case                      NOT DONE (user: spec only)
[ ] Native prototype result: findings, time, memory       NOT DONE (user: spec only)
[ ] Execution site and measured volume of each operation  sites in §8; volumes NOT MEASURED
[x] Selected semantic scope: changed / unchanged          §5; D1 open (§4)
[x] Proof scope, and each difference model / production   §7
[x] Withdrawal condition                                  §9
[ ] WI classification                                     none yet (§10)
[x] Proofs                                                §6
```

Blind spots:

* No rule of this spec has run natively. The proofs show properties of the
  model, not that the model is the runtime, not the cost, and not that the
  rules remove the rows of §1.
* Whether B1 and B2 with H2 remove any forward demand row: by construction
  they do not remove the rows that F77 selects today. Their value is the
  record store content that H1 or H3 can use.
* Whether H1 loses a confirmation on a real project: the counterexample is
  a reduction, not a measured case.
* The hidden changes S-H1, S-H2, S-H6, S-H8 are not measured.
* The heap cost of the B3 capture is not measured.
