# Proofs for concrete relations backed by FLOW

Date: 24 October 2026. Status: **constructive models and local implementation checks pass; fixed project commands closed**.
Contract: [complete specification](run1-flow-backed-concrete-relations.md).
Reference runtime: `40e20d16f03ab046df75a53a489bb331b065a9c1`.
Measured implementation: `5ec1b30be614a0cfdc31ec3102bfa2f9301ee21e`.
Latest measured Thingsboard iteration: **run-2 OOM**, with **run-1 COMPLETE
and accepted**, engine time 392.439 s. See the
[fresh performance report](../docs/reports/bidirectional-flow-backed-concrete-performance-20261024.md).
Project outcomes are validation evidence; they do not extend the proof scope.

The proposed [general correlated-concrete extension](run1-correlated-concrete-initials.md)
removes the run-1/FULL restriction from runtime admission and proves general
path/exclusion/application cells. Its
[updated dossier](run1-correlated-concrete-initials-proofs.md) states the new
all-run protection and adapter obligations. The historical model and measured
implementation described here keep their original scope.

## 1. Claim, scope and proof order

The optimization preserves the supported concrete transport relation and
logical rule/source/sink observations. Its handoff can have fewer marked
rows. Each removed marked dependency has an executable pure transport
replacement through retained FLOW guidance or a NORMAL FLOW record. Exact
compression preserves every remaining marked relation and flag.

The local semantic cell proved here is a canonical STAR/Empty initial with
an ANY final, at equal complete scope and input geometry. The FLOW output
path can equal or prefix the marked output path. A mark must be admitted
by FLOW, its relation must be diagonal and unprotected, and layer strength
must suffice. Unsupported cells retain their exact old semantics. Geometry
sharing does not require semantic subsumption.

The models were written before the final specification. The original AP
operations produced the same-T source counterexample. The original cleaner
then produced a second counterexample. The user selected cleaner assign-back,
corrected assignment protection to use the triggering conclusion, and
selected cycle protection for both local and summary composition. The final
protection model includes all three decisions.

These are relative proofs for the original supported AP concept. They
inherit its program/call/record, sink-seed, primitive-filter and static
adapter assumptions. They do not establish soundness of every Java/Go/IR
adapter, every old unsupported AP cell, or the Kotlin implementation. No
general StrongQueries premise appears in a new model or proof.

## 2. Model map

| Module | Executable object and checked result |
| --- | --- |
| [Run1FlowTaintCoverage](lean/ApSpec/Run1FlowTaintCoverage.lean) | Original pair denotation; ANY coverage; excluded-mark, cross-mark and STAR correlation counterexamples; original source-rule witness |
| [FlowBackedAp](lean/ApSpec/FlowBackedAp.lean) | Actual original `applySummary` equality for equal paths; output-prefix and tree-to-path coverage; narrower-requirement emission; abstract and concrete `emitW` results |
| [FlowBackedProtection](lean/ApSpec/FlowBackedProtection.lean) | Flag functions; typed finite derivations; executable transport extractor |
| [FlowBackedStore](lean/ApSpec/FlowBackedStore.lean) | Admission, exact masks, normalized relation/obligation preservation, progress and counted geometry cost |
| [FlowBackedPriority](lean/ApSpec/FlowBackedPriority.lean) | Four-lane nonzero queue, exact pop, finite-credit measure and barrier predicate |
| [FlowBackedHandoff](lean/ApSpec/FlowBackedHandoff.lean) | Original C2 emission/C5 reduction witnesses; extracted recipe replay |
| [FlowBackedRelationsCounterexamples](lean/ApSpec/FlowBackedRelationsCounterexamples.lean) | Original cleaner counterexample and the selected correction |

`Run1FlowTaintCoverage.assignProtection` is the **historical premise-only
experiment**. Its protection helper does not define the new contract.
`FlowBackedProtection.ruleFlag` supersedes it. The counterexample module
keeps rejected results as controls, then checks the corrected rule.

## 3. Cross-premise coverage and actual AP application

Fix input base/path a/p, output base/path b/q and mark T. Let marked E have
STAR/Empty concrete initial T and ANY output T. Let F have the same shapes,
abstract initial and ANY output `* minus X`, with T not in X.

An E pair contains input/output marks T and arbitrary admitted suffixes.
Use those same suffix witnesses for F. The input mark gate is abstract,
the output preserves the input mark, and T passes the exclusion gate.
Thus every E pair is an F pair. This is a cross-initial-key proof, not an
existing same-ConclusionGroup test.

For a marked output at `q ++ suffix`, the same statement holds with FLOW
output q and ANY tails. `any_output_prefix_covers` uses the marked pair's
actual output suffix r and constructs the FLOW suffix `suffix ++ r`.
Associativity gives the same concrete location; all input and mark witnesses
are unchanged. This proves the requested output-location containment, including
proper prefixes. It does not treat a longer field path as a larger location
set, or remove a field exclusion or correlation requirement.

**Tree-to-path lift.** A FLOW field tree denotes the union of its output
paths. For one TAINT field path, find a FLOW output path which prefixes it
and has the required tail, mark admission and layer. Apply the prefix theorem
to that output. The resulting pair belongs to the FLOW tree by the same
output's union membership. This uses one actual matching path, not a
single-path restriction on the FLOW tree. It does not require every FLOW
branch to cover the TAINT path. Metadata from different branches cannot be
combined to manufacture a qualifying output.

The concrete trie search follows the TAINT path and tests annotated prefix
nodes. A branch node without an output annotation contributes no relation.
The proof's finite `coveringPaths` reference enumerates matching output paths
and supplies the exact prefix candidates; it is not the proposed production
trie traversal or a reason to enumerate the whole FLOW tree at runtime.

The stronger executable result is `any_summary_application`. For every
actual AFact whose mark is T, and either equal summary layer, applying E
or F returns **equal Res values**. After the mark gates reduce, both calls
execute the same path relation, tail operation, normalization and layer OR.
Requests are equal too. This checks the real `applySummary`, not a new
operation defined to return the expected value.

For proper prefixes the output headers can differ, so equality is not claimed.
Pair inclusion and original `applySummary_sound` preserve each concrete
composition pair in the covering FLOW application. The concrete input rules
out a mark-request alternative. At the handoff, `prefix_guide_start` computes
the original `emitW` result for a marked requirement strictly below the FLOW
ANY entry pattern: the result is the FLOW form at the original broader path.
Original C2/C5 then supplies the same whole-premise and requested-pair
guarantees. This is an extension of the equal-path supported cell; no new
StrongQueries admission or new initial shape is introduced.

If F excludes T, no such proof exists. If an edge changes T to U, FLOW
preservation of the input mark makes pair coverage impossible when T differs
from U. If F ends in STAR and E ends in ANY, choose different nonempty
input/output suffixes to disprove inclusion. These checked counterexamples
fix the boundary of the executable test. EXACT/MUST and call identity
classification cells are not inferred from this ANY theorem.

NORMAL strength and caller DEMAND are separate. Summary application ORs the
caller and summary demotion bits. A NORMAL proof can provide stronger
coverage; it cannot make a DEMAND input NORMAL. The existing NORMAL record
protocol is retained when its proof replaces a demand.

## 4. Protection and complete dependency extraction

The new functions are executable Boolean operations. Rule assignment ORs
input protection, equality with the triggering conclusion, and restoration
of the original mark after a different incoming mark. Call application ORs
caller protection, callee protection, and that restoration test. Merge is OR.

Direct constructor proofs establish:

- Assigning the triggering mark always protects, independent of original I.
- Assigning the original mark always protects: either it equals the trigger,
  or the local cycle clause applies.
- A surviving selected cleaner is a same-trigger assignment, so it protects.
- A protected caller, protected summary or restored call mark protects output.
- An ordinary T-to-T pass creates no new protection.
- OR is commutative and idempotent; a protected duplicate dominates.

The main theorem is stronger than these truth tables. `Derivation Op t u p`
is a finite derivation with original t, output u and flag p. Its constructors
are initial, neutral move, concrete assignment, cleaner residual, call and
merge. Op retains each original transport address/recipe as opaque data;
the model does not erase fields or contexts.

`extract?` recursively builds a `Transport Op` tree and fails at assignment
or cleaner residual. It preserves moves, calls and merges. It never chooses
a path from an existential claim.

**Plain diagonal extraction theorem.** For output u=t and p=false, the
extractor returns an actual transport tree:

1. An initial returns its initial node; a move appends its unchanged recipe.
2. An assignment ending in original t has flag true, a contradiction.
3. A cleaner residual also has flag true, a contradiction.
4. For a call, false output protection forces both child flags false and the
   intermediate mark to be t. Apply induction to each child, then construct
   a call node with both actual trees. This is where cycle protection is
   necessary. It covers local composition through the assignment case too.
5. For a merge, false OR forces both children false. Construct both trees.

`extract_sound` proves zero assignment/cleaner barriers and equal operation
lists for every successful extraction. `replayWitness` computes the extractor
and packages those proofs. The impossible failure branch is eliminated by
the completeness theorem. No Classical choice or runtime history is used.

This ghost derivation models one retained original and its accepted rule
contributions. The runtime adapter must OR over every real contribution
and preserve all original projections. It must not select a representative
premise, invent all-ZERO support, or use an unrelated packed mark as a trigger.

## 5. Why the cleaner correction is necessary

The checked witness reads p.left and cleans marks below local x on one
branch. A second branch reads p.right without cleaning. A final may transfer
spreads x to a return value.

With the original AP cleaner, the first branch's abstract result excludes
T but its concrete result keeps exact root T. The second branch supplies
coarse FLOW/ANY which covers the merged marked image. The old three tests
would leave it unprotected and remove its marked guide.

The original abstract backward start excludes T at the cleaner; its left
summary cannot answer a real T requirement. The concrete root query does
survive. Thus coarse coverage is not enough. The final
`corrected_cleaner_keeps_demand` applies the selected assign-back rule and
retains the concrete guide. Cleaner paths, exclusions and requests are
unchanged. Protection alone closes the counterexample.

## 6. Store normalization and exact compression

Project at a complete eligible marked relation key. The reference cell has
three monotone bits: covering FLOW present, marked member seen, protected
member seen. A protected member implies marked membership. The executable
residual is:

```text
residual = marked AND (NOT coveringFLOW OR protected)
```

The history bits are a reference model. Runtime summaries need only FLOW
and residual payload; method-point progress keeps required local marked
memberships. No subsumed-summary archive is required.

Admission sets FLOW or unions a marked offer and its flag. Constructor
proofs give well-formedness, idempotence and commutation. Normalization
preserves `FLOW pairs union marked pairs` because only a covered plain
member disappears. It also preserves every protected obligation. FLOW
arrival does not remove local marked progress. A late protected offer
always restores a residual and is novel when protection was false.

These laws prove order independence for finite equal offer sets by repeated
commutation and idempotence. The argument applies at raw, selected and
publication owners; each must use the same rule. It does not justify
removing only one physical copy or skipping producer effects. Such effects
occur before normalization and retain their existing identities.

The exact mask decoder builds one scalar marked initial/output pair per T
using the stored original header. `decode_exact` proves both directions of
membership. `decode_diagonal` rejects T/U products; `decode_injective` keeps
distinct FULL handles distinct. This proves exact compression even where
FLOW cannot subsume the relation. Protected masks use the same per-member
projection, with subset-of-membership as an invariant.

This projection must also apply when ordinary trie subsumption contains a
new protected region in a broader plain leaf. Protection union is independent
of ordinary fact novelty. The adapter can keep the smaller region, or mark
the containing leaf protected. The latter is conservative: it adds marked
guidance but removes no pair or required dependency. It can reduce savings,
so it must not be counted as exact protection-region compression. The scalar
cell proof does not prove a concrete trie partition algorithm.

## 7. Handoff replacement without general StrongQueries

The handoff comparison is **preservation of supported witnesses**, not
equality of raw demand rows. Source/sink occurrences and required marked
boundaries are retained. Pure transport can use abstract FLOW guidance.

For each removed diagonal member:

1. The coverage theorem supplies its represented concrete pair in F.
2. The flag theorem supplies the executable neutral transport tree. It
   contains no concrete generation or selected cleaner residual whose
   backward evaluation needs a concrete callee start.
3. Keep the original FLOW demand, or the corresponding NORMAL record and
   its reverse. An incoming marked requirement overlaps its abstract pattern.
   `startFromFlowGuide` executes original `emitCertificate` (C2), yielding
   an emitted premise which covers that location, is satisfied by the
   incoming fact and lies **wholly** inside the demand entry.
4. Replay the original neutral transport recipes. At exact compression
   boundaries the scalar operations are unchanged. At the selected summary
   boundary `any_summary_application` proves equal concrete results. Keep
   scalar fallback at every unproved mark-sensitive or call-stage boundary.
5. `publishFromFlowGuide` executes original `restrictCertificate` (C5).
   The required pair survives with the same layer and no invented pair.
   There is no extra response permission. The model also checks that the
   abstract emitter starts FLOW and the protected concrete guide starts T.
6. A caller's real T requirement instantiates that FLOW summary through
   original AP application. Apply this construction recursively to finite
   call/merge trees; no call-depth limit is assumed.

`removedDependencyReplay`, `no_concrete_barrier_removed` and
`removed_recipe_equal` check the extraction/replay part. `execute_equal`
is an explicit trace lift from local operation equality, not an assumption
that whole closures are equal. The original AP certificates prove the
admission/restriction gates. They keep their documented entry-tail guards;
the supported Empty/ANY cells satisfy them.

Cross-mark generation remains as a marked boundary because FLOW cannot
cover it. Restored marks, same-trigger generation and cleaner survivors are
protected. Their ordinary FULL demand is decoded before discarding only
the flag. CM/sink checks still have real local marked memberships and their
seeds; sources and accepted bindings are not deleted as allegedly redundant
rules. This supplies the missing concrete starts in the counterexamples.

For statics, preserve local writer registration, actual supply and waiting
read effects before pruning. A pool supply is not a relation proof or a
globally protected mark. ZERO-created marks and erased static/static
relations keep their existing treatment. The selected static completion
adapter is inherited only for its existing grammar; it is not used to
admit arbitrary nonstatic marked queries. Exact marker and unsupported
static cells retain the fallback.

**Boundary of the mechanization.** The Lean result checks scalar AP
application, constructive dependency extraction, normalization and demand
certificates. It does not prove a Kotlin/IR refinement or all native-call,
ND, observation and static-service adapters. The specification requires
their exact decode or local correspondence tests before enabling an
optimized path. Failure of such a test requires fallback within the
selected semantics, not an unannounced field/query-policy change.

## 8. Scheduling, finite progress and observations

The priority kernel keeps four nonzero lanes. `pop_exact` proves it removes
exactly the head of their FLOW-first linearization and retains every other
item. `pop_decreases` proves the ready count decreases by one. A changed
FLOW item precedes unchanged TAINT. ZERO/control selection stays outside
this kernel.

The projected admission rank is the sum of the three Boolean bits. It is
at most three; every novel offer strictly raises it. Thus one key admits
at most a FLOW event, an ordinary member and a protection upgrade. Repeats
do not generate new work. With a finite complete key domain and bounded
per-admission continuations, fresh work consumes finite admission credit.
`finite_measure_decreases` proves that pending work plus remaining credit
decreases on each processed item. Consequently local FLOW priority cannot
starve a finite ready TAINT closure. It is not a proof that the whole
analyzer always has a finite key domain.

At completion, no work can remain hidden in protection or continuation
lanes. `barrier_drained` checks that condition. For unchanged-repeat sets,
quantum, cancellation, current call stages and producer callbacks, source
correspondence tests are required: these are concrete queue adapters,
not properties of a four-list toy scheduler alone.

Compare complete logical report/source/sink/rule-binding keys. Metadata-only
upgrades update the same occurrence rather than emit another occurrence.
Changing packet/callback counts is allowed. Mark memberships needed for
observers remain decoded at the observer boundary, so transport pruning
cannot make a satisfied CM or sink disappear. Neutral-step finite trace
lifting preserves these observations when the complete observer adapter
is unchanged. Do not apply that claim to alias/identity classifications
without the specification's additional equality test or fallback.

The existing alias classifier also has a checked ANY cell. The theorem
`any_flow_alias_effect` shows that an ANY FLOW output has a memory effect
under that classifier: its initial and final tails are not both STAR.
`same_base_nonidentity_any_alias_effect` shows that a same-base diagonal
TAINT output also has a memory effect when its path differs from the initial
path. The AP coverage and application theorems already permit equal bases.
Thus the two classifications agree for that nonidentity output. In contrast,
`same_path_any_alias_mismatch` checks the same-path case, where the TAINT
output has no memory effect and the ANY FLOW output has one. Keep that
marked output. Split a mixed tree per output path; do not require a different
base for every eligible output. These laws use the existing classifier and
do not change alias application.

## 9. Counted saving and checks

The counted cost is **geometry applications/containers**, not CPU time or
all allocated bytes. k scalar members cost k geometries. A nonempty exact
shared row costs one geometry plus its exact mask/header. The model proves
one is no greater than k, and is one for every nonempty row. Semantic
replacement further removes covered plain publication memberships; it does
not remove required observers, protected members or cross-mark dependencies.

The recorded Thingsboard sample precedes protection. Its overlap percentage
cannot be used as a final deletion rate. No new speedup or completed run
result is claimed. Latest reached iteration remains **run-1 OOM**.

Run from `spec/lean`:

```sh
lake build ApSpec.FlowBackedStore ApSpec.FlowBackedPriority ApSpec.FlowBackedHandoff ApSpec.FlowBackedRelationsCounterexamples
lake env lean run1-flow-backed-concrete-relations-audit.lean
```

The [receipt](lean/run1-flow-backed-concrete-relations-checks.json) pins the
source hashes, commands and results. The audit checks every declaration
owned by the six new modules and runs executable controls. Only the existing
`propext` and `Quot.sound` dependencies are permitted; no Classical choice,
`sorryAx` or new axiom is permitted. The integrated build passes **191 jobs**;
the owned audit checks **460 declarations** and **32 executable controls**.
Runtime adapter checks remain an implementation gate. The
[implementation validation](../docs/reports/bidirectional-flow-backed-concrete-validation-20261024.md)
records local correspondence checks and their limits.
