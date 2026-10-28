# Restricted-run demand, static handoff closure and run-1 exit routing

Date: 28 October 2026. Status: **final design; implementation in progress**.
This is the complete contract for the selected iteration. It replaces
the earlier partial description in this file. The original reference is
[AP](ap.md), sections 6.3, 6.4, 8.5–8.7 and 9.2. The required behavior is
restated below, so the reader does not need the preceding design discussion.
The [earlier investigation](../docs/design/bidirectional-restricted-fact-management-20261027.md)
is supporting evidence, not an additional policy. Follow
[proof-guide.md](proof-guide.md).

The [short modification summary](../docs/design/bidirectional-restricted-demand-summary-20261028.md)
lists modified, added and removed parts, with before/after behavior and
their original-AP, later-extension or new-logic basis.

The [implementation checks](../docs/reports/bidirectional-restricted-demand-validation-20261027.md)
found three correctness cases. On 28 October, the user selected Empty field
exclusions for abstract STAR demand. Apply that rule to demand copies on
both entry and exit; retain actual and native-record exclusions. This
supersedes the exclusion-union candidate in the
[earlier repair design](../docs/design/bidirectional-restricted-demand-open-contracts-20261027.md).
The 28 October follow-up also selects immediate concrete supply at the
executed write point, independent of summary processing. Keep its FLOW
writer. Correct the stale named-field STAR validator and retain lost exit
writers in a separate guidance store. The
[follow-up review](../docs/design/bidirectional-restricted-demand-followup-20261028.md)
records the history. The complete normative workflow is below. Finalizing
this design does not mean that implementation or project acceptance is
complete.

The reviewed checkout is `e908c95899f98ef5ad60b24710aff72225021d18`;
its runtime core is `57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`.
The second review used `eab0b032c7c85e248a3b5d1fdf2c14cea3609aca`,
with the same runtime core.
The latest referenced Thingsboard campaign reached **run-2**, completed
**run-1**, and accepted **run-1**. No project was rerun for this design.

## 1. Original design, current implementation and selected changes

“Original” below means the original AP demand protocol and ordinary
exit-summary protocol. It does not select a rollback of all later AP
extensions. In particular, correlated concrete STAR starts, FLOW-backed
relations, mark protection, current run-1 field processing and the selected
run schedule remain in scope as stated below.

| Mechanism | Originally designed behavior | Current implementation | Proposed behavior |
|---|---|---|---|
| Restricted initial emission | Match actual input against fixed demand; use all matching entry patterns | `StrongQueries.admit` starts a canonical actual-input query even without demand | Restore demand-only emission for both restricted directions |
| Abstract entry pattern | Emit one FLOW premise, shared across admitted caller marks | Only concrete guide entries refine the actual query; abstract guides do not start shared FLOW | Restore shared FLOW emission; do not filter abstract guides |
| Concrete entry pattern | Intersect with an actual concrete mark; never get T from FLOW | Concrete intersections are additive to actual-query starts | Keep only the original demand intersection |
| Summary permission | C5 for ordinary summaries; the original backward seed-return rule is separate | `currentQueries.permits` can additionally publish raw summaries | Restore C5 and retain the original backward seed-return route, explained in section 3.6 |
| Later input after a raw result | Replay existing publications and applicable records | A new query can scan all raw summaries and republish permitted originals | Remove that scan; demand stays immutable |
| Demand selection at handoff | DEMAND, normal ND, and normal backward-ZERO publications are selected; other normal singletons supply records | `config.run1 || ...` selects every run-1 publication | Restore original selection in every run, including run-1 |
| Static/static relations in run-1 | Ordinary AP can retain and apply relations which reach the exit | Current special static path erases them before storage/publication | Keep thin post-exit and lost-exit guidance keys; do not publish them during run-1 |
| Static-related missing guidance | Ordinary AP uses the guidance from its executed summaries | General SQ, an implicit group family and same-field ANY-to-EXACT completion cover more inputs | Complete static-related guidance once at run-1 → run-2; use original AP to execute it |
| Static producer conclusion | Ordinary exit summaries pass exit rules | Local writes and call static results go to `retainSummary` immediately | Route them to the existing post-return NormalExit, then run exit rules and common summary emission |
| Actual write visibility | A write is an effect at its operation | Nonstatic colored supply relied on outward caller application | Local executed write supplies its concrete output immediately; retain its FLOW writer; summary processing is independent |
| NORMAL persistence | Persist eligible raw normal singleton summaries, with their legal exclusions | Raw persistence exists | Keep it; synthetic completion is never a record |
| STAR in handoff | Keep STAR and legal field E; normalize mark exclusions separately | `HandOff.toBackward` changes a STAR result to ANY and clears E | Keep STAR. For an abstract STAR demand endpoint, ignore field E. Keep concrete demand E and native-record E. |

These changes restore the original authority of demand. They deliberately
change the current executable initial set and publication set. They are not
semantics-preserving replacements for the current SQ implementation.

The new static closure is an over-approximation used to guide real run-2
execution. It is not a new transfer rule. The exit shortcut is a selected
run-1 transfer approximation. It cannot establish a confirmed normal flow.

The second review corrects two mistakes in the preceding proposal. Its
STAR-to-ANY handoff rewrite was taken from the current implementation,
not the original AP contract. Its deeper concrete-STAR intersection could
also copy E to the wrong path. Restoring STAR demand and rebasing that
intersection are explicit changes to demand handling. They do not change
ordinary field transfer or invent concrete marks from FLOW. The newly
reachable MUST-input/STAR-entry intersection is specified below instead
of leaving the old typed-domain assertion in place.

After run-1, complete the missing demand through static positions. Keep
ordinary restricted-run emission and complete entry/exit restriction.

```text
known forward relations in one method:
  x -> C1
  C1 -> C2
  C2 -> y

completed forward guidance:
  x -> C2
  C1 -> y
  x -> y

run-2 demand is the ordinary reversed projection of those relations.
```

Keep C1-to-C2 relations at their original run-1 owners. Make their effects
available to transitive callers at handoff. Do not publish these relations
to callers or propagate their static facts through ordinary run-1 code.

Also change the terminal path for a run-1 static conclusion:

```text
current: static producer -> immediate summary insertion
new:     static producer -> graph.exitInst -> exit rules -> common summary emission
```

The target is the existing **NormalExit boundary after return**. It is not
the return instruction. No return transfer or skipped instruction runs on
the shortcut. The user explicitly selected exit rules and summary only.

These are major changes to guidance construction and to which exit rules
observe a run-1 static fact. They are not storage-only optimizations.

Keep these mechanisms unchanged:

- Rule bodies, source/sink identities, full ND guards, ZERO-origin rules,
  concrete marks, group ownership and FULL/GROUP specialization.
- Field transfer, tail kinds, later strong writes, field exclusions and
  existing protection on executable facts. No GroundingSupport is added.
- Local static write presence, FLOW writers, global mark supplies and
  req/reach/processed ownership. A caller summary is not a new local writer.
- Run-1 mark mode, the static diagnostic flag, aliases and the enum hack.
- Record application, sink seeds, source hits and backward ZERO return.
- Run-2 backward FULL limit 1, then run-3 forward FULL limit 2 and the
  existing increasing-limit policy. No limit zero.
- IR storage, references and cache management.

All newly completed relations are **guidance only**. They are not executable
run-1 summaries, normal records, new group supplies or confirmed flows.
Run-2 must derive every answer with its real body, call bindings and rules.

## 2. Terms and fixed invariants

A scalar fact has `(base, path, tail, fieldExclusion, mark)`. Packed FLOW
and TAINT trees represent unions of these scalar facts. Use the existing
tree operations; the scalar notation below does not require leaf expansion
in production.

| Term | Meaning |
|---|---|
| `$`, or EXACT | The path itself; no nonempty suffix |
| `*`, or STAR tail | Correlated continuation of the input path; its field exclusion rejects specified first suffix accessors |
| `[any]`, or ANY | A may region at and below the path; it has no field-exclusion slot |
| `[any-taint]`, or MUST | A forward concrete must region with its own legal field exclusion; absent from backward facts, initials and demand |
| FLOW mark `*` | A pass-through mark; it is not a concrete T and cannot satisfy CM(T) |
| FLOW mark `*∖X` | A pass-through mark with mark exclusions X; runtime tests read them |
| T, U | Full concrete mark identities in FULL mode; a group selector is explicit in GROUP guidance |
| NORMAL, DEMAND | Independent edge layers. Selection for handoff does not change a layer |
| Initial `j` | A complete canonical method assumption, including base, path, tail, applicable E and mark |
| Original `J` | One initial or the complete ND premise set; ZERO is the existing zero original |
| Demand `(Dc, Dp?)` | Entry pattern and optional exit pattern in the receiving direction; it is guidance, not an executable edge |
| Raw summary | A body-derived relation after normal exit rules, before restricted publication |
| Publication | A raw summary's permitted restriction, with the complete original J retained |
| Record | An eligible raw NORMAL singleton summary persisted across completed-run barriers |
| Complete run | Its fixed point, including all counted resumes, effects and publication delivery; an OOM/timeout prefix is incomplete |

Paths are accessor sequences. `p <= q` means that p is a prefix of q. A
tail admits the empty suffix. EXACT admits no nonempty suffix; ANY admits
all suffixes; STAR and MUST reject a nonempty suffix if its first accessor
is in E. Different bases or divergent paths have no location overlap.
Marks have their existing separate matching relation. Field exclusions
and mark exclusions must not be confused.

Run-1 is forward with limit 1. Run-2 is backward FULL with limit 1. Run-3
is forward FULL with limit 2; later runs increase the limit as now. No
limit-zero mode exists. FULL remains the default run-1 mark mode; GROUP
remains supported. The diagnostic `disableRun1Statics` flag keeps its
existing scope and is not a sound production mode.

Keep current field transfer and the E-free run-1 contract. An overwrite
which would require a field-exclusion change moves the affected relation
to DEMAND with empty E; a definitely overwritten precise field is killed;
an unrelated precise field passes. Do not introduce weak-write semantics,
change a STAR tail into ANY merely on demotion, or add actual-input
grounding. Keep later-run strong writes, cleaners, primitive handling,
aliases, input alias closure, FLOW replacement and protection unchanged.

Keep run-1's complete rule guard before emitting each contributing
singleton original. A ZERO original is emitted only when a complete cube
can be satisfied by ZERO-origin inputs. Later forward runs keep full ND
premises and their complete support requirements. This proposal does not
change rule conditions, actions, specialization, equality or hashing.

**Run-1 cannot produce an ND edge in the current implementation or this
proposal.** Every run-1 executable original is one `InitialAp`, including
ZERO. `PremiseSet` is invalid at its point stores, summaries, subscriptions
and static seed boundary. A rule can have an ND guard, but only after the
complete guard succeeds does it emit one singleton edge per contributing
original. An ND guard is not an ND edge. There is no run-1 normal ND
handoff case. The generic ND publication rules below apply to later
forward runs (run-3 and later); backward runs also have no ND edges.

The current `forceRun1Layer` policy makes every run-1 TAINT result, static
result, or result with a static original DEMAND, including FULL mode.
Keep that policy. Restoring demand selection does not promote these
relations to NORMAL. Changing that policy needs a separate decision.

## 3. Restricted runs: restored original AP protocol

This section applies to **every run after run-1**, in both directions.
Incoming demand and the record view are immutable for the complete run.
The static completion in later sections is one part of the incoming
run-2 demand, not an exception to this protocol.

### 3.1 Ownership and input arrival

| Store | Owner and lifetime | Stored value and purpose |
|---|---|---|
| Demand | Shared immutable snapshot, one run | Complete normalized `(Dc,Dp?)` patterns by MethodKey |
| Records | Persistent; read-only view during a run | Eligible native NORMAL relations and permitted read views |
| Subscriptions | Caller, one run | Actual callee input, complete caller original, call/stage, layer and binding information |
| Initials | Callee method actor, one run | Complete canonical initials already started |
| MethodEdgeStore and worklist | Method actor, one run | Admitted point facts and fresh value/protection/resume deltas |
| Raw RunSummaryStore | Method actor, one run | Body-derived post-exit relations, including the raw NORMAL values needed by persistence |
| Selected summary publications | Method actor, one run | Published pieces selected for the next demand snapshot |
| SummaryStorage and publication directory | Existing run owner | Permitted publications for replay and fresh notifications |
| Pending publication batch | Method actor until its existing barrier | Fresh publication deltas, detached before delivery |

There is no callee added-fact history and no later-run request store.
Caller subscriptions retain the actual inputs needed to apply answers.
Initial deduplication is not a permission table.

```kotlin
fun enterCallee(ref: CallerRef, actual: Facts) {
    subscriptions.registerAndReplay(ref, actual)
    records.replayApplicable(ref, actual)
    calleeOwner.send(LinkIn(ref, actual))
}

fun onRestrictedLink(actual: Facts) {
    validateBoundedInputAndStaticGrammar(actual)
    val candidates = linkedSetOf<DemandPattern>()
    for (leaf in ops.leaves(actual)) {
        candidates += demand.near(key, leaf)
    }
    for (d in candidates) {
        for (j in ops.emit(d, actual)) addInitial(j)
    }
}
```

Register the subscription before reading existing publications. Input-first
and answer-first arrival must produce the same applied relation set. A
record match does not suppress all demanded body execution. A later input
does not scan raw summaries or create a new exit permission.

### 3.2 Entry emission

`near` supplies entry ancestors, the same path and strict descendants.
It is only a candidate lookup. Run the full AP location/mark/exclusion
test on every candidate. Union and deduplicate emitted initials.

| Entry mark | Actual input mark | Result when locations overlap |
|---|---|---|
| Concrete T | T | Concrete location intersection, preserving actual T |
| Concrete T | Different full U, or FLOW with any mark exclusion | None |
| Group selector G | Actual full T in G, where the selected adapter admits it | Ordinary concrete intersection with actual full T |
| Abstract `*` | Any admitted actual mark | FLOW form of Dc, not a concrete projection of the actual input |

Do not enumerate full marks of a group. The existing selector relation
tests actual membership. The abstract branch must not be filtered out.

Normalize the offered abstract STAR demand before entry emission and C5.
Use the same endpoint rule for Dc and Dp:

```kotlin
fun normalizeDemandFieldExclusion(p: Pattern): Pattern =
    if (p.fact.mark is MarkSlot.Star && p.fact.tail == Tail.STAR)
        p.copy(exclusion = ExclusionSet.Empty)
    else p
```

This is a demand-copy operation. Do not clear actual input E, ordinary
transfer E, concrete demand E, or raw/native-record E. Keep existing mark
exclusion normalization separate. Normalize before demand deduplication.
Nonempty offered E is valid on an abstract STAR endpoint and is ignored;
it is not an admission error or a reason to build an E-union initial.

| Offered abstract entry tail | FLOW initial tail |
|---|---|
| EXACT | Generic EXACT; forbidden as a typed FlowTree initial |
| ANY | STAR with empty E |
| STAR/E, for any E | STAR with empty E |

Keep entry base/path and mark `*`. Both admitted abstract forms give one
shared STAR/FLOW initial with empty E. The normalized entry satisfies the
original C2 guard by construction; no producer invariant is required.
A preserved concrete STAR demand keeps its legal E and uses the concrete
intersection below. This is an explicit change from preserving abstract
demand E. It does not change STAR into ANY or change field transfer.

For a concrete entry with path p, intersect locations as follows:

| Actual path q versus p | Emission |
|---|---|
| Different base or divergent paths | None |
| q strictly below p | Actual fact, if the entry tail admits the suffix |
| q = p | Same path, tail meet |
| q strictly above p | At p, tail meet, if the actual tail/E admits the suffix |

The tail meet for equal paths is:

| Actual tail | EXACT entry | ANY entry | Generic STAR/E2 entry |
|---|---|---|---|
| EXACT | EXACT | EXACT | EXACT |
| ANY | EXACT | ANY | STAR/E2 |
| MUST/E1 | EXACT | MUST/E1 | MUST/(E1 union E2) |
| Correlated concrete STAR/E1 | EXACT | STAR/E1 | STAR/(E1 union E2) |

The MUST/STAR cell is required when STAR demand is preserved and the next
forward run receives a must fact. The old implementation rejected this
cell because its builder prohibited STAR entries. Union of exclusions is
the location intersection; the initial keeps the MUST kind, actual mark
and the existing start-layer policy. No must fact is introduced backward.

The last row preserves the already selected correlated-STAR extension.
Restoring the original protocol does not revert it to the historical
STAR(T)-to-ANY(T) start. At a deeper demand path, use the existing rebased
intersection: a retained MUST **or concrete STAR** region forgets the
ancestor's E after the strict descent is admitted. Intersect that rebased
region with the demand's tail/E at the new path. EXACT has empty E.

```kotlin
// Only the strictly-above branch, after actual.tailAdmits(suffix) succeeds.
val rebased = actual.copy(exclusion = ExclusionSet.Empty)
val (tail, e) = meet(rebased, entry) // Includes MUST intersect STAR.
val initial = Pattern(entry.fact.copy(tail = tail, mark = actual.fact.mark), e)
```

For `actual=x/STAR/{f}/T` and `entry=x.g/ANY/T`, g is allowed and the
initial is `x.g/STAR/{}/T`. Keeping `{f}` at x.g would incorrectly lose
x.g.f. This correction changes only the emitted intersection, not the
stored incoming fact or its exclusion.

C2 is the required coverage contract: for every common admitted location
and mark of the actual input and normalized Dc, emission supplies a
satisfiable initial covering it, wholly inside normalized Dc. The offered
abstract E is no longer a containment bound. C3 preserves the actual
concrete mark for a concrete entry and emits `*` for an abstract entry.
The original C2 guard holds for the normalized abstract entry. Actual E
still rejects blocked descents during overlap and ordinary matching.
For a concrete entry, this contract also requires concrete input eligibility.
It does not promise specialization of an abstract actual input to T merely
because a set-theoretic reading of that input includes T.

Do not read "intersection" as a symmetric set operation on marks:

```text
emission entry * , actual T       => shared FLOW initial, mark *
emission entry T , actual *       => no initial
emission entry T , actual *∖{U}   => no initial, even when U != T
emission entry T , actual T       => location intersection, mark T
```

The concrete-entry eligibility gate precedes location intersection. An
abstract input is not evidence of a concrete mark. Conversely, the FLOW
initial for an abstract demand does not copy actual T or its mark exclusions.
The actual caller input remains intact and filters/instantiates the answer.

No matching entry means no nonzero initial. Do not synthesize an entry
pattern from the actual input. Do not add a same-field EXACT initial merely
because an actual concrete static input has ANY. An explicit EXACT demand
can still produce the ordinary exact intersection.

### 3.3 Initials and execution

```kotlin
fun addInitial(j: InitialAp) {
    validateDirectionBoundAndGrammar(j)
    if (!initials.add(j)) return
    startAtExistingEntry(j, ops.startFact(j, mode))
}
```

Keep the current starting-fact table, including selected AP extensions:

| Initial | Start conclusion | Layer before the unchanged run-1 override |
|---|---|---|
| ZERO | ZERO | NORMAL |
| STAR/E with FLOW mark | Same correlated fact | NORMAL |
| STAR/E with full concrete T | Same correlated concrete fact | DEMAND |
| ANY with concrete T | Same may fact | DEMAND |
| MUST/E with concrete T | Same must fact; forward restricted runs only | NORMAL |
| EXACT with concrete T | Same exact fact | NORMAL |

Method work uses the existing transfers, limit, rules, cleaners, bindings,
alias expansion and annotation deltas. There are no mark requests after
run-1. In particular, an abstract FLOW body cannot manufacture T to cross
a CM(T) gate. A required marked path needs a concrete demand or its valid
record route. This is why the handoff must retain colored static paths.

One FLOW initial serves every actual Ti admitted by its abstract entry.
The caller instantiates its published FLOW answer against its actual Ti
through ordinary summary satisfaction/application. The callee does not
execute that FLOW body once per actual mark.

### 3.4 Paired summary restriction

For a raw `J -> g`, try every member j of J against every candidate
`(Dc,Dp?)`. Normalize abstract STAR field E on both endpoints first.
`covering` supplies entry ancestors and the same path. Reject the candidate
unless:

1. Dp exists.
2. The **whole** j lies inside Dc in locations and marks, including legal E.
3. The conclusion mark meets Dp's mark.
4. The conclusion base agrees with Dp's base and its locations overlap.

For canonical Dp, the mark gate is:

| Exit mark | Concrete U conclusion | Abstract conclusion `*∖Y` |
|---|---|---|
| Concrete T | Keep only when T = U | Keep only when T is not excluded |
| Group selector G | Keep an actual member U of G | Use the existing selector/exclusion test |
| Abstract `*` | Keep | Keep |

The gate does not change an abstract result into a concrete one. A concrete
entry cannot authorize a FLOW premise. Entry overlap alone is insufficient.

Exit reduction has a different role from entry emission:

```text
exit demand T , conclusion *       => keep conclusion *, not T
exit demand T , conclusion *∖{T}   => reject
exit demand T , conclusion *∖{U}   => keep *∖{U}, when U != T
exit demand * , conclusion T       => keep T, not *
```

For example, with `j=x/STAR/*`, raw `g=ret/STAR/*` and demand
`(x/ANY/*, ret/ANY/T)`, C5 keeps g unchanged. Applying that shared summary
to an actual U passes U; it does not generate T. The publication can extend
outside the concrete exit demand, as the original representability rule
allows. Its pairs still come from the raw correlated relation.

Reduce the permitted conclusion geometry as follows. Let p be Dp's path.

| Conclusion position | Reduction after the gates |
|---|---|
| At p | Use the tail table below |
| Strictly below p | Keep if Dp's tail/E admits its suffix; otherwise reject |
| Strictly above p, ANY | At p: EXACT for exact demand, otherwise ANY |
| Strictly above p, MUST/E | Reject if E blocks the suffix; otherwise at p: EXACT for exact demand, MUST/E2 for STAR/E2 demand, MUST/empty for ANY demand |
| Strictly above p, STAR/E | Keep the complete correlated conclusion if E admits the suffix; otherwise reject |
| Strictly above p, EXACT; divergent paths | Reject |

| Conclusion tail at p | EXACT exit | STAR/E2 exit | ANY exit |
|---|---|---|---|
| EXACT | EXACT | EXACT | EXACT |
| ANY | EXACT | ANY | ANY |
| MUST/E | EXACT | MUST/(E union E2) | MUST/E |
| STAR/E | STAR/E | STAR/E | STAR/E |

Ignoring abstract STAR exit E can permit a raw result which the old Dp
excluded. This is an explicit publication-permission widening. It adds no
pair to the raw relation. Concrete Dp E and the raw conclusion E still use
the table above; do not clear them.

Preserve the original J, conclusion marks, layer and required protection.
Union pieces from all successful members/patterns. An ND publication
retains **all** of J; one matched member is not a sufficient caller input.
Caller application still needs every premise under the existing ND rule.

C5 requires every demanded pair of a wholly contained member to survive,
and forbids introducing a pair absent from the raw relation. It does not
promise exact global narrowing: an uncut correlated STAR, its abstract
mark, or an ANY fact without an E slot can extend outside Dp. Keep these
original representability limits. An absent Dp gives no ordinary summary
publication. The backward-ZERO exception is defined in section 3.6.

### 3.5 Raw storage, publication and outgoing selection

```kotlin
fun finishSummary(original: PremiseKey, offered: Facts) {
    val delta = rawSummaries.add(original, offered) ?: return
    val selected = ops.demandPart(original, delta, direction) != null
    val pieces = when {
        run1 -> listOf(delta) // Except private static/static seeds, section 5.
        direction == BACKWARD && original.isZero -> listOf(delta)
        else -> unionOfAllMemberRestrictions(original, delta, demand)
    }
    for (piece in pieces) {
        if (selected) selectedPublications.add(original, piece)
        pendingPublications.add(Publication(original, piece))
    }
}
```

Run-1 uses the same **selection** predicate as other runs. A raw group is
selected exactly when its layer is DEMAND, its premise is multi-member,
or it is a backward ZERO-premise group. Selection is independent of tails
and of which publication pieces result. Store the selected publications,
not the unrestricted raw value, as ordinary next-run guidance.
For run-1 specifically, no multi-member or backward case is possible:
the predicate reduces to `delta.layer == DEMAND`. A run-1 NORMAL singleton
supplies its eligible record only. Keeping the generic selector does not
authorize a run-1 PremiseSet.

Eligible raw NORMAL singleton relations persist at a complete barrier,
including legal nonempty field exclusions. Native backward ZERO relations
and ND relations do not become records. Native record kind checks and
permitted opposite-direction read views remain unchanged. Persist the raw
relation, not a narrowed publication; a source hit is not fabricated from
a record read. Other normal singletons are record-only and are not also
ordinary demand. All synthetic static closure rows are guidance-only.

Because demand is frozen, the first restriction already sees every allowed
exit for an original. Late callers replay publications and applicable
records. There is no query-triggered `summaries.all()` authorization scan.

### 3.6 ZERO, seeds, sources and observations

The backward ZERO route is the **original balanced seed return**, not a
new exception introduced by this proposal or by StrongQueries. The first
comparison table previously omitted it from the original column; that
description was incomplete.

Its history in this repository is:

| Update | Evidence |
|---|---|
| F57, 6 October 2026, commit `efd7b637374b6011f69964ebfdac6c8f6562f941` | Replaced direct sink seeding/plain reversal with root ZERO, callee ZERO entry, ZERO-to-requirement seeds and balanced returns; `Backward.DB.zret` has no demand restriction premise |
| 7 October 2026, commit `6b2b0fd5b` | Made the prose explicit: the callee does not restrict this summary and the caller makes no satisfaction test; section 9.2's balanced-return paragraph |
| 11 October 2026, commit `b65b46d766790956bbfd50efaf74e706271eddf3` | The first `RunMethodAnalyzer` implementation already published raw backward ZERO summaries, before StrongQueries existed |

The current original AP text states it in sections 4.3, 6.4 and 9.2.
[F57](ap-history.md) records the design decision. It was absent from the
earlier pre-F57 direct-seed design, not from the selected original AP
protocol used as the reference here.

```java
void main(Object p) { helper(p); }
void helper(Object q) { sinkT(q); }
```

Backward ZERO enters helper from this call. At its sink, the seed creates
`ZERO -> q/T`. The requirement reaches helper's forward entry and returns
through the **same call subscription** as `ZERO -> p/T` in main. There need
not be a nonzero return-summary demand in helper: q is consumed locally.
Ordinary `(ZERO, no-exit)` demand cannot publish this requirement under C5.
The dedicated balanced route carries it out; ordinary reversed transfer
then determines whether it reaches an actual source.

This applies only to a backward summary whose **original is ZERO**. It
does not apply to `j -> ZERO` with nonzero j, to a forward source summary,
or to a nonzero static premise. It grants no new initial/query permission,
does not remove field limits, and does not make the seed path a normal
record. It remains balanced at an actual call, rather than broadcasting a
requirement to unrelated callers.

Keep the existing exceptions and seed roles:

- Root ZERO starts directly. Forward ZERO emission uses the existing implicit
  zero entry. Backward ZERO enters each reached callee directly at its
  forward exit; this direct entry does not depend on a nonzero demand.
- A backward ZERO-premise result returns to the caller ZERO which entered
  that callee, with reversed binding and field limit. It bypasses ordinary
  restriction/satisfaction only for this existing balanced-return route.
  It is selected for handoff and is not persisted as a backward record.
- A forward DEMAND report entry supplies full sink requirements at the
  witnessed MethodKey/statement in the next backward run. Preserve its
  bound rule occurrence and complete positive NNF seed scope. A backward
  run does not independently check sinks or perform an AND seed join.
- Backward reversed end-fact triggers retain their existing full seed
  scope, including the necessary trigger of an already confirmed sink.
  The separate `trackFactsReachAnalysisEnd` input remains empty by the
  earlier selected decision; this proposal does not enable it.
- A real reversed unconditional source records the existing source hit.
  Source hits restrict unconditional sources in the next forward run.
  Conditional sources, ZERO keeps and valid end-fact triggers retain
  their existing roles. Run-1 fires all selected sources.
- Preserve report/source/sink identity and rule occurrence identity.
  Batching-dependent callback diagnostic counts may change. No incomplete
  run is accepted as a handoff or new report result.

ZERO is not a substitute for a concrete T input. ZERO can satisfy a static
summary premise only under the already selected **run-1** static rule.
After run-1 the actual static premise is required.

### 3.7 Ordinary handoff normalization

For each selected forward publication and each member j of its original,
construct `(entry = normalized conclusion, exit = normalized j)` for the
backward run. For a selected nonzero backward publication, do the same
swap for the next forward run. A backward ZERO-premise publication has
its conclusion as entry and **no exit**. Keep the forward implicit ZERO
entry. Backward seeds and forward source hits are separate from these
summary pairs.

Use the selected AP normalization, including the MUST-location conversion
and the 28 October abstract-demand E rule, in explicit and virtual patterns:

```text
MUST/E endpoint       -> ANY, empty E, without the must guarantee
FLOW mark *∖X        -> FLOW mark *, without mark exclusions
concrete mark         -> keep full identity or explicit group selector
abstract STAR endpoint -> keep STAR; ignore field E on either side
concrete STAR endpoint -> keep STAR and its legal field E on either side
```

Remove the current blanket STAR-entry rejection. Abstract entries use ANY
or STAR/empty E. Concrete entries can use EXACT, ANY or STAR/E. An EXACT
exit still requires a concrete entry mark in the typed adapter. No demand
endpoint has MUST or mark exclusions. Keep the static anchor grammar.

The current `HandOff.toBackward` STAR-to-ANY conversion was added in
`28a123f0eac937e8f2feca9ee5dd84e38fa8f979` on 16 October, together with
StrongQueries. It is not original AP normalization. It loses correlation
and possibly E. The preceding draft incorrectly retained it as an existing
typed construction rule. Remove this rewrite and update the typed builder
and concrete intersection cases specified above. Do not turn the old
canonical-shape theorems into assumptions about this extended producer set.

The run-1 static completion below uses E-free run-1 endpoints and this
same projection. Normal summaries and records retain all runtime E and
mark exclusions. A generated abstract STAR/E demand is accepted: its
canonical demand copy uses Empty E. The source relation and actual input
remain unchanged. The selected rule applies to both handoff directions.
It replaces the false abstract-STAR producer guard.

## 4. Static endpoints and relation kinds

`C` denotes a complete bounded static position, not only a field name:

```kotlin
sealed interface StaticPosition {
    data class Field(val classId: Int, val fieldId: Int) : StaticPosition
    data class ExactGlobalMarker(val classId: Int) : StaticPosition
}
```

Keep its legal tail and mark information. A bare exact global marker is
distinct from a field. It does not stand for every field of its class.
There is no class-wide FULL mark or broad root FULL input.

A bounded run-2 FULL named-field input can have EXACT, ANY or STAR/E.
EXACT/ANY have Empty E; STAR keeps its legal concrete E. An exact class
marker has EXACT/Empty E. Backward MUST is forbidden. The old validator's
EXACT/ANY-only field test assumed concrete STAR-to-ANY starts; the selected
all-run correlated-STAR change supersedes that assumption. Both first
limits were already 1 when that old validator was added. A bounded C.f.*
fact stays STAR at limit 1 or 2. The demand intersection then decides which
initial can start; validation itself grants no new demand.

This current-input domain does not add STAR source/sink rule literals or
micro-edge target constructors. Their existing EXACT/ANY target grammar
stays unchanged. A legal correlated STAR can arrive from ordinary execution
and call transport without being a legal literal passed to targetTree.


`x` and `y` are method boundary positions under a complete MethodKey. They
can include an argument, receiver, return, exception or an actual ZERO
endpoint where the existing rule permits it. They are not arbitrary locals.

Define forward-oriented seed families:

```text
W[M]  : nonstatic or ZERO -> static
R[M]  : static -> nonstatic or ZERO
B[M]  : static -> static
O[M]  : other existing selected guidance relations
```

R uses the already propagated run-1 relations. W uses ordinary selected
writers plus lost exit writers and their joined actual caller bindings.
B includes retained/lost static copies and rows created by writer binding;
it is retained without live caller propagation. Do not copy
a callee's argument/return names into a caller during handoff.

Collect ordinary W/R through the existing outgoing demand selection.
Collect lost exit writer dependencies through section 6, as guidance only. Under the
unchanged run-1 static layer policy these relations are DEMAND. A genuinely
NORMAL singleton remains record-only; it is not a new ordinary demand seed.
O contains selected guidance, not every raw NORMAL summary. Completion does
not change ordinary record selection.

The prescan graph already resolves calls. Keep a detached immutable adjacency
view through the run-1 handoff. Its current export is method-level; static
relations can use the accepted method/context approximation. W/R endpoints
remain owned by their complete MethodKey. Only B travels up the graph.

For a MethodKey K, static seed visibility uses `K.method` and all seed
owners whose methods are reachable from it. Owner contexts can contribute
to this conservative static view. W/R attachments always use the exact K;
never copy or merge their nonstatic endpoints by method name alone. The
view must also work for a run-2 actor which had no run-1 actor: it reads the
detached graph and has empty local attachments where none were collected.

Detach the method IDs and adjacency at prescan completion, before the current
catalog-coverage release clears that information. Freeze the seed inventory
at the later run-1 barrier. Do not retain the prescan runner or its mutable
method catalog to recover adjacency at that barrier.

Call-order and context approximation remain conservative run-1 guidance.
Two sibling callees can contribute composable static relations to a caller.
This does not assert that their operations execute in that order. Run-2
checks real order and body reachability.

## 5. Run-1 static conclusions go through NormalExit

### 5.1 Target and ingress

The JVM graph already has `JMethodExitNormalInst` after its return paths.
`JIRMethodEntry` requires the boundary triple; the single-exit graph exposes
this normal boundary even when it has no reachable return predecessor.
Use this existing node, conceptually `graph.exitInst`.

```kotlin
fun routeBoundedRun1StaticToExit(original: PremiseKey, bounded: Facts) {
    check(run1 && bounded.base == STATIC)
    val exit = context.normalExit  // graph.exitInst, not JIRReturnInst
    val fresh = edges.add(exit, original, bounded) ?: return
    worklist.add(EdgeDelta(original, exit, fresh))
    requestWork()
}
```

Reuse the normal point-store/worklist admission and its annotation deltas.
The NormalExit statement form is empty; ordinary processing goes to the
existing end-rule handler. Do not create a second summary path or synthetic
IR node. Multiple return instructions converge on this one boundary.

Do not test whether the producer can reach that boundary in the remaining
CFG. The selected shortcut skips those instructions. Its run-1 results
remain DEMAND where the existing phase policy requires it. It cannot make
an executable normal record from a demand fact. Later runs keep their
ordinary control flow and receive no shortcut.

A frontend without its required normal boundary violates this contract.
Diagnose it; do not silently drop the fact or create an IR return.

### 5.2 Write points own immediate pool effects

The executed static-write micro-edge owns write presence, FLOW writer
registration and concrete pool supply. These effects do not await summary
processing. Summary handling is orthogonal.

```kotlin
fun onLocalStaticWrite(at: OperationInput, value: Facts, continueRules: ResultSink) {
    val bounded = existingRun1BoundAndChecks(at.premise, value) ?: return
    staticEffects.localWrite(at.premise, bounded)
    // localWrite always admits actual write presence.
    // FLOW: retain its exact existing request-producing writer relation.
    // TAINT: offer the concrete bounded output marks to the pool immediately.
    val boundary = at.site as? ResumeSite.BoundaryInput
    if (boundary != null && !boundary.atStart) {
        if (existingBoundaryHasNormalSummary(boundary))
            killedStaticWrites.observeCandidate(at.premise, bounded)
        continueRules(at.premise, bounded)
    } else routeBoundedRun1StaticToExit(at.premise, bounded)
}
```

For `C.f = p`, keep `p.*/FLOW -> C.f.*/FLOW` at the writer. A static T
request uses that writer to request Base(p)/T. A matching actual caller
input answers it and starts p/T. When the write produces
`p.*/T -> C.f.*/T`, supply T immediately. A mark-changing executed write
`p/T -> C.f/U` supplies U, not T.

Run-1 nonstatic concrete initials are admitted from actual marked inputs
by the existing abstraction/request join. Structural startup emits FLOW,
not arbitrary p/T. Static concrete point initials require pool replies.
Source actions still require their full existing guards; ZERO still needs
a genuine permitted all-ZERO binding. No provenance flag or grounding
store is added. Run-1 field/order/context approximation remains DEMAND.

This explicitly replaces the older rule in grouped-run1-statics.md that
a nonstatic concrete writer needs another outward caller-binding derivation
before it supplies the pool. It does not change later FULL transfer or
allow partial rule guards. Direct test injection of an arbitrary concrete
initial is not proof of the production admission invariant.

Do not fabricate a FLOW writer for a fixed-mark source action. Register
FLOW writers only for actual FLOW write results. Do not retain answered
non-FLOW writers as future request owners. Every supplied mark uses the
executed bounded output region; global three-set admission stays idempotent.

```kotlin
fun onCallStaticConclusion(original: PremiseKey, value: Facts) {
    val bounded = existingRun1BoundAndChecks(original, value) ?: return
    staticEffects.existingComputedSupply(original, bounded)
    // No local write-point registration, producer index, or producer replay.
    routeBoundedRun1StaticToExit(original, bounded)
}
```

Existing computed supplies from ordinary summary application remain valid
and can offer duplicates. They are not a prerequisite for the local write
supply. A killed outgoing summary cannot revoke or delay that earlier
pool effect. Call application never registers a local write point.

Remove the newly added producer PublicationIndex, producer delivery kind,
replay/notification/application methods and dedicated counters. Do not
replace them with a live pre-exit writer publication directory. The
killed-write store below supplies guidance only.

[LocalStaticWriteSupply.lean](lean/proposals/restricted-demand/LocalStaticWriteSupply.lean)
checks the local admission/write contract, FLOW retention, mark identity,
exit independence and idempotent pool union. It assumes the declared
production admission and ordinary AP/complete-rule adapters. It adds no
runtime support metadata or NORMAL record.

### 5.3 Common exit processing

```kotlin
fun processNormalExit(item: EdgeDelta) {
    // Existing exit-rule order and full condition/ND handling.
    endAt(item.premise, graph.exitInst, item.facts, summary = true)
}

fun emitPostExitSummary(original: PremiseKey, value: Facts) {
    if (!original.isZero && original.allMembersStatic && value.base == STATIC) {
        staticGuidanceSeeds.add(original, value) // known, not published
        return
    }
    existingRawSummaryAndPublication(original, value)
}
```

Remove the run-1 STATIC rejection at normal exit in `emitUnchanged`,
`emitAfter` where relevant, and `endAt`. Outside the normal exit, keep the
existing passive-static suppression. Source and sink exit rules now observe
the shortcut input through the common rule handler. Do not impose a new
ZERO-premise restriction.

An exit-rule result is already at the boundary. It must finish common
summary emission, not jump to NormalExit again. Use the existing
`ResumeSite.BoundaryInput(..., atStart=false)` to distinguish rule processing
from an earlier static producer. The work location belongs to the control
path; it is not a new AP fact flag or equality component.
The callback continues the remaining rule/cleaner stages before common
emission. It does not call the summary store from inside a partially
processed rule. Preserve the exceptional boundary's existing `summary=false`
behavior; it is not a second normal-summary route.

Capture B **after exit rules**, before its old erasure point. A complete kill
emits no method relation. A rewrite emits its actual post-rule relation.
Keep the producer's global write effect distinct from this outgoing relation.

## 6. Stores needed for completion

| Store | Contents and lifetime |
|---|---|
| Existing raw/selected summary stores | W, R and ordinary post-exit relations, owned by each run-1 method actor |
| KilledStaticWriteStore | Thin STATIC dependencies not retained by exit processing; temporary candidates until survivor pruning; run-1 guidance only |
| StaticGuidanceSeedStore | Post-exit B relation patterns and exact mark relation; run-1 only, frozen for handoff |
| Detached caller graph | Method adjacency from successful prescan, without old runners, callbacks or fact stores |
| Frozen completion graph | Shared seed IDs, owner memberships, caller reachability/SCC directory and method-local W/R attachments; incoming run-2 only |
| Query scratch | Visited endpoint/mark-relation states for one demand lookup; discarded after lookup |

Currently B is erased, so it has no authoritative frozen relation inventory.
The new seed store is necessary to implement “known but not propagated”.
It is not an additional full Facts store. Convert each existing scalar
premise/output leaf to an immutable guidance key. Share equal keys and pack
exact mark pairs. Do not retain full call plans, input snapshots or closures.

```kotlin
data class GuidanceKey(
    val from: EndpointPattern,
    val to: EndpointPattern,
    val marks: MarkRelation,
)

class StaticGuidanceSeedStore {
    fun add(original: PremiseKey, result: Facts) {
        for (leaf in existingLeaves(result)) {
            internAndMerge(normalizeForGuidance(original, leaf))
        }
    }
}
```

Run-1 still emits singleton contributing origins after a complete ND cube.
Do not split an unfulfilled cube or invent ZERO during collection.

All colored seeds are retained in this guidance inventory. Do not perform
another FLOW-replacement pass on its colored seed or closure rows. Existing
executable-fact protection remains unchanged. Once a full marked relation
is kept as a demand seed, the ordinary handoff does not need its protection
bit in the final DemandPattern.

### 6.1 Capture lost exit dependencies, including intermediate writes

A post-exit-only inventory is incomplete. For `C.f=p; return C.f`, an
exit cleaner can kill p-to-C.f while the returned dependency remains.
Keep the lost writer as guidance so p-to-C.f-to-ret can compose.

Use thin immutable original/output/mark keys and exact per-method ID sets.
The complete MethodKey, genuine ZERO original and colored mark mapping
are part of the key. No Facts, callback, statement, support tree or second
caller-input history is retained. The B-only interner must not pretend
that it can encode ZERO or nonstatic writer endpoints; use a compatible
separate thin-key interner or explicitly generalize it.

Observe these candidates:

1. Every reached STATIC input to the normal exit pipeline, before rules.
2. Every executed bounded static write in that pipeline, before its next
   rule/cleaner continuation. This includes a new value which another exit
   rule kills before the final drain callback.
3. Static final results before common global-drop/removal filtering.

Observe actual retained keys after common bounded summary handling,
including private B storage. At joined quiescence, remove exactly equal
surviving keys under the same complete original/owner/mark relation.
Until then keep a pending thin candidate if its survivor stability is not
proved. Raw writer packets are not stable: FLOW-backed storage can remove
a concrete DEMAND row when a corresponding FLOW relation arrives. Do not
permanently discard that candidate merely because the row once survived.
The default algorithm prunes against the final available inventory.
An earlier discard is permitted only under a proved stable-key or coverage
contract. Late resumes are included before final pruning.
An unmatched key is conservatively retained whole. Do not subtract by
another original, merge a colored key into FLOW, or require a semantic
set-difference operation on AP trees.

The store temporarily contains possible lost keys, including surviving
writer candidates until their final pruning. This is thin candidate
membership, not a killed-only memory bound. Pack and share mark/geometry
keys and measure peak candidate memberships. After pruning, the store
means “not retained as an equal exit key,” not “a definite cleaner kill.”
A partial, changed, demoted or unresolved exit result can leave extra
DEMAND guidance. No new executable summary or source is created.

```text
observe exit input / executed intermediate write / pre-filter result
    -> candidate key
observe common retained W or private B key
    -> survivor key
joined final prune
    -> keep candidates without an equal available survivor
```

This observes each existing transfer once. It does not rerun exit rules
or wait for a missing group. An exit-rule write continues the current
boundary pipeline and never schedules NormalExit again. An exceptional
boundary keeps summary=false and creates no normal-exit guide inventory.

### 6.2 Bind lost writers before releasing existing caller inputs

A lost p_get-to-C.f row cannot be copied to a wrapper as an unbound formal.
Use existing actual caller subscriptions, including their CallerRef,
stage, layer and genuine ZERO controls, to produce p_wrap-to-C.f.
A static/static row alone can use detached call-graph inheritance.

Current RunManager releases these subscriptions before driver HandOff.
Insert a joined read-only completion phase before actor freeze and runner
release. It may borrow existing N2 candidates; it may not send new events,
create SummaryStorage after completion, restart a method, or copy all
caller inputs into a second store. Emit only thin completed guidance keys.

Process primitive observed/post-exit W and recursively caller-bound W
against matching actual subscriptions. Do not feed static-composition-only
W rows back into this binding phase. Use the full
ordinary AP matcher and summary composition, preserving raw binding data
until that operation completes. Do not run call suffixes, exit rules,
source hits, pool supply, write registration or normal publication.
This adapter mirrors the existing run-1 static-summary result lane,
which routes STATIC output before the caller alias suffix. Do not add a
new alias expansion here. Static writes produced by ordinary nonstatic
call-result alias stages remain primitive run-1 write/candidate events.
Keep raw FLOW mark exclusions until AP application finishes. That
application can repeat a mark-request notification. The live exclusion
producer already owns this request. The joined adapter ignores the repeated
notification; it does not deliver a request or clear the exclusion before
matching. A concrete input excluded by that FLOW relation still fails.
ZERO W uses only a genuine reached ZERO call-control input. A resulting
static original creates B; a nonstatic/ZERO original remains local W.
Repeat fresh writer bindings and B inheritance to their finite fixed point.

This is a separate writer-seed phase, before static composition. Its
coverage argument factors a concrete required route at the static middle:
retain its actual input binding, primitive writer image and inherited
static suffix. This is witness coverage, not equality of AP tail keys for
arbitrary reassociation of bind(W;B) and bind(W);B. Bound output can be cut;
static guidance composition can retain a different conservative tail.
No call graph edge can replace the nonstatic input-binding witness.

Keep cancellation and the configured analysis resource limits active for
this phase. If completion fails or stops, do not export a partial closure
as an accepted complete handoff. Record its time separately from the run-1
engine and ordinary report barrier. Freeze only after successful completion;
release caller inputs and mutable collectors afterward on all exit paths.

## 7. Reference closure: the least fixed point

Let `parent -> child` be a prescan call edge. Start with the collected B and
the existing method-local boundary relations. Repeatedly apply:

```text
CALLER:
  child has C1 -> C2
  -----------------
  parent has C1 -> C2

STATIC-MIDDLE:
  M has A -> C   and   M has C -> B
  --------------------------------
  M has A -> B
```

Before this closure, saturate the primitive writer seed inventory using:

```text
BIND-W (writer-seed phase only):
  callee has primitive or caller-bound A -> C;
  an existing reached call input matches A
  ordinary AP application gives caller original X -> C'
  ------------------------------------------------------
  caller has X -> C' as guidance only
```

A is nonstatic or genuine ZERO. The actual binding retains its CallerRef,
marks, stage and layer. Static output keeps its coordinates. A static X
enters B. Freeze the bound seed inventory after this finite binding phase.
The subsequent eager closure has only SEED, CALLER and STATIC-MIDDLE.
It never applies AP caller binding to a composed guidance row. Only
static/static rows use CALLER; only a static middle uses composition.
Geometry and mark compatibility are part of the join. This produces all
the selected cases:

```text
C1 -> C2, C2 -> C3  => C1 -> C3
x  -> C,  C  -> y   => x  -> y
x  -> C1, C1 -> C2  => x  -> C2
C1 -> C2, C2 -> y   => C1 -> y
```

Use a fixed point, not a single caller-copy pass. A caller can combine
relations from two different callees and create a new static relation which
its own callers must also receive. Recursive call components need the same
monotone rule and exact duplicate admission.

```kotlin
// Phase A. Only primitive W and recursively caller-bound W enter this queue.
while (writerQueue.isNotEmpty()) {
    val (method, writer) = writerQueue.removeFirst()
    for (actual in joinedCallerInputs.matching(method, writer.from)) {
        bindOrdinaryAPForGuidance(writer, actual)?.let { bound ->
            if (bound.from.isStatic) offerStaticSeed(actual.ref.caller, bound)
            else offerFreshWriterSeed(actual.ref.caller, bound)
        }
    }
}
freezeBoundSeedInventory()

// Phase B. The exact eager reference for the factored static-path view.
fun offer(method: MethodKey, edge: GuidanceEdge) {
    if (!relations[method].add(edge)) return
    outgoing[method].indexBySource(edge)
    incoming[method].indexByTarget(edge)
    queue.add(method to edge)
}

while (queue.isNotEmpty()) {
    val (method, edge) = queue.removeFirst()
    if (edge.isStaticToStatic) {
        for (caller in callers[method]) offer(caller, edge)
    }
    if (edge.to.isStatic) {
        for (right in outgoing[method].overlappingStaticSource(edge.to)) {
            composeThroughStatic(edge, right)?.let { offer(method, it) }
        }
    }
    if (edge.from.isStatic) {
        for (left in incoming[method].overlappingStaticTarget(edge.from)) {
            composeThroughStatic(left, edge)?.let { offer(method, it) }
        }
    }
}
```

The method owner in this pseudocode is a complete MethodKey. Only B
visibility can use the coarser detached method graph. Never merge W/R
owners through CommonMethod alone.

This is the executable concept/oracle. Production need not materialize its
method-by-endpoint-pair matrix.

The overlap lookups are candidate indexes by static anchor and path. They
must include every compatible intermediate pattern. `composeThroughStatic`
runs the full region and mark join. Snapshot candidate iteration, or use
an insertion-safe index iterator, when `offer` can mutate the same index.

All ordinary selected pairs remain in the final demand. In particular,
the completion cannot replace a pre-existing colored or full sink guide
with a less specific FLOW guide. Newly composed nonstatic-to-nonstatic
guidance stays at its exact method owner; it is not copied to callers as
an unbound callee argument/return pair. Ordinary run-1 R propagation exposes reader segments. Ordinary W and
joined BIND-W completion expose the needed writer segments. In particular,
a killed callee W must not be assumed already present in its callers.

## 8. Mark and geometry composition

### 8.1 FLOW is diagonal

```kotlin
sealed interface MarkRelation {
    data object Flow : MarkRelation
    data class Mapped(val input: AtomId, val output: AtomId) : MarkRelation
}

fun compose(a: MarkRelation, b: MarkRelation): MarkRelation? = when (a) {
    Flow -> b
    is Mapped -> when (b) {
        Flow -> a
        is Mapped -> if (a.output == b.input) Mapped(a.input, b.output) else null
    }
}
```

FLOW preserves the actual mark. It is not a Cartesian wildcard:

```text
FLOW ; (T -> U)       = T -> U
(T -> U) ; FLOW       = T -> U
(T -> U) ; (U -> V)  = T -> V
(T -> U) ; (V -> W)  = none, when U != V
```

ZERO is a separate endpoint. A genuine source seed can have ZERO as its
input and a fixed output mark. In the symbolic label, use a reserved
`NoInput` atom only for this source endpoint; it is not a taint mark or a
wildcard. Thus `ZERO -> C/T` has `Mapped(NoInput,T)`. Composition preserves
that original ZERO and `NoInput` selector.
`NoInput` is private guidance encoding; it does not enter the runtime
MarkTable or change a ZERO fact.
It cannot create a ZERO premise from nonzero inputs. ZERO is never an
internal vertex of STATIC-MIDDLE.

In FULL mode, atoms are full mark identities. In GROUP mode, keep the
existing group-selector semantics when projecting the completed demand to
FULL run-2. `Mapped(G,G)` remains colored group guidance. Do not turn it
into FLOW or enumerate group members. Runtime mark interning and primitive
tracking remain unchanged.

### 8.2 Retain colored round trips

```text
C1/T -> C2/U -> C3/T
  produces a colored T -> T demand relation.
```

It remains present even if a parallel FLOW path has the same outer geometry.
The completion graph does not repeat semantic FLOW subsumption. This keeps
marked cleanup and mark-change dependencies. The normal AP operations in
run-2 set and transport their existing non-subsumable annotations.

### 8.3 Intermediate static positions

Both relation owners must be the same method view at the join. Match complete
static slot geometry, including the selected class/field anchor and legal
tail-region overlap. Distinct fields do not join just because they share S
or the same class. Exact class markers do not match their fields.

Composition keeps the outer endpoint patterns. It does not concatenate
new arbitrary field paths or synthesize a new executable summary. This is
a conservative permission relation; it can admit more candidates when
bounded intermediate regions overlap. Run-2 still performs real transfer.

Normalize MUST/location and mark-exclusion information only through the
existing handoff normalization. In particular, cleared demand mark exclusions
do not clear exclusions on executable facts or permit T from a FLOW input.
Do not claim the completed relation is an exact program-flow relation.

### 8.4 The shared static carry stays separate

Keep the already selected shared static carry demand for transparent methods.
The closure of known nonidentity relations alone would leave a method with
no static seeds unable to accept a real static requirement.

Treat carry as zero-length at the **same actual static position and mark**.
Do not add a broad S-root graph vertex which could connect C.f to unrelated
C.g through overlap. It is a demand permission, not a computed identity
summary or a normal record. The real body can still kill its input.

The carry adapter must cover the abstract/static inputs used by shared FLOW
analysis and preserve actual FULL identity on its marked branch. This is the
existing static completion scope expressed as demand; it grants no general
nonstatic query permission or automatic same-field EXACT start.

## 9. Factored representation of the same closure

For method M, define:

```text
VisibleB[M] = B seeds owned by M or any transitively reachable callee
T[M]        = nonempty static paths in VisibleB[M]
```

The completed method relation consists of the existing ordinary rows and:

```text
T[M]
W[M] ; T[M]*
T[M]* ; R[M]
W[M] ; T[M]* ; R[M]
```

`T*` includes zero static hops. It gives the direct x-to-C-to-y case. It does
not import nonstatic names from a callee. Ordinary reader propagation and
the joined writer-binding phase supply the method's W/R rows first. W
includes lost exit rows, bound with actual callers. VisibleB includes
post-exit and lost B, including B created by writer binding.

Store static seeds once with owner memberships. Collapse call-graph SCCs or
use equivalent frozen reachability. Equal seed/adjacency values can be
shared. Keep local W/R attachments at their existing MethodKey owner.

Demand lookup follows static paths and composes mark labels with a visited
set. It returns exactly the same permission pairs as the reference closure.
It need not store each caller's complete C1-by-C2 or x-by-y matrix.

```kotlin
interface FrozenCompletion {
    // Both methods enumerate virtual DemandPatterns, not executable facts.
    fun near(method: MethodKey, actual: Pattern): Sequence<DemandPattern>
    fun covering(method: MethodKey, initial: InitialAp): Sequence<DemandPattern>
}
```

`near` has the ordinary prefix/extension candidate semantics. `covering`
finds whole-premise candidates. Both still run the complete AP emitter or
restriction afterward. Lookup is a pure read of the frozen closure. It
does not grant permission by registering an actual query.

For backward lookup, an ending forward endpoint selects the search roots.
Walk the relation in reverse and emit the matching outer source endpoints.
Keep explicit mapped labels on any path which contains them. A path made
only of FLOW remains FLOW and is shared across caller marks.

The finite state includes endpoint and mark-relation label. No path history
or unbounded provenance tree is retained. A T-to-U-to-T cycle yields the
same finite Mapped(T,T) state, which remains distinct from FLOW.

## 10. Handoff and strict run-2 execution

```kotlin
fun finishCompleteRun1() {
    joinAllWorkersAndCountedEffects()
    val completed = completeJoinedWriterBindingsAndStaticGuidance(
        existingSelectedWandR(), privateB(), killedStaticWrites(),
        borrowExistingActualCallerInputs(), detachedPrescanGraph,
    )
    // No caller-input borrow is allowed after this release.
    freezeActorsAndReleaseRunners()
    persistExistingEligibleRawNormalRecords()
    val demand = projectExistingSelectedPairs()
        .withCompletion(completed).withSharedStaticCarry()
    startBackwardRun2(demand, existingFullSinkSeedProjection(), records.readOnlyView())
}
```

Project a completed forward relation with the ordinary rule:

```text
forward:        A -> B
backward guide: entry = normalize(B), exit = normalize(A)
```

Do not persist a completed row as a NORMAL record. Do not insert it into the
run-1 live SummaryStorage or re-run its method statements.

Run-2 uses the original AP demand emitter and paired C5 publication. There
is no general StrongQueries set or raw-answer permission branch. Caller
subscriptions instantiate FLOW answers against actual marks. Concrete
barriers receive the completed colored demand where required.

The new completion view belongs only to the run-1-to-run-2 boundary. The
next handoff uses actual run-2 publications and records under the original
rules. Do not copy this permission closure automatically into later runs.

## 11. Worked cases

### 11.1 Static copy below a getter

```java
void copy() { C.out = C.in; }
Object get() { copy(); return C.out; }
```

```text
copy seed:           C.in -> C.out
get retained read:   C.out -> ret
caller visibility:   get knows C.in -> C.out
composition:         get gains C.in -> ret
run-2 guide:         ret -> C.in
```

Original ordinary AP propagation could retain the relay and its productive
caller composition. Current run-1 keeps the reader but erases the relay;
SQ permits the later caller-specific answer without that paired guide.
The proposal supplies the missing pair explicitly and then uses ordinary
C5. It does not authorize any other raw answer of `get`.

The existing wrapper-exit restriction now permits the real backward answer.

### 11.2 Setter and getter in one wrapper

```java
void set(Object p) { C.out = p; }
Object get(Object p) { set(p); return C.out; }
```

```text
get retained rows:   arg(0) -> C.out, C.out -> ret
composition:         arg(0) -> ret
run-2 guide:         ret -> arg(0)
```

Current stored pairs alone reject `ret -> arg(0)`: the getter pair permits
only C.out at exit, while the writer pair has a different entry. SQ bypasses
that rejection. The proposed static-middle composition supplies exactly
the missing productive wrapper guide. The original AP rules can then
admit the actual body-derived answer without a nonstatic query exception.

There is no new unrestricted nonstatic query rule.

### 11.3 A required colored static bridge

```text
bridge retained seed: C.in/T -> C.out/T  // selected cleaner survivor
get reader:           C.out/FLOW -> ret/FLOW
composition:          C.in/T -> ret/T
run-2 guide:          ret/T -> C.in/T
```

The completed T guide starts the marked route. The parallel FLOW route
does not replace it. The ordinary selected cleaner and its actual T result
decide the backward answer.

### 11.4 Exit processing

```java
C.f = sourceT();
work();
return value;
// NormalExit: configured exit rules
```

```text
write effect:          supply the actual write to the static service
summary candidate:     original -> C.f/T
shortcut:              NormalExit input, skipping work() and return transfer
exit handler:          evaluate normal exit rules and sink occurrences
post-rule relation:    common summary store or private B seed
```

If an exit cleaner kills T, no outgoing T relation is archived or published.
Its earlier write remains available to pre-exit consumers. If the exit rule
adds U, the post-rule U relation follows the same common emission path.

Original ordinary summary construction observes normal exit rules. Current
early static insertion bypasses them. The proposal restores that exit
stage for static candidates while retaining the selected body shortcut.

### 11.5 No demand and shared FLOW

```java
Object identity(Object p) { return p; }
```

```text
Receiving a nonzero input with no matching demand:
  original: no body initial (applicable records can still answer)
  current:  StrongQueries admits a canonical actual-input initial
  proposed: no body initial (same record route as original)

Receiving ret/ANY/T1 and ret/ANY/T2 in a backward method with
guide (ret/ANY/FLOW, arg(0)/STAR/FLOW):
  original: one ret/STAR/FLOW initial; apply its answer to each actual Ti
  current:  separate canonical concrete query initials, plus concrete guides
  proposed: one ret/STAR/FLOW initial; apply its answer to each actual Ti
```

These are operation-count examples, not new project measurements. A real
concrete rule gate still needs its marked guide; shared FLOW cannot satisfy
it merely because one caller carries T.

### 11.6 A normal singleton supplies its record

For the same nonstatic identity body, a run-1 FLOW relation
`arg(0)/*/FLOW -> ret/*/FLOW` can be NORMAL under the unchanged layer policy.

```text
original handoff: record only
current handoff:  record plus selected run-1 demand
proposed handoff: record only
```

The caller applies the valid native/opposite-direction record through its
ordinary record route. Omission from selected demand does not erase the
record or require SQ to execute this identity body again. A concrete run-1
relation already forced to DEMAND is still demand; this example does not
change that policy.

### 11.7 Sibling callees, transitive callers and mark changes

```text
main calls left and right; outer calls main
left B seed:  C.a/T -> C.b/U
right B seed: C.b/U -> C.c/T

main completion:  C.a/T -> C.c/T
outer completion: C.a/T -> C.c/T
label:            Mapped(T,T), still colored
```

Current run-1 erases those B seeds and provides no such stored caller
closure. The proposal retains them privately and imports/composes their
guidance at handoff. Even a parallel `C.a/FLOW -> C.c/FLOW` does not remove
the colored completed row. If the second input is V instead of U in FULL
mode, that marked composition does not exist. The accepted run-1 call-order
approximation can add a guide even when the two calls execute in the wrong
order; real run-2 execution must reject the impossible flow.

### 11.8 ZERO and transparent wrappers

```java
void set() { C.f = sourceT(); }
void wrap() { deep(); }
void deep() { sinkT(C.f); }
void main() { set(); wrap(); }
```

`set` and its ordinary caller path keep the genuine ZERO-to-C.f write.
The sink occurrence supplies its full marked backward seed. A wrapper
which has no productive boundary relation still has the selected static
carry demand. When the real backward requirement crosses `wrap`, its
static premise can start by that fixed demand family; it is not an
actual-query exception. Backward ZERO also enters reached callees by the
existing direct-entry rule, so seed discovery does not require a new
static/static executable summary.

If there is an additional static bridge C.f → C.g, closure composes it with
the existing ZERO write and reader boundaries where present. It keeps the
actual ZERO origin. A nonzero writer `arg(0) -> C.f` cannot become a
ZERO-origin writer merely because the static service has an actual group.
There is no composition through ZERO as an internal vertex.

## 12. Termination, cost and safety properties

The endpoint universe is finite for a completed bounded run-1. It includes
primitive endpoints, existing joined CallerRef originals and bounded AP
images produced by the writer-seed binding phase. A bound source need not
occur in the original callee seed list. After that phase, static closure
does not invent endpoint paths, marks, methods or bases. A relation key has
an owner, two endpoint classes and either FLOW or a finite mark pair. Set
admission therefore reaches a fixed point. Graph cycles do not require an
arbitrary iteration cap or a new pending-memory quota.

An explicit closure can be quadratic in endpoints and marks per method.
It could recreate the memory problem. The factored representation stores
seeds, owner memberships, the call graph and W/R attachments. Query scratch
is finite and discarded. Do not enumerate every virtual pair merely to
print a demand count.

For example, let one callee own a chain of n distinct static positions and
let m callers reach it. The chain uses n-1 seed rows. Explicit nonempty
closure stores n(n-1)/2 static pairs in each caller, or
`m * n(n-1)/2` rows. The factored view stores the n-1 seeds once plus their
owner membership and the caller graph. A demand lookup still visits the
relevant chain. This is a retained-storage saving for this workload, not
a bound on total lookup time for arbitrary queries. Dense marked seeds or
repeated broad lookups can still be expensive.

This changes the location of work: no static CFG/call relay during run-1;
relation matching at handoff or frozen-demand lookup; real flow processing
only in the restricted run. No numerical speedup or memory saving is claimed
without the configured project experiment.

Report ordinary explicit patterns, static seed schemas, owner memberships,
visited closure states, returned virtual pairs, graph/SCC size, closure
time, and retained bytes separately. Mark virtual counts as not expanded
when unavailable. Always include the latest reached/completed/accepted run.

## 13. Correctness proofs and checked scope

### 13.1 Proof scope and interface invariants

The completeness target is the demand omitted by the selected run-1
static shortcut, relative to the original AP operations and the following
interfaces. It is not equivalence to the current broad SQ permission set.

1. The completed, non-diagnostic run-1 retains every required primitive
   static dependency as a post-exit W/R/B key or an observed lost exit key.
   Joined BIND-W uses existing actual caller inputs before their release;
   it supplies the needed nonstatic/ZERO caller writer bindings. Ordinary
   R propagation, normal records and sink/source seed routes remain valid.
2. The detached prescan graph contains every resolved call target. Its
   conservative method/context visibility is the selected run-1 contract.
3. Endpoint compilation preserves every compatible concrete static location
   and mark instance. FULL identities and GROUP selectors retain their
   stated meaning. It does not identify distinct static field anchors.
4. The ordinary interpreter, summary application, emission and restriction
   satisfy their existing AP contracts within the supported bounded grammar.
   Fair counted processing reaches every admitted required transfer.
5. NORMAL records and real runtime facts retain their exclusions, layers,
   complete premise sets and protection. Only guidance uses the stated
   normalization. All required seed paths retain the existing ZERO rules.

These are implementation obligations, not permission to assume a missing
completed demand already exists. The construction below takes **primitive
dependencies**, builds the composed pair and then projects its demand.
The diagnostic statics-off mode is excluded from this coverage claim.

### 13.2 Restored demand authority

For one actual input a, define the emitted set as
`union { AP.emit(Dc,a) | (Dc,Dp?) is in frozen demand }`.
Every member has an explicit demand witness by construction. With an empty
matching set, no nonzero initial is emitted. The entry tables and the
original C2/C3 contracts supply the reverse coverage statement within their
guard: every admitted common location/mark is covered by a satisfiable
initial inside Dc. Abstract demand creates its shared FLOW form regardless
of the number of matching concrete callers.

For an ordinary raw summary, define publications as the union of the
member/pattern C5 restrictions. Every published piece therefore has a
complete permitted pair witness, retains J and has no pair absent from the
raw relation. C5 preserves every required pair under its whole-member
containment condition. Keeping the original backward-ZERO route does not
extend this exception to a nonzero original.

Because the demand set is fixed, its entry and exit tests cannot change
when another caller arrives. A later caller can change which existing
answer it can apply; it cannot change whether the callee may publish a raw
answer. Subscription replay supplies old publications; notifications supply
new publications. Thus a raw-summary authorization scan has no semantic
role after SQ removal. This argument does not remove ordinary replay.

The original-operation local model is
[RestrictedDemand.lean](lean/proposals/restricted-demand/RestrictedDemand.lean).
Its ten audits include demand witnesses for starts/publications, empty
demand, shared FLOW emission and the wrapper gaps shown in section 11.
The original AP C2/C5 certificates cover the guarded scalar operations;
this local model does not independently prove a whole method actor.

### 13.3 No missing finite static composition

Fix a method M. Describe a required finite route by primitive dependencies,
with only static positions as internal joins. Its first/last relation can
be a local W/R relation. Its static/static atoms can belong to M or to
resolved transitive callees. Nonstatic endpoints already belong to M.

Construct its eager completion witness:

1. A local atom uses SEED.
2. A callee static atom follows the finite resolved call path toward M,
   applying CALLER once per call. This gives a witness in M.
3. A lost writer uses its observed exit key. Candidate-minus-survivor
   coverage preserves that key in either the survivor inventory or the
   killed store, including an intermediate executed exit-rule write.
4. A nonstatic/ZERO callee writer follows actual caller bindings via
   BIND-W. At each call retain the actual caller original and static image.
   Factor a composed writer at its static middle; bind its writer prefix
   and inherit its static suffix. This covers the required concrete
   location/mark witness; AP cut tails need not be equal under arbitrary
   binding/composition reassociation.
5. A one-atom route is complete. For a longer route, complete its suffix
   recursively and apply STATIC-MIDDLE to the first atom and that suffix.

This is a structural induction on the route. It covers all four requested
compositions and arbitrary repetitions of them. It does not require
enumerating call paths or all complete pair products in production.
Recursion in the call graph does not invalidate a finite witness.

For forward endpoints A and B, project the completed witness to backward
`(entry=normalize(B), exit=normalize(A))`. Endpoint normalization is a
location/mark cover of the retained run-1 dependency. C2 can start the
required backward assumption when its actual input arrives. C5 permits its
required computed exit. Apply this argument in each method of the ordinary
call derivation. Transparent static passages use the separate static carry.
Concrete rule/cleaner barriers use the colored completed pair, not an
invented concrete mark from FLOW. Under the interfaces in section 13.1,
the static omission alone cannot remove a required guide.

This is **relative completeness of static demand completion**. Extra
method/context/order combinations can be admitted as guidance. They are
not computed answers: actual run-2 transfers, call order and strong writes
still decide which conclusions exist. The full original multi-run/JVM
soundness theorem retains its existing assumptions and integration limits.

### 13.4 Eager closure equals the factored representation

Fix the completed bound seed inventory from phase A. This theorem is for
phase B's SEED/CALLER/STATIC-MIDDLE closure only. It is not an exact-key
associativity theorem for AP binding and guidance composition.

An eager SEED is one local factored atom. An eager CALLER step lifts each
static atom of its child's path through that call. An eager composition
concatenates its two factored paths at the static middle. These three cases
construct a factored witness for every eager relation.

Conversely, expand a local factored atom with SEED. Expand an inherited
atom by its explicit call path and CALLER steps. Fold a multi-atom path
with STATIC-MIDDLE. This constructs an eager witness for every factored
relation. Both conversions are executable. They prove equality of the
guidance sets, not only one inclusion. The `least` induction proves that
any relation closed under the selected rules contains this closure.

The endpoint-witness functions also return an actual seed which supplies
each outer endpoint. In particular, completion cannot invent ZERO as a
new origin. No ordinary or ZERO middle is admitted by the path constructor.
Carry is outside that graph, so it cannot connect unrelated field vertices.

### 13.5 Mark preservation and finite termination

FLOW denotes equal input/output marks. A mapped row denotes the stated
input/output selectors. `joinMark_sound` supplies a compatible intermediate
mark for every instance of a composed symbolic label. `joinMarkWitness`
constructs a result label from two compatible instances. Incompatible
mapped middle marks reject. A round trip T → U → T remains Mapped(T,T),
which is distinct from FLOW, so marked demand is retained beside a FLOW
path. GROUP-mode compilation must satisfy the same coverage statement
through its existing full-mark selector adapter.

Closure keeps the finite run-1 endpoint universe and finite mark labels.
For each owner there are at most `endpointCount^2 * labelCount` possible
keys. Exact admission accepts each key once. Eager work therefore terminates;
factored lookup terminates with its finite `(endpoint,label)` visited set.
No arbitrary replay generation or query authorization can expand that set.

### 13.6 Exit route correctness

For the unique declared normal exit e and bounded input f,
`exitQueue([e],f) = [(e,f)]`. The fact arrives unchanged. If h is the common
exit-rule/summary handler, the shortcut's results are exactly `h(e,f)`.
There is no return-transfer or intervening-statement function in this
composition. Every archived/published output comes from h; a kill by h
produces no output. Its result is not sent back through the ingress route.

Immediate producer effects are a separate output of the write operation.
They occur before the exit queue and do not depend on h returning a value.
This preserves earlier consumers when an exit cleaner removes the outgoing
summary. Fresh exit deltas, late rule resumes and effect delivery stay in
the existing complete-run barrier. Missing boundary metadata is an error,
not a silent empty summary path.

### 13.7 Machine-checked evidence and implementation gates

The [constructive model](lean/proposals/restricted-demand/StaticClosure.lean)
provides:

- A least inference closure with seed, direct-caller import and static-middle
  composition constructors.
- Executable conversions in both directions between that eager closure and
  factored seed paths. The core equivalence requires no classical axioms.
- Executable seed witnesses for outer endpoints and a backward guide witness
  for every finite required path.
- Actual transitive-caller, sibling-composition and W-to-static-to-R witnesses.
- A sound symbolic mark join, an executable compatible-join witness,
  rejection of incompatible mark pairs and retention of a mapped round trip.
- Exit-routing laws: queue only the declared normal target; every summary
  result comes through the supplied exit handler; a kill remains a kill.

The graph model uses compatible endpoint/mark instances. It proves equality
of the two **guidance** representations, not equality with concrete program
flows. The Kotlin adapter must preserve its AP geometry and group matching.
The generic exit-handler model now binds to the user-selected NormalExit
handler after return transfer; it does not model a new return instruction.

All 23 closure-model audited declarations pass with only `propext` and
`Quot.sound`; the core factor/expand equivalence and least-closure theorem
need neither.
There is no new axiom, classical choice or unproved placeholder. The ten
separate original-demand audits also pass. These are 33 audited declarations
across the two local models, not 33 whole-analyzer theorems.

The second-review model
[MarkBoundaryReview.lean](lean/proposals/restricted-demand/MarkBoundaryReview.lean)
adds 18 audits of the original asymmetric mark gates, unchanged correlated
STAR restriction, original STAR/E normalization, generic strict-descent
exclusion rebasing and the E-union intersection law. There are 51 audits
across the three local models. The current scalar Kotlin probe passes 14
expected behavior checks and confirms the inherited-E defect and the
MUST/STAR adapter gap. The new proposal does not describe those two current
results as successful fixes.

The [second-review receipt](lean/proposals/restricted-demand/boundary-review-checks.json)
contains all outputs and source hashes. The
[review report](../docs/reports/bidirectional-restricted-demand-scope-review-20261027.md)
records the history and the corrected scope. Neither the old non-STAR
canonical-shape proof nor these scalar controls prove the full extended
typed emitter. Acceptance must check the supported STAR-entry builder,
MUST cell and packed/scalar correspondence against normalized demand.

The 28 October model
[AbstractDemandEmptyExclusion.lean](lean/proposals/restricted-demand/AbstractDemandEmptyExclusion.lean)
checks 19 local constructive results. They include demand widening and
idempotence, concrete preservation, shared initial C2, whole-entry guard
preservation, retained raw C5 pairs and layer, and actual-E-sensitive
matching. The abstract exit-permission widening has an explicit witness.
These local results replace reliance on a producer invariant. They do not
prove the complete typed adapter, JVM, scheduler or iteration pipeline.

The local scope witness
[WriterBindingScope.lean](lean/proposals/restricted-demand/WriterBindingScope.lean)
has six constructive audits. It checks an explicit counterexample to
exact AP tail-key commutation and the distinction between seed binding
and static closure. It supports the theorem scope above; it does not add
an executable transfer rule.

[KilledStaticWrites.lean](lean/proposals/restricted-demand/KilledStaticWrites.lean)
has 25 constructive audits. Its executed trace observes exit input,
intermediate produced static values and pre-filter output. Final partition
returns the identical original/owner/color key in either available
survivors or killed storage, even when survivor membership decreases.
It constructs seed-only caller-binding witnesses from explicit actual
binding steps, checks finite bound endpoint provenance, and transports
static closure after the bound inventory freezes. Relational read/write
and call-split witnesses preserve their concrete inputs and static middle.
The [audit receipt](lean/proposals/restricted-demand/killed-static-writes-checks.json)
records all commands, dependency hashes and limits. JVM observation,
actual-binding export and bounded AP witness coverage remain production
adapter acceptance gates; the model does not assume them proved by a
method-level call graph.

The selected local supply model
[LocalStaticWriteSupply.lean](lean/proposals/restricted-demand/LocalStaticWriteSupply.lean)
has 14 constructive audits. The selected static-domain repair model
[StaticInputGrammar.lean](lean/proposals/restricted-demand/StaticInputGrammar.lean)
has 15. Their receipts record commands, hashes and proof scope. Neither
claims whole-JVM admission or compiler correctness. StaticProducer.lean
and the exclusion-union candidate are historical superseded mechanisms,
not selected runtime requirements.

The finite oracle compares eager and factored results in 91 cases, including
80 deterministic random graphs. Three generic exit-pipeline controls also
pass. These are design controls, not a production implementation or a new
project result.

The [oracle source](lean/proposals/restricted-demand/closure_oracle.py) and
[complete receipt](lean/proposals/restricted-demand/static-closure-checks.json)
are kept in this repository. The receipt includes every graph case, the
Lean audit output, source hashes and the exact validation scope.

Before implementation acceptance, prove or test the following adapters:

1. Every post-exit B row reaches the private seed store; none reaches live
   publication or executable NORMAL persistence.
2. W/R and lost-key collection preserves complete MethodKey endpoints.
   Joined BIND-W supplies real caller bindings before release. Include ZERO
   returning wrappers and static originals created by binding. Only B uses
   method-level inheritance; every resolved target is visible there.
3. Complete AP slot/tail matching and FULL/GROUP mark projection refine the
   compatibility abstraction without dropping a required witness.
4. Colored closure rows are never lost under FLOW normalization. Actual
   facts retain the existing protection and equality rules.
5. New exit arrivals and late boundary mark answers stay counted until their
   exit rules, summaries, writer effects and notifications complete. Observe
   intermediate executed static writes before another exit rule kills them.
   Every required normalized key survives in final W/B or the killed store.
   Prove early-discard survivor stability, or retain its pending candidate
   until final pruning; do not assume mutable raw packet headers are stable.
6. Ordinary C2 emission and C5 publication accept the newly completed pairs.
   Keep the baseline ZERO, ND, seeds, exclusions and native-record tests.
7. A finite required static dependency can be decomposed into the retained
   W/B/R path. Construct its completion witness, then replay its ordinary
   run-2 steps. Do not assume the missing pair was present initially.

This is not a whole-JVM soundness or termination theorem. Unsupported
frontend geometry or a missing producer must be resolved explicitly,
rather than adding a new general permission fallback.

## 14. Entities to remove, replace or retain

All paths below are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`,
unless marked as tests. This is the required cleanup after implementation,
not an instruction to delete these entities before their replacement is
tested. No runtime code is changed by this document.

### 14.1 Remove obsolete permission state and work

| Entity | Required action | Why it has no role after this change |
|---|---|---|
| `engine/StrongQueries.kt`: `StrongQueries` | Remove the class and its constructor policy checks | Fixed demand is the only nonzero body/publication authority |
| `StrongQueries.admitted`, `admit`, `permits`, `clear` | Remove | Initial dedup already belongs to InitialFactStore; a second set must not authorize raw answers |
| `StrongQueries.completeStaticFull` | Remove | ANY input does not authorize a second EXACT initial |
| `RunMethodAnalyzer.currentQueries` allocation and disposal | Remove | No per-method query-permission owner remains |
| The new-start branch in `RunMethodAnalyzer.addLink` which iterates `summaries.all()` and calls `queuePublications` | Remove the scan | Frozen demand cannot gain a new allowed exit from an input arrival |
| `published` branch `currentQueries?.permits(premise) == true` | Remove | All ordinary restricted publications use complete entry/exit restriction |
| `config.run1 ||` in the outgoing `selected` predicate | Remove this override; retain the ordinary selection predicate | NORMAL singleton run-1 summaries are records, not ordinary guidance |
| `store/DemandStore.kt`: `StaticQueryPolicy` enum, stored property and builder state | Remove | Query-admission policy no longer exists; completion is an immutable demand view |
| `DemandStore.Builder.completeRun1StaticFields()` and its handoff call | Remove | No flag can enable the removed query/EXACT mechanism |
| Current `implicitStaticPair`, `staticGroupsEnabled`, `includeStaticGroups()` and its handoff call | Replace with the frozen same-position carry family and static completion view | The old root-wide, group-only helper does not define the required FLOW carry and completed productive pairs |
| Query-policy constructor plumbing and checks in the above owners | Remove | The receiving run already has its index, direction and limit |
| `HandOff.toBackward` STAR-to-ANY entry rewrite | Remove | Keep STAR. Normalize abstract STAR demand E to Empty; retain concrete E. Native records are unchanged. |
| `DemandStore.Builder` blanket non-STAR-entry and abstract-ANY-only checks | Normalize abstract STAR demand E before validation | Accept offered abstract STAR/E, store Empty E, and keep concrete STAR/E and typed abstract-EXACT prohibition |
| `validFieldExclusion` restricted to a STAR exit | Extend to legal STAR entries as well | E is legal on a preserved STAR endpoint on either side |

Removing `StrongQueries` does not remove `ops.emit`, `ops.restrict`,
`restrictBy`, `InitialFactStore`, raw summary storage, publication storage,
subscription replay or record application. These are required by the
restored protocol.
Preserve the ordinary binding/field-limit cuts and cancellation checks
when deleting the class. Valid transport inputs are bounded before entry
emission. Move a cut used only by a query-specific helper to that ordinary
ingress path if needed; removing authorization must not remove the bound
or turn field limiting into an extra actual-input initial.

### 14.2 Replace the early static-summary path

| Entity | Required action | Replacement |
|---|---|---|
| Direct `retainSummary` from the run-1 local static branch of `emitOperationResult` | Remove that direct insertion | Immediate local write effects, then admitted NormalExit work |
| `promoteStaticSummary` as an early-insertion helper, and all its call sites in `RunMethodCallServices` | Replace the helper and update all call sites | Route the already computed static result to NormalExit; keep computed supplies, never register a call as a local writer |
| `erasesRun1StaticSummary` as a drop-only predicate | Replace its behavior/name | Classify post-exit static/static results for the private seed archive |
| Blanket run-1 STATIC returns in `emitAfter`, `emitUnchanged` and `endAt` | Replace only at NormalExit | The normal boundary runs exit rules and common emission; passive static propagation elsewhere stays suppressed |
| Any exit-rule callback which re-enters the old early-promotion helper | Route its result to common post-exit emission instead | No exit-rule-to-exit-rule loop |
| Newly added SummaryStorage producer PublicationIndex and producerCandidates/publishProducers | Remove | Concrete executed writes supply at their write point |
| Producer delivery kind, notify/replay/applyStaticProducer callbacks and interface plumbing | Remove | No live pre-exit writer summary channel remains |
| Dedicated producer packet/application counters | Remove | Measure local write supply and killed-key/binding/closure work instead |
| StaticProducer.lean claims for outward producer replay | Retain only as historical evidence | Selected local write supply uses LocalStaticWriteSupply.lean |
| False abstract STAR/Empty-E admission assertion and exclusion-union fallback candidate | Remove/reject | Offered E is ignored on abstract STAR demand copies |


Keep `summaryDelta`, `boundedSummaryResult` and common `retainSummary`
responsibilities for other summaries. Split or rename functions as needed;
do not delete the common bounds, kind checks, layer policy, publication
deduplication or persistence path merely because the early caller is gone.

### 14.3 Move validation; remove its query-policy dependency

Update the concrete intersection adapter separately from ordinary field
transfer. `Reference.commonPart` must rebase ancestor E on a strict
descent before meeting tails; apply the same law to packed emission.
`Reference.meet` must replace its MUST-input/STAR-demand assertion with
the MUST/(E1 union E2) cell. Keep MUST demand entries forbidden. These
corrections are required by the retained correlated-STAR extension and
preserved STAR demand; deleting SQ alone would not implement them.

`validateRun2StaticFullInput` and `validateRun2StaticFullAnchor` currently
share `StrongQueries.kt`. They enforce the selected grammar and are still
needed. Move them to an AP/static-boundary validation file, for example
`engine/StaticInputGrammar.kt`. Preserve static anchor checks and correct
only the stale named-field tail domain: EXACT/ANY/STAR with legal STAR E.
Do not add STAR rule literals, actual queries, new starts or broad FULL
root/class inputs.

Replace the obsolete policy test in `RunMethodAnalyzer.checkRun2StaticAnchors`
and `RunMethodLocalServices.seedFact` with the actual boundary condition
`config.index == 2`. Keep checks on seeds, bounded input and actual output.
Do not turn validation into permission or introduce broad concrete S/class
facts. Remove the old policy import/property dependency, not the checks.

### 14.4 Replace obsolete tests and assertions

Test paths below are under `src/test/kotlin/org/opentaint/dataflow/bidi/`:

| Existing test or assertion | Required replacement |
|---|---|
| `StrongQueriesTest` assertions for unconditional actual queries, raw-answer permission and extra exact starts | Demand-only entry/publication tests, FLOW sharing, no-demand/no-start, no ANY-to-EXACT and immutable late-arrival behavior |
| `DemandStoreTest` rejection of all STAR entries; handoff expectations which widen STAR to ANY | Preserve legal STAR/E; accept the supported abstract STAR/empty form; reject only the stated unsupported forms |
| `ImplicitStaticGroupDemandTest` reference inventory of root-wide group pairs | Same-position carry and full static closure tests, including FLOW, colored paths, markers and no cross-field carry |
| `HandOffTest` and `StaticConditionalRequestJoinTest` policy-enum assertions | Assert incoming run-2 completion/carry behavior and its absence at later handoffs |
| `StaticSeedGrammarTest` and `StaticProducerGrammarTest` policy setup | Use run-2 configuration and the retained grammar validators |
| `GroupedRunScheduleTest` old group-family setup | Use the new frozen-demand factory; keep GROUP/FULL schedule/mark assertions |
| Static writer tests which require immediate summary insertion or complete loss of static/static rows | Assert immediate producer effects, deferred exit processing and private seed capture |

Preserve useful mark, exclusion, grammar, layer, record, ND and cancellation
controls from these files. Deleting the old query owner must not delete
those semantic regression tests.

### 14.5 Explicitly retained entities

Keep `Run1StaticService`, `Run1PointResume`, their real local FLOW writer
directory, computed supply joins, read registrations, waiting point
resumes and req/reach/processed sets. They still make writes available
to reads and answer run-1 mark interests. Static handoff composition does
not replace the live service.

Keep `RequestStorage` and the existing run-1 nonstatic request barrier;
they do not become later-run requests. Keep full later-forward conjunction
stores, protected-edge handling, FLOW-backed storage, ordinary caller
subscriptions, native records, sink seeds and source-hit stores. Keep
the enum alias hack, diagnostic flags, method-form caches, references and
IR storage. No new cache manager or grounding-support type is added.

Keep `HandOff.forEachDemandPiece` for ordinary selected publications. Add
the frozen static completion source to that boundary; do not replace
ordinary handoff with a scan of all raw summaries. Keep old investigation
and proof receipts as historical evidence, with their original scope.

## 15. Implementation sequence and acceptance

1. Add the NormalExit routing regression controls. Reuse the existing
   boundary, point admission, exit-rule handler and common summary emission.
2. Extract producer effects from early summary insertion. Preserve immediate
   static supplies and write registrations; add the post-exit B seed store.
3. Add thin killed-key observation at exit input, actual intermediate writes
   and final pre-filter output. Preserve candidate-or-survivor coverage.
   Complete lost writer bindings through existing N2 after join and before
   release. Include cancellation/resource failure and exact duplicate keys.
4. Freeze the detached call graph and W/R/B/lost-key inventory. Compare the
   eager reference including BIND-W with the factored representation.
5. Implement the equivalent frozen graph demand view. Match `near` and
   `covering` against the oracle, including marks, class markers and cycles.
6. Restore original restricted-run emission and C5 publication. Remove the
   broad query permission set/backfill and ANY-to-EXACT completion. Preserve
   STAR at handoff; update the typed demand guard and the concrete descent
   and MUST/STAR cells before switching off the old query path.
7. Keep the shared static carry as a demand family. Exercise the getter,
   setter, colored bridge, strong-kill and exit-rule cases end to end.
8. Run the required common/JVM/driver checks and configured OWASP/project
   campaign. Inspect run-1 exit-rule workload, handoff graph memory and
   run-2 concrete/FLOW queries. No unrelated core refactor is included.

Acceptance requires these behavior checks, beyond the finite design oracle:

| Boundary | Required checks |
|---|---|
| Demand entry | No-demand/no-start; shared FLOW over several actual Ti; concrete mismatch; correct group/full selection; no ANY-to-EXACT start; legal E and MUST forward-only |
| STAR demand | Keep STAR; ignore field E on abstract demand endpoints; concrete ancestor E rebases on strict descent; concrete MUST/STAR meets by E union; actual E remains effective; scalar/packed equality |
| Restricted publication | Whole-member containment; exit mark mismatch; absent exit; retained full ND premise; raw NORMAL record distinct from restricted publication |
| Arrival order | Answer-first and input-first give the same applied relations; later input never authorizes a raw-summary scan |
| Static completion | Primitive/caller-bound writer saturation before static composition; all four static compositions; arbitrary chain; siblings; transitive callers; cycles; absent actors; exact MethodKey W/R ownership |
| Marked completion | FLOW diagonal, incompatible full marks rejected, colored cycle retained beside FLOW, GROUP adapter preserves actual full identities |
| Carry/grammar | Transparent wrappers, no cross-field carry or marker/field confusion, named-field and exact-marker validation retained |
| Exit routing | Unique post-return normal boundary; no return transfer; one completed exit pipeline; late CM resumes; cleaner kill; genuine source/sink observations; immediate writer supply survives an exit kill |
| Write-point pool supply | Retain p.* to C.f.* FLOW writer; immediate T/U supply for executed concrete writes in FULL/GROUP; complete guards; no dependency on an exit summary; no producer replay channel |
| Killed-write guidance | Local/static-copy/ZERO writers; exit-generated intermediate writes killed later; one/two returning wrappers; late exit resumes and survivor pruning; joined N2 read before release; no normal record/pool effect from completion |

| Other mechanisms | Real strong run-2 kills; full sink seeds; backward ZERO entry/return; source hits; normal records with nonempty legal E; unchanged run-1 origins and later ND guard support |

Production acceptance compares complete semantic observations, not an OOM
prefix or exact callback counts. Performance acceptance records run-1 engine
time separately from joined binding, candidate pruning and handoff closure
time. Record observed candidate/peak/final lost keys, bound writer keys,
static bridge memberships and lookup work, plus run-2 starts and memory. This document supplies no new project performance result.
