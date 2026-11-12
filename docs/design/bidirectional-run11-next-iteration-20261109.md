# Next iteration after the run-11 measurements

9 November 2026. **Design overview. Do not implement from this document.**
Update, 12 November: ranks 1 and 3 are selected for specification in the
[combined work-reduction and handoff spec](../../spec/in-handoff-edge-compaction.md#12-prune-impossible-local-c2-descendants).
Other ranks remain unselected. No production implementation has been made.
Measured runtime: `14d7b63369d94f49d4c551be8405ed7719f267cc`.
This is a new proposal based on the completed run-11 campaign. The earlier
main-migration proposal is historical. No runtime or experiment configuration
changes are included here. IR storage is out of scope.

## Evidence and scope

All four source Gradle commands are terminal. They used FULL marks, field limits
`1,1,2,...`, aliases and statics enabled, the same project models and rule inputs,
and the existing heap/time limits. Only OWASP reached a complete run-11 barrier.

| Project | End | Latest reached | Latest completed | Accepted forward report | Confirmed / provisional |
| --- | --- | --- | --- | --- | ---: |
| OWASP | COMPLETE / RUN_LIMIT | run-11 | run-11 | run-11 | 2,633 / 0 |
| Conductor | TIMEOUT / ABNORMAL | run-8 | run-7 | run-7 | 7 / 0 |
| Thingsboard | OOM / ABNORMAL | run-1 | none | none | 0 / 0 |
| Stirling-PDF | TIMEOUT / ABNORMAL | run-11 | run-10 | run-9 | 32 / 0 |

The default run-11 cutoff and latest-forward provisional-report policy stay in
force. RUN_LIMIT is a cutoff, not convergence. A timeout in run-11 must not expose
a partial candidate set. The new Stirling result retains the run-9 report.

The fresh profiles identify different workloads:

| Project and engine | Measured Java execution-sample scope | Share |
| --- | --- | ---: |
| Conductor run-8, backward | C2 inside the loop observer | 83.85% |
| Conductor run-8, backward | Ordinary C5 | 1.90% |
| Stirling run-9, forward | Actual saved replay outside the loop gate | 56.12% |
| Stirling run-9, forward | Virtual saved application inside the observer | 18.75% |
| Stirling run-11, forward | Actual saved replay outside the loop gate | 42.80% |
| Stirling run-11, forward | Virtual saved application inside the observer | 24.15% |
| Thingsboard run-1 | Calls | 44.91% |

These scopes do not establish operation counts or a speed factor. Actual replay
and virtual observation are different operations. Ordinary C5 is 0.01% in the two
Stirling engines. A faster C5 implementation is not the main target there.
Allocation sample weights measure churn, not retained heap. CPU sample shares,
thread wait sums, and wall time have different denominators.

The fresh Thingsboard reachable heap is 11,375,418,560 bytes. Its complete input
census separates **3,437,574 subscription inputs** from **656,046 unresolved-call
diagnostic observations**. The sum is not a subscriber count. Its global static
service retains 57,461,584 bytes; the large static-derived images and caller
inputs also live in method and subscription owners. A static writer registry
alone does not explain the heap.

Portable source data are in the [fresh profile packet](../reports/data/bidirectional-run11-profiles-20261109.json.gz),
[Thingsboard heap packet](../reports/data/bidirectional-run11-thingsboard-memory-20261109.json.gz),
and [rule-validation packet](../reports/data/bidirectional-run11-rule-validation-20261109.json.gz).
The counts needed for this proposal are stated here; they do not depend on a
private raw snapshot.

## Rank

The rank favors work that can be removed, with the strongest current evidence.
It is not a predicted wall-time ordering across different projects.

| Rank | Proposal | Current → new | Intended benefit and limit |
| --- | --- | --- | --- |
| 1 | Prune impossible C2 candidates and reject losing loop probes early | Enumerate rejected descendants and build complete trial results → skip proved-empty subtrees and stop a trial on one exact extra admission | Directly targets Conductor run-8's dominant scope; preserve the complete observation result |
| 2 | Pack neutral FULL caller inputs | Retain one qualified input per full mark → one exact geometry template and a full-mark mask, with scalar fallback | Targets the measured Thingsboard input population; requires new protocol/storage proofs |
| 3 | Remove the disabled unresolved diagnostic archive | Retain full facts before a callback that immediately returns → do no work when tracking is disabled | Removes a measured unused archive; no exact retained-byte saving is known |
| 4 | Reuse existing current-input deltas for actual saved replay | Replay old memberships before current-input deduplication → replay only memberships absent from an existing exact group | Targets a hot Stirling path; duplicate frequency is not measured |
| 5 | Avoid full exit-rule binding during prescan ID discovery | Build full bound rules to collect IDs → exact lightweight eligibility, then bind when used | Targets early binding and retained rules; exact rule-ID equivalence is required |
| 6 | Keep healthy method forms across guard scopes | Clear healthy payloads at every guard exit → keep the explicit form-cache manager until pressure or final cleanup | Avoid repeated builds; can retain more memory, and does not fix field-path growth |
| 7 | Store pending static images in exact buckets | Per-mark mutable image wrappers and unions → one immutable image plus an exact mark mask | Reduce repeated pending work; shared roots already make the physical saving much smaller than logical ratios |

All seven proposals intend to preserve the current AP semantics. They do not
change initial emission, C5, layers, protection, alias meaning, field limits,
Target propagation or rule selection. Packing FULL marks must preserve every
full identity; it is **not GROUP mode**. Diagnostic callback counts can vary as
previously allowed. No new analyzer semantic approximation is selected.

## 1. Prune C2 work and reject losing loop probes

`FrozenDemandTrie.visitCountedNativeOrder` visits strict descendants of an actual
path. `RestrictedInitialPolicy.emit` cannot emit a primary for those descendants
when the actual tail is STAR or EXACT. A failed primary emits no companions.
The descendant calls therefore cannot affect C2's answer.

For example:

```text
actual:  x.*/FLOW, NORMAL
demands: x.[any]/FLOW; x.f.[any]/FLOW; x.f.g.[any]/FLOW

Current: visit all three terminals; the two deeper demands reject.
New:     visit the same-path terminal; do not descend below x.
```

ANY and MUST must still descend. `x.[any]/T` can admit a demanded child, and
`x.[any-taint]/T` can definitely supply a child which it does not exclude.
Keep ancestor visits, same-node values, mark profiles and ordinal order.
Apply this filter only to INITIAL_C2; do not change OUTPUT_C5 or precision
cursors. Keep run-2 static completion and control handling on their existing
paths.

The second change stops a **losing prefix trial**, not the loop analysis. The
current gate computes `observe(raw)`, then complete observations for candidate
prefix cuts. Each observation includes adjacent C2, repeat C2 and saved enclosing
composition/intersection. An exact candidate admission outside the same complete
baseline family already proves inequality. Later unions cannot remove it.

```text
restrictLoopResult(raw):
    apply the existing run-1, ZERO and non-growing-summary bypasses
    baseline = completeObservationDescriptors(raw)
    if baseline is empty: drop

    for budget in existing prefix order:
        candidate = limit(raw, budget)
        for descriptor in streamLocalC2Families(candidate):
            if descriptor is absent from baseline's same scoped family:
                reject this budget immediately
                continue with next budget
        observed = completeObservationDescriptors(candidate)
        if observed == baseline: return candidate
    return raw
```

The descriptors include pattern, layer, consumer scope and ADJACENT/REPEAT label.
Use the actual `emitAdmissions` family, including companions and liveness checks.
Do not intern initials for a losing comparison. Reuse completed query work on
fallback; do not add a second complete C2 pass. Absence of an extra descriptor
does not permit acceptance: a missing baseline member or a different enclosing
result still requires the full observer. Unsupported views and run-2 transitive
queries use the existing fallback.

A principal reconstructed probe from the earlier captured Conductor demand
trie has:

```text
raw: x.MapValue.Iterable.Element.*/FLOW, NORMAL
raw C2 family: x.$; x.MapValue.*; x.MapValue.$;
               x.MapValue.Iterable.Element.*        // all FLOW, NORMAL

budget-1 candidate: x.MapValue.[any]/FLOW, DEMAND
deeper demand:     x.MapValue.MapValue.[any]/FLOW
emitted start:     x.MapValue.MapValue.*/FLOW, NORMAL
```

The last start is outside the four-member baseline family and rejects the trial.
The complete trial family has 466 starts. This is an executable reconstructed
example, not a measured live query frequency in the fresh campaign. Similarly,
an earlier STAR-root query visits 4,666 compatible terminals although only two
same-path terminals can emit. The fresh 83.85% C2 share motivates the target;
those per-query examples do not predict the overall saving.

The [nine constructive local laws and source audit](../../spec/lean/proposals/main-migration-work-reduction-20261109/README.md)
cover empty-family pruning and the first-extra negative witness. The fresh
AP/store/loop parity check supports reuse of that branch audit. They do not
prove the whole native trie, observer or analyzer. Before implementation, update
source correspondence to the chosen revision, prove descriptor materialization
equivalence, and test the full family in both directions: companions, exclusions,
marks, layers, scopes, controls, late extra members, missing-only differences and
run-2 fallback. Keep the old invalid first-budget certificate disabled.

## 2. Pack neutral FULL caller inputs

**Why FLOW subsumption does not replace this proposal:** a FLOW summary can
cover diagonal T→T results, but it does not record which full marks actually
arrived at a call. The stored T input must still match a future T→U summary
or a mark request. Packing retains those exact memberships in a mask; it
does not delete them or emit a synthetic FLOW input. Inputs already avoided
by existing subsumption need no packing. See the
[code and fact trace](../../spec/in-handoff-edge-compaction.md#15-clarification-full-input-packing-versus-flow-subsumption).

The new complete identity query preserves each accumulator owner and exact callee
key. It erases only the same identity full mark T from a singleton original and
its current fact. Every other coordinate remains in the template.

| Subscription population | Count |
| --- | ---: |
| Current input rows | 3,437,574 |
| Identity-mark eligible rows | 2,904,846 |
| Exact mark-erased templates for those rows | 299,300 |
| Scalar fallback rows | 532,728 |

This is a count of representable relations, not measured memory or speed savings.
The masks, template keys, candidate indexes and fallback still have costs.
The query found no duplicate same-T row inside a template. Its maximum template
width is 28 FULL marks; the 221 requested static marks are a different population.

An illustrative neutral call is:

```java
Node copy(Node p) { return p; }
Node use(Node p) { return copy(p); }
```

```text
Current qualified inputs at the same call/context:
  p.*/T1 -> arg0.*/T1
  p.*/T2 -> arg0.*/T2
  p.*/T3 -> arg0.*/T3

New exact representation:
  original shape p.*, current shape arg0.*, full marks {T1,T2,T3}

FLOW identity application: match geometry once; preserve the correlated mask.
T2-specific action: select/decode T2 and use the existing scalar action.
```

The captured stored relation is less simple: one exact template represents 28
rows with original `arg0.*/T` and current
`this.logEntityActionService.[any]/T, DEMAND`, under one fixed caller key, callee
key, call, stage, scope and caller layer. This is a stored native example, not an
invented Java execution trace. Exact masks reconstruct all 28 rows.

Use one table per existing owner. Keep callee/caller MethodKey, call, stage,
scope, caller layer, original base/path/tail/E, current kind/layer/base/tail/E/mx,
and complete ordinary/protected geometry. Use collision-checked equality, not a
shape hash alone. Keep plain and protected memberships separate. Never merge
different origins, contexts, geometries, exclusions or layers because their
current base is equal.

```text
admitCallerInput(ref, facts):
    if not certified singleton identity FULL relation(ref.premise, facts):
        return existingScalarAdmission(ref, facts)
    template, mark = eraseOnlyTheIdentityMark(ref, facts)
    freshMarks = templateRow(template).addExactMask(mark)
    index this geometry once
    queue current replay for freshMarks only

deliver(template, selectedMarks, operation):
    if operation has a proved neutral packed adapter:
        match geometry once and carry the exact selected mask
    else:
        decode each selected full mark and invoke the existing scalar path
```

Reuse the existing `NeutralRelationBatch` geometry/mask/decoder design and
`DiagonalRelations` admission where their contracts apply. Do not invent another
mark abstraction. However, current reuse has strict limits:

- `NeutralRelationBatch.from` requires STAR originals, empty exclusions and a
  nonstatic current base. The query's broader identity predicate does not prove
  all 2,904,846 subscription rows meet that native classifier. Its structural
  screen matched 3,521,000 eligible rows across **both** owner roles; a separate
  subscription-only accepted count was not reported.
- `applyPacked` certifies neutral ordinary statements. It does not certify a
  complete call plan, boundary rule, cleaner, alias callback or request handler.
  Do not run arbitrary call stages through it.
- `toDiagonal`/`addDiagonal` have their own uniform-mask, tail and exact-leaf
  guards. Keep them. A mark-erased template is a storage descriptor, not a new
  emitted FLOW initial; it must not broaden the run-1 initial grammar.
- Initially preserve scalar delivery at uncertified boundaries. Share retained
  geometry and candidate lookup; decode only the required mask. Extend packed
  application only after proving the specific operation.

Required proofs are exact scalar decode/encode, mask admission and growth,
candidate-index completeness, late current publication replay, request answers,
protection separation and ownership/release. Test FULL T→T correlation, T→U
fallback, ZERO/FLOW/GROUP fallback, primitive mark policies, exclusions, mixed
exact/any positions, and equal geometry under different contexts. Existing
neutral-batch tests are useful controls, not a complete proof of new caller-input
packing. No such full proof is claimed here.

## 3. Remove the disabled unresolved diagnostic archive

`JIRInterpreter` implements `UnresolvedCallObserver` even when its
`externalMethodTracker` is null. `SharedObjects.unresolvedObserver` therefore
returns a non-null object. `observeUnresolved` adds full qualified facts to its
`AddedFactAccumulator`; only then does `JIRInterpreter.reached` return because
tracking is disabled. The measured default scans do not enable external-method
tracking. The heap attributes 656,046 entries to this archive, separate from the
3,437,574 subscription inputs.

```java
void send(Node p) { unknownLibrary(p); }
// External-method tracking is disabled.
```

```text
Current: reached TAINT -> merge/archive full input -> observer -> tracker null
New:     tracking disabled -> no archive, merge, or callback
```

Expose enabled state from the observer adapter and check it before allocation or
mark-tree work. Do not confuse this observer with the new reached-sink IDs.

```text
observer = enabledUnresolvedObserverOrNull()
if observer is null: return
// Retain only work needed for the enabled diagnostic output.
```

For enabled JVM tracking, the callback passes only method/signature, current base
position and whether that position has a pass rule. `ExternalMethodTracker`
already unions position strings and ORs rule-use state. A further removal of the
full-fact archive can use that existing aggregation, with repeated callbacks or
a key based on the actual diagnostic payload. It must preserve those identities;
the batch-dependent `callSites` count may vary under the accepted diagnostic
contract. Keep a generic observer's declared contract explicit. Do not use its
diagnostic state as an AP admission condition.

Test disabled tracking with no allocated archive or callback, enabled method and
position identities, pass-rule OR behavior, ignored methods and unchanged
summaries/Targets/findings. Exact bytes dominated only by `observed` were not
queried. The retained-size sums for entire call-service objects include other
machinery and must not be advertised as the saving from this removal.

## 4. Replay saved relations only for existing-group growth

Both real paths replay saved records before their current-input table removes
duplicates. Function calls use `CalleeSubscriptions`/`AddedFactAccumulator`;
internal blocks use `BlockSummaryLinks`/`LocalInputDirectory`. These tables retain
the complete offered packet after successful current admission, not just C2's
selected initials. A non-creating peek can use that existing image.

```java
Node id(Node a) { return a; }
Node f(Node p, boolean b) {
    Node x;
    if (b) x = p.f;
    else   x = p.f;
    return id(x);
}
```

The two producers can offer the same `P -> arg0.$/T, NORMAL` to one call.
Currently each runs saved matching/application before current subscription
admission notices the duplicate. If a current group exists, the second saved
delta is empty. Its saved scan and return continuation need not run.

```text
handleOffer(fullOffer):
    old = peekExistingExactCurrentGroup(fullOffer) // no allocation/registration
    delta = fullOffer if old is absent else mergeAddDelta(old, fullOffer).delta
    replay saved records and saved NORMAL Targets on delta, if nonempty
    initials = C2(fullOffer)                      // original full packet
    if initials is empty: return                 // retain no new history
    admit actual internal-block targets, if applicable
    admit/subscribe the full offer after saved work, as now
    deliver the complete initial packet, as now
```

The exact key includes callee and caller context, complete original premise,
caller layer, call/stage/scope and the full group header, including protection.
Local keys also keep parent/child scopes and logical ports. Use the full offer's
key: an exact-only delta can have a different canonical tail/E header.
Use a transient prepared merge only if its old-row identity is still current;
otherwise recompute at commit. Do not mutate the group before saved replay.

On a group miss, including saved-only inputs with no current demand, keep the
selected full replay on every offer and retain no new history. A rejected new
offer must not grow an old group either. If an old group exists, only its already
processed memberships can be omitted; all other memberships still replay.

An empty saved delta must not skip the whole block offer. On reversal of a loop
with two break predecessors, the same logical normal-entry input can reach a
new real predecessor. `admitTarget` must still start prior initials there.
Many local offers are already fresh through `addCompletion`; duplicate frequency
in the hot forward runs is not known. The JFR shares are not a duplicate count.

Prove the fixed-record delta law, complete key separation, counted pending work,
stateful return-rule/ND Target joins, MUST definite/provisional lanes and physical
port behavior. Keep C2 on the full offer. Do not delta-filter the pure
`LoopConsumerObservation`, which must return a complete comparison signature.
Add no saved-input history store and no source-support mechanism. The detailed
read-only source audit is preserved in the campaign's
`next-run11-candidates/source-replay-delta.md`; this section states the complete
candidate contract needed for selection.

## Lower-ranked candidates

### 5. Avoid full exit-rule binding for prescan ID discovery

Fresh Thingsboard has 4,083,550 bound method-exit sink objects, versus 129
serialized exit-sink records. The provider root retains 801,212,672 bytes. These
numbers establish an expansion category, not its exact per-rule/epoch cause.

Current prescan ID discovery can request full bound rules. Use exact lightweight
context/condition eligibility to collect the same IDs, then bind a full rule when
an actual method boundary needs it. This is different from the ownership-census
optimization already implemented.

```text
prescan: collect exact eligible serialized IDs without full action objects
use:     resolve the selected boundary rule through the existing binder
```

For a void method, `CM(Result,T)` can become false while its negation becomes
true. Static/this positions, missing arguments, unconditional guards and negative
conditions must keep their existing behavior. Prove exact ID selection and rule
reduction equivalence; do not substitute name-only matching. Confirm which
binding epoch remains live before proposing its release. Add no second strong
cache. Recorded resolver waits are early: they do not explain Conductor run-8 or
Stirling run-9/run-11, which have no recorded resolver monitor waits above the
JFR threshold.

### 6. Retain only the explicit healthy form-cache manager

All three memory-guard scopes—engine, run-1 joined phase, barrier—currently clear
managed payloads at exit. The method-form owner survives. Later runs can rebuild
the same forms. Fresh Thingsboard's narrow form payload/lookup scope is 32.69%
of Java samples; it overlaps rule binding and is not all removable compilation.
OWASP also has repeated late form/predicate construction.

```text
guard exit: retain only the explicit analysis-owned form-cache manager
pressure:   keep existing eviction, callbacks, deadlines and cancellation
final join: clean that manager once at the analysis-owner boundary
legacy:     retain the existing default clear-on-exit policy
```

Do not rewrite `SoftReferenceManager`, introduce `WeakIdentityCache`, or retain
unrelated per-run interners. Audit cached payloads for run-specific closures and
keep FULL/RUN1_GROUP views separate. Prove cache hits return the same payload as
rebuild; test all three guards, forward/backward reuse, pressure eviction and
failed/cancelled final cleanup. Retention can increase memory pressure on
Thingsboard. Small soft-payload storage in the snapshot does not mean the strong
method/graph/alias scaffolding is small or will be removed by this change.

### 7. Use exact pending static image buckets

There are 2,827,665 `PendingFlowImages` wrappers, with 45,242,640 shallow bytes.
2,648,677 retain only their own 16 bytes. Most roots are already shared. The
23.8204 logical-coordinate quotient is not a physical-memory or speed ratio.

Current `pending[T]` eagerly merges an incoming image per requested mark. Store
an immutable image bucket with an exact FULL-mark mask instead. Merge geometry
only when answering a specific mark:

```text
request(image I, marks M): bucket(I).marks union= M
answer(T): union only images whose bucket mask contains T; remove T from them
```

Keep the full point key, operation, original, layer and continuation state.
Do not form a Cartesian product between images and marks. Start with immutable
root identity buckets; content-equal distinct roots need checked equality before
merging. Prove each T receives exactly the old image union, including late image
growth and answer detachment. The global writer store itself has only 1,023 FLOW
writer rows in this snapshot; do not target it based on the much larger pending
population elsewhere.

## Semantic boundaries and known blockers

Before selection, write the detailed spec/source correspondence, constructive
proofs and native tests required by `spec/proof-guide.md`. The old local C2 laws
do not prove new caller packing, saved replay or cache lifetime. A new
implementation proposal must name all changed owners and scalar fallbacks.

These correctness questions remain separate and unselected:

- The known cleaner/entry-source descendant findings and Spring scoped
  ZERO/Target routing failures. Do not hide them in a storage or C2 change.
- Changing synthetic alias meaning, including the pre-existing loss of
  `taintCopyOnly` before alias extraction. Removing aliases can change findings;
  model fields are not invalid merely because they are not physical Java fields.
- Changing the sink's physical report location or evaluating exit rules at each
  return. That can alter identity or boundary joins.
- Relaxing unsupported rule shapes, changing GROUP behavior, protection,
  initial-emission/C5 rules, the field schedule or the run-11 report contract.

The fresh strict rule gate passed 585 actual Java BIDI samples and 201 Go samples,
with zero FP/FN/skipped classifications. It also has 22 disabled Java tests and
two explicitly uncollected RemoteService declarations. Those are not executed
passes. Common 2,550 and JVM 467 native tests pass, but the broad root suite has
1,083 tests with **20 failures and 11 skips**. Preserve this distinction and all
real finding assertions. An optimization must not waive a known failure.

## Selection and experiment gates

Do not implement all ranks as one change. Select candidates, then complete their
proofs and implementation plans. Keep each mechanism reviewable on its own.
Use the current FULL project configuration and the existing baseline; do not
change heap, time limits, aliases, statics or rule inputs to manufacture a win.

After each selected change, measure the work it claims to remove:

| Candidate | Required work evidence |
| --- | --- |
| C2 / early rejection | Visited nodes/terminals, identical emitted families, extra witnesses, full fallbacks, interned initials and saved observations avoided |
| FULL input packing | Native eligibility/fallback counts, exact templates and masks, scalar decodes, candidate matches and retained owner layout; verify exact per-mark reconstruction |
| Disabled observer | Zero disabled archives/callbacks; enabled diagnostic identities and unchanged analyzer outputs |
| Saved replay delta | Exact-group misses, covered offers, partial/disjoint growth, C2 misses, saved candidates/applications avoided and preview cost, separately for functions and blocks |
| Binding / forms | Bound objects/IDs, build/reversal counts, pressure rebuilds, early wait scope and retained strong/soft owners |
| Static buckets | Exact point/mark/image memberships, unions performed at request versus answer, wrappers and shared-root ownership |

Repeat project and rule validation with no overlapping heavy jobs. Compare strict
finding identities and confirmed/provisional classification, not just totals.
Compare common completed frontiers as well as final outcomes, because a faster
run can reach a later frontier within the same budget. Always state latest
reached, completed and accepted forward run labels. Separate RUN_LIMIT,
empty-demand convergence, TIMEOUT and OOM. Reinspect exact fact paths and their
processing pipelines after landing a selected optimization; do not infer the
remaining bottleneck from an earlier profile.
