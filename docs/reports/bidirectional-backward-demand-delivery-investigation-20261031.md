# Backward demand growth and summary delivery

Date: 31 October 2026. Production runtime:
`e090118e5f9603f1973c0578a3e04998035f4508`. Repository head `3d8116a1a`
adds reports and controls; production sources are unchanged.

Status: closed investigation. Both passive diagnostic commands and all observer
helpers are closed. They are separate from the completed performance campaign.
No analyzer change is implemented or selected.

The original campaign reached **Stirling run-7**, completed **run-6**, and
accepted **run-5**. Conductor reached **run-4**, completed **run-3**, and
accepted **run-3**. Its run-4 ended on timeout.

## 1. Findings

Stirling's growth is concentrated. Two methods own 94.32% of the run-6 outgoing
rows. New method keys enter through the backward ZERO protocol. This protocol
can start a sink requirement without an incoming explicit demand row. Its
output bypasses ordinary summary restriction and becomes new forward demand.

This mechanism is specified. It does not prove that all generated paths are
useful. The diagnostic confirms two concrete gaps: backward requirements contain
fields from unrelated model classes, and constant-base requirements cross the
method-summary boundary even though ordinary JVM method inputs cannot supply
that base. Library taint copies are used as pointer aliases and can create
self-cycles. Almost every exported diagnostic row is a distinct path geometry,
rather than a new mark on the same path.

Conductor's main measured cost is current-summary delivery. Backward resumption
uses reverse argument binding and caller output admission. The function name
`resumeCallees` does not mean that this run executes the forward return pipeline.
The diagnostic records 231.16 million current-summary applications. An
infeasible List/HashMap context accounts for at least 29.90% of whole-run
application entries. In a later output window, 99.90% of completed point-store
adds produce no new delta. This is mainly small nonstatic FLOW composition,
not the same ZERO path-generation bottleneck as Stirling.

## 2. What the counters mean

A **method key** identifies a method entry point and its analysis context.
The backward engine uses the same owner key as the forward engine.

These logged quantities have different meanings:

| Counter | Meaning |
|---|---|
| `analysed` | Method actors that started at least one nonzero initial |
| `zero only` | Method actors with no nonzero initial |
| `demand edges` | Accepted normalized outgoing demand memberships |
| `in N method keys` | Owners with at least one outgoing explicit membership |
| `left` | Nonzero-initial owners with no outgoing explicit demand |
| `record crossings` | Productive persisted-record applications; not demand rows |

An AP is an access path. FLOW carries an abstract mark; T denotes one full
concrete mark. `$` is an exact-object tail, `*` is a STAR tail, and `[any]` is
an unresolved suffix. The field limit bounds counted field/element accessors;
static class anchors do not count.

ZERO is a control premise, written `0` below. A ZERO-only actor can propagate
millions of concrete marked requirements. It does not process only the zero
fact. A sink seed creates a concrete requirement under premise ZERO without
starting a nonzero initial.

All ratios below use the stated counter unit. A smaller outgoing frontier does
not bound call offers, summary applications, instruction work or tree size.

## 3. Stirling run-6: where the growth occurs

The saved original frontiers give:

| Iteration | Direction / limit | Nonzero-initial actors | ZERO-only actors | Outgoing rows | Outgoing method keys |
|---|---|---:|---:|---:|---:|
| run-5 | forward / 4 | 110 | 7,147 | 888 | 74 |
| run-6 | backward / 5 | 55 | 7,202 | 185,950 | 306 |

Run-6's ZERO-only actors produce **15,164,952 edge deltas**, compared with
148,411 in run-5. It also makes **4,180,880 productive record crossings**,
creates 17,725 ZERO-only subscription entries, and hands off 831 source seeds.
Its ordinary caller gate rejects 4,149,399 of 4,158,533 offers (99.78%). These
numbers locate work outside the ordinary initial-admission gate.

The outgoing growth is not spread uniformly:

| Method owner | After run-5 | After run-6 | Contribution to run-6 |
|---|---:|---:|---:|
| `AdminSettingsController.updateSettingsSection` | absent | 90,991 | 48.93% |
| `PipelineProcessor.runPipelineAgainstFiles` | 70 | 84,400 | 45.39% |
| `GetInfoOnPDF.getPdfInfo` | absent | 4,091 | 2.20% |
| All other owners | 818 | 6,468 | 3.48% |

The exact support difference is:

```text
74 old owners
  20 disappear:                    49 old rows
  54 remain:                      839 -> 85,815 rows
252 new owners:                          100,135 rows
---------------------------------------------------
306 outgoing owners:                     185,950 rows
```

The 252 added owner names are exactly the outgoing ZERO-only owners. In
particular, `updateSettingsSection` has no incoming row and no nonzero initial
in run-6. Its 90,991 rows have ZERO origin. The raw logs have unique printed
owner names for these runs, so this set comparison is exact. Early runs of
some projects have bridge methods with the same printed signature; the parser
retains those raw entries and does not claim unique identity from that display.

### 3.1 Why ZERO search can reopen the frontier

The actual route is:

```text
previous forward report still has a DEMAND sink
    -> HandOff.toBackward creates its sink seed
    -> backward ZERO reaches the method
    -> seed injects a marked requirement under premise 0
    -> reverse transfers and balanced callee summaries propagate it
    -> method-entry result is a backward summary 0 -> requirement
    -> backward ZERO bypasses local C5 restriction
    -> selectDemand keeps it, including a NORMAL result
    -> HandOff.toForward emits (entry=requirement, exit=none)
```

`C5` means the intersection of an ordinary produced summary with its local
paired demand. A backward ZERO result is its explicit exception. An entry-only
row (`exit=none`) can admit next-run initials; it grants no ordinary C5 exit
permission. Thus backward expansion can be followed by a much smaller forward
frontier.

This example shows why an absent incoming owner is not enough to drop the
backward result:

```java
// Selected backward run. L has no incoming explicit row.
// The prior forward report supplies a seed at this sink.
void L(Box p) {
    Box x = p;                 // reverse: 0 -> x.f.$/T becomes 0 -> p.f.$/T
    sinkT(x.f);                // seed: 0 -> x.f.$/T, NORMAL
}
// Backward summary at method entry: 0 -> arg(0).f.$/T, NORMAL.
// Next forward demand for L: (arg(0).f.$/T, none).
// A later actual marked input can now start analysis of this entry path.
```

NORMAL here means that this dependency path was not widened. It does not turn
the seed-dependent result into an unconditional native record. The record
policy excludes backward ZERO summaries for this reason. Removing the bypass
or persisting the summary as an ordinary transfer is a semantic change.

### 3.2 Local path growth: current diagnostic

The separate passive diagnostic completes run-6 with **186,048 rows / 306
keys**, versus 185,950 / 306 in the original campaign. Use the diagnostic's own
denominator. Its frozen census gives:

| Diagnostic run-6 quantity | Count | Share of normalized outgoing rows |
|---|---:|---:|
| ZERO-origin, unpaired rows | 184,756 | 99.31% |
| Rows owned by ZERO-only actors | 100,136 | 53.82% |
| Constant-base rows | 89,698 | 48.21% |
| All outgoing rows | 186,048 | 100% |

ZERO origin and ZERO-only owner are different tests. `PipelineProcessor` has
nonzero initials, yet most of its exported dependencies originate at ZERO.
The census counts 48,308,793 processed items and 41,416,248 edge deltas across
all actors. The three focused owners are:

| Owner | Rows | Geometries with marks removed | Depth-5 rows | Processed items | Edge deltas |
|---|---:|---:|---:|---:|---:|
| `updateSettingsSection` | 90,992 | 90,942 | 82,154 | 2,569,911 | 2,603,057 |
| `runPipelineAgainstFiles` | 84,397 | 84,397 | 72,655 | 31,157,834 | 25,518,811 |
| `getPdfInfo` | 4,091 | 4,083 | see embedded histogram | 8,136,771 | 7,285,016 |

The geometry key retains both endpoint bases, paths, tails and exclusions,
but removes marks. No scratch cap was hit. One full mark contributes 90,926
Admin rows; one other mark contributes 84,389 Pipeline rows. Almost every row
has a different geometry. A large mark product is not the main explanation.

### 3.3 Taint-copy models create pointer-alias cycles

The source path is:

```text
serialized library copy, including taintCopyOnly=true
    -> resolver constructs CopyAllMarks; it does not preserve that flag
    -> alias model treats every CopyAllMarks as a pointer ExternalAssign
       without testing the rule condition
    -> DSU unifies both path endpoints
    -> resulting aliases become ordinary call micro-edges
    -> those micro-edges can run repeatedly in loops and recursive summaries
```

For `Entry.getValue`, the model has both transfers below. The broad transfer
has `taintCopyOnly:true`:

```text
mark transfer A: this       -> result
mark transfer B: this.Value -> result

current pointer-alias interpretation:
    this == result
    this.Value == result
therefore:
    this == this.Value == this.Value.Value == ...
```

A broad copy for `StrTokenizer.next` and its precise storage copy produce an
analogous cycle. Those rules do not all set `taintCopyOnly`. Reading that flag
alone is therefore not a complete repair. `StringConcatRuleProvider` also
copies marks from every operand to the result. The alias provider treats those
copies as pointer assignments too.

The actual Admin source includes:

```java
ResponseEntity<?> updateSettingsSection(String sectionName, Map<String, Object> changes) {
    for (Map.Entry<String, Object> entry : changes.entrySet()) {
        String fullKey = sectionName + "." + entry.getKey();
        saveKeyToSettings(fullKey, entry.getValue(), ...);
        pendingChanges.put(fullKey, entry.getValue());
    }
    // Exit sink seeds also examine the returned response object.
    ...
}
// E is one synthetic accessor: java.util.Iterator#Element.
// Diagnostic backward result, premise ZERO:
// arg(0).E.E.E.E.E.[any]/T93, DEMAND, empty field exclusions.
// arg(0) is the declared String sectionName.
// T93 = java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2.
```

The captured alphabet also contains `StrTokenizer` storage and pair fields.
`StatementSummary.reversed()` drops the forward operand/result type-filter
maps. Subclass library models can therefore contribute heterogeneous field
branches to these requirements. The compiler's alias/type work happens before
the expensive propagation; a small sampled cost in a function named `alias`
does not show that alias-derived work is small.

A standalone control uses the current production DSU and heap-alias APIs.
The broad-plus-field pair creates the self-cycle; the precise-field-only
control does not. With three self-cycle labels, it witnesses 243 depth-5 paths
and 729 depth-6 paths. This is a mechanism proof, not an estimate that the project
has exactly three labels. In the diagnostic, Admin grows from 923 rows at
backward limit 3 to 90,992 at limit 5. Pipeline grows from 2,595 to 84,397.
These are two different backward runs with different seeds/frontiers; the
ratios are not a controlled field-limit experiment.

The live per-statement alias targets were not exported. The current paths,
source adapter and real DSU control establish this amplification mechanism;
they do not assign every project row to one alias rule. No model-removal or
rollback arm was run. A one-flag fix has no measured project saving yet.

The design gap is the use of a taint-copy relation as pointer-alias evidence.
Its products are mostly distinct paths, so ordinary duplicate elimination
cannot remove them. The field limit bounds their length; it does not give a
small number of paths. This explains a finite explosion without requiring an
infinite loop.

### 3.4 Constant requirements leave a boundary that cannot supply them

The JVM interpreter accepts every nonlocal, non-cleaner base as a summary
base. This includes literal constants. Reverse argument binding can turn a
formal requirement into a requirement on a caller literal:

```java
String build(String section, String key) {
    return section + "." + key;
}
// Backward requirement on the concatenation result, T.
// Reverse mark-copy dependencies include:
//   section/T, constant(".")/T, key/T.
// The constant requirement is retained through the caller and can be exported.
```

Admin exports 42,057 constant rows; 41,980 belong to literal `"."`. Pipeline
exports 43,095 constant rows. GetInfo exports 4,072. Across all actors,
89,698 normalized outgoing rows are constants. Selected constant leaves before
normalization comprise 65,436 ZERO/DEMAND and 24,262 ZERO/NORMAL memberships.
All are seed-dependent and ineligible for native record persistence. Raw
summaries also contain 3,603 NORMAL FLOW constant memberships that are eligible
for persistence; a boundary repair must consider those records too.

The selected JVM call adapter supplies only ZERO, STATIC, THIS and formal
arguments forward; backward adds formal return positions. Roots start ZERO.
Sources do not start constant initials. Lambda captures remain fields under
formal bases. Thus a constant entry requirement is outside the supplied
method-initial domain. The generic core still permits Constant initials through
custom APIs; this argument is for the selected JVM adapter.

There is another cost at summary delivery. A ZERO subscription still applies
a Constant conclusion and resumes the call. Cleaner statement substeps can
preserve it. The mandatory generated binding then uses strict `FormApplier.stage`,
which has no untouched-input fallback and no Constant source. It gives no
caller-point result for that Constant. A production-API control checks both
kinds of stage and also the positive reverse-binding route that creates a
local Constant requirement. Therefore “never applied” would be incorrect:
these publications can incur work before the binding discards them.

Keeping local source/rule/sink work and filtering unserviceable boundary rows
is a focused opportunity. It removes handoff/storage work. Preventing the
constant requirement earlier in reverse binding could also remove local
propagation, but needs a separate source-observation proof. **48.21% of rows is
not 48.21% of engine time.** The stopping and reporting effects must be checked,
as well as call-query and suffix-observation equivalence. A local Constant
requirement can enter another call which uses that literal; absence of constant
method initials alone is not a proof that all local Constant processing is
unobservable.

### 3.5 What these measurements rule out

The dominant new demand is not a product of many marks on one AP. It is mainly
ZERO-origin, deep, distinct field paths. The caller admission gate already
rejects almost all ordinary offers. Another input-dedup cache does not prevent
this producer. Normal backward ZERO demand cannot simply be dropped or reused
as an unconditional transfer record. A safe change must address the false
alias producer, unsupplied constant requirements, or a proved tighter seed
search domain.

## 4. Conductor run-4: what consumes the time

The original run-4 has 14,138 Java samples and 2.928 TB of sampled allocation
weight. Current-summary delivery accounts for **69.96% of Java samples and
87.83% of allocation weight**. Persisted replay is 9.29% / 2.75%; demand lookup
is 1.84% / 0.36%; live-input accumulation is 0.59% / 0.07%.

These are inclusive families. A separate disjoint stack partition assigns
each sample once, with the saved phase-predicate precedence:

| Phase | Java share | Allocation share |
|---|---:|---:|
| Candidate snapshot | 16.43% | 1.16% |
| Input matching | 3.71% | 8.92% |
| Summary parts | 1.10% | 4.58% |
| AP image geometry | 14.14% | 25.31% |
| Resumed ordinary stage | 8.33% | 10.51% |
| Resumed own field limit | 2.81% | 4.53% |
| Resumed output subtraction | 1.75% | 21.17% |
| Other resumed output admission | 9.58% | 0.32% |
| Other resumption | 8.23% | 7.06% |
| Cleaner chain | 0.74% | 1.06% |

Each row's denominator is the complete run-4 Java or allocation sample set.
The partition is exhaustive with its saved remaining/outside buckets. It does
not infer that every subtraction returns an empty delta.

### 4.1 The actual backward stage pipeline

```text
callee publication arrives
    -> snapshot current candidate inputs
    -> match each complete current input
    -> ZERO-only: use the published conclusion directly
       ordinary: build the AP summary image
    -> resume at backward Callees.to = ADDED
    -> reversed cleanup actions, ADDED -> BOUND
    -> reversed argument binding, BOUND -> BEFORE
    -> caller's field limit and post-statement edge store
```

The forward return-value rewriter, forward bind-back and forward alias lanes
are not this backward suffix. Cleaner-chain work is small in the profile.
The remaining cost is not explained by a missing initial demand lookup.

### 4.2 Repeated geometry versus distinct premise support

Current input storage keys include the complete original premise. Input matching
does not read that premise. A FLOW-premise summary also does not use it during
AP geometry application. The caller still needs each original premise as
support for the resulting relation.

```java
class Model {
    List<Task> getTasks() {
        return tasks;
    }
}
// Backward publication: ret.*/FLOW -> this.tasks.*/FLOW.
// Two caller origins I1 and I2 have converged to the same supplied ret.*/FLOW.
// Current input storage correctly retains (I1, input) and (I2, input).
// Current work: 2 matches -> 2 equal images -> 2 reverse bindings -> 2 supports.
// A factored design could compute 1 geometry and keep both supports.
```

A production-AP control verifies this two-origin case. The two input groups and
two post-statement supports remain distinct; same-support duplicate output is
rejected. Dropping the second origin is incorrect. The existing equal-image
proposal only merges within the same full caller reference, so it does not
remove this case across different original premises.

A separate control shows that register-before-replay plus queued delivery can
apply the same complete pair twice: fresh replay sees a committed publication,
then its queued delivery also sees the admitted input. Existing output stores
deduplicate after matching and application. The diagnostic measures these two sources separately. Its first-200,000-application
window retains only 2,304 applications because its 2,048-key cap is reached.
It records 256 same-origin repeats across replay/delivery and no different-origin
opportunity in that retained prefix. These small early repeats are real; the
capped prefix does not measure the late hot-loop duplicate rate. The production
AP witness alone cannot rank geometry sharing as the main project fix.

### 4.3 Incompatible type contexts already exist before run-4

The original run-3 debug frontier contains these owners:

```text
ParametersUtils.replaceList(List, ...)       [{arg(0) == java.util.HashMap}] : 54 rows
ParametersUtils.replaceVariables(String, ...) [{arg(0) == java.util.HashMap}] : 112 rows
replaceVariables(String, ..., int)            [{arg(0) == java.util.HashMap}] : 121 rows
```

The `==` context is an exact runtime-type qualifier on the callee argument.
It is not the type of a taint origin or a renamed caller slot. Exact HashMap
is incompatible with the String and List formals above.

The resolver derives allocation types through aliases. It can prefer an exact
alias-derived constraint without intersecting it with the value's static type.
Context construction only removes redundant broad qualifiers; it does not
reject incompatible ones. Boundary filters choose the context type instead of
checking its intersection with the formal type. Reversal then removes those
filters.

This gives the alias-model problem another multiplier: the prescan can create
method contexts which the real call cannot have. A correction must discard
contradictory alternatives and keep a static/default feasible fallback when
all inferred alternatives are invalid. Deleting the sole inferred call target
would be unsafe. The existence of the inconsistent contexts is measured;
their run-4 workload share awaits the caller census below.

### 4.4 Closed diagnostic: hundreds of millions of small applications

The separate diagnostic times out in **run-4**, with **run-3 complete and
accepted**. It enters run-4 with 19,912 rows / 552 keys, versus the original
20,661 / 552. Its counts describe its own event trace. It records
**231,160,357 current-summary application entries** in run-4, compared with
4,363,659 ordinary restricted call offers. These are different protocol events;
the ratio is not a literal duplicate rate.

The first observer's all-run owner-by-callee table fills before run-4. Its global
counts remain valid. A smaller caller-only observer is attached during run-4;
it reads the existing delivery scope and does not restart the engine.

Its closed interval is **02:37:28.176–02:48:08.165 UTC**:

| Caller context | Current-summary entries | Share of this late interval |
|---|---:|---:|
| `replaceList(List, ...) [arg(0)==HashMap]` | 69,117,135 | 47.30% |
| `replace(Map, ...) [arg(0)==HashMap]` | 68,637,447 | 46.97% |
| `getTaskInputV2`, default context | 4,237,951 | 2.90% |
| `getTaskInputV2 [arg(0)==HashMap]` | 1,537,573 | 1.05% |
| Other caller descriptions | 2,587,958 | 1.77% |
| Total | 146,118,064 | 100% |

The infeasible List/HashMap context alone contributes a **29.90% lower bound
of all run-4 application entries**, counting only its observed late subset.
This is an application share, not a CPU share. A feasible replacement context
will still need some work, so it is not a promised 29.90% time saving.

Of these late entries, 145,637,088 (99.67%) apply FLOW-premise publications;
475,820 apply concrete-premise publications; 5,156 are ZERO; none are ND.
Selected inputs are almost entirely nonstatic. Static publication conclusions
account for only 475,820 entries. This interval is not a static-input or ZERO
fanout bottleneck.

Published conclusions average **5.20 spatial trie nodes** and selected inputs
average **4.34**. The maxima reach 1,555. A large-node tail exists, but the
average application does not involve a huge spatial tree. Mark-set width is
not measured by node count. The two recursive Map/List helpers amplify a very
large volume of small relations.

### 4.5 Output deduplication is too late to avoid this cost

A return-only observer counts completed `MethodEdgeStore.add` calls inside
run-4 current delivery, from **02:41:52.516–02:48:08.165 UTC**. It observes
returns without changing the returned reference, null value or exceptions.

| Store-return result | Count |
|---|---:|
| Completed add attempts | 86,714,846 |
| Fresh returned delta | 82,614 |
| Null: no new delta | 86,632,232 (99.904729%) |

Only two caller contexts make these scoped adds:

| Caller context | Attempts | Fresh | Null |
|---|---:|---:|---:|
| Infeasible `replaceList(List) [HashMap]` | 44,333,003 | 40,133 | 44,292,870 |
| `replace(Map) [HashMap]` | 42,381,843 | 42,481 | 42,339,362 |

FLOW-origin attempts are 99.885420% null; concrete-origin attempts are
99.929598% null. Of 481,353,249 offered node occurrences, 480,823,630 belong to
null-return adds. No constant or ZERO base is offered in this output interval;
only 17,778 attempts have static bases.

The store correctly removes already covered or subsumed memberships, including
protection semantics. It cannot recover the matching, AP image, binding and
allocation work already done. A null add does not prove that its exact raw
image or complete input pair was processed before. Different derivations,
field-limit cuts and coverage can converge to the same stored relation.

This is a measured algorithmic target: stop producing irrelevant contexts and
phantom alias paths, then design an output-sensitive join that preserves every
origin and rule observation. Another full-fact input history or a faster null
check is not the principal fix. A blanket skip based only on output coverage
would need a proof for source/cleaner observations before admission.

The late observers have no errors or owner overflow. Their final counters and
caller partitions reconcile exactly. Adds outside summary scope (1,190,050)
and outside requested run-4 delivery scope (38,728) are explicitly excluded.
Their intervals differ; do not divide completed adds by all application entries
as if they formed one common batch.

## 5. Why method-key counts can increase

Let `K(D)` be the set of method owners with an explicit demand row. Let `A` be
the set of actors with a nonzero initial. For run-i at i>=3, static completion
and shared static carry are absent. The source gives these support laws:

```text
A_i is a subset of K(D_(i-1)).

If run-i is forward:
    K(D_i) is a subset of K(D_(i-1)).

If run-i is backward:
    every owner in K(D_i) minus K(D_(i-1)) is ZERO-only.
```

Ordinary C2 initial admission needs a local incoming row. Ordinary C5 publication
also needs that row. The backward ZERO bypass is the only publication path
that can add a new later-run owner. Handoff keeps the same method key; it does
not spread rows to unrelated owners. The full available local-only transitions
pass these checks in the saved logs.

For example, OWASP has only 85 rows / 22 keys after run-3, but 198,829 rows /
3,791 keys after run-4. Run-4 has only two nonzero-initial actors. Its other
**3,789 demanded owners and 198,815 rows** come from ZERO-only actors. The
forward run-5 then finishes with no outgoing demand. An increase alone does
not prove failure to converge.

The diagnostic has the same 7,254 actor-description IDs in run-5 and run-6.
The selected outgoing owners change; the engine does not need to discover new
program methods to produce this growth. A fixed call graph permits this behavior.

A method-key count also includes contexts. Stirling's 306 run-6 keys describe
304 distinct printed method signatures; run-5 has 74 of each. Its growth mainly
reopens methods, with two additional context keys among the new signatures.
Conductor has many more specializations: run-1 has 6,289 keys / 5,429 printed
method signatures; run-2 has 9,263 / 7,581. Printed signatures omit return type,
so early bridge collisions remain a stated lower-level display limitation.

Run-2 is an explicit exception to these tighter local-only laws: its incoming
snapshot includes run-1 virtual static completion and shared carry. Conductor's
run-1-to-run-2 key growth must not be judged by the later-run subset rule.

The [constructive support kernel](../../spec/lean/investigations/method-key-support-20261031/README.md)
proves these conditional boundary laws and an arbitrary-length seeded call-chain
example after exact deduplication. It has 43 explicit theorems and audits all
337 declarations, with no unexpected axioms. It abstracts C2/C5 payload tests;
it is not a proof of every Kotlin callback or global convergence.

## 6. Design gaps and safe next steps

The first target is the producer of false alias states, before another cache
or data-layout change. The current evidence ranks these directions:

| Priority | Change to investigate | Current behavior -> proposed behavior | What it can remove | Semantic scope and proof gate |
|---|---|---|---|---|
| 1 | Separate mark copying from pointer-alias modeling | Every CopyAllMarks supplies an alias -> use explicit alias eligibility, preserve taintCopyOnly, and model fresh concat results correctly | Phantom self-cycles and their field-path products before propagation | Changes alias precision and downstream contexts. Keep mark-copy transfers. Audit real pointer copies and unflagged models; one flag alone is not the complete fix. |
| 2 | Reject infeasible exact method contexts with a feasible fallback | Alias-derived HashMap can qualify String/List arguments -> intersect with static/formal constraints before specialization | Entire impossible contexts, their actors, inputs and summaries | Changes context selection. Prove real call coverage; never drop a call because its only inferred alias alternative was bad. |
| 3 | Keep constant requirements out of JVM boundary publication/handoff | Constant results can be published, applied and discarded by strict binding -> reject the unserviceable boundary result after required end-rule work | Up to 89,698 diagnostic outgoing rows plus their wasted delivery; not a measured time fraction | Prove the selected JVM domain, native/opposite record behavior, observations and driver stopping. Early local pruning is a separate change. |
| 4 | Make reversed model filtering precise | Reverse transfer discards the forward filters -> preserve proved converse constraints on individual edges | Heterogeneous requirements that cannot represent an actual transfer | Changes precision. Whole-map swapping is unsafe: reversal adds identity branches for gen-only targets, which need separate treatment. |
| 5 | Remove repeated current-summary computation | Replay/delivery and separate origins can repeat geometry -> use a proved join frontier or factored geometry with all supports | Repeated matching, grafting, binding and store subtraction | Intended operational optimization. Preserve full context, masks and origin sets. Current project duplicate rates are bounded observations, not a global saving estimate. |

The first four are semantic precision or correctness changes. They must not be
introduced as hidden technical optimizations. The last can preserve the current
relation semantics, but needs its scheduling and observation proof. A finite
alias/control example is not a proof of a twofold project speedup.

No change to field transfer, type filters, mark semantics, seed/export policy,
record eligibility, aliases, context construction, origin preservation or
stopping is implemented here. These directions need separate implementation
specifications before production changes.

## 7. Evidence and limits

The [companion data](data/bidirectional-backward-demand-delivery-investigation-20261031.json)
embeds exact original owner maps, reduced diagnostic captures, decoded vocabularies,
observer controls and source hashes, the disjoint profile partition, finite AP
controls and proof receipts. Raw recordings and full untrimmed observer dumps
remain outside Git. The prior
[performance report](bidirectional-selected-call-policy-performance-20261030.md)
retains the complete original measurements and accuracy limits.

The [validation receipt](data/bidirectional-backward-demand-delivery-investigation-20261031-validation.json)
binds the report/data hashes and checks source, input, counter, owner-map and
proof consistency. Both diagnostic commands retain these final labels:

| Diagnostic | Status | Reached | Complete | Accepted forward |
|---|---|---|---|---|
| Stirling | TIMEOUT | run-7 | run-6 | run-5 |
| conductor | TIMEOUT | run-4 | run-3 | run-3 |

The two diagnostic replays keep 16 GB, FULL marks, statics and aliases enabled,
1,080-second IFDS and 1,200-second outer budgets, and limits 1,1,2,3,... . Initial
JVM/analyzer arguments match after removing observer options and normalizing
output paths. Two later observers attach to conductor without a restart. They
add observation calls only; their instruction/return/exception controls pass.
Their times are not clean performance measurements.

Both diagnostic exports have exactly the same strict sink identities and
multiplicities as the original campaign: conductor 7/7, Stirling 30/77. This
checks the accepted reports, not whole-project completeness after timeout.
Prelaunch and postrun full input audits both pass for 25 datasets and four
models. Previous closed raw captures/indexes were removed only after their
parsed evidence was committed (32 files, 57,789,281,983 bytes). Production
sources remain unchanged. The first capped owner probe, the bounded equality
sample and the late intervals retain their explicit limitations.

For future investigations, add cheap barrier counters for paired/unpaired
rows, ZERO NORMAL/DEMAND origins, constant bases, and new outgoing owners.
Current delivery also needs candidate/match/application and fresh/null output
counts. Outgoing “demand” must distinguish uncertainty-layer rows from NORMAL
seed dependencies; the backward count includes both. These can be aggregate
diagnostics in existing loops. Do not retain per-fact histories merely to
measure them.


## 8. Source map

The companion data also contains numbered, hash-bound source excerpts and
observer controls. These are the principal current-code anchors:

| Mechanism | Source |
|---|---|
| Sink seeds, same-owner handoff and backward ZERO entry-only rows | [HandOff.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/HandOff.kt#L88), lines 88–119 and 143–153 |
| Backward ZERO bypass of local restriction | [RunMethodAnalyzer.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/RunMethodAnalyzer.kt#L802), lines 802–804 |
| NORMAL backward ZERO selected for demand | [Demand.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Demand.kt#L90), lines 90–96 |
| Copy actions become alias assignments | [JIRLocalAliasAnalysis.kt](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/JIRLocalAliasAnalysis.kt#L75), lines 75–86 |
| Serialized taint-only flag and resolved copy actions | [SerializedRule.kt](../../core/opentaint-configuration-rules/configuration-rules-jvm/src/main/kotlin/org/opentaint/dataflow/configuration/jvm/serialized/SerializedRule.kt#L75), line 75; [MethodTaintConfigurationResolver.kt](../../core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/rules/MethodTaintConfigurationResolver.kt#L230), lines 230–231 and 625 |
| Reversal removes type filters | [StatementSummary.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/interp/StatementSummary.kt#L59), lines 59–68 |
| Incompatible exact constraints and context creation | [JIRCallResolver.kt](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/JIRCallResolver.kt#L227), lines 227–244, 264–266 and 346–374 |
| Summary-base admission includes constants | [JIRInterpreter.kt](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRInterpreter.kt#L64), lines 64–65 |
| Statement preservation versus strict stage application | [FormApplier.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/interp/FormApplier.kt#L47), lines 47–72 |
| Call bindings and backward stage construction | [JIRCallPlanBuilder.kt](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRCallPlanBuilder.kt#L119), lines 119–138 and 179–204 |
| ZERO direct delivery and call resumption | [RunMethodCallServices.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/RunMethodCallServices.kt#L385), lines 385–392 and 529–537 |
