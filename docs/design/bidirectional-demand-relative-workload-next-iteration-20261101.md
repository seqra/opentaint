# Next iteration: avoid unrelated demand search and repeated call continuations

Date: 1 November 2026. Status: proposal for selection. No runtime change in
this document is implemented. Use ASD-STE100 Simplified Technical English.

Base runtime: `86ad3b70b5b834d60bc0fe96a91091174265c827`; analyzer bytes
are those of `0ffa5ed8b42dbe193973b4fb4701af28b35716b3`.
Read the [completed measurements](../reports/bidirectional-demand-relative-summary-restriction-performance-20261101.md),
[campaign data](../reports/data/bidirectional-demand-relative-campaign-20261101.json),
and [implementation guide](../../spec/impl-proposal-guide.md).

Latest reached / completed / accepted iterations:

| Project | Iterations | Main remaining cost |
|---|---|---|
| OWASP | run-5 / run-5 / run-5 | run-1 engine is 64.342 s |
| Conductor | run-6 / run-5 / run-5 | Calls and saved-summary replay |
| Thingsboard | run-2 / run-1 / run-1 | Terminal-origin search; also run-1 joined writer binding |
| Stirling-PDF | run-8 / run-7 / run-7 | Calls over large backward body relations |

## 1. Rank, expected impact, and semantic scope

| Rank | Candidate | Work removed | Evidence and limit |
|---|---|---|---|
| 1 | Select terminal origins before static graph search | Origins that cannot select the raw result; repeated searches of an immutable seed; nonzero origin enumeration for Reach | Thingsboard run-2: 96.51% C5 samples; 1.491 billion graph joins; 99.70% exact DATA row rejection |
| 2 | Merge equal call-stage results before their shared suffix | Repeated suffix execution within one materialized stage result batch | Production reverse-alias control: 64 equal x continuations become one; project duplicate ratio is not measured |
| 3, conditional | Share exact equal joined writer inputs across call sites | Repeated guide-only AP application for the same writer and equal complete actual input | Thingsboard joined binding: 220.565 s and 222.461 million candidate visits; useful quotient cardinality is not measured |

This rank is by expected avoidable workload, not a measured speedup.
Only candidate 1 has direct evidence for almost the whole slow phase.
Candidate 2 can remove a width-times-suffix family, but cannot remove
distinct path work or separate replay invocations. Candidate 3 must pass
its cardinality gate before implementation. No two-fold project speedup
is proved or promised.

The intended semantic change for all three candidates is **none**.
For a completed analysis, preserve admitted Facts/protection, complete
originals, source and rule identities, summaries, demands, Targets and
reports. Work counters and batch-dependent diagnostic callback counts can
change. Timing can let a formerly incomplete run finish.

Keep these mechanisms unchanged:

```text
C2 initial emission and its layers
exact paired C5, then each row's Dp-relative cut
the global body field limit and field transfer
cleaners, field E, raw FLOW mark exclusions mx, protection
complete ND originals, source permissions and typed Target rules
saved replay on every offer, before current demand selection
run-1 direct static write supply and normal-exit summary processing
static completion only at run-1 -> run-2; later demand lookup is local
post-S result storage and CFG delivery cache
```

Do not restore unrestricted summary storage to avoid repeated C5 work.
Do not add input history, grounding support, new field validation, or a
new NORMAL/DEMAND conversion. Do not discard protected TAINT paths.
Local loop widening or previous-point guidance would be major semantic
changes. They are outside this proposal. A proof that requires them must
be reported as a new behavior question.

## 2. Shared terms

```text
Z = ZERO; DT = anonymous DemandTarget; NT = NormalTarget(id)
P -> Q = method relation under its complete original P
W = primitive or caller-bound writer: nonstatic/Z -> static
B = visible static -> static primitive
terminal input = static pattern whose method-local relation reaches DT
Pattern = complete base, field path, tail, field exclusions and mark
MethodKey = complete method/context key, not CommonMethod alone
```

FULL mode uses exact full mark labels. FLOW carries the current label.
A mapped bridge can change a label, for example `C.a/U -> C.b/T`.
Use the existing `staticAnchor`, overlap and mark-composition laws at
every join. A generic string-prefix or unlabeled graph is insufficient.

## 3. Select terminal origins before graph search

### 3.1 Current path

```kotlin
// DemandStore.intersect(method, original, raw), simplified.
visitControlPairs(includeDerived = original.isZero) { pair ->
    when (pair.exit) {
        Zero -> if (raw is Reach) offer(raw)
        is Data -> if (raw !is Reach) exactC5ThenRowLimit(raw, pair)
    }
}

// Derived contribution inside visitControlPairs:
for (origin in walkTargetOrigins(method, localThenVisible)) {
    offer(PairedDemand(Target, origin.asExit()))
}
```

`walkTargetOrigins` starts from every terminal input, walks static
predecessors, and then calls the raw-output test. Its visited set belongs
to one traversal. The next ZERO-origin summary can repeat the graph.

In Thingsboard run-2, 94.49% of Java samples are in this traversal below
`retainSummary`, outside `acceptsTarget`. The outer stack combines
ZERO-to-TAINT DATA and ZERO-to-Reach callers. Optimizing only
`acceptsTarget` or only DATA would leave a major possible workload lane.

K6 prohibits a FLOW result under ZERO. Thus the derived ZERO DATA lane
has TAINT results. The first implementation can optimize FULL mode and
retain the current reference path for GROUP mode, ordinary AP rows and
nonzero originals. This is an exact-query replacement, not a mark-policy
change or an expansion of GROUP mode support.

### 3.2 New path and origin indexes

Keep explicit control rows unchanged and consume them first. Replace
only their derived terminal contribution:

```kotlin
fun visitDerivedForZero(method: MethodKey, raw: Facts, policy, offer) {
    when (raw) {
        is Reach -> {
            if (hasZeroOriginToTerminal(method)) offer(raw) // same layer
        }
        is TaintTree -> visitSelectedDataOrigins(method, raw, policy, offer)
        is FlowTree -> error("ZERO cannot own FLOW")
    }
}

fun visitSelectedDataOrigins(method, raw, policy, offer) {
    // Packed selection: no full catalog or scalar-mark enumeration.
    for (candidate in originIndex.possibleOrigins(method, raw)) {
        val pair = PairedDemand(Target, Data(candidate.origin))
        val selected = exactC5(ZERO, raw, pair, policy)
        if (selected.isEmpty()) continue
        if (!reachesTerminal(method, candidate.seed, candidate.view)) continue
        relativeLimitAndOffer(selected, pair.exit, policy, offer)
    }
}
```

Build indexes over primitive input endpoints and existing local writer
inputs. Do not build the transitive origin relation. Select by raw base,
path/anchor and input label before graph expansion. Indexes may select
extra candidates; exact C5 still rejects them.

| Raw output | Complete candidate origin | Forward seed |
|---|---|---|
| Nonstatic T | Matching local W input | W output after its label relation |
| Named static field T | Matching B input or direct terminal input | Selected B output, or that direct input |
| EXACT class marker T | Matching input in that exact anchor | Corresponding exact static marker state |
| Reach | ZERO-input W of this full MethodKey | That W output |

A static origin can be relevant with no local W. Do not require a writer
for the bridge-only case. Include the empty B path and direct terminal
inputs. Several seeds can represent the same origin; a failed first seed
cannot reject its other seeds. One successful seed proves that origin.

Deduplicate complete successful origin rows before repeating C5 where
useful. Every successful DATA origin must still contribute its own
selection and budget. A precise NORMAL output from one row cannot stop
a shorter DEMAND output from another row.

### 3.3 Reach needs only a ZERO origin

```kotlin
fun hasZeroOriginToTerminal(method): Boolean {
    val writers = completion.localZeroWriters(method)
    if (writers.isEmpty()) return false // zero B expansions
    for (view in existingLocalThenVisibleViews(method)) {
        for (writer in writers) {
            if (reachesTerminal(method, writer.to, view)) return true
        }
    }
    return false
}
```

All terminal seeds and all B endpoints are static. A reversed path can
first reach ZERO only through a local ZERO-input W. Therefore no such
W means no **derived** ZERO origin. It does not reject the whole query:
an explicit `(Target,ZERO)` or `(ZERO,ZERO)` row remains sufficient.
Nonzero derived origins can never select a raw Reach result. Do not
construct them for this query.

### 3.4 Selected forward search and completed-answer reuse

```kotlin
data class SeedKey(
    val method: MethodKey,
    val view: ViewKind, // LOCAL or VISIBLE
    val staticPattern: Pattern, // full geometry, E, tail, exact mark
)

// The frozen completion snapshot owns this thread-safe memo.
fun reachesTerminal(method, seed, view): Boolean {
    val key = SeedKey(method, view, seed)
    completedAnswers[key]?.let { return it }
    val pending = ArrayDeque<State>()
    val seen = HashSet<State>()
    pending.add(seed)
    seen.add(seed)
    while (pending.isNotEmpty()) {
        checkpoint()
        val state = pending.removeFirst()
        if (terminalIndex.matches(method, state)) {
            completedAnswers.putIfAbsent(key, true)
            return true
        }
        for (b in selectedOutgoingB(view, state)) {
            val next = existingForwardJoin(state, b) ?: continue
            if (seen.add(next)) pending.addLast(next)
        }
    }
    completedAnswers.putIfAbsent(key, false)
    return false
}
```

The existing outgoing-B API is FLOW-only. Extend selected lookup to
mapped FULL labels; do not use an all-label scan. A `U -> T` bridge must
reach a T terminal when the raw input mark is U. Filtering terminal
readers by raw U before following the bridge would be unsound.

The snapshot identity is an implicit memo-key field. Keep full MethodKey,
LOCAL/VISIBLE policy and full seed Pattern. Different contexts, labels,
field E or visibility can give different answers. Keep outside-call-graph
owner handling. Do not share this cache with run-3 or another AP namespace.

Publish false only after a complete finite search. Cancellation or a
gray cycle node cannot supply a negative cache entry. An early true
search proves its seed and explicit witness path; it does not prove all
visited states true. Duplicate concurrent searches are acceptable;
partially published answers are not.

Store booleans, not all composed paths or historical Facts. C5 and the
per-origin cut still run for the current candidate. Cached graph answers
must not mix one origin's mark permission with another origin's budget.

### 3.5 Code, facts, and old/new work

```java
void use(Box p) {
    C.a = p;              // W: p.* -> C.a.* / FLOW
    C.b = C.a;            // B: C.a.* -> C.b.* / FLOW
    sinkT(C.b);           // terminal input C.b/T
}
```

```text
Provided run-2 candidate       Current work             New work
Z -> q.$/U                    walk b -> a -> p, reject  no matching origin, no walk
Z -> p.$/T                    walk b -> a -> p, select  select p/T; search a/T -> b/T
Z -> C.a.$/T                  walk b -> a, select       select a/T; search b/T
Z -> Reach, no ZERO W         walk nonzero origins      no B expansions
repeat same a/T seed          repeat traversal          reuse completed boolean
```

The Reach row is rejected only in the derived lane. Existing explicit
ZERO permission still applies. NT stays in its normal-only forward lane
and is ignored backward as specified.

Mark-change control:

```java
void changed() {
    C.a = sourceU();
    C.b = convertUToT(C.a); // CM(arg,U) assigns T to ret
    sinkT(C.b);
}
// W: Z -> C.a/U; B: C.a/U -> C.b/T; terminal C.b/T.
// Both C.a/U DATA relevance and ZERO Reach permission must survive.
```

### 3.6 Proof and test gates

No completed kernel proof of this replacement is claimed yet. Before
runtime edits, add a constructive Lean model with executable finite
endpoints, complete geometry labels, mapped marks, owner views and rows.
Prove these properties, then test the production adapter:

1. The old reverse traversal and selected forward search have the same
   complete origin-to-terminal witnesses under the existing AP join law.
   Include cycles, empty paths, mapped labels and EXACT class markers.
2. Every selectable old DATA origin is in the new index: direct terminal,
   B input or local W input. Over-selection may cost work, not lose rows.
3. A derived ZERO origin exists exactly when a local ZERO W reaches a
   terminal through B*. With no such W, Reach needs no B traversal.
4. All successful complete rows yield the same exact-C5 then relative-cut
   Facts/protection union. Preserve N+D results and complete ND originals.
5. Full-key attachments and LOCAL/VISIBLE owner policies are equivalent.
6. Completed memo answers are query-independent under the stated key;
   cancellation and concurrent lookups cannot create false permission.

Production differential tests must compare full old/new output sets for
packed marks, field E, arrays, two contexts of one CommonMethod, unequal
origin budgets, explicit ZERO controls, bridge-only origins and U-to-T
paths. A large nonzero-only bridge component with no ZERO W must perform
**zero B expansions** for Reach. The old reference traversal stays in
tests, not as an all-candidate production fallback.

Old work can approach `Q * (origin states + predecessor joins)`. The new
query pays indexed selection per offer and a search per distinct seed,
with the Reach no-writer case constant after indexed local lookup.
A huge first seed can still be expensive. Measure it before proposing
shared SCC/reverse reachability for a fixed terminal set.

## 4. Merge equal call-stage results before the shared suffix

### 4.1 Boundary and key

`RunMethodCallServices.PlanFacts` already merges equal ordinary results
and ORs protection in some run-1 cleaner paths. Other stage outputs and
later-run cleaner outputs use lists. Reuse that merger at existing
materialized result boundaries:

```text
applyStage output -> next frame
one cleaner READ -> CLEAN; one cleaner step -> next step
one applyParts/applyRecord result batch -> resumeCallees
one resumed cleaner result batch -> flow
```

Execute every producer operation and its effects first. Merge only its
returned continuation values. Keep frame/branch order, cleaner order,
stage cursors and invocation boundaries.

```kotlin
data class PlanFact(
    val premise: PremiseKey, // complete original, including ND
    val facts: Facts,       // exact ordinary payload and layer
    val identityCandidate: Boolean?,
)

fun applyStage(...): List<PlanFact> {
    val out = PlanFacts(ap) // singleton fast path; map only after growth
    for (input in existingOrderedInputs) {
        executeExistingStageAndItsEffects(input) { result -> out.add(result) }
    }
    return out.toList()
}
```

The actor/run, call site, directed stage or cleaner phase, caller layer
and pending demotion are fixed by the surrounding collection. If a
collector holds multiple scopes, put those fields in its key explicitly.
Never share a collector across such boundaries.

Facts equality deliberately omits `nonSubsumable` protection. Equal
ordinary keys must merge protection by OR. `distinct()` or a plain
Facts HashSet can lose it. Keep different marks, trees, E, mx, tails,
layers, originals and null/true/false identity states separate.

### 4.2 Code and traced work

```java
void root(Node x, Holder h) {
    h.f0 = x; h.f1 = x; // ... h.f2 through h.f62 ...
    h.f63 = x;
    touch(x);
    sinkT(h);
}
Node touch(Node x) { return x; }
```

The snippet illustrates an alias family. The production reduced control
supplies its 64 alias micro-edges directly; it does not assert that every
Java alias resolver produces all 64 for this source.

```text
Forward aliases at touch: x.* -> h.f0.* ... x.* -> h.f63.*, FLOW.
Backward input: original A -> h.[any]/T, DEMAND.
Each reverse alias returns the same A -> x.[any]/T, DEMAND.

Current: 64 producers -> 64 equal x values -> 64 suffixes -> one fresh x.
New:     64 producers -> one protected-union x -> one suffix -> same x.
Separate h pass-through remains: total finishes 65 -> 2, stored rows 2 -> 2.
```

Preserve all producer source/action occurrences, static operations,
requests, rule/ND bindings, seed permissions, cut callbacks and Target
identities. Equal DATA values do not permit dropping distinct source
occurrences. Repeated semantic observations in a suffix must be proved
idempotent under the same scope. Diagnostic callback counts can vary
within the already selected observation contract.

### 4.3 Limits and proof state

Two reversed saved record views currently invoke two separate suffixes.
This local merger does **not** combine them. Saved replay on each new
offer also remains. Cross-callback batching would change interleaving
with mutable stores and needs another explicit scope/effect-order proof.
Do not introduce it as a collection helper.

The constructive [local proof dossier](../../spec/call-stage-result-merging-analysis-proofs.md)
and [receipt](../../spec/lean/proposals/call-stage-result-merging-analysis-20261101/checks.json)
pass 44 theorems and 76 audited declarations, with only `propext`.
They prove finite ordinary/protected observation preservation, complete
key separation, and the executable 64-to-1 control with its separate
identity branch. Their suffix theorem requires a deterministic suffix
that preserves protection OR. They do not prove that every Kotlin
stateful hook satisfies that requirement, arbitrary packed multi-mark
refinement, whole-driver scheduling or project speedup.

Before implementation, prove/test runtime key correspondence, producer
effect placement, and the suffix OR/idempotence laws for every selected
boundary. Include incomparable and late protection, complete ND originals,
source occurrences, both directions, both mark modes, synchronous delivery,
cleaner phases, native must-demotion lanes and NormalTarget restrictions.

For b equal results and suffix length/cost k, continuation work changes
from b*k to k; total work still includes b producers and collection cost.
If all outputs differ, this candidate removes no suffix work. Measure
raw output offers, distinct exact keys, protection upgrades, suffix counts,
CALL cuts, fresh post-S deltas and collector allocation by stage.

## 5. Share exact joined writer inputs across call sites

This candidate applies only after all runners join, while their complete
input directories are sealed. It does not change live call handling.
Keep primitive and lost W rows and recursive caller binding: they carry
caller-original-to-static guidance even when exit processing kills the
live static result. Global pool supply does not replace that dependency.

```java
void set(Object p) { C.f = p; }
void wrapper(Object x) {
    set(x); // A
    set(x); // B, assume x and all annotations unchanged
}
// Both inputs bind the same p.* -> C.f.* FLOW writer to
// wrapper: x.* -> C.f.*. Current call/stage keys keep both applications.
```

Within one fixed `(owner MethodKey, raw writer ID)`, quotient only exact
equal guide inputs:

```kotlin
data class GuideInputKey(
    val caller: MethodKey,
    val wholeOriginal: InitialAp,
    val callerLayer: Layer,
    val linkLayer: Layer,
    val zeroOnly: Boolean,
    val actual: ExactFactsKey,
)
// ExactFactsKey retains full tree, base, tail, layer, E, raw mx,
// complete marks, and the complete protection mask.

for (input in borrowedSealedCandidates(writer)) {
    checkpoint()
    checkExistingDomainGuards(input, writer)
    if (!seen.add(exactGuideKey(input))) continue
    existingMatchApplyCoverLimitAttachAndRecursiveOffer(input, writer)
}
```

Release `seen` after this writer. The key removes call instruction and
stage ordinal only. Existing AP match and guide attachment in this phase
do not consume them. `GroupKey` omits the full trie and Facts equality
omits protection; neither is this key.

This first step still visits all borrowed callbacks. Avoiding the
222 million visits would require a sealed-directory quotient index,
whose build time and retained bytes need separate measurement.
Do not claim candidate-callback savings from per-writer AP dedup alone.

Prove sealed-input immutability, one-step congruence of this exact key,
and equal least recursive-W closure by constructive finite worklist
models. Preserve ZERO-only ports, complete contexts, whole originals,
raw annotations, static-origin B admission, and cancellation. Composed
B paths must never re-enter the W binding queue.

Do not add a global FLOW geometry cache in this first change. In
particular, demand export erases raw mx, but recursive raw W application
still needs it:

```java
void w(Object p) { C.f = p; }
void a(Object x) { removeT(x); w(x); }
void root() { a(sourceT()); sinkT(C.f); }
// Actual input at w: p.*/FLOW excluding T.
// Raw bound W: x.*/FLOW -> C.f.*/FLOW excluding T.
// Reusing an mx-erased guide as this raw W incorrectly accepts outer T.
```

If a later cache shares pure FLOW geometry, prove commutation with mx
erasure and restore `actual.mx UNION rawWriter.mx` **before** recursive
offer. TAINT-to-FLOW, mapped marks, GROUP and ZERO need their own laws.
This optional deeper cache is not included in candidate 3.

The selection gate is a measured useful difference between old full
InputKey cardinality and safe GuideInputKey cardinality. Compare AP
applications avoided with set/index construction and peak memory. If
most safe keys differ, reject this candidate instead of adding a cache
which cannot remove substantial work.

## 6. Delivery plan and acceptance

1. Select candidates explicitly. Complete the missing Lean query/adapter
   proofs before runtime edits; do not treat this proposal as a completed
   implementation spec for unproved boundaries.
2. Add production differential tests first. Preserve the old scalar
   traversal and duplicate-list behavior as finite test references.
3. Implement one candidate at a time. Commit and record its source hashes.
   Use optional numeric counters and bounded copied samples; do not retain
   new raw Facts merely to profile them.
4. Run the required common/JVM regressions and the fixed FULL/16 GiB
   four-project configuration. Reuse the legacy baseline. Do not rerun
   an alternate configuration without a selected experiment.
5. Report latest reached/completed/accepted iteration, findings, engine
   and handoff times separately. Compare complete semantic identity sets,
   not only total report counts. Keep existing baseline gaps visible.

Additional counters for candidate 1:

```text
ZERO-origin DATA versus Reach offers
Reach queries with/without local ZERO W; B expansions in each lane
indexed DATA origins, exact-C5 passes, successful distinct origin rows
distinct complete seed keys, completed memo hits/misses and retained bytes
states/joins for first seed versus repeat seed, LOCAL versus VISIBLE
```

Candidate 2 needs per-stage offer/key/suffix ratios and evidence for the
specific hot controller/ParametersUtils paths, not only the 64-alias
control. Separate current batches, saved callbacks and separate offers.
Candidate 3 needs both full and quotient key counts per writer and the
time/allocation of its index. A broad cache hit counter is insufficient.

After implementation, repeat the body-versus-admitted shape analysis:
max-depth distributions, fields/marks/bases, protected membership,
raw summary offers, admitted summaries, native replay and fresh post-S
work. Identify whether residual cost is first-time graph search, equal
continuations, genuinely different local paths, inter-method products or
another family. A smaller C5 frontier alone is not proof that body or
inter-method explosion is solved.

The 60-second run-1 target remains. Candidate 1 primarily helps run-2;
candidate 3 primarily helps the run-1 handoff. Neither alone is a design
for Thingsboard's 393-second run-1 engine. Do not combine their savings
with the engine target or claim that all projects will finish.
