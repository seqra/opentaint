# Static demand closure and run-1 exit routing

Date: 27 October 2026. Status: **selected design; implementation unchanged**.
Use [proof-guide.md](proof-guide.md) and the
[restricted-run fact design](../docs/design/bidirectional-restricted-fact-management-20261027.md).
This specification selects demand completion, rather than general StrongQueries.

The referenced runtime core is `57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`.
The latest referenced Thingsboard campaign reached **run-2**, completed
**run-1**, and accepted **run-1**. No project was rerun for this design.

## 1. Selected changes

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
- Ordinary restricted-run AP emission, shared FLOW starts, C5 restriction,
  record application, sink seeds, source hits and backward ZERO return.
- Run-2 backward FULL limit 1, then run-3 forward FULL limit 2 and the
  existing increasing-limit policy. No limit zero.
- IR storage, references and cache management.

All newly completed relations are **guidance only**. They are not executable
run-1 summaries, normal records, new group supplies or confirmed flows.
Run-2 must derive every answer with its real body, call bindings and rules.

## 2. Endpoints and relation kinds

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

W and R use the already propagated run-1 relations, including their actual
caller bindings. B is retained without live caller propagation. Do not copy
a callee's argument/return names into a caller during handoff.

Collect W/R through the existing outgoing demand selection. Under the
unchanged run-1 static layer policy these relations are DEMAND. A genuinely
NORMAL singleton remains record-only; it is not a new ordinary demand seed.
O contains selected guidance, not every raw NORMAL summary. Completion does
not change ordinary record selection.

The prescan graph already resolves calls. Keep a detached immutable adjacency
view through the run-1 handoff. Its current export is method-level; static
relations can use the accepted method/context approximation. W/R endpoints
remain owned by their complete MethodKey. Only B travels up the graph.

Detach the method IDs and adjacency at prescan completion, before the current
catalog-coverage release clears that information. Freeze the seed inventory
at the later run-1 barrier. Do not retain the prescan runner or its mutable
method catalog to recover adjacency at that barrier.

Call-order and context approximation remain conservative run-1 guidance.
Two sibling callees can contribute composable static relations to a caller.
This does not assert that their operations execute in that order. Run-2
checks real order and body reachability.

## 3. Run-1 static conclusions go through NormalExit

### 3.1 Target and ingress

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

### 3.2 Preserve producer effects at the producer

Moving summary insertion must not delay or remove a real write's global
visibility. A static value can be consumed before the method's exit rules.

```java
C.f = sourceT();
sinkT(C.f);
// An exit cleaner can remove T later.
```

The write must supply T before the exit cleaner handles its outgoing
summary candidate. Otherwise the earlier sink can lose its run-1 candidate.

```kotlin
fun onLocalStaticWrite(at: OperationInput, value: Facts) {
    val bounded = existingRun1BoundAndChecks(at.premise, value) ?: return
    staticEffects.localWrite(at, bounded)       // presence and FLOW writer
    staticEffects.computedSupply(at.premise, bounded)
    routeBoundedRun1StaticToExit(at.premise, bounded)
}

fun onCallStaticConclusion(original: PremiseKey, value: Facts) {
    val bounded = existingRun1BoundAndChecks(original, value) ?: return
    staticEffects.computedSupply(original, bounded)
    // No localWrite registration for a summary application.
    routeBoundedRun1StaticToExit(original, bounded)
}
```

Reuse the current conditional-input joins and idempotent global supply
admission. Do not register answered non-FLOW writes as future FLOW writers.
Post-exit generated values still use their existing computed-supply path.
Duplicate supply offers must not create duplicate reached memberships.

The shortcut replaces only the producer paths which currently insert or
promote a static summary. Do not revive passive unchanged static copies
discarded by the current read/operation path.

### 3.3 Common exit processing

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

Capture B **after exit rules**, before its old erasure point. A complete kill
emits no method relation. A rewrite emits its actual post-rule relation.
Keep the producer's global write effect distinct from this outgoing relation.

## 4. Stores needed for completion

| Store | Contents and lifetime |
|---|---|
| Existing raw/selected summary stores | W, R and ordinary relations, owned by each run-1 method actor |
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

## 5. Reference closure: the least fixed point

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

Only static/static rows use CALLER. Only a static middle uses composition.
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
fun offer(method: MethodId, edge: GuidanceEdge) {
    if (relations[method].add(edge)) queue.add(method to edge)
}

while (queue.isNotEmpty()) {
    val (method, edge) = queue.removeFirst()
    if (edge.isStaticToStatic) {
        for (caller in callers[method]) offer(caller, edge)
    }
    if (edge.to.isStatic) {
        for (right in outgoing[method, edge.to]) {
            composeThroughStatic(edge, right)?.let { offer(method, it) }
        }
    }
    if (edge.from.isStatic) {
        for (left in incoming[method, edge.from]) {
            composeThroughStatic(left, edge)?.let { offer(method, it) }
        }
    }
}
```

This is the executable concept/oracle. Production need not materialize its
method-by-endpoint-pair matrix.

## 6. Mark and geometry composition

### 6.1 FLOW is diagonal

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

### 6.2 Retain colored round trips

```text
C1/T -> C2/U -> C3/T
  produces a colored T -> T demand relation.
```

It remains present even if a parallel FLOW path has the same outer geometry.
The completion graph does not repeat semantic FLOW subsumption. This keeps
marked cleanup and mark-change dependencies. The normal AP operations in
run-2 set and transport their existing non-subsumable annotations.

### 6.3 Intermediate static positions

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

### 6.4 The shared static carry stays separate

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

## 7. Factored representation of the same closure

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
not import nonstatic names from a callee. Ordinary run-1 binding/propagation
has already supplied the method's W/R rows.

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

## 8. Handoff and strict run-2 execution

```kotlin
fun afterCompleteRun1(result: CompleteRun) {
    joinAllExitRuleWorkAndPublications()
    persistExistingEligibleRawNormalRecords()

    val ordinary = projectExistingSelectedPairs()
    val completion = freezeStaticCompletion(
        staticGuidanceSeeds,
        existingBoundaries = collectWandR(),
        callers = detachedPrescanGraph,
    )
    val demand = ordinary.withCompletion(completion).withSharedStaticCarry()
    val seeds = existingFullSinkSeedProjection()
    releaseRun1ActorsAndMutableCollectors()
    startBackwardRun2(demand, seeds, records.readOnlyView())
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

## 9. Worked cases

### 9.1 Static copy below a getter

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

The existing wrapper-exit restriction now permits the real backward answer.

### 9.2 Setter and getter in one wrapper

```java
void set(Object p) { C.out = p; }
Object get(Object p) { set(p); return C.out; }
```

```text
get retained rows:   arg(0) -> C.out, C.out -> ret
composition:         arg(0) -> ret
run-2 guide:         ret -> arg(0)
```

There is no new unrestricted nonstatic query rule.

### 9.3 A required colored static bridge

```text
bridge retained seed: C.in/T -> C.out/T  // selected cleaner survivor
get reader:           C.out/FLOW -> ret/FLOW
composition:          C.in/T -> ret/T
run-2 guide:          ret/T -> C.in/T
```

The completed T guide starts the marked route. The parallel FLOW route
does not replace it. The ordinary selected cleaner and its actual T result
decide the backward answer.

### 9.4 Exit processing

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

## 10. Termination, cost and safety properties

The endpoint universe is finite for a completed bounded run-1. Composition
does not invent paths, marks, methods or endpoint bases. A relation key has
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

## 11. Proofs and integration limits

The [constructive model](lean/proposals/restricted-demand/StaticClosure.lean)
provides:

- A least inference closure with seed, direct-caller import and static-middle
  composition constructors.
- Executable conversions in both directions between that eager closure and
  factored seed paths. The core equivalence requires no classical axioms.
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

All 18 audited declarations pass with only `propext` and `Quot.sound`; the
core factor/expand equivalence and least-closure theorem need neither.
There is no new axiom, classical choice or unproved placeholder.

The finite oracle compares eager and factored results in 91 cases, including
80 deterministic random graphs. Three generic exit-pipeline controls also
pass. These are design controls, not a
production implementation or a new project result.

The [oracle source](lean/proposals/restricted-demand/closure_oracle.py) and
[complete receipt](lean/proposals/restricted-demand/static-closure-checks.json)
are kept in this repository. The receipt includes every graph case, the
Lean audit output, source hashes and the exact validation scope.

Before implementation acceptance, prove or test the following adapters:

1. Every post-exit B row reaches the private seed store; none reaches live
   publication or executable NORMAL persistence.
2. W/R collection preserves complete MethodKey endpoints and already applied
   call bindings. Caller static visibility covers every resolved target.
3. Complete AP slot/tail matching and FULL/GROUP mark projection refine the
   compatibility abstraction without dropping a required witness.
4. Colored closure rows are never lost under FLOW normalization. Actual
   facts retain the existing protection and equality rules.
5. New exit arrivals and late boundary mark answers stay counted until their
   exit rules, summaries, writer effects and notifications complete.
6. Ordinary C2 emission and C5 publication accept the newly completed pairs.
   Keep the baseline ZERO, ND, seeds, exclusions and native-record tests.
7. A finite required static dependency can be decomposed into the retained
   W/B/R path. Construct its completion witness, then replay its ordinary
   run-2 steps. Do not assume the missing pair was present initially.

This is not a whole-JVM soundness or termination theorem. Unsupported
frontend geometry or a missing producer must be resolved explicitly,
rather than adding a new general permission fallback.

## 12. Implementation sequence

1. Add the NormalExit routing regression controls. Reuse the existing
   boundary, point admission, exit-rule handler and common summary emission.
2. Extract producer effects from early summary insertion. Preserve immediate
   static supplies and write registrations; add the post-exit B seed store.
3. Freeze the detached call graph and W/R/B seed inventory after complete
   run-1. Implement the eager concept as a small-test oracle.
4. Implement the equivalent frozen graph demand view. Match `near` and
   `covering` against the oracle, including marks, class markers and cycles.
5. Restore original restricted-run emission and C5 publication. Remove the
   broad query permission set/backfill and ANY-to-EXACT completion.
6. Keep the shared static carry as a demand family. Exercise the getter,
   setter, colored bridge, strong-kill and exit-rule cases end to end.
7. Run the required common/JVM/driver checks and configured OWASP/project
   campaign. Inspect run-1 exit-rule workload, handoff graph memory and
   run-2 concrete/FLOW queries. No unrelated core refactor is included.
