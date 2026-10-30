# Next iteration: remove measured redundant work and storage

Date: 30 October 2026. Base analyzer:
`c98d12582a138d5898e94908ee6690dda73998ca`.
Status: the selected changes are implemented at
`edb2e06cdb17eecafbe03415236bf56c57910239`.
See the [closed campaign report](../reports/bidirectional-identity-owner-protection-performance-20261030.md)
and the [new next proposal](bidirectional-input-admission-delivery-next-iteration-20261030.md).
The base measurements below are historical.
The detailed [implementation proposal](bidirectional-identity-owner-protection-implementation-20261030.md)
contains the APIs, source changes, checked formal models and test gates.

Use the [current performance report](../reports/bidirectional-demand-stop-static-labels-cfg-delivery-performance-20261030.md).
The latest reached / complete / accepted iterations are OWASP **run-5 / run-5 /
run-5**, conductor **run-6 / run-5 / run-5**, thingsboard **run-2 / run-1 /
run-1**, and Stirling-PDF **run-6 / run-5 / run-5**.

The previous proposal is implemented and measured. Do not carry forward its
old hotspot estimates as if they describe the current analyzer.

## 1. Priority and semantic scope

| Priority | Change | Current evidence | Expected effect |
|---|---|---|---|
| 1 | Store literal identity results as point bits | Thingsboard run-2: 5.92 million identity-only cells; point-store union 3.43 GB | Avoid millions of full result containers; keep the post-S gate |
| 2 | Share static owner visibility on the frozen call graph | Thingsboard run-2: graph reachability 54.88% of Java samples, 630 GB sampled allocation weight | Replace repeated graph searches with a shared finite relation |
| 3 | Avoid protection normalization when inclusion is already proved | Stirling run-6: mask intersection 77.72% of Java samples | Remove redundant whole-mask walks during result admission |

Priority 1 addresses the blocking OOM. It is a representation change. It does
not claim to reduce the number of required relations. Priorities 2 and 3 avoid
repeated computations whose results already follow from immutable data or
local invariants. They do not merely make each traversal a little faster.
The ranking is a decision priority, not a predicted common speedup across
different projects. Measure each change separately before combining results.

**No analyzer semantic change is proposed.** Keep all of these contracts:

```text
completed output belongs to producing statement S
initial/resumed input is not a completed output
no standing destination input-history gate
the same fields, tails, exclusions, marks, layers and protection
the same source/sink, cleaner, alias and static-write observations
the same exact C2 emitter and C5 restriction
the same local W/R MethodKey scope and static owner predicate
the same selected outgoing-demand stop rule and field-limit schedule
```

No rule reduction, field-transfer change, grounding support, IR storage
change, SoftReferenceManager rewrite, or new global strong form cache is part
of this proposal. New cache/index state must not enter semantic equality or
hashing. A detailed implementation spec must prove these boundaries before
runtime changes, as required by [proof-guide.md](../../spec/proof-guide.md).

## 2. Store literal identity results as point bits

### 2.1 Current versus new

Current scalar storage uses a ConclusionGroup at every occupied
`(initial, producing statement)` cell. Even a single unchanged identity owns
maps, lists and fact headers. This is now durable because relevant identity
outputs pass through the post-S gate.

The new storage records a literal identity with the initial, statement index,
layer, and protection state. It reconstructs the value when needed. A point
which needs another conclusion uses the existing full group. This preserves
the selected output gate and removes the repeated payload.

The thingsboard run-2 census finds:

```text
all occupied scalar cells                  7,514,636
strict identity-only cells                 5,923,972  (78.83%)
static identity-only cells                 5,325,214  (70.86% of all cells)
static TAINT identity-only / static cells  5,237,365 / 5,359,538
point-store retained union                 3,431,625,208 bytes
all per-premise statement arrays             129,494,896 bytes
```

Thus changing only the sparse statement arrays is too small a target. The
static identity-only cells alone need at least 809,432,528 bytes for their
ConclusionGroup, two map object headers and BooleanArray, before tables,
lists, fact groups or trees. The future net saving must subtract the new bit
storage and any promotion cost. Do not count shared roots twice.

### 2.2 Exact eligible shape

An eligible identity is the complete literal image of a **single** initial I.
It is not a subtree which happens to contain I. Compare:

```text
base; entire single field path; field tail; field exclusion; mark image
FLOW: mark exclusion is empty
TAINT: one initial mark at one initial position
```

Compare the canonical initial **image**, not raw enum fields. An EXACT
concrete initial has an exact leaf; its TaintTree.anyTail is canonically
ANY_TAINT and does not make that leaf a must-tail leaf.

Keep NORMAL and DEMAND separately. For a valid one-position/one-mark TAINT
identity, protection is either absent or covers that one membership. Record
the protection upgrade separately. Do not use ordinary Facts equality to
ignore protection. Use the full group for a mixed tree, unsupported annotation,
multiple premise, nonidentity result or another unsupported shape.

This is a scalar-store optimization. The current packed run-1 FULL store can
remain unchanged. Do not introduce a new rule about which run may emit facts.

### 2.3 Storage and admission

The following API shows the required behavior, not a required final layout.
Allocate bit sets lazily. The implementation can combine maps with the current
per-premise owner to avoid a second large key directory.

```kotlin
class IdentityPoints {
    val normal: PointBits
    val demand: PointBits
    val protectedNormal: PointBits
    val protectedDemand: PointBits
}

// At producing S, after transfer/rules and existing observation callbacks.
fun add(S, initial, offered): Facts? {
    val full = fullGroupAt(initial, S)
    if (full != null) return full.add(offered)

    val literal = exactIdentityImage(initial, offered)
    if (literal != null) {
        val old = identityState(initial, S, literal.layer)
        // State is ABSENT, PRESENT or PROTECTED. PRESENT is not false/absent.
        val next = old.join(PRESENT(protected = literal.protection))
        if (next == old) return null
        recordIdentity(initial, S, literal.layer, next)
        // A new annotation must propagate as the current T2/T4 contract says.
        return reconstructIdentity(initial, literal.layer, next)
    }

    val group = createFullGroup(initial, S)
    restoreExistingIdentityLayers(group, initial, S)
    clearCompactIdentityAt(initial, S)
    return group.add(offered) // Same old group admission and delta behavior.
}
```

Promotion must restore the exact current identity snapshot, with both layers
and protection. It must not emit restored members as new output. Then the
incoming result uses the existing group semantics. Do not reinsert an arbitrary
history of facts: that can change compaction order. `edgesAt` and pattern
matching must enumerate the reconstructed identity plus full rows exactly once.

### 2.4 Code and fact trace

```java
// Schematic CFG example, not recovered source for the measured method.
void helper() {
    a();  // S1: completed I -> I, where I = S.C.f.*/T, NORMAL.
    b();  // S2: completed I -> I, same full initial and conclusion.
    c();  // S3: completed I -> I, same full initial and conclusion.
}
```

```text
Current:
  groups[I][S1] = full container for I -> I / NORMAL
  groups[I][S2] = another full container for the same value
  groups[I][S3] = another full container for the same value

New:
  identity[I].normal = {S1,S2,S3}
  reconstruct the same I -> I / NORMAL at each stored point

Repeated S2 output:
  current group rejects it; new bit rejects it
Late protected S2 output:
  new protectedNormal bit grows; emit the same protection upgrade
Late S2 output I -> x/T:
  materialize S2's group with its exact old identity, then admit x/T
```

The real heap has a `TbKafkaProducerTemplate.addAnalyticHeaders(List)` context
with 617 static premises, 28 identity positions and 17,104 static identity-only
cells. These are statement indices; the census does not classify all 28 as
calls. This is the measured premise-by-statement product. The proposal keeps
all those point memberships while it avoids most per-cell objects.

### 2.5 Proof and test obligations

Model a scalar point store as a finite map from initial/point to complete
layered conclusions with protection. Define an executable decoder for the
compact representation. Prove:

1. A compact identity decodes to the exact old value, including exclusions,
   mark slot, layer and protection. Unsupported shapes take the full fallback.
2. `decode(addCompact(s,f)) = addOld(decode(s),f)` for state and emitted delta.
   Include no change, fresh ordinary content and protection-only growth.
3. Promotion preserves the complete old snapshot and introduces no observation.
4. Both `edgesAt` APIs return the same values. There is no new input gate and
   no change in the producing point or rule/subscription callback order.
5. Release at actor freeze remains complete. No cache retains initial/fact
   history after the current owner is released.

Compare old and compact scalar stores over generated finite event sequences.
Include both insertion orders, both layers, protection upgrades, exclusions,
EXACT/STAR/ANY_TAINT, promotion to a mixed tree, and later subsumption inside
the materialized group. Run the actual engine CFG tests as well.
Include ANY cases, and assert the full fallback for any unsupported image.

Measure compact points, promoted points, fallback reasons, bytes of bits and
containers, point-store retained union and queue payload. The success target
is a material reduction of the measured identity containers, with unchanged
decoded results. A completed thingsboard run-2 must be measured; it is not
guaranteed by the lower-bound object count.

## 3. Share static owner visibility

### 3.1 Current versus new

Current inherited views allocate a family memo and search the same frozen
call graph. A fresh view can repeat a question answered by an earlier view.
Current thingsboard run-2 records 1,850,835 memo views and 52,148,176 owner
evaluations. The graph-reachability family has 54.88% of Java samples and
630.23 GB sampled allocation weight. Only four views remain live in the heap.
This is mainly repeated computation and allocation, not an owner-cache leak.

Build owner visibility once on the frozen graph. Each view borrows an
immutable row and answers the graph part with one bit test.

### 3.2 Preserve the exact owner meaning

```text
visible(q,F) = q in owners[F].outsideGraph
               OR exists o in owners[F].graphIds: Reach(q,o)
```

Reach follows prescan caller-to-callee edges and includes the zero-length
path. Reuse the existing exact `outsideGraph` set; no new outside-owner
storage is needed.

The LOCAL test remains exact common-method membership. Two different methods
in one recursive component are not the same local owner. Local W/R rows stay
attached to their full MethodKey, including context. Each selected original
label retains its own owner family. Do not merge all owners for a geometry.

### 3.3 Build and query

Use a stack-safe finite SCC algorithm. Collapse each strongly connected
component to one vertex. Retain the existing caller-to-callee direction in
the quotient DAG. Seed the existing family IDs at their existing graph owners.
Propagate family bits from callee components to caller components.

```kotlin
fun buildVisibility(graph, familiesByExistingId): OwnerVisibility {
    val scc = iterativeScc(graph)
    val dag = quotientDag(graph, scc)
    val rows = Array(scc.count) { LongArray(ceilDiv(familiesByExistingId.size, 64)) }
    for (family in familiesByExistingId)
        for (owner in family.graphIds)
            rows[scc.of(owner)].set(family.id)
    for (parent in topologicalOrder(dag).asReversed())
        for (child in dag.children(parent)) rows[parent].or(rows[child])
    return freeze(scc.methodComponents, rows)
}

fun visible(q, family): Boolean {
    cancellation.checkpoint()
    if (q in family.outsideGraph) return true // Existing exact membership.
    val id = graph.id(q) ?: return false
    return visibility.rowFor(id).contains(family.id)
}
```

Build after the last existing family ID is assigned, including projected
entry families. Publish only a complete index. A cancelled build must not
install an empty or partial negative result. The owner is the existing frozen
run-1-to-run-2 snapshot. Run-3 and later still use local-only demand lookup.

Keep the selected lookup pipeline:

```text
spatial candidates -> necessary label ordinals -> existing exact predicate
 -> same row's owner Boolean -> unchanged AP matching/composition
```

### 3.4 Code and fact trace

```java
void A() { wrapper(); }
void wrapper() { reader(); }
void reader() { C.b = C.a; }
// Frozen B: S.C.a.*/T -> S.C.b.*/T [DEMAND], owner reader.
```

For a matching run-2 query at A:

```text
Current view 1: allocate memo; search A -> wrapper -> reader; true.
Current view 2: allocate another memo; repeat the same search; true.

New build: seed reader's family bit; OR it into wrapper, then A.
New views 1 and 2: read A's same family bit; true.
```

Both paths return the same complete demand row. No fact is propagated along
this graph by the index. A U row owned by an unreachable method remains
invisible even if its geometry equals the T row. A query absent from the
graph can succeed only through its existing exact outside-owner membership.

### 3.5 Bounds and obligations

Let C be component count, Ec quotient edges, F family count and W=ceil(F/64).
After SCC construction, the build costs `O((C+Ec)*W + owner memberships)` and
retains `C*W` words. A graph-family query is constant work. Current counts
before SCC reduction give a word-padded upper bound of **106,815,368 bytes**
for the main bit rows: 51,953 methods, 16,414 families, 257 words per row.
Array headers, SCC/DAG data and references are additional. This adds a shared
retained index while it removes temporary searches. Do not subtract cumulative
30.38 GB memo capacity from retained heap as a claimed saving.

The formal model must construct path witnesses. Prove SCC internal mutual
reachability, original/quotient path correspondence, seed meaning and reverse
topological closure. A set bit must yield a path to an existing family owner;
an existing finite path must set the bit. Include length-zero paths. Substitute
the equal Boolean into the unchanged C2/C5 pipeline to prove equal results.
Preserve the distinct local and outside-owner cases.

Test chains, diamonds, recursion, disconnected owners, empty families, outside
methods, two labels with different owners in one geometry, projected entry
families, and different contexts of one common method. Compare the Boolean
to independent finite BFS, then compare complete C2/C5 outputs.

Measure build time, SCC/DAG size, actual retained index bytes, graph searches
removed, query count, allocation and run-2 completion. The 55% Java region is
an opportunity bound, not a promised 55% wall-time reduction or OOM fix.
Remove unused per-view memo/status/reachability scratch after all its callers
use the shared relation. Keep graph IDs, own-row indexes and local scope.

## 4. Avoid protection normalization after proved admission operations

### 4.1 Current versus new

Stirling's latest run-6 has 80,076 of 103,030 Java samples in
`intersectTaintMask`: **77.72%**. Its allocation weight is 2.468 TB out of
3.906 TB. Exact parent stacks lead to TaintGroup.add through `withRoot` and
`withProtection`. This is different from conductor's hot unprotected wrapper.
`NodePair` already uses identity equality; do not propose to fix it by changing
structural equality.

Current store admission can normalize an old mask against a new root, discard
that intermediate mask, then normalize a newly merged mask against the same
root. In the following cases, inclusion is already a mathematical consequence
of the operation. Construct the same final annotated result once.

### 4.2 Union case

Let ordinary membership sets be A and B, with protection P⊆A and Q⊆B.
Here membership is the exact coordinate `(field path, EXACT-or-ANY leaf kind,
full mark)`. It is not AP overlap, prefix coverage or ANY descendant coverage.
The mask intersection matches those exact coordinates.

```text
R = A union B
M = P union Q
M is a subset of R
```

```kotlin
// Current TaintGroup.add.
stored.withRoot(intern(R)) // Walk P intersect R.
      .withProtection(M)  // Discard that mask; walk M intersect R.

// Proposed private admission helper, after proving M subset R.
makeAdmissionResult(base, layer, intern(R), exclusion, tail, includedMask = M)
```

Preserve manager ownership and the existing exclusion/tail canonicalization.
The helper must be private to proved admission paths. It must not turn the
public `withRoot`, field transfers or cleaners into unchecked operations.

### 4.3 Delta and subtraction cases

Current admission explicitly builds a delta root which includes the protection
upgrade. The upgrade is therefore already a subset of that delta root.
Subtraction similarly builds its emitted root as the union of remaining
ordinary members and remaining protected members.

```kotlin
// This is TaintGroup's remainder mask, not a generic merged mask.
val deltaMask = rest.nonSubsumable
val deltaRoot = merge(ordinaryDelta, deltaMask) ?: return null
return makeAdmissionResult(/* same header */, deltaRoot, deltaMask)

val keptProtection = subtractProtectedCovered(input.protection)
val keptRoot = merge(subtractOrdinaryCovered(input.root), keptProtection) ?: return null
return makeAdmissionResult(/* same canonical header */, keptRoot, keptProtection)
```

Do not use the input's whole mask after subtraction. Keep exactly the current
`protectedOnly` coverage rule. Cases outside a proved inclusion keep the old
intersection. Interning changes node identity but preserves ordinary membership;
it must preserve the same inclusion witness.

### 4.4 Code and facts

```java
// seedT/seedU/seedV: unconditional sources at arg0.
// copyT(a,b): CM(arg0,T) -> AssignMark(arg1,T).
// copyU(a,b): CM(arg0,U) -> AssignMark(arg1,U).
Box build() {
    Box p = new Box();
    seedT(p.left);
    seedU(p.right);
    Box x = new Box();
    seedV(x.shared);
    copyT(p.left, x.left);   // T-triggered assignment protects x.left/T.
    copyU(p.right, x.right); // U-triggered assignment protects x.right/U.
    return x;
}
```

This illustrates legal protected results, not a recovered Stirling source
trace. Consider one post-S admission cell with the same complete premise I
(the unconditional source route can use ZERO), base x, DEMAND, empty E and
ANY tail:

```text
stored:   I -> {x.left/T,x.shared/V},  protection {x.left/T}
offered:  I -> {x.right/U,x.shared/V}, protection {x.right/U}
incoming remainder after ordinary subtraction: {x.right/U}, protected

Current: compute ordinary union; intersect old mask with union;
         union masks; intersect merged mask with union again.
New:     compute same ordinary union and mask union;
         their inclusion follows from the two valid inputs; construct once.

Both:    stored root {x.left/T,x.right/U,x.shared/V};
         mask {x.left/T,x.right/U}; delta {x.right/U}, protected;
         same subsequent observations.
```

This example illustrates store admission. It does not change the rule which
creates protection. Preserve selected-cleaner survivors, local and summary
mark cycles, group/FULL modes, and all protection upgrade behavior.

### 4.5 Proof and validation

Model ordinary and protected finite membership sets separately. Prove union
inclusion, delta-plus-upgrade inclusion, subtraction inclusion, and equality
between certified construction and current mask intersection. Then prove the
complete TaintGroup state and delta are equal for every admission branch.
Keep header canonicalization in the model. Compare finite event sequences and
production store/engine results, with late protection upgrades, partial masks,
mixed exact/any trees, exclusions, interning, both layers and no-change events.

Do not reuse a stored-union certificate for an arbitrary emitted delta:

```text
old root={a/T}, mask={a/T}
new root={a/T,b/U}, mask={a/T}
ordinary delta={b/U}
```

The merged mask is not a subset of that ordinary delta. The general
TrieOps.mergeAddDelta path must retain its current trim unless a separate
proof constructs the correct protected delta. TaintGroup's case above is safe
because its delta root explicitly includes the offered protection remainder.

Count removed mask traversals separately from remaining required traversals.
Measure Java CPU, allocation, GC and full run-6 behavior. The proposal removes
whole redundant passes; it does not claim that every sample in the 77.72%
region disappears. An exact-input fast rejection is a separate candidate: its
frequency is not measured and is not credited to this change.

## 5. Candidates to retain for later investigation

- **Construct only selected forward call aliases.** OWASP run-1 has 29.94% of
  Java samples in eager alias construction. Run the existing memory-effect
  guard first; build alias rows only for actual admitted input bases. Preserve
  complete backward aliases and stage ordinals. This is a useful source-backed
  option, but thingsboard's normal profile has only 0.63% alias construction
  and OWASP already completes. Do not rank it as the thingsboard fix.
- **Summary replay/delivery overlap.** An inline replay can process a record
  which is also awaiting queued delivery to the same subscription. The finite
  schedule exists, but real-project duplicate frequency is unknown. Measure
  complete input revision, summary revision, annotation growth and replay cuts
  before selecting a pair gate or join barrier. Do not drop valid late updates.
- **Select joined writer inputs more precisely.** Thingsboard binding tests
  222.44 million candidates for 28.02 million matches. Measure rejection causes
  before designing a mark/header index. Do not claim all rejects are mark
  mismatches or remove valid FLOW/concrete joins.
- **Share context-independent JVM relevance footprints.** The heap proves
  duplicate physical instruction keys, but this metadata is much smaller than
  completed identity containers. Keep it below the main memory proposal.

Do not select the whole-protected-image shortcut from the old wrapper profile.
Its extra-image branch is absent from sampled conductor run-4 to run-6 and is
small in the audited early thingsboard run-1 prefix. Stirling's measured
normalization problem above is a different operation.

## 6. Implementation and measurement sequence after selection

1. Write the detailed specs, constructive Lean models and finite equivalence
   proofs for the selected subset. Bind them to runtime source and add tests
   before implementation. Highlight any required semantic change for decision.
2. Implement each atomic change in a separate commit. Do not add new field,
   rule, alias or grounding semantics to make a proof pass.
3. Run the existing core and JVM suites and the selected formal checks.
4. Repeat only the authorized four-project configuration, with the same saved
   legacy finding baseline. Keep FULL, 16 GB, aliases/statics enabled and limits
   `1,1,2,...`. Do not rerun the legacy baseline.
5. Report engine, joined binding and barrier times separately. Report latest
   reached, complete and accepted run labels; all demand frontiers; current and
   legacy finding differences; CPU/allocation; and retained heap on OOM.
6. For thingsboard, require direct evidence that identity containers and owner
   searches fall. For Stirling, require evidence that redundant mask walks
   fall. Faster partial timeout endpoints alone are not fixed-work speedups.

The full acceptance goal still includes the three strict legacy Stirling
misses and thingsboard's large added-location set. Equal reports to the current
base are necessary regression evidence, but they do not close these older
accuracy limits.
