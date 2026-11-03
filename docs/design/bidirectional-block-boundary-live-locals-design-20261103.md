# Drop dead local conclusions at block boundaries

3 November 2026. **Selected design. Not implemented.**

This extends point 2 of the
[combined implementation proposal](bidirectional-joined-state-loop-consumers-packed-guidance-implementation-20261103.md).
Use the same runtime reference, `050b83cfb7b2e75856ea113c44d0a2d6b707250d`.
Follow the [implementation guide](../../spec/impl-proposal-guide.md) and
the [proof guide](../../spec/proof-guide.md).

## 1. Contract

Compute forward and backward live-local bit sets when the method block
metadata is built. At an outgoing boundary, drop a DATA edge if its
conclusion is a local variable that is dead on that continuation. Perform
this test **before summary construction, publication, C5 intersection and
loop-consumer demand checks**.

Use CFG instructions only. Do not load rules, inspect rule conditions,
enumerate aliases or call alias analysis. A rule cannot access a local
that its instruction does not mention. An inaccessible local does not
need an alias check.

A loop-body temporary whose old value is dead on repeat and on every
leaving route has no boundary summary. It does not escape the loop body.
This test uses values and CFG uses, not variable names or declaration text.

| Current behavior | New behavior |
| --- | --- |
| Unchanged delivery brings a temporary to a boundary, then constructs a local summary and checks its consumers | One bit test drops a dead local conclusion before this work |
| A temporary can enter parent completion, publication and demand stores although the continuation cannot read its value | The temporary stays inside its useful block scope |
| Live loop-carried values use the ordinary block path | The same path remains for live loop-carried values |

**Major analyzer semantic changes: none.** The selected change removes
unobservable local rows. Internal local summaries, demand rows, callbacks
and work counters can decrease. They are not required to be equal to the
unfiltered inventories. Preserve observations, live results, method
summaries, reports, source permission and static effects. Do not change
field transfer, marks, layers, protection, ND joins, CFG reachability,
loop restriction, initial emission or method exit rules.

Only test the conclusion base. Keep the complete premise and all retained
fact annotations unchanged. Never drop ZERO, Target, static, argument,
`this`, return or exception facts through this test. Keep effects already
produced inside the block, including Targets and NORMAL rule contributors.
Do not infer a new lexical variable identity or rename method registers.

## 2. Principal pattern

```java
x = ...;
while (true) {
    var tmp = x;          // Reads x. Replaces the old tmp.
    use(tmp);            // Reads the new tmp.
}
```

```text
At the copy:             P -> x.$/T produces P -> tmp.$/T.
At repeat, before:       tmp enters summary/demand processing.
At repeat, after:        drop P -> tmp.$/T immediately.
Reason:                  the next copy kills old tmp before any read.
Retain x:                the next copy reads x before overwriting it.
```

The same test applies to FLOW and DEMAND facts with this local base.
The field chain and mark do not make an inaccessible local accessible.
An effect from `use(tmp)`, such as `P -> Target`, is already separate and
remains. The filter does not undo the instruction.

This is different from a live carried value:

```java
Node tmp = null;
while (again()) {
    if (choose()) tmp = sourceT();
    else sinkT(tmp);      // Can read a previous iteration's tmp.
}
// AL does not use tmp.
```

The repeat continuation keeps `tmp`: there is a path to a read before an
overwrite. The existing summary and restriction path handles that value.
The leaving continuation drops `tmp` if it is dead in AL. Do not add a
direct repeat path or drop live carried values.

## 3. Instruction metadata and fixed point

Add a small metadata API next to method forms. It must inspect operands
without compiling or specializing a rule. Do not reuse
`isBaseRelevant`: its current backward footprint can query aliases.

```kotlin
data class LocalAccess(
    val uses: BitSet,
    val definiteDefinitions: BitSet,
    val mentions: BitSet,
)

// Proposed API. All indices are the existing LocalVar.idx indices.
fun localAccess(instruction: CommonInst): LocalAccess
```

Forward `uses` contains RHS locals, call receiver/arguments, address and
index locals of a memory LHS, and return/throw operands. A direct local
LHS is a definition, not a read, unless it also occurs in an operand.
For `tmp = x`, USE is `{x}` and DEF is `{tmp}`. For `x = x.f`, USE
contains `x` whether or not the overwrite can be certified. A field/array
write does not define its base local.
`JIRAssignInst.operands` includes the LHS. Do not collect that array as
forward USE without separating the direct local LHS from the RHS.

A definition kills the old local only if the overwrite is definite on
all successors of that CFG instruction. If an assignment can throw before
it commits, use an empty kill set unless the existing graph already has
a separate committed-write node. Do not add a graph rewrite or a new
exception policy to make the mask smaller.
The initial classifier can certify plain local/constant copies, including
`tmp = x`. An unknown or potentially throwing RHS has no certified kill.
`LanguageManager.producesExceptionalControlFlow == false` is not a commit
certificate: its JVM implementation does not classify every throwing RHS.

Use ordinary forward USE/DEF liveness. Backward analysis must include
definitions as accesses: it must reach the instruction that defines the
demanded local. Use all instruction mentions and no kills for the backward
mask. This conservative backward calculation needs no reverse-transfer,
rule or alias analysis. It can keep extra locals; it cannot drop a needed
one. In particular, do not swap USE and DEF and kill RHS locals: the
reverse of `a = b` also preserves existing `b` facts.

```kotlin
// Temporary solver state. graph is the actual graph for this direction,
// including its exceptional/discovery edges and the loop feedback edges.
val liveIn = Array(graph.size) { BitSet(localCount) }
val queue = allInstructionIndices()

while (queue.isNotEmpty()) {
    val s = queue.removeFirst()
    val next = if (forward) access[s].uses.cloneBits()
               else access[s].mentions.cloneBits()
    graph.forEachSuccessor(s) { to ->
        val carried = liveIn[to].cloneBits()
        if (forward) carried.andNot(access[s].definiteDefinitions)
        next.or(carried)
    }
    if (next != liveIn[s]) {
        liveIn[s] = next
        graph.forEachPredecessor(s) { queue.addIfAbsent(it) }
    }
}
```

Initialize **all** nodes, including non-returning SCCs. Starting only from
method exits misses `while (true)`. The equations compute the least fixed
point from empty sets. They do not inspect current facts or demand.

## 4. Masks at real boundary continuations

Retain immutable bit sets for block output interfaces in both directions.
The bit set for a real directed route `s -> to` is `liveIn[to]`: the
instruction at `s` has already run. Do not use the input mask of `s`.

```kotlin
// Proposed sidecar for the existing immutable layout/form owner.
class BlockLiveLocals {
    fun mayLeave(direction: Direction, block: BlockId,
                 exit: PortId, local: Int): Boolean
    fun mayFollow(direction: Direction, route: MethodBlockRoute,
                  local: Int): Boolean
}
```

For the existing single logical normal exit, union the masks of its real
leaving routes. Keep feedback separate. Before actual delivery, check
each real route again. A union must not leak a value from a live route
onto a dead route.

```text
Loop repeat output:    union of genuine repeat continuations.
Loop leaving output:   union of genuine leaving continuations only.
Actual route delivery: liveIn of that route's destination.
```

Use the same rule for backward routes, empty identity blocks and nested
blocks. A child result kept for one continuation can become dead when it
crosses the next parent boundary. Check that boundary too. Preserve the
single loop exit and its existing join scope.

Build this sidecar with the existing method decomposition metadata, once
per actual graph direction. Cache it with that form/layout owner, not
with each run, scope, fact, mark or caller. Release instruction solver
arrays after retaining the required boundary masks. No fact or callback
belongs in this metadata. Treat stored bit sets as immutable.
An unsupported synthetic output role keeps the native path until its
actual target is known. A missing mask is not an empty live set.

## 5. Boundary integration

```kotlin
fun keepLocalConclusion(block: BlockId, exit: PortId, value: Facts): Boolean {
    val local = value.base as? AccessPathBase.LocalVar ?: return true
    return liveLocals.mayLeave(direction, block, exit, local.idx)
}

// BlockRunState: early guard avoids boundedSummaryResult work.
fun retainBlockSummary(exit: PortId, original: PremiseKey, value: Facts) {
    if (binding?.keepLocalConclusion(exit, value) == false) return
    existingRetainBlockSummary(exit, original, value)
}

// Central guard also covers endAt's direct retainSummary path.
fun retainSummary(original: PremiseKey, value: Facts, exit: PortId) {
    if (binding?.keepLocalConclusion(exit, value) == false) return
    existingNormalizeCountRestrictAndPublish(original, value, exit)
}

// MethodBlockRuntime.onApplied: applies to saved and current child results.
fun onApplied(link: LocalLink, exit: PortId, original: PremiseKey, value: Facts) {
    if (!keepLocalConclusion(link.child.block, exit, value)) return
    existingLimitRestrictAndStoreCompletion(link, exit, original, value)
}

// Before routing one actual completion branch.
for (route in deliveryRoutes(exit)) {
    val local = value.base as? AccessPathBase.LocalVar
    if (local != null && !liveLocals.mayFollow(direction, route, local.idx)) continue
    existingRouteCompleted(route, original, value)
}
```

Use the same producer guard for leaf delivery, empty identities and
parent forwarding. Do not add an independent fact store or replace
post-statement deduplication. Leave unchanged delivery inside a block.
It can deliver a dead temporary to the boundary; the bit test stops it
before the expensive boundary work.

Apply the same masks inside loop observation. Adjacent and repeat C2
families use their own continuation masks. Saved-AL replay checks its
completed local output against the enclosing output mask before
normalization/C5. Do not let observer-only replay reintroduce a row that
actual boundary delivery drops. All nonlocal observation families keep
their existing order and behavior.

Physical method entry/exit rules still run at their existing instruction.
Do not put a dead-local shortcut ahead of those handlers. Filter only
their completed DATA output. The direct `endAt`/`retainSummary` path must
use the same final output guard; do not bypass it accidentally. The
STATIC shortcut and Target path have nonlocal conclusions and pass.

Save completed effects and existing contributor snapshots as before.
An edge with a dead local **premise** and a live conclusion remains.
This feature does not remove inputs needed by joined writer binding or
the inventories retained by point 1.

| Source | Proposed change |
| --- | --- |
| `JIRMethodEntry`, `JIRMethodForms` and method-context metadata access | Extract raw local operands; own the decomposition-side liveness metadata; do not use the alias-aware relevance API |
| `MethodBlockLayout` sidecar | Hold immutable per-direction interface and real-route masks; leave block/port IDs unchanged |
| `BlockRunState.retainBlockSummary` and `retainSummary` | Early and central conclusion-only guards |
| `MethodBlockRuntime.onApplied` and `routeCompleted` | Guard saved/current results before observer work and before each actual route |
| `MethodBlockRuntime.observe` | Use the same continuation and enclosing-output filters in observer-only replay |

The metadata API must have a conservative default for unsupported
backends. It must not silently return an empty mask for an unclassified
instruction or interface. The selected JVM path must classify the plain
copy in section 2 exactly.

## 6. Proof and implementation gates

The [constructive model and proof report](../../spec/lean/proposals/block-boundary-live-locals-20261103/REPORT.md)
cover finite CFG liveness, forward read-before-kill paths, conservative
backward mentions, boundary masks and dead-local observation removal.
The checker passes 42 theorems and audits 72 declarations. Its source
pins use `c7ed16e99c599ca926812c067df0b6608b6185f2`, which has the same
runtime as the combined proposal's reference revision.
The native instruction classifier and insertion sites remain implementation
obligations. The model does not prove a JVM speedup or a byte saving.

The proof chain is:

```text
finite monotone equations -> executable least fixed point
read before definite kill -> local is in liveIn
local absent from liveIn -> no observation of that old value
each boundary mask covers its actual continuations
drop dead conclusion -> same remaining observations and live results
nonlocal/premise/annotation/completed effects -> unchanged
```

Do not claim equality of all internal summary streams after removing dead
rows. The three original component proofs still apply to their retained
inputs. The new erasure proof establishes the observation projection for
the pre-filter. Kernel checking does not establish the Kotlin adapter.

Add native RED controls before implementation, then make them GREEN:

| Control | Required check |
| --- | --- |
| `x=...; while(true){ tmp=x; use(tmp); }` | No `tmp` boundary summary, completion or observer call; retain `x` |
| Dead copy with FLOW, FULL T and DEMAND | Same drop for all annotations; surviving facts stay bit-for-bit equal |
| Conditional assignment then use on another traversal | Keep live carried local on repeat; preserve sink |
| Dead AL local but live repeat | Keep repeat; no DATA delivery to AL |
| Live AL local | Preserve its output and later sink |
| Two leaving routes, local live on one | Shared exit keeps it; actual dead route drops it |
| Nested loop local | Recheck child and parent exits; no leak into an unrelated suffix |
| `x=x.f`, field/array write, exceptional assignment | Read-before-write and uncommitted overwrite preserve old-value liveness |
| Backward `a=b` and definition reached before a read | Keep required definitions and preserved RHS facts |
| ZERO, Targets, statics, arguments, return, exception | Existing paths, exit effects and inventories unchanged |
| Live conclusion with a dead premise | Keep full original premise and annotations |
| Non-returning SCC, empty block, backward discovery | Valid fixed point and exact route coverage |

Compare reports, live/method outputs, source permissions and required
guidance with the unfiltered oracle. Check dead-row absence separately.
Do not require old diagnostic work counts or dead local demand rows.

Run this pre-filter before the query-reuse optimization in point 2.
Counters can record local boundary offers/drops and avoided summary or
observer entries. Do not perform a demand lookup to count avoided work.
In the selected campaign, report those counts with the latest reached,
complete and accepted run-N. The current measurement frontiers remain:
OWASP run-5/5/5; Conductor run-6/5/5; Thingsboard run-1/none/none;
Stirling-PDF run-8/7/7. No new measurement is part of this design update.
