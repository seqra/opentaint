# Method-owned loop blocks

Date: 2 November 2026. Status: selected design; no runtime changes.

This document defines ownership and execution for
[loop fragments and demand-guided feedback](loop-fragments-and-demand-collapse.md).
Use [proof-guide.md](proof-guide.md). The method analyzer owns the split.
Blocks are internal analysis regions. They are not generated methods.

## 1. Selected changes and preserved behavior

| Part | Earlier proposal | Selected design |
|---|---|---|
| Owner | Fragment owners associated with generated functions | One method analyzer owns a tree of block states |
| Control | Synthetic function calls and return statuses | Internal block entry and exit transitions |
| Registers | Transfer through fragment argument positions | One original method register namespace; identity transfer between blocks |
| Summaries | Function-like fragment relations | Internal block relations, scoped by block and control ports |
| Loop restriction | Feedback transition | Loop-block output transition, for both repeat and leave routes |
| External analysis | Potential synthetic method/call-graph entries | Only the original method remains externally visible |

This replaces the generated-function mechanism in the earlier proposal.
It keeps the selected approximation rules: strict body-summary growth,
`FL(Zero)=0`, the three consumer checks, MAY/DEMAND cuts, and complete ND
execution. Putting the gate on both loop output routes is explicit. It
must not become a gate on every instruction or every sequential-block
transition.

Keep original field transfer, cleaners, mark handling, layers, exclusions,
real call handling, source permissions, static effects and typed Targets.
Keep original instruction and rule identities. Do not add a mark, field,
register pack, output-binding protocol or alias model for block routing.
A no-loop method keeps its existing transfer and summary behavior.

## 2. Initialization and immutable layout

The analyzer initializes its layout before accepting its first fact:

```kotlin
fun initializeMethod() {
    val layout = methodForm.blockLayout() // Cached on the original form.
    states = layout.blocks.map { block -> newBlockState(block) }
    root = states[layout.root]
}

fun buildLayout(graph: MethodGraph): BlockLayout {
    if (!graph.hasCycle()) return singleSequentialBlock(graph)
    return decomposeIntoBlockTree(graph)
}
```

The immutable layout can be built on first method-analyzer initialization.
It uses the original CFG, before direction-specific routing. Reuse the
same layout in both directions and in every run of this analysis. Do not
rebuild unrelated block identities from a backward traversal order.

```text
BlockId       = original method + deterministic tree path
BlockSnapshot = BlockId + entry port + exit port + run data
```

Block IDs are local to the method. They are not new MethodKeys. The
prescan call graph still contains the original methods and real calls.
There are no synthetic calls for prescan to resolve. An original
instruction's real calls, static accesses and rule positions keep their
original method owner.

At the transition between runs, load demand and saved rows for this same
layout. Do not introduce a new restricted-run block with empty historical
guidance and treat that absence as permission to discard its work.

A no-loop method has one sequential root. That root can use the current
method stores and execution path directly. It needs no extra forwarding
layer or duplicate summary store.

## 3. The block tree and the control graph

The tree describes containment. Control edges between blocks can repeat;
the execution graph is not a tree.

```text
Sequential B
  BL: sequential before region
  L:  loop region
      sequential iteration body, with nested block trees if needed
  AL: after region, recursively decomposed
```

Both kinds can contain children. A sequential region has no cycle after
its child loop regions are contracted. It can contain branches. Its
descendants can contain loops. A loop region has explicit repeat and leave
ports. Decompose its iteration body recursively for loops inside that body.

For an ordered region, split at its first outermost loop. BL contains the
prefix, L contains that loop, and AL contains the complete remaining
region. Recursively decompose AL. AL is not required to be a leaf or a
loop-free suffix. It can contain an arbitrarily deep hierarchy.

```text
Source:
    prefix
    loop1
    loop2
    suffix

Block tree:
    B1 = Sequential {
        BL1 = prefix
        L1  = loop1
        AL1 = B2 = Sequential {
            BL2 = {}       // Empty identity region.
            L2  = loop2
            AL2 = suffix
        }
    }
```

Thus L2 is below AL1 in the containment tree. It is not another child
beside L1, and it is not inside the body of loop1. A loop inside the body
of loop1 would instead occur below L1's iteration region. These two
hierarchies describe different source control flow.

Apply this rule recursively to every remaining ordered region. The
empty BL2 executes no physical operation and adds no method boundary
rule. Original instructions retain their order and occur once in the
leaf partition. The existing multi-entry/exit-port contract still applies
to a general CFG; this ordered example does not add a new CFG edge.

An original instruction belongs to exactly one lowest block. An ancestor
contains that instruction through its child; it does not execute or store
a second copy of it. After child loops and selected feedback edges are
handled as boundaries, the remaining local control graph is acyclic.
A self-loop must cross a loop boundary too.

The schematic `B := BL ; L ; AL` applies to a structured loop. Empty BL or
AL regions are valid identity boundaries. For general CFGs, keep the
original entry and exit ports rather than forcing a linear sequence.
An irreducible region can have several entry ports. The tree must not
merge distinct entries, duplicate instructions or invent a control edge.

The two principal loop routes are:

```text
Forward:   L -> L       repeat
           L -> AL      leave

Backward:  L -> L       repeat in the reversed CFG
           L -> BL      leave toward the original before region
```

These are route categories, not a limit of two physical CFG edges. Keep
each original source/destination pair and its exit kind. Original return,
throw and handler transfers can leave to an ancestor continuation. They
keep their existing control and observation policy. An inner break must
not become an outer break merely because both use the word "leave".

## 4. Shared registers and alias access

Every block uses every register in the original method:

```text
BL: x is original LocalVar(7)
L:  x is original LocalVar(7)
AL: x is original LocalVar(7)
```

A block boundary preserves the AP value:

```text
LocalVar(7).f.$/T -> LocalVar(7).f.$/T
same base, path, tail, mark, exclusions and protection
```

This line describes identity boundary transport, not a new executable
summary row that must be stored. Ordinary summary application can still
change the value according to its relation.

An internal boundary runs no BIND_IN/BIND_BACK call stages and starts no
extra alias expansion. Alias effects remain at the original physical
operations. This removes synthetic-call routing; it does not suppress
existing alias handling in a real method call or field operation.

Blocks do not have private argument registers. An internal block initial
can name an original local register. Use the existing fact shapes and
C2 rules with that base in the block's local scope. This does not widen
the original method's public initial or summary interface. ZERO, static
positions and the actual method return position keep their existing AP
representations.

Alias access is unchanged:

```kotlin
aliases.query(originalMethod, originalInstruction, originalFact)
```

The shared register namespace does not mean that facts from different
blocks are globally available. A fact reaches another block only through
a valid control transition or an applied block summary. Do not merge all
block edge stores just because their bases have the same register IDs.

## 5. Per-block state under one method owner

```kotlin
class MethodAnalysis {
    val layout: BlockLayout
    val blocks: Map<BlockId, BlockState>
    val work: Queue<BlockWork> // Contains a BlockId; one method owner drains it.
}

class BlockState {
    val edges: EdgeStorage          // Results after local processed points.
    val summaries: SummaryStorage   // Admitted, port-labelled relations.
    val demand: DemandView          // Frozen C2/C5 guidance for this run.
    val persisted: NormalRecords    // Saved admitted NORMAL block rows.
    val continuations: LocalLinks   // Existing summary/input composition.
    val firstRunAdmission: Run1Abstraction? // Run-1 only; local admission.
}
```

These are logical interfaces. Reuse existing store and AP code where its
contract matches. Do not create one UnitRunner, method actor or worker
thread per block.

| State | Contents and purpose |
|---|---|
| In-block edges | Local initial dependency and facts after each original instruction or child-completion point; filters duplicate output |
| Summary storage | Local initial-to-output relations, with entry/exit ports; shares a completed traversal |
| Demand view | Block-local entry admission and complete paired summary restriction; guides current work |
| Saved NORMAL records | Replays known transfers before current-demand admission |
| Local continuation links | Connect a child result to the waiting parent/loop prefix without changing its original dependency |
| Run-specific admission state | Existing run-1 abstraction/request state and backward source-hit state in their local scopes |
| Method work queue | Block-tagged instruction, delivery and publication work owned by the existing method actor |

For a composite block, the edge store contains its own child-transition
results. It does not copy the child's internal instruction facts. Parent
summaries compose child summaries. The root is the original method's
public summary boundary; it is not a second method analyzer around the
same block stores.

A local scope includes:

```text
BlockId + entry port + local complete initial + processed point
summary: also the actual exit port
```

Keep the existing layer and protection distinctions. ND originals remain
complete. A result under another block or port is not a duplicate. Block metadata belongs in storage and continuation keys, not in AP facts
or rule identities. Keep their existing equality and hashing. Do
not put a loop-iteration counter into a key; repeated traversals share
one block state.

## 6. Block entry, summary reuse and execution

Internal blocks use the selected call policy without a real call plan:

```kotlin
fun enter(block, input, parentLink) {
    replay(block.persisted, input, parentLink) // Every complete offer.
    replayNormalTargetsUnderExistingPolicy(block, input, parentLink)
    val initials = block.demand.emitInitials(input) // C2; same register IDs.
    if (initials.isEmpty()) return
    subscribeLocally(block.summaries, parentLink)
    startBlockInitials(block, initials)
}
```

Run-1 uses its existing abstraction/start policy in place of restricted
C2. It must not discard every block input because no earlier demand
snapshot exists. Shared registers need no bind-in/bind-back AP rewrite.
This does not remove C2, local initial dependencies or summary composition.

Request matching and run-1 abstraction also use the block scope. A request
for a local initial in one block is not a request for an equal register
name at every point in the method. The method owner commits the existing
temporary request buffers at its barrier and delivers local request
changes through the waiting internal links.

The link retains the parent prefix `P -> input`. A child starts under its
own admitted local initial `I`. When `I -> C` is applied, ordinary AP
composition gives `P -> result`. Never replace P by I at the parent.
A real call inside a block keeps its original call plan and bindings. Its
waiting continuation identifies the block, entry port and local premise.
When the original method actor receives a callee delivery, it resumes that
waiting block state. It does not inject the result into the root store.
The physical method/call-site identity stays unchanged.

For an ND row, actual execution still needs every member; the unary view
is only loop-restriction metadata.

A loop summary describes one traversal to a labelled repeat or leave
boundary. It does not stand for an arbitrary number of iterations with
an unlabelled exit. Repetition is an internal transition through the same
L state. Nested loop completion is a child result within that traversal.
The enclosing B relation is built by normal parent composition.

After processing original statement S, store its result at S. For a child
summary application, store the result at its parent child-completion
point. Enqueue destinations only for fresh output. Keep the original
instruction-index/base CFG-delivery cache, but stop local traversal at
block boundaries. A cache entry must not jump across a loop gate. Its
scope includes the immutable layout, direction and containing block.

## 7. Loop output transitions

The method analyzer routes the output. The block owns no independent
scheduler:

```kotlin
fun leaveLoop(loop, row, parentPrefix, actualPort) {
    val F = applyBlockSummary(parentPrefix, row)
    val values = if (!grows(row)) listOf(F) else restrictLoop(loop, F)
    for (value in values) {
        storeFreshAtLoopOutput(actualPort, value) { fresh ->
            routeToActualDestination(actualPort, fresh)
        }
    }
}

fun grows(row) = FL(row.conclusion) > FL(row.premise) // FL(Zero) = 0.
```

This applies to the repeat and leave output routes. The actual port is
retained through restriction. A successful AL check cannot turn a repeat
edge into a leave edge, or deliver its result to both ports.

For each loop, its enclosing composition is `B := BL ; L ; AL`. The
three checks in forward order are:

```text
1. C2 against AL demand.
2. F composed with AL saved NORMAL summaries, then paired B C5.
3. C2 against L demand at the actual next entry port.
```

In backward order they are:

```text
1. C2 against BL demand.
2. F composed with BL saved NORMAL summaries, then paired B C5.
3. C2 against L demand at the actual reversed re-entry port.
```

AL and BL in these checks denote their complete regions, including all
nested children. In the two-loop example, L1 checks AL1 demand and saved
AL1 summaries. It must not substitute AL2 or jump directly to the suffix,
since loop2 belongs to AL1. AL1 has its own entry demand, summaries and
paired restriction; entering it routes work through BL2, L2 and AL2.

For L2, the enclosing B is B2, which is AL1. Its composition check uses
AL2 summaries and B2 demand. Parent composition then carries a completed
B2 result to B1. Do not use B1's exit permission in place of B2's local
paired row. The same tree is traversed backward: AL2, L2, empty BL2,
then the enclosing continuation toward L1 and BL1. Do not flatten those
scopes when BL2 is empty.

B is the enclosing composition for this decomposition level. At the top
level it is the method root. At a nested level it is an internal parent
region with its own demand. Normal parent composition carries results
up to the root; it does not bypass the root's final paired restriction.

Use the union of all selected images. Keep F's complete parent dependency
for the B test; use the unchanged value bases for the C2 tests. These are
read-only checks. Hypothetical AL/BL composition executes no instruction,
exit rule, static write or Target report. Actual routing and replay at
the selected destination still follow the ordinary policy.

Equal/shrinking rows bypass this extra loop restriction. Growing rows use
the existing projection contract: retain the required concrete prefix,
cut only an actual suffix to MAY/DEMAND, and preserve all selected images.
If all families reject, drop the value. Do not force an unmatched exact
value to MAY to manufacture admission.

## 8. Rules, effects and normal exits

All physical operations still execute in their original method context.
Block entry, child completion and loop dispatch are silent control points.
They do not execute copies of method entry/exit rules, resolve new
configured calls or get new source/sink identities.

A static write supplies its mark at the original write point. A sink
creates its Target at the original sink. These observations do not wait
for a loop to exit normally. Static callbacks keep their original method and instruction identity; the
layout selects the owning block for a point resume. Request, local initial
and parent-prefix scopes remain distinct. Existing static shortcuts go to
the original method's exit-rule/summary path; a block exit is not graph.exitInst.
A shortcut does not create a normal CFG exit from an infinite loop.

Actual method return instructions and handlers retain their physical
ports. Apply real method exit rules once at the method's real exit path.
Block summary admission applies its own C5 without those real rules.
A run-1 static shortcut first lifts its block-local dependency through
the existing parent links to the original method scope. It then uses the
original exit-rule/summary handler. Do not insert a block-local initial
directly into the root public store. Terminal/side-effect summary delivery
does not wait for a loop leave and does not invent a normal CFG return.
These existing effect channels are separate from the two ordinary loop
output routes.

Only root public summaries enter the original inter-method publication
interface. Internal Target rows use the same selected typed rules and
local composition; their report identity remains the original location
and rule ID.

## 9. Run completion and handoff

All block work contributes to the method's existing counted work. At a
method-queue barrier, commit pending local summaries and deliver their
fresh deltas before declaring the method idle. A pending local delivery,
request or static effect cannot be hidden in an otherwise empty block.
Do not wait for an external message to deliver a summary to a sibling
block owned by the same analyzer.

Freeze only after the ordinary run barrier:

```text
for each block:
    persist its admitted NORMAL rows under BlockId and ports
    select its outgoing DEMAND/typed guidance for the next run
    freeze a block demand snapshot with the existing reversed orientation

publish/collect original-method results at the root
release transient block stores through the existing run lifecycle
```

The root's outward demand is not a replacement for internal block demand.
Both must remain available in their scopes. The method-owned outgoing
refinement frontier is the union of the selected block frontiers, tagged
with their block IDs and ports. The existing empty-frontier stopping rule
uses that union; public inter-method summaries still come from the root.
Count only admitted rows selected by the existing refinement/Target rules,
not every local MAY value or stored NORMAL row. This preserves the earlier
per-region refinement policy under one method owner. Do not force another iteration for
an irrelevant cut. The current field-limit schedule remains `1,1,2,3,…`.

## 10. Principal trace

```java
Node B(Node p) {
    Node x = p;             // BL: arg(p) -> local(x).
    while (again()) {
        x = x.f;            // L: local(x).f.* -> local(x).*.
    }
    return x;               // AL: local(x).* -> ret.*.
}
```

```text
BL completes:    parent dependency p -> x.
L first offer:   x.f.f.$/T; every block uses the same x register ID.
L saved row:    x.f.*/FLOW -> x.*/FLOW; shrinking, no new gate.
Repeat result:  x.f.$/T; store at the repeat output, then re-enter L.
Next repeat:    x.$/T after another saved read.
Later leave:    the test selects leave; its identity row retains x.$/T.
AL application: ret.$/T; paired root C5 uses the original p dependency.
```

A different x base in a block never appears. No synthetic argument or
alias mapping is required. The port still determines whether a result
repeats or leaves; equal AP payloads do not collapse the two routes.

## 11. Proof and validation boundary

The constructive ordered-region model preserves the exact source segment
sequence and gives the recursive AL shape for the two-loop example. It
also covers arbitrarily many successive loops. It treats each selected
loop region as an opaque segment; it is not a general CFG loop detector.

The constructive block model proves one method owner, unchanged shared
payload transport, separation of block stores, labelled direction-symmetric
routing and owner-preserving summary delivery. The existing control model
proves exact finite physical traces for a supplied valid partition and
feedback ports. The projection and summary-shape proofs remain in force.

The decomposition algorithm must construct that valid tree and routing
certificate from the real CFG. The model does not certify a Kotlin
extractor, all AP transfer adapters or whole-driver convergence. Validate
no-loop identity behavior, sequential/nested/self/multi-entry loops,
original alias access, both output routes, backward port reversal, local
publication barriers, internal demand handoff and original boundary rules.
No new project measurement is claimed by this design update.
