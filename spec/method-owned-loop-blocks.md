# Method-owned loop blocks

Date: 2 November 2026. Status: selected design. The boundary corrections
pass 2,372 common and 453 JVM tests. These native controls do not prove all
AP adapters or project quality. The latest attempted project campaign (`3750b73a`) reached OWASP **run-1 FAILED**,
with no completed or accepted iteration, then stopped conductor during prescan.
The earlier `10957156` campaign completed OWASP **run-5** with 51 missing
baseline sink identities. A fresh campaign is required. See the
[boundary coverage report](../docs/reports/bidirectional-loop-boundary-source-gap-20261102.md).

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
| Backward exceptional ZERO | Demand lookup at the reached exceptional boundary only | Also apply complete normal-exit control demand; its outgoing ZERO DemandTarget uses the borrowed normal invocation in handoff metadata only; section 3.1 |
| Boundary coverage | The current block adapter excludes the real entry/exit transfer from its adjacent-region records | Adjacent-region summaries cover that transfer when their span reaches the real boundary; section 6.1 |
| Target and run-1 static output | Some original boundary results belong only to the public method | Publish first at the nearest block boundary, then compose through every ancestor; section 6.2 |
| Normal loop exit | Separate physical leave ports can partition AL rule joins | Use one logical normal exit and AL ingress; keep actual routes and the accepted branch-union false positive; section 6.3 |
| Static shortcut input refinement | A rebased exit input can request C.g/T without refining its waiting C.f/FLOW origin | Relay the actual request through existing identity continuation links, then reuse the original-input materializer and forward its genuine answer; section 8 |
| Static exit phase | A STATIC conclusion and child entry can cause a completed exit to run again | Carry raw output as `STATIC_SHORTCUT`; only it runs the real exit, and completed `ROOT_EXIT` rows use metadata-only finalization; section 8 |

This replaces the generated-function mechanism in the earlier proposal.
It keeps the selected approximation rules: strict body-summary growth,
`FL(Zero)=0`, the three consumer checks, MAY/DEMAND cuts, and complete ND
execution. Putting the gate on both loop output routes is explicit. It
must not become a gate on every instruction or every sequential-block
transition.

Keep original field transfer, cleaners, mark handling, layers, exclusions,
real call handling, source permissions, static effects and typed Targets,
except the explicit backward exceptional-ZERO demand lookup in section 3.1
and the explicit normal-exit control interface in section 6.3.
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
The shared normal loop-exit interface in section 6.3 is a logical join.
It retains the original physical route labels; it does not erase this
CFG contract or merge irreducible loop entries.

The two principal loop routes are:

```text
Forward:   L -> L       repeat
           L -> AL      leave

Backward:  L -> L       repeat in the reversed CFG
           L -> BL      leave toward the original before region
```

The backward view also retains the existing exceptional-exit discovery
edges required by interpreter I11(e)/AP S11. The hierarchy uses the original
forward CFG, but its directed view comes from the existing backend graph,
which can have this backward-only overlay. Discovery is not a new forward
edge or a normal loop leave. See the implementation proposal's existing
backward-discovery adapter.

These are route categories, not a limit of two physical CFG edges. Keep
each original source/destination pair and its exit kind. Original return,
throw and handler transfers can leave to an ancestor continuation. They
keep their existing control and observation policy. An inner break must
not become an outer break merely because both use the word "leave".

### 3.1 Selected exception: normal demand at a backward exceptional ZERO

This is a selected semantic change. It is a narrow compatibility hack.
A sink Target keeps the logical normal exit as its conclusion boundary,
including a sink in a loop that has no normal leave. In backward analysis,
the existing exceptional discovery route can reach that loop. Its reached
ZERO must also use the normal-exit control demand.

```text
lookup(invocation, ordinaryRows, normalExitRows):
    rows = ordinaryRows
    if invocation.direction == BACKWARD
       and invocation.input == ZERO
       and invocation.actualBoundary == EXCEPTIONAL_EXIT:
        rows += normalExitRows     // Keep each complete row unchanged.
    return existingTypedLookup(rows, invocation)
```

The invocation must have an actual reach witness in the supplied directed
CFG. For an original method exit, this can be the existing configured
backward ZERO start. For a block boundary, it must come from the existing
method-owned route. This rule does not start a block, create another seed,
scan demand to find a start, or create a CFG edge. Continue from the
actual exceptional boundary through the supplied backward graph.

Borrow only rows that admit ZERO under the existing typed matching law.
In particular, a paired Target row retains its own other endpoint. If
the normal row is `(Target, p/T)`, admission does not turn it into
`(Target, q/U)` or an unpaired ZERO permission. Later publication must
still satisfy that same complete pair. Union two row lists; do not make
an entry/exit product.

The rule does not alias Target demand to every physical entry. Forward
lookups, non-ZERO inputs, other boundaries, DATA lookup, and native record
ports keep their existing behavior. A DATA result derived from admitted
ZERO still uses its complete paired control row; it does not obtain an
independent DATA input permission from this exception.

```java
void work() {
    while (true) {
        sourceTAtFFFF(x); // Assign T at x.f.f.f.f.$; preserve other positions.
        x = x.f;
        sinkRootT(x);   // DEMAND witness; Target uses logical normal exit.
    }
}                      // No normal CFG return is required for Target.
```

The run-1 field limit is 1.

The existing backward graph has exceptional discovery for this body.
When its exceptional ZERO is reached, the normal Target demand can admit
that ZERO. The analyzer then follows the actual backward routes. The
forward graph still has no path from this loop to the normal return.
Only selected DEMAND Target rows guide this next run. NormalTarget rows
remain ignored in backward analysis.
This admission is not evidence that a NORMAL finding exists. Layers,
source permissions, complete bindings and Target publication remain
separate checks.

#### Required continuation law for the borrowed control demand

An existing exceptional discovery edge can have a backward-only physical
port `d`. That port is valid for the live backward invocation. It is not
a forward entry. Thus an outgoing backward `ZERO -> DemandTarget` from
this admitted invocation must carry the borrowed normal invocation in
its handoff metadata.

```text
Actual backward state:
    scope = (block, d), ZERO -> DemandTarget, logical exit = ROOT_ENTRY

Outgoing handoff metadata only, with a normal-borrow witness:
    scope = (block, ROOT_EXIT), ZERO -> DemandTarget, exit = ROOT_ENTRY

Reversed forward control demand:
    scope = (block, ROOT_ENTRY), (Target, ZERO), exit = ROOT_EXIT
```

Apply this address change only when all conditions hold:

```text
direction == BACKWARD
an actual exceptional/discovery ZERO invocation borrowed normal demand
the outgoing premise is ZERO
the outgoing target is DemandTarget
```

The witness must come from successful admission by one complete normal
control row. Preserve that row's paired payload and all annotations.
Do not use a broad flag that merely says this block has an exceptional
edge. Ordinary C5 still validates the published result.

Do not change live subscriptions, current Target storage, DATA rows,
native records, NormalTarget rows or non-ZERO Target rows. They keep their
physical scopes and ports. This is a control-demand handoff address,
not another AP projection, seed or direct-start policy.

In the four-field example above, run-1 (limit 1) and run-3 (limit 2) can
retain only a DEMAND candidate. Run-5 (limit 4) can resolve the exact
source path through four ordinary reads. A handoff that still names
backward-only `d` can stop this continuation at run-3. The normal-invocation
metadata keeps the required forward control route. The finite model
checks this witness; whole-driver/native correspondence remains a test
obligation.

The scoped proof dossier gives the constructive model and its limits.

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

### 6.1 Required coverage of an original method boundary

This amendment corrects an implementation gap in the complete observer.
It does not change field transfer, C2, source permission or rule semantics.
The pre-correction adapter did not satisfy this contract. Its before-region
record started after the real entry rules. Its after-region probe reached
enclosing C5 before the real exit rules. Both omissions can drop a useful
growing loop output.

A region summary must cover the complete program span that its control
ports name. If BL reaches the real method entry, its relation includes the
actual entry rules and the original entry instruction, in their existing
handler order. Its original is the input before that transfer. If AL
reaches a real method exit, its relation includes the existing exit
transfer, exit rules and metadata effects before the enclosing B C5 test.
The same span rule applies in backward analysis.

```text
Entry-inclusive prefix:
  true pre-entry input -> actual entry transfer -> BL body -> L entry

Exit-inclusive suffix:
  L output -> AL body -> actual exit transfer -> B C5
```

This requirement is recursive. An adjacent region below a nested AL must
cover the boundary transfers in its own declared span. Composition toward
an ancestor must not skip an intervening boundary transfer. A root-only
cached prefix does not establish coverage for every nested region.

Use the same original boundary handler once on actual execution. A local
block entry or completion does not execute a second copy. Reuse its genuine
summary relation for saved replay and guidance. Do not add a hypothetical
boundary evaluator, raw-fact fallback, source hit, seed or lookup rule.
An otherwise empty BL is not an identity relation when its span includes
an actual entry rule.

Keep the true original, entry port and exit port on every composed row.
Do not relabel an after-rule BL row as a pre-rule row. For example, the
two existing NORMAL transfers below have this composed relation:

```text
ZERO -> request.[any-taint]/T   // Actual entry source.
request.*/FLOW -> cookies.*/FLOW
----------------------------------------------------
ZERO -> cookies.[any-taint]/T  // True entry-inclusive BL.
```

`request.*/FLOW -> cookies.*/FLOW` alone does not encode that source.
The full public method summary is not a substitute for this shorter span:
its real exit can remove entry marks, and its public-base filter can
reject local results. Keep those existing exit effects at their real span.

Use ordinary row classification. Eligible NORMAL relations use native
record persistence and replay. DEMAND relations use the existing selected
handoff and C2/C5 guidance. A field-limit cut or a GROUP producer does not
become NORMAL to make it persistable. The existing backward ZERO-origin
NORMAL handoff exception also remains in force: an exit-inclusive reverse
suffix can provide forward guidance through that exception even when it
is not a native backward record.

Complete ND execution within the selected block-entry scope, normalization, exclusions, protection, mark
binding, native reversal and typed Target handling stay unchanged. A
unary restriction arm does not prove an entry or exit rule. Saved replay
applies only an eligible, already inferred relation at its genuine ports;
it creates no fresh source hit. Actual unresolved sources still use the
existing source-permission mechanism.

The boundary relation also needs the correct current-run ownership and
paired guidance interface. Exporting a root completion snapshot alone
does not establish this property. For example, a root Target with no
corresponding scoped AL row can leave that AL's later paired restriction
empty. The implementation must establish the genuine boundary-inclusive
relation and its ordinary demand interface; it must not bypass C5 to
populate a missing row. This adapter remains a design and test obligation.

### 6.2 Selected nearest-boundary publication

Publish a Target or a run-1 static result first at its nearest block
boundary. Apply that summary through the existing waiting parent links.
Each internal ancestor retains its own admitted relation. Continue until
ordinary composition reaches the method boundary. Do not publish only at
root and then construct missing child guidance from that root row.

```text
Physical sink/write, with local original I:
  nearest block: I -> Target/static
  parent:        P -> Target/static   // Existing complete application.
  ancestor:      Q -> Target/static
  method:        A -> Target/static
```

Every step keeps its genuine entry and exit ports, complete waiting
original, layer, mark, exclusions, protection and physical report identity.
No step changes an ND row into independent executable arms. All members
must match under the existing full binding. NormalTarget still composes
only with NORMAL inputs and is ignored backward. Its persisted-row
suppression stays unchanged. DemandTarget and run-1 static outputs retain
their DEMAND classification.

The method entry and exit transfers belong to their genuine region spans.
Use the existing boundary handler and original physical operation once.
Forward entry rules run before the original entry operation. The real
exit transfer and exit rules retain their existing order. This ownership
does not make every block completion a method exit.

Apply any existing method-original-dependent exit adjustment after the
parent composition has supplied that complete method original. In
particular, `globalStateDrop` and entry mark removal must not test a
non-ZERO local I in place of a true ZERO method A. The selected boundary
rule joins use the shared normal interface in section 6.3. Keep the accepted
root branch-union false positive; do not use a per-ingress partition to remove it.

These local rows use ordinary restriction, persistence and handoff. A
DEMAND Target therefore gives its own paired guidance to every selected
ancestor and to its nearest block in the next run. A NORMAL producer uses
native replay where eligible. The existing backward-ZERO NORMAL handoff
exception remains in force. There is no boundary actor, new source seed,
guidance closure, hypothetical rule evaluator or unrestricted snapshot.

### 6.3 Selected single normal loop exit

Use one logical normal exit for a loop and one corresponding AL ingress.
Keep the actual physical route as control metadata. Ordinary rule joins
at that shared normal interface can combine its normal-leave inputs.
Complete ND execution remains required; unary restriction metadata cannot
satisfy a multi-condition rule.

An SCC alone is not always that complete loop region. Extend its normal
leave paths with their reachable acyclic tails up to the nearest common
real normal postdominator J. Keep J outside L. If J is in the current
region, AL begins there. Keep the original SCC headers
and feedback edges. This moves the existing tail operations into L; it
does not copy an operation or add a CFG edge. Check that the extended
iteration graph is acyclic after the original feedback cuts and that
every ordinary normal outlet reaches J. A second normal exit cannot be
absorbed as a tail. If actual normal leaves have no certified common
join, detect and report that layout gap; do not dispatch to all targets.
A loop with no ordinary normal leaves needs no new join or exit edge.

```text
Original SCC:     {1, 7}, header 1, feedback 7 -> 1
Normal tails:    1 -> 2 -> 3 -> 6
                 1 -> 4 -> 5 -> 6
Extended L:      {1, 7, 2, 3, 4, 5}
AL begins at J:  6
Normal outlets:  3 -> 6 and 5 -> 6, one logical exit
```

Build this partition and its normal-interface directory deterministically
from the original graph. Reuse it in both directions and all runs.
Canonical join IDs belong to that directory; they do not collide with
physical ports or the existing backward discovery overlay.

The earlier proposal to remove the cross-entry branch-union false
positive is withdrawn. That false positive is accepted. For example:

```text
while (again()) {
    choose {
        a = sourceT(); break;
        b = sourceU(); break;
        continue;
    }
}
normalExit: sink if CM(a,T) AND CM(b,U);
```

No concrete execution in this example supplies both marks. The old root
join could merge its NORMAL ZERO-origin contributions and emit
NormalTarget. The common normal interface permits that result too.
It must also retain a complete witness whose inputs come from one path.

The common join identity is not a new physical CFG edge. Forward DATA
delivery keeps the actual continuation. Native and demand handoff must
retain or refine its physical route labels when the direction reverses.
If several leaves reach the same physical AL boundary, its reverse view
can visit every original normal predecessor. It cannot choose only one
representative edge and lose the others. If continuations differ, do not
route a value to another continuation merely because the normal join
identity is shared. Establish the exact route correspondence explicitly.

Feedback is relative to the current loop. Its own feedback stays a repeat.
An edge to an enclosing header can be an inner normal leave and an outer
feedback edge. It can use that real enclosing header as J even when J is
outside the current recursive region; the inner AL is then an empty
logical continuation. Keep the original route, port and outer feedback
owner. On reaching the outer interface, restore its outer repeat role.
The classification view does not change the physical graph or its
feedback directory.

Exceptional, discovery and method-return routes keep their existing ports
and policies. Do not fold them into the common normal exit. No change to conditions, actions,
fields, cleaners, mark checks or complete ND binding is selected here.

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
creates its Target at the original sink and publishes it at the owning
block's logical normal boundary. These observations do not wait
for a loop to exit normally. Static callbacks keep their original method and instruction identity; the
layout selects the owning block for a point resume. Request, local initial
and parent-prefix scopes remain distinct. A run-1 static shortcut first
publishes at the nearest block boundary. Ordinary parent composition then
reaches the original method's exit-rule/summary path; a block exit is not graph.exitInst.
A shortcut does not create a normal CFG exit from an infinite loop.

Actual method return instructions and handlers retain their physical
ports. Apply real method exit rules once at their real physical boundary
within its owning region. Other block summary admissions apply their own
C5 without those real rules.
A run-1 static shortcut first lifts its block-local dependency through
the existing parent links to the original method scope. It then uses the
original exit-rule/summary handler. Do not insert a block-local initial
directly into the root public store. Terminal/side-effect summary delivery
does not wait for a loop leave and does not invent a normal CFG return.
These existing effect channels are separate from the two ordinary loop
output routes.

Retain internal static/static rows. For example, a local `C.f -> C.g`
relation must reach its internal parent and ancestor through ordinary
summary application. Erase static/static summaries only at the public
method boundary, after the existing real exit processing. Keep the
existing complete static-guidance seed at that public erasure. Erasing
the nearest row first can hide a real exit rule on `C.g`. Applying an
internal or public summary does not register another physical write
point; immediate writer supply still occurs only at the original write.

Use distinct output ports for the two static phases:

```text
raw nearest static-write row:     exit = STATIC_SHORTCUT (-5)
completed real-exit row:          exit = ROOT_EXIT
private real-exit operation input: entry = ROOT_EXIT
```

Carry `STATIC_SHORTCUT` unchanged through ordinary ancestor application.
Only that typed output invokes the original real-exit handler at root.
That handler publishes its completed rows with `ROOT_EXIT`. An ordinary
AL/J result with `ROOT_EXIT` has already executed the real exit rules,
including when its conclusion is STATIC. Apply metadata-only root
finalization to it. Do not infer the phase from the fact base or the
child entry. Otherwise a surviving static result can execute an exit
source or cleaner twice.

`STATIC_SHORTCUT` is not a CFG route or an input permission. It is an
internal output discriminator. Raw run-1 static rows are DEMAND and do
not become native NORMAL records. Their selected handoff reverses the
whole pair exactly: entry `p`, exit `STATIC_SHORTCUT` becomes entry
`STATIC_SHORTCUT`, exit `p`. Only the existing narrow run-2 static Target
result check reads that W/completion pair. Do not create a C2 alias or an
initial at the typed port. The actual private operation still uses its
existing `ROOT_EXIT` input. Completed AL/J rows, public method ports and
ordinary DATA/native scope reversal stay unchanged.

The operation-local static exit continuation must also keep its input
correlation. For example, its outer input can be `C.f/FLOW -> C.g/FLOW`,
while the inner exit-rule initial is canonical `C.g/FLOW`. A real
`CM(C.g,T)` request must refine that waiting outer input too:

```text
Actual FLOW mark check at the normal-exit operation:
    keep existing C.g/T pool interest
    follow registered ROOT_EXIT identity input links: C.g -> C.g
    at the outer C.f -> C.g link, use the existing input request service
    request C.f/T from the actual pool

Genuine reply C.f/T -> C.g/T:
    retain C.f/T as the outer waiting original
    enter each inner continuation under canonical C.g/T
    apply existing C.g/T -> ret/U to obtain C.f/T -> ret/U
```

A reached `C.g/T` alone is not evidence for `C.f/T`. Follow only the
existing matching identity continuation inputs, with exact scope and
initial matching. Do not trace instructions backward, add a static
RequestStorage row, register a writer or create another source. Use a
per-request visited set and cancellation checks; do not keep a global
answered/seen history. With no matching parent input, the existing C.g
point interest still runs.

Register a new local input before enqueuing its actual boundary operation.
That operation performs its mark check before ordinary output deduplication.
Thus a late C.h/FLOW input can request C.h/T even if the canonical C.g
initial and point were handled earlier. An already admitted initial must
not suppress this delivery. A genuine marked reply uses the existing
static-boundary delivery path; ordinary Run1Abstraction still ignores
STATIC inputs. Keep the operation-local canonical C.g/T basis distinct
from the complete outer C.f/T original.

Keep complete existing rule lowering. A static condition at the real exit
has its existing `StaticOperation.MarkInput` and keep transfers. Actual
ZERO control reaching that exit in ordinary AL/J registers the static
consumer there. Its actual pool reply and exit rule can infer the ordinary
`(AL,J) -> ROOT_EXIT` relation. That row guides reverse AL execution to J.
The reserved `(AL,ROOT_EXIT) -> ROOT_EXIT` shortcut row describes only the
exit operation; it is not a replacement for the ordinary AL span. Do not
relabel it, ignore a paired port or add an initial to compensate for
missing form metadata. Both paths use the existing static-condition
machinery and the same original rule/action identity.

The DATA-only method exit adjustment uses the complete method original.
For forward global static drop, select each positive `ContainsMark`
Holds part from the same immutable post-composition value, in the old
sink/mark/leaf order. Append a part even if the ND rule has no complete
witness. Apply the existing `without` fold in that order, then the existing
entry-mark removal. Do not union or reorder masks: removing the last ANY
membership can change the remaining tree's header. Backward adds no
forward static-drop mask. The existing run-1 entry-mark-removal exception
is unchanged. This selector emits no report, source hit, request or join
update; the actual boundary handler already performs those effects.

Keep the reverse publication permission for this shortcut at run-2. A
run-1 local raw writer `ZERO -> C.f/T` with entry `p` and typed exit
`STATIC_SHORTCUT` gives a paired run-2 shortcut demand with entry
`STATIC_SHORTCUT`,
static input `C.f/T`, ZERO output and exit `p`. If an actual run-2 static
initial reaches the source, its `C.f/T -> DemandTarget` result can use
that exact W/completion pair at output `p`. Use the same native paired
restriction and lazy static composition. A registered ZERO-origin writer
derivation is required. Shared static carry or an unrelated normal
demand is not sufficient. This is a result check for the existing static
shortcut, not another DATA input permission or a DATA/native port alias.
It applies only in run-2 backward mode. It does not remap live scopes,
Target handoff metadata or ordinary AP outputs.

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
