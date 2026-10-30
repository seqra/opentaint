# Cached CFG delivery and completed statement results

Status: selected runtime contract, 30 October 2026.
Language: ASD-STE100 Simplified Technical English.

This contract replaces the unchanged queue in AP §8.1 and analyzer-core §4.3.
It implements section 5 of the [selected proposal](../docs/design/bidirectional-demand-stop-static-labels-cfg-delivery-implementation-20261030.md).
It changes result storage and routing. It does not change AP transfer, field
limits, source/sink rules, cleaners, aliases, marks, layers or protection.

## 1. Storage and input

```kotlin
// The result after S, not input to S or input to a successor.
val fresh = edges.add(S, premise, completedResult) ?: return
for (next in successors(S)) deliverAt(next, premise, fresh)
```

All completed ordinary results use this gate. An identity result uses it too.
The existing T2/T4 admission law retains protection and annotation growth.
There is no completed-input cache at a destination. A relevant statement can
receive equal inputs from different producers and evaluate them more than once.
Its equal output is admitted once. A relevant identity loop thus terminates.

InitialFactStore still admits initial identities. Start rules run before input
queueing. Initial and statement-resume inputs do not prepopulate the post-S row.
Call, cleaner, read and boundary resumes keep their exact internal stage.

## 2. Relevance and routing

```kotlin
interface MethodForms {
    // False must certify identity with no effect, check or registration.
    fun isBaseRelevant(direction, statement, base, view): Boolean = true
}
```

The JVM footprint uses normalized operand/result bases. Call footprints also
include STATIC. Reverse write and call footprints include existing alias target
bases. Every boundary and every ZERO fact base is relevant. Noncall read rules
use ZERO and the read lhs. Call rules use bound operand/result/static positions.
Unknown providers keep the default true. Relevance does not bind rules, enumerate
marks, change semantic keys, or depend on the packet's path, mark or premise.

Each actor owns a sparse cache for its method, run, graph direction and rule view:

```text
start instruction index -> base -> immutable destination index array
```

A miss performs FIFO BFS from start over the oriented CFG. Stop each path at
its first relevant instruction. Visit each node at most once in that search.
Keep exceptional edges. A neutral closed component gives an empty array. Cache
that result too. Publish only a complete search; cancellation gives no partial
row. Cache only the queried start, not all visited branch nodes.

A hit sends the unchanged packet directly to each cached destination. ZERO
packets enqueue directly at start without a singleton cache row. Cache rows hold
indices and bases only. Release the cache with its actor context.

## 3. Boundary and static effects

```text
normal statement:
  transfer -> existing cut/cover/hooks -> post-S admission -> cached routing

normal end:
  ordinary transfer -> existing cut/cover/hooks -> exit rules and observations
  -> global/entry-mark adjustment -> bounded completed result
  -> post-S admission -> existing summary normalization and publication

run-1 static shortcut:
  executed writer hooks -> producer-S admission -> enqueue normal-exit input
  -> exit rules and completed result/summary (skip return transfer, as before)
```

End boundaries terminate the oriented method CFG. The generic end node can
have a return transfer. Retain it. A JVM synthetic
normal exit has no return transfer. An exceptional exit makes no normal summary.
A boundary input is not a completed boundary result. An exit-rule static write
finishes the current pipeline and does not enqueue the exit again.

Local writes supply the static pool before result admission. Computed call
results still supply groups before admission, without new write registrations.
Source/sink observations and late-support registrations also precede admission.
Duplicate output cannot hide a distinct rule occurrence or executed write.

## 4. Queue and work reservation

Remove unchanged lanes, repeat keys, their seen set and burst resets. Ordinary
work retains exact ZERO-to-ZERO priority. FULL run-1 retains FLOW-before-TAINT
priority. Keep pending mark cohorts and quantum remainders. Each packed
destination owns a separate mutable remaining-mark wrapper.

Admit once before successor fan-out. Do not yield until all destinations are
queued with work reservations. Cancellation cannot claim completion. The
method-queue-empty barrier still commits requests and static batches as before.

## 5. Correctness and cost

The [constructive Lean package](lean/proposals/selected-work-20261030/README.md)
checks finite BFS frontier soundness/completeness, empty-cycle safety, valid
cache hits and producer admission with annotation upgrades. Each cached delivery
has a neutral-prefix witness in the original CFG. Every original path to a
first relevant node has a destination in the frontier. Identity AP transfer and
no observations on skipped nodes establish path simulation in both directions.
Existing admission algebra establishes unchanged completed result membership.
Repeated observations retain their original identity and annotation merge.

The proof model does not prove the Kotlin adapter. Exhaustive three-node CFG
controls, actor tests, existing transfer tests and real JVM compiled-form
footprint tests bind these laws to the implementation. Project campaign checks
remain required for integration and report identity.

A cache miss costs O(V+E). A hit costs its frontier width. For P packets on a
neutral chain of length L, routing changes from P*L visits to one search and P
deliveries. Cache space is the sum of stored frontier widths. Its worst case is
O(B*V²), for B bases. This contract does not promise lower memory in every CFG.
