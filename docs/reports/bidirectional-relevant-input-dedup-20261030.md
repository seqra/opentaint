# Relevant input deduplication after unchanged traversal

Date: 30 October 2026. Runtime: `bb74cef6cf483db167c161020a8a4cca576ca005`.
This is a clarification of the
[Stirling investigation](bidirectional-stirling-small-demand-workload-20261029.md).
No new project analysis was run. The latest project result remains **reached
run-6 / complete run-5 / accepted run-5**. The small test below models run-5.

## 1. Corrected interpretation

The durable method store deduplicates the outputs of relevant transfers at
their successor instructions. It is not a universal input gate at relevant
instructions. An unchanged arrival bypasses that store, even when its target
instruction is relevant. The target can therefore process an equal input again.
Its equal outputs are still rejected by the durable successor store.

Thus the fixed-point argument still applies to stored output memberships.
The evidence does not show equal outputs circulating indefinitely. Nor does
it prove that most of the 1.575 billion unchanged visits in Stirling are
duplicates. The exact-repeat probe was bounded and biased; its 7.75 million
witnesses cannot be extrapolated to a global duplicate fraction or speedup.

## 2. A small diamond is sufficient

The following code shows the control-flow shape. The finite test uses the
production local-copy and return forms, with one neutral node on each arm.
It does not claim to reproduce every JVM instruction of this Java outline.

```java
// Demand: p.$/T -> ret.$/T.
// Submitted fact: p.$/T. C2 emits the valid NORMAL initial p.$/T.
Box example(Box p, boolean b) {
    Box y;
    if (b) {
        y = p;          // Relevant copy; outputs stored at L.
        Stats.left++;   // L: neutral for the marked y fact.
    } else {
        y = p;          // Relevant copy; outputs stored at R.
        Stats.right++;  // R: neutral for the marked y fact.
    }
    return y;           // J: relevant for y; can receive the same input twice.
}
```

Let `F` be the complete relation `p.$/T -> y.$/T`, NORMAL, with empty field
exclusion and no protection. Both branches use the same original premise.
The two copies admit F at different successor nodes, L and R. This is valid
fresh admission in each point store.

```text
changed queue: [(L,F), (R,F)]

1. Pop one branch packet.
   neutral instruction -> addUnchanged(J,F)
   J processes F; return transfer produces ret.$/T
   edges.add(exit, premise, ret.$/T) accepts the first output
   unchanged work drains; seen is cleared
   the other branch packet is still pending as changed work

2. Pop the other branch packet.
   neutral instruction -> addUnchanged(J,F), accepted again
   J processes the same complete F again
   edges.add(exit, premise, ret.$/T) rejects the duplicate output
   no second returned fact is processed
```

Empty unchanged work means the current unchanged traversal is drained.
It does not mean every pending changed packet has completed its own traversal.
Also, deduplicating the output at the exit does not record that F was already
evaluated at J.

The neutral nodes matter. Remove them, so both copies submit their changed
output directly to J. Both then call `edges.add(J, premise, F)`. The second
copy is rejected before J is processed again.

## 3. Production-actor control

The isolated test uses `RunMethodAnalyzer`, `MicroEdgeBuilder.move`, the real
`MethodEdgeStore`, the real `DeltaWorklist`, and the real C2 admission policy
for run-5 with field limit 4. It submits one concrete exact input against the
matching concrete exact demand. There are no calls, aliases, sources, ND rules,
predefined summaries or protection changes in the fixture.

| Control | Visits to J with the marked y input | y input rows stored at J | Processed returned fact | Returned output rows |
|---|---:|---:|---:|---:|
| Copies feed J directly | 1 | 1 | 1 | 1 |
| Neutral node on each arm before J | 2 | 0 | 1 | 1 |

The test asserts equality of both complete J inputs in the second control.
It also asserts closure: another bounded work call performs no more steps.
Both controls pass. This is one test method with two cases, in an isolated
checkout. Production analyzer source is unchanged.

The [data file](data/bidirectional-relevant-input-dedup-20261030.json) embeds
the test source, XML result, build log, actual processed-node trace, source
hashes and independent source-review notes. A full project rerun is not needed
to reproduce this local queue/store behavior.

## 4. What this means for Stirling

The sampled node 464 in PipelineProcessor is neutral for its body fact.
Node 483 is a relevant local copy. That copy emits both its preserved source
and copied local through the durable successor gate. If both outputs are
already present, that repeated traversal stops there. Repeated visits at 464
do not prove that duplicate outputs escape 483.

The same small input can also be processed unchanged at a point before a
later changed arrival first inserts it into that point's durable store.
Thus a fresh stored admission is fresh relative to that store, not necessarily
the first semantic visit to the point. The 6.33 million changed process items
cannot be classified as either all new semantic relations or all duplicates
from the existing counters.

The earlier report establishes large instruction work and exact revisits.
It does not establish which fresh producer feeds every later traversal, or
how much time a longer-lived repeat cache would save. Keep these two possible
optimizations separate:

- Exact duplicate removal avoids repeated evaluations of equal complete inputs.
- Certified neutral routing avoids intermediate visits even for a new input.

The next attribution should record fresh output memberships by producer point
and complete premise, first durable insertions after an earlier unchanged visit,
relevant-input visits versus new successor outputs, and cross-burst neutral
traffic between producer and consumer boundaries. Include path/mark/protection
growth. This distinguishes many required new relations from repeated delivery
of known relations. Do not change the repeat lifetime or add a standing input
cache before its observation and memory contracts are specified.
