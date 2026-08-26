# Conductor's fact explosion: the whole chain, and where each claim is measured

Index and synthesis for the five documents written on `saloed/31-any-unroll-manager-design` on
2026-08-25. Read this one first; each section says which document holds the evidence.

> **Superseded for `anyUnrollLimit = 100` by
> `2026-08-25-conductor-fact-explosion-at-L100.md`.** Everything below is the `L = -1` arm, where the
> unroll is the mechanism and the run dies of memory. At `L = 100` the unroll is 0.001 % of the node
> mass, the run dies of the clock instead, and the binding constraint turns out to be a throughput
> collapse rather than either. Read that document's §2 before reusing links 2–5 here.

**One endpoint and one taint rule exhaust 8 GB on conductor.** Not the 66-rule ruleset, not 107
handlers — one `@PostMapping` method and one join rule.

| document | question it answers |
|---|---|
| `2026-08-25-conductor-fact-explosion-trace.md` | where the mass is, and the trace from the source rule to the statement |
| `2026-08-25-any-unroll-growth-mechanics.md` | which operation manufactures the nodes, and the recurrence |
| `2026-08-25-why-the-budget-does-not-help.md` | why the `[any]` budget stops the unroll and the work stays |
| `2026-08-25-why-concat-grows-the-fact.md` | what one summary graft does and why the result is 5× its input |
| `2026-08-25-the-delta-concat-round-trip.md` | the `arg0.[any].*` + `arg0.a.*→ret.a.*` round trip: real, and a fallback |

Harness (durable, outside the repo):
`/drive-testcomp/opentaint-go-rules/opentaint-w3-benchmark-results/scoped-harness/` — `README.md`,
`scoped-run.sh`, `buildjar.sh`, `gate.sh`, `rulesets/`.

---

## The chain

**1. The source is a whole-object star on a Spring handler parameter.**
`spring-untrusted-data-source` matches `$TYPE $*UNTRUSTED` on every `@GetMapping`/`@PostMapping`/…
parameter, and `StarredPosition.bases()` turns each star into two positions, so each parameter is
seeded with `arg(i)![mark]` **and** `arg(i).[any]![mark]`.

*The control that makes this causal:* the same run with `$*UNTRUSTED` → `$UNTRUSTED` **converges in
38.6 s** instead of exhausting 8 GB — IFDS phase 3.5 s against 2 m 53 s, `walkStates` 404× lower,
`anyDescents` 11.6 M → 0. It also loses both findings, so this is the familiar sound-but-lossy
boundary, not a free win.

**2. A 3-node fact emits 42,074 premises.** `arg(1).[any]![spring-source].$` — three nodes, submitted
**once** — emits 42,074 summary premises. Across the run, 233 of 11,226 bases carry an `[any]`; they
hold 1.5% of all nodes and produce **47% of every premise emitted**.

**3. The generator is `unrollAnyAccessors`, and it copies the wrong thing.** It re-roots the node
that **carries** the `[any]` edge — not the `[any]` subtree — under `prefix.c`, once per demanded
accessor. Carriers copied: **3,518,558 nodes**; the `[any]` subtrees under them: **8,152**. 432×
apart. One event re-roots a **62,781-node** carrier to unroll an `[any]` subtree of **2**.

**4. The copy carries an `[any]` again — 20,659 of 20,782 (99.4%)** — so the next level extends it.
The loop closes through `MethodAnalyzer.handleInputFactChange` → `registerNewInitialFact`, not
through the `while (true)` inside `addAbstractInitialFact`, whose emissions register with
`NO_EXCLUSIONS` and offer nothing. Measured ladder: prefix depths 0–7, **48% of materialisations at
depth 6**. Fixed point: **every non-repeating sequence over the demand set**, `Σ N!/(N−k)!` — pinned
exactly at N=2→4, N=3→15, N=4→64 by `AnyUnrollGrowthPatternTest`.

**5. Nothing stops it, because past a `java.lang.Object` edge the type filter accepts everything.**
`typeMayHaveSubtypeOf` returns `true` unconditionally for `Object`. 15% of field edges in the largest
fact declare `Object`, and **99.6% of its nodes sit below one**. The erasers are mostly *modelled*:
`java.util.Map#MapValue#java.lang.Object`, and `java.lang.String#<serialized-value>#java.lang.Object`
from the Jackson/snakeyaml/fastjson models, which hangs an `Object` child off **every tainted
String**. The untracked `JIRFactTypeCheckerUnrollFilterTest` already pins this; its two `Object`
cases are the gate's two standing failures.

**6. The mass lands in the summary graft, not the unroll.** `concatToLeafAbstractNodes` creates
**131.6 M nodes** against the unroll's 2.7 M — the unroll is **2%**. And the graft is not
multiplicative: it receives the callee's small **conclusion** (6.3 nodes) and the caller's
**remainder** below the matched premise (23.6 nodes = **53% of the caller's whole fact**, because
premises average **1.35 links** against facts 13–17 deep), and 78% of grafts attach at exactly one
point. **A summary application does not summarise the caller's fact; it re-roots it.** Result /
receiver = 4.8×, 10.32 genuinely new distinct nodes per call, 6.0 M calls.

**7. All static state is one access-path base, broadcast to every callee.** `data object ClassStatic`
is a singleton; the synthetic `__spring_registry__` (one static field per Spring bean) hangs off it,
so the whole DI graph is one object; and `JIRMethodCallFactMapper` copies a `ClassStatic`-based fact
into every callee with no reachability test. **147 distinct methods each hold a ≥5,000-node `<static>`
tree**, including `WorkflowModel#getWorkflowName()` (53,361 nodes).

**8. 98.4% of one accumulator's growth enters at one statement** — `WorkflowExecutorOps.java:1891`,
the recursive `rerunWF(subWorkflowId, taskId, taskInput, null, null)` — and **75% of those 10,218
arrivals add no new node at all**.

---

## Why the budget cannot fix it

The `[any]` manager does exactly what it was designed to do. At `L=100`: `maxPotTotal=100` (the
limit, exactly), `maxPotRefusals=45,281`, unroll materialisations **20,782 → 333 (62×)**, ladder
depth 7 → 5, and the coarse `[any]` premise emitted instead.

And both budgeted arms are **worse**:

| | off (default) | `L=100` | `L=0` |
|---|---:|---:|---:|
| **A** unroll → nodes into `added` | 2,681,364 | 1,397 | **0** |
| **B** `getChild` `[any]` synthesis — calls | 58,765 | 202,316 | **27,883,524** |
| **C** `concat` → nodes created | **131,623,220** | **138,410,824** | **136,023,638** |
| **C** nodes per call | 25.31 | 76.30 | **101.67** |
| exit / progress | 253 @ 209 s, 2.10 M | 254 @ 280 s, 872 k | 254 @ 309 s, 770 k |

**A goes to zero; C is conserved to within 5%.** Findings stay at 2 in all three arms — lossless and
useless at once.

**There are two ways to spend an `[any]`, and they are alternatives.** *Unroll it*: concrete
accessors up front, a factorial premise population, but concrete facts and a cheap graft (2.72
attachment points, 25 nodes/call). *Keep it*: fewer premises, but every read is a fixed point that
makes no progress, the `[any]` never dies (98.5% of grafts hand it straight through), conclusions
stay abstract so the graft attaches at 16.5 points and costs 4× more. The budget switches from the
first mode to the second.

The round trip `arg0.[any].*` + `arg0.a.* → ret.a.*` ⇒ `ret.a.[any].*` is exactly the second mode. It
is confirmed byte-for-byte by `AnyDeltaConcatRoundTripTest` and appears verbatim on conductor with
`remainderPerFact = 1.00` — and in the default configuration it fires **twice** in a whole run,
because the unroll consumes the `[any]` first. Both exact tree dumps agree from the other side:
**`[any]` edges: 0**.

---

## What a fix would have to touch

Ranked by measured share of the node mass, not by how easy it looks:

1. **`concat`'s inputs** — 98% of nodes. Either make premises long enough to consume the fact (which
   means more premises: the same dichotomy), or reduce the number of summary applications. The
   budget touches neither.
2. **The `Object` erasure** — 99.6% of the tree sits below one such edge.
   `String#<serialized-value> : Object` is the weaker of the two hot modelled erasers and the cheaper
   thing to test first; `Map#MapValue : Object` is genuinely sound and harder to justify removing.
3. **The `ClassStatic` broadcast** — 46% of accumulated nodes, delivered to methods that never touch
   a static. A reachability test on the `ClassStatic` arm is a small change; the trace resolver may
   depend on the unconditional one.
4. **The star sources** — the on/off switch, and the one that costs findings.

Not the unroll budget, and not `filterStartsWith` (measured a net shrink: 70.7 M nodes in,
10.5 M out).

---

## Standing caveats

- **Single samples.** Volume counters vary ~30% run to run because the run dies on memory at a
  different point; the structural counters (`materialisedByPrefixDepth`, `copyCarriesAny`, the
  carrier/anyChild ratio) vary by 0.02%, and every structural claim rests on those.
- **No provenance links C to A.** "C is downstream of A" rests on the 121× ratio between arms, not on
  a counter attributing a grafted node to the premise family that produced it.
- **`depthGain` is not a link count** — `maxDepth` adds `ANY_ACCESSOR_DEPTH_CHARGE = 10` per
  `[any]`-owning node.
- **Entry-point scoping does not scope sources.** Four handlers still fire on the one-endpoint arm,
  and both findings' flows start at handlers other than the selected one.
