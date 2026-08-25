# The growth mechanics: which operation makes the nodes, and what the pattern is

Companion to `2026-08-25-conductor-fact-explosion-trace.md`, which located the mass but not the
operation.

> **Scope, added after the fact:** every measurement below was taken with the `[any]` unroll manager
> **disabled** — `opentaint.anyUnrollLimit` defaults to `-1` and the harness never set it. So these
> are the unbudgeted numbers. Turning the budget on cuts the unroll 62× and makes the analysis
> *worse*; see `2026-08-25-why-the-budget-does-not-help.md`, which is the other half of this story. This answers "how does a fact grow in size" at the level of individual operations, with an
operation-level budget on the real workload, a control that zeroes it, and a deterministic unit
reproducer of the pattern.

**The mechanism in one sentence:** `unrollAnyAccessors` re-roots the node that *carries* the `[any]`
edge — not the `[any]` subtree — under `prefix.c` once per demanded accessor `c`, and 99.4% of those
copies carry an `[any]` again, so the next level extends them by another accessor and the fixed point
is every non-repeating sequence over the demand set.

---

## 1. The four operations that can return more nodes than they were given

Everything else in `AccessTree` is a filter, a rewrap, or a shrink. Measured with a new
`-Dopentaint.apOpDiag=true`, on the one-endpoint/one-rule conductor arm, against the same arm with
the source rule's star removed:

| | | star | no star |
|---|---|---:|---:|
| **A** | `unrollAnyAccessors` — calls | 4,076 | **0** |
| | accessors offered by the demand trie | 79,142 | 0 |
| | materialised (a re-rooted copy) | 20,782 | 0 |
| | **nodes it added to `added`** | **2,681,364** | **0** |
| **B** | `getChild`, the `isCoveredByAny` arm — calls | 58,765 | **0** |
| | nodes returned | 176,295 | 0 |
| **C** | `concatToLeafAbstractNodes` — calls | 5,199,708 | 103,904 |
| | **nodes created** | **131,623,220** | 1,085,069 |
| | nodes created per call | 25.31 | 10.44 |
| **D** | `filterStartsWith` — calls | 1,437,158 | 94,042 |
| | nodes in → out | 70,712,505 → 10,491,071 | 476,661 → 166,703 |
| | calls that grew | 11,324 (0.8%) | 0 |

Read it as three facts.

**A and B do not exist without `[any]`.** Not "smaller" — exactly zero. They are the only operations
in the engine whose existence the star switches on.

**C is where the nodes are physically manufactured**, and the star multiplies it **121×** (and its
per-call yield 2.4×). C is the summary graft: it attaches a callee summary's delta at every abstract
node of the caller's fact. It is downstream of A — the deltas it grafts are answers to premises A
enumerated — but it is where the node count actually lands.

**D is a net shrink and is not a growth source here.** 70.7 M nodes in, 10.5 M out; 0.8% of calls
grow, by 57,233 nodes total, against C's 131.6 M. Earlier notes put weight on `filterStartsWith`
re-prepending its matched spine; as a *node-manufacturing* operation that is not visible on this
workload. (The earlier claim was about premise *length*, which this counter does not measure, so this
is not a refutation of it — but it does rule `filterStartsWith` out as a source of tree size.)

---

## 2. What A actually copies

The request captures `state.added` — the node that **owns** the `[any]` edge — and hands it to:

```kotlin
// TreeInitialFactAbstraction.unrollAnyAccessors
val prefix = ReversedApNode(accessor, unrollRequest.currentAp)
val nodeFilter = prefix.createFilter(typeChecker)
val filteredNode = unrollRequest.node.filterAccessNode(nodeFilter) ?: return@forEachInt

newFacts += filteredNode.withAnyState(childAnyState)
    .addReversedApParents(prefix, unrollRequest.governingAnyId)
```

`unrollRequest.node` is the carrier. `addReversedApParents` hangs **the whole carrier** under
`currentAp.accessor`. Two counters were added specifically to separate the carrier from the `[any]`
subtree, because "unrolling the `[any]`" sounds like it should copy the latter:

| | nodes |
|---|---:|
| carriers copied (summed over materialised accessors) | **3,518,558** |
| `[any]` subtrees under those carriers | **8,152** |

**432× apart.** The single largest event makes it concrete:

```
[A-unroll +62781] re-root carrier (size=62781, anyChild=2) under prefix depth 1 + .<get-default>
                  -> copy size=62781  carriesAny=true
```

A **62,781-node** object re-rooted under one accessor, to unroll an `[any]` subtree of **2 nodes**.

And the copy is unrollable again:

| | count |
|---|---:|
| copies that carry an `[any]` of their own | **20,659 (99.4%)** |
| copies that are `[any]`-free | 123 (0.6%) |

That is the recurrence. Level *k* produces prefixes of length *k*, each carrying an `[any]`; level
*k+1* extends every one of them by another demanded accessor.

---

## 3. The ladder, on real data

The loop that closes the recurrence is **not** the `while (true)` inside `addAbstractInitialFact` —
emissions register with `NO_EXCLUSIONS`, so the new trie nodes offer nothing. It closes through the
engine: `MethodAnalyzer.handleInputFactChange` → `registerNewInitialFact` re-registers an emitted
premise *refined with a non-empty exclusion set*, which is what gives the trie node at that prefix a
demand set for the next round.

Requests and materialisations by prefix depth, i.e. by rung:

| prefix depth | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| requests | 107 | 49 | 40 | 124 | 390 | 883 | 1,940 | 543 |
| **materialised** | 145 | 58 | 262 | 628 | 1,904 | 5,238 | **10,019** | 2,528 |

The ladder reaches depth 7. **48% of all materialisations happen at depth 6**, and levels 2→6 grow by
2.4×, 3.0×, 2.75×, 1.9× — exponential in depth with a base near the effective demand-set size, then a
collapse at depth 7 where the depth budget bites.

The rungs spell exactly what the recurrence predicts — the same prefix with one more demanded
accessor, siblings enumerated at one position:

```
.taskInput.MapValue.tasks.Element.name
.taskInput.MapValue.tasks.Element.taskDefinition
.taskInput.MapValue.tasks.Element.type
.taskInput.MapValue.tasks.Element.forkTasks
.taskInput.MapValue.tasks.Element.loopOver
.taskInput.MapValue.tasks.Element.defaultCase
.taskInput.MapValue.tasks.Element.decisionCases
.taskInput.MapValue.tasks.Element.subWorkflowParam

.workflowDef.tasks.Element.inputParameters.headerValue
.workflowDef.tasks.Element.inputParameters.headerValues
.workflowDef.tasks.Element.inputParameters.MapKey
.workflowDef.tasks.Element.inputParameters.MapValue
```

`.taskInput` is `RerunWorkflowRequest.taskInput`, the attacker-controlled `Map<String, Object>` from
§3 of the trace document. `.MapValue` is `java.util.Map#MapValue : java.lang.Object`, so from that
point the type filter accepts every field in the program — and eight `WorkflowTask` fields are
enumerated as siblings at one position, which is the demand set at that trie node.

B's largest event shows the same erasure from the other side:

```
[B-getChildAny +3] read .partETags off a node that owns an [any]: literal=0 -> returned=3;
                   owner=.[any]![graaljs…#spring-source].$
```

`partETags` is an AWS S3 multipart-upload field. **All 58,765 of B's reads have `literalNodes = 0`** —
every one asks for an accessor the fact does not hold, and gets a synthesised answer.

---

## 4. The pattern, pinned deterministically

`AnyUnrollGrowthPatternTest` (new, 5 tests, all passing) reproduces the recurrence without the
analyzer, against `FactTypeChecker.Dummy` — which is not a convenience but exactly the state the real
checker is in past a `java.lang.Object`-typed edge, where 99.6% of conductor's largest fact sits.

| test | claim |
|---|---|
| `one unroll level offers exactly one premise per demanded accessor` | fan-out width = demand-set size |
| `the unroll re-roots the any-carrying node, so the copy can be unrolled again` | had it copied the `[any]` subtree, `this.a` would hold `![mark]` and nothing else, and there would be no second level |
| `a repeated accessor is not enumerated` | `limitFieldAccess` is the only bound, and it bounds at `N!`, not at infinity |
| `the fixed point is every non-repeating sequence over the demand set` | exact for N = 2, 3, 4 |
| `growth is superexponential in the size of the demand set` | each extra accessor more than doubles the population |

The law, verified exactly:

```
premises(N) = Σ_{k=1..N} N!/(N−k)!        N=2 → 4      N=3 → 15      N=4 → 64
```

Θ(e·N!). This reproduces on the current tree the law recorded from the older `FactExplosionReproTest`,
and ties it to the specific line that produces it.

**Why a depth cap is worth so little** follows directly: truncating at depth K keeps
`Σ_{k=1..K} N!/(N−k)!`, and the last term dominates, so cutting the deepest rung removes most of one
level and leaves the rest. That is the measured 1.58× at K=7 on ThingsBoard, and it is visible here as
the depth-6 rung holding 48% of all materialisations.

---

## 5. The chain, end to end

1. `$*UNTRUSTED` on a Spring handler parameter seeds `arg(i).[any]![mark]` (`StarredPosition.bases()`).
2. A callee's field-read ladder refines the premise it was handed and re-registers it with a
   non-empty exclusion set — the demand set at that prefix (`handleInputFactChange`).
3. The walk hits the `[any]`-carrying node, and `unrollAccessors` offers the demand set.
4. **A** re-roots the whole carrier under `prefix.c` for each `c`. 99.4% of copies carry `[any]`
   again → go to 2, one accessor deeper.
5. Each emitted premise becomes a summary premise; **C** applies those summaries at call sites,
   grafting at every abstract node — 5.2 M applications, 131.6 M nodes, the actual mass.
6. Nothing stops step 3 from offering another accessor, because past a `java.lang.Object`-typed
   edge `typeMayHaveSubtypeOf` returns `true` unconditionally, and 99.6% of the tree is below one.
   The only bound is `limitFieldAccess`'s no-repeats rule, which bounds the enumeration at `N!`.

---

## 6. What is not established

- **Whether C's 131.6 M is all downstream of A.** The 121× ratio between the arms is strong, and the
  largest grafted delta is an A-shaped chain, but no counter attributes a graft to the premise that
  produced its summary. A `[any]`-provenance bit on the delta would settle it.
- **Whether `filterStartsWith` lengthens premises** as an earlier note claimed. Ruled out as a
  source of tree *size*; the premise-length claim is untested either way.
- **Volume counters vary run to run** (`carrierNodes` 2.70 M vs 3.52 M across two runs of the same
  jar) because the run dies on memory at a slightly different point. The *structural* counters —
  `materialisedByPrefixDepth`, `copyCarriesAny`, the carrier/anyChild ratio — are stable to within
  0.02%, and every claim above rests on those.
