# The `[any]` unroll manager: implementation, measurement, and what conductor's premises are actually made of

Results for `2026-08-24-any-unroll-manager-design.md`, implemented on
`saloed/31-any-unroll-manager-design`.

**Verdict in one line:** the manager is implemented, correct, and measurably working as a mechanism —
and it bounds a mechanism conductor barely uses. The design's own R1 is confirmed. Two unrelated
levers turned up on the way, and both look larger than the budget ever was.

- **Branch**: `saloed/31-any-unroll-manager-design`, six commits, nothing pushed.
- **Gate throughout**: 3433 tests, 2 failures, both pre-existing (`JIRFactTypeCheckerUnrollFilterTest`,
  an uncommitted file that fails identically at `HEAD` — verified in a separate worktree).

| commit | what |
|---|---|
| `4d44e5013` | the manager: two pointer DSUs, the cyclic automaton, the charge, the forced collapse, refusal |
| `990989018` | spec revision 5 — four claims the implementation refuted |
| `5fee9b72c` | the fusion accounting fix, plus ten findings from an adversarial review |
| `d23e5a56e` | summary-premise and TIFA censuses |
| `2e9516297` | the exact `added` DAG dump and the growth trace |

---

## 1. The measurements

Reference numbers are the recorded main-side runs (`cond-e2e/fix2-*`), which two independent builds
agree on. `-Dopentaint.anyUnrollLimit=100` used to mean the per-`(entry point, base)` counter and now
means the per-origin manager, so the same flag on the same project is a direct head-to-head.

| arm | rc | wall | peak RSS | findings |
|---|---|---:|---:|---:|
| thingsboard — old per-base cap 100 | 0 | 166 s | 14.19 GB | **15** |
| thingsboard — no cap | 253 | 341 s | 14.25 GB | **15** |
| thingsboard — manager L=100, broken accounting | 0 | 162 s | 13.89 GB | 14 |
| thingsboard — manager L=100, fixed accounting | **254** | **948 s** | 14.05 GB | 14 |
| conductor — old per-base cap 100 | 253 | 367 s | 9.90 GB | **6** |
| conductor — no cap | 253 | 226 s | 9.75 GB | **6** |
| conductor — manager L=100, broken accounting | 253 | 974 s | 10.05 GB | 2 |
| conductor — manager L=100, fixed accounting | 253 | **835 s** | 9.90 GB | 5 |

The manager is worse than **both** references on **both** projects, on time and on findings.

### What is nonetheless working

Every structural obligation the design set is met, and measured:

- **Origins collapse.** 12,170 mints against 11,482 fusions on thingsboard leaves ~690 live pots.
  R23 feared this would stay at 40k.
- **No propagation site leaks a mint.** `spineRebuild=0, bulkMerge=0, deserialize=0`; every origin
  comes from `prependAnyAccessor` or a chain fold, the only two sites §4.1 says have no predecessor
  in scope. That was R2, the highest-rated propagation risk.
- **Re-derivation is free.** 76% of reads hit an existing transition (58,319 of 76,434).
- **Query callers never charge.** All query reads go through `peekChild`.
- **The branch invariant holds in live trees.** The exact dump (§4) finds at most one `[any]` per
  root-to-leaf path, which is also why `collapses=0` — there is never a nested `[any]` to collapse.
  Step 0's forced normalisation is a no-op on both workloads and costs nothing.

### Why it is worse anyway

**(a) Absorption is not cheaper — the design assumed the opposite.** §5.3 treats refusal as a pure
coarsening with a precision cost. It also has a throughput cost, and on conductor the throughput cost
dominates: `X.[any]` matches strictly more premises than `a.[any]`, so coarsening *multiplies*
subscription matches and summary applications rather than reducing work. 2.15 M absorptions ran
**2.7× slower** than not absorbing.

**(b) Retiring `unrolledFactCount` was premature.** thingsboard converged under it (`rc=0`, 166 s) and
does not under the manager (`rc=254`, 948 s) — and the reference's own no-cap arm shows the counter
was doing the work, not the workload being easy. §1.1b argued the counter was ineffective because
7,347 buckets × 100 is a ~735,000 allowance; empirically ~690 components × 100 ≈ 40,000, a *tighter*
aggregate allowance, does not converge. The cut's **shape** matters more than its size:

| | charges |
|---|---|
| `unrolledFactCount` | once per materialised **fact**, at every position, every time |
| the manager | once per distinct `(state, accessor)` **transition**; re-derivation free by design |

Those coincide only if paths are not re-derived at many positions. Measured: `reusedFree=6,981` of
`12,768` reads — **55% of reads were free** and would each have charged the old counter. R4's "reuse
it free" is the design working exactly as specified, and it is precisely what makes the cut weak per
unit of work.

---

## 2. The accounting bug, and the fix

The first measurement was unmissable: **1,323 transitions across ~690 pots — under two each — and
16,792 of 76,434 reads refused.** Conductor was worse: 220 transitions, 3,076,821 refusals of
4,643,281 reads. Nothing should hit a limit of 100 at that density; the implied charge was ~52 per
transition.

`dag.total += pathCount`, and `pathCount` was summed on every union. **11,482 of 11,625 unions are
cross-dag fusions**, and each merges the two automata's **start states** — so their path counts added.
After *k* fusions into one component the root's count is *k*+1, saturating at `L`, and a component of
a hundred fused origins refused on its *first* new accessor.

That is wrong rather than merely aggressive. Two start states both denote the **empty sequence**, and
the fusion cascade pairs states reached by the *same* accessor sequence in the two automata, so the
merged path set is the union of two sets that overlap by construction:

```
fusion cascade:   pathCount = max(x, y)     -- |S_A ∪ S_B|, sets overlap by construction
same-dag union:   pathCount = x + y         -- different positions, disjoint sequences
```

`dag.total` still sums across a fusion: those are real transitions really paid for, and a fusion means
the two origins were the same origin all along.

Effect: refusals fell 7.5×, absorptions 80× on thingsboard.

---

## 3. Adversarial review findings

An independent review of `4d44e5013` found eleven issues. It explicitly cleared the classes that
would have been fatal — the absorption's soundness split, the branch invariant, `mergeStates`
termination on a cyclic automaton, and `find`'s acyclicity. **Every defect it did find was in the
over-budget direction**, so none could explain a lost finding.

Fixed in `5fee9b72c`:

| # | what | why it mattered |
|---|---|---|
| F4 | `union` short-circuits on `find()` before taking the lock | receiver preference plus stored-reference node identity makes "two objects, one representative" the STEADY state, so every merge of two `[any]` nodes took the per-manager monitor to learn there was nothing to do |
| F1b | union before the trim may substitute a pair | when `trimAnyCoveredAndPushChildren` substitutes, `mergeNodeLoop` never calls `mergeAddStep` for the original pair, so its union never ran — and the trim is exactly what deletes the edge whose state is lost. Fires on every `mergeAdd` with `foldToAny` |
| F1a | `absorbCoveredByAnyPrefix` unions the consumed `[any]` | §4.4 requires it; the graft's absorbing arm is a per-summary-application event |
| F1c | `removeAllAccessorChains` unions a deleted `[any]` chain edge | `[any]` is an ordinary vertex of the accessor graph, so an SCC can contain it |
| F7 | `addReversedApParents` takes the governing state | the one TIFA emission path left unthreaded; minted a full fresh pot when the type filter had already stripped the subtree's `[any]` |
| F2 | the normalisation short-circuits under `AnyAccessorDisabled` | that strategy **throws** rather than returning false, and the normalisation runs from the node factory, which cannot prove an `[any]` edge exists the way `addParentAbsorbingAny` can |
| F5 | `binarySearch` not `indexOf` on the sorted accessor arrays | twice per node build, on the most numerous object in the analysis |
| F9 | the dormant state survives six more wrapper operations | it was carried by four and dropped by the rest |
| F11 | a structurally dead mint bucket removed; `queryReads` KDoc corrected | it counts calls, so "must stay at zero" was never a real gate |

Deferred, with reasons:

- **F6** — `SummariesIdStorageNode.finalAccess` mints an origin that is the concat receiver for *every*
  application of that summary, so it becomes a cross-caller fusion hub and dominates `dagFusions`.
  Sound (pots sum), but it makes effective `L` depend on call-graph sharing. Fixing it means threading
  state through premise-keyed storage, which §6 is emphatic must not happen.
- **F3** — the forced collapse ships on by default and is a coarsening, so `4d44e5013`'s "off by
  default" is true of the budget and overclaims for the representation.
- **F10** — `ConcurrentReadSafeInt2ObjectMap`'s retry loop reads plain fields; pre-existing house type,
  now on a new lock-free path.

---

## 4. Conductor: where the premises actually come from

### 4.1 Summary premises

`-Dopentaint.summaryPremiseDiag`. **76,386 summary premises over 14,811 methods.** Top five:

| premises | id | ap | carry `[any]` | maxLinks | method |
|---:|---:|---:|---:|---:|---|
| **6,278** | 155 | 6,123 | 883 (14.1%) | 10 | `WorkflowExecutorOps#decide(WorkflowModel)` |
| 2,176 | 64 | 2,112 | 504 (23.2%) | 10 | `DoWhile#execute(…)` |
| 1,573 | 42 | 1,531 | 304 (19.3%) | 10 | `WorkflowExecutorOps#terminateWorkflow(…)` |
| 1,531 | 19 | 1,512 | 350 (22.9%) | 10 | `WorkflowExecutorOps#terminate(…)` |
| 1,475 | **1,248** | 227 | 59 (4.0%) | 6 | `virtual java.util.stream.Stream#map(Function)` |

Top 5 = 17.1% of all premises; top 20 = 32.6%. `Stream#map` is a different animal — 85% identity
summaries, almost no `[any]` — so the `virtual` pass-through models are their own population.

Note the existing per-method `sum:` column counts summary **applications**, not premises. A method can
top that list with one premise applied 236,000 times, which is not a population problem at all.

### 4.2 The unroll is not the driver

`-Dopentaint.tifaDiag`, which separates the unroll's refusals from every other refusal:

```
unrollRequests=469  accessorsOffered=1,956  materialised=198  refusedByBudget=0
```

**The manager refused zero TIFA unrolls on conductor.** Of 1,956 accessors offered, 198 materialised;
the rest were dropped by the ordinary filters (unroll strategy, type-checker `Reject`,
`filterAccessNode`, `addReversedApParents`). All 736,040 refusals are in `getChild`'s arm
(`filterStartsWith` / `delta`), not the unroll.

*Methodological note, recorded because it nearly derailed the investigation twice.* An earlier reading
of `tifaFacts=231` as "the unroll is a rounding error" was unsupported — `readsRefused` mixes TIFA's
refusals with `getChild`'s, so 231 could have been a censored number. It was then retracted on the
grounds that it *must* be censored, which was equally unsupported. Only a counter that separates the
two settles it, and the separated counter says the unroll is genuinely small **and never cut**.

### 4.3 The exact tree

`-Dopentaint.tifaDiag` retains the largest `added` and dumps it as a full DAG. For
`<this> @ WorkflowExecutorOps#terminate(WorkflowModel, TerminateWorkflowException)`:

| | |
|---|---|
| distinct nodes | **346** (3,520 edges, 88 distinct accessor labels) |
| `size` (multiplicity) | 32,095 → **93× inflation**; it was never 32k objects |
| structural depth | **16** |
| `maxDepth` field | **127** |
| nodes owning an `[any]` edge | **254 of 335 internal (76%)** |
| `[any]` edges on any one root-to-leaf path | **1** |
| taint-mark edges | 371 (247 grpc-request-source, 124 spring `$UNTRUSTED`) |
| node kinds | 223 abstract, 57 abstract + deep-exclusion claim, 65 plain, 1 final, 11 leaves |
| max out-degree | 82 |

Hottest edges: `.[any]` **254**, `![conductor-grpc-request-sources]` 247, `.MapKey` 188, `.name` 157,
`.type` 138, `![graaljs…#spring-source]` 124, `.Element` 117, `.headerValue`/`.headerValues` 115/115,
`.subWorkflowParam` 108.

`size` counting with multiplicity matters beyond bookkeeping: it drives `INTERN_SIZE_REQUIREMENT =
1_000` and `SIZE_TO_FORCE_INTERN = 100_000`, and is used as a heap proxy. At 93× inflation, "force
intern at 100k" fires at ~1,100 distinct nodes.

### 4.4 The growth mechanism

**1. The initial fact is a whole-object star on a Spring handler parameter.**
`rules/ruleset/java/lib/spring/untrusted-data-source.yaml` marks `$*UNTRUSTED` on every
`@GetMapping`/`@PostMapping`/… handler **parameter**. `StarredPosition.bases()`:

```kotlin
return if (!star) listOf(pos) else listOf(pos, pos.withAnyField())
```

→ `AnyAccessorAfter` → `PositionAccess.Complex(ap, AnyAccessor)`. Each such parameter is seeded with
**both** `arg(i)![mark]` and `arg(i).[any]![mark]`. (The other hot mark,
`conductor-grpc-request-sources`, is *not* a star source — its position is the getter's return value,
exact.) The main ruleset has 279 `$*` occurrences across 22 files; the source-side ones are
concentrated in three.

**2. Whole trees are transplanted into argument slots on a purely syntactic test.**
`JIRMethodCallFactMapper.mapMethodCallToStartFlowFact`:

```kotlin
val argBase = MethodFlowFunctionUtils.accessPathBase(arg)
if (argBase == factBase) { … onMappedFact(checkedFact, AccessPathBase.Argument(i)) }
```

No reachability or aliasing test — SSA base equality. `WorkflowExecutorOps.java:1216` is
`workflowSystemTask.execute(workflow, task, this)`, so once `WorkflowExecutorOps.this` carries a fact
the **entire access tree is copied into `arg(2)` of every `WorkflowSystemTask.execute`
implementation**. This is directly visible in the census: byte-identical 31,802-node / depth-125 trees
for `Noop`, `Wait`, `Switch`, `Join`, `HttpTask`, `Inline`, `Event`, `Decision`, `SetVariable`,
`ExclusiveJoin`, `JsonJqTransform`, `SubWorkflow`, `PullWorkflowMessages`. **`Noop.execute` never
reads `workflowExecutor`** — the whole subtree is dead work.

**3. Growth is entirely caller subscription.** Every captured stack is identical:

```
TreeInitialFactAbstraction.addAbstractedInitialFact        (TIFA:66)
NormalMethodAnalyzer.addInitialFact                        (MethodAnalyzer:267)
TaintAnalysisUnitRunner.submitMethodInitialFact            (:311)
TaintAnalysisUnitRunner.subscribeOnMethodSummaries         (:395)
NormalMethodAnalyzer.handleMethodCall                      (:763)
NormalMethodAnalyzer.propagateFactCallFact                 (:484)
NormalMethodAnalyzer.callStatementStep                     (:389)
```

Not `handleInputFactChange`, not exclusion refinement, not the unroll. A plausible-looking hypothesis
that exclusion refinements re-walk the whole tree via `registerNewInitialFact` was **refuted by these
stacks** — it is a real code path, but it is not what grows this tree.

**4. The arrivals are already huge**: `incoming size=160, 1865, 3694, 6430 …`, ~4,000 per base, each
`rebase`d wholesale. Many add `+0` — pure re-merge cost. Globally `addCalls=1,183,672` against
`addDeltas=365,373`.

**5. `foldToAny = false`** keeps every concrete branch beside the `[any]`s that already denote it.
`TreeInitialFactAbstraction` is the **only** place in the engine that disables the fold, set
deliberately in `aba23d6a6` — the same commit that introduced `[any]`-aware merging everywhere else.
**Do not "fix" it**: `added` must remember concrete arrivals or the walk stops emitting their premises,
which is a lost flow rather than a saved node.

**Net:** a self-amplifying transplant loop on a god object. `WorkflowExecutorOps.this` accumulates a
tree; every internal `this.foo(...)` transplants it wholesale; `foo` summarises; the summary grows the
caller's tree; repeat — with `[any]` from the star source making each tree bushy enough that 76% of
its nodes carry one.

---

## 5. Two levers, neither of which is the budget

### 5.1 `maxDepth` charges per `[any]`-**owning** node, not per `[any]` crossed

```kotlin
depth = accessorNodes.maxOf { it.maxDepth } + 1
if (containsAnyAccessor()) depth += ANY_ACCESSOR_DEPTH_CHARGE   // 10
```

The charge applies to every node on a path that **owns** an `[any]` edge — whether or not the path
descends through it. With 76% of nodes owning one, eleven charges accumulate down a sixteen-link path:
16 + 110 = 126, reported 127.

`maxDepth` is what `MethodAnalyzer.edgeExceedLimit` gates on and what **both** soundness-critical
prefilters in `filterStartsWith` compare against. So conductor's facts are cost-gated as though they
were 127 links deep while being 16, and the resume ladder's `factDepthLimit` must climb past 127 to
admit them.

Charging a path that takes a *sibling* edge is arguably a bug. Before changing it, note the KDoc's
warning that a charge large enough to make the gate unsatisfiable parks every `[any]`-carrying edge
forever.

### 5.2 The star sources, and the transplant test

§14 of the design already named the `$*` markers as the alternative lever, and the census puts numbers
on it: the two dominant marks are 371 of 3,520 edges in the largest tree, one of them a whole-object
star seeded on every Spring handler parameter. The transplant test (`argBase == factBase`, no
reachability) is what turns one god object's tree into ~17,860 `(method, base)` copies.

---

## 6. What is not established

- **Whether the machinery is free when the budget is off.** The `L < 0` arm was queued and not run.
  thingsboard at `L=100` barely binds (3,547 transitions against a ~40,000 allowance) yet runs 948 s
  against the no-cap reference's 341 s, so ~600 s is unexplained by the budget. R3 — `anyId` in node
  identity fragmenting the interner across 10,894 origins — is the standing suspect and §12.7 called
  it the change's binding constraint. **This is the first thing to run before any decision about
  keeping the manager.**
- **Why thingsboard lost `unsafe-reflection` at `ReflectionUtils.java:27`** in the converged
  broken-accounting arm. It was found by both references, absent from a run that reached `rc=0`, and
  the fixed-accounting arm timed out so its count is not comparable. Not explained.
- **Run-to-run stability.** §12.6 has still never been run; every number here is a single sample.
- **thingsboard's premise census.** Only conductor was profiled.
