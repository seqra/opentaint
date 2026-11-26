# Implementation proposal: backward condition progress (refined MAY seeds)

Status: PROPOSED, 26 November 2026. Base: `saloed/bidirectional` at
`64b8ce57a`. This proposal follows
[impl-proposal-guide.md](impl-proposal-guide.md) and
[proof-guide.md](proof-guide.md).

- Source spec: [backward-condition-progress.md](backward-condition-progress.md):
  - §II.2, the seed layer;
  - §I.3, the capture tree;
  - §II.4, the refinement;
  - §II.5, the progress guarantee;
  - §II.6, the semantic scope;
  - "Gate and checklist".
- Proofs, in `spec/lean/ApSpec/`:

  | Module | Level | Theorems |
  | --- | --- | --- |
  | `BackCondRules.lean` (`BackCond`) | seed layer rule (spec §II.2) | existing |
  | `BackNDRefine.lean` (`BackND`) | capture tree and refinement rule (spec §I.3, §II.4, §II.5) | existing |
  | `BackCondExamples.lean` (`BackCondEx`) | spec examples | existing |
  | `BackCondImpl.lean` (`BackCondImpl`) | implementation of both rules (§4.4, §5.4 here) | 49, new |

  Check: `cd spec/lean && lake build && lake env lean audit.lean`. Only
  `propext` and `Quot.sound` occur.

Line numbers refer to `64b8ce57a`. File paths are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.
`test:` means
`core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/`.
`jvm:` means
`core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/`.

## 0. Summary

| Id | Rule | Where it acts | What changes | Proof |
| --- | --- | --- | --- | --- |
| R1 | Seed layer (spec §II.2) | `engine/RunMethodLocalServices.kt` `seedFact`, `fireSinkSeeds`, `fireTriggerSeeds`; backward runs | A requirement is NORMAL only if its literal is unary and has the `$` tail. An ND `$` literal (K3) gives DEMAND. All other rows keep their layer | `BackCondImpl` §1, §1b |
| R2 | Capture tree and refined seeds (spec §I.3, §II.4) | new `ap/CaptureTree.kt`, new `store/CaptureTreeStore.kt`; capture in forward runs; `driver/Seeds.kt`, `driver/HandOff.kt`; seeds in backward runs | The forward run keeps one field tree per (place, rule occurrence, `[any]` literal). The next backward run seeds this tree in place of the literal (K2, K4, S3, S5). An empty tree gives the CURRENT seed | `BackCondImpl` §2-§6 |

R1 changes the layer of one seed row. R2 changes the shape of four seed
rows and adds forward state. Neither rule touches the forward transfer,
the caps, the hand-off selection or the reports. The landed code has no
switch, no census and no counter.

Not in this proposal: the round argument of spec §II.5 stays argued. The
model has no multi-run form of C2 and C5.

## 1. Decisions that this proposal implements

| Date | Decision | Effect here |
| --- | --- | --- |
| 26 Nov | Prefer MAY with progress. No backward MUST, no new tail kind | R2 seeds DEMAND trees. No new `Tail`, no new `Layer` (§2) |
| 26 Nov | An ND `$` literal gives a DEMAND seed (user correction) | R1 (§4) |
| 26 Nov | Capture tree: meet first, leaves only, one tree | R2 (§5.1, §5.3 (a)) |
| 26 Nov | `$` leaves stay in the tree | `insertCaptureLeaf` keeps `$` leaves (§5.3 (a)) |
| 24 Nov | No switch and no in-code census | §4.3, §5.3: no flag, no counter, no new log field |
| 24 Nov | Never relax the FL+1 caps | A refined seed goes through the CURRENT `Cut.SEED` (§5.3 (g)). No cap changes |
| 26 Nov | A literal cannot be satisfied by a FLOW fact, so no non-`TaintTree` fact is stored (user answer to Q1 of the first revision) | §5.1, §5.3 (a), (b), (d); Lean `nfOne`, `CapConc` |
| 24 Nov | Serve every route | Captures come from ALL completed combinations (§5.3 (d)) |
| 24 Nov | Any change of confirmed or provisional results fails the gate | §8 |

The proposal makes nine calls of its own (§10). The one question of the
first revision is answered (§6).

## 2. Semantic scope

**Changed.**

| Change | Rows | Rule |
| --- | --- | --- |
| An ND `$` sink seed: NORMAL → DEMAND | K3 (and K7 for an ND `$` literal) | R1 |
| An `[any]` sink seed: the literal → its capture tree, DEMAND | K2, K4 | R2 |
| A reversed `[any]` source literal: the literal → its capture tree, DEMAND | S3, S5 | R2 |
| The forward run keeps capture trees until the hand-off | new state | R2 |

**Unchanged.** The forward transfer and the sink check (R2 only reads
their completed combinations). The backward rules S1, S2, S4, S6-S9. The
unary `$` seed (K1). The `[any]` layer (W6). The cleaners and type
filters. The records, their application and views. The hand-off demand
and its selection (ap.md §8.5, F77). C2, C5 and the relative caps. The
field limits and the FL+1 caps. The reports.

**Hidden-change candidates.** S-H1 to S-H3 come from the spec (§II.6).
S-H4 to S-H6 come from this implementation.

| Id | Candidate | Evidence |
| --- | --- | --- |
| S-H1 | The refined seeds narrow the forward demand. A provisional result that only the wider demand made can go away | Not proved. Gate §8 |
| S-H2 | An ND `$` seed makes DEMAND callee rows in place of NORMAL rows | Results expected equal, not proved. Gate §8 |
| S-H3 | The capture trees stay in the heap from the forward run to the end of the next backward run | Not measured. Gate §8 |
| S-H4 | The code reads "unary" on the literal SET of an alternative. An alternative that repeats its `$` literal stays NORMAL (CURRENT). The rule model (`BackCond.reqs`) gives DEMAND for it | `BackCondImpl.Vec.layer_repeat`. The code keeps the CURRENT result, and the seed is MUST (`code_normal_must`) |
| S-H5 | A unary source transfer with an `[any]` literal runs one more `checkMark` per call, after the edge fired | Work only. §5.8 |
| S-H6 | One source tree serves every backward arrival at the reversed source, whatever witness started the route. It holds the inputs of all forward combinations at that source | The tree is inside the literal (`codeSeeds_inside`) and serves each real route location (`codeSeeds_sound`). Same risk as S-H1 |

**Data-class equality and hashing.**

- `Seed.Sink` and `Seed.PredicateSink` do not change. R1 computes
  "unary" in the backward run from the forms (C5). It adds no field.
- `SeedIndex` gets two maps (§5.3 (f)). They are outside the `Seed`
  equality. `SeedIndex` has no equality of its own.
- New key class `CaptureKey(method, statement, rule, literal)`, a data
  class. Its fields have structural equality: `MethodKey`, `CommonInst`,
  `RuleOccurrenceId` (data class, `interp/RuleIdentity.kt:21`) or
  `RuleId` (the legacy sink rule, compared as in `Seed.Sink`), and `Pattern` (data class,
  `ap/Reference.kt:8`). It is not stored in an analysis store.
- A refined seed is a `TaintTree` with a different `root`. Its equality
  and hash include the root (`ap/Conclusions.kt:61-64`). The backward
  stores treat it as a new fact. This is the intended change.

**Behavior on a throw.** The capture stores are run state. A cancelled
run is dropped as today. The hand-off reads the stores only after a
complete run.

## 3. Code facts

The design depends on these facts of the base. Each is a code reading.

| # | Fact | Source |
| --- | --- | --- |
| F1 | Every production sink is a predicate sink with `patterns == predicate.leaves` | `jvm:interp/JIRRuleForms.kt:545` is the only production `SinkRule` constructor |
| F2 | A predicate leaf and a sink literal have a concrete mark. A sink literal has the tail `$` or `[any]` | `interp/RulePredicate.kt:110`, `interp/RuleStatement.kt:29-32` |
| F3 | `checkMark` on a `TaintTree` gives the overlap with the literal: the spine `[any]` leaves whose exclusion admits the literal path, and the subtree at the literal path, with only the matched marks | `ap/MarkCheck.kt:10-36` (`taintOverlap`, `gate.taintMarks`) |
| F4 | A FLOW fact never satisfies a literal. `checkMark` gives `Request` (run 1) or `None`. A rule edge with a concrete premise gives no FLOW result: `flowMarks` is null, so `flowHit` only requests | `ap/MarkCheck.kt:21-26`, `ap/MarkGate.kt:19-20`, `ap/EdgeApplication.kt:129-133` |
| F5 | `isUnary(leaf)` is `leaf ∈ singletons(root)`: LEAF `{leaf}`, OR union, AND intersection. The builder folds `TRUE` and `FALSE` away, and leaves are canonical | `interp/RulePredicate.kt:119-130`, `:166-201` |
| F6 | Legacy sinks (`predicate == null`) and legacy statement conjunctions (`ConjunctiveEdge`) have no production constructor. JVM end facts are empty, so K7 never fires in production | no use in `jvm:`; `jvm:interp/JIRRuleForms.kt:549-551` |
| F7 | `witness` adds the seeds of a sink only on a DEMAND arm, once per call | `engine/RunMethodLocalServices.kt:367-405` |
| F8 | `fireSinkSeeds` reads the seeds at `(core.key, node)` and resolves a `PredicateSink` through the forms at that node | `engine/RunMethodLocalServices.kt:409-425` |
| F9 | The hand-off builds the `SeedIndex` of the next backward run from `result.analyzers.flatMap { it.sinkSeeds }` | `driver/HandOff.kt:86` (`toCompacted`), `:166` (`toBackward`) |
| F10 | `sinkSeeds` and `sourceHits` live on the root `BlockRunState`. A block runtime delegates to the root | `engine/BlockRunState.kt:59`, `:128`; `engine/MethodBlockRuntime.kt:234-235` |
| F11 | `CompletePredicateBinding.inputs[k]` is the input of `leaves[k]`. `Combination` has the same form. `ConjunctionStore.CompleteBinding.inputs[k]` is the input of literal `k` | `store/RulePredicateStore.kt:89-104`, `store/ConjunctionStore.kt:21` |
| F12 | The run-1 origin cube keeps the inputs of each leaf in `support.domains` (leaf → origin → input) | `store/Run1OriginPredicateStore.kt:23-24`, `:72-75`, `:357-364` |

## 4. R1: the seed layer

### 4.1 Definition

```text
layer(requirement of literal p) =
  CURRENT   NORMAL ⇔ p.tail = $                         (normalize makes [any] DEMAND: W6)
  NEW       NORMAL ⇔ unary(p) ∧ p.tail = $
unary(p)  = some alternative of the rule condition has the literal set {p}
  predicate sink   RulePredicate.isUnary(leafIndex(p))                    (F5)
  legacy sink      some SinkRule of the same rule at the statement has patterns ⊆ {p}
```

| Row | Literal | CURRENT | NEW |
| --- | --- | --- | --- |
| K1 | unary `P.$(T)` | NORMAL | NORMAL |
| K2 | unary `P.[any](T)` | DEMAND | DEMAND (R2 changes the shape) |
| K3 | ND `P.$(T)` | NORMAL | **DEMAND** |
| K4 | ND `P.[any](T)` | DEMAND | DEMAND (R2 changes the shape) |
| K5 | unary and ND | as K1 or K2 | as K1 or K2 |
| K7 | trigger seed of alternative `A` | as K1-K4 | as K1-K4, with the NEW layer |

### 4.2 Native code

```kotlin
// engine/RunMethodLocalServices.kt:437-449
private fun seedFact(core: BlockRunState, requirement: Pattern, emit: (Facts) -> Unit) {
    if (!RuntimeDataDomain.base(requirement.fact.base)) return
    core.ap.cancellation.checkpoint()
    core.cut(Cut.SEED, core.ap.zero, core.ops.targetTree(requirement.fact, Layer.NORMAL)) { _, facts -> ... }
}
```

`fireSinkSeeds` (`:409-425`) and `fireTriggerSeeds` (`:427-435`) call it
for each literal, with no "unary" information.

### 4.3 Code changes

(a) `seedFact` takes the layer decision and the capture tree (R2 uses the
tree, §5.3 (g)).

```kotlin
private fun seedFact(core: BlockRunState, requirement: Pattern, unary: Boolean, tree: TaintNode?,
                     emit: (Facts) -> Unit) {
    if (!RuntimeDataDomain.base(requirement.fact.base)) return
    core.ap.cancellation.checkpoint()
    val normal = unary && requirement.fact.tail == Tail.EXACT                    // R1: only K1 is NORMAL
    val literal = core.ops.targetTree(requirement.fact, if (normal) Layer.NORMAL else Layer.DEMAND)
    val seed = refinedSeed(core, literal, requirement, tree)                     // R2, §5.3 (g); null tree: literal
    core.cut(Cut.SEED, core.ap.zero, seed) { _, facts -> /* unchanged body */ }
}
```

For an `[any]` literal the layer does not change: `targetTree` with
`NORMAL` already gave DEMAND (W6).

(b) One lookup of the sink alternatives at a node. It is the CURRENT
lookup of `fireSinkSeeds`, moved into a helper.

```kotlin
private fun sinksAt(core: BlockRunState, node: CommonInst, use: (List<SinkRule>) -> Unit) {
    val call = core.context.callAt(node)
    if (call != null) core.forms.withCall(core.key, node, call) { use(it.sinks) }
    else core.forms.withStartRules(core.key, node) { use(it.sinks) }
}

/** Lean BackCondImpl.legacyUnary: an alternative of the rule has the literal alone (patterns are never empty). */
private fun legacyUnary(sinks: List<SinkRule>, rule: RuleId, literal: Pattern): Boolean =
    sinks.any { it.predicate == null && it.rule == rule && it.patterns.all { p -> p == literal } }

/** Lean Form.single: the predicate flag; an unknown literal is not unary (C4). */
private fun predicateUnary(predicate: RulePredicate, literal: Pattern): Boolean =
    predicate.leaves.indexOf(literal).let { it >= 0 && predicate.isUnary(it) }
```

(c) `fireSinkSeeds`:

```kotlin
override fun fireSinkSeeds(node: CommonInst, emit: (Facts) -> Unit) {
    val core = activeCore()
    val seeds = core.config.seeds
    for (seed in seeds.at(core.key, node)) {
        core.ap.cancellation.checkpoint()
        if (seed is Seed.Sink) sinksAt(core, node) { sinks ->
            seedFact(core, seed.requirement, legacyUnary(sinks, seed.rule, seed.requirement),
                seeds.sinkTree(core.key, node, seed.rule, seed.requirement), emit)
        }
        if (seed is Seed.PredicateSink) sinksAt(core, node) { sinks ->
            val sink = sinks.singleOrNull { it.occurrenceId == seed.occurrence }
                ?: error("A predicate seed must resolve to its frozen rule occurrence")
            val predicate = checkNotNull(sink.predicate)
            for (requirement in sink.seedPatterns()) seedFact(core, requirement, predicateUnary(predicate, requirement),
                seeds.sinkTree(core.key, node, seed.occurrence, requirement), emit)
        }
    }
}
```

(d) `fireTriggerSeeds` (K7): the same layer, no tree.

```kotlin
for (literal in sink.seedPatterns()) {
    core.ap.cancellation.checkpoint()
    core.countTriggerSeed()                                   // CURRENT
    val predicate = sink.predicate
    var unary = false
    if (predicate != null) unary = predicateUnary(predicate, literal)
    else sinksAt(core, node) { unary = legacyUnary(it, sink.rule, literal) }
    seedFact(core, literal, unary, tree = null, emit)
}
```

### 4.4 Properties (Lean, `BackCondImpl` §1, §1b)

| Claim | Theorem |
| --- | --- |
| The code layer is the rule layer (K1, K3, K5), for alternatives without a repeated literal | `code_normal_iff` |
| A NORMAL code seed is MUST, for every condition | `code_normal_must`, `unaryC_must` |
| `legacyUnary` is the set reading `UnaryC` | `legacyUnary_iff` |
| The set reading is `[p] ∈ c` when no alternative repeats a literal | `unaryC_iff_mem`, `eq_single_of_nodup` |
| `isUnary` (`singletons` on the NNF) is the DNF set reading | `Form.single_iff`, `Form.dnf_ne_nil` |
| The predicate flag and the legacy computation agree on the DNF | `Form.single_eq_legacy` |
| Rows K1, K3, K5, `[any]`, a repeated literal, a shared DAG leaf | `Vec.layer_k1`, `layer_k3`, `layer_k5`, `layer_any`, `layer_repeat`, `flag_shared` |

Model and production:

- `Form` is a tree. The code has a DAG. `singletons` of a node depends
  only on its subformula, so sharing does not change the flag.
- `Form` has binary AND and OR. The code has n-ary nodes with `reduce`
  and `flatMap`. An n-ary node is a nest of binary nodes.
- `Form` has no constants. The builder folds them (F5). Only a constant
  root has them, and a constant root gives no literal.

### 4.5 Tests

New `test:BackwardSeedLayerTest.kt`:

1. K1: a unary `$` predicate sink seeds NORMAL.
2. K3: the ND predicate sink `a.$(T) ∧ b.[any](U)` seeds `a.$(T)` DEMAND.
3. K5: `a.$(T) ∨ (a.$(T) ∧ b.[any](U))` seeds `a.$(T)` NORMAL.
4. A predicate whose DNF repeats the literal, `(a ∨ b) ∧ (a ∨ c)`:
   `a.$(T)` NORMAL (S-H4).
5. Legacy sink, two alternatives `[a]` and `[a, b]` of one rule:
   `a.$(T)` NORMAL. One alternative `[a, b]`: `a.$(T)` DEMAND.
6. K7: a legacy ND alternative with an end fact seeds DEMAND for its
   `$` literal.

Existing suites to run: `MethodLocalServicesTest`,
`FieldLimitScheduleAdmissionTest`, `StaticSeedGrammarTest`,
`RulePredicateEngineTest`, `HandOffTest`, `HistoricalPredicateDomainTest`,
`Run1SinkProjectionTest`, `PredicateClosureTest`,
`StaticCatalogIterationTest`. A test that expects an ND `$` seed in the
NORMAL layer changes its expected layer to DEMAND (K3). The commit
message lists each such change.

### 4.6 Cost

One forms lookup per legacy seed per backward run (a predicate seed
already has it). One `indexOf` over the leaves per predicate literal.
K3 can make more DEMAND callee rows per backward run (S-H2).

## 5. R2: the capture tree and the refined seeds

### 5.1 Definition

```text
FORWARD RUN (each run)
  at each COMPLETED combination of a rule occurrence at (method, statement), NORMAL or DEMAND:
    for each input i of an [any] literal p (concrete mark, empty exclusion, not a GROUP mark):
      tree(method, statement, occurrence, p) := insert(tree, meet(normalForm(i), p))
  occurrences: sink predicates, legacy sinks, conditional sources (unary transfer and multi combination)

meet + normal form of a checked input i (F3), relative to the literal path:
  only a TaintTree input is stored: a FLOW fact never satisfies a literal (F4)
  an [any] leaf of i on the spine, exclusion admits     → the literal itself: [any] at σ = []          (meet: input above)
  the subtree of i at the literal path, each leaf at σ  → [any] at σ if the leaf has an any mark,
                                                          else $ at σ                                    (meet: input at or below)
  mark := the literal mark; exclusion dropped

insert(tree, σ, kind)  (Lean BackND.insertLeaf)
  an [any] leaf at a prefix of σ (σ included)           → no change
  kind = $ and a $ leaf at σ                             → no change (an equal leaf is kept once)
  kind = [any]                                           → the subtree at σ becomes one [any] leaf
  kind = $                                               → a $ leaf at σ; the leaves below σ stay

HAND-OFF (forward → backward)
  sink trees: keep a tree only if a seed at (method, statement) has its rule and literal
  source trees: keep all

BACKWARD RUN
  K2, K4  seed(p) = p.base . p.path . tree (the mark of the literal fact), DEMAND    if a tree exists
                    p                                                               otherwise (CURRENT)
  S3, S5  the reversed result of an [any] source literal, if it is the literal fact → the same tree seed
          any other result                                                           → unchanged (C9)
```

### 5.2 Native code

- The completed combinations exist (F11, F12). They go to `witness`
  (sinks) or to the action targets (sources). Their inputs are dropped
  after the callback.
- `seedFact` seeds each `[any]` literal as the whole literal (§4.2).
- The backward source branch (`engine/RunMethodLocalServices.kt:182-190`)
  applies the reversed edge to each leaf. For an `[any]` leaf the result
  is the literal fact, DEMAND (W6).

### 5.3 Code changes

(a) New `ap/CaptureTree.kt`: the key, the insert, the meet and the seed.

```kotlin
/** One field tree per (place, rule occurrence, [any] literal) (spec §I.3). */
data class CaptureKey(val method: MethodKey, val statement: CommonInst, val rule: Any, val literal: Pattern)

/** Lean BackND.insertLeaf on a trie below the literal path. Returns the same object if nothing changes. */
internal fun TaintAlgebra.insertCaptureLeaf(root: TaintNode?, sigma: IntArray, any: Boolean,
                                            exactLeaf: TaintLeaves, anyLeaf: TaintLeaves): TaintNode {
    fun go(n: TaintNode?, d: Int): TaintNode? {                       // null: no change
        if (n != null && n.leaf.hasAny) return null                    // an [any] leaf at a prefix of σ
        if (d == sigma.size) return when {
            any -> leafNode(anyLeaf)                                    // replaces the $ leaf at σ and all leaves below
            n != null && !n.leaf.isEmpty -> null                        // an equal $ leaf
            else -> node(exactLeaf, n?.accessorData, n?.childData)      // the leaves below σ stay
        }
        val child = go(n?.child(sigma[d]), d + 1) ?: return null
        return replaceChild(n, n?.leaf ?: empty, sigma[d], child)
    }
    return go(root, 0) ?: checkNotNull(root)
}

/** One leaf below the literal path, with the literal mark (C10). */
internal fun ApManager.captureLeaf(tree: TaintNode?, sigma: IntArray, any: Boolean, literal: Pattern): TaintNode {
    val mark = MarkSet.EMPTY + (literal.fact.mark as MarkSlot.Concrete).mark
    return taintAlg.insertCaptureLeaf(tree, sigma, any, taintAlg.leaves(mark, MarkSet.EMPTY), taintAlg.leaves(MarkSet.EMPTY, mark))
}

/** Meet first, then the normal form (spec §I.3): insert the leaves of one checked input. */
internal fun ApManager.captureInput(tree: TaintNode?, input: TaintTree, literal: Pattern): TaintNode? {
    var result = tree
    var n: TaintNode? = input.root
    for (accessor in literal.fact.path) {
        cancellation.checkpoint()
        val node = n ?: return result                                                // no overlap: no leaf
        if (node.leaf.hasAny && input.exclusion.admits(accessor))
            return captureLeaf(result, EMPTY_PATH, any = true, literal)              // meet: input above → the literal
        n = node.child(accessor)
    }
    val tip = n ?: return result                                                     // no overlap: no leaf
    taintAlg.forEachLeaf(tip, EMPTY_PATH, cancellation) { sigma, leaf ->              // meet: input at or below
        if (!leaf.isEmpty) result = captureLeaf(result, sigma, leaf.hasAny, literal)
    }
    return result
}

/** The refined seed (spec §II.4): the literal fact with the tree below the literal path (C10). */
internal fun ApManager.treeSeed(literal: TaintTree, literalPath: List<AccessorIdx>, tree: TaintNode): TaintTree {
    val marks = taintAlg.foldAll(literal.root, cancellation).any                       // the literal mark of this run
    val exact = taintAlg.leaves(marks, MarkSet.EMPTY)
    val any = taintAlg.leaves(MarkSet.EMPTY, marks)
    val body = checkNotNull(taintAlg.mapLeaves(tree, cancellation) { l ->
        when { l.isEmpty -> l; l.hasAny -> any; else -> exact } })
    return taintTree(literal.base, Layer.DEMAND, taintAlg.prepend(this, path(literalPath), body), anyTail = Tail.ANY)
}

/** Merge two trees of one key (two analyzers of one method): insert each leaf of b into a. */
internal fun ApManager.mergeCapture(a: TaintNode, b: TaintNode, literal: Pattern): TaintNode {
    var result = a
    taintAlg.forEachLeaf(b, EMPTY_PATH, cancellation) { sigma, leaf ->
        if (!leaf.isEmpty) result = captureLeaf(result, sigma, leaf.hasAny, literal)
    }
    return result
}
```

The checked piece is the overlap with the literal (F3), so the two "no
overlap" returns are not reached. They add no leaf.

(b) New `store/CaptureTreeStore.kt`, in the form of `SourceHitStore`.

```kotlin
/** Forward-run capture trees (spec §I.3). The driver reads them at the barrier, as SourceHitStore. */
class CaptureTreeStore(private val ap: ApManager) {
    private val sinks = HashMap<CaptureKey, TaintNode>()
    private val sources = HashMap<CaptureKey, TaintNode>()

    fun addSink(key: CaptureKey, input: Facts?) = add(sinks, key, input)
    fun addSource(key: CaptureKey, input: Facts?) = add(sources, key, input)

    private fun add(trees: HashMap<CaptureKey, TaintNode>, key: CaptureKey, input: Facts?) {
        if (input !is TaintTree || !captured(key.literal)) return         // a FLOW fact never satisfies a literal (F4)
        val old = trees[key]
        val new = ap.captureInput(old, input, key.literal) ?: return
        if (new !== old) trees[key] = new
    }

    /** Only [any] literals with an empty exclusion and a FULL concrete mark (C7). */
    private fun captured(p: Pattern): Boolean = p.fact.tail == Tail.ANY && p.exclusion == ExclusionSet.Empty &&
        (p.fact.mark as? MarkSlot.Concrete)?.mark?.let { !ap.marks.isGroup(it) } == true

    fun sinkTrees(): Map<CaptureKey, TaintNode> = sinks
    fun sourceTrees(): Map<CaptureKey, TaintNode> = sources
}
```

(c) Wiring, as `sourceHits` (F10):

```kotlin
// engine/BlockRunState.kt, next to sourceHits (:59)
val captures: CaptureTreeStore? = if (binding != null) binding.captures else if (forward) CaptureTreeStore(ap) else null
// BlockRuntimeBinding: val captures: CaptureTreeStore?
// engine/MethodBlockRuntime.kt, next to :234-235
override val captures get() = root.captures
```

(d) Capture sites in `engine/RunMethodLocalServices.kt`. Each site is a
completed combination. Each site captures before the CURRENT body.

```kotlin
// checkSinksAt, predicate branch (:301-311)
{ combination ->
    core.captures?.let { store -> combination.inputs.forEachIndexed { k, input ->
        store.addSink(CaptureKey(core.key, node, checkNotNull(sink.occurrenceId),
            predicate.leaves[combination.leaves[k]]), input.facts)
    } }
    /* CURRENT: edges, witness, fired */
}
// checkSinksAt, legacy non-conjunctive (:324-327)
core.captures?.addSink(CaptureKey(core.key, node, sink.rule, literal), checked.facts)
// checkSinksAt, legacy conjunctive callback (:333-341)
core.captures?.let { store -> combination.inputs.forEachIndexed { k, input ->
    store.addSink(CaptureKey(core.key, node, sink.rule, sink.patterns[k]), input.facts)
} }
// sourcePredicateActionsAt, restricted multi combination (:216-232), inside `if (allowSingle || ...)`
core.captures?.let { store -> combination.inputs.forEachIndexed { k, input ->
    store.addSource(CaptureKey(core.key, node, source.id, selected.leaves[combination.leaves[k]]), input.facts)
} }
// sourcePredicateActionsAt, run-1 cube (:200-214), inside `if (allowSingle || ...)`
cube.forEachInput { leaf, input -> core.captures?.addSource(CaptureKey(core.key, node, source.id, selected.leaves[leaf]), input.facts) }
```

The unary source transfer (`transfer`, `:169-180`) captures once per
call, after the first fired edge. The edge reads the raw facts, so the
capture runs the CURRENT `checkMark` to get the checked piece (S-H5).

```kotlin
fun transfer(pattern: Pattern, multi: Boolean) {
    val tree = if (source.backward) core.config.seeds.sourceTree(core.key, node, source.id, pattern) else null  // (g)
    var captured = source.backward || core.captures == null
    for (action in source.actions) {
        /* CURRENT checks */
        core.ops.applyEdge(facts, premise, edge.edge, statementEdge, core.mode,
            core.collectAfterRun1Policy(at) { _, result ->
                core.sourceHits?.add(core.key, node, edge.forward, action.id)
                if (!captured) {
                    captured = true
                    val checked = core.ops.checkMark(facts, pattern, core.mode, core.unchangedStaticInitial(premise))
                    core.captures?.addSource(CaptureKey(core.key, node, source.id, pattern),
                        (checked as? MarkCheck.Holds)?.facts)                     // no Holds: nothing stored (A7)
                }
                sink(premise, if (tree == null) result else refineReversed(core, result, pattern, tree), action.id)
            }, may = edge.may, ruleAssignment = true)
    }
}
```

In run 1 with `groupTransfers`, `transfer(unary.anchor, ...)` keys the
tree by the anchor. The backward run looks up `predicate.leaves[leaf]`.
If the anchor is not that leaf, the lookup misses, and the backward run
uses the CURRENT seed (C7).

(e) `store/Run1OriginPredicateStore.kt`: the cube gives its inputs (F12).

```kotlin
sealed class ReadyCube protected constructor(val proof: ProofKey, val leaves: List<Int>, val layer: Layer) {
    /* CURRENT members */
    /** The inputs of each leaf of this cube (capture tree, spec §I.3). */
    abstract fun forEachInput(visit: (Int, ConjunctionStore.Input) -> Unit)
}
private class ReadyResult(/* CURRENT */, private val domains: PersistentMap<Int, Domain>) : ReadyCube(...) {
    override fun forEachInput(visit: (Int, ConjunctionStore.Input) -> Unit) {
        for ((leaf, domain) in domains) for (choice in domain.choices.values) visit(leaf, choice.input)
    }
}
// readyCube (:357-364): ReadyResult(key.proof, key.leaves, layer, support.domains) answer@{ ... }
```

(f) `driver/Seeds.kt` and `driver/HandOff.kt`.

```kotlin
class SeedIndex(byPlace: Map<Pair<MethodKey, CommonInst>, List<Seed>>,
                sinkTrees: Map<CaptureKey, TaintNode> = emptyMap(),
                sourceTrees: Map<CaptureKey, TaintNode> = emptyMap()) {
    /* CURRENT members */
    private val sinkTrees: Map<CaptureKey, TaintNode> = Collections.unmodifiableMap(HashMap(sinkTrees))
    private val sourceTrees: Map<CaptureKey, TaintNode> = Collections.unmodifiableMap(HashMap(sourceTrees))
    fun sinkTree(method: MethodKey, statement: CommonInst, rule: Any, literal: Pattern): TaintNode? =
        sinkTrees[CaptureKey(method, statement, rule, literal)]
    fun sourceTree(method: MethodKey, statement: CommonInst, rule: Any, literal: Pattern): TaintNode? =
        sourceTrees[CaptureKey(method, statement, rule, literal)]

    companion object {
        val EMPTY = SeedIndex(emptyMap())
        fun of(seeds: List<Seed>): SeedIndex = SeedIndex(seeds.groupBy { it.method to it.statement })
        /** Forward → backward: the seeds and the capture trees of all analyzers (C2, C3). */
        fun of(seeds: List<Seed>, captures: List<CaptureTreeStore>, ap: ApManager): SeedIndex {
            val byPlace = seeds.groupBy { it.method to it.statement }
            fun seeded(k: CaptureKey) = byPlace[k.method to k.statement].orEmpty().any { s ->
                (s is Seed.PredicateSink && s.occurrence == k.rule) ||
                    (s is Seed.Sink && s.rule == k.rule && s.requirement == k.literal) }
            val sinks = HashMap<CaptureKey, TaintNode>()
            val sources = HashMap<CaptureKey, TaintNode>()
            for (store in captures) {
                for ((k, t) in store.sinkTrees()) if (seeded(k)) sinks.merge(k, t) { a, b -> ap.mergeCapture(a, b, k.literal) }
                for ((k, t) in store.sourceTrees()) sources.merge(k, t) { a, b -> ap.mergeCapture(a, b, k.literal) }
            }
            return SeedIndex(byPlace, sinks, sources)
        }
    }
}
```

`HandOff.kt:86` and `:166` (forward direction only) become:

```kotlin
SeedIndex.of(result.analyzers.flatMap { it.sinkSeeds }, result.analyzers.mapNotNull { it.captures }, shared.ap)
```

The backward → forward hand-off (`sourceSeeds`) does not change. The
trees live in the `RunConfig` of one backward run (F9).

(g) The backward use in `engine/RunMethodLocalServices.kt`.

```kotlin
/** R2 for K2, K4 (seedFact): the tree seed of an [any] literal; the literal otherwise. */
private fun refinedSeed(core: BlockRunState, literal: Facts, requirement: Pattern, tree: TaintNode?): Facts =
    if (tree != null && requirement.fact.tail == Tail.ANY && literal is TaintTree)
        core.ap.treeSeed(literal, requirement.fact.path, tree) else literal

/** R2 for S3, S5: replace the reversed [any] literal by its tree seed. Any other result stays (C9). */
private fun refineReversed(core: BlockRunState, result: Facts, literal: Pattern, tree: TaintNode): Facts {
    if (result !is TaintTree || literal.fact.tail != Tail.ANY) return result
    val plain = result.withoutProtection()
    if (plain != core.ops.targetTree(literal.fact, Layer.DEMAND, core.mode)) return result      // A3 guard
    val seed = core.ap.treeSeed(plain, literal.fact.path, tree)
    return if (result.nonSubsumable != null) seed.withProtection(seed.root, core.ap.cancellation) else seed
}
```

A refined sink seed goes through the CURRENT `Cut.SEED` and the run-2
static validation in `seedFact`. A refined source result goes to the
CURRENT `sink(...)` of `sourcePredicateActionsAt`.

Not changed: the legacy statement conjunctions (`ConjunctiveEdge`) keep
the CURRENT seed (C8, F6). K7 and K8 keep the CURRENT seed (spec
§II.3).

### 5.4 Properties (Lean, `BackCondImpl` §2-§6)

| Claim | Theorem |
| --- | --- |
| The normal form is exact on the literal mark: `*/e` read as `[any]` with `e` | `nf_tail`, `nf_cov` |
| The stored form (`nfOne`) of a concrete input covers each of its locations with the literal mark. An input with the abstract mark is not stored | `nfOne_cov`, `nfOne_shape`, `nfFact_kind` |
| The stored form is a legal capture (concrete mark, `$` or `[any]`) | `ncap_wf`, `mem_ncap`, `nfIn_some` |
| The code tree in arrival order (`foldl`) serves exactly its stored leaves, the same as the rule tree (`foldr`) | `mergeL_cov`, `mergeL_mergeLeaves_cov` |
| Each code leaf is a stored leaf; at most one code leaf per stored leaf | `mergeL_sub`, `mergeL_length` |
| The code seeds serve each real route location (soundness). The capture is concrete (`CapConc`): F4 | `codeSeeds_sound` |
| Each code seed lies inside its literal | `codeSeeds_inside` |
| The code seeds are legal backward seeds | `codeSeeds_legal` |
| G1 and G2 for each code leaf, against the literal and against its input in normal form | `codeSeeds_deepens`, `codeTree_meet` |
| The task form (all completed combinations) gives the code form; more inputs keep it | `codeCaptured_of_forward`, `forwardCaptured_mono` |
| THE BACKWARD CONTRACT AND THE ITERATION THEOREM WITH THE CODE SEEDS | `seedsCover_code`, `B_general_code`, `iteration_general_code` |
| Vectors: C2 cut start, spine exclusion, an abstract-mark input and an input with another mark (not stored) | `Vec.star_start`, `spine_excl`, `flow_none`, `mark_other` |

`B_general_code` closes the open item of spec §II.7 ("the contract for
the tree seeding is argued, not proved"). It holds for the merged tree
without exclusions, in arrival order, with the fallback.

### 5.5 Model and production

| Model | Production | Relation |
| --- | --- | --- |
| A literal list per witness; the capture is `(literal index, input, exclusion)` | A tree per `CaptureKey`; a repeated legacy pattern shares one tree | More inputs per tree: sound by `forwardCaptured_mono`; never wider than the literal by `codeSeeds_inside` |
| `mergeL`: a list of leaves, `insertLeaf` in arrival order | `insertCaptureLeaf` on a trie below the literal path | Case table in §5.3 (a). Equivalence is tested (§5.7 (2)), not proved |
| `meetLit` on `PFact` with the input exclusion | A walk of the checked piece (F3): spine `[any]` with the exclusion check, then the tip subtree | The three cases of the spec meet table: above, at, below. The checked piece has only matched marks (F3) |
| The exclusions are dropped after the meet (`capMeets`) | The tree has no exclusion | Equal |
| `nfOne` of an abstract mark: not stored; `codeSeeds_sound` assumes a concrete capture (`CapConc`) | The store drops a non-`TaintTree` input | Equal. F4 gives `CapConc` |
| `codeSeeds`: the tree, or the literal if the tree is empty | `seedFact` with `refinedSeed`; no tree → the literal | Equal |
| The leaf mark is the literal mark | `treeSeed` re-marks with the marks of the literal fact of the backward run | Equal on one literal (C10) |
| Not modelled | `Cut.SEED`, the run-2 static validation, the protection of S3/S5 results, GROUP mode | CURRENT behaviour, applied to the new seed |

### 5.6 Assumptions

| # | Assumption | Check |
| --- | --- | --- |
| A1 | A sink or source occurrence has the same `(method, statement)` in the forward and the backward run | CURRENT seeds rely on it (F8). Test §5.7 (3) |
| A2 | The input lists of the completed combinations are aligned with their leaves (F11, F12) | Code reading. Test §5.7 (3), (4) |
| A3 | The reversed result of an `[any]` source literal is the literal fact, DEMAND | Guarded (C9). Test §5.7 (5) fails if the guard never passes |
| A4 | The checked piece of `Holds` is inside the overlap with the literal and has only matched marks (F3) | Code reading. Test §5.7 (1) |
| A5 | The stores of one analyzer root have no concurrent writers, as `sinkSeeds` and `sourceHits` | Same owner (F10) |
| A6 | `predicate.leaves` has one entry per pattern (canonical leaves), so `indexOf` finds the leaf | `RulePredicate.Builder.intern` (`interp/RulePredicate.kt:104-113`) |
| A7 | If the edge of a unary `[any]` source literal fires on a `TaintTree`, `checkMark` holds on it | Both match the same pattern on the same facts. Test §5.7 (4) |

### 5.7 Tests

1. New `test:ap/CaptureTreeTest.kt`, the meet and the insert:
   - spec rows m1-m4 and t1-t4, the Lean vectors `star_start`,
     `spine_excl`, `mark_other`;
   - a `FlowTree` or `Reach` input to the store: nothing is stored
     (`flow_none`).
2. In the same file, a property test of the trie against a reference.
   The reference is a Kotlin copy of Lean `insertLeaf` on a list of
   `(σ, kind)`. Random leaves: three fields, depth 3 or less, both kinds,
   random order. Check: the trie leaf set equals the reference list as a
   set, and two orders give the same covered positions
   (`mergeL_mergeLeaves_cov`).
3. New `test:RefinedSeedIterationTest.kt`, end-to-end with
   `bidi.fixtures.DriverFixtures`:
   - program PG of spec §I.2: run 1 stores the tree `{f: [any]}`; run 2
     seeds `x.f.[any](T)` DEMAND; run 3 reports the finding as
     confirmed; run 4 has no witness. CURRENT gives a provisional finding
     in each round;
   - the ND sink of t5: two `$` leaves for `b`; `a.$(T)` DEMAND (R1);
   - an empty tree: the seed is the literal.
4. In the same file, a conditional source:
   - S3 (unary `arg0.[any](U)`, input `arg0.h.$(U)`): the backward run
     emits the tree seed `arg0.h.$(U)` DEMAND at the reversed source;
   - S5 (multi): the same through a restricted `Combination`;
   - run 1 with a multi source: the cube inputs give the tree;
   - A7: each fired unary `[any]` source edge on a `TaintTree` stores a
     leaf.
5. The A3 guard: in the S3 case, assert that `refineReversed` returns the
   tree seed. If the reversed result is not the literal fact, this test
   fails.
6. Extend `test:HandOffTest.kt`: a sink tree without a matching seed is
   dropped; a source tree is kept; two analyzers with one key merge into
   one tree.
7. Run the existing seed suites of §4.5.

### 5.8 Cost

| Site | Volume per run | Work |
| --- | --- | --- |
| Sink capture | each input of a completed combination with an `[any]` literal | a walk of the checked piece; one insert per leaf (depth ≤ field limit + 1) |
| Unary source capture | each `transfer` call of an `[any]` leaf with a fired edge | one `checkMark` and one walk (S-H5) |
| Multi source capture | each emitted combination or cube | one walk per input |
| Hand-off | each capture key | one pruning check; one merge per duplicate key |
| Backward seed | each `(seed, [any] literal)` per backward run | one `treeSeed` (mark fold, `mapLeaves`, `prepend`) |
| Heap (S-H3) | one trie per key | from the end of the forward run to the end of the next backward run |

None of these volumes is measured. The gate (§8) measures time and peak
memory per rule.

## 6. Answered question

**Q1 (first revision): how to store an input with the abstract mark
(FLOW).** The spec said "a FLOW input: the mark of the literal" (§I.3,
line 185) and "an input with the abstract mark gives no leaf" (line 212,
t6). The first revision stored the literal for such an input.

Answer (user, 26 November): a literal cannot be satisfied by a FLOW fact,
so the capture stores no non-`TaintTree` fact. This is code fact F4. A
FLOW fact is never an input of a completed combination, so the capture is
concrete (`CapConc`), and "no leaf" is sound: `codeSeeds_sound` takes
`CapConc` as its hypothesis. The counterexample of the first revision put
a FLOW input in a completed combination; that cannot occur. The spec rows
of lines 185 and 212 and t6 now say this (§9).

## 7. Order of work

1. Commit 0 (with this proposal): `BackCondImpl.lean`, its import in
   `ApSpec.lean`, the spec updates of §9 that do not wait for a
   measurement.
2. Commit 1: R1 code (§4.3) and R1 tests (§4.5). The checks of §8.1.
3. Commit 2: R2 code (§5.3) and R2 tests (§5.7). The checks of §8.1.
4. The measurement of §8.2: R1 alone, R2 alone (on the base, without
   R1), then both. The spec gate is per rule, alone.
5. The updates of §9 that need the measurement.

## 8. Gate

Spec "Gate and checklist" and the decisions of §1. Hold the lock
`/drive-testcomp/opentaint-go-rules/termination-next-20261119/.projects.lock`
for each suite and project launch.

### 8.1 Pre-merge checks

| Check | Pass condition |
| --- | --- |
| Module suite (with the new tests) | 0 failed tests after each commit |
| Jvm suite | 0 failed tests after each commit |
| Rule suite, bidirectional mode | the native success count, 0 false positive, 0 false negative, 0 skipped (the native disabled set) |
| Lean | `lake build` succeeds; `lake env lean audit.lean` reports 0 unexpected axioms |

### 8.2 Measurement

One launch per project and per arm (R1, R2, R1+R2), with the reference
launch of the base. Stirling-PDF gets three launches: its stall depends
on the order of work.

| Check | Expected |
| --- | --- |
| Results | OWASP, Stirling-PDF, Conductor, ThingsBoard: confirmed and provisional results identical to the base |
| Time | Wall time not worse than the base beyond the spread of the base launches |
| Memory | Peak RSS and largest heap after GC (Young/Full only) not worse |
| Effect (R2) | The demand rows of Stirling-PDF `AuthController#login` and its entry point (spec §II.1): they reach zero in some run (requirement AC). Record the forward hand-off rows per run |
| S-H2 (R1) | The DEMAND callee rows per backward run, R1 against the base |
| S-H3 (R2) | A class histogram (`jcmd <pid> GC.class_histogram -all`) at the end of a forward run of Conductor: the `CaptureKey` count and the trie bytes |

### 8.3 Withdrawal

Revert a rule commit when one of these occurs:

- a pre-merge check fails;
- a confirmed or provisional result differs from the base;
- the time or the peak memory of a project is worse beyond the spread of
  the base launches;
- R2: the capture makes peak memory worse (spec gate).

## 9. Spec and model updates

Now (commit 0):

- `backward-condition-progress.md` §I.3, line 185 and line 212, and t6:
  the capture stores only `TaintTree` inputs; a FLOW fact never satisfies
  a literal (F4, Q1).
- `backward-condition-progress.md` §II.4 and §II.7: the contract for the
  tree seeding is proved for the code seeds (`BackCondImpl.B_general_code`).
- `backward-condition-progress.md` §II.5 Limits: add C7 and C8 (GROUP
  anchors and legacy statement conjunctions keep the CURRENT seed).
- `BackCondExamples.ex_t6`: the doc comment says that an abstract-mark
  input gives no leaf; add that the code never meets one (F4).
- `proof-status.md`: add `BackCondImpl`.

After the measurement: the spec header and the "Gate and checklist" with
the commit ids and the measured effect; ap.md §9.2 and interpreter.md
§4.9 (spec §II.6, documented invariants).

## 10. Calls made in this proposal

These are implementation choices. The owner can change each of them.
C1 and C11 of the first revision stored the literal for a FLOW or an
unmatched input. The user decision of 26 November (§1) withdraws them.

| # | Call | Reason | Alternative |
| --- | --- | --- | --- |
| C2 | Capture at all completed combinations during the run; prune sink trees at the hand-off to the seeded `(method, statement, rule, literal)` | The run does not know yet which witness becomes DEMAND. The spec takes inputs from NORMAL and DEMAND combinations | Capture only at DEMAND witnesses: loses inputs of NORMAL combinations at the same occurrence |
| C3 | Keep all source trees at the hand-off | The backward run reads them at each arrival at the reversed source; no seed names them | Prune to the sources that the backward run reaches: not known at the hand-off |
| C4 | A predicate literal that is not a leaf is not unary (DEMAND) | MAY-sound; F1 makes the case empty in production | `check` and fail |
| C5 | The legacy "unary" comes from the forms in the backward run | No new `Seed.Sink` field; `Seed` equality does not change | A `unary` field in `Seed.Sink`, computed in `witness` |
| C6 | The run-1 multi-source cube gives its inputs through a new `ReadyCube.forEachInput` | The domains already hold them (F12); no new state | No capture in run 1 for multi sources: one round of progress later |
| C7 | No tree for a literal with a GROUP mark or a non-empty exclusion; a GROUP anchor that is not a FULL leaf misses the lookup | The backward run is FULL; the model has no literal exclusion | Map GROUP anchors to FULL leaves |
| C8 | The legacy statement conjunctions (`ConjunctiveEdge`) keep the CURRENT seed | Test-only (F6) | Capture them as S5 |
| C9 | A reversed source result is replaced only if it equals the literal fact | Keeps CURRENT for any other shape (A3) | Replace unconditionally |
| C10 | The tree holds the literal mark; the seed takes the marks of the literal fact of the backward run | The forward run can use GROUP mode; the backward run uses its own mark atoms | Store FULL atoms and trust them |

## 11. Checklist and blind spots

```text
[x] Failure class and real trace          spec §II.1
[ ] Ablation                              not done (spec decision: spec and proofs only)
[ ] Native prototype                      not done
[x] Execution site and volume             sites §5.8; volumes not measured
[x] Selected semantic scope               §2 (K3 layer; K2, K4, S3, S5 shape; capture state; S-H1 to S-H6)
[x] Proof scope and model differences     §4.4, §5.4, §5.5 (49 theorems; propext and Quot.sound only)
[x] Withdrawal condition                  §8.3
[x] Gaps                                  Q1 answered (§6)
```

- **Nothing ran.** No prototype and no measurement exist. S-H1, S-H2 and
  S-H3 are open until §8.2.
- **The trie insert is tested, not proved.** The Lean model is a list
  (`mergeL`). §5.7 (2) compares the trie with a list reference.
- **The round argument (spec §II.5) is not proved.** `iteration_general_code`
  proves soundness over rounds, not progress.
- **A7 is a code reading.** If a unary `[any]` source edge fires where
  `checkMark` does not hold, that input gives no leaf. §5.7 (4) checks it.
- **A3 is guarded, not proved.** If the guard never passes, S3 and S5
  keep the CURRENT seed. §5.7 (5) detects this.
- **The capture walk depends on F3.** If `checkMark` ever keeps an
  unmatched mark in the checked piece, the tree can get a leaf that no
  real route needs. It stays inside the literal (`codeSeeds_inside`).
- **GROUP mode in run 1** gives no tree for GROUP-folded source leaves
  (C7). Run 1 uses FULL by default.
- **The ND form of the backward contract** is not proved (spec §II.7,
  unchanged).
