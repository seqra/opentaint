# Summary-edge compaction — design proposal

Status: proposal, awaiting approval. Nothing implemented.
Target: the ThingsBoard/SSRF full-scan explosion on `saloed/5-default-get` (`4888917f`).
Supporting measurements: `issue-explore.md`.

## 1. Where the growth is

A summary edge is a triple `(I, F, E)` — premise (initial AP), conclusion (final AP), exclusion.

`pass:` in the debug stats is `passEdges.sumOf { it.factAp.size }` over
`collectAllFactToFactSummariesTo`, i.e. **the sum, over premises, of each conclusion's tree size**.
`collectSummariesTo` emits one builder per stored premise
(`MethodInitialToFinalApSummaries.kt:250-253`), so:

```
pass  =  Σ over distinct premises  |conclusion tree for that premise|
```

The measured 124.7x at a step-matched snapshot is therefore a product of two independent factors:
the **number of premises** and the **size of each conclusion**. They need different mechanisms, and
only one of them has a mechanism today.

**The storage is asymmetric.** `MethodTaintedSummariesGroupedByFactStorage` keys everything by premise:

- `idEdges` (`MethodTaintedSummariesIdStorage`) — a trie over premises, each node holding only an
  `ExclusionSet`. The conclusion is *not stored*; it is reconstructed as exactly `I/*`
  (`:131-137`). This store has real premise subsumption: `NodeSubsumedException` on insert
  (`:97-106`), skip on query (`:108-117`), retroactive `removeChildren` (`:89-92`).
- `nonUniverseAccessPath` (`MethodTaintedSummariesInitialApStorage`) — a trie over premises, each node
  holding a `MergingTreeSummaryStorage` that accumulates that premise's **conclusion** tree. This
  store has **no premise subsumption at all**; it overrides nothing but `createStorage` (`:60-70`).

`compressNode` (`MergingTreeSummaryStorage.kt:59-73`) operates on
`MergingTreeSummaryStorage.edges` — one premise's accumulated **conclusion**. So the only compaction
in the system acts on conclusions, one premise at a time. It cannot reduce the number of premises.

## 2. Why the premise side has no compaction — a result, not an oversight

Summary application (`MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge:19-32`, then
`MethodCallSummaryHandler.handleSummary:104-141`) is:

```
residual = callerFact.delta(premise)
result   = conclusion.concat(residual)
```

The premise is a *prefix pattern*; whatever the caller's fact has beyond it becomes the residual, and
the residual is concatenated onto the conclusion's abstract leaves.

Now consider widening a premise from `p.a` to `p`, for a caller fact `p.a.δ`:

| premise | residual | result |
|---|---|---|
| `p.a` | `δ` | `F.concat(δ)` |
| `p` | `a.δ` | `F.concat(a.δ)` |

These are **different facts**, and neither contains the other. Widening the premise does not
over-approximate the conclusion — it silently shifts what the edge concludes. So premises cannot be
merged while conclusions are held fixed.

**The exception is exact and is the whole reason `idEdges` works.** When the conclusion is the
identity of the premise, `F = I/*`, premise-widening and conclusion-widening move together:

| premise | conclusion | residual | result |
|---|---|---|---|
| `p.a` | `p.a/*` | `δ` | `p.a.δ` |
| `p` | `p/*` | `a.δ` | `p.a.δ` |

Identical. This is exactly why `SummariesIdStorageNode` can afford to store no conclusion at all
(`:131-137`) and why it may legally delete subsumed descendants (`:89-92`).

**Result.** *Premise widening is exact iff the conclusion is the identity of the premise.* The general
condition (`E_{p.a}` redundant given `E_p` iff `a ∉ X_p` and `T_{p.a} ⊑ shift_a(T_p)`, where `shift_a`
appends `a` at every abstract leaf) is the same statement: it requires the conclusion to move with the
premise.

**Consequence.** The compact/expensive split is structural. Premise-side compaction cannot be bolted
onto `nonUniverseAccessPath`, because there the premise and conclusion vary independently. The only
sound way to reduce premise count is to get **more edges into the identity store** — i.e. to improve
the decomposition, not to add a second subsumption mechanism beside it.

## 3. The decomposition, and what we do not know

`addNonUniverseEdge` (`:204-232`) already attempts exactly this, via
`exitAccess.splitOnMatching(initialAccess)` (`AccessTree.kt:506-533`):

- `MatchedWithRemainder` — the identity part goes to `idEdges` (where premise subsumption works), the
  remainder to the expensive store;
- `NotMatched` — the entire edge goes to the expensive store.

`splitOnMatching` returns `NotMatched` when: the premise's accessor chain is not present in the
conclusion tree (`:525-526`); or the node reached is not `isAbstract` (`:529`) — i.e. the conclusion
is strictly deeper than the premise; or that node carries a `deepAccessorExclusion` (`:508`, `:529`).
It also walks with the private `getNodeByAccessor` (`:385-386`, plain binary search), so unlike the
sibling `contains` (`:496` via `getChild`, `:415-433`) it does **not** expand `AnyAccessor`.

**The gap in our evidence.** We do not know which of these three causes dominates for the real summary
edges in this run. The `SSRF_FACT_DIAG` sampling in the diagnostic artifacts recorded *intra-procedural
path edges*, not summary edges, so the shape distribution we have does not describe premises and
conclusions. And there is no counter anywhere for premise count, decomposition outcome, or
`NotMatched` reason — confirmed by an exhaustive search of the logging.

Designing the fix without that measurement would be guessing. The three causes call for three
different changes, and only one of them is cheap.

## 4. Proposal

### Step 1 (prerequisite) — Measure the decomposition

Add opt-in instrumentation to `MethodTaintedSummariesGroupedByFactStorage.addNonUniverseEdge`
recording, per method entry point:

- number of distinct premises in `nonUniverseAccessPath`, and the size distribution of their
  conclusions — this splits the 124.7x into its two factors, which we currently cannot do;
- decomposition outcome per added edge: `MatchedWithRemainder` vs `NotMatched`;
- for `NotMatched`, which of the three causes fired (chain absent / not abstract / deep exclusion);
- premise and conclusion depth, and whether either carries an `AnyAccessor`.

This is the same shape as the existing `SsrfFactDiagnostics` patch (still present, uncommitted, in the
`opentaint-w3-ssrf-default-get` worktree) and reuses the same benchmark harness. It is cheap and it
converts the rest of this proposal from speculation into engineering.

**Everything below is conditional on what Step 1 shows.** The conditions are stated explicitly.

### Step 2A — If `NotMatched` is dominated by "conclusion strictly deeper than premise"

Then the decomposition is working as designed and the edges genuinely are not identity edges. Premise
count cannot be reduced inside the summary storage (§2), and the work belongs upstream, in how many
premises unrolling generates. See §5.

In that case the summary-side work reduces to Step 3 (cost) — worth doing, but not a fix.

### Step 2B — If `NotMatched` is materially caused by the missing `AnyAccessor` expansion

`splitOnMatching` is structural where `contains` is semantic, so a conclusion `p.<any>/*` — which
semantically *does* contain `p/*` — is reported `NotMatched` and sent whole to the expensive store,
losing a premise that could have lived in the compact one.

The sound repair is the match that *ends* on the ANY edge: if the node at `p` has a child
`<any> -> A` with `A.isAbstract` and `A.deepAccessorExclusion == null`, the identity part is
`p.<any>/*` and the remainder is `T` with `A` replaced by `A.removeAbstraction()`. This preserves the
exact decomposition invariant `spine ⊔ remainder === T` that `reconstructRemainder` maintains today,
because `A ⊒ abstractNode` implies `A.removeAbstraction() ⊔ abstractNode = A`. Cost is one extra
binary-search level. `SummariesIdStorageNode` gains a `Boolean` and a second `ExclusionSet`, kept
separate because `p.<any>/*` is strictly stronger than `p/*` under the merge order.

A match that *traverses* the ANY edge is **not** repairable: the decomposition needs
`spine(p) ⊔ R === T`, but `spine(p)` has a concrete `p`-child that `T` lacks, so the join overshoots
for every `R`. The exact difference would need "abstract except one accessor at position 0", and
`AccessNode` offers only `isAbstract` and `DeepAccessorExclusion` (which forbids an accessor
*everywhere below*). The languages are closed under difference; the node type is not.

**Prerequisite.** `<any>` is a Kleene star whose ε-case is half-built: a node carrying `<any> -> A`
must satisfy `isAbstract ⊇ A.isAbstract` and `isFinal ⊇ A.isFinal`, and nothing establishes it —
not `create`, not `mergeAddStep`. `getChild` compensates for children (`:423`) but never for the
node's own flags, and `getChild(FINAL)` (`:416`) ignores `A.isFinal`, while `splitOnMatching` (`:508`,
`:529`), `contains` (`:498`) and `delta` (`:202`) read the raw flag.
`AccessTreeAnySuffixMatcher` implements the ε-case for `isFinal` (`:101`, `:141`) but stores
`isAbstract` at `:10` and never reads it. Step 2B is unsound until this is closed.

### Step 3 — Cost reductions, valid unconditionally

These change no results and are worth landing regardless of Step 1's outcome. They target the measured
44.4% of retained heap sitting in the summary-edge pathway, and the top of the CPU profile.

**3a. Hoist the interner.** Each `MergingTreeSummaryStorage` owns a private `AccessTreeSoftInterner`
(`:13`), so conclusions of sibling premises never share structure even when structurally identical —
and with many premises drawn from one accessor pool they overlap heavily. Hoist it to the group or to
`TreeApManager`. Zero precision cost, and it makes `countNodes()` (DAG) a meaningful unit for any
future budget, in place of the unfolded `size` the current threshold uses.

**3b. Memoize the ANY matcher.** `AccessTreeAnySuffixMatcher` is on the hot path of every
expensive-store add, because `foldToAny` defaults to `true` on `mergeAdd`/`mergeAddDelta`
(`AccessTree.kt:815`, `:854`) and `MergingTreeSummaryStorage.add` calls `mergeAddDelta`. Its trie
construction (`:64-110`) and `getNonMatchingNode` (`:113-152`) both recurse with no visited set and no
memo — O(*unfolded* size) — and a fresh matcher is allocated per merge pair (`AccessTree.kt:981`,
`:990`). Memoize on `(TrieNode identity, AccessNode identity, prefixCoveredByAny)`, following the
existing `AccessNodeMergePair` pattern (`:803-813`), and change the structural `!=` at
`AccessTreeAnySuffixMatcher.kt:133` to `!==` (the function returns the identical node when unchanged,
`:149`, so identity is exact and strictly cheaper than `AccessNode.equals`, which recurses via
`contentEquals`).

This is a constant-factor and repeated-work win, not a complexity fix: trie states are
`(node, failureLink)` pairs, so state count stays tied to unfolded size, and the exact problem
underneath is NFA language inclusion. The matcher is a deliberate one-sided approximation; do not try
to make it exact.

## 5. If the premise count is the dominant factor

Then it is not a summary-storage problem. The premise count is an *input*: `TreeInitialFactAbstraction`
emits one abstract premise per unrolled path (`:82-97`), and each becomes its own trie node and its own
`MergingTreeSummaryStorage`. §2 shows the storage cannot merge them.

Premise count is set by how many paths unrolling generates, which is governed by
`TaintAnalyzer.unrollStrategy` together with `JIRFactTypeChecker`'s filter. That filter is currently
inert on model paths: every field modifier in `model/java/config` declares
`fieldType = java.lang.Object` (9,381 of 9,381), which makes `typeMayHaveSubtypeOf` vacuously true
(`JIRTypes.kt:83`), so a path may step from any class's field to any other class's. Combined with the
no-repetition invariant (a field occurs at most once per path, `AccessTree.kt:443`, `:625-639`,
`:1461-1489`), the generated set is the permutations of a large accessor alphabet rather than a
recursive closure. Full analysis and a failing characterization test are in `issue-explore.md`.

## 6. Constraints any change must satisfy

- **No `AnyAccessor` in a conclusion.** `AccessNode` init adds `depth += 10_000` when one is present
  (`AccessTree.kt:307-309`) and `edgeExceedLimit` delays `factAp.depth > factDepthLimit + 2`
  (`MethodAnalyzer.kt:591-595`) where the limit starts at 3 and rises by one per resume round
  (`TaintAnalysisUnitRunner.kt:356`). Such an edge is delayed ~forever. Premises are unaffected
  (`AccessPath.depth = size`).
- **Removal must re-emit in the same `add`.** Propagation is delta-only and subscription is
  register-then-pull-once (`SummaryEdgeSubscription.kt:792-795`, `:118-128`); there is no re-scan.
  `MergingTreeSummaryStorage` already models this correctly by setting `edgesDelta` to the whole tree
  on compression (`:36`).
- **Mutations must be publish-safe single field writes.** Writers are synchronized, readers are not;
  `removeChildren` writes `children.put(accessor, null)` and readers null-check
  (`AccessBasedStorage.kt:120-136`).
- **Idempotence.** The stored set is replayed through the same `add` on cache load
  (`MethodAnalyzer.kt:215-230`).
- **No `Universe` exclusions** (`Edge.FactToFact.init`, `Edge.kt:88-92`). `Empty` is widest; the
  widening join on exclusions is intersection.
- **Three AP modes share the `Storage` contract**; keep changes inside Tree.

## 7. Test plan

There are currently **zero** direct tests of `MethodInitialToFinalApSummaries`, `CommonF2FSummary`,
`SummaryEdgeStorageWithSubscribers`, `FactToFactEdgeBuilder` or `Edge.FactToFact`. This work should
ship the first.

1. *Decomposition exactness* — for every `MatchedWithRemainder`, assert `spine ⊔ remainder === T`.
   This is the invariant Step 2B extends, and it is untested today.
2. *Premise-widening exactness* — encode §2 directly: for an identity conclusion, assert that the
   `p` edge and the `p.a` edge produce the same fact for caller `p.a.δ`; and assert the converse for a
   non-identity conclusion, so the boundary is pinned rather than assumed.
3. *Delta completeness* — assert the union of emitted deltas equals `collectSummariesTo` at every step
   (this is what §8 suspects is already violated).
4. *Idempotence* — feed `collectSummariesTo` back through `add`; assert no deltas.
5. *No ANY in conclusions* — direct guard for §6's first constraint.
6. *`AccessTree` no-field-repetition invariant* — prepend a field already present deeper; assert no
   path contains it twice. This invariant is load-bearing throughout and has no test (the element
   analogue has a runtime `check` at `:611-613`; the field analogue has none).

**Existing suites that must stay green:** `DeepCleanSummaryAnalysisTest` (emits two summary edges from
one initial fact), `CleanerFieldSensitivityAnalysisTest` (four non-vacuity tests catch *dropped*
edges), `AnyFieldMarkExclusionTest`, `DeepAccessorExclusionTest`, `CleanerDslControlFlowAnalysisTest`,
`CleanerDslAnalysisTest`, `StarOperatorTest`, the Go trace suites (they assert `traceResolved`
separately from `vulnerabilityReported` — the only coverage of the backward reader), and the ND suites
as a blast-radius check.

**Benchmark gate:** the existing isolated harness
(`opentaint-w3-benchmark-results/post-rebase/run-measurement.sh`, 12 GiB, 300 s IFDS timeout, quiet
gate). Success is measured at a *step-matched* snapshot on premise count and retained heap — not on
wall time, which the timeout censors.

## 8. Latent bug found during analysis (independent of this proposal)

`MethodTaintedSummariesMergingStorage` merges exclusions with `union` (`:271`) while
`MethodTaintedSummariesIdStorage` uses `intersect` (`:150`). Since larger exclusion means narrower
edge, union *narrows* the stored edge on every merge:

- the pull path (`summaries()`, `:292-299`) returns the narrowed exclusion while earlier subscribers
  already received the wider one via deltas, so `collectSummariesTo` can be **strictly weaker** than
  the union of past pushes — late subscribers and reloaded caches then see a weaker set;
- when the conclusion is unchanged but the exclusion grows, `add` returns `true` (`:279`) yet
  `getAndResetDelta` returns `emptySequence()` (`:282-283`).

Cactus does the opposite, re-emitting the whole edge on an exclusion change
(`access/cactus/MethodInitialToFinalApSummaries.kt:114-119`), pinned by
`CactusAccessTest."cleaner change re-emits the complete access value"`. The tree side has no
equivalent test. Worth filing separately; test 3 above would catch it.

## 9. Open questions

1. Was the `union` at `MethodTaintedSummariesMergingStorage.kt:271` deliberate? If so, what is the
   argument that the pull path may be weaker than the deltas already delivered?
2. Is the half-built `<any>` ε-closure a known gap or an oversight?
3. The `depth += 10_000` encoding effectively bans `AnyAccessor` from conclusions, which is what forces
   unrolling to concrete paths and thus multiplies premises. Is that deliberate policy or an
   expedient? If ANY-bearing conclusions could propagate under a separate budget, the compact
   representation would become usable and §5 would change shape entirely. Larger than this proposal,
   but it is the one lever that would make conclusion-side widening available at all.
