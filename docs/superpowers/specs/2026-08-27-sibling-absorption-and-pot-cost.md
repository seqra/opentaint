# Sibling absorption, the pot's cost function, and compressing after `mergeAdd`

Three questions. The first was my error, the second is refuted, the third is built and measured.

---

## 1. The correction: absorb the steps, do not drop the abstraction

What I implemented previously was **deletion**: `AccessTreeAnySuffixMatcher` cancels `isAbstract`
(`thisAbstract = node.isAbstract && !trie.isAbstract`) and the subsumed branch disappears. That is
denotationally exact and it is the wrong operation, for exactly the reason given: the abstract node
is not ours to drop, and the only things an `[any]` can absorb are **covered steps — fields and
elements**.

The right rewrite is at the sibling position, and it **merges** rather than deletes:

```
N{ f -> T , [any] -> S }   ==>   N{ [any] -> (S | T) }        f covered
```

Sound as a widening **of the denotation**: `[any].(S|T)` denotes `<covered>*.(S∪T)`, which contains
`f.T` with the `[any]` taking the single step `f`, and contains the original `[any].S` with it taking
zero. Uncovered edges — taint marks, statics, `[value]`, type-info — are things an `[any]` provably
cannot denote, so they stay as literal edges. `isFinal` is a flag, not an edge, and rides along
untouched.

**And that argument is only half the story — this is the correction that matters.** It holds for the
DENOTATION reader. It is false for the MATCHING reader, which has been the default since literal
`[any]` matching landed: `getChildMatching` keeps `literal(a)` and the zero-step `any().literal(a)`
and **drops the synthesised term**. Absorbing deletes the literal `f` edge, and the zero-step read
then finds something deeper and different — so a premise naming `f` stops selecting that branch.

> **Absorption is a widening of what the fact DENOTES and a NARROWING of what it can MATCH.**

That is the mechanism behind conductor going 2 → 0, and no denotational argument can see it. Pinned
by `SiblingAbsorptionTest.absorption widens the denotation and NARROWS what the fact can match`,
which asserts `delta(fact, premise f)` is non-empty before the fold and empty after.

**Why merging beats deleting, concretely.** A mark at `f.T.![m]` does not vanish; it lands at
`[any].![m]` — one level under the `[any]`, which is precisely where `TreeInitialFactAbstraction`
R3b enumerates. Deletion destroyed that name; absorption *hoists it into view*. Pinned by
`SiblingAbsorptionTest.a mark under a covered sibling is hoisted to directly under the any`.

Implemented as `AccessTree.AccessNode.compressAbsorbCoveredSiblings()`. It is **idempotent by
identity**, which the storage layer requires — every storage decides "already known" with
`merged === stored`, so a pass that rebuilt an unchanged node would make every re-derivation look new
and re-propagate the whole tree. After one pass a node holds its `[any]` plus uncovered edges only,
so the covered-sibling test fails and the node is returned unchanged. Pinned by
`the pass is idempotent by identity`.

Note this is a *different position* from the existing `absorbCoveredByAnyPrefix`, which folds a
covered step **below** an `[any]` (`[any].x.U → [any].U`), only on the grafted delta, and fires 60
times in 29M graft points. The sibling position is the one the redundancy actually lives in.

---

## 2. Is the pot's cost computation wrong? No — but a different bound is broken

The suspicion was that `total` should be *"the sum over all acyclic paths of the path's length"* and
that a wrong cost is why 278 of 298 components sit below a total of 2.

**Refuted, on both halves.**

**What `total` computes.** The only two writers are `mint` (`AnyUnroll.kt:1428`,
`dag.total = satAdd(dag.total, current.pathCount, …)`) and cross-dag fusion (`:934`,
`dx.total = satAdd(dx.total, dy.total, …)`). With no sharing every `pathCount` is 1, so

```
total  =  number of paid-minted transitions  =  number of distinct accessor sequences sold
```

— **one unit per materialised sequence, regardless of its length.** `pathCount` generalises it: a
state reachable by *k* sequences charges *k* for its next accessor, because that one transition
authorises *k* new words. That is the design's stated semantics (§2.6, *"The charge is the path
count, not one"*) and it is pinned by `AnyUnrollManagerTest`: `total` 1 → 2 → 4 with the message
*"emitting `c` at a state two sequences reach authorises `ac` and `bc`, so it costs 2"*. No test,
assertion or comment anywhere in the repo relates `total` to path length.

**Why the intended alternative cannot be used**, in increasing order of severity:

1. **It needs a traversal, which the design forbids.** `AnyUnrollState`'s KDoc is explicit that the
   structure *"must be allowed to become cyclic"* — `while (*) { x = x.a }` over `x.[any].*` writes
   `m --a--> m` — and that *"NOTHING may compute a quantity by traversing the automaton"*. Self-loops
   are not a corner case here: `wouldStay` is **8,962,678 of 11.41M** absorption outcomes, 78.5%.
2. **Magnitude.** Simple-path counting in a general digraph is #P-complete, and even on a DAG the
   count is exponential — the observed 165-state component could carry ~2^80 simple paths. `satAdd`
   would pin every non-trivial pot at `Int.MAX_VALUE`.
3. **It is not monotone, which destroys termination.** `mergeStates` *destroys* states; folding a
   chain into a self-loop would take the acyclic-path sum **down** — the observed `7/1` row would go
   from 7 to **0**. A budget a program loop can refund never terminates. The current measure is a
   count of mint *events*, i.e. of history, which is monotone by construction.

**And the motivating observation does not hold.** For the shipped `PerDag` policy, every mint while
`total < L` charges `pathCount ≥ 1`, and every fusion merges at least one state, giving

> `total < L`  ⟹  `states ≤ total + 1`

Every printed row satisfies it, several tightly (`12/13`, `5/6`, `4/5`, `3/4`). So the **278 pots
below 2 hold at most 2 states and at most 1 transition each** — origins that materialised almost
nothing, not structure the cost function failed to see. The census only prints `states` for the top
12 rows, so its output never contained evidence for the concern either way. Two rows point the other
way, incidentally: `7/1` and `6/2` charge more than any path-structural measure could justify for
one or two states — the doubling signature of `union(x, successor(x))`.

**A real defect did fall out of this.** Design §3.8 claims *"an automaton has at most `L` transitions
and therefore at most `L + 1` states"*. That rested on a read past the limit being **refused**.
`readChild` now mints for free past the limit as `CREDIT`, so nothing bounds a crossed pot's state
count — and the observed `total=200 / states=165` against `L=100` **is that bound failing**. Combined
with 298 live origins, the effective population bound is `L × origins` = 29,800, which the design
already names as its weak point. This is worth fixing independently of anything here.

---

## 3. Compressing the tree after `mergeAdd`

Built: `-Dopentaint.absorbSiblings=true` applies `compressAbsorbCoveredSiblings()` to the result of
every edge-store merge, in both `MethodEdgesFinalTreeApSet` and `MethodEdgesInitialToFinalTreeApSet`,
on the changed path only — the storage identity guard runs first (see the defect list).

It is deliberately **not** gated on the `[any]` manager. The manager's `absorbTargetFor` refuses 82%
of prepends, fires 9 times in 6.59M at `L=100`, and the measured ceiling on opening its kind gate is
+14.5%; gating this rule the same way would make it equally inert. The structural rule needs no
budget because it is a widening, not a materialisation.

**Measured on conductor** (single entry point, single rule, frontier flags, 8 GB):

| arm | rc | wall | events | folded | mass | vulns |
|---|---|---:|---:|---:|---:|---:|
| literal, as shipped | 253 low-memory | 138.0 s | 670,745 | – | – | 2 (1 traced) |
| **+ absorbSiblings** | **0 converged** | **44.1 s** | 368,297 | 411,470 | 1,046,266 | 0 |
| + depth fix (`charge 1`, `ceiling 9`) | 0 converged | 48.7 s | 369,983 | – | – | **2** |
| + depth fix + absorbSiblings | 0 converged | 44.7 s | 329,047 | 231,718 | 773,381 | 0 |

**It works, and it is cheap.** Absorption *alone* converges the arm that otherwise dies of memory at
138 s, folding 411,470 sibling branches carrying 1.05M nodes.

**And it is free everywhere except conductor's witness.** The rule-level suite is **byte-identical**:
688 success, 0 skipped, 0 false positives, and the single `bad-hexa-conversion` false negative that
is present in every arm including the unmodified one. Unit gate 3502 / 2, both pre-existing.

So the operation does not lose flows in general. What it loses is conductor's specific witness — and
§1 now says exactly why, which is sharper than the recorded slogan: **deleting the literal edge
deletes the premise from the fact's matchable set.** `anyTrimAbstract=true`, `anyTrimAbstract=safe`,
`L=0` forced prepend absorption and sibling absorption all converge the run and all report 0, and
they share this one mechanism rather than merely sharing an outcome.

> Shrinking the premise set is safe; coarsening the FACT is not — because under literal matching the
> fact's literal edges ARE its premise set.

**A control worth recording as inconclusive.** Running absorption with `-Dopentaint.literalAnyMatch=false`
(where the rewrite is sound in both channels) does not settle it: that regime has almost no
`[any]`-carrying facts, so absorption fires **15 times** in the whole run against 734,114 under
literal matching. The two readers do not share a fact population, so the workload cannot be used to
A/B the soundness question. The unit falsifier above can, and does.

The depth-gate fix remains the only lever measured to converge conductor **with** its findings, and
it is not a coarsening at all — it fixes a cost function (`[any]` charged 10 against a budget
starting at 3) rather than the facts.

---

## 4. Where this leaves the design

Sibling absorption is worth having: it is sound, idempotent, cheap, invisible to 688 rule tests, and
it removes roughly the whole size problem. It should ship **off** until the conductor witness is
understood, because the honest summary is that it converges the run by making the facts too coarse to
carry that particular flow.

The open question is unchanged and now sharper. Every fold — exact deletion, name-preserving
deletion, prefix absorption, sibling absorption — converges and loses the deep witness, because
premise emission reads the fact's **literal edges**. Until the names R2/R3b need are recorded
independently of those edges, no fact-side compression can be adopted, however sound it is.

Instrumentation: `edgeStore siblingAbsorb folded=… mass=…`. Tests: `SiblingAbsorptionTest` (6,
including the matching-narrowing falsifier), plus `NameCriticalFlagTest` /
`SelfSubsumptionClassifierTest` from the previous round.

**Known defects in this implementation, not yet fixed** (the guard-ordering one was):

1. *Fixed.* Compression ran BEFORE the storage identity guard, so a merge that added nothing could
   still rebuild the node, fail `merged === stored` and re-propagate the whole tree for no new fact.
   The guard now runs first and compression happens only on the changed path.
2. **Not idempotent by identity when an `[any]` sits below an UNCOVERED accessor.** Folding can
   recreate the covered-sibling pattern one level down, and `normaliseUnderAny` only heals the case
   where the intervening accessor is covered. Fix: re-run the fold on the merged `[any]` child, or
   loop to a fixpoint. Turning off `-Dopentaint.anyCollapseNested` would make this common.
3. `SiblingAbsorptionTest` constructs its manager with `anyUnrollLimit = -1`, so the
   `(anyId != null) == containsAnyAccessor()` invariant and all `AnyUnrollState` propagation are
   untested. Add an arm with a non-negative limit.
4. `MethodEdgesNDInitialToFinalTreeApSet` is a third whole-propagating store and is not hooked.
5. Cost: a fresh memo per top-level call, and `k` suffix-matcher rebuilds over a monotonically
   growing subtree when folding `k` siblings. Accumulating the siblings and doing a single merge
   into the `[any]` child would remove the quadratic term.
