# TIFA without unrolling

`saloed/7-fact-explosion-report`, 2026-08-26. Design for `TreeInitialFactAbstraction` (TIFA),
`core/.../ap/ifds/access/tree/TreeInitialFactAbstraction.kt`.

Resolves `2026-08-21-any-premise-design.md` §7 R5 — *"should `[any]` premises be emitted always, or
only past the cap?"* — in favour of **always**.

---

## 1. Vocabulary

TIFA turns a concrete taint fact into **premises**. It returns `(InitialFactAp, FinalFactAp)` pairs:
the premise, and the abstract fact paired with it. The premise is the "if the caller has this at
entry" half of a method summary.

Per `(method, access-path base)` it holds two things:

- **`added`** — the accumulated union of every concrete fact seen at this base. The **supply**.
- **`analyzed`** — a trie over accessor chains. The **demand**. At each node, `exclusions()` returns
  the set of accessors a premise terminating there has been refined against. **`null` means no
  premise has ever terminated here**; an empty set means one has, and nothing has been demanded of it.

Demand grows two ways: a flow function refines a premise (`propagateFactWithAccessorExclude` →
`registerNewInitialFact`), and **every premise TIFA emits registers itself in the trie**. The second
is what makes the walk a ladder — emitting `P` creates `P`'s trie path, so a later walk descends past
it instead of stopping there.

`[any]` denotes **zero or more** steps over the accessors `isCoveredByAny` accepts — in production,
field and element steps only. Write `U` for the rest: taint marks, class statics, type-info
accessors, `[value]`, `[final]`. Nothing in `U` is reachable through an `[any]`.

A premise is a **chain** with no abstraction flag; matching is prefix-based, so the premise `p` means
`p.*`. The `*` is a real object only on the paired fact, where it is the endpoint — and that endpoint
is the **graft point** the summary application needs. A premise whose paired fact is not abstract at
its endpoint has its delta silently discarded.

---

## 2. The rules

At a walk state `(T, N, p)` — trie node `T`, fact node `N`, prefix `p`, `E = T.exclusions()`:

- **R0 — no demand.** `E == null` → emit `p`. Unchanged. On the first walk for a base this emits the
  bare base premise, which matches every fact on that base.
- **R1 — never unroll.** No accessor is ever materialised out of an `[any]` into `added`. The round
  loop, `unrollAnyAccessors` and the one-shot `unrolled` memo all go.
- **R2 — concrete.** For each `a` that `N` holds literally: if `T.child(a) ≠ null` descend; else if
  `a ∈ E` emit `p.a`. Unchanged.
- **R3a — the covered frontier.** If `N` owns an `[any]` and `E ≠ ∅`: if `T.child([any]) ≠ null`
  descend through it with prefix `p.[any]`; else emit `p.[any]`. One edge for everything `[any]`
  covers. The `!enumerateHere` gate is deleted.
- **R3b — the uncovered frontier.** For each `u ∈ U` in `N`'s `[any]` subtree that is demanded
  (`T.child(u) ≠ null` or `u ∈ E`), emit **both** `p.[any].u` and `p.u`, then continue past `u` as
  `abstractNextAccessPath` does. §3.
- **R3c — demanded, covered, not present.** For each `a ∈ E` that `N` does not hold literally, where
  `N` owns an `[any]`, `isCoveredByAny(a)`, and the type filter accepts `a` → emit `p.a`. §4.
- **R4 — the virtual descent.** For a trie child `a` that `N` does not hold literally but whose
  `[any]` can reach, descend with `(T.child(a), N.getChild(a), p.a)`. §4.

### The invariant that makes rules 2 and 3 compose: demand is never consumed

Emitting `p.[any]` answers the demand at that level **for now**. It must not retire it. Worked
example, and this is the case to get right:

```
added = arg0.[any].*        demand at root grows to E = {f}
                            no concrete f under arg0
  ->  emit  arg0.[any]      (R3a)

later a new fact arrives:   arg0.f.g.h.*
  ->  emit  arg0.f          (R2, on the delta)
```

`E = {f}` is still `{f}`; the `[any]` premise registered `root.child([any])`, not anything about `f`;
so when supply catches up with demand, R2 fires on the new delta exactly as if the `[any]` premise had
never been emitted. Nothing may be marked as "already answered" — which is precisely the behaviour the
one-shot `unrolled` memo had and R1 removes. The self-registration at the emission site is the only
de-duplication, and it keys on the **premise**, not on the demand.

The same holds in the other order: R3c may emit `arg0.f` before any fact supplies `f`, and a later
fact that does supply it re-emits nothing, because `root.child(f)` now exists and R2 takes the descend
arm.

---

## 3. Why the frontier splits — R3b

`[any]` covers field and element steps, so a **taint mark is not reachable through it**. A premise
`arg0.[any]` paired with `arg0.[any].*` says "something under `arg0` is tainted" without saying with
which mark, and the mark is the finding. Measured: collapsing the frontier onto `[any].*` loses
conductor's findings **2 → 0**, and the two lost rules are `ssrf` and `path-traversal`
(`2026-08-21-any-premise-design.md` §3.2).

Today that demand is answered by the **hoist** — a walk state that keeps the same trie node and swaps
`N` for the `[any]` subtree, so a mark physically below the `[any]` is reached at the trie level where
the sink registered it. R3b is its replacement, restricted to `U`, which is the only class that needs
it.

**Two edges, not one.** `p.[any].u` denotes `p.u` but does not *match* it: `AccessBasedStorage` enters
an `[any]`-keyed trie child only from the arm that requires the **fact** to carry an `[any]` there, so
a caller whose fact reaches the mark by a concrete path selects nothing. Pinned by
`AccessBasedStorageAnyLookupTest:330`.

`saloed/12-any-unroll-budget` commit `a6e5be532` implements exactly this split and records
**premises 891,654 → 21,828, with 98 engine tests and 237 rule-level tests passing at cap 1** — which
is "never unroll" in all but name. It predates `[any]`-carrying premises, so it had to keep the
premise concrete and fight the endpoint; with `[any]` allowed in a premise,
`createAbstractNodeFromReversedAp` puts the `*` below the `[any]` and that plumbing disappears.

---

## 4. Why the ladder needs R3c and R4

The unroll's real job was never precision — it was putting a **literal child into `added`** so that a
later walk's `forEachAccessor` would route to the deeper trie node. Remove it and emit `arg0.f`
without materialising anything, and no later walk is ever routed to trie node `f`: the abstraction
sticks one level below every `[any]`.

- **R3c** hands out `p.a` the first time `a` is demanded, which registers `T.child(a)`.
- **R4** is what makes the next walk descend there. `AccessTree.AccessNode.getChild(a)` is documented
  as *"the unique point at which a concrete accessor is SYNTHESISED out of an `[any]`"* — for a node
  owning an `[any]` it returns the merge of the literal `a` child, the `[any]` subtree's `a` child,
  and the `[any]` re-installed below. That is exactly the node the unroll builds by copying the
  carrier, without the copy.

A read cannot grow a stored fact: `getChild` assembles its result from subtrees of the receiver and
nothing is merged back into `added`. The unroll's cost was the copy — `carrierPerRequest = 10.72`,
`nodesPerMaterialised = 5.91` — and it is that copy, which still owns an `[any]`, that re-arms the next
round and gives `AnyUnrollGrowthPatternTest` its `Σ n!/(n−k)!` fixed point (4, 15, 64 premises for
demand sets of 2, 3, 4). R4 walks the same shapes and stores none of them.

**R3c is required, not advisory.** `InitialFactAbstractionTest` runs every scenario on both the tree
and automata backends, and eight of them — `any accessor scenario 1…7` and `scenario 36` — assert a
premise naming an accessor that exists in **no** concrete branch of the fact. The automata backend
passes them through exactly this non-materialising emission
(`AutomataInitialFactAbstraction.abstractGraph`), with no round loop and no memo. Rule 1 removes the
tree backend's mechanism and R3c is the only replacement that keeps those eight green.

**Use `peekChild`, not `readChild`.** `getChild` takes a `record` flag choosing between them.
Recording a transition per ladder step would put the walk back inside the `[any]` manager's budget,
which is the coupling rule 1 exists to remove.

---

## 5. Soundness, in four lines

- An **`[any]` premise is emitted only because `added` holds an `[any]`**, and `added` holds it
  because a caller supplied it. The premise is matched by the fact that produced it; a caller whose
  fact is concrete produces a different `added` shape and is answered by R2/R3c.
- Coarsening the paired **fact** is safe in the usual direction: a larger entry state yields a
  superset of derivations — precision, not recall.
- The **base premise always exists** (R0 on the first walk) and matches every fact on that base, so
  no shape can fall through to nothing.
- The **endpoint stays abstract**: `createAbstractNodeFromReversedAp` folds over `abstractNode`, so a
  chain ending in `[any]` yields `p.[any].*` with the `*` below the `[any]`.

---

## 6. What is deleted

`unrollAnyAccessors`, `UnrollResult`, `AnyAccessorUnrollRequest`, `addReversedApParents`; the round
loop; `AccessPathTrieNode.unrolled` and `unrollAccessors`; `enumerateAnyFrontier`/`enumerateHere`; the
hoist state and `AbstractionState.hoistedAny`; the A-unroll diagnostics.

And `AnyUnrollManager.readChildPaidOnly` and `budgetExhausted` — **their only callers are the three
lines this removes**. `readChildPaidOnly` is the engine's only entry point that can refuse, and 99.5%
of `PAID` mints come from it. So after this change `anyUnrollLimit` no longer caps anything: it only
decides whether a `readChild` mint is `PAID` or `CREDIT`, i.e. whether the absorbing prepend may fire.
Say so in its KDoc, or rename it.

Keep a loop, but a different one: re-walk while the last round emitted a **new premise**. It
materialises nothing and terminates because the trie grows monotonically, `[any]` cannot nest, and
each descent through an `[any]` moves to a strictly smaller subtree. Without it a depth-`k` premise
needs `k` triggering events.

---

## 7. Tests

**Must stay green.** `InitialFactAbstractionTest` `any accessor scenario 1…7` + `scenario 36` (R3c);
its 19 `expectedEmpty` scenarios, which tolerate only a size-0 premise — R3a's `E ≠ ∅` guard is what
keeps them green; `AnyPremiseAbstractionTest:142` (no `[any]` premise without demand), `:174` and
`:188` (a mark below an `[any]`, and the zero-times descent — R3b);
`AccessBasedStorageAnyLookupTest:330`; `AnyAccessorCollapseTest:199` (`AccessPath.size` must keep
counting `[any]` as 1); `CleanerFieldSensitivityAnalysisTest` on both backends; `StarOperatorTest`,
whose header says outright that *"a concrete field read only inherits that taint once the
any-accessor is unrolled to a field read"* — R3c + R4 must reproduce that; the Go sample suites,
318 `traceResolved` assertions.

**Must be deliberately rewritten**, visibly in the same commit rather than deleted:
`AnyUnrollGrowthPatternTest:186` and `:202` assert **4 / 15 / 64** premises and superexponential
growth — they pin the explosion, and rule 1 exists to invalidate them;
`AnyPremiseAbstractionTest:159` (`while the base still unrolls no any premise is emitted`) and `:361`,
`:375`, `:417` (the cap); `AnyUnrollManagerTest:316` (`readChildPaidOnly`'s contract).

---

## 8. Open

1. **The premise-chain bound does not survive an `[any]`.** `AccessPath.limitFieldAccess` returns
   unchanged the moment it meets one, and the repeated-field collapse it implements is the only thing
   bounding the premise family (`AnyUnrollGrowthPatternTest:147-148`: *"the ONLY thing bounding the
   enumeration below, and it bounds it at N! rather than at infinity"*). Putting `[any]` into a
   majority of premises removes that bound from a majority of chains. **The design owes a replacement
   and does not have one.** Most serious item here.
2. **Does R3c consult the type filter?** The automata backend does; the unroll does. If R3c does not,
   it hands out premises for accessors the type system rejects.
3. **Two consumers key on premise shape.**
   `MethodSideEffectHandlerWithAnyAccessorRequestHandling.kt:55` answers an unfold request only when
   every accessor is an `AnyAccessor`, so a *mixed* premise `arg0.f.[any]` silently stops answering.
   And `taint/Source.kt:44-58` carries a fallback whose comment says it *"must stay until step 5 puts
   a PRODUCER of `[any]` premises in place"* — this design is that producer, so leaving it in turns it
   into unbounded over-matching. Handle both in the same change.
4. **`remainderPerFact` is the acceptance metric.** A coarser premise lands shallower and leaves a
   **bigger** remainder, and the remainder is what the summary graft attaches at every abstract node.
   Expect `E-delta remainderPerFact` to rise from 0.40 and `concat deltaNodes` (96.7M) with it. Do not
   read the current `anyPremise` row as evidence to the contrary: 99.95% of those calls do not match
   at all and still count, and the ones that do land on a bare abstract leaf that scores zero by
   construction.
5. **Every emitted pair feeds the engine's hottest function.** `AccessTreeAnySuffixMatcher.getNonMatchingNode`
   runs on every merge of an `[any]`-carrying tree and was 73.6% of analyser CPU before the memo
   landed. Watch it, not the premise store, for the performance outcome.

---

## 9. Validation

1. **Unit first**, and write R3b's test before the change: a mark under an `[any]` must still be
   named. Add one per rule.
2. **The positive control on the control.** Build R3a without R3b once and confirm findings **2 → 0**
   with `ssrf` and `path-traversal` lost. A suite that cannot detect the known failure is not
   validating.
3. **The gate**, 3,480 tests. Read `CleanerFieldSensitivityAnalysisTest` and the rule-level suites
   first; the two `JIRFactTypeCheckerUnrollFilterTest` failures are pre-existing.
4. **Byte identity** only on `rulesets/single-rule-nostar`, the one conductor arm that converges.
5. **Then conductor**, two replicates minimum, quoting ranges: volume counters span up to 5× across
   replicates of the same jar because of the interner race.
6. **Read `Total vulnerabilities` before SARIF.** Every non-converging arm loses traces to the clock,
   and a SARIF count read as a soundness signal has produced a false alarm here before.
