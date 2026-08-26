# TIFA without unrolling: the `[any]` premise as the only frontier summary

`saloed/7-fact-explosion-report`, 2026-08-26. Design for
`TreeInitialFactAbstraction` (TIFA),
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/ap/ifds/access/tree/TreeInitialFactAbstraction.kt`.

**This resolves an open question that has been carried in the specs since 2026-08-21.**
`2026-08-21-any-premise-design.md` §7 R5 — *"should `[any]` premises be emitted always, or only past
the cap?"* — proposed the second and noted the first was "worth measuring as an ablation once the
feature works, because it would delete the round loop, `unrollAnyAccessors`, and the `unrolled` memo
outright". This design takes the first.

Contents: §1 the three rules · §2 what TIFA does today · §3 the design (R0–R4) · §4 the frontier
split, and why rule 3 needs it · §5 what is deleted · §6 what it does to the `[any]` manager ·
§7 soundness · §8 precision cost and R3c · §9 test impact · §10 predictions · §11 risks ·
§12 validation

---

## 1. The three rules

Stated by the user, and taken as the specification:

> 1. Never unroll `[any]`.
> 2. If we have a concrete accessor matching the current exclusion → emit it with `*`.
> 3. If we have no concrete accessor, but we have an `[any]` (or the required accessor is after the
>    `[any]`) → emit a fact with an `[any]` premise.

Read against the code, these are not three new rules. **Rule 2 is what TIFA already does** — the
`exclusions.contains(accessor)` arm of the per-accessor helper (`TIFA:531-536`). **Rule 3 is what
TIFA already does past the cap** — the `!enumerateHere && currentLevelExclusions.isNotEmpty()` arm
(`TIFA:456-457`). **Rule 1 is the whole change**: it makes rule 3 unconditional, and everything else
follows from deleting the machinery rule 1 makes unreachable.

That framing matters, because it means the risk is not in inventing behaviour — both emission shapes
are shipped and exercised — but in removing the two mechanisms that today answer the demands rule 3
will have to answer alone: the enumeration (`unrollAnyAccessors`) and the hoist. §4 is about the
second of those, and it is the part of this design that can lose findings if it is got wrong.

---

## 2. What TIFA does today

### 2.1 Two sides: supply and demand

Per `(method, access-path base)`, `MethodSameBaseInitialFact` holds

- **`added`** (`AccessTreeNode`) — the accumulated union of every concrete fact seen for this base.
  The **supply**.
- **`analyzed`** (`AccessPathTrieNode`) — a trie over accessor chains. The **demand**.

`AccessPathTrieNode` has three fields and each means something different (`TIFA:651-698`):

| field | meaning |
|---|---|
| `children` | a registered premise passes through this accessor here |
| `terminals` | a registered premise **ends** here; the set is that premise's exclusions. `exclusions()` returns it, and **`null` means no premise has ever ended here** |
| `unrolled` | the one-shot memo: an accessor may be offered to the unroller once, ever |

Demand arrives two ways. `registerNewInitialFact` folds a caller/sink premise into the trie; and the
emission block folds **every premise TIFA itself emits** back in
(`facts.addAnalyzedInitialFact(initialAbstractAccessNode, exclusions = IntOpenHashSet())`,
`TIFA:164`). The second is what makes the walk a ladder: emitting `P` creates the trie path for `P`,
which lets a later walk descend one level further.

### 2.2 The walk

`abstractAccessPath` is a worklist over `AbstractionState(analyzedTrieRoot, added, currentAp,
governingAnyId, hoistedAny)`. At each state:

1. `exclusions = trieNode.exclusions()`. **`null` → emit `currentAp` and stop** — nobody has asked
   for anything more specific here, so the most abstract premise is the right one (`TIFA:396-399`).
2. If `added.containsAnyAccessor()` (`TIFA:401-460`):
   - collect an `AnyAccessorUnrollRequest` for `trieNode.unrollAccessors(exclusions)` — the demanded
     accessors this node has not yet offered — but only while `enumerateAnyFrontier` holds and the
     pot is not spent;
   - **the hoist**: push `(trieNode, anyBranch, currentAp)` — the `[any]` taken *zero* times, same
     trie node, `added` swapped for the `[any]` subtree;
   - **the descent through**: `anyAp = currentAp.[any]`. If `trieNode.child([any])` exists, push a
     state there; otherwise, if the round is coarse and the level carries demand, **emit
     `currentAp.[any]`**.
3. For every concrete accessor of `added`, the per-accessor helper (`TIFA:498-546`):
   - `trieNode.child(a) != null` → descend (or, for an always-unroll-next accessor, emit everything
     below it via `abstractNextAccessPath`);
   - else `exclusions == null` → emit `currentAp`;
   - else `!exclusions.contains(a)` → **emit nothing**;
   - else → **emit `currentAp.a`** — rule 2.

### 2.3 The pair that is emitted

```kotlin
val initialAbstractAccessNode = apManager.createNodeFromReversedAp(abstractAccess)
val initialAbstractAp = AccessPath(apManager, base, initialAbstractAccessNode, Empty)     // the PREMISE
val apAccess = apManager.createAbstractNodeFromReversedAp(abstractAccess, governingAnyId)
val ap = AccessTree(apManager, base, apAccess, Empty)                                     // the FACT
```

The premise is a **chain**; matching is prefix-based, so a premise `a.b` already means `a.b.*` and
there is no abstraction flag to set on it. The fact is built by folding the same chain over
`abstractNode`, so **the fact's endpoint is `*`** (`AccessTree.kt:3322-3337`). That `*` is
load-bearing: `2026-08-21-any-premise-design.md` §2.4 records that it *becomes the graft point* for
`concatToLeafAbstractNodes`, and that a premise whose endpoint is not `isAbstract` has its delta
silently discarded. **"Emit it with `*`" in rules 2 and 3 is therefore already the mechanism, not a
new requirement** — and, importantly, it works for an `[any]`-terminated chain too, because the fold
puts the `*` *below* the `[any]` edge.

### 2.4 The round loop

`addAbstractInitialFact` walks, unrolls what the walk requested, and walks again over the newly
materialised delta, until nothing new is unrolled — with one extra coarse round when a pot runs out
mid-flight (`TIFA:112-188`). Unrolling materialises **fact** copies: `filterAccessNode` the `[any]`
carrier under each demanded accessor and merge them back into `added`.

---

## 3. The design

### 3.1 The rules, made precise

Let `Σ_any` be the accessors `[any]` covers — `TreeApManager.isCoveredByAny(a)`, which delegates to
the injected `AnyAccessorUnrollStrategy` and in production is **field and element steps only**. Write
`U = ¬Σ_any` for the rest: taint marks, class statics, type-info accessors, `[value]`, `[final]`.

At a walk state `(T, N, p)` — trie node `T`, fact node `N`, prefix `p` — with `E = T.exclusions()`:

- **R0 (no demand).** `E == null` → emit `p`. *Unchanged.*
- **R1 (never unroll).** No `AnyAccessorUnrollRequest` is ever collected, `unrollAnyAccessors` does
  not exist, and the walk runs **once** per call rather than to a fact fixpoint.
- **R2 (concrete).** For each `a` with `N.child(a) ≠ ∅`:
  - `T.child(a) ≠ null` → descend, as today (or `abstractNextAccessPath` for always-unroll-next `a`);
  - else `a ∈ E` → emit `p.a`. *Unchanged.*
- **R3a (the covered frontier).** If `N` owns an `[any]` and `E ≠ ∅`:
  - `T.child([any]) ≠ null` → descend through it with prefix `p.[any]`;
  - else → emit `p.[any]`.
  One edge for everything `[any]` covers. **The gate `!enumerateHere` is deleted**; the emission is
  now unconditional on demand.
- **R3b (the uncovered frontier).** For each accessor `u ∈ U` that occurs in the `[any]` subtree of
  `N` and is demanded — i.e. `T.child(u) ≠ null`, or `u ∈ E` — emit **both** `p.[any].u` and `p.u`,
  and continue past `u` exactly as `abstractNextAccessPath` does today. Two edges each.
  **Both, not one**: §4.3 establishes that an `[any]` premise is unreachable for a caller fact with
  no literal `[any]` at that position, so `p.[any].u` does not subsume `p.u`. The second edge is the
  hoist, restricted to `U`.
- **R3c (demanded, covered, not present) — required, not optional.** For each `a ∈ E` that `N` does
  not hold literally, where `N` owns an `[any]`, `isCoveredByAny(a)`, and `p`'s type filter accepts
  `a` → emit `p.a`. §8 is the evidence; the short version is that seven shared cross-backend tests
  demand exactly this and the automata backend already passes them this way.
- **R4 (the virtual descent) — the piece that keeps the ladder climbing.** Where the walk today
  reaches a deeper trie node only because the unroll *materialised* a fact under it, descend through
  `N.getChild(a)` instead: for a trie child `a` that `N` does not hold literally but whose `[any]`
  can reach, push `(T.child(a), N.getChild(a), p.a)`.

R3b and R4 are the parts that are not simply "delete code". §4 is why R3b has to exist; §3.4 is why
R4 does.

### 3.2 Why R3a and R3b are the whole frontier

`[any]` denotes zero-or-more steps **over `Σ_any` only**. So for a demand `d` sitting somewhere below
the `[any]`:

- if every step from the `[any]` down to `d` is in `Σ_any`, then `p.[any].*` already denotes the path
  to `d` and R3a's single edge answers it;
- if any step is in `U`, `p.[any].*` does **not** denote it, and the accessor must appear in the
  premise. That is R3b.

The split is exhaustive by construction, and it is the same split the earlier prototype made — see §4.

### 3.3 The walk becomes single-pass, and the ladder still climbs

Deleting the round loop does not make the abstraction shallower, because the ladder was never the
loop: it is the **re-registration** at `TIFA:164`. Emitting `p.[any]` creates `T.child([any])`, so
the *next* walk takes R3a's first arm and descends, and can then emit `p.[any].q`. Walks are re-run on
every `addAbstractedInitialFact` and `registerNewInitialFact`, and both re-walk the whole `added`
union rather than a delta.

**A loop is still worth keeping, but a different one.** Re-walk while the last round emitted at least
one *new* premise — a **premise fixpoint** rather than a fact fixpoint. It costs a walk per level and
materialises nothing; it terminates because the trie grows monotonically, `[any]` cannot nest (the
node factory collapses `[any].[any]`), and each descent through an `[any]` moves to a strictly
smaller fact subtree. Without it, a depth-`k` premise needs `k` triggering events, and whether those
events always arrive is exactly the kind of thing that is invisible until a rule silently stops
firing. **Recommendation: keep the loop, on the new termination argument.**

### 3.4 R4: `getChild` is the unroll, minus the copy

The sharpest objection to "never unroll" is not soundness, it is that **the demand ladder stops
climbing**. Today the ladder below an `[any]` works like this: the unroll materialises
`arg0.f.[any]…` into `added`; the *next* walk's `state.added.forEachAccessor` then sees a literal `f`,
routes to trie node `f`, and can emit `arg0.f.g`. Emit `arg0.f` without materialising anything and
`added` never acquires an `f` child, so no later walk is ever routed to trie node `f`. The abstraction
would be stuck one level below every `[any]`.

The fix is already in the engine and TIFA simply does not use it. The walk descends by **literal**
accessors (`forEachAccessor`) everywhere except the single `getChild(ANY_ACCESSOR_IDX)` at
`TIFA:423`. But `AccessTree.AccessNode.getChild(a)` is documented as *"the unique point at which a
concrete accessor is SYNTHESISED out of an `[any]`"* (`AccessTree.kt:710-740`): for a node owning an
`[any]` it returns the merge of the literal `a` child, the `[any]` subtree's `a` child, and the
`[any]` re-installed below — which is **exactly the node the unroll builds by copying the carrier**,
without the copy.

So R4 is:

> where the trie has a child `a` that the fact node does not hold literally, and the fact node owns an
> `[any]`, descend with `(T.child(a), N.getChild(a), p.a)`.

**Why this is not unrolling.** A read cannot grow a stored fact: `getChild` returns a node assembled
from subtrees of the receiver, and nothing is merged back into `added`. The unroll's cost is the
materialisation — `filterAccessNode` copies the carrier per demanded accessor and merges the copies
into the accumulator (`carrierPerRequest = 10.72`, `nodesPerMaterialised = 5.91`), and it is that copy
which still owns an `[any]` and so re-arms the next round. That feedback is what
`AnyUnrollGrowthPatternTest` pins at `Σ n!/(n−k)!` — 4, 15, 64 premises for demand sets of size 2, 3,
4. R4 walks the same shapes and stores none of them.

**R3c and R4 are the two halves of one mechanism**: R3c hands out the premise `p.a` the first time `a`
is demanded, which registers `T.child(a)`; R4 is what makes the *next* walk descend there. Neither
works without the other, and together they are the unroll's precision at the unroll's semantics
minus the unroll's accumulator.

**One thing to settle in code, not here**: `getChild` has a `record` parameter that decides between
`readChild` and `peekChild` on the `[any]` manager. TIFA's walk is not a fact derivation and should
almost certainly `peek` — recording a transition per premise-ladder step would put the walk back into
the automaton's budget, which is the coupling rule 1 exists to remove.

### 3.5 The shape of the diff

| today | after |
|---|---|
| `addAbstractInitialFact`'s `while (true)` over `unrollAnyAccessors` | `while` over "did this round emit a new premise" |
| `unrollAnyAccessors`, `UnrollResult`, `AnyAccessorUnrollRequest` | deleted |
| `AccessPathTrieNode.unrolled` + `unrollAccessors` | deleted |
| `enumerateAnyFrontier`, `enumerateHere`, `budgetExhausted` calls | deleted |
| `anyUnroll.readChildPaidOnly` | **its only caller disappears** — see §6 |
| the hoist state push | replaced by R3b |
| `AbstractionState.hoistedAny` | deleted (diagnostics-only today) |
| `!enumerateHere && E.isNotEmpty()` gate on the `[any]` emission | `E.isNotEmpty()` |

---

## 4. The frontier split, and why rule 3 needs it

**This is the one place where the design as literally stated loses findings, and it has already been
measured.** `2026-08-21-any-premise-design.md` §3.2:

> Measured: collapsing the frontier onto a bare `.*` (or `[any].*`) loses conductor's findings
> **2 → 0**, and the two lost rules are `java/security/ssrf.yaml:ssrf` and
> `java/security/path-traversal.yaml:path-traversal` — precisely the rules whose marks the provenance
> trace attributed to the starred Spring sources.

The mechanism is not subtle: `[any]` covers field and element steps, so a **taint mark** is not
reachable through it. A premise `arg0.[any]` paired with a fact `arg0.[any].*` says "something under
`arg0` is tainted" without saying *with which mark*, and the mark is the finding.

Today the mark demand is answered by the **hoist**. A sink precondition `<this>.![m].$` registers as
`trieRoot → [m] → [final]`, so `trieRoot.child([m]) ≠ null`. A fact `this.[any].![m].$` has no `[m]`
child of its own; the hoist pushes `(trieRoot, anyBranch, p)`, the concrete loop then sees `[m]` with
a trie child, and `abstractNextAccessPath` emits `<this>.![m].$`. That is the only route, and the
code comment at `TIFA:432-440` says so, naming the same two rules.

**So R3b is not an optimisation — it is the replacement for the hoist**, and it must be built at the
same time as R1, not after it.

### 4.1 There is a working prototype of exactly this split

`saloed/12-any-unroll-budget`, commit `a6e5be532`, *"cap `[any]` unrolling, summarising the frontier
by a split coarse edge"*:

```
covered      one edge for all of them
                 premise  a.b     fact  a.b.[any].*  join  a.b.*
not covered  a taint mark, a class static, type info -- one edge each, with
             the accessor concrete on both sides
                 premise  a.b.T   fact  a.b.[any].T.(sub join *)
```

and its own commit message:

> The second half is what makes the cap loss-free. Collapsing the whole frontier onto `*` drops
> exactly the accessors `[any]` cannot reach, and a `$*VAR` source puts its taint mark there —
> measured as findings 2 → 0 on conductor.
>
> Premises fall 891,654 → 21,828 and no method exceeds 1024 premises. **98 engine tests and 237
> rule-level tests pass with the cap forced to 1.**

A cap of 1 is "never unroll" in all but name. **The proposed behaviour has already passed the full
test suite once**, in a form that predates `[any]`-carrying premises.

### 4.2 What the shipped `[any]` premise changes about it

The prototype could not put `[any]` in a premise, so it had to keep the premise concrete (`a.b`,
`a.b.T`) and put the `[any]` only on the fact side — and then fight the consequence, because the
premise's endpoint was the node *holding* the `[any]` edge, which is not `isAbstract`, so the delta
would be discarded. That is what `createAnyPrefixedAccessorNodeFromReversedAp` and the
"`join *`" columns above are for.

With `[any]` allowed in premises this disappears. `createAbstractNodeFromReversedAp` folds the chain
over `abstractNode`, so `p.[any]` yields `p.[any].*` and **the premise's endpoint is the `*`, below
the `[any]`**. R3a and R3b need no special constructor; the ordinary emission path already produces
the right shape. The split survives; the plumbing for it does not.

### 4.3 An `[any]` premise does NOT subsume its `[any]`-free variant — settled, and it constrains R3b

`[any]` is zero-or-more, so `p.[any].T` *denotes* `p.T`. It does not *match* it. The matching side is
`AccessBasedStorage`, and the asymmetry is structural:

```kotlin
private fun collectNodesContainsAccessor(pattern, accessor, nodes) {
    if (accessor == ANY_ACCESSOR_IDX) { collectNodesContainsAnyAccessor(pattern, nodes); return }
    children.get(accessor)?.collectNodesContains(pattern, nodes)          // AccessBasedStorage.kt:87-98
}
```

The `[any]` rule fires on the accessor of the **caller fact**, not of the premise. A premise trie
child keyed by the literal `[any]` is entered only from `collectNodesContainsAnyAccessor`'s
*structural* arm — `children.get(ANY_ACCESSOR_IDX)` — which is reached only when the fact has an
`[any]` at that position. A caller fact with a purely concrete path takes the second line above, and
`children.get(c)` never returns the `[any]`-keyed child.

The KDoc names the three arms and each is a property of the **fact's** `[any]`: zero-steps, structural,
expansion (`AccessBasedStorage.kt:100-128`). There is no arm for "the premise has an `[any]` and the
fact does not".

**Two consequences, and they are the load-bearing ones in this design:**

1. **R3b must emit both edges** (§3.1). Otherwise a caller whose fact reaches the mark by a concrete
   path activates nothing that names the mark, and that is the 2 → 0 signature.
2. **R3a alone does not cover concrete caller facts.** If the callee's `added` is `[any]`-shaped and
   its only premises are `p.[any]…`, a caller fact `p.a.![m].$` matches none of them and falls back to
   the coarsest premise for the base — which exists (the ladder starts at the bare base, matching
   everything) so **no flow is lost**, but the answer is the most abstract one available and the mark
   is not named. That is exactly the field-sensitivity loss §8 measures, now with a mechanism rather
   than a test comment. **It is also the strongest argument for R3c**: R3c is what supplies the
   concrete premise when `added` has only the `[any]`.

---

## 5. What is deleted

- `unrollAnyAccessors`, `UnrollResult`, `AnyAccessorUnrollRequest`, `addReversedApParents`,
  `ReversedApNode.createFilter` — roughly 130 lines, the whole enumeration.
- `AccessPathTrieNode.unrolled` and `unrollAccessors` — the one-shot memo, and with it a subtle
  ordering constraint the current code has to document ("the budget is consulted BEFORE the memo,
  deliberately… collecting a request we will not honour burns demand", `TIFA:404-407`).
- `enumerateAnyFrontier` / `enumerateHere` / the coarse-round restart.
- `AbstractionState.hoistedAny` and the `emitsHoistedFromAny` diagnostics.
- `TifaDiagnostics.unrollRequests`, `unrollAccessorsOffered`, `unrollMaterialised`,
  `unrollRefusedByBudget`; `ApOpDiagnostics` A-unroll (`unrollCalls`, `recordUnrollRequest`,
  `recordUnrollMaterialised`, `samplePrefix`, `unrollMergedNodes`, `unrollAddedDelta`);
  `AnyUnrollDiagnostics.tifaUnrolledFacts`.
- `AnyUnrollManager.readChildPaidOnly` and `budgetExhausted` — **their only callers are the three
  lines this design removes** (`TIFA:245`, `TIFA:304`, `TIFA:408`; verified by a repo-wide grep).

That last one is not a tidy-up. It changes what `anyUnrollLimit` means, so it gets its own section.

---

## 6. What this does to the `[any]` manager

`readChildPaidOnly` is the **only entry point in the engine that can refuse**. `readChild`, the
fact-side read, "never refuses, and that is the whole point" (`AnyUnroll.kt:1251`). So today:

- the pot's *refusal* has exactly one consumer, TIFA's unroll;
- `mintKind=[paid:409(unroll:407), credit:143]` on the frontier arm — **99.5% of PAID mints come from
  `readChildPaidOnly`**;
- and PAID is what `writesAbove` gates absorption on, so the states TIFA mints are the states that
  decline absorption. One of them was measured carrying 83.1% of all 11.4M declines.

Delete the unroll and:

1. **`anyUnrollLimit` stops being a precision cap and becomes purely an absorption dial.** Nothing
   refuses any more; `limit` only decides whether a `readChild` mint is `PAID` or `CREDIT`, i.e.
   whether the absorbing prepend may fold an accessor into that `[any]`. The knob keeps its name and
   changes its meaning, which is worth saying out loud in its KDoc.
2. **The PAID population collapses.** With the unroll gone, PAID mints come only from `readChild`
   under `dag.total < limit`. Whether that makes absorption fire more (fewer PAID states to decline)
   or less (the origins that used to be PAID are now the only ones with any pot pressure) is **not
   predictable from the code and must be measured** — it is P4 in §9.
3. `budgetExhausted` becomes dead outside diagnostics. Either delete it, or keep it for the dag
   census and mark it as such — but do not leave a public method whose only remaining callers are
   counters, which is how `witnessDisagreesWithThreadedState` came to be read as evidence for three
   weeks while never being incremented.

**A consequence worth stating plainly**: after this change `L = -1` (the shipped default) and
`L = 100` differ only in whether absorption is allowed to fire. The "budget" framing that has driven
four design documents no longer describes anything TIFA does.

---

## 7. Soundness

### 7.1 The obligation

TIFA must not lose a flow. Concretely: for every concrete fact `F` that reaches the abstraction, the
emitted set of `(P, A)` pairs must be such that any caller fact that would have activated a summary
under the old TIFA still activates one, and the activated conclusion still denotes at least what it
denoted before.

**And here is the trap, which I got wrong on the first pass and §4.3 corrects: an `[any]` premise is
a NARROWING, not a widening.** `X.[any].*` is a strictly *stronger* assertion than `X.*`
(`2026-08-21-any-premise-design.md` §3.5), and the matching side agrees: a premise `[any]` link is
only reachable from a caller fact that carries a literal `[any]` there. So the usual reasoning —
"coarsening a premise admits more callers, therefore it is safe" — **does not apply to rule 3**.

The correct statement of the obligation is:

> **Rule 3 may only ADD an `[any]` premise, or replace a premise that only `[any]`-carrying caller
> facts could ever have matched. It may never replace a premise a concrete caller fact needs.**

That is why R3b emits two edges, and it is the reason R3c is required rather than recommended (§8).
Coarsening the paired **fact** is a different matter and is safe in the usual direction: a larger
entry state yields a superset of derivations, which costs precision and not recall
(`2026-08-21-any-premise-design.md` §S3).

"Answered at all" is the whole risk, and it has exactly three failure modes:

- **F1 — the demand is never reached.** The walk stops at a level and never emits anything naming the
  demanded accessor. This is what killed the naive collapse (§4): a mark below an `[any]`, with the
  hoist removed and nothing put in its place.
- **F2 — the premise is emitted but cannot match.** The endpoint is not `isAbstract`, so the delta is
  discarded (`2026-08-21-any-premise-design.md` §2.4).
- **F3 — a concrete premise is replaced by a strictly narrower `[any]` one.** The caller fact that
  needed the concrete premise now matches nothing more specific than the base, and the flow is
  answered too coarsely to be a finding. This is F1's quieter sibling: nothing is lost from the
  *analysis*, only from the *answer*.

R3b addresses F1 and F3 by construction (two edges). F2 is addressed by
`createAbstractNodeFromReversedAp`'s fold over `abstractNode` (§2.3), which puts the `*` below the
`[any]` rather than at it.

**The safety net that makes F3 a precision loss rather than a soundness one**: the trie starts empty,
so the first walk for any base hits R0 and emits the bare `base` premise, which matches every fact on
that base. Every base therefore always has a matching premise. If the redesign ever changes the
first-emission path, that stops being true and F3 becomes a genuine loss.

### 7.2 Why never unrolling is sound

Unrolling is a **precision** feature, not a correctness one — `2026-08-21-any-premise-design.md` §2.6
states this directly: *"Removing it is a deliberate trade of precision for performance."* The unroll
converts `arg0.[any].![m].$` into concrete paths like `arg0.MapValue.externalInputPayloadStoragePath.![m].$`,
so the premise says exactly which field sequence must be tainted. The `[any]` premise says "some
sequence of covered steps", which is a superset of every enumeration the unroll could have produced —
including the ones it never got to, which is why the coarse edge is *more* complete than a truncated
enumeration, not less.

### 7.3 Termination

The premise fixpoint of §3.3 terminates because: the trie only grows; `[any]` cannot nest, so a
descent through an `[any]` cannot be repeated at the same position; and each such descent moves to a
strictly smaller fact subtree. The old loop's termination argument rested on the one-shot `unrolled`
memo — a weaker guarantee, since it bounded how often an accessor could be *offered* rather than how
deep the walk could go.

---

## 8. Precision cost, and the rule that pays it back

### 8.1 The cost is field sensitivity under an abstract source

`CleanerFieldSensitivityAnalysisTest` is the test class that will decide this. Its
`concrete two-level clean over an abstract source - the sanitized field is silent` carries a comment
that is, read carefully, a description of the mechanism this design removes:

> The source is any-field, so the cleaner's path **does not exist as a fact until the demand-driven
> refinement produces it**. Once it does, the clean is a node deletion again and field sensitivity
> survives the summary — an abstract source is not the problem.

The refinement that "produces it" is the unroll: with an any-field source, `added` is
`arg.[any].![m].$` and has no concrete `node`/`leaf` child, so rule 2 — which only ever runs over
accessors `added` actually has — cannot fire. The concrete path exists only because
`unrollAnyAccessors` materialised it.

Under R1 + R3a alone, it does not exist, the cleaner's node deletion has nothing to bite on, and the
sanitized field reports. **That is a false positive, and it is the design's real price.** The engine
comment at `TIFA:441-450` describes the same effect from the other direction: an `[any]` premise
"cannot express a node deletion inside the `[any]`, so a cleaner that bites on a concrete path stops
biting under it", and names this test.

### 8.2 R3c — emit the demanded accessor without materialising it. Required.

**The automata backend already does this, and passes every one of these tests.**
`AutomataInitialFactAbstraction.abstractGraph` (`:193-236`):

```kotlin
exclusion.forEach { accessor ->
    if (!delta.startsWith(accessor)) {
        if (!delta.startsWith(anyAccessorIdx)) return@forEach
        if (tryAnyAccessorOrNull(accessor.accessor) { true } != true) return@forEach
        …type filter…
    }
    …
    val singleAccessorGraph = emptyGraph().prepend(accessor)
    newAnalyzedGraphs.add(analyzedGraph.concat(singleAccessorGraph))
}
```

Read it against rule 3: when the demanded accessor is **not** present concretely but the fact starts
with `[any]` and the `[any]` covers it and the type filter accepts, the automata backend emits a
premise naming **the concrete accessor** — not the `[any]`. `AutomataCleanerFieldSensitivityAnalysisTest`
overrides nothing, so it passes all four cleaner cases with no round loop, no memo, and no
materialisation.

That gives a fourth rule for the tree backend:

- **R3c (demanded, covered, not present).** For each `a ∈ E` that `N` does not have concretely, where
  `N` owns an `[any]`, `isCoveredByAny(a)`, and `p`'s type filter accepts `a` → emit `p.a`.

**R3c is not unrolling.** Unrolling's cost is the *materialisation* — `filterAccessNode` copies the
`[any]` carrier under each accessor and merges it back into `added`
(`carrierPerRequest = 10.72`, `nodesPerMaterialised = 5.91` on the frontier arm), and that copy is
what re-arms the next round and what the round loop exists to service. R3c copies nothing, registers
nothing in `added`, and needs no loop: it hands out a premise, and the premise's own registration in
the trie is what lets the next walk go deeper. It is bounded by **demand**, `|E|`, not by the
accessor alphabet.

With R3c the four rules compose cleanly:

| situation | rule | premise | fact |
|---|---|---|---|
| demanded accessor present concretely | R2 | `p.a` | `p.a.*` |
| demanded, absent, covered by the `[any]`, type-accepted | **R3c** | `p.a` | `p.a.*` |
| anything else the `[any]` covers | R3a | `p.[any]` | `p.[any].*` |
| an uncovered accessor under the `[any]` | R3b | `p.[any].u` | `p.[any].u.*` |

**R3c is required by the shared cross-backend test suite, not merely advisable.**
`InitialFactAbstractionTest` runs every scenario against both the tree and the automata backends, and
seven of them — `any accessor scenario 1…7` at `:419, :427, :435, :443, :451, :459, :467` — assert a
premise naming an accessor that **exists in no concrete branch of the fact**. `:443` is the sharpest:
exclusion `{e}` over a fact with no `e` anywhere must yield `this.b.e`. So does `:375`
(`scenario 36`), the one merged scenario whose demanded accessor is absent from every concrete branch.
The automata backend passes all eight through the non-materialising emission quoted above. The tree
backend passes them today through the unroll. **Rule 1 removes the tree backend's mechanism, and R3c
is the only replacement that keeps those eight green.**

Build it unconditionally. If it must be flag-guarded for an ablation, default it ON and expect those
eight tests to fail with it off — that is the ablation's *result*, not a bug in it.

§4.3 makes the case for R3c stronger than "it keeps a test green". Because an `[any]` premise is only
reachable from an `[any]`-shaped caller fact, a callee whose `added` is `[any]`-shaped and whose
premises are all `[any]`-carrying answers a **concrete** caller fact with nothing more specific than
the bare base. R3c is the rule that puts a concrete premise in reach in that case, and it does so at a
cost bounded by demand rather than by the alphabet. Without it, rule 3 is not just coarser than the
unroll — it is coarser in a way the matching side cannot recover from.

---

## 9. Test impact, stated up front

Nothing in the repo names `unrollAnyAccessors`, `AnyAccessorUnrollRequest`, `AccessPathTrieNode`,
`enumerateAnyFrontier` or `AbstractionState`. The machinery is pinned only through the two public
methods, which is good news for the diff and bad news for the review: **the tests that break are
behavioural, and each one has to be argued rather than mechanically updated.**

### Must stay green — these are the correctness net

| test | what it pins |
|---|---|
| `InitialFactAbstractionTest` `any accessor scenario 1…7` (`:419-467`) and `scenario 36` (`:375`) | a premise naming an accessor absent from every concrete branch. **R3c exists for these.** They run on both backends |
| the 19 `expectedEmpty` scenarios | `abstractionIsEmpty` tolerates **only** a size-0 premise (`:525-526`), so an `[any]` premise emitted where the level carries no demand fails them. R3a's `E ≠ ∅` guard is what keeps them green |
| `AnyPremiseAbstractionTest:142` `no any premise is emitted where the level carries no demand` | the same guard, stated directly |
| `AnyPremiseAbstractionTest:188` the zero-times descent | R3b's obligation |
| `AnyPremiseAbstractionTest:174` a mark below an `[any]` is named | R3b again |
| `AccessBasedStorageAnyLookupTest:330` `a plain fact does not reach a premise any` | §4.3 — do not "fix" this while making rule 3 fire more |
| `AnyAccessorCollapseTest:199` `filterStartsWith` matches a 16-link premise against `base.[any].*` | `AccessPath.size` must keep counting `[any]` as 1 |
| `CleanerFieldSensitivityAnalysisTest` (both backends, 4 deep-clean cases) | field sensitivity under an abstract source — §8.1 |
| `StarOperatorTest` (16 tests) | its header says outright that *"a concrete field read only inherits that taint once the any-accessor is unrolled to a field read"* — R3c + R4 must reproduce that |
| the Go sample suites (318 `traceResolved` assertions) | the largest net, and the one that catches trace loss |

### Must be deliberately rewritten — they assert the mechanism being removed

| test | why |
|---|---|
| `AnyUnrollGrowthPatternTest:186` `the fixed point is every non-repeating sequence over the demand set` | asserts **exactly** 4 / 15 / 64 concrete premises at closure. It pins the explosion; rule 1 is meant to invalidate it |
| `AnyUnrollGrowthPatternTest:202` `growth is superexponential in the size of the demand set` | same |
| `AnyPremiseAbstractionTest:159` `while the base still unrolls no any premise is emitted` | there is no "still unrolls" any more. The premise it forbids is the one R3a now emits |
| `AnyPremiseAbstractionTest:361, :375, :417` (the cap) | the cap is what rule 1 replaces |
| `AnyUnrollManagerTest:316` `readChildPaidOnly`'s pre-credit contract | the method's only caller is being deleted |
| `JIRFactTypeCheckerUnrollFilterTest` (3 tests, currently failing) | the filter the unroll consults. If the unroll goes, decide whether R3c keeps consulting it — §10 O7 |

**Rewriting a test that asserts the explosion is the right move, and it must be visible in the diff.**
An assertion changed from 64 to 3 in the same commit that changes the behaviour is fine; an assertion
deleted is not.

---

## 10. Predictions

Falsifiable, against the frontier arm (`L=100`, `rescore`/`bfs`, conductor, one endpoint, one rule).
Baselines are `scoped-runs/rev-bfs-1` and `rev-bfs-2` unless stated.

**P1 — premises collapse.** Today 54,169 premises over 14,696 methods, top five holding 23%, and
`WorkflowExecutorOps#decide(WorkflowModel)` alone at 6,537 (4,684 under the re-score). The 2026-08-21
prototype measured 891,654 → 21,828 with the cap at 1. **Predict at least a 5× fall in total
premises and no method above ~1,000.** A fall smaller than 2× falsifies the premise that the
enumeration is what builds the population — and would point back at
`addAbstractInitialFact` re-walking the whole `added` union on every registration, which this design
does not touch.

**P2 — the `[any]` share inverts.** `emitsWithAnyInChain` is 3.9% of emitted premises today, and the
"`[any]` taken zero times" hoist yields 1.0%. **Predict a majority of premises carry an `[any]`.**

**P3 — the graft's delta GROWS, and this is the risk, not the reward.** I first read the `E-delta`
split the other way round and it is worth recording why that reading is wrong, because the counter
invites it:

```
E-delta concretePremise calls=3,689,728  factNodes=327,749,644  remainderNodes=131,355,222  remainderPerFact=0.40
E-delta anyPremise      calls=1,735      factNodes=11,141       remainderNodes=34           remainderPerFact=0.00
```

The `anyPremise` row does **not** say "an `[any]` premise consumes the fact and leaves nothing". It
says three other things at once:

1. **Most of those calls do not match at all.** `getChild(ANY)` returns `null` unless the fact carries
   a literal `[any]` edge, so `deltaImpl` returns `emptyList()` — which still counts `calls + 1` and
   still adds the whole tree to `factNodes`, while adding **0** to `remainderNodes`.
2. **When it does match, the landing node is a bare abstract leaf.** A summary keyed on `[any]`
   carries exit fact `X.[any].*`, so `removeAbstraction()` leaves an empty node and only
   `EmptyAccessTreeDelta` comes back — which scores 0 by construction.
3. `[any]` premises are **0.047%** of all delta calls, and their mean fact is **6.4 nodes** against
   the concrete row's **88.8**. It is not a sample of the same population.

The mechanism runs the other way: **a coarser premise lands SHALLOWER, so it leaves a BIGGER
remainder**, and the remainder is exactly what `concatToLeafAbstractNodes` grafts at every abstract
node of the conclusion. **Predict `remainderPerFact` rises above 0.40 and `concat deltaNodes` (96.7M)
rises with it.** A fall would be a genuine surprise and would need explaining before being believed.

`remainderPerFact` is therefore the design's **acceptance metric**, not its selling point. Also note
the stale comment at `ApOpDiagnostics.kt:196-205`, which claims an `[any]` premise "leaves nearly the
whole caller fact as the remainder" — that describes the `F-roundtrip` bucket (a *concrete* accessor
read *through* an `[any]`), not this one, and it is what led me astray.

**P4 — the manager's kind distribution is unpredictable; measure it.** `mintKind=[paid:420(unroll:418),
credit:149]` today. With `readChildPaidOnly` gone, `unroll:` goes to 0 by construction. Whether
`absorptions` (2.83–3.32M) rise or fall is **not derivable from the code** — fewer PAID states means
fewer declines, but the origins that carried the pot pressure were exactly the unroll's. Report
`absorptions`, `writtenPaid`, and the `cf decliningStates` census.

**P5 — the walk gets cheaper.** `anyDescents` fires 106,453 times and each hoist re-walks the whole
`[any]` subtree at the same trie level. **Predict `walkStates` falls materially**; R3b visits only
uncovered accessors.

**P6 — findings, the falsifier.** `Total vulnerabilities: 2` and SARIF 2 must hold. **If R3b is
omitted, predict 2 → 0 with `ssrf` and `path-traversal` lost** — that is the measured signature from
§4 and it is the cheapest possible check that R3b is wired correctly. Run that arm deliberately once,
as a positive control on the control.

**P7 — throughput is genuinely uncertain.** Coarser premises match more caller facts, so a summary
fires more often even though there are fewer of them; against that, P3 says each firing grafts less.
**No prediction.** Report `Progress` and the window differential of
`docs/superpowers/specs/2026-08-26-any-manager-review-and-perf.md` §5 rather than a cumulative
average — that document records how a cumulative average misread this exact quantity by an order of
magnitude.

---

## 11. Risks and open questions

**O1 — settled, and it changed the design.** An `[any]` premise does not match a caller fact with no
literal `[any]` at that position (§4.3, `AccessBasedStorage.kt:87-128`). R3b therefore emits two
edges per uncovered accessor, and R3c stops being optional polish. **What remains open is the
`AccessTree.delta` half**: whether the delta computation agrees with the storage lookup on the
zero-step case, since the KDoc says the storage rule "mirrors the fact-side reader, `getChild`, which
is what `AccessTree.delta` uses downstream". Confirm the mirror holds rather than assuming it —
a lookup that admits a premise the delta then discards is a silent loss.

**O2 — the `AnyAccessorDisabled` strategy throws.** `isCoveredByAny` delegates to the injected
strategy, and the one installed for the whole prescan phase **throws rather than returning false**
(`TreeApManager.kt:50-60`). R3a/R3b/R3c all query coverage, so each must prove an `[any]` edge exists
first, or short-circuit on `anyAccessorsQueryable`. This is a known trap with a known shape; it is
listed so it is not rediscovered.

**O3 — precision loss beyond the cleaner tests.** §8 names the one class that is certainly at risk.
The rule-level suite (237 tests in the prototype's run) is the real gate, and it passed there at cap
1 — but that was before `[any]`-carrying premises, so it is evidence, not proof.

**O4 — the demand ladder may need more rounds than events supply.** §3.3. Mitigated by keeping a
premise fixpoint loop. If the loop is dropped for simplicity, this becomes a live correctness risk
and needs a counter (premises emitted per round, and rounds per call).

**O5 — `anyUnrollLimit` keeps its name and loses its meaning.** §6. A knob that no longer does what
four design documents say it does is a documentation hazard; either rename it or write the change
into its KDoc in the same commit.

**O7 — the `[any]` depth charge will park most initial edges.** `AccessPath.AccessNode.depth`
charges an `[any]` link **10** (`AccessPath.kt:489`, `AccessTree.kt:2963`), and
`MethodAnalyzer.edgeExceedLimit` gates on `initialFactAp.depth > factDepthLimit` with
`INITIAL_ALLOWED_FACT_DEPTH = 3`, rising by one per delayed-resume round
(`TaintAnalysisUnitRunner.kt:356`). If most premises carry an `[any]`, most initial edges are delayed
for **at least seven rounds at every entry point**. This is arithmetic, not a measurement, and it is
the most likely source of a "nothing happens for the first N seconds" regression. Either re-tune the
charge in the same change or measure `delayedF2FInitialEdges` occupancy and the resume-round count.

**O8 — the only bound on premise chain length does not survive an `[any]`.**
`AccessPath.limitFieldAccess` returns the node **unchanged** the moment it meets an `[any]`
(`AccessPath.kt:661-669`), and the repeated-field collapse it implements is the only thing bounding
the premise family — `AnyUnrollGrowthPatternTest:147-148` says so in as many words: *"That is the
ONLY thing bounding the enumeration below, and it bounds it at N! rather than at infinity."* A design
that puts `[any]` into a majority of premises removes that bound from a majority of chains. **The
design owes a replacement bound and does not currently have one.** This is the most serious
unresolved item on the list.

**O9 — more `[any]` in facts feeds the engine's hottest function.** Every emitted pair carries an
`[any]`-bearing `FinalFactAp`, and `AccessTreeAnySuffixMatcher.getNonMatchingNode` — which runs on
every merge of an `[any]`-carrying tree — was profiled at **73.6% of all analyser CPU and 83.5% of
all allocation** in the late conductor window
(`2026-08-26-any-manager-review-and-perf.md` §7.5). The memo landed on 2026-08-26 and buys 1.4–1.8×,
but the walk still scales with how much `[any]` is in the facts. **Watch that function, not the
premise store, for the performance outcome.**

**O10 — two consumers key on premise shape and will change behaviour silently.**
`MethodSideEffectHandlerWithAnyAccessorRequestHandling.kt:55` answers a taint-mark unfold request only
when `getAllAccessors().all { it is AnyAccessor }`; a *mixed* premise such as `arg0.f.[any]` fails
that test and stops answering, and its own KDoc warns this loses sinks. And `taint/Source.kt:44-58`
carries a fallback that retries a lookup with a trailing `[any]` stripped, with a comment saying it
*"must stay until step 5 puts a PRODUCER of `[any]` premises in place"* — this design is that
producer, so leaving the fallback in turns it into unbounded over-matching. **Both must be handled in
the same change.**

**O11 — does R3c consult the type filter?** The automata backend does
(`AutomataInitialFactAbstraction.kt:203-217`), and the unroll does
(`accessorFilter.check(accessorInstance)`, `TIFA:255-268`). If R3c does not, it hands out premises for
accessors the type system rejects. If it does, `JIRFactTypeCheckerUnrollFilterTest` keeps its purpose
and its two standing failures become relevant again rather than pre-existing noise.

**O12 — premise subsumption does not exist and cannot cheaply be added.** `AccessBasedStorage` is a
trie of distinct keys; `NodeSubsumedException` is exclusion-based, identity-edge-only, and every read
path bypasses the overrides by reading `children` directly. So a concrete premise and an `[any]`
premise for the same flow both stand and both propagate (`MethodAnalyzer.kt:1159-1172` groups by
premise equality). R3b emits two edges per uncovered accessor by design; that is a doubling nothing
downstream will collapse.

**O13 — `MethodSameBaseInitialFact.addInitialFact` still merges with `foldToAny = false`.** This
design does not touch it. It is one of only two such call sites in the module, and the measured
counterfactual (`J-trimCF keptFraction = 0.97`) says it is currently inert — but that measurement was
taken with the trim's abstract-cancellation hole open, and closing that hole took the same figure to
0.19. Under a design where `added` stops receiving unrolled copies, the `added` tree's shape changes,
and the measurement should be retaken rather than assumed.

---

## 12. Validation plan

1. **Unit first.** Add tree-backend tests that pin each rule: R2 (concrete demanded), R3a (covered
   frontier), R3b (a mark under an `[any]` — the ssrf shape, as a unit test rather than an end-to-end
   one), R3c if built. R3b's test is the one that matters; write it before the change.
2. **The gate.** 3,480 tests. `CleanerFieldSensitivityAnalysisTest` (both backends) and the rule-level
   suite are the ones to read first; the two pre-existing `JIRFactTypeCheckerUnrollFilterTest`
   failures are expected.
3. **The loss-free control.** `rulesets/single-rule-nostar` on conductor converges in 38–62 s with
   `rc 0` and has given a byte-identical `results.sarif` across every build so far. It is the only
   conductor arm that can support a byte-identity claim; use it.
4. **The positive control on the control.** Build R3a without R3b once and confirm findings 2 → 0
   with `ssrf` and `path-traversal` lost (P6). A validation suite that cannot detect the known
   failure is not validating.
5. **Then conductor**, two replicates minimum, reading ranges not point values — volume counters span
   up to 5× across replicates of the same jar because of the interner race
   (`no-widening-nothing-bounds-breadth`).
6. **Read `Total vulnerabilities` before SARIF.** Every non-converging arm loses traces to the clock;
   a SARIF count read as a soundness signal has produced a false alarm in this investigation before.

