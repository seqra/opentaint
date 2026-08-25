# Absorbing the prepend: making the `[any]` unroll budget see the operation that grows the fact

**Status:** design. Nothing implemented. Self-contained — it restates what it needs from
`2026-08-24-any-unroll-manager-design.md` (**M§n**) rather than assuming it.

**What it changes in the shipped design.** M§4.4 concluded the `concat` graft "needs propagation, not
a charge"; §1 shows why that is the gap. M§5.3 triggers absorption on the *pot* being spent; §7
replaces that with a per-state trigger that can tell a round trip from real structure.

**How to read it.** §4 is the semantic contract — the section to argue with. §5–§8 are the mechanism,
§9 the correctness argument, §11 the three knobs, §14 the validation. §5.8 is separable: it answers
the fork in the reversed automaton and ships only if step 4's counter says the fork is real. Appendices A–E are measurements
taken against the current tree; Appendix F records what an adversarial review changed and is the only
place this document discusses its own history.

---

## 1. The gap

`[any]` denotes zero-or-more *covered* accessor steps. Two operations move an accessor across an
`[any]` edge, and they are inverses:

| | operation | where | charged? | grows a fact? |
|---|---|---|---|---|
| **read** | `[any]ᵖ.R` — read `a` → `[any]ˢ.R′` | `getChild`'s covered arm, `AccessTree.kt:681-700` | **yes** (M§5.1) | **no** |
| **prepend** | `[any]ˢ.R` → `a.[any]ˢ.R` | six sites, §8.1 | **no** (M§4.4 exempts the graft) | **yes, one link each** |

Write `Σ` for the accessors `isCoveredByAny` accepts, so `[any].R` denotes `Σ*·L(R)`. The residual by
`a ∈ Σ` is `Σ*·R ∪ a⁻¹(R)` — `a·w = u·r` splits into `u = ε` or `u = a·u′` — and those are the two
operands `getChild` merges. The read consumes a link of the *premise* and none of the fact.

M§4.4 proved `concat` cannot **invent** an `[any]` and inferred the graft needs no charge. The proof
is about invention; the growth is not invention. `arg0.[any]ᵖ.*` becomes `ret.a.[any]ˢ.*` with the
same number of `[any]` edges and one more link. **So the budget stops the operation that is free and
never looks at the operation that costs.** Three measurements on this branch already say so:

- `AnyDeltaConcatRoundTripTest` (3 passing): the remainder of `arg0.[any].*` against premise `arg0.a`
  still carries the `[any]` — `remainderPerFact = 1.00` on real conductor samples; the round trip
  returns `ret.a.[any].*`; four laps give `arg0.a.b.c.d.[any].*`.
- `2026-08-25-why-the-budget-does-not-help.md`: at `L = 100` the unroll is cut 62× and `concat`'s node
  total is *conserved* — 131.6 M (off) / 138.4 M (L=100) / 136.0 M (L=0). The work moves.
- `AnyUnrollGrowthPatternTest` (5 passing): the fixed point is **every non-repeating sequence**,
  `Σₖ N!/(N−k)!` exactly (4 / 15 / 64 for N = 2/3/4).

The one absorption that would have closed this cannot reach it: `addParentAbsorbingAny`
(`AccessTree.kt:934-945`) is gated on `budgetExhausted` and has exactly **one caller**,
`filterStartsWithImpl:2220`. The graft — `concat`'s spine rebuild at `:2131-2137` — goes through
`bulkMergeAddAccessors`, which has no absorption at all.

---

## 2. Why the pot is the wrong trigger

The one-line fix is to route the other five prepend sites through `addParentAbsorbingAny` and keep
`budgetExhausted`. That is the null hypothesis this design has to beat, and it fails on *what* it
stops.

`budgetExhausted` is a property of the **pot**, shared by every `[any]` position descended from one
origin. Once it fires, every covered accessor prepended above any `[any]` of that origin is dropped —
including ones the callee genuinely produced:

```
fact  x.[any]ᵖ        premise  arg0.a.*        conclusion  ret.b.*
```

`b` is not a step out of the caller's `[any]`; the callee wrote field `b` of the return value.
Dropping it turns `ret.b.X` into `ret.[any].X`, which then activates every premise rooted at `ret`.
Coarsening a fact **increases** the premises it matches — `cap0-concrete-premises` records cap 0
losing findings *and* doing more work.

The automaton can draw the distinction the pot cannot: `a` is a transition out of the state the
fact's `[any]` carries, and `b` is not. That test is the whole content of this design.

---

## 3. The design in one page

**(1) The automaton is compressed.** Predecessor and successor edges name only DSU representatives; a
union remaps them (§5.5). Worth doing on its own — it closes a measured retention hole — and it is
what makes the backward query cheap and complete.

**(2) The state records how it was obtained.** `AnyUnrollState` gains a `kind`: `ORIGIN` for a start
state, `PAID` while the pot has budget, `CREDIT` once it does not. Written once at the mint; what a
union does with it is the one open question and is therefore a knob (§5.4, §11).

**(3) The read never refuses.** Past `total ≥ L`, `readChild` mints a `CREDIT` successor rather than
returning `null`, and charges nothing for it. A refused read leaves the fact holding the *parent*
state, erasing the fact that a read happened, so the prepend has nothing to key on. There is no
second ceiling and no sink: the automaton records every accessor it is asked for, and the pot decides
only how that record is **labelled**. One boundary, not two.

**(4) The prepend consults the state.** Installing a covered `a` directly above an `[any]` at state
`s`, where the `[any]`'s subtree has no `a` child (§4.3):

| `kind(s)` | is `a` an incoming edge of `s`? | result |
|---|---|---|
| `ORIGIN` / `PAID` | — | `a.[any]ˢ.R` — write it, unchanged from today |
| `CREDIT` | yes (self-loop included) | **absorb**: `[any]ᵖ.R`, `p` the predecessor |
| `CREDIT` | no | `a.[any]ˢ.R` — this accessor did not come out of this `[any]` |

with §4.4's split preserved: the step is dropped only on the `[any]`-rooted branch and kept on every
concrete sibling. The rule lives in two funnels, `create(accessor, node, anyState)` and
`bulkMergeAddAccessors`, which cover the census of §8.1 with one deliberate exclusion (§8.3).

The effect on the round trip:

```
lap 0   arg0.[any]ᵖ.*
        delta(arg0.a.*)      read a    →  [any]ˢ.*      s = p·a, CREDIT
        concat(ret.a.*)      prepend a    p --a--> s ✓
lap 1   ret.[any]ᵖ.*                                     ← same state, same depth
```

The ratchet becomes a loop.

**(5) The position is a set when it has to be.** The forward automaton is a DFA; the reversed one is
not, and `mergeStates` forks it on the operation that dominates the manager's traffic. Asking *is `a`
an incoming edge* is then single-path search on an NFA, which dead-ends on paths that exist. §5.8
replaces the pick with a **lazy subset construction**: a fact's `[any]` carries a state, or — after a
fork — an immutable, capped set of them, allocated at the point of use and owned by the fact node
(no registry, §5.8c). `clusterMax = 1` recovers the pick exactly, so which of the
two ships is a measurement (§5.8i), not an argument.

---

## 4. Semantics: what must be preserved

### 4.1 What an `[any]` denotes

`L([any].R) = Σ*·L(R)`, where `Σ` is what `isCoveredByAny` accepts — under the production strategy
(`TaintAnalyzer.kt:70-83`) exactly `FieldAccessor` and `ElementAccessor`. Three facts about `Σ` that
every argument below uses:

- **`ANY_ACCESSOR_IDX ∉ Σ`.** `isCoveredByAny(ANY_ACCESSOR_IDX)` is `false` by design and the codebase
  depends on it (`AccessTree.kt:1190`, `AccessBasedStorage.kt:148`); every site admitting a nested
  `[any]` writes the disjunction explicitly. So `getChild(ANY_ACCESSOR_IDX)` never takes the covered
  arm and never charges.
- **Marks, statics, type-info and `[value]` are outside `Σ`**, which is what makes the coarsening
  conditional (§4.3).
- **Querying `Σ` can throw.** The prescan strategy `AnyAccessorDisabled.unrollAccessor` **throws**
  rather than returning false (`ApManager.kt:55-59`), and the production one throws for
  `ValueAccessor` (`TaintAnalyzer.kt:85`). Every path that might reach the query must first prove an
  `[any]` edge exists, or short-circuit on `anyAccessorsQueryable`. This has been hit once already,
  stalling openmrs at `Progress: 1/7367` with zero findings.

### 4.2 The read, and the one term it drops

`getChild`'s covered arm merges the two residual operands **minus one deliberate subtraction**, and
the variable names are the only place it is stated:

```kotlin
val anyAccessorNoRepeats = anyAccessorNode.clearChild(accessor)      // R ∖ a, not R
val originalAnyNoRepeats = anyAccessorNoRepeats.addParentIfPossible(ANY_ACCESSOR_IDX, …)
resultNode = mergeAddMaybeNull(originalAnyNoRepeats, resultNode)
```

For a node owning `[any] → R` the arm returns `L(R_a) ∪ L(literal a-child) ∪ Σ*·L(R∖a)` against a
true residual of `… ∪ Σ*·L(R)`. Since `Σ*·L(R) = Σ*·L(R∖a) ∪ Σ*·a·L(R_a)`, it **drops
`Σ*·a·L(R_a)`** — a **narrowing**, measurable (Appendix E):

```
read( this.[any].a.![m].$ , a )  =  this.![m].$        ← no longer denotes g.a.![m]
```

The trim is pre-existing and load-bearing. What matters here is that it makes the consumers
**non-monotone in `L(·)`**, so "the rewrite produces a superset" is not by itself a soundness
argument.

### 4.3 The rewrite, and the guard that makes a superset sufficient

```
ABSORB:   a.[any]ˢ.R   ⟼   [any]ᵗ.R      for a ∈ Σ, any states s, t
```

**Claim 1 (language).** `L(a.[any].R) = {a}·Σ*·L(R)` and `{a}·Σ* ⊆ Σ*` for `a ∈ Σ`, so the result is
a superset. The state is an annotation: it enters node *identity* (`AccessTree.kt:465`, `:529`,
`AccessTreeInterner.kt:31`) and nothing that decides what a fact denotes. ∎

**Claim 1 is not sufficient**, by §4.2. After the rewrite, reading `a` off `[any].R` gives
`L(R_a) ∪ Σ*·L(R∖a)`; before it, reading `a` off `a.[any].R` short-circuits on
`getNodeByAccessor(ANY_ACCESSOR_IDX) ?: return node` and gives `Σ*·L(R)` exactly. The difference is
`Σ*·a·L(R_a)`, empty **iff `R` has no `a` child**. Hence:

```
GUARD:  absorb `a` into an `[any]` only when the `[any]`'s subtree has no `a` child.
```

**Claim 2.** With the guard the dropped term is `Σ*·a·∅ = ∅` and the read after the rewrite equals
the read before it — verified in Appendix E, where absorbed and unabsorbed facts return the *same
node* for the same read. ∎

One `getNodeByAccessor` probe on a path that already did one. The excluded shape is `a.[any].a.…`,
which the engine refuses to build **for fields** — `prependAccessor(a)` onto `this.[any].a.![m].$`
runs `addParentFieldAccess` → `limitFieldAccessCached`, which cuts every `a`-labelled edge at any
depth *including through the `[any]`*, giving `this.a.![m].$` (measured). For `[element]` there is no
equivalent: element runs are capped only when *consecutive*, and `[].[any].[]` is not. The guard is
stated as a subtree condition rather than as an appeal to `limitFieldAccess` for that reason.

**The exposure is pre-existing.** `normaliseUnderAny`'s nested collapse and the shipped
`addParentAbsorbingAny` (which has no such probe) already produce facts in the trimmed
representation. This design widens the population from "facts a spent pot produced" to "every
`a.[any].R` the engine builds", so the guard ships **first**, as its own commit, as a fix to the
existing absorb.

Two further riders. The inclusion `Σ* ⊇ Σ·Σ*` is **strict**, so this is a coarsening, not an identity
— M§8.2 makes the same correction to older documentation. And it needs `a ∈ Σ`: for uncovered `f`,
`Σ*·f·Σ*·g` contains paths `Σ*·g` does not denote at all, so absorbing there would **lose** flows.

### 4.4 The split is mandatory

The node the rewrite runs on is generally a merge, `N = [any]ˢ.R ⊕ f.S ⊕ g.T`. Dropping the step
across the whole node rewrites `a.f.S` as `f.S` — neither superset nor subset, since the two are
disjoint. So:

```
a.N  ⟼  a.(f.S ⊕ g.T)  ⊕  [any]ᵗ.R
```

`addParentAbsorbingAny` already does this in three lines. Its test is `AnyUnrollFactTest`'s
*absorption keeps the step on branches an any does not denote* — not
`AnyFieldMarkExclusionTest.kt:317-334`, which builds `[any].f.*`, goes through `concat`, and pins
C4/`parentEdgeIsAny` instead; that one never reaches `addParentAbsorbingAny` and cannot detect a
broken split.

### 4.5 The obligation table

Every operation the rewrite touches. "Depth" means position relative to the node a claim is anchored
at, not from the base — §4.6 is where the difference bites.

| operation | file:line | guarantees | what the rewrite must not break |
|---|---|---|---|
| `getChild` | `:672` | §4.2's residual **minus `Σ*·a·L(R_a)`**; a fresh `[any]` node so parent and child carry different states | **the one that bites** — non-monotone in `L(·)`, so a superset can answer with less. §4.3's GUARD is the repair |
| `deltaImpl` | `:260` | a descent driven by the premise chain, one `getChild` per link | nothing directly; it produces the `[any]`-rooted remainder the graft installs |
| `concatToLeafAbstractNodes` | `:2066` | the caller's residual below the callee's conclusion; `parentEdgeIsAny` is **one-level** memory | the rewrite fires in the spine rebuild, *after* `concatNode` was filtered — §4.6 |
| `absorbCoveredByAnyPrefix` | `:1196` | consumes a delta's covered prefix into an `[any]` **above** it, and reports it did | complementary direction; the reporting obligation transfers — §4.6 |
| `filterDeepExclusion` | `:961` | a depth-relative claim with a start exemption cancelled when a step was consumed | **the one that can be got wrong** — §4.6 |
| `normaliseUnderAny` | `:1014` | after it returns, every `[any]` in the subtree is gone or shares the installed edge's state | the rewrite installs through `createAnyEdge`, so normalisation runs on it |
| `trimAnyCoveredAndPushChildren` | `:1656` | on every `mergeAdd` with `foldToAny`, one side's `[any]` deletes what its suffix language denotes | it folds a covered prefix under a **closed** `[any]` and not an open one (Appendix D) — the reason R7b exists |
| `mergeAddStep` + guard | `:1490-1517` | union before guard; the guard returns the **receiver object** | the rewrite must not change which object survives a union — §5.4(a) |
| `limitFieldAccessCached` | `:2333` | cuts every edge labelled the field at any depth, **including through an `[any]`** (the premise side is the opposite and stops at one, `AccessPath.kt:661`) | matches on accessor identity, never depth, so removing a level changes nothing. It is also what makes §4.3's GUARD unreachable for fields — and not for elements |
| `limitElementAccess` | `:1241` | caps *consecutive* element runs | absorption shortens, never lengthens, so the cap cannot be exceeded — but it must slot in **ahead** of the limiter |
| `maxDepth` prefilters | `:2172`, `:2213` | reject a premise longer than the tree can reach — **guarded by `!containsAnyInThisOrDeepNodes`** | the rewrite always leaves an `[any]` at or above the rewritten position, so the prefilter is disabled there. Pinned by `AnyAccessorCollapseTest.filterStartsWith matches a premise longer than the any depth charge` |

The `maxDepth` row answers a real worry: a shallower tree could in principle make a soundness-critical
prefilter reject a premise it should have matched. It cannot here, because both prefilters
short-circuit on `containsAnyInThisOrDeepNodes` before reading `maxDepth`, and every branch the
rewrite shortens still carries the `[any]` it absorbed into.

### 4.6 The exclusion interaction

`DeepAccessorExclusion` is **depth-relative** and absorption hoists. The engine already knows this
where it already absorbs (`AccessTree.kt:950-960`):

> `[absorbedAnyStep]` is C2 of the concat absorption: `DeepAccessorExclusion` is DEPTH-RELATIVE, and
> absorption hoists accessors upward, so a `![m]` that stood at depth 4 arrives here as a START
> accessor. When at least one step was consumed every surviving accessor is logically at depth >= 1,
> so the depth-1 set must also be applied with `keepStartAccessor = false` — otherwise the start
> exemption silently frees a mark the sanitizer had claimed.

The claim has exactly two buckets, so only `k ≥ 1` matters, not how many. **Both error directions are
unsound and both are pinned by a matched pair of passing tests** — *a depth-1 claim still bites on a
delta whose covered prefix was absorbed* and *…keeps its start exemption when nothing was absorbed*:

- reporting `false` when a step *was* consumed exempts a claimed mark → the sanitized flow is
  re-reported;
- reporting `true` when nothing was consumed deletes a legitimately direct mark; if that empties the
  node `filterDeepExclusion` returns `null`, `concatNode` is `null`, and the branch is dropped →
  **lost taint**.

**What this design owes.** Its rewrite hoists too, and fires in the spine rebuild at `:2131-2137`,
*after* `concatNode` was filtered in the same frame. So:

1. `absorbBeyondAnyEntries` must return the same signal, **per branch** — the split means one branch
   was shortened and its siblings were not, and a single Boolean for the node would over-report on
   the siblings, the unsound direction.
2. It cannot be inferred later: after the rewrite the tree does not record that a level was removed.
3. The cheapest correct implementation is to apply the rewrite **before** `concatNode` is filtered,
   so the existing flag covers it. That is a re-ordering of the frame and should be evaluated first,
   because it turns a new obligation into an existing one.

This and §4.3's GUARD are the two sharpest correctness items, and they differ in kind: this one is
bookkeeping owed to a mechanism that measures *depth*, the GUARD is about one that measures
*language*. Both can lose a finding; both have named tests in §14.1.
---

## 5. The automaton

### 5.1 What it is

One automaton per `[any]` **origin** — the point where an `[any]` edge is created with no predecessor
to inherit from. States are positions in the set of concrete accessor sequences materialised out of
that `[any]`; transitions are `(state, accessor) → state`, at most one successor per accessor. It is
allowed to be **cyclic**: a program loop over `x.[any].*` produces `union(m, m.a)`, i.e. `m --a--> m`,
and that self-loop is how the loop reaches its fixed point — the next read of `a` finds an existing
transition, mints nothing, charges nothing. Consequently nothing may compute a quantity by traversing
it. All of this is M§2, unchanged.

Two pointer DSUs sit over it, one on states and one on pots. `find()` is lock-free with path halving;
every mutation runs under the manager lock, because two threads racing `union(x, y)` and `union(y, x)`
could otherwise leave a **cycle** in the DSU forest and make every subsequent `find` spin forever.

A fact node carries a state reference iff it owns an `[any]` edge (`AccessNode.anyId`,
`AccessTree.kt:375`, checked at `:444-451`).

### 5.2 `kind`

```kotlin
enum class AnyUnrollKind { ORIGIN, PAID, CREDIT }
```

`ORIGIN` is a start state: **neutral in the merge** (`merge(ORIGIN, k) = k` under either strategy)
and writable, for the reason §5.4(c) gives. `PAID` is every state minted while `dag.total < L`,
`CREDIT` every state minted after that — there is no further tier, because the read never stops
recording (§6.1). Written once at the mint; a union is the only other writer. The three values are
ordered writable-to-absorbing, which is what makes §5.4(b)'s `min`/`max` mean what it says.

```kotlin
/** Whether a covered accessor may still be WRITTEN above an `[any]` sitting at [state]. */
fun writesAbove(state: AnyUnrollState?): Boolean {
    if (!enabled || state == null) return true
    return state.find().kind.let { it == ORIGIN || it == PAID }
}
```

Deliberately *not* `budgetExhausted` — §2.

### 5.3 The backward query, and why it is not a lookup

The prepend must answer *is `a` an incoming edge of the position the fact's `[any]` carries?* at a
site with no access to the read that created it. Compression (§5.5) maintains a reverse index, so the
raw question is a lookup — but the answer is a **set**, and that is the whole of §5.8:

```kotlin
/** The position to move to, or null when [accessor] is not an incoming edge at all. */
fun absorbInto(pos: AnyUnrollPos, accessor: AccessorIdx): AnyUnrollPos?
```

**The forward automaton is a DFA and the reversed one is not.** `readChild` gives at most one
successor per (state, accessor) — `mergeStates` enforces it by queueing conflicting targets for
merging rather than keeping both (`AnyUnroll.kt:394-397`), and the comment there says why: *"an NFA
here would make every lookup explore a SET of states, re-derivation would stop being free, and the
whole design collapses."* Nothing gives a state at most one **predecessor** per accessor, and the same
function is what breaks it: `y.parent = x` re-points every predecessor of `y` onto `x`, so if both
had an `a`-predecessor, `x.parents[a]` now holds two. §5.8 takes the fork seriously; the paragraph
below survives it unchanged.

**Null rather than the position itself, and that is load-bearing.** A caller testing
`result === pos.find()` to mean "not from this `[any]`" would conflate two opposite situations: on
a **self-loop** `p --a--> p`, `parents[a]` contains `p`, so the correct answer is `p` — absorb,
staying put — while the identity test reads it as "no incoming edge" and *writes* the accessor. A
self-loop is precisely the automaton saying `a` is already folded into the `[any]`
(`AnyUnrollManagerTest.kt:169`), and this design manufactures such loops itself: `createAnyEdge`'s
`union(installed, found)` (`:2783`) joins the installed state with every state collected from the
subtree *below* it, an ancestor/descendant union by construction.

Nothing depends on the query being *sound* in the sense of naming the one true predecessor —
absorption is correct at any state (§9.1). What it must be is **reproducible**, and — for the
telescope to close — **complete**: §5.8 is what buys the second.

### 5.4 The union: two decisions, and only one is a preference

#### (a) Which object survives — receiver preference, a fixpoint requirement

`union(a, b)` keeps `a`'s representative. This is not a tuning choice. `AccessNode.anyId` is
canonicalised at construction and `equals` compares the **stored** reference (`:375`, `:529`); in
`mergeAdd` the receiver is the accumulated, long-lived tree. If the arrival's representative won, the
accumulated node's reference would move, the rebuilt node would be a different object,
`mergeAddStep`'s guard (`:1510-1517`) would not return `this`, and every storage `===` test —
`MethodEdgesFinalTreeApSet.kt:33`, `MethodEdgesInitialToFinalTreeApSet.kt:100`,
`MethodEdgesNDInitialToFinalTreeApSet.kt:34` — would report new work. **Every folded loop in the
program would cost an extra lap.**

The obligation is on the callers: **the accumulated side is always the receiver.** §8.4 audits every
site, because a reversed pair is not a crash and not a wrong answer — it is a silent extra lap.

Under §5.8 this obligation is **subsumed rather than met**: set union is idempotent, so an arrival
that adds nothing returns the receiver object from either side. The audit stays worth having for the
state DSU underneath, which the pot still uses.

#### (b) What kind the survivor carries — a strategy, because the answer is not known

```kotlin
enum class AnyUnrollKindMerge { PreferBelow, PreferBeyond }

// in mergeStates, AFTER `y.parent = x` -- which this choice does NOT affect:
x.kind = when {
    x.kind == ORIGIN -> y.kind                                 // §5.4(c)
    y.kind == ORIGIN -> x.kind
    kindMerge == PreferBelow -> minOf(x.kind, y.kind)          // writable if ANY member is
    else                     -> maxOf(x.kind, y.kind)          // absorbing if ANY member is
}
```

| | `PreferBelow` (default) | `PreferBeyond` |
|---|---|---|
| precision | higher — only states that went on credit absorb | lower — a credit state pulls its class |
| the cut | weaker; unions erode it | stronger |
| the decision over time | only ever **finer** | only ever **coarser** |
| re-derivation | a **subset** of what is stored | a **superset** |
| fixpoint | safe | costs work; **cannot diverge** |

The asymmetry is measured (Appendix D). A kind change rewrites nothing already stored — the guard
ignores `mergedAnyId` — so what matters is the *next* derivation merged into what is there.
`PreferBelow` re-derives finer: for a closed fact `mergeAdd` returns the receiver **unchanged**
(`[any].$ ⊕ f.[any].$ === [any].$`), the guard fires, no new work; for an open fact it keeps both
branches and costs a lap. `PreferBeyond` re-derives coarser: storage changes in both shapes and the
fact re-enters the worklist carrying an `[any]` matching strictly more premises — the shape
`2026-08-25-why-the-budget-does-not-help.md` measured as "the work moves rather than going away".

**`PreferBeyond` cannot fail to terminate**, and saying so precisely is what makes it an experiment
rather than a fear. Under a *fixed* strategy the kind is monotone in one direction over a
three-element lattice, so each state changes kind **at most twice** — once out of `ORIGIN`, once
between `PAID` and `CREDIT` — and each change triggers a re-derivation of the facts carrying that
state. The cost is `promotions × facts-per-state`, both counted by §14.4; §9.4iii is where the
product is bounded. `PreferBeyond` risks a *worse answer, more
slowly* — never a run that does not end.

**The strategy must be fixed for the run**; every argument above assumes at most two transitions per
object.

#### (c) Origins must be neutral, or the mint rate decides instead of the knob

Origins are minted constantly — `MINT_PREPEND`, `MINT_RAW_EDGE`, `MINT_BULK_MERGE`,
`MINT_DESERIALIZE` — and M§2.6 measures **11,482 of 11,625 thingsboard unions as cross-dag fusions**,
each merging two *start states* and cascading pairwise down both automata.

If origins carried `PAID`, `PreferBelow` would demote every `CREDIT` class on its first fusion with
any fresh origin, irreversibly (§9.4iii). The pot is untouched by a fusion —
`dx.total = satAdd(dx.total, dy.total, …)` stays ≥ `L` — so `budgetExhausted` would say *spent* while
`writesAbove` said *writable*, and **the absorption would never fire at all**. "Lower `L`" would not
help: an origin is `PAID` at every `L`, including 0. `PreferBeyond` mirrors it — one spent origin
promotes the fresh cascade to `CREDIT`, which then spreads by contagion across those same fusions
until every `[any]` in the program is absorption-*eligible*. Removing the `SINK` tier makes that
milder than it reads: a `CREDIT` state still absorbs only accessors it recorded, so the failure is a
cut decided by the fusion rate rather than the indiscriminate collapse `cap0-concrete-premises`
records as losing findings.

Neither outcome is a knob working; both are the fusion rate deciding for it. A start state was never
bought and has no opinion, so `merge(ORIGIN, k) = k`. What remains is the genuine case — a `PAID`
state in one automaton paired with a `CREDIT` state in the other, requiring both to have materialised
the same sequence, one before its ceiling and one after. §14.4 counts those separately, because only
they are evidence about the knob. The residual price is R6.

### 5.5 Compression: only representatives appear in edges

`mergeStates` (`AnyUnroll.kt:361-404`) compresses the **outgoing** direction only: `y.children` is
folded into `x` and nulled. Nothing touches the states *pointing at* `y`, so after a union a
predecessor's transition names the loser verbatim, forever. Measured, Appendix C:
`assertSame(t, p.find().children!!.get(B)!!)` holds, and a `WeakReference` to the merged-away state
survives eight collections. `AnyUnrollManagerTest.a merged-away state with no holder becomes
unreachable` **passes in the same run** — it pins the outgoing direction, and nothing pins the
incoming one. So M§3.8's "transient mint" reclamation does not happen for any state that was ever a
transition target.

**The invariant, in the form that is true:**

> **(I)** On exit from any locked mutation, no `children` or `parents` map holds a non-representative,
> as key or value. A reader **outside** the lock may observe one transiently, mid-remap, and must
> still resolve it with `find()`.

Not "at every instant" — `mergeStates` repoints while its `pending` deque drains. Not "readers may
drop `find()`" — `ConcurrentReadSafeInt2ObjectMap` captures backing arrays and retries, so a racing
reader can read the pre-remap value. Stating the strong form would invite exactly the deletion that
breaks it.

```kotlin
/**
 * Incoming edges: accessor -> the representatives with a transition on it INTO this state.
 *
 * The value is an IMMUTABLE array, replaced wholesale under the lock, never mutated in place.
 * [ConcurrentReadSafeInt2ObjectMap] re-checks its backing array lengths so a lock-free reader cannot
 * straddle a rehash -- but that protects the MAP, not a mutable value hanging off it. A
 * grow-in-place list would publish an incremented size before the element store was visible and
 * `absorbInto`'s lock-free scan would dereference a null; an in-place `replace` would let a racing
 * scan see one predecessor twice and another never, making `minByOrNull` non-deterministic -- and
 * that choice reaches `AccessNode.anyId`, hence `hash`, hence the merge guard.
 */
@Volatile @JvmField var parents: ConcurrentReadSafeInt2ObjectMap<Array<AnyUnrollState>>? = null
```

`putTransition(p, a, s)` gains its mirror. `mergeStates(x, y)` gains two remap loops under the lock
it already holds:

```kotlin
// (1) incoming: everything that pointed at y now points at x, and x inherits the edges.
y.parents?.forEach { a, preds -> preds.forEach { pred ->
    val pr = pred.find()
    putTransition(pr, a, x)             // NOT `pr.children?.put`, which no-ops when children is null
    x.addParentEdge(a, pr)              // copy-on-write
} }
y.parents = null

// (2) outgoing: only REMOVES the stale mirror -- the existing fold's putTransition adds the new one.
absorbed.forEach { a, target -> target.find().removeParentEdge(a, y) }
```

Loop (1) writes another state's `children`, which is safe for the reason the existing fold documents
at `AnyUnroll.kt:392-395`: if `pr` later loses root status its children, including the entry just
written, are folded into the new winner by the same code. That same conflict arm does *not* call
`putTransition` — it queues the pair for merging — so between that write and the drain of `pending` a
lock-free `absorbInto` can observe a predecessor whose forward edge does not yet resolve back. Sound
(§9.1), and it is why **Lemma 9.2's forward re-check is retained**: it turns that window into a miss
rather than a wrong predecessor, and `witnessForwardCheckFailed` counts it.

**What it buys.** The backward query becomes complete, so no single-witness record is needed and no
merge can silently replace one. Reclamation starts working. `find()` stays shallow, since automaton
traversal never routes through non-representatives.

**What it costs.** `mergeStates` goes from `O(out)` to `O(in + out)`, and that lands on the hot path
by the same 11,482-of-11,625 measurement. One map per state, against the witness fields it replaces.
Both measured at step 1, before anything depends on them (R8).

### 5.6 Identity: the new fields stay out of it

Neither `kind` nor `parents` enters `AccessNode.hash` (`:465`), `equals` (`:529`) or
`AccessTreeInterner.InternStrategy.equals` (`AccessTreeInterner.kt:31`). Only `AnyUnrollState.id`
does, and it is immutable. §5.8 widens that to `AnyUnrollPos.hashSeed` and to a by-value comparison
for clusters — both computed from immutable stored data and never from `find()`, so the property that
matters here is preserved exactly: **nothing that enters a hash ever moves under a live entry.**

This matters more than it looks: `kind` is mutable after construction, and M§3.4's central hazard is a
hash that moves under a live entry — `AccessTreeInterner`'s buckets, `EdgeSet`
(`EdgeCollection.kt:177`) and `hashSetOf<FinalFactAp>()` (`MethodAnalyzerEdges.kt:47`) would each
silently lose an entry the moment a union changed a kind.

The corollary §5.4(b) turns on: **a kind change re-propagates nothing.** The guard returns `this`,
every storage `===` fires, stored facts are untouched. A coarsening or refinement takes effect only
for facts built after it.

### 5.7 Memory

M§3.8's bound is `live origins × (L + 1) × ~48 B` and rests entirely on `readChild` refusing.
**This design gives that bound up, and that is the price of having one boundary instead of two.**
A dag now holds one state per distinct covered sequence read out of its origin; `L` caps how many of
them are `PAID`, not how many exist.

```
live origins × states-per-origin × ~64 B
```

`~64 B` is the per-state cost including the `parents` map. The middle factor is the one nothing
proves — ten states per origin is ~26 MB on the conductor witness's ~40k live origins, a hundred is
~260 MB — and the reason that is acceptable rather than alarming is empirical: **the benchmarks this
design targets do not exhibit a state-population problem.** The measured pressure is fact and premise
mass, not automaton mass, so the sink was a static backstop for a failure mode nobody has observed,
bought with a second ceiling and a fourth kind. §9.3(a) is the argument for why it should settle;
`maxStatesPerDag` and `statesLive` (§12, §14.4) keep the assumption falsifiable for two counters'
worth of cost; R3 is the repair if a workload ever contradicts it. §5.8 adds a second population on
top of this one, with its own cap and its own counters.

### 5.8 The fork: a lazy subset construction on the reversed automaton

#### (a) The fork is the normal case, not an edge case

`mergeStates` creates it twice over. `y.parent = x` re-points every predecessor of `y` onto `x`, so
two automata that each had an `a`-predecessor now leave `x.parents[a]` holding both; and the conflict
arm queues `(existing, target)` for merging (`AnyUnroll.kt:394-397`), cascading the same forking down
both child maps. M§2.6's measurement is therefore a prediction about the reverse index:
**11,482 of 11,625 thingsboard unions are cross-dag fusions**, each cascading pairwise from two start
states. A fork on a shared accessor is what that operation *does*.

And the two predecessors generally belong to **different origins**, so a greedy pick can move a
fact's `[any]` into the automaton of an unrelated program location — sound (§9.1), but the telescope
then follows edges that have nothing to do with the round trip it is trying to close.

#### (b) Greedy is single-path search on an NFA

§5.3's `minByOrNull { it.find().id }` answers *"pick a predecessor"*. The telescope asks a different
question — *"is there a **path** back through `aₖ … a₁`?"* — and greedy answers it wrongly:

```
q₀ --a--> q₁ --b--> t        the path the fact actually took
p₀ ---------b-----> t        another b-predecessor of t, smaller id, no incoming a
```

Telescoping `ret.a.b.[any]ᵗ` takes `pred_b` then `pred_a`. Greedy goes to `p₀`, finds no `a` edge,
stalls, and writes `ret.a.[any]`. **A path existed and was not found**, so the fact keeps a link it
should have shed — on every lap. That is the growth mode strategy 1 pays for, and no tie-break fixes
it: the defect is choosing before the rest of the word is known.

The textbook answer is the subset construction, and one property makes it affordable: it is built
**lazily**, so only the subsets actually reached exist. It needs no interning and no registry — (c).

#### (c) Positions are values, not interned objects

```kotlin
/** What a fact's `[any]` carries. `hashSeed` is what `AccessNode.hash` mixes in -- §5.6. */
sealed interface AnyUnrollPos { val hashSeed: Int }

class AnyUnrollState(@JvmField val id: Int, …) : AnyUnrollPos {    // today's, unchanged
    override val hashSeed get() = id
}

/**
 * Two or more states the `[any]` may equally be at: an immutable VALUE, allocated at the point of
 * use and owned by the fact node that holds it. Members are resolved through `find()` and sorted by
 * id at construction, `2 <= size <= clusterMax`. A singleton is never a cluster, so a fact that
 * never forks pays one type check and nothing else.
 */
class AnyUnrollCluster(@JvmField val members: Array<AnyUnrollState>) : AnyUnrollPos {
    override val hashSeed = members.fold(0) { h, m -> h * 31 + m.id }   // computed once, immutable
}
```

**There is no intern table and no cluster DSU**, and that is a deliberate reversal of the obvious
design. Interning would buy `===` on equal subsets, but it is a *registry of states* — §12's
"the one thing that would force weak references back into the design" — and it would own the
reclamation problem §5.5 exists to close. A cluster instead dies with the last fact node that
references it, under the ordinary collector.

Nothing re-canonicalises a cluster after construction, because nothing needs to: **every operation
resolves members through `find()` at the point of use** (`readChild`, `absorbInto`, `writesAbove`,
`union`), so a stale member is exactly as harmless as the stale state reference a fact carries today.
When the automaton coarsens under a cluster, the next derivation builds the canonical value and the
two converge one lap later — which is the trade-off `AccessNode.equals` already documents for states:
*"Two nodes whose states have since been unioned stay unequal; they are structural duplicates that
the next rebuild removes, which is cheaper than a hash that moves under a live entry."* A cluster
whose members collapse to one representative is simply built as that state.

**Three identity obligations**, and they are what replace interning:

1. **`union` returns the receiver *object* when the arrival adds nothing** — (d). This is the one that
   carries the fixpoint: the re-derived fact merges into the stored one, the union sees a subset,
   the stored position comes back unchanged, `mergeAddStep`'s guard returns `this`, and no work is
   queued. Without it a fresh-but-equal cluster on every lap would re-enter the worklist forever;
   with it, allocating fresh in `absorbInto` costs nothing but the allocation.
2. **`AccessNode.hash` mixes `pos.hashSeed`** instead of `anyId.id`. Identical for a state, and for a
   cluster a deterministic digest of member ids — so the existing property that the hash "adds no
   run-to-run variation" (`:463-465`) survives, which an identity hash would have destroyed.
3. **`AccessNode.equals` and `InternStrategy.equals` compare positions by value**:
   `a === b || (both clusters && members.contentIdentityEquals)`, reusing the helper already in
   `AccessTreeInterner.kt`. The singleton case short-circuits on `===`, so the hot path is unchanged.
   This is not needed for termination — (1) is — but without it two structurally equal facts occupy
   two nodes. Note it keeps the interner's explicit comparison rather than leaning on the hash, which
   its own comment requires: a collision must never fuse two pots.

#### (d) The three operations

```kotlin
/** FORWARD: the subset step. Mints only when NOTHING can move -- see (e). */
fun readChild(pos: AnyUnrollPos?, a: AccessorIdx): AnyUnrollPos? {
    if (!enabled || pos == null) return pos
    if (pos is AnyUnrollState) return readChildSingle(pos.find(), a)   // today's path, untouched
    val moved = pos.members.mapNotNull { it.find().children?.get(a)?.find() }
    if (moved.isNotEmpty()) return posOf(moved)                        // no mint, no charge
    return readChildSingle(pos.members.minBy { it.id }.find(), a)      // §5.3's tie-break
}

/** BACKWARD: the subset step. Null iff NO member has an incoming [a]. */
fun absorbInto(pos: AnyUnrollPos, a: AccessorIdx): AnyUnrollPos? {
    val preds = pos.eachMember { it.find().parents?.get(a).orEmpty() }.mapTo(sorted) { it.find() }
    return if (preds.isEmpty()) null else posOf(preds)
}

/** The only constructor. Dedups, sorts, degenerates a singleton to the state, applies the cap (g). */
private fun posOf(states: Collection<AnyUnrollState>): AnyUnrollPos

/** MERGE: set union. The subset case returns the RECEIVER OBJECT -- the fixpoint, §5.8(c1). */
fun union(x: AnyUnrollPos?, y: AnyUnrollPos?): AnyUnrollPos? =
    when {
        x == null || y == null  -> x ?: y
        members(y) ⊆ members(x) -> x                     // the SAME object: guard fires, no lap
        else                    -> posOf(members(x) ∪ members(y))       // a real change, one lap
    }
```

**`union` gets simpler, not harder.** §5.4(a) makes "the accumulated side is the receiver" a
correctness obligation because a DSU union moves a representative and a moved reference costs a lap
on every folded loop in the program. Set union is **idempotent and monotone**: when the arrival adds
nothing the receiver object comes back unchanged whichever side it was passed on, and when it does
add something the position genuinely changed and a lap is owed. The obligation and its silent failure
mode both dissolve — §8.4's audit stays worth having for the *state* DSU underneath, which the pot
still uses.

#### (e) Minting only when stuck is the cluster's self-loop

M§2's program loop produces `union(m, m·a)`, and today the destructive merge's self-loop is what
closes it. Under positions it is the cluster `C = {m, m·a}`, and the next lap reads `a` from `C`:
`m` can step (to `m·a`), so **nothing is minted** and the result is the singleton `{m·a}`; merging
that back into the stored `C` hits `union`'s subset case and returns `C` — the receiver object
itself — so `mergeAdd`'s guard fires and the lap is free. Had the read instead minted from every stuck member, the loop would have produced
`m·a·a` and gone round forever. The rule is not an optimisation.

#### (f) What the subset step buys, precisely

Write `step_a(S) = {s ∈ S : s.children[a] ≠ null}` and `hasPred_a(S) = {s ∈ S : parents_a(s) ≠ ∅}`.

> **Lemma (round trip).** `pred_a(succ_a(S)) ⊇ step_a(S)` and `succ_a(pred_a(S)) ⊇ hasPred_a(S)`.
> **Corollary (telescope).** The backward run of `aₖ … a₁` from `T` is non-empty **iff** there is a
> path `q₀ --a₁--> … --aₖ--> t` with `t ∈ T`.

*Proof.* `succ` is a function on states and `pred` its relational inverse; both identities are the
subset construction's, and the corollary is Rabin–Scott applied to the reversed automaton. ∎

Greedy decides a strictly weaker predicate, and the Lemma is what §9.4(ii) needs: the absorb is the
inverse of the read **up to the coarsening the fork already introduced**, rather than up to an
arbitrary choice among forks.

#### (g) The cap, and why it truncates rather than merges

`clusterMax` (default 8). A set larger than that is **truncated to its min-id member** — reproducible,
and exactly strategy 1's behaviour, so `clusterMax = 1` *is* strategy 1 and the two seed strategies
are one code path at two settings. The choice between them becomes a measurement.

It deliberately does **not** collapse the members with a destructive `union`. That would be cheap and
would bound the cluster count harder, but it pushes a **local** ambiguity into the **global**
automaton, and §5.4(c) is the record of what happens next: with fusion traffic at 98.8% the
coarsening spreads by contagion until the fusion rate decides the cut instead of the knob. Truncation
loses precision only where it is applied.

#### (h) The interactions worth naming

**The kind fold can switch the mechanism off.** `kind(C)` folds the members under §5.4(b)'s strategy,
computed on demand and never cached (member kinds move under union). Under the default `PreferBelow`
that is the meet, so **one `PAID` member makes the whole cluster writable and the telescope stops**.
This is the one place where a larger cluster is less absorbing rather than sharper.
`absorbSkippedWritableCluster` counts it; if it dominates, the answer is a lower `clusterMax`, not a
different fold — a fold that ignored the knob would make the knob mean two different things at
singletons and at clusters.

**The forward automaton stays a DFA.** `AnyUnroll.kt:394-397`'s comment — *"an NFA here would make
every lookup explore a SET of states"* — is about the automaton, and it still holds: the conflict arm
still merges conflicting targets, and no state gains a second `a`-successor. What may be a set is the
**position a fact carries**, bounded by `clusterMax` and reached only after a fork. A lookup on a
singleton is unchanged; re-derivation stays free because `union`'s subset case hands back the stored
position itself (c1) rather than because the sets were shared.

**Memory** adds one small immutable object per cluster-carrying fact node, ≤ 8 references each,
reclaimed with the node. There is nothing to reclaim *separately* — no table, no weak references, no
second population to bound — which is the practical payoff of (c) and the reason §5.7's numbers do not
move. What clusters can cost instead is allocation churn, and `clusterRate` is what measures it.

#### (i) Build the counter before the mechanism

`absorbForkHits` (absorbs where `|preds| > 1`) and `telescopeStalls` (a fold that stopped absorbing
with links still above it) need only the `parents` index step 1 already builds. **If forks are rare,
none of §5.8 should ship** and §5.3's greedy pick is the design. (a) predicts they are common; that
prediction costs two counters to falsify and a subset construction to assume.

---

## 6. The read never refuses

### 6.1 The change

```kotlin
fun readChild(state: AnyUnrollState?, accessor: AccessorIdx): AnyUnrollState? {
    if (!enabled || state == null) return state
    // ... unchanged lock-free reuse fast path: an existing transition is free, and that is the
    // termination argument rather than an optimisation ...
    synchronized(lock) {
        val current = state.find()
        current.children?.get(accessor)?.let { return it.find() }

        val dag = current.dag.find()
        val paid = dag.total < limit                        // the ONLY thing the pot decides

        val child = AnyUnrollState(stateIds.incrementAndGet(), dag)
        child.kind = if (paid) AnyUnrollKind.PAID else AnyUnrollKind.CREDIT
        child.pathCount = current.pathCount
        putTransition(current, accessor, child)             // and the parents mirror, §5.5
        if (paid) dag.total = satAdd(dag.total, current.pathCount, Int.MAX_VALUE)
        return child
    }
}
```

**A `CREDIT` mint is free, and that is deliberate.** The pot is charged exactly as today — only for
`PAID` mints — so `total` still stops just past `L` and `budgetExhausted` answers the same question
for every existing caller. Charging unpaid mints would make `total` a mixture of two quantities and
would shorten TIFA's paid window as a side effect of what `getChild` did (§6.2).

**Why refusal was the wrong shape.** Refusal keeps the fact at `[any]ᵖ`, the state before the read.
That is a *correct* residual — the `[any]` branch of `a⁻¹(Σ*·R)` is `Σ*·R` itself — which is why
M§5.3 calls refusal absorption rather than truncation. It is also lossy in the one dimension this
design needs: afterwards the fact cannot distinguish "nothing was read here" from "`a` was read here
and we declined to pay", so the prepend has nothing to key on. **The credit state is the message the
read leaves for the prepend.**

`readChild` no longer returns `null` on the enabled path. `getChild`'s `childState ?: anyId` keeps its
Elvis for the disabled case only.

**No second ceiling, and no sink.** Every accessor asked for is recorded; the pot decides only
whether the state that records it may still be written above (§7). Two ceilings would have to answer
the question "how much automaton is worth recording for recognition" — a budget in a different unit
from the precision budget `L`, with its own default to defend and its own `0 < 0` edge (R10). One
ceiling has no such question. What it costs is §5.7's memory bound and §9.3(a)'s population
statement; what it buys is that **the prepend rule has a defined answer for every `[any]` in the
program at every pot level**, which is exactly the property the refusal lacked.

### 6.2 TIFA needs the old contract, and must not absorb

Today's `readChild` answers a *recorded* transition free, past the limit, **before** consulting the
pot — twice, at `AnyUnroll.kt:433-436` and `:440-443`, both above `:446`. Two existing tests pin it.
So moving TIFA's cut to a `budgetExhausted` test *before* the read would refuse accessors that today
are granted, silently narrowing the premise side. The split is a second entry point, the same shape
M§5.2 uses for query-vs-build:

```kotlin
/** Exactly today's contract: reuse free at any pot level, mint only while paid, else null. */
fun readChildPaidOnly(state: AnyUnrollState?, accessor: AccessorIdx): AnyUnrollState?
```

`getChild` takes the credit-minting variant; TIFA takes this one and its truncating refusal arm
(`TreeInitialFactAbstraction.kt:210-217`) is untouched.

**And TIFA's own prepend must not absorb.** Its unroll re-roots the materialised copy and then
prepends the accessor it just read (`:236-237`), where `prefix = ReversedApNode(accessor, currentAp)`
and `accessor` is covered by construction. So the query would match perfectly, the absorption would
fire, and §7's telescoping would take the whole prefix away — throwing away the `filterAccessNode` copy,
the most expensive thing in that loop, *after* paying for the transition. Census row 5 is therefore
excluded from the funnel (§8.3).

### 6.3 What credit does not buy

It does not relax the precision cut: `dag.total` still stops at `L`, `budgetExhausted` answers the
same question, and a `CREDIT` transition materialises no premise. M§8.1's headline restated: at most
`L` prefixes are **materialised into premises**; every prefix read is **recorded and nothing else**,
and a recorded-but-unpaid one exists only to be absorbed.
---

## 7. The prepend rule

```kotlin
/**
 * Install [accessor] above [node], absorbing it into an `[any]` at [node]'s root when that `[any]`
 * is no longer entitled to carry a concrete step above it.
 *
 * `a.[any].R` is a subset of `[any].R` for covered `a`, so declining to write the step asserts MORE,
 * not less: absorption, not truncation.
 *
 * Which state the surviving `[any]` takes is where this differs from a budget-only form. Moving to
 * the predecessor makes the absorption the exact inverse of the read that bought the accessor, so a
 * delta/concat round trip returns the fact to the state it started from and the fixed point closes.
 * Keeping the state would bound the DEPTH while leaving every lap tagged with a different state,
 * i.e. a different node, i.e. more work.
 *
 * Two traps. The SPLIT: this node is generally a MERGE of the `[any]` branch and concrete branches,
 * and dropping the step across the whole node rewrites `a.f.S` as `f.S` on the concrete ones --
 * neither superset nor subset. The SUBTREE PROBE: `getChild`'s covered arm drops `SIGMA*.a.L(R_a)`,
 * so it is a NARROWING, and a narrowing means a bigger fact can answer a read with LESS; absorbing
 * `a` into an `[any]` whose subtree already has an `a` child loses those paths on the next read.
 *
 * The coverage query is reached only AFTER an `[any]` edge has been proved to exist: `isCoveredByAny`
 * delegates straight to the injected strategy, and the prescan's THROWS rather than returning false.
 */
private fun AccessNode.installAbove(accessor: AccessorIdx, anyState: AnyUnrollState?): AccessNode {
    val anyNode = getNodeByAccessor(ANY_ACCESSOR_IDX) ?: return createRaw(accessor, this, anyState)
    if (accessor == ANY_ACCESSOR_IDX) return createRaw(accessor, this, anyState)
    val pos = anyId ?: return createRaw(accessor, this, anyState)          // AnyUnrollPos?, §5.8c
    if (manager.anyUnroll.writesAbove(pos)) return createRaw(accessor, this, anyState)
    if (anyNode.getNodeByAccessor(accessor) != null) return createRaw(accessor, this, anyState)  // §4.3
    if (!manager.isCoveredByAny(accessor)) return createRaw(accessor, this, anyState)

    // A `CREDIT` position with no incoming edge on this accessor ANYWHERE IN IT: the step did not
    // come out of this `[any]`, and keeping it is the whole point of the targeting -- §2. A SELF-LOOP
    // is not this case: `pred` is then non-null and contains the state itself, and the step is
    // absorbed in place. Nor is a FORK: `pred` is then the set of predecessors, and carrying all of
    // them is what lets the next accessor up telescope through the one that has it (§5.8b).
    val pred = manager.anyUnroll.absorbInto(pos, accessor)      // resolves members internally
        ?: return createRaw(accessor, this, anyState)

    val absorbed = createRaw(ANY_ACCESSOR_IDX, anyNode, pred)
    val rest = clearChild(ANY_ACCESSOR_IDX).takeIf { !it.isEmpty } ?: return absorbed
    return createRaw(accessor, rest).mergeAdd(absorbed)
}
```

`createRaw` is today's `create(accessor, node, anyState)` body (`AccessTree.kt:2726-2760`) with the
absorbing check lifted out; `create` becomes `installAbove`, so every existing caller is covered
without a census to keep in sync. `addParentAbsorbingAny` disappears into it, its four early exits
becoming the guards above and `filterStartsWith`'s call becoming plain `create`.

**Guard order is load-bearing.** The first four are O(1) field and array probes and are the
overwhelmingly common exits; `isCoveredByAny` is last because reaching it on a tree with no `[any]`
throws during prescan. This is the discipline `addParentAbsorbingAny` already follows and the bug it
already documents.

**Iterated absorption telescopes.** The rule is local, but the sites that use it fold whole spines
(`filterStartsWith`'s downward loop, the two chain folds, `concat`'s recursion). Each application
moves the state one step back, so a `k`-link round trip telescopes home:

```
ret.a.b.[any]ᵗ   →   ret.a.[any]ˢ   →   ret.[any]ᵖ
```

Termination of the rewrite is immediate: every application removes one edge and adds none, so it is
bounded by the tree's depth. It does not rest on the automaton being acyclic.

**Elements are in, not out.** `manager.create(elementAccess = limitElementAccess(...))` resolves to
`elementAccess?.let { create(ELEMENT_ACCESSOR_IDX, it) }` (`:2720-2723`) and `limitElementAccess`
never returns null, so the element arm goes through the funnel; `ElementAccessor` is covered
(`TaintAnalyzer.kt:76`). §4.3's GUARD is what makes that safe — `[].[any].[]` is the one
repeated-accessor-across-an-`[any]` shape the engine does *not* collapse at construction, because
`limitElementAccess` caps only *consecutive* runs.

---

## 8. Where the rule fires

### 8.1 The census

M§4.1 enumerates the seven sites that *create* an `[any]` edge. This is the previously un-enumerated
census: sites that install an edge **above** a node that owns one.

| # | site | file:line | via | notes |
|---|---|---|---|---|
| 1 | `create(accessor, node, anyState)` — the raw single-edge choke point | `:2726` | itself | serves `reconstructRemainder` (`:905`), both chain folds (`:2900`, `:2919`), and `addParentIfPossible`'s static / mark / type-info / `[value]` arms |
| 2 | `bulkMergeAddAccessors(entries, entryAnyState)` | `:1425` | `createElementAndField` | **the graft** — `concat`'s spine rebuild is `manager.create(...).bulkMergeAddAccessors(nestedAccessors, anyId)` at `:2131-2137` |
| 3 | `addParentFieldAccess` | `:1267` | → 1 **and** → 2 | **the hottest covered prepend in the engine.** Its `create(newRootField, limitedThis)` at `:1274` installs a covered field above `limitedThis`, which routinely owns an `[any]` (`limitFieldAccessCached` recurses through every child, `ANY_ACCESSOR_IDX` included, stripping only `newRootField`). The comment at `:1279` is about the entry LIST, not this `create`. Reached from the public `prependAccessor`, hence `Cleaner`, `AliasUtil`, `RulePreconditionUtils`, TIFA |
| 4 | `filterStartsWith`'s spine re-fold | `:2218-2222` | → 1 | already absorbing — on the wrong trigger **and into the wrong state**; the closing note below |
| 5 | `TreeInitialFactAbstraction.addReversedApParents` | `TIFA:292-302` | **excluded** — §8.3 | |
| 6 | `addParentIfPossible`'s element arm | `:733` | → 1 | see §7 |

**Two funnels cover every row.** Put the rule in `create` (1) and in `bulkMergeAddAccessors` (2);
rows 3, 4 and 6 inherit it and row 5 opts out. Rows 3 and 6 are the two carrying *covered* accessors,
so they are exactly the rows that will absorb — the blast radius is the hottest prepend path in the
engine, not a periphery (R4).

The funnel argument is the structural one M§5.1 makes for putting the record in `getChild` rather
than in one caller: it covers every caller at once and stays covered as callers are added.

**Row 4 is this design in miniature, hand-wired, and it is the reason the rule is the right shape.**
`filterStartsWith` descends with `getChildRecording` (`:2199`) — the recording read, so every step it
takes is a transition the automaton now holds — and folds back up prepending the *same* accessors in
reverse (`:2218-2222`). Read and prepend are co-located, so **every accessor it prepends is an
incoming edge of the state the fact carries, by construction**: §7's query cannot miss there, and the
rule absorbs exactly the set `budgetExhausted` drops today.

It goes further. The function already captures `consumedAnyState = filteredTreeNode.anyId` *before*
each read (`:2190`) and threads it down the fold — the predecessor state, in hand. Today it is not
used for the absorption: `addParentAbsorbingAny` installs the surviving `[any]` with `anyId` (`:942`),
the state *after* the read, and for a covered field the threaded value is inert anyway, since `create`
consults `anyState` only when the accessor is `ANY_ACCESSOR_IDX` (`:2748`). So at the one site where
both ends of the round trip are visible three lines apart, the fact still comes back tagged with the
successor. §7 replaces `anyId` with `absorbInto(anyId, accessor)`, which at this site must return the
value already sitting in `parentAnyStates[i]` — **a checkable identity**, and §14.1 checks it.

This design puts on the automaton what one function threads by hand, so the sites where read and
prepend are *not* co-located can use it.

### 8.2 Row 2 — the graft

`bulkMergeAddAccessors` takes a list, so the rule is a list-to-list pre-pass:

```kotlin
private fun bulkMergeAddAccessors(accessors: List<...>, entryAnyState: AnyUnrollState?): AccessNode {
    val (entries, absorbedState) = absorbBeyondAnyEntries(accessors)   // identity when the manager is off
    val mergedAnyId = manager.anyUnroll.union(manager.anyUnroll.union(anyId, entryAnyState), absorbedState)
    if (entries.isEmpty()) return this
    // ... unchanged: group, merge duplicates, mergeAccessors, create(..., anyStateIfPresent(...)) ...
}
```

`absorbBeyondAnyEntries` walks the entries; for each `(a, N)` where — **in this order** — `N.anyId`
is non-null and not writable, `a` is not `ANY_ACCESSOR_IDX`, `N`'s `[any]` subtree has no `a` child,
`a` is covered, and `absorbInto` returns a predecessor, it replaces `(a, N)` with `(a, N.clearChild(ANY))`
(dropped when empty) plus `(ANY_ACCESSOR_IDX, N.getNodeByAccessor(ANY)!!)`, accumulating the absorbed
states into one union. The existing grouping then merges the new `[any]` entry with any the receiver
already had.

**The order is not stylistic.** `isCoveredByAny` delegates straight to the strategy, and the
prescan's throws. `bulkMergeAddAccessors` runs during prescan on both callers — `concat` at `:2137`
and `addParentFieldAccess` at `:1281` — so a pre-pass testing coverage first throws on the first
field entry of the first concat. Probing `N.anyId != null` first makes it unreachable, because with
the manager disabled every `anyId` is null. (`normaliseUnderAny` carries a dedicated short-circuit
for the same reason at `:1016-1021`.) A latent sibling: the **production** strategy also throws, for
`ValueAccessor`; row 1's `[value]` arm is unreachable only because it bails at `:739-741` when the
node carries a non-taint-mark accessor, and an `[any]` edge is one — a guard, not a type.

The union **must** stay before the `entries.isEmpty()` early return, for the reason written at
`:1429-1431`: it is a side effect of the merge, and short-circuiting past it loses the transition
that makes a program loop reach its fixed point.

### 8.3 The one row that must be excluded

Census row 5 keeps `createRaw`. §6.2 has the argument: TIFA prepends exactly the accessor it just
read, so the absorption would match, fire, and telescope away the copy `filterAccessNode` had just
built — undoing a deliberate enumeration *after* paying for it. The rewrite exists to stop the graft
re-installing what the delta read, not to cancel the unroll.

Mechanically this is why `installAbove` and `createRaw` are two functions rather than a flag:
`addParentIfPossible` must be reachable in both modes. §14.4's `tifaAbsorbsOwnUnroll` must read
**zero**.

### 8.4 The union-order audit

§5.4(a) makes "the accumulated side is the receiver" an obligation on callers. All nine production
`anyUnroll.union` sites were audited. The four of the `mergeAdd` family the rule was written for are
correct — `bulkMergeAddAccessors:1432`, `mergeAddStep:1499`, `mergeAddDeltaStep:1538`,
`trimAnyCoveredAndPushChildren:1669` (correct because `mergeNodeLoop` seeds
`AccessNodeMergePair(this, other)` at `:1609` and the trim preserves side order). Both merge steps run
the union **before** the unchanged-guard and the guard returns the receiver object.

Three findings, descending:

**(a) `mergeAddMaybeNull` silently inverts its parameters**, and `getChild` uses it twice:

```kotlin
// AccessTree.kt:644-650
private fun mergeAddMaybeNull(l: AccessNode?, r: AccessNode?): AccessNode? {
    if (l == null) return r
    if (r == null) return l
    return r.mergeAdd(l)          // <- the SECOND parameter is the receiver
}
```

`git blame` dates it to 2026-06-18, before the manager existed. At `:701` the swap is load-bearing in
the *right* direction — `resultNode`, the value accumulated so far, becomes the receiver; at `:680` it
makes the concrete edge the receiver and the `[any]`-derived node the arrival. Neither operand at
`:680` is the long-lived stored fact, so it costs no lap today. The hazard is the signature: `l`/`r`
read as receiver/argument and the body inverts them, so **any new call site written on the obvious
assumption gets the arrival as receiver.** This design adds call sites in that neighbourhood.
Renaming the parameters is a one-line prerequisite for step 5 (R9).

**(b) `removeAllAccessorChains:2402` unions the dying side as receiver** —
`union(anyId, transformed.anyId)` where `this` is being deleted and `transformed` survives. Sound, but
it is the opposite convention from `absorbCoveredByAnyPrefix:1226`, which puts the survivor first and
says so. It is the one site where a stored node's `find()` moves as a side effect of summary
compression — the shape §5.4(a) says costs a lap. Worth flipping, separately, so the effect is
attributable.

**(c) `createAnyEdge:2783` and `createElementAndField:2857` invert on purpose** — the caller-supplied
state wins over the incumbent below. `createAnyEdge`'s KDoc justifies it; the identical block in
`createElementAndField` has none and inherits the rationale by pattern-matching. §8.2 adds a third
state to that union, so the undocumented one should get the same comment first.

Not a defect, but worth knowing: at the graft the receiver of `bulkMergeAddAccessors` is a freshly
created empty node with `anyState = null`, and the accumulated state arrives as the *argument*.
`union(null, x)` short-circuits, so no representative moves — but the invariant does not hold
lexically there, which is why the audit is about which state *survives* rather than argument position.
---

## 9. Correctness

### 9.1 Soundness

**Claim 1 (the language).** For covered `a`, replacing the `[any]`-rooted branch of `a.N` by
`[any].R` yields a superset, for *any* states. §4.3.

**Claim 1 is not sufficient**: `getChild`'s trim makes the reads non-monotone in `L(·)`, so a
superset fact can answer a read with less (measured, Appendix E).

**Claim 2 (the guard).** With §4.3's GUARD the dropped term is empty and the read after the rewrite
equals the read before it (measured, Appendix E). ∎

Together they are the soundness argument. Three consequences:

- **The backward query cannot cause unsoundness.** A predecessor that is not the one the read came
  from, a missing entry, a stale read racing a remap — each changes only *which* superset is produced
  or *whether* the coarsening fires. That is why §5.3 picks `minByOrNull` for reproducibility rather
  than correctness, and why `AnyUnrollKindMerge` is a precision knob and not a soundness one.
- **No configuration can lose a finding** — `L = 0`, `PreferBeyond`, a pot spent on the first read —
  *given the guard*. M§8.2 states this for the shipped design; it survives here only because Claim 2 restores
  the premise it rests on. Without the guard it is false, and false for the shipped
  `addParentAbsorbingAny` too.
- **The split is where the rest of soundness lives** (§4.4).

### 9.2 Lemma: a recorded incoming edge is always a real edge of the quotient automaton

**Claim.** If `s` was minted by `readChild(p, a)`, then at every later time
`find(p).children[a].find() === find(s)`.

**Proof.** `putTransition(p, a, s)` establishes it; only `mergeStates` can disturb it. *(i) `p` loses
root status to `x`.* The fold at `AnyUnroll.kt:388-400` moves every transition of `p` into `x`: if
`x` has no `a`-edge, `putTransition(x, a, target.find())` reinstates it; if it has one to `u`, the
pair `(u, target)` is queued and merged, so `find(x.children[a]) === find(u) === find(s)`. *(ii) `s`
is merged into `x`.* Only `find(s)` changes, and both sides of the claim resolve through `find()`.
`mergeStates` is the only writer of `parent` outside path halving, which writes only links to genuine
ancestors. ∎

**Executed** — Appendix A, six cases against the current manager, all passing, including the two that
could have broken it: conflicting `a`-edges merged (the fold must merge the targets, not drop one)
and a cross-dag fusion cascading through the start states. The sixth pins the design's premise:
`readChild(p, a)` leaves `p.children[a]` on the fact, so the state a delta's `[any]` carries **is**
`child(p, a)` for the accessor the premise read. That is what makes the query hit at the graft.

Under compression the lemma extends to `parents` by the same argument, and the forward re-check
becomes what it should be: a defence against the racing window of §5.5, not a repair for a merge.
Under §5.8 it extends memberwise: a cluster is a set of states each satisfying the lemma, so the
subset step is exact on a structure the lemma already covers — which is why §5.8 needs no new
theorem, only Rabin–Scott applied to it.

### 9.3 Termination and the population bound

The analysis already terminates without this design, and being precise about why changes what has to
be proved. The concrete prefix above an `[any]` contains **no repeated field** — on the premise side
`limitFieldAccess` stops at an `[any]` and collapses nothing (`AccessPath.kt:661`), on the fact side
`limitFieldAccessCached` cuts through it (`:2333`, measured in Appendix E) — so its length is bounded
by the number of distinct field accessors. Finite, and `AnyUnrollGrowthPatternTest` measures what that
is worth: every non-repeating sequence. **The engine terminates in theory and not in practice.** What
is owed is therefore a population statement, in three parts.

**(a) The recorded part is bounded by what is read, and by nothing else.** This is the price of
removing the refusal and it should be stated plainly: with no second ceiling, a dag mints a state for
every distinct covered sequence the analysis actually reads out of that origin. Three things keep
that finite and **none of them is a static cap**. The automaton is *deterministic and shared* — a
sequence already recorded costs a lookup and mints nothing, which is what makes a program loop close
into a self-loop (§5.1). The *repeated-field collapse* bounds what can be read off one fact. And the
design's own effect is the third: once the round trip closes (§9.4ii) it stops generating new
sequences, so what remains is what the callee genuinely produced. The first two are properties of
existing code; the third is the thing being tested. `statesLive` and `maxStatesPerDag` are carried so
the assumption stays falsifiable — **not as a gate**. A static cap is not being kept for a growth mode
the real benchmarks do not show, and R3 records the shape of the repair should one ever appear.

**(b) The written part is not bounded, it is targeted.** A `CREDIT` state absorbs only its own
incoming accessors; a prepend whose accessor is not one is written — by design, since that accessor
is real structure (§2). This narrows growth to "what the callee genuinely produced" without bounding
it.

It does **not** make facts bigger than the shipped build makes them, and the reason is §8.1's closing
note: the one site that absorbs today is `filterStartsWith`, where read and prepend are co-located, so
every accessor it folds back is an incoming edge by construction and the rule absorbs exactly what
`budgetExhausted` drops. Two exceptions, both wanted. §4.3's GUARD declines to absorb where the
subtree already has that child — a **soundness fix**, shipped first as step −1, and the only change
here that can gain a finding. And a backward-query miss inside §5.5's racing window writes what it
cannot recognise, which `witnessForwardCheckFailed` counts. Everywhere else today absorbs nothing at
all, so the rule can only remove links.

**(c) The residual bounded by neither.** A walk over `PAID` transitions revisiting states
through a cycle writes an unbounded prefix with every state on it `PAID`. Two things bound it in
practice and neither is a proof: the repeated-field collapse (a self-loop on `a` would need the fact
to write `a.a`) and the depth gate. If `paidPrefixWritten` grows, the repair is one clause in §7's
guard — `writesAbove(state) && children[accessor].find() !== state.find()` — one map lookup on a path
that already does one. It is out of the primary design because it changes behaviour *below* the
limit, and the central claim is that below the limit nothing changes.

**Termination itself never rested on any of this**, which is why removing the sink does not endanger
it: it comes from the repeated-field collapse plus the depth gate, both untouched. What (a) puts at
risk is memory and time, not the existence of a fixed point.

### 9.4 The fixpoint

Three mechanisms, and conflating them is how this gets got wrong.

**(i) The guard, protected by receiver preference.** The storage "unchanged" test is `===` on
`mergeAdd`'s result, and `Edge` hashes its `FinalFactAp`, hence the node, hence `anyId.id`. A fact
whose state *object* changed is new work. §5.4(a) is what stops that happening on every union.
Independent of the kind.

**(ii) The absorption closes the round trip.** Absorbing while *keeping* the state — `anyId`, the
state after the read, at `AccessTree.kt:942`, although its one caller has the predecessor in hand
three lines away (§8.1) — bounds depth but leaves each lap tagged with
whatever state the read reached, so the population of distinct facts stays high though none is deep.
Moving to the predecessor returns the fact to a state already seen at that position — and
**only the subset step makes that true past the first link**, since a greedy pick can stall the
telescope on a fork and leave the prefix half-absorbed (§5.8b, §5.8f).

One qualification: the re-derived subtree is not byte-identical, because `getChild` returns
`clearChild(accessor)` under the rebuilt `[any]`. The round trip returns a **subset** of the fact it
started from — which is what makes the guard fire for a closed fact — so the claim is "the fact stops
changing", not "the fact is restored".

**(iii) The kind change.** §5.4(b) has the measurement; the bound is: under a fixed strategy the kind
is monotone in one direction over a three-element lattice, so each state changes kind at most twice,
and total kind changes are `2 × states`, each triggering a re-derivation of a bounded fact population.
That second factor is now *states actually minted* rather than a static per-dag cap, so it inherits
§9.3(a) and is counted rather than proved — but the per-state factor of 2 is what the termination
claim needs, and it is unaffected. `PreferBeyond`'s risk is therefore `promotions × facts-per-state`
of extra work — never a run that does not end.
`PreferBelow`'s opposite risk is that unions dissolve the cut and the design achieves nothing. The
same two counters detect both.

### 9.5 Determinism

Which sequences land in the paid window before the ceiling fires depends on arrival order, so
precision is order-sensitive. Not new: M§8.4 documents the same for `total`, with the measurements
behind it — the analysis runs on `newFixedThreadPoolContext(availableProcessors() / 2)`, the per-unit
`PriorityQueue` is not a stable order, accessor indices come from a first-encounter interner, and
across ten same-config runs one codeFlow flipped between `MiscUtils.java:91` and `:94`.

No source is added — `L` was already such a boundary and there is no second one — and one is removed:
the kind is combined with `min`/`max`, both **symmetric**, so unlike every receiver-preferred choice
around it the merged kind does not depend on which side of a union a fact arrives from.

Outer bounds unchanged: order can move the false-positive count but never the true-positive set, and
`ci-analyzer-owasp.yaml` asserts `EXPECTED_TRACES: 2633` on every push to main.

### 9.6 What is not proved

1. **The automaton has no static bound** (§9.3a) — deliberately: the growth a static cap would stop
   is not one the benchmarks exhibit, and the design's own effect is what should settle it. Watched,
   not proved, and the memory number is therefore evidence about the design rather than a
   precondition for it.
2. Growth above an `[any]` past the limit is not bounded, only targeted (§9.3b), and past the limit
   `filterStartsWith` keeps steps it drops today.
3. The `PAID` cyclic case is not bounded (§9.3c); the repair is written out and deliberately not taken.
4. `PreferBeyond`'s cost is bounded but not estimated — which is what makes it an experiment.
5. The non-monotone-consumer audit is not exhaustive. §4.5 checks eleven operations and finds one;
   nothing proves there is not a twelfth.
6. **The fork is predicted, not measured.** §5.8(a) infers from the fusion rate that the reverse
   index is nondeterministic almost everywhere; `absorbForkHits` is what would establish it, and the
   whole of §5.8 is conditional on that number.
7. No provenance links the graft's node mass to the round trip.
   `2026-08-25-why-concat-grows-the-fact.md` attributes 98% of node creation to `concat` and shows the
   graft *relocating* 53% of the caller's fact under a small conclusion, 78% of it attaching at one
   point. Whether that relocation is the round trip in disguise is not established by any counter.
   §14.4's first job is to answer it.

---

## 10. Interaction with the rest of the engine

**`normaliseUnderAny` and the nested collapse.** `createRaw(ANY_ACCESSOR_IDX, anyNode, …)` goes
through `createAnyEdge`, which normalises the subtree and then unions with the caller's state
preferred — so the absorbed edge is normalised on installation like every other `[any]` edge and the
branch invariant (M§2.4) is re-established at the point of the rewrite. The union can join a state
with one of its own descendants, producing a cycle; that is legal (M§2.5) and §5.3 is what stops it
switching the rewrite off.

**`absorbCoveredByAnyPrefix` and `parentEdgeIsAny`.** `concat` already absorbs a delta's covered
prefix when the delta lands *directly under* an `[any]` edge (`:1196`, gated at `:2094`). That is the
complementary case — there the `[any]` is above the material, here below — and they do not compete:
`parentEdgeIsAny == false` is the arm M§4.4 calls the most-executed graft in the engine, and it is
exactly the arm reaching this design through `bulkMergeAddAccessors`. What must be copied from it is
not the absorption but the **bookkeeping** (§4.6).

**The branch invariant** is unaffected: the rewrite creates no `[any]` and removes none, and the
construction check `(anyId != null) == containsAnyAccessor()` holds on both output branches —
`absorbed` owns an edge and gets a state, `rest` goes through `recreate` → `anyStateIfPresent`, which
drops the state with the edge.

**Serialization drops the new fields.** The wire format carries only `isFinal`, `isAbstract`, the
exclusion flag and accessor ids (`:2422-2452`); a deserialised `[any]` takes one fresh origin per tree
(`:2513-2519`). So a `CREDIT` state returns as an `ORIGIN` and a fact that was being absorbed
becomes writable. Sound — a fresh budget means less coarsening — and already the documented behaviour
for the pot. Extending the format is not proposed: `parents` names other states, which have no wire
identity.

**The premise side needs nothing.** `AccessPath` carries no state and gains none (M§6): a premise
`[any]` is a key, and a key materialises nothing. Premises are derived from facts, so a fact that
stops growing emits premises that stop growing.

**The depth gate** is untouched. `ANY_ACCESSOR_DEPTH_CHARGE = 10` and the `maxDepth` prefilters do not
fight this, because the rewrite removes links and the gate only counts them — see §4.5's last row for
why a shallower tree cannot cause a wrong rejection.

---

## 11. Configuration

**`opentaint.anyUnrollLimit`** — unchanged in meaning and default. `L < 0` is "off entirely": no
states, no kinds, no `parents`, no absorption, bit-identical to a build without the feature. There is
**no second window and no second knob**: past `L` the read still records, it just records as `CREDIT`
(§6.1). `L` therefore keeps a single meaning — how much is materialised into premises — and every
value of it, `0` included, leaves the mechanism operating.

**`opentaint.anyUnrollKindMerge=below|beyond`** — §5.4(b), default `below`. Threaded the way `L`
already is, as a `TreeApManager` constructor parameter defaulted from the property "so a test can pin
it without touching global state", and added to `FORWARDED_TEST_PROPERTIES`
(`DefaultConfiguration.kt:62-66`), which also declares it a task input so a changed value re-runs the
tests.

```kotlin
val DEFAULT_KIND_MERGE: AnyUnrollKindMerge =
    System.getProperty(ANY_UNROLL_KIND_MERGE_PROPERTY)?.trim()?.let { raw ->
        AnyUnrollKindMerge.entries.firstOrNull { it.name.equals(raw, ignoreCase = true) }
    } ?: AnyUnrollKindMerge.PreferBelow
```

The parse is **null-returning and strict**, matching `toBooleanStrictOrNull` / `toIntOrNull` at the
two existing knobs, so a typo falls back to the default; a bare `enumValueOf` would turn a misspelled
`-D` into a class-initialisation failure, which for a knob read at class-init means the analyzer does
not start. This is the module's first enum-valued knob — `grep -rn "enumValueOf\|enumValues"` over
`opentaint-dataflow-core` returns nothing — so it sets the precedent.

**`opentaint.anyUnrollClusterMax`** — §5.8(g), default `8`, parsed with the same strict
`toIntOrNull` fallback. `1` is strategy 1 exactly (pick the min-id predecessor, never carry a set),
which makes the two candidate designs one code path at two settings and the choice between them a
measurement. Values above ~16 are not expected to be useful: a fact whose `[any]` could be at
seventeen places is one the cut has already lost.

**Not offered:** a switch for receiver preference in `union`. §5.4(a) is a correctness requirement,
its failure mode is invisible, and a knob would imply the question is open.

---

## 12. Live root and exhaustion counts in the progress log

`TaintAnalysisUnitRunnerManager.reportRunnerProgress` (`:562-570`) is the periodic line:

```
Progress: 128413/128571 (+2044)
Memory usage: 6.1G/8.0G (76%)
[any] roots: 41207 live, 38994 beyond, 512k states (max/dag 47), transitions 4.1M
```

The plumbing follows the idiom `ApManager` already uses for optional backend behaviour —
`fun listEdgeCompressionRequired(edge: Edge): Boolean = false` (`ApManager.kt:38`) — so no cast and the
automata and cactus backends are untouched: `fun reportApStats(): String? = null`, overridden by
`TreeApManager` to `anyUnroll.liveReport()`, returning `null` when `limit < 0` so an unconfigured run
gains no line.

**Counting without a registry.** The manager holds no collection of states or dags — *"a registry of
states is the one thing that would force weak references back into the design"* — and neither number
needs one. Live roots are `dagsCreated - dagsFused`: `newOrigin` is the only creator, the cross-dag
fusion the only destroyer, and a fusion removes exactly one representative. Exhaustion is a
*transition*, so it needs a per-dag latch, written under the lock where the pot already is:

```kotlin
private fun noteTotal(dag: AnyUnrollDag) {
    if (!dag.exhaustedCounted && dag.total >= limit) { dag.exhaustedCounted = true; dagsExhausted.incrementAndGet() }
}
```

The fusion is the part that is easy to get wrong — the pots sum, so it can push the survivor over on
its own *and* remove a dag that was already counted:

```kotlin
dx.total = satAdd(dx.total, dy.total, Int.MAX_VALUE)
dagsFused.incrementAndGet()
when {
    dy.exhaustedCounted && dx.exhaustedCounted -> dagsExhausted.decrementAndGet()  // two counted, one survivor
    dy.exhaustedCounted                        -> dx.exhaustedCounted = true       // the count transfers
}
noteTotal(dx)                                                                      // the sum may newly cross
```

One pot and one latch is the whole scheme. `total` is monotone and the latch is never cleared, so
nothing drifts downward except at the fusion, where the decrement is exactly the dag that ceased to
exist. The state counts follow the same shape: `statesMinted - statesMerged` is live states, because
`mergeStates` is the only destroyer and removes exactly one representative; `maxStatesPerDag` needs a
per-dag counter incremented beside `total` and summed at the fusion like the pot. **Assert
`dagsExhausted ≤ dagsCreated - dagsFused`** once per tick: it is an invariant of the scheme and a
violation means the fusion accounting is wrong, which is otherwise a silent, slowly drifting number
that would be believed.

**What "live" honestly means.** `dagsCreated - dagsFused` counts live *representatives*, not dags
still reachable from a live fact — a pot whose facts have all been dropped still counts. Making it
mean the latter needs the weak registry this avoids; the counter over-reports by exactly the amount
M§3.8 identifies as un-reclaimed, and §5.5 is what moves that number. The counters are **per manager**
(there are two `TreeApManager`s per run, the prescan's forced to `-1` and silent) and
**unconditional** rather than gated on `anyManagerDiag`: four `AtomicInteger` increments on paths
already doing atomic work.

**What the line is for** — separating the failure modes aggregates cannot:

| reading | means | lever |
|---|---|---|
| `live` large, `beyond` ≈ 0 | origins proliferating, none spending | the mint sites (M§4.1), not `L` |
| `live` small, `beyond` ≈ `live` | a few origins absorbing the whole program | `L` too low, or one origin is the problem |
| `beyond` climbing while `(+delta)` falls | the cut fires and the work *moves* — the L=100 conductor shape | §14.5's prediction, live |

`queue-depth-hides-throughput-collapse` records that `queued` is pinned near zero by construction and
only the `(+delta)` is readable, so putting these on the adjacent line is what makes the third row
legible at all.

---

## 13. Implementation plan

| # | step | changes behaviour? |
|---|---|---|
| −1 | **§4.3's GUARD on the existing `addParentAbsorbingAny`.** A one-line subtree probe; a fix to a pre-existing exposure, independent of everything below | **yes** — the only step that can *gain* a finding |
| 0 | **The progress log (§12).** The instrument for reading whether any later step worked | no |
| 1 | **Compression (§5.5)** — `parents`, the two remap loops, invariant (I) as a debug check. Repairs the retention hole on its own; measure the fusion path here (R8) | no (except memory) |
| 2 | **`AnyUnrollKind`, the `kind` field, `AnyUnrollKindMerge`** and its plumbing. Nothing reads `kind` yet | no |
| 3 | **`readChild` stops refusing** + `readChildPaidOnly` for TIFA, **in one commit** — split them and the premise-abstraction cut silently changes | no |
| 4 | **`writesAbove` / `absorbInto`** with counters, **`absorbForkHits` among them**. Still nothing calls them — and this is where §5.8(i)'s measurement is taken, on the real workload, before any of §5.8 is written | no |
| 4b | **Positions and clusters (§5.8)** — *only if step 4 says forks are common.* `AccessNode.anyIdRaw` widens to `AnyUnrollPos?`, a type change across `AccessTree` with no behaviour of its own; then `posOf`, the three operations and `clusterMax` — no table, no reclamation (§5.8c) | no |
| 5 | **`create` becomes `installAbove`**, `addParentAbsorbingAny` deleted, `mergeAddMaybeNull`'s parameters renamed (R9). Covers census rows 1, 3, 4, 6 | **yes** |
| 6 | **`bulkMergeAddAccessors` pre-pass** — row 2, the graft. The commit the design exists for | **yes** |

Steps −1 to 4 need no gate beyond the unit tests. Steps 5 and 6 each need their own SARIF comparison
against the same arm, and each needs both `AnyUnrollKindMerge` settings measured. **1 before 4**:
`absorbInto` is written against `parents`, and without compression it would need a single-witness
fallback, which is a different design with a different proof. **4 before 4b**: step 4's counter is
what decides whether 4b is built at all, and it costs one increment on a path that already takes the
lock.
---

## 14. Validation

### 14.1 New unit tests

**`AnyUnrollManagerTest`** — the manager in isolation, plain int accessors:

| test | pins |
|---|---|
| `a paid mint records its incoming edge` | `parents[a]` contains the origin; `kind == PAID` |
| `a mint past the limit is credit, not a refusal` | non-null at `total == L`; `kind == CREDIT`; `total` unchanged |
| `at L = 0 the first read still mints` | non-null and `CREDIT` — R10's defect class, gone by construction |
| `a recorded sequence mints nothing on re-read` | the sharing §9.3(a) rests on: second read of the same accessor is a lookup |
| `absorbInto walks back exactly one step` | `absorbInto(p·a, a) === p`; `absorbInto(p·a, b) == null` |
| `absorbInto survives a union of the predecessor` | union `p` into `q`, then `absorbInto(s, a) === find(q)` — §9.2 |
| `absorbInto returns the state itself on a self-loop` | non-null and equal to the state — the case an identity test would have written |
| `absorbInto picks the same predecessor twice` | determinism of the tie-break |
| `an origin is neutral in the merge` | `merge(ORIGIN, CREDIT) == CREDIT` under **both** strategies, both argument orders — §5.4(c) |
| `a union takes the meet under PreferBelow` / `the join under PreferBeyond` | both orders |
| `the kind merge does not change which object survives` | under both strategies `union(x, y) === x` — §5.4(a) is independent of §5.4(b) |
| `a union remaps the predecessor's transition` | §5.5 — the inverse of Appendix C's first test |
| `a merged-away state with an incoming edge becomes unreachable` | §5.5 — the inverse of Appendix C's second |
| `no map holds a non-representative after a cascade` | walk from `dag.rootState` after a fusion; `find() === it` for every key and value |
| `the parents index survives a conflicting union` | §5.5 loop (2) |
| `a fusion forks the reverse index` | after a cross-dag fusion `parents[a]` holds two — §5.8(a), the premise the section rests on |
| `the telescope survives a fork` | `q₀-a→q₁-b→t` plus `p₀-b→t` with `p₀.id < q₁.id`: at `clusterMax = 1` the fold stalls one link up, at `8` it telescopes home — **the test §5.8 exists for** |
| `the forward step mints only when no member can move` | `{m, m·a}` reads `a` to `{m·a}`, `total` unchanged — §5.8(e) |
| `a program loop closes as a cluster` | `union`'s subset case returns the receiver object, so the guard fires and the lap is free |
| `a cluster is never built with one member` | a fork whose members have since merged yields the state itself |
| `union returns the receiver object when the arrival adds nothing` | `assertSame` — §5.8(c1), the obligation that replaces interning, from both argument orders |
| `a re-derived equal cluster queues no work` | build the same set twice from separate `absorbInto` calls, merge the second into the first, `assertSame` on `mergeAdd`'s result — the test that would fail if (c1) were dropped |
| `two nodes carrying equal clusters are equal` | `AccessNode.equals` and the interner strategy, by value — §5.8(c3) |
| `the cap truncates to the min-id member` | `clusterMax = 1` reproduces strategy 1 exactly, on the same fixture as the telescope test |

**`AnyUnrollFactTest`** — the manager as the fact tree uses it; the idiom is already there
(`TreeApManager(…, configuredLimit)` behind a `check(!managerCreated)` guard).

| test | pins |
|---|---|
| `a paid any keeps a concrete step written above it` | large `L`: unchanged from today |
| `a credit any absorbs the step it sold` | `L = 0`: read `f`, prepend `f` back, get `this.[any].*` carrying the ORIGIN's state |
| `a credit any keeps a step it did not sell` | `L = 0`: read `f`, prepend `g`, get `g.[any]` — **the targeting test, the one §2 exists for** |
| `a paid any keeps the step, a credit any does not` | `L = 1`: the boundary `L = 0` cannot reach |
| `an any whose subtree already has the accessor does not absorb` | §4.3's GUARD |
| `absorbing leaves the read unchanged` | its positive half — Appendix E as a test |
| `absorption keeps the step on branches an any does not denote` | the split (§4.4); the existing test generalises |
| `the automaton derives what filterStartsWith threads by hand` | at every fold step `absorbInto(result.anyId, aᵢ)?.find() === parentAnyStates[i]?.find()` — Lemma 9.2 end-to-end on the engine's hottest read channel, against a value the engine computes independently (§8.1) |
| `the graft absorbs through bulkMergeAddAccessors` | the graft, not only `filterStartsWith` |
| `an absorbed step is reported to the deep exclusion filter` | §4.6 |
| `a finer re-derivation is absorbed by the merge guard` / `a coarser one is not` | Appendix D — together they make `PreferBelow` the default |

**`AnyDeltaConcatRoundTripTest`** — a fourth test: `with the manager on, the ratchet becomes a loop`,
the same four laps at `L = 0`, ending at `arg0.[any].*` with depth constant and the state back at the
origin. The three existing tests keep `anyUnrollLimit = -1` and keep asserting the ratchet — they are
the control and must not change.

### 14.2 Existing tests that constrain this

62 tests across five files are hard representation constraints: `AnyAccessorCollapseTest` (7),
`AnyAccessorPremiseTest` (12), `AnyUnrollFactTest` (13), `AnyUnrollManagerTest` (19),
`AccessBasedStorageAnyLookupTest` (11). Plus the two depth-1-claim tests of §4.6 and the C4 test
`AnyFieldMarkExclusionTest.kt:317-334` — which must stay green for its own reason (§10) even though
it is *not* the split's boundary.

The findings-level net is `StarOperatorTest` — 13 of 19 tests run with `AnyAccessorEnabled`, and it is
the only end-to-end check that an unroll change loses no flow. Every commit from step 5 on must run it.

### 14.3 What legitimately changes, and one hazard

Three `AnyUnrollManagerTest` cases pin the refusal step 3 removes — `the pot refuses once it is
spent`, `a spent pot still answers an accessor it already recorded`, `limit zero refuses from the
start`. They become assertions about `kind == CREDIT` and about `total` not advancing. A contract
change, and it should be visible in the diff as one.

**The hazard.** Four `[any]` test files — `AnyAccessorCollapseTest`, `AnyAccessorPremiseTest`,
`AccessBasedStorageAnyLookupTest`, `AnyFieldMarkExclusionTest` — construct `TreeApManager` with **no
explicit limit**, so they inherit the property, which `DefaultConfiguration.kt:62-86` forwards into
the forked test JVM *and* declares a task input. They are silently sensitive to the knob, and will be
to the second knob too. An earlier reading of a `gate-L100` run attributed a failure of
`AnyAccessorCollapseTest.prepending any collapses an any reachable through covered accessors` to the
limit; **it does not reproduce** — all seven pass at `L` ∈ {unset, 0, 100} with `--rerun-tasks`. The
exposure is structural, not observed. Those four should still take explicit values before step 5,
because without it the gate cannot tell a regression from a knob.

`JIRFactTypeCheckerUnrollFilterTest`'s two failures are unrelated and pre-existing — they encode the
`java.lang.Object`-erasure fix, which no part of this design touches.

### 14.4 Counters

Extend `AnyUnrollDiagnostics` (`-Dopentaint.anyManagerDiag=true`), each incremented at the event. The
four progress-log counters of §12 are separate and unconditional.

| counter | question | red flag |
|---|---|---|
| `paidMints`, `creditMints` | how much of the automaton is unpaid | `creditMints ≫ paidMints` ⇒ `L` too small for the workload |
| `absorbExact` vs `absorbStay` | is the backward query hitting? | `absorbStay` dominant ⇒ check §5.5 landed |
| `prependWritten{Paid,CreditMismatch}` | the targeting split — structure **kept** that a budget-only form would drop | the number justifying this over §2's null hypothesis |
| `kindPromotions` / `kindDemotionsGenuine` / `kindDemotionsFromOrigin` | how fast unions move the cut | the last should be **zero** once `ORIGIN` is neutral; the middle is the evidence about the knob |
| `rederivationsAfterKindChange` | the other factor of §9.4's bound | large under `PreferBeyond` ⇒ the experiment failed |
| `tifaAbsorbsOwnUnroll` | §8.3 | **must stay zero** — non-zero means row 5 leaked into the funnel |
| `witnessForwardCheckFailed` | Lemma 9.2 and §5.5's racing window | should be small; a rising count means loop (2) is wrong |
| `witnessDisagreesWithThreadedState` | the §8.1 identity, asserted on real workloads rather than in a unit test: at `filterStartsWith`'s fold the query must return the state the caller already threaded | **must stay zero** — non-zero falsifies Lemma 9.2 in production, where no test reaches |
| `absorbForkHits` | §5.8(a) — **is the fork real?** | ≈ 0 ⇒ do not build §5.8 at all; this is step 4's whole purpose |
| `telescopeStalls` | folds that stopped absorbing with links still above them | falling after step 4b is §5.8 working; flat means the fork was not the obstacle |
| `clusterRate`, `clusterMaxSize`, `clusterTruncations` | what the subset construction costs | truncations dominant ⇒ `clusterMax` too low, or the automaton is too fused to telescope |
| `absorbSkippedWritableCluster` | §5.8(h) — the kind fold switching the mechanism off | dominant under `PreferBelow` ⇒ lower `clusterMax`, not a different fold |
| `elementPrependOverAny` | element absorption is ON (§7) | it is the `[].[any].[]` case the GUARD covers |
| `paidPrefixWritten` | §9.3(d) | growing without bound ⇒ take the self-loop guard |
| `remapsIncoming` / `remapsOutgoing` | the work §5.5 adds to the fusion path | R8 |
| `statesLive`, `maxStatesPerDag` | §5.7 — the assumption that dropping the static bound is free | either failing to settle over a run ⇒ R3 |

Plus the existing `ApOpDiagnostics` C-block re-run against the same arm, since §9.6(7) is answerable
only by comparing it before and after step 6. `statesReclaimed` is deliberately **not** a counter — it
is unmeasurable without the registry the design refuses, so §5.5's memory claim is gated on the heap
number.

### 14.5 The gate, and the predictions to falsify

`scoped-harness/gate.sh` (3,441 tests, 2 pre-existing failures), plus the conductor single-endpoint
arm across `anyUnrollLimit ∈ {-1, 0, 8, 100} × anyUnrollKindMerge ∈ {below, beyond}` with both
diagnostics on, plus `anyUnrollClusterMax ∈ {1, 8}` **at the chosen `L` only** — the full cross
product is sixteen arms, and that the two knobs do not interact is itself a claim, cheaply checked by
comparing `absorbForkHits` across the `kindMerge` pair. Plus a SARIF comparison on the star/no-star
control, which converges in 38.6 s and is the only arm where "byte-identical findings" is meaningful.

**Prediction 1.** At `L = 8` the conductor arm's `concat` result-node total falls materially below
the 136.0 M it records today, and the SARIF is a superset of the `L = -1` arm's. If the total is
conserved again — as it was across off/100/0 for the read-side cut — the round trip is not the
channel, §9.6(7) is the answer instead, and steps 5–6 should be reverted rather than tuned.

**Prediction 2.** `PreferBeyond` shows a lower node total and a higher `rederivationsAfterKindChange`
than `PreferBelow` at the same `L`. If it shows a lower total *and* no more re-derivation, the default
is wrong and should be flipped. If it shows more re-derivation and no less node mass, the knob should
be deleted rather than left as a trap.

**Prediction 3.** `clusterMax = 8` shows fewer `telescopeStalls` and a lower `concat` node total than
`clusterMax = 1` at the same `L`. If the stalls do not fall, the fork was not what stopped the
telescope and §5.8 should be deleted rather than tuned. If the stalls fall and the node total does
not, the telescope was closing on facts nobody re-derives — which is R1 again, not a §5.8 result.

---

## 15. Risks

**R1. The round trip may be a small share of the real workload.** It fires **twice** in the whole
default conductor arm, and dominates only when the unroll is refused. This design makes the mechanism
cheap to close; it does not establish that closing it moves the number. Prediction 1 is the test, and
this is the largest risk here — the correctness risks have answers, this one has only an experiment.

**R2. The `getChild` trim makes "superset" insufficient**, and §4.3's GUARD is verified only for the
shape Appendix E exercises. §4.5 audits eleven operations and finds one non-monotone consumer;
nothing proves there is not a twelfth.

**R3. The automaton has no static bound.** Removing the refusal removes M§3.8's memory bound (§5.7),
and this is a deliberate simplification rather than an oversight: the sink capped a state population
the real benchmarks do not exhibit, so it bought a proof about a failure mode nobody has measured, at
the cost of a second ceiling, a fourth kind and a second `0 < 0` edge. Two counters keep it
falsifiable. If a workload ever does contradict it, the repair is *not* the two-ceiling scheme but a
per-dag state cap under which `readChild` folds the transition into a **self-loop** on the current
state instead of minting: the read stays put, `absorbInto` returns the state itself, and the prepend
absorbs in place — today's `addParentAbsorbingAny` behaviour, reached without a fourth kind and
without a second boundary.

**R4. `create` becoming absorbing is a wide blast radius**, wider than an arms-count suggests: the two
arms of `addParentIfPossible` that carry *covered* accessors (field, element) are the ones that will
absorb, and the field arm is the public `prependAccessor` path used by `Cleaner`, `AliasUtil`,
`RulePreconditionUtils` and TIFA. The mitigations are the GUARD and §8.3's exclusion, both
load-bearing. Every arm's protection is a guard, not a type: adding a covered accessor kind silently
widens the rewrite, and for `[value]` the production strategy `error()`s rather than returning false.

**R5. Serialization asymmetry** makes a warm cache measurably more permissive than a cold one.
Already true for the pot; this adds a dimension.

**R6. `PreferBelow` may still dissolve the cut** through genuine `CREDIT`/`PAID` pairings, even with
`ORIGIN` neutral. `kindDemotionsGenuine` is the counter; the response is a lower `L` or a switch to
`PreferBeyond`, both one flag away.

**R7. `PreferBeyond` may cost more than it saves.** Bounded (§9.4) but unestimated; both factors are
counted. And a demotion is not free on an *open* fact — `[any].* ⊕ f.[any].*` keeps both branches
(Appendix D), so the finer re-derivation adds a branch instead of being absorbed by the guard.
Bounded, but it lands on the round-trip shape.

**R8. Compression puts `O(in-degree)` on the fusion path**, which is the hot path by the
11,482-of-11,625 measurement. Step 1 is separately valuable, so a bad measurement there is a cheap
stop.

**R9. `mergeAddMaybeNull`'s inverted parameters are a trap for the new call sites** (§8.4a). Renaming
them is a prerequisite for step 5, not a later cleanup.

**R10. `L = 0` was the sink, not the credit window**, in an earlier draft whose second ceiling was
tested as `dag.credit < limit` — which evaluates `0 < 0`, so at `L = 0` the mechanism was simply off.
Three prose claims and five test specifications said that value exercised the credit window and none
evaluated the expression. The instance was first fixed with a decoupled ceiling; this revision
removes the ceiling, and with it the class — `readChild` now has one comparison and no value of `L`
at which a read stops recording. `at L = 0 the first read still mints` is the test that keeps it that
way.

**R11. Four test files inherit the knobs from system properties** (§14.3), so the gate cannot tell a
regression from a setting until they take explicit values.

**R12. The subset construction can blow up**, in cluster count rather than size — `clusterMax` bounds
each set but not how many distinct sets are reached. Since clusters are values owned by their fact
nodes (§5.8c) this is allocation churn on a hot path rather than a growing table, which is the
cheaper failure and the easier one to read: `clusterRate` and `clusterMaxSize` measure it and
`clusterMax` throttles it, and a smaller `clusterMax` costs precision monotonically — the right shape
for a throttle.

**R13. The kind fold can switch the absorption off exactly where the fork is worst** (§5.8h). Under
the default `PreferBelow` one `PAID` member makes a whole cluster writable, so a bigger set is *less*
absorbing — the opposite of the intent. Counted, and the response is `clusterMax`, not a special-case
fold.

**R14. §5.8 is conditional on a number nobody has yet taken.** Step 4 exists to take it before step
4b is written, and the plan is ordered so that finding `absorbForkHits ≈ 0` costs one counter rather
than a subsystem.

---

## 16. What this design does not do

- It does not touch the **`java.lang.Object` erasure**, measured as 99.6% of conductor's largest fact
  sitting below one edge past which nothing is rejected — the largest single lever in
  `2026-08-25-conductor-fact-explosion-summary.md`'s ranked list, and orthogonal to this.
- It does not touch the **`ClassStatic` broadcast** (46%) or the **star sources**.
- It does not make the graft cheaper. It removes links from what the graft installs; the 6.0 M grafts
  and their 131.6 M nodes are a separate question (§9.6(7)).
- It does not change the premise side, the depth gate, `limitFieldAccess`, or any storage.
- It does not bound the automaton's *language* — only what may be written above an `[any]` in a fact.
- It does not make the automaton an NFA. §5.8 puts a bounded set on the **fact's position**; the
  transition relation stays deterministic, conflicting targets are still merged, and the warning at
  `AnyUnroll.kt:394-397` still holds as written.

---

## Appendix A. The witness lemma, executed

Lemma 9.2 is the one claim here that is a theorem about existing code rather than a definition or a
language inclusion, and everything leans on it: if it fails, `absorbInto` walks back to something that
is not a predecessor and the coarsening lands arbitrarily — still sound (§9.1), but no longer the
inverse of the read, so §9.4(ii) evaporates. It needs no new field to check, being a property of
`mergeStates` alone. **Six of six pass** against the current manager:

```
the witness survives a union of the successor()                  PASSED
the witness survives the predecessor losing root status()        PASSED
the witness survives a conflicting union of two predecessors()   PASSED
the witness survives a cross-dag fusion()                        PASSED
the witness survives a self-loop()                               PASSED
a read advances the state to the successor of the accessor read() PASSED
```

Each case builds an origin, reads one or two accessors off it, performs the named union and asserts
`assertSame(s.find(), p.find().children!!.get(a)!!.find())`. The two that could have gone the other
way are the third — two predecessors carrying conflicting `a`-edges, where the fold at
`AnyUnroll.kt:388-400` must *merge* the targets rather than drop one — and the fourth, where a
cross-dag fusion cascades through the start states with `accumulatePaths = false`. The sixth is not
the lemma: it pins the design's premise, that `readChild(p, a)` leaves `p.children[a]` on the fact.

The test belongs in `AnyUnrollManagerTest` at implementation step 1.

## Appendix B. What was executed, and what was read

| claim | how |
|---|---|
| Lemma 9.2, all five merge shapes | **executed**, Appendix A, 6/6 |
| a read leaves `child(p, a)` on the fact | **executed**, Appendix A case 6, and the existing `a covered read through an any records one accessor` |
| the round trip is a ratchet — `arg0.[any].*` → `arg0.a.b.c.d.[any].*` | **executed**, `AnyDeltaConcatRoundTripTest` 3/3 |
| the fixed point is every non-repeating sequence, `Σₖ N!/(N−k)!` | **executed**, `AnyUnrollGrowthPatternTest` 5/5 |
| all 23 `AnyFieldAccessorExclusionTest` cases pass, both depth-1 directions included | **executed** |
| `getChild` drops `Σ*·a·L(R_a)` — a narrowing | **executed**, Appendix E |
| with no `a` child, absorbed and unabsorbed answer the read identically (the GUARD) | **executed**, Appendix E |
| `a.[any].a.…` is not constructible for fields | **executed**, Appendix E |
| the coarser re-derivation changes storage; the finer is absorbed for a *closed* fact but not an open one | **executed**, Appendix D |
| a predecessor's transition still names the merged-away state, which survives GC | **executed**, Appendix C |
| the existing GC test passes anyway — it pins only the outgoing direction | **executed**, same run |
| `AnyAccessorCollapseTest` fails under the limit | **falsified**, 7/7 at `L` ∈ {unset, 0, 100} |
| `union` prefers the receiver; the `mergeAdd` family passes the accumulated side first | read — `AnyUnroll.kt:271-281`, all nine sites audited (§8.4) |
| `mergeAddMaybeNull(l, r)` returns `r.mergeAdd(l)` | read — `:644-650`; `git blame` 2026-06-18 |
| `removeAllAccessorChains` unions the dying side | read — `:2402`, against the convention at `:1226` |
| the element arm reaches `create` via `manager.create(elementAccess=…)` | read — `:2720-2723` |
| `addParentFieldAccess` installs a covered field above a possibly-`[any]`-owning node | read — `:1271-1274` |
| the split's real test is `AnyUnrollFactTest`'s, not `AnyFieldMarkExclusionTest`'s | read — the latter goes through `concat` and pins C4 |
| `ConcurrentReadSafeInt2ObjectMap` re-checks array lengths — safe for the map, not mutable values | read — `:9-20` |
| `readChild` answers a recorded transition free **before** consulting the pot | read — `AnyUnroll.kt:433-436`, `:440-443`, both above `:446` |
| the module has no existing enum-valued knob | read — grep returns nothing |
| the round trip fires twice in the default conductor arm | prior measurement — **not re-run** |
| `concat`'s node total is conserved across `L ∈ {off, 100, 0}` | prior measurement — **not re-run** |

## Appendix C. The compression hole, executed

§5.5 claims the automaton retains merged-away states through incoming edges — a statement about the
code as it stands, so it was run. Both pass:

```
a predecessor keeps pointing at the merged-away state()            PASSED
a merged-away state is retained by its predecessor's transition()  PASSED
a merged-away state with no holder becomes unreachable()           PASSED  <- existing test, same run
```

The first mints `p --A--> s` and `p --B--> t`, unions `s` with `t` (receiver wins, `t` is absorbed)
and asserts `assertSame(t, p.find().children!!.get(B)!!)` — the stored value **is** the
non-representative, and readers are correct only because every one calls `find()`. The second holds a
`WeakReference` to `t`, drops every strong reference, GCs eight times, and it survives.

The third line is the point: the existing reclamation test is green while the hole is open, because it
pins `y.children = null` and nothing pins the incoming direction. Under §5.5 both invert — the first
asserts `p.children[B]` names the **winner**, the second asserts the weak reference clears — and they
are listed that way in §14.1.

## Appendix D. Which direction of a kind change costs a lap

§5.4(b) decides the merge rule on the claim that the two directions are not symmetric. That is a claim
about `mergeAdd`, so it was probed. Two fact shapes, both directions, `anyUnrollLimit = -1`:

```
PROBE closed=true
   coarse = .[any].$        fine = .f.[any].$
   c+f    = .[any].$                       sameAsCoarse = true     <- guard fires, no new work
   f+c    = .[any].$                       sameAsFine   = false

PROBE closed=false
   coarse = .[any]/*        fine = .f.[any]/*
   c+f    = .f.[any]/* | .[any]/*          sameAsCoarse = false
   f+c    = .f.[any]/* | .[any]/*          sameAsFine   = false
```

1. **The forbidden direction always costs a lap.** `f+c` — the coarse arrival merged into a stored
   fine fact — never returns the receiver, in either shape. Storage changes, the fact re-enters the
   worklist carrying an `[any]` that matches strictly more premises. That is why `kind` takes the meet.
2. **The allowed direction is free for a closed fact.** `c+f` at `closed=true` returns the receiver
   object itself: the merge-time trim folds the covered prefix `f` into the `[any]` that already
   denotes it, so a demotion re-derives something already stored and nothing happens.
3. **It is not free for an open fact.** With `closed=false` the merge keeps *both* branches. The trim
   collapses a covered prefix under a closed `[any]` and not under an open one — and open is the
   summary-exit shape, hence the round-trip shape. Hence R7, and hence §9.4(ii)'s observation that
   absorbing at the prepend does work the merge-time fold declines to do for exactly these facts.

## Appendix E. The no-repeat trim, and the guard it forces

`L = -1` throughout, so only the tree's own semantics are in play; `Σ` covers fields and elements.

```
GUARD fact       = <this>.[any].g![m].$
read(f, a)       = <this>.[any].g![m].$          <- unchanged; `a` is not a child of the subtree
GUARD unabsorbed = <this>.a.[any].g![m].$
read(u, a)       = <this>.[any].g![m].$          <- IDENTICAL to the absorbed read

SIMPLE           = <this>.[any].a![m].$
read(SIMPLE, a)  = <this>![m].$                  <- the trim: SIGMA*.a.m is gone
read(SIMPLE, a) denotes g.a.m = false            <- although SIMPLE does

UNABSORBED       = <this>.a![m].$                <- built as a.[any].a.![m] and COLLAPSED on prepend
```

**1. The trim is a narrowing.** `this.[any].a.![m].$` denotes `Σ*·a·m`, hence `g.a.m`; reading `a` off
it returns `this.![m].$`, which does not — the residual should have retained `Σ*·a·m` (take
`u = a·g ∈ Σ*`). So "the rewrite produces a superset" is not a soundness argument on its own.

**2. With no `a` child, absorbed and unabsorbed answer identically** — both return
`<this>.[any].g![m].$`. That is the GUARD, verified: the dropped term is `Σ*·a·L(R_a)` with `R_a`
empty.

**3. The excluded shape is not constructible for fields.** Building `this.a.[any].a.![m].$` through
`prependAccessor` yields `this.a.![m].$`: `addParentFieldAccess` → `limitFieldAccessCached` cuts every
`a`-labelled edge at any depth **including through the `[any]`**. For `[element]` there is no
equivalent — `limitElementAccess` caps only consecutive runs — which is why the guard is a condition
on the subtree rather than an appeal to `limitFieldAccess`.

The exposure is **pre-existing**: `normaliseUnderAny`'s nested collapse and the shipped
`addParentAbsorbingAny` (no such probe) already produce facts in the trimmed representation. This
design widens the population, which is why the guard ships first as a fix to the existing absorb.

## Appendix F. The adversarial pass

An earlier draft was given to a reviewer instructed to default to "this is broken" and concede only
against code. Eight of ten attacks landed. The *shape* is the useful part: seven of the eight were
places the draft cited a section, a comment or a KDoc instead of evaluating the code it described.

| # | attack | verdict | where it went |
|---|---|---|---|
| 1 | `L = 0` never mints a `CREDIT` state — `0 < 0` fails twice — so every test demonstrating the mechanism was specified at the one value that disabled it | **landed** | first a decoupled ceiling; now §6.1 — the ceiling is gone (R10) |
| 2 | fresh origins were `PAID` and 98.8% of unions are cross-dag fusions, so `PreferBelow` demoted every class on first fusion and `PreferBeyond` spread `SINK` by contagion | **landed** | §5.4(c) — `ORIGIN` becomes neutral; the contagion arm now reads `CREDIT` for `SINK` and is milder for it |
| 3 | on a self-loop `absorbInto` returned the state itself, the identity test read that as "not from this `[any]`", and the rewrite *wrote* — precisely where the automaton says the accessor is already folded in | **landed** | §5.3 — returns null instead |
| 4 | the census was wrong at both rows carrying *covered* accessors: the element arm does go through the funnel, and `addParentFieldAccess` has its own `create` | **landed** | §8.1 rows 3 and 6, §7, R4 |
| 5 | the named soundness boundary was the wrong test — it pins C4, not the split | **landed** | §4.4 |
| 6 | the reverse index was read lock-free with a value mutated in place; the map's array re-check does not protect a mutable value. NPE and non-determinism | **landed** | §5.5 — copy-on-write |
| 7 | TIFA: a pot test before the read refuses transitions today grants free; and the absorption would undo TIFA's own unroll after paying for it | **landed** | §6.2, §8.3 |
| 8 | §8.2's pre-pass tested coverage first, which throws during prescan | **landed** | §8.2 |
| 9 | soundness of `Σ·Σ* ⊆ Σ*` and of the split | **survives** | — |
| 10 | serialization / cache round trip | **survives** | — |

Two observations worth keeping. **The two surviving attacks are the two argued from first
principles**; the eight that landed were all argued from a citation — attack 1 sharpest, where three
prose claims and five test specifications said `L = 0` exercises the credit window and none evaluated
`0 < 0`.

**Two of the ten were later answered by deletion rather than by repair.** Attacks 1 and — half of —
2 were both about the `SINK` tier and the second ceiling that fed it, machinery whose only job was a
static bound on a state population the benchmarks do not show growing. Removing it removed both
defect surfaces along with the fourth kind, the second pot, the second knob-shaped constant and the
`0 < 0` edge. Worth noting as a pattern: a mechanism that exists to prove a bound against an
unobserved failure mode is also a mechanism that has to be got right everywhere else.

And the reviews found each other's mitigations. §4.3's GUARD came from a *different* review's
objection (Appendix E) and turns out to be exactly what makes attack 4's correction safe: element
absorption is on, and `[].[any].[]` is the one repeated-accessor shape the engine does not collapse at
construction. Neither review knew of the other's finding.
