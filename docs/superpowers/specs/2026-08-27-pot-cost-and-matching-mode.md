# The pot's cost function, and one global switch for `[any]` matching

Two changes, one measured consequence each.

1. `AnyUnrollDag.total` now counts the **accessors** an origin has materialised, not the **words**.
   `L` is a budget of letters.
2. The literal / denotational `[any]` decision is now a single global option with one parse, and a
   per-instance choice beats the bisect knobs. That makes it possible to run sibling absorption in
   the mode where it is sound in both channels.

---

## 1. What `total` was, and what it is now

The old measure charged `current.pathCount` per paid mint: **one unit per accessor sequence sold,
regardless of its length.** A chain of forty accessors and a single first step both billed 1 per
word. Correct as a count of words; wrong as a bound on materialised structure, which is what `L` is
supposed to bound.

The new measure charges the **length** of every word it authorises. Each state carries

```
pathCount  -- how many sequences reach it            (already existed)
lengthSum  -- the sum of THEIR LENGTHS               (new)
```

and the whole update rule is one line, at the mint:

```
child.pathCount = current.pathCount
child.lengthSum = current.lengthSum + current.pathCount    -- one more letter on each word
charge          = child.lengthSum                          -- the new words' letters, in full
```

`charge = child.lengthSum` is exact rather than approximate: `total` is the running
`SUM over states of lengthSum`, minting `child` is the only thing that changes it, and no other
state's contribution moves. On a chain `a`, `ab`, `abc` the charges are 1, 2, 3 and `total` is 6 —
literally *the sum over all paths of the path's length*, which is what was asked for. The legacy
measure answers 3.

A merge accumulates `lengthSum` exactly as it accumulates `pathCount`: summed when the two states
are reached by genuinely different sequences, `max` when a cross-dag cascade has paired states
reached by the SAME sequence in two fused automata and the union overlaps by construction.

### Why this is monotone, and why the recomputed version is not

The concern that killed the first reading of this idea was termination: `mergeStates` **destroys**
states, so *"sum of path lengths over the automaton as it currently stands"* **falls** when a chain
folds into a self-loop. A budget a program loop can hand back never terminates.

The accumulator does not have that problem, because it never looks at the automaton. `total` is a
sum over mint **events** — over history — and a fold is not a mint. Folding the three-state chain
above onto its origin leaves `total` at 6 while the surviving structure has one state and three
self-loops. Pinned by `folding a chain into a loop never lowers the pot`.

That also gives the cycle rule its precise reading. A mint always creates a **fresh** state, so at
the instant of every charge the structure is acyclic and the charge is exactly the acyclic sum. A
cycle only ever appears afterwards, from a fold, and the transition that closes it was already
charged once as a tree edge. Every later lap finds the transition present, mints nothing and charges
nothing.

> **Each cycle is charged for at most one lap.** That is what makes the measure finite where the
> accepted language is not, and it is why nothing here ever traverses the automaton — the standing
> constraint from `AnyUnrollState`'s KDoc, which the cyclic structure makes non-negotiable.

Pinned by `a cycle is charged at most one lap`.

### The unit changed, so `L` changed meaning

This is not a free correction. At a fixed `L`, the new measure exhausts a pot **sooner** — by a
factor of the mean word length — because it bills the same structure more. `-Dopentaint.anyPathLengthCost=false`
restores the word count as an ablation, and it is the arm every "did the measure or the budget move
this?" question is answered against. A `total` printed under one measure cannot be compared with a
`total` printed under the other.

---

## 2. One global option

`opentaint.literalAnyMatch` was read in two places that could not see each other, and the `.part`
bisect rungs consulted a JVM-wide property **in preference to** the constructor argument.

- **`Cleaner.kt` parsed the property on its own file.** Its use site is inside
  `FinalFactAp.cleanConcrete`, which has no `ApManager` in scope, so no per-instance override could
  reach it: a manager built with `literalAnyMatch = false` still got literal-era cleaning in the
  same JVM, silently and in the direction that changes findings.
- **`partOverride` inverted precedence.** `literalAnyMatch = false` in a test meant "false unless
  some `-D` I never set says otherwise".

Both are now `AnyMatchMode` (`ap/ifds/access/AnyMatchMode.kt`): one object, one parse, `literal` and
`exactCleanerKeepsAny` beside each other because they are one decision. `TreeApManager` delegates
its default there, and a part rung is consulted **only** when the instance agrees with the global
default — an instance constructed against it made a deliberate choice and a bisect knob does not
overrule it. Pinned by `AnyMatchModeTest`.

---

## 3. Measured: the corrected cost is right, and on conductor it changes nothing

Conductor, single entry point (`WorkflowResource#rerun`), single rule, frontier flags
(`anyUnrollLimit=100`, `rescore`, `bfs`), 8 GB, 300 s IFDS budget. `found` is the analyzer's own
pre-trace count (`vulnerabilities: N`); the SARIF count is not usable as a findings metric here
because trace reconstruction is what the non-converging arms run out of time in.

| cost measure | rc | wall | events | found |
|---|---|---:|---:|---:|
| legacy: one per word | 253 low-memory | 157.2 s | 676,059 | 2 |
| **path length (new default)** | 253 low-memory | 159.8 s | 681,151 | 2 |

Indistinguishable. The pot census says why, and it is not that the correction is inert:

| `-Dopentaint.anyManagerDiag=true` | legacy | path length |
|---|---:|---:|
| live pots / `crossedLimit` at `L = 100` | 298 / **1** | 298 / **1** |
| pots below a total of 2 | 278 | 278 |
| largest totals, `total/states` | 205/165, **23/6**, 13/11, 12/13, 8/7, 7/1 | 205/165, **54/6**, 13/11, 12/13, 10/1, 10/7 |
| mints / transitions, whole run | 604 / 368 | 604 / 365 |
| mint kinds, paid / credit | 200 / 168 | 195 / 170 |
| re-scores: n, visited, demoted | 1, 19, **2** | 2, 185, **43** |

The measure has teeth. The second-largest pot goes **23 → 54 on the same 6 states** — a factor of
2.35, which is the mean length of the words those six states are reached by, exactly the quantity
the old measure could not see. It triggers a second re-score and demotes 43 states where the old one
demoted 2.

And it does not matter, because **the pots are tiny**: 604 mints and 368 transitions in the entire
run, against 6.6 M prepends. 278 of 298 origins materialise almost nothing whichever way they are
billed, and the same single pot crosses `L` under both. The one pot that crosses reaches 205 either
way — past the limit every mint is `CREDIT` and free, so a crossed pot stops where it stops.

> The `[any]` automaton was never the binding constraint on conductor. The explosion is in the fact
> trees; the manager's whole state population would fit on one screen.

This also fixes what the correction is FOR. Since the never-unroll commit removed the callers of
`readChildPaidOnly` and `budgetExhausted`, the **only** production consumer of the `PAID`/`CREDIT`
stamp is `writesAbove` at `AccessTree.kt:1917` — the absorbing prepend. So the cost function's entire
production effect is *how soon a state becomes eligible for that one absorption*, which fires 10
times in 6.6 M. Correcting the counter is worth doing because a budget that bills a forty-accessor
chain as 1 is not a budget; it is not worth doing as a performance lever, and this measurement is
what says so.

---

## 4. Measured: switching the global option does not make sibling absorption usable

The hypothesis was that sibling absorption — sound as a widening of the DENOTATION, but a narrowing
of what a fact can MATCH under the literal reader — becomes usable if the engine is switched to
denotational matching. It does not, and the reason is sharper than the hypothesis.

`folded` / `mass` are `edgeStore siblingAbsorb`, from the `-Dopentaint.edgeCensus=true` arms.

| matching mode | absorb | rc | wall | events | folded | mass | found |
|---|---|---|---:|---:|---:|---:|---:|
| literal (shipped) | off | 253 low-memory | 157.2 s | 676,059 | – | – | **2** |
| literal | **on** | **0 converged** | 44.5 s | 383,438 | 528,602 | 1,392,988 | **0** |
| denotational | off | 254 timeout | 271.4 s | 2,232,395 | – | – | **2** |
| **denotational** | **on** | 254 timeout | 271.3 s | 2,339,862 | **19** | **85** | **2** |
| mixed: denotational reader + lookup, literal premises | off | 253 low-memory | 119.2 s | 619,609 | – | – | **0** |
| mixed | on | 0 converged | 48.3 s | 379,783 | 3,727,054 | 9,121,773 | 0 |

**The decisive row is the fourth. Under denotational matching, absorption folds 19 branches in the
whole run — against 528,602 under literal matching. It keeps the findings because it does nothing.**

The reason is that the two modes do not share a fact population. The denotational reader comes with
the R3c/R4 premise ladder, which hands out CONCRETE premises; summaries are keyed concretely, and the
facts that come back carry no `[any]` for the fold to find. The earlier census measured the same
thing from the other side: **0** `[any]`-owning nodes in 2,714 sampled facts under that reader,
against 39,944 in 723 under the literal one.

So the matrix needed a cell where absorption has material AND the reader cannot narrow: literal
premises (which keep `[any]` in the facts) with the denotational reader and lookup. That is the
"mixed" row, and it folds 3.7 M branches and converges in 48 s — **but its own control, mixed WITHOUT
absorption, already reports 0.** The mixed mode loses the witness on its own; absorption is not what
broke it, and the denotational reader is not what saves it.

That control is what turns this from a null result into an explanation:

> The loss is upstream of matching. Premise EMISSION walks the fact's literal edges, and absorption's
> saving IS the deletion of literal edges — the covered branch merges into `[any].*`, where `*`
> denotes everything and the branch's mass disappears. **The names and the mass are the same object.**
> A mode in which the fold is harmless is a mode in which it is inert.

Nothing in the reader can fix that, because no reader is consulted for an accessor nobody demanded.
The open design question is unchanged and now has a second independent measurement behind it: until
the names R2/R3b need are recorded somewhere the fold does not touch, no fact-side compression is
adoptable, however sound.

`-Dopentaint.absorbSiblings` therefore still ships **off**, and the three implementation defects
recorded against it (fixpoint under an uncovered accessor, the unhooked third store, the untested
manager arm) are now fixed regardless — see §5.

---

## 5. What shipped

| | default | flag |
|---|---|---|
| pot charges path length | **on** | `-Dopentaint.anyPathLengthCost=false` restores the word count |
| one global matching option | – | `-Dopentaint.literalAnyMatch=true\|false`, parts under it |
| sibling absorption | off | `-Dopentaint.absorbSiblings=true` |

Sibling absorption's recorded defects, fixed here:

1. **Fixpoint under an uncovered accessor.** `compressAbsorbCoveredSiblings` now re-folds the merged
   `[any]` child and loops until a pass returns the receiver by identity, so an `[any]` sitting below
   an uncovered accessor no longer leaves a covered-sibling pattern one level down. The identity
   return is preserved — a pass over an already-folded node returns it unchanged, which is what the
   storage layer's `merged === stored` test requires. Pinned by
   `the fold is a fixpoint under an uncovered accessor`, verified to FAIL with the loop removed.
2. **The third whole-propagating store.** `MethodEdgesNDInitialToFinalTreeApSet` is hooked, guard
   first, matching the other two.
3. **The untested manager arm.** `SiblingAbsorptionTest` now runs every case against two managers,
   `anyUnrollLimit = -1` and `= 100`, and asserts `(anyId != null) == containsAnyAccessor()` over the
   whole result of every fold. 7 bodies, 14 tests.

**Gates.** Rule-level suite **byte-identical under both cost measures**: 688 success, 0 skipped, 0
false positives, and the one `bad-hexa-conversion` false negative present in every arm including the
unmodified one. Unit gate 3520 / 2 — the two `JIRFactTypeCheckerUnrollFilterTest` failures are
pre-existing and unrelated.

Still not fixed: the fresh memo per top-level call and the `k` suffix-matcher rebuilds over a growing
subtree. Accumulating the siblings and merging once into the `[any]` child removes the quadratic term
and is the right moment to thread one memo through the loop.
