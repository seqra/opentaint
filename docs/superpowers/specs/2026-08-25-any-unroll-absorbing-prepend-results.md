# Absorbing the prepend: what shipped, and what conductor says about it

**Status:** implemented and measured. Companion to
`2026-08-25-any-unroll-absorbing-prepend-design.md` (**D§n**), which is the design; this document
records what was built, what was deliberately *not* built, and what the conductor single-endpoint arm
measured.

**Harness.** `opentaint-w3-benchmark-results/scoped-harness/`, conductor +
`WorkflowResource#rerun` + `rulesets/single-rule`, `-Xmx8g`, IFDS budget 300 s, both diagnostics on
(`anyManagerDiag`, `apOpDiag`). Baselines built from `378b8a724`, the last commit before this work.

**The one-line answer.** The mechanism works exactly as specified and does not move conductor's
number. The round trip closes — measurably, at the unit level and in `depthGain` — and the node mass
it was supposed to be feeding does not fall. That is D§R1, confirmed rather than refuted, and it is
what D's own Prediction 1 was written to detect.

---

## 1. What shipped

| step | commit | what |
|---|---|---|
| −1 | `56c0772f8` | the subtree probe on the existing absorb — the only step that can *gain* a finding |
| 0 | `f1c0c5a89` | the `[any]` population on the progress line |
| 1 | `59da25045` | the reverse index, and the two remap loops that close the retention hole |
| 2 | `85ba9914e` | `AnyUnrollKind` and `anyUnrollKindMerge` |
| 3 | `3cacaf4fe` | the read records past the limit; `readChildPaidOnly` keeps the old contract |
| 4 | `a3411d030` | `writesAbove` / `absorbInto`, and the shadow probe that took the measurement |
| 5+6 | `16090d6c6` | `create` becomes `installAbove`; the graft gets the list-to-list form |
| — | `e8d6900fb` `ecc36c027` `dd6d29344` | the round-trip closure test, R11, Appendix D, two more counters |

**Steps 5 and 6 landed in one commit** rather than two. They share one guard chain
(`absorbTargetFor`), and splitting them would have meant two near-identical bodies. Attribution
between the two funnels is by counter — `graftAbsorbs` against `absorptions` — which is finer than
two runs would have given: at every `L` measured, **96–99 % of all absorptions are the graft**, which
is the site D§1 says the budget never looks at.

**Step 4b — the subset construction on the reversed automaton — was NOT built.** §5 is the number
that decided it.

---

## 2. The arms

`find` is the SARIF count. Every `L ≥ 0` arm hits the 300 s IFDS budget and every `L = -1` arm hits
the 8 GB low-memory stop, so **no arm converges** and the finding column is a race, not a verdict —
§4 is where that is settled.

| arm | rc | wall s | progress | ev/s | find | concat calls | resultNodes | nodes/ev | concatAnyDelta | depthGain |
|---|---|---|---|---|---|---|---|---|---|---|
| `base-Loff` | 253 | 260 | 2,455,376 | 9,444 | 2 | 5.86 M | 186.4 M | 76 | 14,420 (0.25 %) | 186 k |
| `step6-Loff` | 253 | 225 | 2,145,135 | **9,534** | **2** | 5.17 M | 167.2 M | 78 | 11,159 (0.22 %) | 144 k |
| `base-L8` | 254 | 284 | 863,694 | 3,041 | 2 | 1.61 M | 181.5 M | 210 | 924,731 (57 %) | 19.87 M |
| `step6-L8` | 254 | 300 | 843,151 | 2,811 | 1 | 1.58 M | 196.2 M | 233 | 752,204 (48 %) | 16.34 M |
| `step6-L8` beyond | 254 | 293 | 775,658 | 2,647 | 0 | 1.55 M | 178.5 M | 230 | 716,099 (46 %) | 13.64 M |
| `step6-L0` | 254 | 267 | 619,955 | 2,322 | 0 | 1.01 M | 125.3 M | 202 | 601,645 (60 %) | 10.42 M |
| `step6-L100` | 254 | 277 | 886,302 | 3,199 | 2 | 1.86 M | 230.5 M | 260 | 187,246 (10 %) | 4.23 M |

### 2.1 The control holds

`step6-Loff` is bit-for-bit the shipped default (`L < 0` is "off entirely"). It finds the same 2,
runs 1 % faster, and every new counter reads zero. `depthGainPerCall` is **12.90 in both builds**.
Whatever the rest of this document says, the default configuration is untouched.

### 2.2 The round trip is made by the budget, not by the program

The single most useful number here is `concatAnyDelta` on the two `Loff` arms: **14,420 of 5.86 M
concat calls, 0.25 %**. With the manager off, the unroll materialises concrete premises and the
`[any]` does not survive into deltas, so the ratchet D§1 describes barely fires. Turn the budget on
at `L = 8` and it fires on **57 %** of concat calls.

The round trip is not a property of conductor. It is what the read-side cut *creates* when it refuses,
and this design is a fix for a mechanism the previous design switched on.

### 2.3 Prediction 1 is falsified

> *"At `L = 8` the conductor arm's `concat` result-node total falls materially below the 136.0 M it
> records today. If the total is conserved again — as it was across off/100/0 for the read-side cut —
> the round trip is not the channel."*

It does not fall. Normalised by events processed, node mass goes **210 → 233 per event (+11 %)** at
`L = 8`, and throughput falls 7.6 %. Only `L = 0` is roughly flat (202, −4 %).

What *does* fall is exactly what the design targets: `depthGain`, the depth the graft adds to
`[any]`-carrying deltas, drops **19.87 M → 16.34 M (−18 %)** at `L = 8` and to 10.42 M at `L = 0`.
The round trip closes. The saving does not appear in the total.

The reason is visible one column over: `pointsPerCall` — the number of abstract nodes the delta is
offered at — rises **17.50 → 20.46**. A shorter fact is a *coarser* fact, a coarser fact matches more
premises and attaches at more graft points, and the work moves rather than going away. That is the
same conservation `2026-08-25-why-the-budget-does-not-help.md` measured for the read-side cut, now
measured for the write-side one.

D§9.6(7) is therefore the standing answer: nothing links the graft's 131 M node total to the round
trip, and this design does not establish the link either.

---

## 3. What the counters say about the mechanism itself

Every obligation the design put on the implementation is discharged, on the real workload, at every
`L`:

| counter | reading | what it settles |
|---|---|---|
| `witnessDisagreesWithThreadedState` | **0** everywhere | Lemma 9.2 holds in production, where no unit test reaches: the backward query returns the state `filterStartsWith` had already threaded by hand |
| `kindDemotionsFromOrigin` | **0** everywhere | `ORIGIN` really is neutral, so the 98.8 %-cross-dag-fusion traffic is not deciding the cut |
| `graftAbsorbUnderClaim` | **0** everywhere | no receiver carrying a `DeepAccessorExclusion` reaches the graft pre-pass, so the depth-relative report D§4.6 discusses is genuinely not owed |
| `witnessForwardCheckFailed` | 0 / 1 / 5 | the racing window in the incoming remap is real and negligible, and it degrades to a miss |
| `remapDeferred` | **17** at `L = 8`, 9 at `L = 0` — 0.13 % of transitions | invariant (I) is NOT exact, and the code said it was |
| `guardBlocked` | 0 everywhere | §4.3's subtree probe never fired on conductor — the `[].[any].[]` shape it exists for is not present here |

### 3.0 One thing the implementation got wrong, and the counter caught it

The incoming remap declines to write when a predecessor's real forward edge resolves somewhere other
than the winner, and the code said that case was "unreachable if the mirror is exact". It is not.
`mergeStates`'s conflict arm QUEUES a pair rather than writing the transition, so between the
queueing and the drain a predecessor listed in `parents` genuinely does point at a state that has not
been unified yet — the same window D§5.5 describes for a lock-free reader, occurring *inside* the
drain. 17 events against 12,677 transitions.

Skipping is the arm that cannot drop a transition, and it is self-healing: the queued merge runs
later and its own remap moves that predecessor onto the winner. Until then the backward query misses
the edge and declines to absorb, which is the sound direction. The comment and the progress-line
rendering are corrected — `beyond > live` stays an alarm because it is an invariant of the counting
scheme; `remapDeferred` is a magnitude, reported so the window stays visible rather than assumed
away.

### 3.1 The targeting is the whole of the effect

`prependWrittenCreditMismatch` counts steps the rule KEPT that a budget-only form would have dropped
— D§2's null hypothesis, measured:

| arm | absorptions | of which graft | writtenMismatch (steps kept) | writtenPaid |
|---|---|---|---|---|
| `L = 100` | 17,287 | 17,244 | 804 | 15.0 M |
| `L = 8` | 113,047 | 112,314 | 2,845 | 26.0 M |
| `L = 8` beyond | 34.9 M | 34.6 M | **12.7 M** | 8,275 |
| `L = 0` | 14.3 M | 13.8 M | **5.7 M** | 8,371 |

At `L = 0` the shipped `addParentAbsorbingAny` would have dropped every one of those 5.7 M steps,
because its trigger is the pot and the pot is spent everywhere. The rule keeps them because the
automaton says the accessor is not a transition out of that `[any]` — the callee wrote it. That is a
precision improvement the throughput numbers do not show and the finding counts are too truncated to
show either.

### 3.2 `PreferBelow` at a middling `L` is the only configuration where the design behaves as designed

`absorbExact` (a genuine backward step to a predecessor) against `absorbStay` (a self-loop, i.e.
absorb in place — the shipped behaviour, but targeted):

| arm | absorbExact | absorbStay | reading |
|---|---|---|---|
| `L = 100` | 17,198 | 89 | 99.5 % genuine backward steps |
| `L = 8` | 111,903 | 1,144 | 99.0 % genuine backward steps |
| `L = 0` | 22,624 | 14,313,827 | 99.8 % in place |
| `L = 8` beyond | 14,753 | 34,911,618 | 99.96 % in place |

D§9.4(ii)'s claim — the absorption is the exact inverse of the read, so the round trip returns the
fact to the state it started from — is realised at `L ∈ {8, 100}` under `PreferBelow` and **collapses
at `L = 0` and under `PreferBeyond`**. The collapse is not a bug and D§10 anticipates it: once every
position is `CREDIT`, unions fuse ancestors with descendants and the automaton becomes self-loops, at
which point `absorbInto` correctly answers "stay put". The mechanism degenerates to the shipped
absorb — but a *targeted* one, which is what §3.1's 5.7 M and 12.7 M columns are.

### 3.3 Prediction 2, on the knob

> *"`PreferBeyond` shows a lower node total and a higher `rederivationsAfterKindChange` than
> `PreferBelow` at the same `L`."*

Half right. `PreferBeyond` does show a lower node total (178.5 M vs 196.2 M) — and it does it by
absorbing 300× more often (34.9 M vs 113 k) and processing 8 % fewer events. Per event the two are
within 1 % (230 vs 233). Kind churn is tiny in both (73/0 promotions/genuine demotions under
`beyond`, 53/22 under `below`), so the re-derivation cost the prediction expected never
materialised — because there are only ~500 states in the whole run to change kind.

The knob is real and it does what it says. Neither setting moves the number.

---

## 4. TBD: does it lose a finding?

---

## 5. Step 4b was not built, and the counter is why

D§5.8(i) made the subset construction conditional on one number taken before writing it. Two were
taken.

**Forks are real.** `absorbForkHits` = 92,039 at `L = 8` on the step-4 shadow probe, with
`maxWidth = 10`; 3,155–10,487 with the rule live. The reversed automaton is an NFA on conductor, as
D§5.8(a) predicted from the fusion rate.

**And the fork is not what stops the telescope.** `telescopeStallsAfterStep` — a fold that made at
least one backward step and *then* dead-ended, the only population a lazy determinisation could
rescue — against all stalls:

| arm | telescopeSteps | telescopeStalls | after ≥1 step | share |
|---|---|---|---|---|
| `L = 0` | 23,996 | 284,382 | 5,388 | **1.9 %** |
| `L = 8` | 39,843 | 389,020 | 10,959 | **2.8 %** |
| `L = 8` beyond | 33,232 | 341,751 | 8,358 | 2.4 % |
| `L = 100` | 40,303 | 489,216 | 9,060 | 1.9 % |

97–98 % of telescopes stall on the **first** link, where the fact's position is a single state and no
set of positions can exist yet. A stall there is not a mis-chosen fork; it is the targeting answering
correctly that the accessor never came out of that `[any]`.

That is Prediction 3's falsification condition — *"if the stalls do not fall, the fork was not what
stopped the telescope and §5.8 should be reverted rather than tuned"* — established **before** the
subsystem was written rather than after. The cost of finding out was two counters. D§5.8 stays in the
design document as an answered question: the widening of `AccessNode.anyId` to a value-typed
`AnyUnrollPos`, the identity edit across `hash` / `equals` / `InternStrategy`, and the three subset
operations were not written.

---

## 6. TBD: what to do next
