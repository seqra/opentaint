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
what D's own Prediction 1 was written to detect. Nothing loses a finding: every arm that reaches the
sink finds the same two vulnerabilities (§4), and the one arm that converges produces a
byte-identical SARIF.

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
the 8 GB low-memory stop, so **no arm converges** and the finding column is a race, not a verdict.
§4 settles it: every arm that reaches the sink finds the same two vulnerabilities in every build, and
what varies is whether their traces can be reconstructed before a second, separate timeout.

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

## 4. It does not lose a finding. It loses a TRACE, and only at `L = 8`

The SARIF column in §2 reads 2 / 1 / 0 / 0 / 2 across the `L ≥ 0` arms, which looks like a soundness
regression and is not one. The analyzer log separates the two, and the separation is unambiguous:

| arm | `Total vulnerabilities` | trace resolution | filtered for want of a trace | SARIF |
|---|---|---|---|---|
| `base-Loff` | **2** | 2/2 in 2.6 s | 0 | 2 |
| `step6-Loff` | **2** | 2/2 in **0.8 s** | 0 | 2 |
| `base-L8` | **2** | 2/2 in 1.9 s | 0 | 2 |
| `step4-L8` | **2** | **timeout** | 2 | 0 |
| `step6-L8` | **2** | **timeout** | 1 | 1 |
| `step6-L8` beyond | **2** | **timeout** | 2 | 0 |
| `step6-L100` | **2** | 2/2 in 7.6 s | 0 | 2 |
| `step4-L100` | **2** | 2/2 | 0 | 2 |
| `step6-L0`, `step4-L0` | **0** | — | — | 0 |
| `long-base-L8` (16 G, 1200 s) | **2** | 2/2 in ~40 s | 0 | 2 |
| `long-final-L8` (16 G, 1200 s) | **2** | **timeout** after 107 s | 2 | 0 |

**Every arm that reaches the sink reports two vulnerabilities.** The taint edge is found in every
build at every `L`. What fails is `ParallelProcessingContext`'s trace reconstruction, whose own
timeout then discards the vulnerability — the `Filter out N vulnerabilities without traces` class,
which is found-then-discarded rather than not-found.

At `L = 0` neither build reaches the sink inside the 300 s IFDS budget at all (`Total
vulnerabilities: 0`, 620 k events against `L = 8`'s 843 k). That is throughput, not the rule.

### 4.1 The cost belongs to step 3, not to the absorbing prepend

`step4-L8` is the build in which the prepend rule does not exist yet — the absorb is still the
shipped `budgetExhausted` one — and it already times out and loses both traces. `step6-L8`, with the
rule live, recovers one of the two. So the mechanism is **step 3**: once the read records past the
limit, two facts that used to be identical (both left holding the parent state by a refusal) become
two distinct nodes, and the graph the trace walker has to cross grows. Steps 5–6 shorten the facts
again and buy back part of it.

`long-final-L8` is the sharpest version: 16 GB, a 1200 s budget, **more** events processed than the
baseline (1,150,403 against 1,127,493), the same two vulnerabilities found, and the trace phase
running 107 s to a timeout where the baseline finished in ~40 s.

### 4.2 Where it converges, it is byte-identical

`rulesets/single-rule-nostar` is the only conductor arm that converges — 38 s, 188 k events, `rc 0`.
Across three builds it produces the **same `results.sarif`, sha256 `d14667c3c33b015f`**: baseline,
this build at `L = -1`, and this build at `L = 8`. Together with the 3,445-test gate and the two
`Loff` arms, that is the soundness evidence; the truncated arms are not.

### 4.3 And the default gets slightly better

`step6-Loff` resolves both traces in **0.8 s against the baseline's 2.6 s**, and runs 1 % more events
per second. One sample each, so it is an observation rather than a claim — but it is the right
direction, and it is the arm that ships.

---

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

## 6. The bigger number this uncovered

The design was aimed at one mechanism inside the `[any]` unroll budget. Measuring it produced a
sharper reading of the budget itself, and it is the most actionable thing here.

| arm | ev/s | concat calls | **graft points per call** | nodes/ev |
|---|---|---|---|---|
| `base-Loff` (budget off) | **9,444** | 5.86 M | **2.74** | 76 |
| `step6-L100` | 3,199 | 1.86 M | 16.61 | 260 |
| `base-L8` | 3,041 | 1.61 M | 17.50 | 210 |
| `step6-L8` | 2,811 | 1.58 M | 20.46 | 233 |
| `step6-L0` | 2,322 | 1.01 M | 17.63 | 202 |

**Turning the `[any]` unroll budget on multiplies graft points per concat call by six and cuts
throughput by three.** `Loff` and the `L ≥ 0` arms stop for different reasons — low memory at 8 GB
against the 300 s IFDS budget — so the wall clocks are not directly comparable, but the direction is
not in doubt: `Loff` processes 2.46 M events in 260 s, `L = 100` processes 886 k in 277 s.

The mechanism is the one §2.2 names. Refusing a read leaves the `[any]` in the delta; a delta that
carries an `[any]` is abstract at more positions; `concatToLeafAbstractNodes` grafts at *every*
abstract node of the conclusion. So the budget converts precision it declined to buy into breadth it
then has to pay for. The absorbing prepend shortens what gets grafted — `depthGain` per round-trip
call falls 21.49 → 17.32 — and does not touch how many places it gets grafted at.

---

## 7. What to do next

**Do not turn `anyUnrollLimit` on for conductor.** The default is `-1` and every arm above says that
is the right default on this workload. Both cuts have now been measured — the read-side one in
`2026-08-25-why-the-budget-does-not-help.md`, the write-side one here — and both move work rather
than removing it.

**Keep steps −1, 0 and 1 regardless.** They are not part of the budget. The subtree probe is a
soundness fix to an absorb that already shipped; the progress line is the instrument that made the
rest of this document possible; the incoming remap closes a retention hole that was measured open
(a `WeakReference` to a merged-away state surviving eight collections) and is what makes the backward
query complete. None of them is gated on `L`.

**If `anyUnrollLimit` is ever turned on, `L = 100` is the only value measured here that behaves.**
It is the fastest `L ≥ 0` arm (3,199 ev/s), it resolves both traces, and it is the only one where the
backward step is a genuine predecessor walk 99.5 % of the time. `L = 8` costs the traces (§4) and
`L = 0` does not reach the sink.

**Keep steps 2–6, off.** They convert a blunt cut into a targeted one — 5.7 M steps kept at `L = 0`,
12.7 M under `PreferBeyond`, each one a callee-produced accessor the shipped absorb would have
dropped — and they cost nothing at the default. D's Prediction 1 says a conserved total means steps
5–6 "should be reverted rather than tuned"; reverting them would restore a *less precise* absorb
inside a feature that is off, to fix a throughput problem the feature itself causes. The decision
that is actually open is about `anyUnrollLimit`, not about this design.

**Do not build step 4b.** §5.

**If step 3's cost matters later, it is a distinct and separable problem.** Recording past the limit
is what splits previously-identical facts into distinct nodes, and §4.1 attributes the trace-phase
timeout to it. The credit record is what the prepend rule keys on, so it cannot simply be removed —
but the population it creates (485 states, max 154 per dag, 12,677 transitions on this arm) is small,
and the cost is in how many distinct FACT nodes those states induce, not in the automaton. That is
the number to measure next if the budget is ever revisited.

**The levers that would move conductor are the ones D§16 lists as out of scope**, and nothing here
changes their ranking:

- the `java.lang.Object` erasure — 99.6 % of conductor's largest fact sits below one edge past which
  the type filter rejects nothing;
- the `ClassStatic` broadcast — one global singleton, 46 %;
- the star sources — 10 `$*` markers, 16–37×.

The graft's node mass is 131 M and this work attributes none of it. D§9.6(7) asked whether the
graft's relocation of 53 % of the caller's fact is the round trip in disguise. The answer is no: with
the budget off, the round trip fires on 0.25 % of concat calls.
