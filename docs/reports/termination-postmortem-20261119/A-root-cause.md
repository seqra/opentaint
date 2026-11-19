# Why the demand-refinement spec + term-task process failed

Read-only investigation, repo `/drive-testcomp/opentaint-go-rules/opentaint-w3`, branch `saloed/bidirectional`, 2026-11-19.
Short names used below:

- `TT` = `term-task.md`
- `SPEC` = `spec/demand-refinement-and-termination.md` (current, 1775 lines); `SPEC@impl` = the same file at `e342cdfba` (898 lines, the version commit `1197f72f7` implemented)
- `CAT` = `docs/reports/bidirectional-demand-termination-counterexamples-20261115.md`
- `PERF` = `docs/reports/bidirectional-demand-refinement-performance-20261118.md`
- `B101` = `docs/reports/bidirectional-termination-baseline-run101-20261118.md`
- `VAL` = `docs/reports/bidirectional-termination-fix-validation-20261117.md`
- `PROTO` = `docs/reports/bidirectional-demand-refinement-rule-prototypes-20261118.md`
- `AUDIT` = `spec/demand-refinement-no-loss-audit.md`
- `ROWS` = `docs/reports/bidirectional-demand-row-campaign-20261112.md`
- `IMPL` = `docs/design/bidirectional-demand-refinement-implementation-20261118.md`

Everything marked **[V]** I read directly in the cited file/commit. **[I]** is my inference.

---

## 0. One-paragraph answer

The process optimised a different problem from the one the real projects have. Three of the four real projects do not fail by "demand renewed forever"; they fail by running out of time or memory long before the run limit (ThingsBoard never finishes run-1; Conductor times out in run-8; Stirling-PDF times out in run-11). Only OWASP is a genuine run-limit recurrence, and its mechanism (a FLOW DATA demand renewed in a loop-free helper by a relative C5 cap plus a library-model "inside read") had already been traced and given a retirement predicate on 10 November. `TT` then (a) restricted counterexamples to synthetic ordinary code and excluded library models, (b) forbade the repair class that fixes OWASP ("hiding demand, cancelling Targets"), which pushed every repair toward "add more precise service on the hot path", (c) accepted stops in reference models as proof, and (d) had no measured gate on any real project. The spec that was implemented contained 35 rules, about 30 of them on per-fact/per-offer/per-publication paths, and zero demand-retirement rules: the only retirement rules (R37–R40) had been deferred. So the implementation could only add work, and it did.

---

## 1. Exact measured numbers of the failure

### 1.1 Implemented build (`1197f72f7`) vs previous bidirectional core (`472288cf3` ≡ parent `0438facd2`) [V] PERF "Comparison with the previous bidirectional core" (lines ~86–97)

| Project | Previous reached / completed / accepted fwd | Revised reached / completed / accepted fwd | run-1 engine s | run-2 engine s | Other |
|---|---|---|---|---|---|
| OWASP | 11 / 11 / 11 (RUN_LIMIT) | 11 / 11 / 11 (RUN_LIMIT) | 79.917 → 80.748 | 22.580 → 27.049 | run-11 engine 3.169 → 6.086 s; total engine 151.761 → 147.720 s |
| Conductor | 8 / 7 / 7 | **2 / 1 / 1, OOM** | 19.556 → 21.490 | **41.308 → 219.120 (OOM)** | H1 rows 127,044 → 173,371 |
| ThingsBoard | 1 / none / none (OOM) | 1 / none / none (OOM) | 183.641 → 179.704 | — | reachable heap within 0.1% of previous |
| Stirling-PDF | 11 / 10 / 9 | **4 / 3 / 3, timeout** | 21.127 → 24.516 | 13.783 → 41.852 | **run-3 engine 4.224 → 418.955 s (99x)**; run-4 566 s then timeout |

### 1.2 Implemented build vs legacy engine reference (`54ad708fe`) [V] PERF "Project results" (lines ~25–30, 72–75)

| Project | Reference status / wall s | Revised status / wall s | Findings ref / revised | Missing / extra | Peak RSS GiB ref → revised |
|---|---|---|---|---|---|
| OWASP | Complete / 156.357 | Run limit / 233.102 (+49.1%) | 2,633 / 2,633 | 0 / 0 | 8.58 → 9.75 |
| Conductor | OOM / 187.389 | OOM / 311.024 (+66.0%) | 7 / 2 | 5 / 0 | 9.36 → 9.68 |
| ThingsBoard | OOM / 439.652 | OOM / 333.842 | 15 / 0 | 15 / 0 | 13.48 → 13.79 |
| Stirling-PDF | Complete / 52.109 | Timeout / 1,118.766 (21.47x) | 24 / 28 | 10 / 14 | 7.58 → 9.96 |

Termination result of the implementation: **no project gained a natural stop.** OWASP still ends by RUN_LIMIT at run-11 with 776 handoff rows; the one rule-suite case that hit the cutoff (`PathTraversalServletSamples#streamFile`) still hit it (PERF "Test gates").

### 1.3 Native baseline that the termination work was supposed to improve [V] PROTO "Native baseline" (lines ~40–45)

| Project | Reached / completed / accepted | Status | Wall s |
|---|---|---|---|
| OWASP | 11 / 11 / 11 | Complete, **run limit** | 266.022 |
| Conductor | 8 / 7 / 7 | **Timeout** | 1,128.739 |
| ThingsBoard | 1 / none / none | **Memory guard** | 611.630 |
| Stirling-PDF | 11 / 10 / 9 | **Timeout** | 1,149.314 |

---

## 2. What the real unsolved termination cases are

### 2.1 OWASP `doSomething` helpers — the only measured uncapped real recurrence [V]

- Code (ROWS lines ~175–185): `bar = new String(Base64.decodeBase64(Base64.encodeBase64(param.getBytes())))`. Loop-free, recursion-free, one method key.
- Recurring rows: twelve `doSomething` owners account for all 72 repeated forward FLOW pairs at H11; `BenchmarkTest01000$Test#doSomething` repeats 6 forward and 8 backward FLOW DATA pairs every run from run-7/run-8 to run-101 (PERF "Cutoff evidence"; B101 lines ~57–60: 17 / 30 handoff pairs constant from run-7 to run-101 while the global limit goes 6 → 100).
- Mechanism, two producers (B101 lines 62–71; ROWS lines ~225–240):
  1. **Relative paired cap.** Raw `p.b.[].*/FLOW → ret.b.[].*/FLOW,N` is restricted against the shallow selector `ret.*/FLOW`; the relative cap `FL(Dp)+1` stays 1 (2 in the other direction) and republishes a DEMAND cut. "Increasing the global limit beyond those caps leaves the cuts unchanged."
  2. **Intrinsic MAY from a library-model inside read.** Applying a compiled relation with a deeper premise (`callee.arg(0).[].*/FLOW → callee.this.*/FLOW`, String constructor; `String#<string-bytes>` model field) to an ancestor STAR actual yields `[any]/FLOW, DEMAND` "without a field-limit cut. Increasing the limit does not resolve this particular operation when its input stays STAR."
- Proof that this is the whole problem for that entry: removing only the six helper FLOW pairs at the run-7 handoff makes the selected entry stop naturally at **run-11** with both findings (B101 "Isolated helper handoff ablation"); the R41 geometry ablation stops it at **run-7** (PROTO "R41 on the compiled OWASP entry").
- This is what **R41** addresses (SPEC §7.1, "Retire an independently replayable FLOW obligation"). It is a handoff-time *retirement* of a FLOW DATA demand whose transfers are all covered by retained NORMAL replay.
- Still unsolved: the general R41 guard keeps the OWASP demand through run-101 (closed-root variant rejects it because the entry has two roots; the certificate has zero "saved work" allowance at H4) — PROTO lines ~222, ~362–380.

### 2.2 R42 — protected/neutral uniform-cut guide [V]

SPEC §7.3: "The protected global-cut case needs this rule. A single caller input can yield a definite uniform reply and a cut descendant on DEMAND." B101 "Specification changes": "Use same-lane R42 for the neutral and protected uniform-cut cases." Its evidence is the synthetic *global-cut / protected global-cut* fixtures that natively still hit RUN_LIMIT at run-101 (B101 table line 25), not a real-project trace. PROTO line 223 classifies R42 as **USELESS**: frontier 6 → 3 at run-101, "The Target remained", OWASP unchanged. So R42 is not tied to a named real project. **[I]** It was added because the run-101 native baseline showed that fixtures the catalogue called "resolved" still do not stop natively.

### 2.3 Other OWASP run-11 rows [V] PERF "Cutoff evidence"

Of 776 H11 pairs: 20 are genuinely new (progress, nested-loop owners `BenchmarkTest02326#doPost`, `BenchmarkTest01474#doPost`), 72 are the helper FLOW family, **684 repeated pairs "retain their exact keys… Their complete dynamic guards remain open"** — i.e. unclassified. Loop-owner Target callbacks: 245,899 / 387,770 / 433,878 in run-7/9/11.

### 2.4 Rule-suite `PathTraversalServletSamples#streamFile` [V] PERF "Test gates"

"This is the known LOOP Target renewal… Deferred R37/R38 address that terminal service." A real (rule-test) LOOP Target case exists, and its rule was deferred.

### 2.5 Conductor, Stirling-PDF, ThingsBoard — not demand-renewal cases at all [V]/[I]

- [V] None of them reaches the run limit natively (1.3). ThingsBoard dies in run-1 before any handoff exists. Conductor's H5→H7 handoff grows 30,646 → 88,792 rows (ROWS line ~40) — a growing frontier, not a stationary one.
- [V] ROWS: across the three projects 25,389 repeated rows; **5,382 method rows vs 20,007 inner-block (loop) rows** (line 46); 20,754 rows OPEN after the coverage proof; OWASP 0 of 1,153 redundant.
- [I] For these three, "terminate without a hard limit" is not the binding constraint; per-run cost is. No rule in `SPEC@impl` reduces per-run cost.

---

## 3. Ranked root causes

### RC1 (process, highest). The problem statement was wrong for 3 of 4 projects: resource exhaustion was treated as non-termination. Confidence: high

- [V] Native baseline: Conductor timeout in run-8, ThingsBoard memory guard in run-1, Stirling-PDF timeout in run-11 (PROTO lines ~40–45). Only OWASP is "Complete, run limit".
- [V] TT line 54: "Assume no hard iteration limit. A finite run or repeated count is not a proof. Find an exact recurring demand…". TT has no time/memory dimension in its definition of a counterexample; a program that needs 8 expensive runs is not a counterexample.
- [V] `issues.md` (12 October) already listed "Memory growth prevents completion" as issue 1 on all four projects.
- [I] The campaign therefore could at best help OWASP, and any added per-run work was guaranteed to hurt the other three.

### RC2 (process). Synthetic-only scope excluded the real mechanism, although the real mechanism was already known. Confidence: high (H1 confirmed)

- [V] TT line 12: "We analyze synthetic data-flow reachability." TT lines 49–53: "Use fully analyzed ordinary code… Use no special pass rules, unresolved library models or predefined summaries… Prefer small examples."
- [V] CAT line 3: "Synthetic data-flow reachability investigation, 13–17 November." `grep -ci 'owasp|conductor|stirling|thingsboard'` on CAT returns **1** line, and that line was added by `758ad99ff` after the failure (CAT line 141).
- [V] The real OWASP producer #2 is exactly an excluded class: a compiled library relation (String constructor / `<string-bytes>` model) producing intrinsic MAY (ROWS ~225–240; B101 line 67 "a native inside read that already produces intrinsic MAY before C5"). CAT's own "Intrinsic MAY rule target" entry is "Excluded special-pass model; not solved by the current scope" (CAT status map).
- [V] The real trace and a fix predicate predate the campaign: `docs/reports/bidirectional-owasp-helper-cycle-20261110.md` and `spec/normal-backed-flow-demand-retirement.md` (10 Nov, "A FLOW demand can retire when every concrete transfer behind it already has an independently retained NORMAL replay route" — this is R41), plus `spec/flow-only-frontier-replay-retirement.md` and `spec/final-confirmed-report-demand-retirement.md` (11 Nov — the ancestors of R41's run-level candidates). `demand-task.md` ran on real post-handoff rows of OWASP/Conductor/Stirling. PERF line ~641 calls the 10 Nov proposal "a design experiment".
- [V] Mechanism-class mismatch: the catalogue's dominant shape is a **repeated root Target (ZERO→DT)** (B101 table: every row "Each retains the repeated root Target"); 11 of 24 entries are closed by R38 Target retirement (VAL line 7). The real OWASP stall is **FLOW DATA** pairs with no Target, no loop: "R37–R40 address Target service. The helper's repeated pairs are FLOW DATA and its method has no loop" (PERF line ~632).
- Qualification [V]: two catalogue entries (root-MAY renewal, global-cut growth) are in the same geometric family; the R41 ablation stops them too (PROTO line 222). But the catalogue marked them resolved via "current complete method reference stops at run-5" — a reference model — and they still hit RUN_LIMIT natively at run-101 (B101 line 25).

### RC3 (design + process). The rules that terminate were deferred; the rules that were implemented do not terminate anything. Confidence: high (H5 partly confirmed, see nuance)

- [V] `SPEC@impl` contains R01–R36 (35 distinct IDs, R17 withdrawn) and zero `[LOOP]`/`[REC]` markers; R37–R40 were removed in `e342cdfba` (−167 lines; diff deletes "### 6.4 R37/R38 terminal service proof", R39 rows) and moved to `spec/demand-target-retirement.md`. IMPL line ~24: "R37–R40 are future work."
- [V] `SPEC@impl` §6.2: "Keep typed Target compaction and the stop test." No rule changes the stop test or removes a live demand row.
- [V] The catalogue's stops depended on the deferred rules: VAL line 3 "Stops that use those rules apply to that reference scope"; `SPEC@impl` §4 COMPLEX: "The ordinary-delivery control reaches natural run-9 **with the deferred Target-retirement certificate**"; IMPL §6: "Keep stops that require R37–R40 attributed to that reference bundle."
- [V] Post-hoc isolated native test of each rule against the run-101 fixtures (PROTO lines 204–224): **USELESS** (no natural stop added) for R01–R03, R04, R06, R07, R08, R10, R20, R27, R29, R31, R32, R34, R37, R38, R42 and §8.1. Only five rules stopped any fixture: R13, R26, R35, R36 (one or three cleaner/nested-write fixtures each) and R41. All five are also marked COSTLY on peak RSS. None of the four that were in the implementation (R13, R26, R35, R36) stops OWASP.
- [V] Some rules made termination worse natively: R04 grew a fixture from 4 to 7 pairs; R06 turned a natural run-5 into a run-101 cutoff; R10 took the protected global-cut fixture from 7 pairs to 240 (PROTO lines 206–210).
- Nuance on H5 [V]: postponing LOOP/REC did not remove the fix for the *OWASP helper* (loop-free; needs R41, which never was in the spec). It did remove the only rules addressing (a) `streamFile`, the one rule-suite cutoff, (b) the 433,878 loop-owner Target callbacks in OWASP run-11, and (c) the class that is 79% of real repeated rows (20,007 of 25,389 are inner-block rows). And even un-deferred, R37/R38 are USELESS in the copy-only native scope. So: the deferral removed all retirement, but restoring it would not have been sufficient either.

### RC4 (process). TT forbade the repair class that works, and thereby selected for work-adding repairs. Confidence: medium-high

- [V] TT line 94–96: "Do not force termination by accepting unresolved candidates, hiding demand, canceling required Targets or weakening the stopping test." TT line 92: "Preserve increasing refinement precision and eventual precise observations under an uncapped schedule."
- [V] The rule that fixes the real case is precisely a certified demand omission at handoff (R41), and SPEC §7 is now titled "Discharge demand at the completed handoff".
- [V] Under that constraint the repairs became "serve the demand more precisely so that it empties by itself": new tail NE (R01–R03), extra C2 starts (R04–R08, R32), prepared children (R09–R12), extra possible saved reply (R34), "run C5 even if a saved NORMAL relation covers it" (R18), "keep distinct MAY and NE rows" (R23), "keep an admitted DEMAND row when a NORMAL MUST covers it" (R24), "a ready NORMAL result leaves the applicable DEMAND reply eligible" (R19).
- [V] R18 is the direct negation of the OWASP fix: PERF line ~643 "The active spec explicitly keeps ordinary C5 in the historical precoverage case"; PERF "R18 and R20–R23 retain the cut beside the precise result"; "The capture shows the active rules producing their specified results."
- [I] The soundness phase (3/4) is what pushed these rules to *keep* everything: each discovered loss was repaired by retaining another row or adding another start.

### RC5 (process). "Proved" meant "a reference model stops"; nothing was validated natively before implementation. Confidence: high (H4 confirmed)

- [V] TT line 161: "Production implementation stays unchanged". TT line 66: "State any difference between the formal reference and production".
- [V] VAL line 9: "The production driver at `966a40c36` does not implement the complete reference protocol." VAL last paragraph: "Native activation still requires correspondence for the actual scheduler, source permissions and physical ports."
- [V] Reference and native disagree in both directions: VAL line 54 "The long shared-word native control finishes at run-5 without the expected observation. The reference reaches it at run-13… The nested writer scalar pilot repeats at diagnostic run-9 while the native version naturally stops at run-5."
- [V] AUDIT §5 (lines 213–221, dated 17 Nov, before the implementation): "Those maps are activation obligations… Do not activate the full proposal by default based on scalar property tests." PERF line ~3: the scans ran with the comparative activation proof still open.
- [V] Scale of the formal effort: 7,554 cumulative Lean claims (VAL), 1,199 `.lean` files / ~365k lines under `spec/lean`, 121 proposal packages; 77 reports and 23 design docs dated 13–17 Nov (26 reports on 16 Nov alone); searches of 2,551,500 / 13,604 / 11,340 / 9,704 synthetic cases (CAT). **No Lean claim is about cost.** The first cost-related Lean file is `termination-rollback-20261118/HandoffBudget.lean`, written after the rollback, and it proves only bookkeeping of a saved/reserved counter.
- [V] The first native test of whether a rule stops a native fixture is PROTO (18 Nov, after rollback). Result: 17+ of the rule IDs do nothing.
- [V] `758ad99ff` adds the corrective sentence: "A selected rule cannot be enabled using only a reference model stop" (SPEC line 52).

### RC6 (process). No measured acceptance gate, no cost budget; "give bounds" was satisfied by local per-operation bounds. Confidence: high (H2 confirmed)

- [V] TT line 87: "Give bounds or representative before/after workload counts." No project, time, memory or event budget appears anywhere in TT. Completion criterion is "fresh searches in phases 1 and 3 find no further example in an explicitly stated scope".
- [V] Bounds actually given are local: "A new family has at most two starts" (R32 design doc §4); "cost one indexed candidate scan each"; "Projection still offers at most k·m pairs" (`SPEC@impl` §6.2); "Extra work is finite per row" (AUDIT R09/R10). CAT line ~1262: "no new project measurement is claimed."
- [V] R32's design doc states "This repair can add run-2 work" and stops there. Measured: the R32 same-head cell received 1,076,995 STAR row offers in Conductor run-2, **99.78% via shared static carry**; "The ordinary R32 proof example concerns a nonstatic wrapper" (PERF lines ~370–396). "At most two starts per family" was true and irrelevant — the multiplier was the number of families.
- [V] The real measurement gate existed only in `task.md` *after* implementation ("Implement the modification… Test…"), i.e. as a post-mortem, and IMPL §7 is titled "After implementation: investigate run-11 cutoffs".
- [V] The corrected gate was written only in `758ad99ff`: SPEC §8.4 "A reproducible increase on one project fails the variant regardless of savings elsewhere."

### RC7 (design). Rule accretion on hot paths, with repair-of-repair chains; the rule set is a semantics rewrite, not a termination patch. Confidence: high for counts, medium for classification (H3 confirmed)

- [V] Rule count: 37 IDs in the first committed spec (`8da26aa13`, 425 lines), 40 by `b29cc5ea5`, 35 at implementation, 41 now. The spec was rewritten 11 times in one day (18 Nov 09:13–18:13; line counts 425 → 750 → 830 → 1247 → 1135 → 1711 → 1498 → 1441 → 1058 → 898 → 1369).
- [V]/[I] Stage classification of the 35 implemented IDs (from the "stage" column of each rule table in `SPEC@impl`):
  - per-instruction transfer / fact representation: R01–R03, R13, R26, R29, R31, R35, R36 (9)
  - per-offer C2 admission: R04–R08, R32 (6)
  - per-row preparation and per-application matching/replay: R09–R12, R14, R15, R34 (7)
  - per-reply delivery and per-publication C5: R16, R18, R19, R20–R22 (6)
  - scheduler: R27 (1); invariants on storage/application: R30 (1)
  - handoff-time only: R23 (partly), R24 (partly), R25, R28, R33 (≈5)
  So ≈30 of 35 execute per fact/offer/publication, ≈5 at handoff. The implementation diff matches: 52 main-source files, +1,389/−262, concentrated in `DemandStore.kt` (+341), `RestrictedInitialPolicy.kt` (+206), `BlockRunState.kt`, `EdgeApplication.kt`, `DeltaWorklist.kt`, `MethodBlockRuntime.kt`, `Summary.kt`, `CalleeSubscriptions.kt`, `PublicationIndex.kt` — the C2/C5/delivery inner loops (`git show --stat 1197f72f7`).
- [V] Repair-of-repair chains:
  - R37 (report-ID Target retirement) → loses a second marking origin → **R38** supersedes it (CAT "Earlier source-specific four-phase result").
  - R39 NoRoute certificate → cannot certify nested reader → **R40** (CAT "Current search result").
  - Proposal's same-head STAR rejection → loses nested-overwrite observation that "the unchanged native engine… retains" → **R32** run-2 STAR relay (`bidirectional-nested-star-soundness-gap-20261117.md`: "This is a proposal regression, not a claim that the current production driver has this failure").
  - Exclusion-aware child replay → case 165 loss → **R34** possible DIRECT replay (CAT "Soundness status").
  - Cleaner/getter admission loss → **R31** disjoint-FLOW (CAT).
  - R17 (value-only omission) → proven to lose a track (AUDIT §1) → withdrawn; "Apply this same proof requirement to R16, R19 and R24".
  - R20 raw check, R07/R08, R15: AUDIT §3 gaps E/F list them as able to remove native service.
  At least R31, R32, R34, R38, R40 and the guards on R16/R19/R24 exist only to repair losses introduced by earlier *proposal* rules, never observed in production. **R32 — a repair of a self-inflicted synthetic soundness gap — is the measured trigger of the Conductor OOM.**

### RC8 (process). Postmortem-style iteration without convergence signal. Confidence: medium [I]

- [V] Each cycle ended with "No known open termination counterexample remains in the stated checked scopes" (CAT, five times) followed by a new counterexample in the next cycle. The search space was the model's own rule interactions, so every new rule created new places to find counterexamples.
- [I] The loop's termination condition ("fresh searches find no further example in an explicitly stated scope") is satisfiable by narrowing the scope, and the scope was narrowed three times (pass rules excluded, G1–G4 left open, LOOP/REC deferred).

---

## 4. Where the measured degradation came from (H6)

All [V] from PERF unless noted.

| Project | Mechanism | Rule(s) | Evidence |
|---|---|---|---|
| Conductor run-2 OOM | Same-head STAR start + FLOW companion admitted for every shared-static-carry offer | **R32** | Offers in the cell: 1,076,995, 99.78% from static carry. Restoring EXACT only for carry (D4): run-2 completes in 183.584 s, initial keys 2,730,060 → 1,168,385, caller groups 1,370,523 → 732,869 |
| Conductor run-2 | Auxiliary "qualified reply" channel for possible starts | R06/R09–R12 qualified delivery, R18/R20–R22 raw C5 | B diagnostic: run-2 completes in 98.344 s; `decide` DATA publications 133,031 → 19,758; qualified stores held 448,592 memberships beside 449,452 ordinary |
| Conductor run-2 | Lost fast paths | revised C2/C5 implementation | `decide` C2 cache hits 13,764 → **0** of 1,061,221 requests; static C2 coverage exits 935,842 → 0; static C2 states 99,701 → 4,525,716 (45.4x); static C5 2.9M → 9.45M |
| Conductor run-1→2 | More demand rows from NE / kept rows | R01–R03, R23 | H1 127,044 → 173,371 (+36.5%) |
| Stirling-PDF run-3/4 timeout | Loop boundary: complete observation (saved replay + C5) per attempted prefix | revised loop observation, revised C5/C2, raw witness (R20) | run-3 4.224 → 418.955 s; 2 contexts of `EmlProcessingUtils#decodeMimeHeader` = 1,455,858 observations, 524,384 prefix trials, 2,331,037 C5 queries; at abort 355,581 observations produced **33** row publications. PERF: "A stalled event count does not establish an uncapped demand cycle." |
| OWASP +49% wall vs legacy; run-11 engine 3.2 → 6.1 s | Terminal lookup | `DemandStore.visitControlPairs`, `RestrictedInitialPolicy.rawWitness` (R20) in 61/100 run-11 samples | |
| ThingsBoard | No change (dies in run-1 for unrelated volume reasons) | — | reachable heap within 0.1% |

Did the spec predict it? **No.** `SPEC@impl` COMPLEX notes say "R04–R08 and R32 use the scalar table, prefix tests and a bounded rewrite" and "The scheduler and block layout reuse the native engine". The only warning is the generic sentence in the R32 design doc ("can add run-2 work") and the AUDIT's "do not activate by default". The spec's own §3.4 concedes "No independent stop caused by the currently enabled preparation has been established." The static-carry interaction was outside every proof scope ("no… static… rule changes", R32 design doc §1). The current SPEC §8.3 table is the after-the-fact list of exactly these expansions.

---

## 5. Hypothesis verdicts

| # | Verdict | Key evidence |
|---|---|---|
| H1 synthetic bias | **Confirmed.** 0 of 24 catalogue entries from a real trace; real OWASP mechanism is FLOW DATA + library-model intrinsic MAY, a class TT excluded; catalogue is Target-dominated | TT 12, 49–53; CAT line 3; B101 62–71; PERF ~632 |
| H2 wrong objective | **Confirmed.** No real-project gate, no cost budget; bounds were local per-operation counts, never measured before implementation | TT 54, 87; CAT ~1262; SPEC §8.4 added afterwards |
| H3 rule accretion | **Confirmed.** 35 implemented IDs, ≈30 hot-path; ≥6 repair-of-repair chains; R32 chain ends in the Conductor OOM | §RC7 |
| H4 proof/prod gap | **Confirmed.** Reference ≠ production stated repeatedly; activation proof open at implementation; no cost proofs; 17+ rules USELESS natively | VAL 9, 54; AUDIT 213–221; PROTO 204–224 |
| H5 LOOP/REC postponement | **Partly.** It removed every retirement rule and the rules for the dominant real row class (79% inner-block) and for `streamFile`; but it is not why OWASP's helper was unsolved (that needed R41), and R37/R38 are natively USELESS in copy-only scope | ROWS 46; PERF "Test gates"; PROTO 220–221 |
| H6 perf source | **Identified, not predicted.** R32 on static carry + qualified reply channel (Conductor), per-prefix complete loop observation (Stirling), cache/fast-path bypass | §4 |

Truer root causes than the listed hypotheses: **RC1** (resource failure mislabelled as non-termination) and **RC4** (TT banned demand retirement, the only repair class that the evidence supports).

---

## 6. Timeline

| Date | Event | Source |
|---|---|---|
| 12 Oct | All four bidi runs end on memory guard; "memory growth prevents completion" | `issues.md` |
| 10 Nov | OWASP helper cycle traced from real capture; P(X) NORMAL-backed FLOW retirement proposed (= future R41) | `bidirectional-owasp-helper-cycle-20261110.md`, `spec/normal-backed-flow-demand-retirement.md` |
| 10–12 Nov | `demand-task.md` real-row campaign: 25,389 repeated rows, 20,007 inner-block; OWASP 0/1,153 redundant; intrinsic-MAY library read identified | ROWS |
| 12 Nov | Work-reduction baseline `472288cf3`: OWASP 11/11/11, Conductor 8/7/7, Stirling 11/10/9, ThingsBoard run-1 OOM | PERF |
| 13–17 Nov | Synthetic four-phase campaign (`TT`): 24 catalogue entries, R01–R40, 7,554 Lean claims, 77 reports; production untouched | CAT, VAL |
| 17 Nov | No-loss audit: R17 unsound; "do not activate the full proposal by default" | AUDIT |
| 18 Nov 09:13–14:17 | Spec committed and rewritten 10 times; R37–R40 deferred in `e342cdfba` | `git log` |
| 18 Nov 14:52 | Implementation proposal (`490894ea4`) | IMPL |
| 18 Nov 15:25 | `1197f72f7` implementation: 74 files, +1,895/−286 | `git show --stat` |
| 18 Nov | Project scans: Conductor OOM run-2, Stirling timeout run-4, OWASP still RUN_LIMIT | PERF |
| 18 Nov 18:12 | `0c3154701` rollback (73 files, −1,833) | |
| 18 Nov 18:13 | `758ad99ff`: run-101 native baselines, R41/R42 added, §8 release gates, 28 new native fixtures | B101, SPEC |
| 18–19 Nov | Isolated prototypes: 5 useful rules, rest USELESS; cost fixes | PROTO, cost-fix report |

---

## 7. Not verified / limits

- I did not rerun anything; all numbers are quoted from the reports.
- I did not read the Kotlin diff of `1197f72f7` line by line; the hot-path claim rests on the `--stat` file list plus PERF's profiler frames.
- The stage classification of rules in RC7 is my reading of the spec's stage columns; a few rules (R23, R24, R25) straddle publication and handoff.
- PERF attributes the Conductor OOM by ablation (D, D2, D3, D4, B, C); those ablations change coverage and PERF itself says they "give no full-coverage basis for either rollback". The causal claim is "trigger in the measured configuration", not sole cause.
- Whether Conductor/Stirling would exhibit an uncapped recurrence if given unlimited resources is unknown; no report establishes it. PERF explicitly declines to call Stirling's stall a demand cycle.
- The 684 unclassified repeated OWASP H11 pairs may hide further mechanisms.
- R42's link to a real project: I found none; it is justified by synthetic global-cut fixtures only.
