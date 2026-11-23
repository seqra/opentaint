# Natural termination for the bidirectional analyzer

Status: PROPOSAL, revision 3, 21 November 2026. Next iteration. All
mechanisms are native prototypes behind flags on local branches (§9).
None is merged.

- Stop: empty forward demand, or an exact fixed point (`FIXED_POINT`,
  §4). Gated alone and in combination.
- Requirement AC (§3A): every acyclic method reaches zero forward rows.
  Partly met: OWASP 33 → 6 rows, Stirling-PDF 47 → 43 (configuration S,
  §0A).
- Cyclic growth (§5): W gives Stirling-PDF a fixed point at run-33.
  Conductor still diverges.
- Current best configuration S (§0A): OWASP ends naturally at run-11 with
  the same report and about 21 % less driver time than native;
  Stirling-PDF ends at run-33; Conductor times out as before.

This proposal replaces
[termination-driver-stop-proposal.md](termination-driver-stop-proposal.md)
(revision 2). It follows the [design guide](design-guide.md). The
branches, reports and data are listed in §9.

## 0. Summary

The driver may stop only when it can prove that no later run changes the
result. Two conditions give that proof:

1. The forward demand is empty (`NO_DEMAND_EDGE`, as today).
2. The state repeats exactly, and the repetition does not depend on the
   field limit K (`FIXED_POINT`, new).

A stop test that reads the report state is not a proof. `QUIESCENT`
("no new confirmed report in two runs") and `DECIDED` ("every reached
report is confirmed") infer the future from the present. A native
fixture marks a deep field chain that ends in a boxed value: at each
small K the cut fact is filtered out, so the report state shows nothing,
and a later run with a larger K confirms the finding (§1.3). Both tests
are rejected.

Measured for `FIXED_POINT` (shadow logs and gate):

- 0 false stops in all measured analyses.
- OWASP stops naturally at run-17, with the same 2,633 findings as the
  run-11 cutoff. This costs 25-28 s more driver time than the cutoff.
- The two rule tests that hit the cutoff stop at run-9 and run-5.
- Without the K condition the test stops falsely in two native
  regressions. The K condition is what makes the test a proof.

Conductor and Stirling-PDF never repeat natively. On these projects,
paths grow by one repeated segment per pair of runs, through a loop or a
recursive call. Step 2 folds such a segment only where a loop traversal
or a recursive call adds it (W, §5.3). With W, Stirling-PDF reaches
`FIXED_POINT` at run-33 with the same report, and Conductor's
`getObject` growth stops. Conductor still diverges, because `replace`
grows by new combinations of distinct fields, not by repetition (§5.4).

The main acceptance criterion is requirement AC (§3A): every method or
block with no loop and no recursion, transitively, must become fully
summarized and lose all its forward demand rows after some run. This
needs no stop test. Natively it fails on every project. The fixes so far
(the MUST-cover reply rule, DemandTarget subsumption with the G6 drop
form, and "an EXACT cleaner does not apply to a MUST fact") remove most
of the residual. The rest comes from reads at a strict prefix of a
premise and a few makers on Stirling-PDF (§0A).

The run-11 cutoff stays until both steps pass their gates. Then the
driver deletes it (§6).

## 0A. Integrated result (21 November)

Branch `proto/termination-integration-20261120` merges the mechanisms
that passed their own gates. Configuration NT: canonical order (§4.3),
`FIXED_POINT` (§4), W (§5.3), the MUST-cover reply rule for acyclic
callees (§3A), DemandTarget subsumption X with the G6 drop form (§3A).
All flags are off by default. With all flags off the module suite, the
jvm-dataflow suite, the rule suite and OWASP match native.

| Case | Native | NT |
| --- | --- | --- |
| OWASP, interleaved triples at normal load | `RUN_LIMIT` 11; driver 133-134 s; wall 201-205 s | `FIXED_POINT` 17 in 9 of 9 launches; identical SARIF and code flows; driver 124 s; wall 192 s; late runs 0.9-1.0 s against 3.0-3.5 s |
| Stirling-PDF, 2 NT + 1 native, timeout 3,000 s | `RUN_LIMIT` 11 when fast; this native launch stalled 2,558 s in run-11 (driver 2,826 s) | `FIXED_POINT` 33 in 2 of 2; 32 confirmed + the same 2 provisional; driver 590-646 s |
| Conductor | timeout in run-8 | timeout in run-8; identical report; `replace` still diverges |
| Rule suite | 583 natural, 2 `RUN_LIMIT` | 584 `NO_DEMAND_EDGE`, 1 `FIXED_POINT` 11 (a loop owner); 585 of 585 reports equal |
| Module suite | — | no failure that a single mechanism does not also cause; report changes only for M4 (the intended G6 drop) and the two fault-injection fixtures |

Mechanisms do not interact: module failures and end runs are the union
of the single mechanisms; OWASP ends at run-17 as `FIXED_POINT` alone;
Stirling-PDF at run-33 as W alone. On OWASP W and the G6 drop form never
act.

Remaining forward demand on OWASP: a constant 336 rows from H7. Of these,
65 `doPost` roots with a loop keep 135 Target rows, their 65 post-loop
blocks 130, 38 `doGet` callers 38 relay rows, and 7 acyclic `doSomething`
helpers 33 DEMAND rows. All 9,609 late DEMAND sink witnesses are in block
scopes, which X does not cover (`engine/MethodBlockRuntime.kt:569-570`
lifts the block target to the root). The 7 helpers belong to the open
loop roots; their callers offer the same DEMAND facts in every run.

Requirement AC is not yet met:

- OWASP: 7 helpers, 33 rows, fed by cyclic callers.
- Stirling-PDF: 47 rows. 17 acyclic methods hold 39 (Target rows at
  conjunctive sinks and relays, DEMAND rows in `EmlParser` setters); one
  block that no loop precedes holds 8.
- 21 module fixtures and 1 rule case keep a DemandTarget at a sink that
  is never confirmed. X covers only confirmed sinks.

**AC closure** (branch `proto/ac-closure-20261121`, on top of NT; each
fix behind its own flag):

| Fix | What it does | Exact? |
| --- | --- | --- |
| `acCleanExact` | After an EXACT cleaner at `c` on `x.MUST`, the strict descendants of `c` had no NORMAL form, so the native code put the whole region on DEMAND. A new excluded-point member ε of the exclusion set lets `x.MUST{ε}` mean exactly the strict descendants, so a cleaned region splits into disjoint NORMAL pieces (at most depth + 1). | No loss measured. **Not selected** (21 November): replaced by the simpler rule that an EXACT cleaner does not apply to a MUST fact. The MUST fact stays NORMAL and unchanged; the cleaned point stays tainted (a precision trade). Gate running: `proto/must-cleaner-20261121`. |
| `acExactStart` | For a NORMAL actual deeper than an ANY entry in an acyclic callee, C2 starts the actual itself (the FLOW companions stay). | No loss measured. **Not selected** (21 November): it refines deeper than the demand requested and can explode the facts. Its volume is measured as evidence only. |
| `acC5Exact` | Acyclic methods publish without the relative C5 cap | No change alone |
| `acOfferClosure` | Do not start an acyclic callee for a DEMAND offer that its saved record covers | **Not exact**, withdrawn (below) |

Forward AC residual at the last forward barrier ("safe" = NT +
`acC5Exact` + `acCleanExact` + `acExactStart`):

| Gate | NT | safe | safe + offer closure |
| --- | --- | --- | --- |
| OWASP, 3 interleaved launches per arm | 33 | 6 | 0 |
| Stirling-PDF | 47 | 43 | 34 |
| Conductor (H7) | 21 | 15 | 10 |
| Rule suite | 8 (case 349) | 8 | 8 |
| Module suite (analyses / rows) | 21 / 56 | 5 / 6 | 5 / 6 |

- Project reports are identical in every arm (OWASP 2,633 / 0,
  Stirling-PDF 32 / 2, Conductor 7 / 0, rule suite 786 pass).
- OWASP with safe: the fixed point moves from run-17 to run-11; driver
  145-153 s → 127 s, wall 222-232 s → 203-205 s (both arms with the
  census on, which costs about 21 s). `acCleanExact` also stops most
  cyclic renewal on OWASP: forward rows 336 → 111.
- 16 module analyses change a provisional finding to confirmed: 6 from
  `acCleanExact`, 10 from `acExactStart`. Each fixture's own control case
  states that the confirmed answer is right. Under the gate rule this is
  a report change, so it needs a decision.
- The offer closure is the literal form of "a covered callee needs no
  start". It loses `delayed U sink` in `RepeatedDemandHiddenRenameTest`
  when combined with `acC5Exact`. The callee's DEMAND row is also the
  admission key for later, more refined offers: C2 admits starts only
  against a callee row, and the saved NORMAL record does not contain the
  hidden rename. So a row must not be suppressed. It must stop being
  produced, because its maker gives a NORMAL result.
- Makers of what remains:
  - OWASP: an inside read on a coarse FLOW premise in 3 helpers; a
    cleaner survivor in `Thing2` (a `toString` return rewriter with an
    EXACT reset under a MUST region), which 3 callers inherit.
  - Stirling-PDF: inside reads, one DEMAND-supplied start, DemandTargets
    with ND premises at a confirmed predicate sink
    (`bytesToWebResponse` and relays), a static-registry target in
    `AuthController#login`, and a block before a loop in
    `decodeMimeHeader`.
  - Module fixtures: 4 rows from an intrinsic MAY rule (outside the
    assumption), 2 others.
  - Rule case 349: not fixed.
- Next for inside reads: a NORMAL form instead of suppression. At an
  inside read of `p.*` at `p.q`, publish the record of the finer premise
  `p.q.*` in the same run, so that the coarse premise owns no row and
  later offers find the finer record.

**Configuration S** (branch `proto/must-cleaner-20261121`) = NT +
`acC5Exact` + an EXACT cleaner does not apply to a MUST fact
(`ap/Clean.kt:202, 230-240`; reference model `ap/Reference.kt:491-493`).
The rule acts when the reach is EXACT, the leaf is a MUST (`ANY_TAINT`)
leaf, and its region holds the cleaned point. The leaf stays unchanged
(layer, marks, exclusion, protection). Exact `$` marks at the point,
MAY and STAR leaves, FLOW facts and BELOW / AT_AND_BELOW cleaners keep
the native behaviour. On real code it fired 91-3,491 times per launch,
always on the MUST leaf at the cleaned root of `ret`, `<this>` or
`arg(0)` (`toString()`, `HtmlUtils.htmlEscape`, `prepareStatement`),
never in a backward run.

| Gate | NT | S |
| --- | --- | --- |
| OWASP reports (3 + 1 launches) | 2,633 / 0 | identical digest and code flows |
| Stirling-PDF, Conductor reports | 32 / 2; 7 / 0 | identical |
| Rule suite | 786 / 0 FN / 0 FP | identical; 467 SARIF results identical |
| Module suite (348 analyses) | — | 1 new confirmed finding (`UniformRootCleanerTerminationTest`, exact-root sink after `RemoveMark T` at `x` on `x.MUST/T`: the designed precision trade); 3 provisional → confirmed, as the fixtures state; 0 lost |
| OWASP acyclic residual | 33 | 6 from barrier 5 (the inside-read helpers) |
| OWASP forward rows (all / cyclic) | 336 / 303 | 99 / 93 |
| OWASP end | `FIXED_POINT` 17 | `FIXED_POINT` 11 |
| OWASP driver, census off (1 launch each) | 124 s (native 132-134 s) | **105 s** |
| Stirling-PDF residual, end | 47, run-33 | 43, run-33 |
| Conductor residual at H7 | 21 | 15; timeout in run-8 as before |
| Module suite open analyses / rows | 21 / 56 | 18 / 47 |

So OWASP now ends naturally at the run of today's cutoff, with the same
report, about 21 % faster than native. The contribution of `acC5Exact`
inside S is not isolated.

Volume of the rejected exact start (diagnostic, one launch per arm):
facts in the affected callees +28 % (OWASP), +60 % (Stirling-PDF),
+20 % (Conductor); over all methods +0.14 %, −0.005 %, +2.1 %. On
Conductor run-4, run-6 and run-7 took about 1-2 min longer each. In a
synthetic wide object graph it makes one premise per leaf at once (peak
256 premises per run against 16) but 35-38 % fewer facts in total.

**Loop-block DemandTarget renewal** (branch `proto/loop-dt-20261121`, on
S):

- The OWASP cyclic residual under S (93 rows) is three `doPost` loop
  roots (`02326`, `01418`, `01874`), their post-loop blocks and two
  `doGet` relays. On `02326` every late witness is at
  `write(bar.toCharArray())` in post-loop block 6, at two conjunctive
  sinks that are already confirmed. The DEMAND arm is a STAR start
  `var(7).<field>.*` below the NORMAL `var(7).MUST`; a `var(7).MAY` row
  admits it, and the sink's any-field seed makes that row in the
  backward run. The cycle is: witness → DemandTarget and seed → MAY row
  → STAR start → the same witness. The taint enters the block from
  outside, so the block never gets a complete target of its own.
- Why XE lost finding B in deep-chain D4: B has its own DemandTarget
  and seed, and its seed does reach the source. The cause is
  `LoopOutputRestriction.restrictScalar`: it drops a growing loop output
  that no consumer admits. In run-5 only the coarse row that A's
  any-field seed made kept the one-pass output `c.f$`. Without A's seed
  `c.f$` is dropped and `c.f.f$` is never made. This is the same native
  defect that loses loop-grown chains of depth 3 or more with all flags
  off: a loop is not monotone in K. Keeping the unobserved outputs
  restores B, but the analysis then runs to `RUN_LIMIT`.
- Rule LG (`-Dorg.opentaint.bidi.loopDtCover=true`): a DEMAND witness in
  a loop block, whose method root has a saved complete ZERO →
  NormalTarget for the same sink, emits no DemandTarget and no seed only
  when (a) every sink of the method that captured a seed so far is
  covered the same way, and (b) the method relayed no callee
  DemandTarget in this or the previous forward run. It reads only seeds,
  targets and complete summaries.

| Gate of LG alone on S | Result |
| --- | --- |
| New loop fixtures L1-L6 and D4 | no finding lost (XE lost B in L1, L2, L4, D4) |
| Module suites (366 analyses, 78 deep-chain variants) | 0 report changes; `LoopMarkOriginServiceTest` no longer refines the deep route of an already-confirmed sink (same report) |
| Rule suite | 585 of 585 identical; LG never acts |
| OWASP, 3 interleaved pairs | identical SARIF and code flows; **`NO_DEMAND_EDGE` at run-7** in 3 of 3 (S: `FIXED_POINT` 11); cyclic and helper rows go to 0 |
| OWASP driver, census off, 2 pairs | S 105.1 / 103.8 s, LG 101.3 / 100.2 s (native 132-134 s) |
| Stirling-PDF, Conductor (1 launch each) | identical reports and ends; LG never acts (its guard fails on all 15 Stirling-PDF candidates) |

So OWASP's forward demand becomes empty: the stop of the original task,
with the same report and about 25 % less driver time than native. LG
has no proof. Its guard avoids the loop-output interference, which is
live on Stirling-PDF (200,107 drops) and Conductor (672,433). The real
fix is to make the loop output restriction monotone in K; then LG's
guard may become unnecessary.

**Inside reads and the no-cap rule** (branch `proto/inside-read-20261121`):

- S without `acC5Exact` (S'): reports and ends equal, but the AC residual
  rises (OWASP 6 → 18, Stirling-PDF 43 → 44, Conductor 15 → 21), because
  the relative-cap rows come back. `acC5Exact` adds no facts: acyclic
  NORMAL facts fall by 1.0 % (OWASP), 0.1 % (Stirling-PDF), 1.1 %
  (Conductor). It stays.
- Trace (full OWASP): the only forward inside read in the helpers is the
  `new String(byte[])` model edge `arg(0).[].* → <this>.*` on the coarse
  premise `arg(1).String#bytes.*/FLOW`. The finer premise
  `…String#bytes.[].*` already exists and is NORMAL. The caller offers
  exact actuals `arg(1).String#bytes.$/T`, so the coarse premise starts
  in every run, and its DEMAND reply `ret.MAY` reaches those exact
  actuals, although an exact `$` holds no array element. That reply
  reaches the XSS sink and renews the callers' DemandTargets.
- Rule `insideReadNormal`: in forward restricted runs, in acyclic
  root-scope methods, at a NORMAL FLOW inside read of `P = b.p.*`, do not
  emit the DEMAND reply; start the finer premise `F = b.p.q.*` in the same
  run, and let C5 check F's publications against the entry of P's row.
  F is the rule's own read path and equals the backward image that the
  native row requests, so the rule stays inside the requested
  refinement. Natively C2 starts the same F later: on OWASP the same 24
  premises, 4 runs earlier. Saved replay finds F's record by prefix
  without a row. No proof.

| Gate | S | S + inside-read rule |
| --- | --- | --- |
| OWASP end (4 launches) | `FIXED_POINT` 11 | **`NO_DEMAND_EDGE` 7** in 4 of 4 |
| OWASP report | 2,633 / 0 | identical SARIF and code flows |
| OWASP driver / wall | 104-105 s / 181 s | **100-101 s / 177 s** (native 132-134 s driver) |
| OWASP forward rows / AC residual | 99 / 6 | **0 / 0 from H5** |
| Rule suite | — | the rule never fires; identical |
| Stirling-PDF (2 + 2) | `FIXED_POINT` 33, 32 / 2 | `FIXED_POINT` 33, **32 / 0**; AC residual 35, forward rows 484 (S: ~940) |
| Conductor (1 launch) | timeout in run-8 | same; run-6 **+10 %** (6:20 against 5:46-5:54); facts +5.4 % NORMAL, +12.9 % DEMAND, nearly all in cyclic methods |
| Module suite (348 analyses) | — | one report change: a fault-injection variant of `RepeatedDemandHiddenRenameTest` that removes the helper's coarse row now confirms the true finding; 0 lost |

- On OWASP this rule alone drains everything, also the cyclic callers,
  because their late demand was the DemandTarget renewal that the
  helpers' DEMAND replies fed. So it does the work of LG at the maker,
  without a guard. If it passes its gate, LG is not needed.
- **The rule fails its gate in this form** (decision of 23 November).
  The two Stirling-PDF stored-XSS candidates (`UserController.java:753`,
  `:768`, §5.5) disappear: `UserService#saveUser(Optional, String)` no
  longer hands off its DEMAND replies `__repo__.MAY` and `ret.MAY`.
  There is no trusted ground truth that calls this a precision gain, so
  it is a report change. Gate rule from now on: confirmed AND
  provisional results must stay identical; a change that looks like a
  precision gain is still a failure.
- The Conductor cost increase also fails "no performance loss" (n = 1);
  its cause is not traced.
- The same maker does two things. On OWASP the DEMAND reply to an exact
  actual only renews DemandTargets at confirmed sinks. On Stirling-PDF
  it also makes two sinks reached (and so provisional) that nothing
  confirms. A rule that removes the reply removes both. A form that
  passes must keep what the reply makes reached and remove only the
  demand that the reply renews.

**Stirling-PDF makers** (branch `proto/stirling-ac-20261121`, on S):

| Rows of the 43 | Owner | Maker |
| --- | --- | --- |
| 14 | `WebResponseUtils#bytesToWebResponse` | DEMAND arms of the XSS predicate sink with ND premises, fed by DEMAND offers from two cyclic callers |
| 10 | `multiPartFileToWebResponse`, 4 `FilterController` methods, entry points | relays of those DemandTargets |
| 3 | `AuthController#login` and its entry point | a self-renewing DemandTarget at the STAR static premise `REG.User#username.*`, started from a backward MAY row |
| 8 | `decodeMimeHeader` block 1 (in AC scope: no loop before it) | relative C5 cap at the block exit |
| 1 | `CustomHtmlSanitizer#sanitize` | a start that is DEMAND only because its caller offers DEMAND |
| 7 | inside-read owners | (the inside-read rule) |

- Ablation: dropping the 21 rows of `bytesToWebResponse` once at H7
  takes the residual 43 → 5 and the end `FIXED_POINT` 33 → 15, driver
  577 s → 81 s, same report and code flows. That one DemandTarget loop
  anchors 38 of the 43 rows and about half of Stirling-PDF's cyclic
  demand.
- No exact cover exists at the witness for ND premises. Covering a
  DEMAND arm with premise P by a complete NormalTarget whose premise is a
  subset of P loses `B@g:1` in attack fixture M3: the DEMAND arm's
  DemandTarget and seed are the only refinement channel for callers that
  bind the premise on DEMAND. X is exact only because ZERO needs no
  binding. Adding a channel at the caller (relay plus call-site seed)
  was exact but cost 3 min against 3.4 s in one forward run; withdrawn.
- Rule RX: the witness tags its DemandTarget with its report identity,
  and a tagged DemandTarget is not relayed into a caller that already
  has a complete ZERO → NormalTarget for that identity. Exact by the
  same argument as X (ZERO at the caller).

| Gate of RX on S | Result |
| --- | --- |
| Stirling-PDF, 2 launches | residual 43 → 19; end `FIXED_POINT` 33 → **15**; driver 577-581 s → **71-72 s**; forward rows 944 → 478; same report and code flows |
| OWASP, 2 launches | forward rows 99 → 11 (cyclic 93 → 9); residual 6 → 2; same report and time |
| Conductor | timeout in run-8 as before; same report; residual at H7 15 → 11 |
| Rule suite | identical |
| Module suite | 325 analyses identical (23 generated analyses not compared); 49 assertions fail because they compare the untagged DemandTarget object or count DemandTarget rows |

- `C5B` (the no-cap rule for acyclic blocks): `decodeMimeHeader` block
  rows 8 → 2, same report, +1.7 % driver time on Stirling-PDF (n = 2).
- Left on Stirling-PDF with RX: `bytesToWebResponse` 14 rows (its
  remaining DEMAND input is probably from a block of
  `PipelineController#handleData`, not traced), `login` 3 rows,
  `saveUser` 2 inside-read rows. The `bytesToWebResponse` STAR arms and
  the `login` STAR start both come from a backward MAY row that turns
  into a forward STAR start. That is the next maker to study.

Open questions for the next step:

1. Scope of AC for an acyclic callee of a cyclic caller: decided. The
   callee must reach zero rows anyway (§3A). (Running:
   `proto/ac-closure-20261121`.)
2. Makers of the DemandTarget at never-confirmed sinks in acyclic code
   (the 21 fixtures, Stirling-PDF's conjunctive sinks). The census named
   the cleaner survivor (`ap/Clean.kt:194-218`) as a forward MAY maker.
   A per-maker ablation is the next measurement.
3. DemandTarget renewal in loop blocks (cyclic; XE lost a finding in
   deep-chain D4).

## 1. What this iteration analysed

### 1.1 The updated rule spec (commits a0b18b4e1, 32b037292, a0a1978c6)

[demand-refinement-and-termination.md](demand-refinement-and-termination.md)
adds two run-level stop proofs to R41: a closed observer check and a
closed run-pair check (its §7.1). It keeps the run-11 cutoff and the
profile R13, R26/R35, R36, R41.

- Neither stop proof ran on OWASP, Conductor, Stirling-PDF or
  ThingsBoard. The scope bounds (at most 4 roots, 64 actors, 64 demand
  rows) excluded all four projects. The projects have 3,719 to 30,791
  roots.
- The only stop on real code is the compiled OWASP helper at run-11.
  That is the run of the production cutoff.
- The observer census reads the report state. It is rejected for the
  same reason as `DECIDED` (§1.3).
- The closed run-pair check is an exact fixed-point test. Step 1 keeps
  it, removes the scope bounds, and replaces the witness verifier by
  counters (§4).
- The work-removal items (one index build per seal, loop replay skips,
  bounded-cut fast path) do not change termination. They stay as
  separate performance items.
- Commit 32b037292 adds native regressions. Three of them decide this
  proposal:
  - `RepeatedDemandRelayTest`: equal demand at runs 3 and 5, natural
    stop at run-9, the finding confirmed only at run-9.
  - `RepeatedDemandHiddenRenameTest`: the same shape, stop at run-13.
  - `LoopMarkOriginServiceTest`: natural stops at run-13 and run-17.

### 1.2 The driver-stop proposal, revision 2

`QUIESCENT` stops at a forward run `i ≥ 5` when the confirmed set equals
the set two runs earlier. This is a cutoff with a floor.
`RepeatedDemandRelayTest` breaks it: the confirmed set is empty at runs
3, 5 and 7, so `QUIESCENT` stops at run-5 and the run-9 finding becomes
provisional. A fixed run constant (run-7) fails in the same way.

### 1.3 `DECIDED`, tried and rejected

`DECIDED` stopped at a forward barrier when every reached report was
confirmed (`L_i ⊆ C_i`). It was prototyped and gated (branch
`proto/decided-stop-20261119`). On the measured projects it changed no
report and cut Conductor from a 1,120 s timeout to 250 s.

It is still a guess. It assumes that a run at a small K reaches every
sink that a larger K reaches. Nothing in the design guarantees that.
Each operation that drops a fact must keep the cut fact whenever it
keeps the exact fact below it, and one documented operation does not
(the type-filter mark policy, interpreter gap G6, `ap/Primitives.kt:18-23`).

Native breaks (branches `proto/decided-stop-attack-20261119` and
`proto/deep-chain-fixture-20261120`):

- A deep field chain that ends in a boxed value (fixture D5):
  `x.f1.f2.f3.f4.value := T`, then `y = x.f1.f2.f3.f4` (an `Integer`),
  a use of `y` through a type filter, and a sink on `y.value`.

  | Run | K | L | C | Filter dropped T | Binding K reads |
  | ---: | ---: | --- | --- | ---: | ---: |
  | 1 | 1 | {A} | {A} | 1 | 1 |
  | 3 | 2 | {A} | {A} | 1 | 1 |
  | 5 | 4 | {A} | {A} | 1 | 1 |
  | 7 | 6 | {A, B} | {A, B} | 0 | 0 |

  At K ≤ 4 the read leaves the cut part as a MAY tail at the root of
  `y`. The filter drops T there, because `Integer` is boxed. The exact
  fact keeps T under the field `value`, which the filter does not read.
  `DECIDED` stops at run-1 and loses B. Native confirms B at run-7. The
  same holds at every prefix depth 1-6, and for `Integer[]` and
  `Integer[][]` values (9 of 16 variants; M4 is one of them).
- Plain deep chains (a deep source, a chain of writes, nested wrapper
  callees, a sink in a callee, a chain grown in a loop) did not break
  `DECIDED` in 56 variants. There the cut keeps T in a MAY tail on the
  DEMAND layer (`ap/Limit.kt:17-20`), the sink accepts it
  (`ap/MarkCheck.kt:27-33`), and B stays in `L∖C` until K reaches the
  chain. A fuzzer with deep paths (92,000 programs) found no other
  break.

- The same shapes with `String`, `String[]`, `String[][]`, a `String`
  inside a `List`/`Map` element, `int[]`/`byte[]`/`char[]`, user
  classes, or a primitive-tracking mark do not break `DECIDED` (189 of
  202 variants on branch `proto/string-chain-fixture-20261120`). All 13
  breaks need three things together: a boxed level (`Integer`,
  `Character`, `Long`, `Boolean`) on the root or the element spine of a
  filtered value, an ordinary (not primitive-tracking) mark, and an
  exact fact that continues under the boxed value's `value` field. The
  path filter is prefix-closed: a real-type check over 29 types and
  11,899 exact facts found no cut that it drops while it keeps the exact
  fact. Only the mark policy of the primitive-tracking option is not
  prefix-closed (`ap/Filter.kt:97-108`, `ap/Primitives.kt:47-48`,
  `JIRTypeFilters.kt:50-55`).

So the break is real, and it is a deep chain. One gap of the
interpreter is enough to make the report state lie about later runs.

The same gap is also a defect of the primitive-tracking option without
any stop test. When the boxed value comes out of a callee (for example
an approximation body for `List.get`), the run-1 drop leaves the sink
with no seed, the callee is never analysed again, and the native
analysis loses the finding at every run. A primitive-tracking mark, or
a policy that also reads the fields under a boxed level, restores it.
This is a separate item for the primitive-tracking option. A
repair for each such case (for example the G6 mark-policy changes on
branch `proto/decided-g6-20261119`) is a repair rule for a guess.
Design-guide rule 2 forbids that. `DECIDED` and its G6 repairs are
withdrawn.

## 2. The measured problem

Native runtime at HEAD, shadow logs with the cutoff raised to run-31 or
run-41.

| Case | End today | Demand after the last report change |
| --- | --- | --- |
| OWASP | `RUN_LIMIT` 11 | Exact period 2 from H7 (H8 backward) to run-41. Last persistent change at barrier 9. Last binding K read in run-15. |
| Conductor | timeout in run-8 | Diverges: 17,470 / 25,131 / 85,205 forward rows at H3/H5/H7. Records still grow at H7 (+1,891). |
| Stirling-PDF | `RUN_LIMIT` 11 or timeout | Counts constant from H17, but keys rotate, one record is added per pair of runs, and binding K reads never stop. |
| Rule suite, 585 cases | 583 natural, 2 at the cutoff | Exact period 2 in both cutoff cases |
| Module driver analyses, 314 | 199 natural, 30 at the test limit | Exact period 2 in 26 of the 30 |

Two facts decide the design.

1. Where the analysis does not grow, it repeats exactly. The repetition
   can be proved at a barrier.
2. Where it grows, a path grows by one repeated segment per pair of runs
   through a loop or a recursive call (§5.1). No stop test can end that
   honestly. The domain must become finite.

## 3. Why the demand does not end

A row is handed off when it is a DEMAND summary, any multi-premise (ND)
summary, a backward ZERO summary, or an outgoing DemandTarget
(`ap/Demand.kt:136-140`, `driver/HandOff.kt:51-71`). The barrier builds
a new demand store (`HandOff.kt:75`). Thus the driver has no memory of
demand, and it can test only "is the demand empty".

Most demand sources do not read K:

| Source | Code | Behaviour in later runs |
| --- | --- | --- |
| Relative C5 cap `FL(Dp)+1` | `store/DemandStore.kt:277-299` | Repeats when `FL(Dp)+1 < K`. The OWASP helper pairs recur from H7 to H101. |
| Read at a strict prefix ("inside read") | `ap/EdgeApplication.kt:83-94`, `ap/Summary.kt:120-140` | Repeats unless the caller offers a deeper actual |
| DEMAND start layer | `ap/AdmittedInitial.kt:11-30` | Repeats |
| DemandTarget at a sink | `engine/RunMethodLocalServices.kt:380-408` | Repeats. A confirmed sink can still emit DemandTargets. |
| ND and backward ZERO summaries | `store/RecordStore.kt:256-257` | Repeat. They are complete, but they are never persisted. |
| Global K cut | `ap/Limit.kt:7-19` | Changes with K. Ends for a finite path. Never ends for a path that repeats a segment. |

So most of the demand that never ends is a repetition. A run that serves
the same demand, on the same persistent state, with no read of K that
binds, does the same work and produces the same state. That is a fixed
point, and the driver can prove it (§4). Demand that changes with K is
real refinement. The driver must continue while it exists.

Earlier designs removed demand at the handoff (R37/R38, R41, R42).
Removal changes the next run. The regressions in 32b037292 show lost
findings when identical demand is removed (`RepeatedDemandRelayTest`,
`DistinctMarkOriginServiceTest`, `UniformCoverageOriginAuditTest`). A
fixed-point stop removes nothing. It only proves that continuing repeats.

## 3A. Requirement AC — acyclic code converges

This is the main acceptance criterion of the iteration.

**Definition.** An owner (a method or a block) is *acyclic* when it has
no loop, and no method that it reaches through resolved calls is
recursive or has a loop. A model without a body is a leaf. An analysed
approximation body is code. A block is acyclic only if, in addition, no
loop of the same method comes before it: a block after a loop gets its
facts from that loop. (My call: the census counted such post-loop blocks
as acyclic, and they hold all complete-row residual of acyclic owners on
OWASP.)

**Assumption.** JVM pass rules have no `[any]` in `from` or `to`.
Source and sink conditions with `[any]`, and conjunctions, are allowed.
They make MAY facts in backward runs only, never in forward runs.

**Requirement.** Under this assumption, for each acyclic owner there is
a forward run `i` after which the owner is fully summarized (its forward
summaries are NORMAL) and it has no row in any later forward handoff. No
stop test and no limit gives this. The analysis itself must converge.

The callers do not matter (decision of 21 November). If a method has no
demand row, the demand that a caller submits to it cannot change
anything in it: C2 admits no start there, and the caller uses the
method's saved complete records. So each acyclic method must reach zero
rows, also when a cyclic caller offers it DEMAND facts in every run. The
imprecision of such a caller is carried by the caller's own rows.

Backward handoffs may keep MAY rows that come from `[any]` source or sink
conditions and from conjunctions. They are allowed, but only if they
make no forward demand. The stop is tested at forward barriers only. So
when the forward handoff becomes empty, the analysis ends with
`NO_DEMAND_EDGE`, which is the stop of the original task. That is the
plan: no demand after a forward run.

**Why it must be possible.** In an acyclic cone every access path that
the code builds has a bounded depth D: each field write on a path adds
at most one accessor, and there is no cycle to repeat it. When K > D, no
global cut happens in the cone. Every DEMAND row that remains then comes
from a source that does not read K. Each such source must stop when the
cone is fully summarized:

| Source | Required behaviour in a fully summarized acyclic cone |
| --- | --- |
| Global K cut | Ends when K > D. Nothing to change. |
| Relative C5 cap `FL(Dp)+1` | The cut part must not come back as demand when the same relation is already complete (NORMAL) for a covering pair. |
| Read at a strict prefix ("inside read") | Ends when the offered facts are exact. A model that is MAY by itself needs a decision (open question below). |
| DEMAND start layer | A start may be DEMAND only while its input is DEMAND. |
| DemandTarget renewal | A DemandTarget comes only from a DEMAND arm. It ends when the arms are NORMAL. A DEMAND hit at a sink that the same owner already reaches with a complete ZERO → NormalTarget must not emit a DemandTarget or capture a seed. On full OWASP this is the dominant source: 919 control rows at 431 roots keep themselves alive with no DATA row. |
| Complete ND and backward ZERO summaries | They are complete but never persisted (`store/RecordStore.kt:256-257`), so each run hands them off again (`ap/Demand.kt:136-140`). The task says complete edges must be persisted and reused. Persist them, or stop handing them off once they are served. |

**Known violations (measured):**

- The OWASP `doSomething` helpers are loop-free. Their FLOW pairs recur
  from H7 to H101. Root cause (branch `proto/dosomething-fix-20261120`,
  traced on `BenchmarkTest01000#doPost`):
  1. A NORMAL start `var(27).MUST/T` in the caller's post-loop block
     offers `arg(1).MUST/T` to the helper. Saved replay returns the NORMAL
     reply `ret.MUST/T` first (`engine/RunMethodCallServices.kt:347`).
  2. The subscription also applies the helper's current DEMAND replies:
     `ret.MAY/T,D` from an inside read of the coarse premise
     `arg(1).X.*`, and `ret.Y.MAY/T,D` from a relative C5 cut
     (`RunMethodCallServices.kt:393-409`).
  3. The layer is part of the group key (`ap/Conclusions.kt:69-71`), so
     the MUST fact never covers the MAY fact. The DEMAND fact reaches the
     SQL sink and emits a DemandTarget.
  4. That Target renews the block's root MAY row backward. Its probes
     start the coarse helper premise again, and the `String(byte[])`
     model's read below that start recreates the inside read.

  No consumer needs the DEMAND reply: the MUST reply covers it. Removing
  only the one Target row, or only the 2 inside-read rows, gives
  `NO_DEMAND_EDGE` at run-11 on the entry. Removing the 4 cut rows does
  not.

  Fix (flag `-Dorg.opentaint.bidi.mustCoveredReply=true`, scoped by
  `mustCoveredAcyclicOnly=true`): in forward restricted runs, drop a
  current DEMAND callee reply when a NORMAL MUST leaf that saved replay
  resumed for the same caller premise and call point covers every leaf
  (same base and mark, MUST path a prefix, exclusion admits the rest).
  Protected facts are kept. Apply it only when the callee's call cone has
  no loop and no recursion.

  | Gate | Result |
  | --- | --- |
  | Single entry | `NO_DEMAND_EDGE` at run-5, 0 rows, equal report (native: `RUN_LIMIT` to run-41) |
  | Module suite, 342 analyses | 340 identical; 2 acyclic baseline fixtures now stop at run-7 with equal reports |
  | Rule suite | 585 of 585 identical; the rule never fires |
  | OWASP, 3 + 3 interleaved | identical SARIF in 7 launches; the 5 helper families have 0 rows from H5 (native 103 / 154 at H7 / H8); driver time native-like |
  | Conductor, scoped form | native-like rows and times; equal report. The unscoped form doubled the H7 rows (186,430) and is rejected. |

  Exactness: within the run, every dropped fact is DEMAND and covered by
  a NORMAL fact at the same premise and call point, so no NORMAL fact,
  record, NormalTarget or report of that run changes. Across runs it is
  not exact: on the entry, native adds 6 NORMAL records and 4 block
  NormalTargets in runs 5-8 that the fix never makes. No report changes
  anywhere. No proof.

  Full OWASP still ends at `RUN_LIMIT` (and `FIXED_POINT` at run-17).
  With the fix, 413 acyclic owners keep 935 forward rows at H7: 844 of
  them are DemandTarget renewal. At H8 the backward rows of acyclic
  owners are: complete backward-ZERO and ND rows 1,035, raw DEMAND 514,
  Target 328, DEMAND start 69, relative cap 26. Twenty other helpers
  still have rows; in the traced ones the caller renews its own
  MUST-premise Target. As an upper bound, dropping every Target row from
  H7 makes all four traced single entries stop naturally with equal
  reports. So this fix plus DemandTarget subsumption should empty most
  of OWASP's forward demand. That is an inference, not measured on the
  full project.
- The acyclic run-101 fixtures keep 1 Target and 2-7 pairs to run-101.
- `PassthroughFileModelSamples#fileToStringUnsafe` is straight-line
  code. It renews an anonymous Target in every forward run.

**Check.** A shadow census counts, per barrier, the acyclic owners
that still have rows, with their row kinds and the source counters in
the table. The count must reach 0 and stay 0 on OWASP, Stirling-PDF,
Conductor, the rule suite and the module suite.

**Native census** (branch `proto/acyclic-census-20261120`; classes from
the run-1 call plans, loop blocks and Tarjan SCCs; the source of 7 owners
read by hand):

| Case | Acyclic owners with rows | Reach 0 and stay | Never reach 0 | Acyclic share of open demand (last F / B) |
| --- | --- | --- | --- | --- |
| OWASP, cutoff 21 | 2,950 | 2,600, all by run-5 | 350 (164 `doPost`, 164 `doGet`, 22 `doSomething`) | 66 % / 67 % |
| Stirling-PDF, cutoff 21 | 3,288 | 3,271 | 17 | 4.4 % / 5.1 % |
| Conductor, runs 1-7 | 8,330 | 8,325 | 5 | 0.02 % |
| Rule suite | — | 583 cases end with no demand | `fileToStringUnsafe` | 100 % there |
| `AcyclicTerminationBaselineTest` | 2-3 per case | 0 | all, to run-101 | 100 % |

The open owners repeat with period 2. This is a fixed residual, not a
slow convergence. The residual in acyclic owners, by maker:

1. **DemandTarget renewal at an already-confirmed sink.** OWASP: 164
   roots, 468 forward rows. The DEMAND witness is a cleaner survivor: a
   `RemoveMark` cleaner on `ret` with reach EXACT leaves the marks below
   on the DEMAND layer (`ap/Clean.kt:194-218`). That survivor is the
   `DEMAND arg(0)/[any-taint]` fact at the conjunctive path-traversal
   sink. Checked for all 164 roots: 151 have no other maker.
2. **Relayed and backward-source DemandTargets** that follow from 1
   (`doGet` relays `doPost`). OWASP: 328 owners per barrier.
3. **Complete but not persisted rows.** Backward ZERO-premise NORMAL
   summaries are handed off again in every backward run. OWASP: 730 of
   1,481 backward acyclic rows. Stirling-PDF: 8, plus 5 ND rows.
4. **DEMAND rows from other MAY makers** (co-occurrence, not proven
   cause): the relative C5 cap with an inside read in helpers (OWASP
   `doSomething`; fixed by the MUST-cover rule above); a DEMAND sink
   seed; a reversed any-field condition; MAY rule edges; the DEMAND
   start layer.

**Rule-made MAYs.** No pass rule made a MAY. Three rule forms other than
pass rules do:

- A sink requirement with an any-field (`$*`) starts the backward seed
  on the DEMAND layer (`ap/Reference.kt:378`,
  `engine/RunMethodLocalServices.kt:475-490`). OWASP: 2,736 such seeds
  per backward run.
- A rule condition with an any-field, reversed in a backward run. The
  forward edge `this/[any] → ret` becomes the MAY `ret → this/[any]`.
  The rule is probably `$RES = (Object $*OBJ).toString()` in
  `rules/ruleset/java/lib/generic/path-traversal-sinks.yaml:15-18`
  (not traced to the compiled form).
- A conjunctive rule edge is a MAY edge (`MicroEdge.may`).

**DemandTarget renewal: ablation and prototype X** (branch
`proto/dt-subsumption-20261120`).

| OWASP arm, from H7 | End | Report |
| --- | --- | --- |
| Drop the control rows of owners whose renewed sinks are all confirmed (896 rows, 430 owners) | `NO_DEMAND_EDGE` at run-9 | identical |
| The same plus the FLOW and concrete DATA rows | `NO_DEMAND_EDGE` at run-7 | identical |

So the control-row cycle is the only anchor of OWASP's late demand.
With no forward Target row at a root, the backward run makes no row
there, and the helper DATA rows die with it.

Prototype X (`-Dorg.opentaint.bidi.dtSubsumption=true`): at a forward
sink witness, a DEMAND arm emits no DemandTarget and captures no seed
when the same method and block scope already has a complete ZERO →
NormalTarget for the same sink. Cost: at most three hash lookups per
DEMAND witness.

| Gate | Result |
| --- | --- |
| OWASP, 3 + 3 interleaved | identical SARIF; forward rows of loop-free owners 729-753 → 39-63 (no Target rows left); none of the 328 open loop-free roots keeps a row; late runs 3.5 s → 1.0 s |
| Rule suite | 0 report changes; `fileToStringUnsafe` ends with `NO_DEMAND_EDGE` at run-3 |
| Conductor, Stirling-PDF | identical reports; X never acts on Conductor |
| Module suite, X alone | **17 analyses lose finding B** (deep-chain D5, D6 and M4) |
| Module suite, X + G6 keep form (keep MAY-tail marks at boxed levels) | 0 report changes (keep form not selected) |
| G6 drop form alone (branch `proto/g6-drop-xsub-20261120`) | Prefix-closed over 29 real JIR types and 1,464 paths: 0 cut facts dropped while the exact fact is kept (native: 1,114). Removes finding B in M4, D5, D6 and the 13 boxed string-chain variants, at every K, as intended. Rule suite and all three projects: identical SARIF; the drop never acts on OWASP and drops no field leaf on Conductor or Stirling-PDF. |
| X + G6 drop form | Module suite: 0 report changes against the drop form alone. Rule suite, Conductor, Stirling-PDF: identical reports. OWASP, 3 + 3 + 3 interleaved: identical SARIF; forward rows of loop-free owners 711-753 → 39-63 (only `doSomething` FLOW and CONC rows; no Target row from H5); the loop roots unchanged. Still `RUN_LIMIT` at 41: driver 152-155 s against 140-141 s native at cutoff 11; late runs 1.0 s instead of 3.5 s. |

Why X fails without the G6 fix: the G6 gap hides B at a small K, so the
renewal of the confirmed sink A is the only demand that keeps the driver
running until K reaches B. X removes it, and the analysis ends before B
is confirmed. This is the same gap that broke `DECIDED`. X is correct
only if every sink that a later run can confirm keeps its own witness
and seed. That holds when the abstraction is monotone in K, so the G6
fix is a prerequisite of X, not an option.

Still open on OWASP with X: 66-70 `doPost` roots that have a loop, and
their `doGet` callers. Their DEMAND witness is in a loop block, whose
scope has no complete target of its own;
`engine/MethodBlockRuntime.kt:548-549` lifts the block DemandTarget to
the root. A variant that uses the root's target for the block (XE)
reaches `NO_DEMAND_EDGE` at run-7 on OWASP, but loses B in the deep-chain
fixture D4 (a chain grown in a loop): B's own seed does not find its
source, and the suppressed seed of A did. XE is withdrawn. These roots
are cyclic, so they are outside AC.

All three make MAY only in backward runs. The assumption allows them
(decision of 20 November). They count against AC only if they make a
forward row. So AC is measured on forward handoffs. On OWASP the forward
residual of acyclic owners is makers 1 and 2: DemandTarget renewal at
164 `doPost` roots (468 rows), the `doGet` relays, and 22 `doSomething`
helpers. The backward residual (maker 3, the `$*` seeds) matters only
where it keeps a forward row alive, as in the DemandTarget cycle.

**Relation to the other steps.** When AC holds, the open demand at late
runs is only in cyclic cones (loops and recursion). Where there is none,
the analysis ends with `NO_DEMAND_EDGE`, which is the definition of the
original task. Where there is some, `FIXED_POINT` (§4) proves that the
cyclic part repeats, and W (§5.3) makes cyclic growth finite.

**Under the assumption, no MAY comes from a model.** The rule
translator already rejects a pass rule with an `AnyField` premise
(`JIRRuleForms.kt:417`). A source with an `AnyField` target gives
`[any-taint]`, which is NORMAL and complete. Thus every MAY in an
acyclic owner is made by the analyzer:

- a global cut or a C5 cap cut;
- a rule or summary applied at a strict prefix of its premise, which is
  a STAR or MAY fact offered where the rule reads a deeper exact path
  (`ap/Reference.kt:300-317`, `ap/Summary.kt:120-140`);
- the DEMAND start layer.

The "library-model inside read" in the earlier OWASP trace is the second
case. The model is exact. The offered fact is too coarse. AC has no
exception for models.

The translator does not reject an `AnyField` target in a pass rule. A
rule set with such a target is outside the assumption, and AC does not
apply to the owners that use that rule.

## 4. Step 1 — exact fixed point

### 4.1 Definition

At a completed forward barrier of run `i`, stop with `FIXED_POINT` when
all three conditions hold:

1. **Equal handoffs.** The canonical key set of handoff `H_i` equals
   `H_{i-2}`, and `H_{i-1}` equals `H_{i-3}`. A key covers the full row:
   owner, scope, ports, both patterns (base, path, tail, exclusions,
   marks) and the control kind. The comparison does not depend on order.
2. **No persistent change.** Barriers `i-1` and `i` add or remove no
   NORMAL record key, add no NormalTarget, rule contributor or confirmed
   report, and do not change the seed set or the reached set `L`.
3. **No binding read of K.** In runs `i-1` and `i`: no global cut that
   cuts, no C5 clamp in the `depth ≥ K` branch that cuts, and no
   `fitsBudget` rejection. A read that fits at K also fits at each
   larger K.

```text
at a completed forward barrier i:
    if the handoff is empty:          end NO_DEMAND_EDGE   report C
    else if FIXED_POINT(i):           end FIXED_POINT      report C + (L_i ∖ C) provisional
    else if the policy cutoff holds:  end RUN_LIMIT        report C + (L_i ∖ C) provisional
    else: continue
```

The output is the output of every later cutoff: the state repeats, so
`C` and `L` do not change again.

### 4.2 Why it is a proof

Run `i+1` reads only the handoff, the persistent stores, K and the fixed
inputs (`IterationDriver.kt:237-243`, `engine/RunConfig.kt:15-26`).
Conditions 1 and 2 make these inputs equal to the inputs of run `i-1`,
except K. Condition 3 makes the run independent of K. Thus run `i+1`
repeats run `i-1`, and run `i+2` repeats run `i`. By induction, no later
run changes the state.

`closedPairRepeats` and `limitReadStable` in
[ClosedRunPair.lean](lean/proposals/termination-rollback-20261118/ClosedRunPair.lean)
prove this for a deterministic run function.

The deep-field-chain case does not break it. While a chain is deeper
than K, the chain is cut at K in each run. That is a binding read, so
condition 3 fails and the driver continues. In fixture D5 this is the
only condition that holds the stop back: at run-5 the handoff repeats
and nothing persistent changes, and one statement cut at K remains.
Without condition 3 the test would stop at run-5 and lose B. In all 78
deep-chain variants the full test never holds before B is confirmed.

Condition 3 is necessary. In `RepeatedDemandRelayTest` and
`RepeatedDemandHiddenRenameTest` the sealed state is equal for several
runs. Only K changes, and a later run confirms a finding. The variants
without condition 3 stop early in both tests. The full test does not.

### 4.3 Prerequisite: a deterministic handoff

The proof needs a deterministic run function. Production is not
deterministic yet:

- A shift of the JVM identity-hash order changed the end run of two fuzz
  programs (run-3 or run-5; run-5 or run-7) with the same report
  (branch `proto/decided-stop-attack-20261119`).
- Likely causes: `IdentityHashMap` iteration in
  `store/RunSummaries.kt:10`, which feeds the compaction tie-break by
  input order (`driver/HandoffCompactor.kt:54-55`); the `HashMap` order
  of the merged record index (`store/RecordStore.kt:149-162`);
  `recompact` by arrival order (`store/FlowBackedSummaries.kt:42-76`).
- OWASP H11 row counts differ between identical launches (975 to 1,153).

Required change: break every tie in handoff compaction and record
recompaction by a canonical key, not by arrival order. Then repeat the
identity-hash shift and the OWASP launches. Gate: equal reports, equal
handoff key sets across launches, end runs unchanged by the shift.

Result (branch `proto/deterministic-handoff-20261120`, flag
`-Dorg.opentaint.bidi.canonicalOrder=true`): ties are broken by 64-bit
content keys built from names, not interner ids. This covers the actor
order, the compaction tie-break, the demand-store rows, the record
arrival and index order, the seeds and the report representative.

| Probe | Without | With |
| --- | --- | --- |
| Fuzz, 20,000 programs, identity-hash shift 0..3: end-run / content changes | 2 / 2 | 0 / 0 |
| Fuzz, 1 vs 4 workers: programs that differ | 3 | 1 (same end and report) |
| Rule suite, 2 launches: analyses with different barrier digests | 1 of 585 | 0 of 585 |
| OWASP, 3 + 3 launches | handoffs differ from barrier 1 (975 / 1,017 / 1,111 / 1,153 rows) | handoff, C, L and NormalTargets equal at every barrier from barrier 2 |

Cost: about 1.4 s per OWASP analysis, all at the barrier (record sort
1.2 s); 0.71 s for Conductor's largest handoff (477,788 rows).

Still open: the run function itself is not confluent. With equal input
content in a different order, one run gives a different output (fuzz
seed 115126 run-5; `UnsafeFileUploadServlet#doPost` run-5). OWASP run-1,
which has no handoff input, gives two results (68,053 or 68,063 rows).
Suspected sources inside the engine, not fixed: the ND combination
resumes with the caller layer of member 0 and sorts members by
interning id; a covered row is published only if it arrives before the
row that covers it; accessor and mark ids follow interning order. Thus
the barrier is deterministic for a given run result, but the premise
"equal state gives an equal next run" holds only empirically.

Other inputs that the comparison does not cover:

- The prepared C5 program cache, whose key contains the clamped budget
  (`store/PreparedOutputPrograms.kt:107-109`), lives for one call
  (`store/DemandStore.kt:75`).
- Interners and soft caches in `SharedObjects` do not change semantics.
  This is an argument, not a proof.

### 4.4 Selected semantic scope

Changed:

- The stop decision at a completed forward barrier.
- `EndReason`: a new value `FIXED_POINT`.
- `ReportBuilder.build`: `FIXED_POINT` publishes `L∖C` as `RUN_LIMIT`
  does (`Report.kt:70-75`).
- Barrier bookkeeping: the handoff key sets of the last four barriers,
  the persistent deltas (`FlowBackedSummaries.addAll` already returns
  them), and one counter per K-read site.
- The tie-break order in handoff compaction and record recompaction
  (§4.3). It selects which of two equivalent rows is kept. It must not
  change a report.

Unchanged: field transfer, C2, C5, tails, layers, exclusions, summary
application, replay, publication, cleaners, the content of the handoff,
the run-1 and run-2 static views, the field-limit schedule, and the work
of each run.

### 4.5 Cost

| Operation | Site | Measured |
| --- | --- | --- |
| Handoff key hash | once per handoff row, at the barrier | at most 0.30 s per barrier (478k rows at Conductor H2) |
| Persistent deltas | at the barrier | already computed, now kept |
| K-read counters | one increment at a cut that already happens | driver time to barrier 5 on Conductor: 185.3 s native, 185.8 s with counters |
| Fixed-point check | once per forward barrier | at most 238 ms per barrier |

Shadow cost per analysis: 0.21 s on OWASP, 0.40 s on Stirling-PDF,
0.75 s on Conductor (0.7 %, 1.2 % and 4.9 % of barrier time). No work is
added per fact, per offer or per summary.

### 4.6 Measured results

Shadow logs (branch `proto/fixed-point-shadow-20261119`) and the gate
arm `DECIDED_FP` (branch `proto/decided-stop-20261119`):

| Case | First run where `FIXED_POINT` holds | Report at that run against the native end | After it |
| --- | --- | --- | --- |
| OWASP, 2 launches | 17 | 2,633 / 0 provisional, equal | nothing changes to run-41 |
| `UnsafeFileUploadServlet#doPost` | 9 | 1 confirmed, equal | nothing changes to run-41 |
| `PassthroughFileModelSamples#fileToStringUnsafe` | 5 | 1 confirmed, equal | nothing changes to run-41 |
| Module analyses at the test limit | holds in 26 of 30 | equal | 2 fixtures inject a fault at run-11: the stop at run-5 publishes a provisional entry that the faulted native run loses |
| Natural stops (199 module, 583 rule tests) | never before the native stop | — | — |
| Conductor, Stirling-PDF | never | — | — |
| Fuzzer, 45 programs where it held | — | equal | no later change |

- 0 false stops.
- OWASP: driver time to barrier 17 is 184-189 s, against 157-165 s to
  the cutoff at barrier 11.
- The K reads that delay OWASP to run-17 are statement cuts inside
  `doPost` bodies (112 of 118 at run-11 in `BenchmarkTest02302#doPost`).
  They fall to 0 at run-17.

Gate of `FIXED_POINT` alone, with canonical order (branch
`proto/deterministic-handoff-20261120`):

| Suite | Result |
| --- | --- |
| Module suite | 28 end-run assertions change (tests that expect run-101 or `RUN_LIMIT` now stop at run 5-13 with equal reports); 1 order-only assertion; 2 provisional changes, both in fixtures that inject a fault at run-11 |
| `RepeatedDemandRelayTest`, `RepeatedDemandHiddenRenameTest`, `LoopMarkOriginServiceTest` | same end and report as native |
| `DeepChainFixtureTest`, 78 variants | `FIXED_POINT` never holds before B is confirmed |
| Rule suite, 2 launches per arm | 583 identical; `PassthroughFileModelSamples` run-11 cutoff → `FIXED_POINT` 5; `UnsafeFileUploadServlet#doPost` → `FIXED_POINT` 11 (9 without canonical order); reports equal |

| OWASP, interleaved | End | Confirmed / provisional | Wall (s) | Driver (s) | Peak RSS (GiB) |
| --- | --- | --- | --- | --- | --- |
| native ×3 | `RUN_LIMIT` 11 | 2,633 / 0 | 205 / 205 / 202 | 136 / 136 / 134 | 9.22-9.29 |
| `FIXED_POINT` ×3 | `FIXED_POINT` 17 | 2,633 / 0, identical SARIF and code flows | 237 / 236 / 235 | 169 / 168 / 167 | 9.25-9.29 |

OWASP stops at run-17 in all 7 `FIXED_POINT` launches, with and without
canonical order. The stop costs +32 s wall: about 26 s for the six extra
runs, the rest for canonical order and the shadow bookkeeping. This
fails the old rule "wall time not worse". It is the price of a natural
stop over a cutoff. The OWASP work in §3A and §5A aims to remove it with
an empty demand.

Stirling-PDF and Conductor without W: no stop, as expected.

### 4.7 Proof scope

- The Lean model `ClosedRunPair.lean` covers the induction and the limit
  reads. Its hypothesis is a deterministic step. §4.3 gives that
  hypothesis in production.
- Model differences: the counter sites must cover every K read that can
  change a result. The attack reading found that from run-3 on all
  K-dependent decisions are counted (`ap/KTouch.kt` on the branch). Run-1
  and run-2 are never compared, because the test starts at `i ≥ 5`.
- The record comparison uses key equality. It ignores the order of the
  saved-record index. §4.3 makes that order canonical.

## 5. Step 2 — a finite domain where paths grow through a cycle

Step 1 does not stop Conductor or Stirling-PDF. Their state never
repeats. This section gives the traces and the next experiment. It
selects no rule.

### 5.1 Paths that grow by repetition

| Owner | Growing path | Cause |
| --- | --- | --- |
| Stirling-PDF `PipelineProcessor#runPipelineAgainstFiles` | `__repo__.Optional#Element.Optional#Element…`, `outputFiles.Element…` | One new record per pair of runs, no K read in the owner. The relative C5 cap as the cause is an inference. |
| Stirling-PDF `PdfAttachmentHandler#processInlineImages` | `[pattern, regex]` repeated, at the loop boundary | Global K. 64 boundary cuts per forward run from K=8 to K=30. Rows unchanged since H8. |
| Conductor `ScriptEvaluator#getObject` and four evaluators | entry path grows by one of `{Element, MapKey, MapValue}` | Each forward handoff. Rows ×3. |
| Recursion fixtures (`RecursiveWrapper`, `BranchingWriteRead`, `WordChunk`) | recursive wrapper paths | K |

`decodeMimeHeader` on Stirling-PDF also reads K after run-17. Its cut
count falls from 960 to 20 over runs 17-31, but it is still 30 in run-31
over both contexts.

A path that grows by one repeated segment through a cycle has no fixed
point under a growing K. The limit of `p`, `p.s`, `p.s.s`, … must be
represented by a fold such as `p.s.[any]`. This is a widening. It is a
precision decision, not a stop rule: a flow that needs the exact
repetition becomes a DEMAND (provisional) flow.

### 5.2 The fold ablation

Branch `proto/repeat-fold-20261119` folds every path at its first
repeated counted accessor:

- It removes the `getObject` growth (14 rows at every run).
- It loses 23 native natural stops, at least 4 confirmed module findings
  (20 other tests never reached their finding assertions), and 1
  confirmed Stirling-PDF finding (`UserController.java:130`).
- Conductor still times out in run-8. `replace` widens over distinct
  accessors, which a repeat fold cannot bound.

A fold at every repeated accessor is too wide. A fold selected by growth
across runs is also wrong: K grows by one per pair of runs
(`IterationPolicy.kt:48`), so each finite repeated path also grows by
one accessor per pair until it reaches its real depth (`x.f` → `x.f.f`;
`field3.field2` → `field3.field2.field3`). These are the ablation
losses.

### 5.3 W: fold at a program cycle (prototyped)

Branch `proto/cycle-fold-20261120`, flag
`-Dorg.opentaint.bidi.cycleFold=true`.

**Trace (Stirling-PDF).** The pipeline rotation is
`ret.PipelineResult#outputFiles.(Iterable#Element)^n` against `arg(0)`.
One more level comes with each pair of runs, through the outer `for`
loop (`PipelineProcessor.java:98-253`; `outputFiles = newOutputFiles` at
252). The `__repo__.Optional#Element^n` chain stops growing by run-11.
The `processInlineImages` chain is `(Matcher#pattern.Pattern#regex)^n`
at the repeat port of the `while (matcher.find())` loop.

**Rule.** Cut a path at the first accessor that the applied relation
adds and that already occurs above it on the same path. The cut part is
a DEMAND MAY tail, as at a global cut. The fold does not read K. A ZERO
premise is never folded. It applies only at two sites:

- a loop site: the child block is a loop and the exit is one of its
  repeat ports, so one full traversal re-enters the loop
  (`engine/MethodBlockRuntime.kt:476-478, 493-495, 558-565`);
- a recursion site: a callee summary is applied and caller and callee
  are in one cyclic call-graph component, computed once per run from the
  observed call edges (`engine/RunMethodCallServices.kt:633-672`).

Forward runs only. The variant that folds in both directions lost a
confirmed finding (`LoopBlockDeepNoLeaveTest`) and three natural stops,
because the backward fold cut demand that had to reach a source at
depth 4. It is withdrawn.

**Results.**

| Case | Native | With W |
| --- | --- | --- |
| Stirling-PDF, 2 launches | no fixed point to run-31 | the pipeline rotation stops at H19; loop-boundary cuts are 0 from run-9; `FIXED_POINT` holds from run-33 to run-41; SARIF identical (32 confirmed, the same 2 provisional, `UserController.java:130` confirmed) |
| Conductor, 1 launch | `getObject` 42 / 126 / 378 rows at H3 / H5 / H7 | `getObject` 18 / 12 / 12, stable from H5. Still times out in run-8: `replace` grows by new combinations, not by repetition. SARIF identical. |
| Module suite, 2 launches (342 analyses) | — | 0 report changes, 0 lost natural stops. Two recursion fixtures that native ends at `RUN_LIMIT` 101 reach `FIXED_POINT` at run-7 and run-9. `AcyclicTerminationBaselineTest` does not fold, so `x.f.f` stays exact. |
| Rule suite, 585 cases | — | identical ends and reports |

The only remaining blocker on Stirling-PDF is `decodeMimeHeader`. It
reads K in statement cuts inside a loop scope (`EmlProcessingUtils.java:515`).
The counts are equal with and without W (660, 450, … 30) and reach 0 at
run-33. They are finite, but deep. Their cause is not traced.

Precision change: a path whose repetition a loop traversal or a
recursive call adds becomes a DEMAND MAY tail. Measured report changes:
0. One component test (`LoopBlockExternalHeaderTest`) expects the exact
`x.f.f` from an inner growing loop and now gets `x.f` with a MAY tail.

Cost: about 46,300 loop-site checks per late forward run on
Stirling-PDF; 2.46 M loop-site and 155k recursion-site checks in
Conductor run-7; one Tarjan pass per run over 13,423 methods. Time is
not measured yet.

Gate still open: three interleaved launches per project for time and
memory; OWASP and ThingsBoard with W; determinism (§4.3). The two W
launches on Stirling-PDF differ by 28 forward rows with the same report.

### 5.4 Conductor: the cost of the `replace` widening

W removes the `getObject` growth, but Conductor's main volume is
elsewhere. `ParametersUtils#replace` and `replaceList` widen over
combinations of distinct accessors at depth 3-4: 74 % of the H7 rows are
new combinations, not deeper paths. One loop scope (block 2, port 40→40)
holds 26,235 of 28,835 rows of one context. Each of its top three exits
pairs with 3,780 entries. On an older runtime `replace` levelled off
from H9. At HEAD run-6 costs 499 s, and run-8 does not complete: it
times out natively, and with the fold and a 3,000 s budget it ran out of
memory after 1,862 s of work.

Trace result (branch `proto/conductor-volume-20261120`, native, cutoff
9):

- The cross product is three FLOW summaries in the `replace` loop
  scope. Their premises are `var3.Iterator#Element.Map$Entry#Value.{Map#MapValue,
  Iterable#Element, Map#MapKey}.[any-taint]`, and all three results
  project to the same entries. At H7 the scope has 33,006 rows; 12,300
  of them are 4,100 entries × 3 exits.
- The 4,100 entries are a full product {10} × {10} × {41}: 10 container
  accessors (`Iterator#Element`, `Map$Entry#Value`, `Map#MapValue`,
  `ImmutablePair#right`, …) at each level, and 31 data fields at the
  third. H5 had 400 entries at depth 2; H7 has 4,100 at depth 3, with no
  overlap. The depth grows by one per pair of runs, and `replace` makes
  no K read in run-7. So the inferred driver is the relative C5 cap. H9
  would hold about 41,000 entries.
- The growth adds a different container accessor at each level. It
  repeats no accessor, so W (§5.3) cannot fold it. Every finite
  combination is new, so `FIXED_POINT` cannot hold.
- No exact cover exists. 0-10 rows per barrier share a C2/C5 service
  key. A shallower `[any]` entry exists for 73 % of the backward H6 rows,
  but C2 cuts at the first field after the entry path, so the deeper
  entry admits different starts. A shallower exit is no C5 cover,
  because the C5 cap is relative to the exit depth.
- The rows do not drive the cost. In backward runs 6 and 8 the busy
  worker spends 71-99 % in saved-record replay of the `replace` loop,
  mostly the loop output restriction, and 26-41 % in C2 trie scans.
  C5 is 3.5-6.7 %. A factored row would be exact, but it saves at most
  the C5 share. Not built.
- A run-long memo of the loop observer's C2 answers was exact (all
  reports equal) but saved 7-15 % in run-4 only. It stored 23.9 M
  distinct answers in run-8, so the C2 work is real and not repeated.
  Withdrawn.
- Owner census: 96-98 % of Conductor's rows are in owners that change
  rows and records at every barrier. The three `ParametersUtils` owners
  hold 68-93 % of all rows. Backward run-6 makes 570,138 and 395,746 K
  cuts in them.

Correction and widening (branch `proto/cyclic-widening-20261121`, on S):

- The relative C5 cap is not the driver; the loop does not add the
  levels either. In each loop pass the analyzer puts a pathless DEMAND
  fact `var(3).[any]` on the iterator. Seven calls in the loop write it.
  The `ALIASES` call stage copies a callee's coarse reply, and the `put`
  write, onto every local that the alias analysis links to the argument.
  At the back edge C5 copies that pathless fact into every exit row of
  the previous backward run: in run-5, 400 of 401 publications of one
  premise come from it, and 46,594 of 58,157 over all `replace` loop
  scopes. Backward, C2 starts one counted accessor below each entry. So
  the demand gains one level per pair of runs.
- The 10-way branching comes from the models: `it.next()` dispatches to
  `Iterator#Element`, `StrTokenizer#inputContent`,
  `HeaderIterator#headers` and `HeaderElementIterator#headerElements`;
  `e.getValue()` to `entryData`, `Value` and two `Pair#right` fields,
  each also with an identity copy. Inferred root cause: models that
  return the receiver itself (`this → result`) pollute the alias set, so
  the iterator seems to alias `result`, which never happens in Java. This
  alias-set precision is a separate item.
- Widening A (`-Dorg.opentaint.bidi.cyclicWidening=fwd`): in a loop block
  at its back-edge exit, or at the method level of a recursive method,
  C5 restricts a MAY fact only to the first counted accessor below the
  MAY node: `var(3).[any]` with exit `var(3).a.b.c` gives
  `var(3).a.[any]`. It refines less than the demand requests. It has no
  numeric parameter and reads neither K nor the report state. What it can
  lose: a finding that needs a deep exact start below a MAY node in a
  cyclic scope where that node does not move with K. None was observed.

| Conductor | S | S + A (2 launches) |
| --- | --- | --- |
| `replace` loop rows | 33,006 at H7, growing | 5,215-5,408 from H9; 194-195 entries |
| Run-6 / run-7 | 349 s / 162 s | 186-191 s / 26-29 s |
| Run-8 | does not finish | 397-401 s |
| Binding K reads | still at run-7 | 0 in every run from 16 to 21 |
| End | timeout in run-8 | no `FIXED_POINT` by run-21 (budget 5,400 s) |
| Findings | 7 / 0 | identical SARIF and code flows |

- Still open on Conductor: from run-17 only the handoff and record
  conditions of `FIXED_POINT` fail. Backward rows of `replaceList` grow
  (+3,300 at H18, +2,929 at H20) and record keys rotate. Backward runs
  cost 600-772 s each, so Conductor cannot end inside the 1,080 s
  production budget even if it converged. Next: trace `replaceList` in
  runs 18-20, measure the backward mode of A, profile one late backward
  run, and the alias-set precision.
- Gate of A: module suites identical (A never fires); rule suite
  identical; OWASP identical (A never fires; handoff digests equal);
  Stirling-PDF identical (A fires 51-189 times per forward run and
  changes only H3-H5).

Conclusion: Conductor's divergence is cyclic growth by combinations of
container accessors, driven by the demand chain itself. `replace` is in
a loop and a recursion, so it is outside requirement AC. No exact
reduction exists. A natural fixed point here needs a widening of the
demand in cyclic scopes that does not wait for a repeated accessor.
That is a precision decision, and it is the open design problem of the
next step. The §8 loop replay skip (§5A) is the first enabler to
re-gate, because saved-record replay of this loop dominates the
backward runs.

### 5.5 Undecided reports on Stirling-PDF

Two stored-XSS candidates (`UserController.java:753` and `:768`) stay
reached and unconfirmed from run-5 to run-31. They are reached only
under a demand premise on the Spring repository model (`__repo__`). The
legacy engine reports neither. They do not block `FIXED_POINT`. When
Stirling-PDF repeats, `FIXED_POINT` publishes them as provisional, as
the cutoff does today.

### 5.6 Order of work

0. Requirement AC (§3A): the acyclic census, then one fix per source
   that keeps demand in acyclic owners, each gated alone.
   - MUST-cover reply rule for acyclic callees: done; the five
     `doSomething` families drain.
   - G6, the primitive-tracking mark policy, made monotone in K. It is a
     prerequisite of DemandTarget subsumption, and it removes the K
     dependence behind the native recall loss (§1.3). Decision (20
     November): the drop form. At a boxed level, a non-primitive-tracking
     mark is dropped on the whole value, also on the leaves below it such
     as `value`. A boxed value carries only primitive-tracking marks.
     True primitive levels and primitive-tracking marks keep today's
     behaviour. (Running with the X gate: `proto/g6-drop-xsub-20261120`.)
   - DemandTarget subsumption X: gated with the G6 drop form; 0 report
     changes; drains every loop-free OWASP root.
   - Integration of every mechanism that passed its own gate: canonical
     order, `FIXED_POINT`, W, the MUST-cover reply rule, X and the G6
     drop form. (Running: `proto/termination-integration-20261120`.)
   - DemandTarget renewal in loop blocks (66-70 OWASP roots): cyclic,
     outside AC, needs its own mechanism (XE withdrawn).
   - Complete backward-ZERO and ND rows: done, not a driver (branch
     `proto/persist-complete-20261120`).
     - They are not persisted on purpose. A backward ZERO summary is a
       seed path, not a flow, and an ND summary is a conjunction, so
       neither can be reversed into an exact record (ap.md §8.7,
       ap.md:3037-3054; F70 made every non-record edge into demand).
     - OWASP and Conductor have no forward ND rows. Stirling-PDF has 5,
       and DEMAND rows of the same owners hand off the same 5 rows.
     - Not handing off served complete rows from H7 keeps the project
       reports equal. It loses confirmed findings in the module suite
       (attack fixtures M1, M3): when K grows, the same row content is
       not the same input, and the row was the only way a now-exact fact
       entered the callee.
     - Persisting ND summaries forward and replaying them through the
       conjunction join is exact on every measured case. It has no
       effect on the forward residual, so it is not selected.
     - Conclusion: the complete rows ride along with the DemandTarget
       cycle. When the DemandTarget stops, they stop being derived.
   - Cleaner survivor on the DEMAND layer (`ap/Clean.kt:194-218`): the
     maker of the DemandTarget renewal at 151 of 164 OWASP roots. Not
     started. R36 of the rule spec addressed a related residual.
   - Census: done; it is the measuring tool for each item above.
1. §4.3: canonical tie-break. Done: barriers are deterministic across
   launches. Open: the engine sources S9-S11 that make a run not
   confluent.
2. Gate `FIXED_POINT` alone. Done: no report change; OWASP +32 s wall.
3. Full-OWASP drain diagnostic (§5A). It decides whether R41-class
   retirement can empty OWASP's demand. (Running:
   `proto/owasp-drain-20261120`.)
4. W (§5.3): done as a prototype. Stirling-PDF reaches `FIXED_POINT`
   at run-33 with an identical report. Next: the time and memory gate,
   OWASP with W, and a trace of the `decodeMimeHeader` cuts that delay
   the fixed point to run-33.
5. Conductor `replace` (§5.4): traced. No exact reduction exists. Next:
   a design for widening demand in cyclic scopes, and the loop replay
   skip as a run-cost enabler.
6. Depending on 3: R38 in shadow mode on OWASP H7–H17 and the rule
   suite, extended to loop scopes.
7. Re-gate the §8 enablers (§5A) and check R27 on Stirling-PDF.

## 5A. The rule spec under the new goals

The postmortem judged R01–R42 only by one question: does the rule give
an empty demand? The goals are now different: a proven fixed point,
less open demand without a report change, and cheaper runs. A rule
that does none of these stays out.

| Rule | Target | Reads the report state? | Measured | Verdict |
| --- | --- | --- | --- | --- |
| R01–R03, R05, R20–R23 (NE) | Global K cut, inside read | No | Global-cut fixture 6 → 302 pairs; 668,506 NE memberships on Conductor | Out. More keys; the K read stays. |
| R04, R06–R08, R32 | DEMAND start layer, inside read, run-2 static carry | No | R06: two run-5 stops became run-101. R32: Conductor run-2 41 → 219 s, then out of memory | Out. They create growth. |
| R09–R12, R34 | Inside read | No | R10: helper rows grow 6 → 127 (H3 → H49) | Out. R34 is a separate recall item. |
| R13 | Invalid nested-write keep | No (removes an unsound result) | Fixture run-101 → run-3; a false provisional entry goes | Keep as a precision fix. It matters more now that `FIXED_POINT` publishes `L∖C`. |
| R14–R16, R18, R19, R24, R25, R28–R30, R33 | Native behaviour | — | — | They name the producers of the open demand (R18 is the relative-cap regeneration). They reduce nothing. |
| R26/R35, R36, R31 | Cleaner survivors | No | 0 activations on all four projects | Out. They add K reads (`headLength + 1 ≤ limit`), which delay `FIXED_POINT`. |
| R27 | Work order inside a run | No | 0 of 92 cases changed; never on a project | Check on Stirling-PDF: does a fixed order remove the bimodal run-9? |
| R37/R38 | DemandTarget renewal at a root (Target→Zero) | R37 alone: yes (report ID). R38: no. It retires an origin only when every origin of the row has a committed NORMAL track or a NoRoute proof, enumerated beyond the cut. | Prototyped only with one root and copy-only methods: zero effect. Never measured on the control rows. | Candidate for less open demand. The only rule aimed at the dominant class. Acyclic only. |
| R39/R40 | DemandTarget renewal in loops and recursion | No (static NoRoute proof) | Model only | Narrow: it discharges only origins with no route. Its grammar extraction is the base for W (§5.3). |
| R41 | Relative-cap and inside-read FLOW copy rows | No: it needs a retained NORMAL provider and proved delivery at the removed service point | Geometry form: OWASP H11 1,111 → 1,002 (inside the native spread). The sound form made 0 attempts on four projects. Identity-based removal loses `RepeatedDemandRelayTest`. | Depends on the drain diagnostic below. Directly at most 121 of 1,153 OWASP rows. |
| R42 | Uniform cut descendant | No | Frontier 6 → 3; the Target stays | Out. The cut and its K read stay. |
| §7.1 observer census | Stop | Yes | — | Rejected (§7). |
| §7.1 closed run pair | Stop | Its clause "every reached identity has a receipt" reads the report state | Bounds excluded every project | Its ancestor role is kept in `FIXED_POINT`: reuse the generation counters, the ordered seal comparison and the K-read audit list. Drop the receipt clause and the bounds. |

Which rows repeat on OWASP: at H11, 1,032 of 1,153 forward rows are
control rows (Target→Data 594, Target→Zero 438); backward H10 adds
Data→Zero 1,271 and Zero→Zero 438. A sink cube with any DEMAND edge
emits a DemandTarget even when its report is confirmed
(`engine/RunMethodLocalServices.kt:371-405`). No rule targets the
backward ZERO rows. On the compiled OWASP entry the control rows drain
when the 6 FLOW rows are dropped at H7. On the full project they do not
(branch `proto/owasp-drain-20261120`, one launch per arm, cutoff 41):

| Arm, from H7 | Forward rows at H41 | Control rows | End | Report |
| --- | --- | --- | --- | --- |
| native (matched state) | 1,111 | 1,008 | `RUN_LIMIT` 41 | 2,633 / 0 |
| FLOW rows dropped | 990 | 935 | `RUN_LIMIT` 41 | identical |
| all DATA rows dropped | 919 | 919 | `RUN_LIMIT` 41 | identical |

- After H7 no DATA row comes back, and 919 forward control rows stay
  for ever, in 431 root `doGet`/`doPost` methods. The DATA rows keep
  alive only the control rows of 7 roots (the `doSomething` families)
  and 66 Target→Data rows.
- Every one of the 431 roots renews only sinks that are already
  confirmed. Each root runs a closed two-run cycle with no DATA row:
  forward, the root's Zero→Zero and Data→Zero rows let `acceptsTarget`
  (`store/DemandStore.kt:219-223`) accept a DEMAND hit at the confirmed
  sink, which emits a DemandTarget and captures the sink seed again
  (`engine/RunMethodLocalServices.kt:385-399`); backward, that seed
  reaches the source and rebuilds the zero rows. The mechanism is read
  from the code and the row counts. It is not yet ablated.
- The native handoff has three different steady states between launches
  (1,153, 1,111 and 1,017 forward rows at H7). This is the
  nondeterminism of §4.3.

So R41-class retirement cannot empty OWASP's demand. The dominant
source is DemandTarget renewal at a sink that already has a complete
witness. This is the "DemandTarget renewal" row of requirement AC. The
exact local form to test: a DEMAND hit does not emit a DemandTarget or
capture a seed when the same owner already has a complete ZERO →
NormalTarget for the same sink. ZERO is the weakest premise, so the
complete target covers every premise of the DemandTarget. This reads a
complete summary of the owner, not the report state. A dedicated track
tests it (branch `proto/dt-subsumption-20261120`).

§8 work items worth a new gate, as enablers for the extra runs:

1. Joined saved-record index seal: index rebuilds 202 → 101; Conductor
   handoff at run-6 2.663 → 1.368 s. It is also the place to fix the
   record order (§4.3).
2. Loop saved-DATA replay skip: Stirling-PDF run-9 167.6 → 142.0 s at
   equal work; 9.67 M replays skipped.
3. C5 index bypass and singleton compaction skip: 216,598 insertions
   bypassed on Conductor. Its tie-break must follow §4.3.
4. C5 equal entry/exit test reuse: the work-side form of a factored row
   (§5.4). Not measured on a project.

The §8.2 work allowances, the prefix cut cache, trie scratch and
whole-protection replay stay out. The §8.4 pass rule ("equal or better
end-to-end time") must change: a natural stop can cost more than the
cutoff (OWASP +25-28 s driver).

## 6. Plan to delete the run cutoff

1. Make requirement AC hold (§3A) on every reference project and suite.
2. Land the canonical tie-break and `FIXED_POINT`, with the cutoff kept
   as the existing guard. OWASP and the two rule tests then end
   naturally, after run-11.
3. Do Step 2.
4. Delete `HardRunLimitPolicy` and `RUN_LIMIT` when every reference
   project and every suite ends with `NO_DEMAND_EDGE` or `FIXED_POINT`.

ThingsBoard fails in run-1 for memory. No stop test applies to it. Its
memory fix is a separate item.

The wall-clock timeout and the memory guard stay. They are resource
budgets of the caller. An analysis that ends by timeout is `ABNORMAL`
and publishes the last confirmed set, without provisional entries.
Publishing provisional entries at a timeout would make the wall clock a
cutoff with output.

## 7. Rejected after test

| Idea | Why rejected |
| --- | --- |
| `QUIESCENT` (revision 2), a fixed run constant | Reads the report state. `RepeatedDemandRelayTest` loses its run-9 finding. A replay of fixture D1 (depth 8) predicts a stop at run-5 with B confirmed only at run-9. |
| `DECIDED` (`L_i ⊆ C_i`) | Reads the report state. Native breaks: a deep chain into a boxed value (D5, D6, M4), §1.3. |
| G6 mark-policy changes (guard, keep, drop) | Repairs for `DECIDED` only |
| `DECIDED` at two consecutive forward barriers | A window constant on a guess |
| Observer census | Reads the report state; 115 of 117 OWASP helper observers stay unconfirmed |
| Report-stability stop (no new report or record in a triple) | Reads the report state; Conductor still adds records at H7 |
| Fixed point without the K condition | False stops in `RepeatedDemandRelayTest` and `RepeatedDemandHiddenRenameTest` |
| Fixed point on row counts | Stirling-PDF counts are constant from H17 while keys rotate and records grow |
| Fold at every repeated accessor | 23 lost natural stops, at least 5 lost confirmed findings, no Conductor stop |
| Widening selected by growth across runs | Each finite repeated path also grows while K grows (§5.2) |
| Factored handoff rows for Conductor | Exact, but the rows are not the cost: C5 is 3.5-6.7 % of the busy worker |
| Run-long memo of loop C2 answers | Exact, but only run-4 gains 7-15 %; the C2 work is on distinct questions |
| Do not hand off a complete row already served | Loses confirmed findings (M1, M3): with a larger K the same row content is a different input |
| Persist backward ZERO rows as forward admission rules | Loses M3: the backward run no longer reopens the sink's seed path; a fix would need persisted seeds too (a repair of a repair) |
| DemandTarget subsumption without the G6 fix | 17 module analyses lose finding B (D5, D6, M4) |
| DemandTarget subsumption at a loop block from the root's target (XE) | Loses B in deep-chain D4: the suppressed seed of A was the one that found B's source |
| Offer closure: no start for a DEMAND offer that the callee's saved record covers | Loses `delayed U sink`: the callee row is the admission key for later refined offers |
| Drop a C5 cut when another row keeps the full relation at NORMAL | Defeats itself: the backward covered cuts are what create the forward deep rows |
| MUST-cover reply rule without the acyclic scope | Conductor H7 rows doubled (186,430 against 84,378-85,519) |
| W in both directions (W1) | The backward fold cut demand that had to reach a source at a finite depth: 1 lost confirmed finding, 3 lost natural stops |
| Influence-cone fixed point | The Stirling-PDF pipeline is inside the cone of the undecided reports |
| Demand removal by key identity or report ID (R37 alone, identity-based R41, R42) | Identical-demand removal loses findings (32b037292); R42 leaves the Target. R38 and the sound R41 stay candidates (§5A). |
| Closed run pair with scope bounds | The bounds excluded every project |
| Provisional output at a timeout | Makes the wall clock a cutoff with output |
| Per-run time budget | A limit. It decides nothing. |

## 8. Withdrawal

- Withdraw `FIXED_POINT` on the first native case where a run after the
  stop changes the state or the report.
- A diagnostic mode continues after a `FIXED_POINT` stop to the native
  end and checks this. `RepeatedDemandRelayTest`,
  `RepeatedDemandHiddenRenameTest` and `DeepChainFixtureTest` (78
  variants) are the regression tests.
- Withdraw W on the first lost confirmed finding in its gate.

## 9. Evidence

All branches are local, not pushed. Data directories are under
`/drive-testcomp/opentaint-go-rules/termination-next-20261119/`.

| Item | Branch and report | Data |
| --- | --- | --- |
| Shadow fixed-point logging | `proto/fixed-point-shadow-20261119`, `docs/reports/fixed-point-shadow-20261119.md` | `fp-shadow/` |
| Fold ablation | `proto/repeat-fold-20261119`, `docs/reports/repeat-fold-ablation-20261119.md` | `repeat-fold/` |
| Combined gate (`DECIDED_FP`) | `proto/decided-stop-20261119`, `docs/reports/decided-stop-gate-20261119.md` | `decided-stop/` |
| Adversarial fixtures, fuzzer, hash-order shift | `proto/decided-stop-attack-20261119`, `docs/reports/decided-stop-attack-20261119.md` | in the branch |
| G6 variants (withdrawn) | `proto/decided-g6-20261119`, `docs/reports/decided-g6-20261119.md` | `decided-g6/` |
| Deep-field-chain fixtures | `proto/deep-chain-fixture-20261120`, `docs/reports/deep-chain-fixture-20261120.md` | in the branch |
| Stirling-PDF trace | this proposal, §5 | `scripts/` |
| Cycle-attached fold W, Stirling-PDF row trace, owner census | `proto/cycle-fold-20261120`, `docs/reports/cycle-fold-20261120.md` | `cycle-fold/` |
| Stirling-PDF makers, rule RX, `C5B` | `proto/stirling-ac-20261121`, `docs/reports/stirling-ac-20261121.md` | `stirling-ac/` |
| Inside-read rule, no-cap isolation | `proto/inside-read-20261121`, `docs/reports/inside-read-20261121.md` | `inside-read/` |
| Conductor cyclic widening A, `replace` growth trace | `proto/cyclic-widening-20261121`, `docs/reports/cyclic-widening-20261121.md` | `cyclic-widening/` |
| Loop-block DemandTarget cover LG, D4 trace, loop fixtures L1-L6 | `proto/loop-dt-20261121`, `docs/reports/loop-dt-20261121.md` | `loop-dt/` |
| Configuration S: MUST ignores an EXACT cleaner; exact-start volume | `proto/must-cleaner-20261121`, `docs/reports/must-cleaner-20261121.md` | `must-cleaner/` |
| AC closure fixes | `proto/ac-closure-20261121`, `docs/reports/ac-closure-20261121.md` | `ac-closure/` |
| Integration NT and its gate | `proto/termination-integration-20261120`, `docs/reports/termination-integration-20261120.md` | `integration/` |
| G6 drop form, X + drop gate | `proto/g6-drop-xsub-20261120`, `docs/reports/g6-drop-xsub-20261120.md` | `g6-drop/` |
| Complete backward-ZERO and ND rows | `proto/persist-complete-20261120`, `docs/reports/persist-complete-20261120.md` | `persist-complete/` |
| DemandTarget subsumption X, control-row ablation | `proto/dt-subsumption-20261120`, `docs/reports/dt-subsumption-20261120.md` | `dt-subsumption/` |
| Acyclic-owner census | `proto/acyclic-census-20261120`, `docs/reports/acyclic-census-20261120.md` | `acyclic-census/` |
| `doSomething` root cause, MUST-cover reply rule | `proto/dosomething-fix-20261120`, `docs/reports/dosomething-fix-20261120.md` | `dosomething/` |
| Full-OWASP drain diagnostic | `proto/owasp-drain-20261120`, `docs/reports/owasp-drain-20261120.md` | `owasp-drain/` |
| Canonical order, `FIXED_POINT` gate | `proto/deterministic-handoff-20261120`, `docs/reports/deterministic-handoff-20261120.md` | `det-handoff/` |
| Conductor `replace` trace, census, C2 memo (withdrawn) | `proto/conductor-volume-20261120`, `docs/reports/conductor-volume-20261120.md` | `conductor-volume/` |

## 10. Checklist (design guide)

```text
[x] Failure class and real trace: §2, §5 (OWASP, Conductor, Stirling-PDF, two rule tests)
[x] Ablation on the real case: shadow decisions; fold ablation (§5.2)
[~] Native prototype result, 3 launches: shadow on OWASP ×2; combined arm only; FIXED_POINT alone not gated
[x] Execution site and measured volume of each new operation: §4.5
[x] Selected semantic scope: §4.4
[x] Proof scope and each model difference: §4.7 (determinism open, §4.3)
[x] Withdrawal condition: §8
[x] Adversarial review of the draft and native counterexamples: §1.3, §4.2
```

## 11. Blind spots

- Determinism is open (§4.3). Until it is fixed, the proof holds for the
  model only. The shadow evidence holds for the measured launches.
- The counter sites were checked by reading the code, not by a proof.
- ThingsBoard was not run.
- Stirling-PDF and Conductor shadow runs are single launches, and they
  overlapped another analysis.
- Hash keys: owners hashed by printed name, seeds by a 32-bit hash.
  Collisions were not checked.
- Stirling-PDF launches stalled in a loop block of `decodeMimeHeader`
  (run-9 or run-11, no new events for 20 minutes), in native shadow mode
  as well. This is the known bimodal run-9. It is a work defect of its
  own.
- Step 1 makes OWASP slower than the cutoff (+25-28 s driver). It is a
  natural stop, not a speed gain.
- The cause of the pipeline rotation on Stirling-PDF is inferred, not
  traced to rows.
- The Conductor `replace` cost has no candidate yet, only a trace plan.
- A separate recall defect: a chain grown in a loop
  (`loop { c2.f = c; c = c2 }`, depth ≥ 3) is never confirmed natively,
  even with demand kept alive to run-13. The cause is not known. It is
  outside this proposal.
- Whether real rules put a mark on `Integer.value` (the D5 shape) was
  not measured.
