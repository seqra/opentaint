# OWASP non-termination and Stirling-PDF fast/slow split: root causes and two rules

Status: PROPOSAL, 27 November 2026. Two rules: **M1** (OWASP) and **H1**
(Stirling-PDF). Both are native prototypes behind a flag on proto
branches. Verdict (§11): **H1 is WI**. **M1 is not WI**: it stops the
OWASP cycle, but it fails the gate on Conductor (§6.4 to §6.6).
Design rules: [design-guide.md](../../spec/design-guide.md),
[proof-guide.md](../../spec/proof-guide.md).

Data paths are relative to the campaign directory
`/drive-testcomp/opentaint-go-rules/cycle-stall-20261126/`. Code paths
are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.

Labels: **VERIFIED** means measured in a launch or read in the code.
**INFERENCE** means a conclusion from VERIFIED facts that no launch
tested directly.

## 0. Summary

| # | Problem | Root cause (one line) | Rule | Gate | WI |
| --- | --- | --- | --- | --- | --- |
| A | OWASP reaches the hard run limit (run 11, or run 21 with a higher limit). The reports are final at run 3. | C2 cuts a MUST actual that fits the relative cap to a STAR start. A STAR start with a concrete mark is DEMAND. Its DEMAND witness at the sink makes the same DEMAND rows in each backward run: an exact period-2 cycle from hand-off 7. | **M1**: in a forward restricted run, a NORMAL MUST actual that fits the cap below a concrete ANY entry starts as itself (NORMAL must-premise). | OWASP: NO_DEMAND_EDGE in run 7, results equal, every route served. **Conductor: fails** (H4 +125%, OOM in run 6). | **Not WI** |
| A' | M1 on Conductor | The CURRENT cut also keeps MUST facts out of blocks and callees. M1 lets them in, and CURRENT's FLOW MUST start rows turn them into a loop-carried FLOW relation over the iterator aliases of `ParametersUtils#replace`; the backward run crosses it two fields deep (§6.5). | - | Ablation A5 (§6.6): with the FLOW MUST rows replaced, M1 adds +1.6% H4 rows; but the replacement costs +49% alone. | - |
| B | Stirling-PDF has fast launches (run 7 in 2-3 s) and slow launches (run 7 in 18-123 s, run 9 can time out). | The root summary store keeps an exact demand row next to a MAY row that covers it, if the exact value arrives first in run 6. The hand-off projects both rows. The exact row gives an EXACT NORMAL start that a loop wraps up to the field limit. | **H1**: the hand-off normalizes each TAINT lane of a store with the removal half of the store's own TaintGroup law. | Results equal on all projects, Stirling-PDF route census equal, suites pass; fewer rows on Stirling-PDF and Conductor, and 13 fewer at OWASP H4; the fast form in every H1 launch. | **WI** |

Both rules remove work where they act. Neither rule relaxes a cap,
stops on reports, cuts work by a number or switches a rule off in a
scope. The open decisions for the user are in §14.

## 1. Notation

- **Run N.** Odd runs are forward. Even runs are backward. Field limit
  schedule `REPEAT_RUN1`: run N has the field limit K = N-1 (N ≥ 2).
- **HN.** The hand-off rows that run N gives to run N+1 (the
  `BIDI_HANDOFF_DIGEST run=N rows=...` line).
- **Fact text.** `base.path.TAIL/MARK,LAYER`. `N` is NORMAL, `D` is
  DEMAND, `P` is protected (`nonSubsumable`). Tails: `*` STAR, `$`
  EXACT, `MAY` ANY (some location below carries the mark), `MUST`
  ANY_TAINT (every location below carries the mark, except below the
  first accessors in the exclusion `E`). `FLOW` is the abstract mark.
- **Accessors.** `SB` = `String#<string-bytes>`, `BY` = `String#bytes`,
  `CT` = `CharSequence#content`, `[]` = array element.
- **T.** A concrete rule mark, for example `sqli.yaml:sql-injection#source`.
- **C2.** The start policy of a restricted run
  (`ap/RestrictedInitialPolicy.kt`): for a demand entry `Dc` and an
  actual fact at a call or block entry, it gives the initial facts
  (starts) of the callee or block. **Relative cap**: a start has at most
  `min(K, FL(Dc)+1)` counted fields, where `FL` counts fields.
- **C5.** The publication cut at a block or method exit.
- **DT / NT.** `DemandTarget` / `NormalTarget`: a target row that a
  backward run makes for a DEMAND / NORMAL witness at a sink.
- **Fits the cap.** The actual is below the entry `Dc`, and its first
  counted accessor below `Dc` is its last accessor
  (`firstFieldEnd(...) == q.size`).
- **Lane.** The TAINT rows of one store and one premise with the same
  base, layer and protection class.
- **CURRENT / NEW.** Every rule row has one of these labels. CURRENT is
  the code at `eb36f401d` (branch `saloed/bidirectional`). NEW is the
  proposed rule.

## Part A. OWASP

## 2. Root cause of the OWASP non-termination

This section gives the real trace, the cycle step by step, and the
evidence that the cycle does not depend on K.

### 2.1 Real trace and counts

Launch `owasp/full-a` (native, run limit 21), VERIFIED:

| Run | Direction | HN rows | Methods with demand rows | Test classes | Engine time |
| ---: | --- | ---: | ---: | ---: | ---: |
| 2 | backward | 19,292 | 4,296 | 1,914 | 26.1 s |
| 3 | forward | 303 | 163 | 76 | 9.6 s |
| 4 | backward | 579 | 163 | 76 | 1.2 s |
| 5 | forward | 108 | 27 | 11 | 1.1 s |
| 6 | backward | 242 | 27 | 11 | 0.21 s |
| 7 | forward | 157 | 21 | 8 | 0.32 s |
| 8 | backward | 254 | 21 | 8 | 0.23 s |
| 9, 11, ..., 21 | forward | 157 (same digest as H7) | 21 | 8 | ≤ 0.33 s |
| 10, 12, ..., 20 | backward | 254 (same digest as H8) | 21 | 8 | ≤ 0.23 s |

- The reports are final at run 3: 2,633 confirmed, 0 provisional, the
  same at runs 3, 11 and 21. VERIFIED.
- From H7 the hand-off is an exact period-2 repeat: H7 = H9 = ... = H21
  and H8 = H10 = ... = H20 (same row count and digest). VERIFIED.
- The 21 methods: `doPost`, the helper `doSomething` and (for 4 of
  them) `doGet` of BenchmarkTest00996, 01000, 01009, 01117, 01446, 01474,
  01985 and 01988. VERIFIED (frontier lines, runs 9 and 10).
- Other launches have a different native H5 (108 in `full-a`, 79 in
  `routes-native`; different diagnostic builds). Each native launch
  reaches the exact period-2 repeat. VERIFIED.

### 2.2 The program shape

BenchmarkTest01009 (`OWASP/src/main/java/.../BenchmarkTest01009.java`):

```java
for (Cookie theCookie : theCookies) {                 // loop block
    if (theCookie.getName().equals("BenchmarkTest01009")) {
        param = URLDecoder.decode(theCookie.getValue(), "UTF-8"); // source
        break;
    }
}
String bar = new Test().doSomething(request, param);   // post-loop block B3
String sql = "SELECT ... PASSWORD='" + bar + "'";
JDBCtemplate.queryForRowSet(sql);                     // sink
...
String doSomething(HttpServletRequest request, String param) {
    return new String(Base64.decodeBase64(Base64.encodeBase64(param.getBytes())));
}
```

`param` is `var(27)` in `doPost`. The sink literal reads the String
content of its argument.

### 2.3 The cycle, step by step

Forward part (VERIFIED by the owner trace `owasp/full-trace-native`
and `owasp/v3-routes`, run 5, `BenchmarkTest01009#doPost`, block B3,
entry port 88):

1. The source makes the NORMAL fact `var(27).MUST/T` before the loop.
2. C5 at the loop exit intersects `var(27).MUST/T` with the String
   content shapes of the sink literal. The result is a set of NORMAL MUST
   actuals one counted field below `var(27)`: `var(27).SB.MUST/T`,
   `var(27).BY.MUST/T`, `var(27).CT.MUST/T`, `var(27).[].MUST/T` and
   `Enumeration#elements.MUST` in other tests.
3. The demand entry of B3 is `var(27).MAY/T` (the DT of §2.3 step 7). Each
   actual of step 2 is one counted field below it, so it fits the
   relative cap `FL(Dc)+1`.
4. CURRENT C2 for the actual `var(27).CT.MUST/T,N`:

   ```
   initials=[var(27).CT.*/T,D ; var(27).CT.*/FLOW,N ; var(27).$/FLOW,N ; var(27).CT.$/T,N]
   ```

   The MUST tail becomes STAR. A STAR start with a concrete mark is
   DEMAND by itself (ap.md §6.5, Lean `startFact`). The cut is not a cap
   cut: the actual already fits the cap. It is the tail abstraction of
   the `ANY` branch of `RestrictedInitialPolicy.emit`, which keeps EXACT
   for an EXACT actual but not MUST for a MUST actual.
5. The DEMAND start `var(27).CT.*/T,D` flows through `doSomething` and
   the concatenation to the sink. The sink sees a DEMAND fact, so the run
   records a DEMAND witness.

Backward part (VERIFIED by the owner trace, runs 6 and 8):

6. The DEMAND witness gives a DT at the sink. The backward run carries
   it to B3 as `TARGET => var(27).MAY/T` and hands off the DEMAND row
   `ZERO -> {var(27).MAY/T}` and the helper rows (for example
   `$Test#doSomething arg(1).SB.*/FLOW -> {ret.MAY/FLOW},D`, the inside
   read of the FLOW companion of step 4).
7. The next forward run meets the same entry `var(27).MAY/T` and the
   same actuals. Step 4 gives the same DEMAND start again.

Why NORMAL work does not close the cycle:

8. The EXACT companion `var(27).CT.$/T,N` and other NORMAL starts reach
   the sink. They give NORMAL witnesses and the confirmed findings (run
   3). But layers never subsume each other: a NORMAL witness does not
   remove a DEMAND row. So the DEMAND rows of step 6 stay.

### 2.4 Why the cycle does not depend on K

- The start of step 4 is fixed by the tail rule, not by K: the actual
  fits the relative cap in every run, so a larger K gives the same
  start. VERIFIED: H7 to H21 are identical while K grows from 6 to 20.
- A K-dependent chain rides on the cycle: in native runs 7 to 21, exact
  NORMAL leaves below `arg(0)` of the sinks grow with K
  (`arg(0).CT.SB.SB.[].$` and similar, 26 leaves). They do not change
  the hand-off rows. VERIFIED (§3.4).
- The driver cannot stop on an exact repeat: K changes the run state in
  each run, so no state repeats although the hand-off repeats.
  VERIFIED (records change until run 9; NT rows until run 7).

### 2.5 Controls

- **EXACT actual converges.** The single-entry launch of 01474
  (`owasp/single-01474-a`) has EXACT actuals at depth 1 at the same
  block. CURRENT C2 keeps EXACT for them: an EXACT NORMAL start. The
  launch ends with NO_DEMAND_EDGE at run 5. In the full launch the same
  block has MUST actuals, and it cycles. VERIFIED.
- **One entry point is enough.** The single-entry launch of 01000
  (`owasp/single-01000-a`, native) reaches the run limit (run 21) in
  3.2 s. The same entry with M1 (`owasp/single-01000-mp`) ends with
  NO_DEMAND_EDGE at run 5. VERIFIED. This is the smallest real reduction
  of the failure.
- **A MUST start with a FLOW companion does not converge (v2).** The
  probe v2 started only concrete-mark MUST actuals as themselves and kept
  a FLOW STAR companion. OWASP still reached the run limit (run 21,
  70 firings per forward run). The FLOW STAR companion gives the helper
  inside-read DEMAND rows of step 6. VERIFIED (`owasp/v2-trace`,
  `owasp/routes-mp`).

### 2.6 Ablation

Bypass of the cut (probe v1, `owasp/full-mp`): a MUST actual that fits
the cap starts as itself; no STAR start, no FLOW STAR companion. OWASP
ends with NO_DEMAND_EDGE at run 7: H5 = 18, H6 = 31, H7 = 0 rows.
2,633 confirmed, 0 provisional, SARIF identical. VERIFIED. One
mechanism in, the cycle; the same mechanism out, convergence.

## 3. Rule M1: a MUST actual that fits the cap starts as itself

### 3.1 Statement

| Row | Run | Entry `Dc` | Actual | CURRENT start | NEW start |
| --- | --- | --- | --- | --- | --- |
| M1.1 | forward restricted | ANY tail with a concrete mark, actual strictly below `Dc` | NORMAL MUST (ANY_TAINT), fits the cap | STAR start at the actual's path (DEMAND for a concrete mark) + FLOW STAR companion | the actual itself: `x.p.MUST/E/T`, NORMAL must-premise; no STAR start, no FLOW STAR companion |
| M1.2 | forward restricted | as M1.1 | as M1.1, but `result(...)` gives null | as M1.1 | CURRENT (fallback; dead code, §9 R8) |
| M1.2a | forward restricted | ANY tail with an abstract mark `*` | MUST, fits the cap | FLOW STAR start | CURRENT (unchanged; v4 guard, §9 R6) |
| M1.2b | forward restricted | as M1.1 | a DEMAND MUST actual, fits the cap | STAR start (DEMAND) | CURRENT (unchanged; v5 guard: a DEMAND actual gets a DEMAND start in both forms, so M1 would only split its key by `E`) |
| M1.3 | forward restricted | as M1.1 | MUST, does not fit the cap (a counted field after the first one) | STAR start at the cut | CURRENT (unchanged) |
| M1.4 | forward restricted | as M1.1 | EXACT, or MAY, or STAR | EXACT start (EXACT, fits) or STAR start | CURRENT (unchanged) |
| M1.5 | backward | any | any | CURRENT | CURRENT (unchanged: `legalInitial` rejects ANY_TAINT in a backward run) |
| M1.6 | forward restricted | any | any | other companion starts (EXACT companion, root FLOW EXACT) | CURRENT (unchanged) |

`canEmitInitial` follows `emit`: it accepts the M1.1 start.

The NEW start is an existing start form. ap.md §6.5 has the row
`(x, p, [any-taint], E, T)` → must-premise, NORMAL, forward restricted
runs only. The Lean model of the emission (`Restricted.emitM`, case
`.below r → some a`, and `AnyTaintExDefs.emitTX` with the must flag)
already starts the actual itself. So M1 makes production follow the
spec emission on the M1.1 rows. M1 adds no tail, no kind and no layer.

### 3.2 Real case (prototype v3)

Run 5, `BenchmarkTest01009#doPost`, B3 entry 88, actual
`var(27).CT.MUST/T,N`. VERIFIED (`owasp/v3-routes`):

```
CURRENT initials=[var(27).CT.*/T,D ; var(27).CT.*/FLOW,N ; var(27).$/FLOW,N ; var(27).CT.$/T,N]
NEW     initials=[var(27).CT.MUST/T,N ; var(27).$/FLOW,N ; var(27).CT.$/T,N]
```

M1 fires 78 times in OWASP, all in run 5 (`BIDI_MUSTPROBE`). In the
traced owners it fires 31 times.

### 3.3 Why the cycle stops

The NEW start is NORMAL. It reaches the sink as a NORMAL fact, so the
sink records a NORMAL witness, not a DEMAND witness. No DT is made, and
the backward run hands off no DEMAND row for B3. H7 is empty, so the
analysis ends with NO_DEMAND_EDGE at run 7. VERIFIED (§6).

### 3.4 Serve every route

Sink route census (`-Dorg.opentaint.bidi.sinkRouteCensus=true`: every
NORMAL leaf at a sink witness), union over all forward runs. VERIFIED
(`owasp/routes-native` run limit 21, `owasp/v3-routes`):

| | Native | M1 |
| --- | ---: | ---: |
| NORMAL sink leaves (union) | 5,356 | 5,330 |
| Leaves only in this arm | 26 | 0 |

- The 26 native-only leaves are deep exact leaves below `arg(0)` at 3
  sinks: 01446 command injection, 01009 and 01474 SQL injection (for
  example `arg(0).CT.SB.SB.[].$/T`). They first occur in native run 7:
  they are the K-following chain of §2.4.
- At each of the 3 sinks, M1 has the NORMAL leaf `arg(0).MUST/T`. It
  covers every location below `arg(0)`. So every native route is served
  by an M1 route at the same sink. VERIFIED.

### 3.5 Execution site and volume

- **Site.** One extra test per C2 query in the ANY branch of
  `RestrictedInitialPolicy.emit`: one tail compare and one
  `result(...)` call when the actual fits the cap. No new per-fact work.
- **Volume** (OWASP, the largest project that M1 changes): 78 firings in
  run 5. The test runs on each C2 query of an ANY entry; the M1 rows
  replace two starts (STAR + FLOW STAR) with one.
- **Saving.** H5 108 → 18 rows, H6 242 → 31, H7 157 → 0. Runs 8 to 11
  are not made. VERIFIED.

### 3.6 Trivial alternatives

| Alternative | Result | Evidence |
| --- | --- | --- |
| T1. Stop on an exact repeat of the hand-off (FIXED_POINT) | The repeat starts at H7. A proven repeat needs two periods of equal state, and K changes the state in each run (§2.4): the earliest stop is run 13 or later. It also keeps the DEMAND rows that are the cause. | INFERENCE from the digests |
| T2. Probe v2: concrete marks only, keep a FLOW STAR companion | Still cycles to run 21 (70 firings per run). | VERIFIED (`owasp/routes-mp`) |
| T3. Exact start: start a deep actual at its full depth (acyclic-convergence §8) | Rejected there because it relaxes the relative cap. M1 does not: it starts the actual only when the actual fits the cap (Lean `new_depth`). | Spec |
| T4. A lower run limit | A numeric cutoff. Rejected by the stop rules. | - |

### 3.7 Withdrawal condition

Withdraw M1 if one of these occurs:

1. A confirmed or provisional result of a reference project differs
   from the native launch, apart from a provisional entry that becomes
   confirmed with the same rule, method and statement, and only after a
   hand check of the flow (§6.1 has the two fixture cases).
2. The sink route census of a reference project has a native NORMAL leaf
   that no M1 leaf at the same sink covers.
3. A backward run gets an ANY_TAINT start (the guard is lost).
4. A project gets more hand-off rows or more runs with M1 than without.

Status: condition 4 holds on Conductor for v3, v4 and v5 (§6.2, §6.4).
M1 is withdrawn in the tested forms.

## Part B. Stirling-PDF

## 4. Root cause of the Stirling-PDF fast/slow split

Full report: `docs/reports/stirling-split-20261126.md` on branch
`proto/stirling-split-20261126` (`70c10d61d`). This section gives the
summary that the rule needs.

### 4.1 The extra row

- Owner: `EmlProcessingUtils#decodeMimeHeader(String)`, premise
  `ret.*/xss`. In a slow launch, backward run 6 stores an exact row
  `ret.* -> {arg(0).X.$/xss},D,P` next to the MAY row
  `ret.* -> {arg(0).MAY/xss},D,P`. X is `String#bytes`, `CT`, or the
  three leaves `arg(0).$`, `Matcher#group.$`, `Matcher#input.$`. The MAY
  row covers every leaf of the exact row. VERIFIED in 11 of 11 launches
  that made the row.
- f6 (the owner's H6 rows) has +1 to +3 rows. Run 6 is the first run
  that differs. VERIFIED.

### 4.2 The decision point

- The root summary store keeps a TAINT lane in two parts: the diagonal
  relations (a tree with an ANY or STAR tail and no exact leaves) and the
  scalar groups (all other trees). The TaintGroup law
  (`ap/Groups.kt`, `subtractSubsumed`) runs only inside one group. No
  code compares a group row with a diagonal row. VERIFIED (code).
- If the exact value is the first protected value that reaches the root
  for `ret.*`, it goes to the scalar groups and stays. If the MAY value
  is first, the exact value is not fresh at the completion store and
  never reaches the root store. VERIFIED (PUB order, 14 of 14 launches;
  COMPL trace).
- The order is an arrival order inside run 6. It is fixed per launch:
  one worker thread gives both outcomes, and one launch makes the same
  choice again in runs 8 and 10. Its per-launch source (identity hash
  order or ids set before run 1) is not isolated. VERIFIED / INFERENCE
  as marked in the report §3.3.
- Control: for the EXACT premise `ret.$` both values go to the scalar
  groups, and the law removes the exact row in every launch. VERIFIED.

### 4.3 Causal chain

| Step | Fast | Slow (+1 row) | Slow (+3 rows) |
| --- | ---: | ---: | ---: |
| f6 extra rows | 0 | 1 | 3 |
| Owner offers, run 7 | 31,501 | 175,451 | 1,239,866 |
| Values over the field limit at a loop boundary, run 7 | 6 | 65,913 | 565,841 |
| Run 7 engine time | 3.1 s | 17.9 s | 123.1 s |

VERIFIED. The extra row gives forward run 7 an extra EXACT NORMAL
start `arg(0).X.$`. A loop in the owner wraps an exact value one field
deeper on each pass; a STAR value absorbs the chain, an exact value does
not. The loop restriction cannot cut NORMAL values, so only the field
limit stops them. INFERENCE for the loop mechanism.

### 4.4 Ablation

A drop of only the extra row at the f6 hand-off makes run 7 fast in 3
of 3 slow launches (offers within 1% of the fast form). VERIFIED.

### 4.5 Is the fast form valid? Is it an optimization?

The fast form is the analyzer's own output in the launches where the MAY
value arrives first (about 2 of 10 launches). The extra row is legal but
redundant: it asks for a subset of what the MAY row asks for. So the
fast form is not a bug in the fast launches; the slow form is a gap in
the store normal form. The optimization is to make every launch give the
fast form.

## 5. Rule H1: the hand-off normalizes each TAINT lane

### 5.1 Statement

| Row | Site | CURRENT | NEW |
| --- | --- | --- | --- |
| H1.1 | hand-off read (`HandOff.toCompacted`), per store and premise, a lane with 2 or more TAINT edges | every stored demand edge is projected | in a launch-independent order (header, then sorted decoded leaves), each tree loses the leaves that the other current trees of the lane cover (the subtraction of `TaintGroup.subtractSubsumed`), until no tree changes; an empty tree is removed |
| H1.2 | as H1.1, a lane with 1 TAINT edge | projected | CURRENT (unchanged) |
| H1.3 | FLOW and REACH edges; a tree with mixed protection | projected | CURRENT (unchanged) |
| H1.4 | the stores themselves, in-run publication, compaction keys | CURRENT | CURRENT (unchanged: H1 reads; it does not write a store) |

No tree is merged, no leaf is rewritten, no field limit changes.

### 5.2 Prototype result (from the Stirling report §8)

4 of 4 full launches with H1: COMPLETE at run 11, SARIF byte-identical
to the reference (32 confirmed + 2 provisional, same code flows). In 3
of them run 6 made the extra row, and H1 removed it; f6 is then the fast
form, and run 7 has the fast-form offers (31,197 and 31,439 against
31,501; 13,322 against 13,247). Peak RSS 9.92-10.18 GB against 10.49 GB.
VERIFIED. Gate queue 3 measures H1 again on all projects (§6).

### 5.3 Execution site and volume

- **Site.** Once per hand-off, per (store, premise) with 2 or more
  TAINT edges in one lane. Not on any per-fact path.
- **Volume** (Stirling-PDF, p01): 712 to 251,996 demand edges scanned
  per barrier, 14 to 565 lanes, 6 to 21 removed edges, at most 246 ms
  (305 ms in p04) per barrier, including the edge scan that the baseline
  also does. VERIFIED.

### 5.4 Trivial alternatives

| Alternative | Result | Evidence |
| --- | --- | --- |
| T1. Insert-time check in `FlowBackedSummaries.addPacket` | No: the exact value arrives before the MAY value in 11 of 11 slow launches, so no diagonal row exists at insert. | VERIFIED |
| T2. One worker thread | No: s01 is slow with one thread. | VERIFIED |
| T3. MAY coverage in the compactor keys (`HandoffServiceKeys.c5Alternatives`) | Would remove the row, but the compactor keys are "exact C5 image containment, never C2 MAY coverage". A row-level MAY rule needs its own C2 proof. | Code |
| T4. Two-way store normal form at insert | Gives the fast form at the barrier, but changes the fresh deltas inside each run. Larger change, not built. | INFERENCE |

H1 is the cheapest candidate: once per barrier, the subtraction that the
store already uses, no in-run change.

### 5.5 Withdrawal condition

Withdraw H1 if one of these occurs:

1. A confirmed or provisional result differs from the native reference.
2. A Stirling-PDF launch with H1 has an f6 row set for the owner that is
   not the fast form of its f5 state, or a run 7 with owner offers more
   than 2x the fast form.
3. A module, jvm or rule suite fails with H1 on.
4. The root summary store gets a normal form across its two parts. Then
   H1 removes nothing and is dead code.

## 6. Gate

Gate queue 3 (`scripts/gate-queue3.sh`, log `gate-queue3.log`, data
`gate/`). Build: branch `proto/mp-hs-20261126` at `dd068a66f` (M1 v3
and H1 on top of the diagnostics). Arms: native (both flags off), mp
(M1), hs (H1), both. All launches and suites ran under the project lock,
one at a time.

### 6.1 Module and rule suites

| Suite | native | mp (M1 v3) | hs (H1) | both (v3) | mp (M1 v4, §6.4) |
| --- | --- | --- | --- | --- | --- |
| dataflow module (2,807 tests) | 0 failed (landing baseline) | 11 failed | 0 failed | 11 failed (the same 11) | 10 failed (the v3 set without the abstract-mark `EmissionTest` case) |
| cycle fixtures (8 classes, 38 tests) | 0 failed | 7 failed | not run | 7 failed | 7 failed (the same 7, the same report entries) |
| jvm module (474 tests) | 0 failed (landing baseline) | 0 failed | 0 failed | 0 failed | 0 failed |
| rule suite (bidirectional) | pass (landing baseline) | pass | pass | pass | pass (M1 fires 20 times) |

The 11 M1 failures, classified (VERIFIED, `gate/unit-dataflow-mp`):

| Class | Tests | Expected (CURRENT) | Observed (NEW) | Verdict |
| --- | --- | --- | --- | --- |
| C2 table tests | `EmissionTest` ×3, `ReferenceOperationsTest` ×1, `ExcludedGuardCycleTest` "fine query" ×1 | STAR start (and its FLOW or abstract-mark companion) for a MUST actual that fits the cap | the M1.1 start `arg(0).p.MUST/E/T` | The table records the CURRENT row. Update it to the NEW row. |
| Cycle diagnostics | `AlternatingConditionalCycleTest`, `DifferentUniformReplyCycleTest`, `ExcludedGuardCycleTest`, `ProvisionalMustReplayCycleTest`, `ProvisionalUniformReplayCycleTest` (assert RUN_LIMIT at run 101), `ConditionalMarkMayCycleTest` (asserts run 5) | the native cycle | NO_DEMAND_EDGE at run 3 | The tests capture the native cycle as a diagnostic. M1 removes it. Update them. |

Report entries of the cycle fixtures (`OPENTAINT_BIDI_REPORT_ENTRIES`,
`gate/fixtures-*`), VERIFIED:

| Fixture | Native | M1 (mp and both) |
| --- | --- | --- |
| DifferentUniformReply, ProvisionalMustReplay, ProvisionalUniformReplay | 2 confirmed, RUN_LIMIT 101 | the same 2 confirmed, NO_DEMAND_EDGE 3 |
| ConditionalMarkMay (3 cases) | 1 confirmed each, runs 5/3/3 | the same, runs 3/3/3 |
| **AlternatingConditional** | 1 **provisional**, RUN_LIMIT 101 | the same entry **confirmed**, NO_DEMAND_EDGE 3 |
| **ExcludedGuard** | 1 **provisional**, RUN_LIMIT 101 | the same entry **confirmed**, NO_DEMAND_EDGE 3 |

The two marked rows are a result change (provisional → confirmed, same
rule, method and statement). A provisional entry is a sink that the last
run reached only through DEMAND when the run limit stopped the analysis
(`driver/Report.kt`). Hand check of the fixture flows:

- AlternatingConditional: `arg(0).f` is MUST/T. Call 1 meets rule 0
  (`arg.f.g` carries T), so `x` is MUST/U. Call 2 meets rule 2
  (`x.f.g` carries U), so `y` is MUST/T. Call 3 meets rule 0 again, so
  `z` is MUST/U. The sink `z.MAY/U` matches. The flow exists.
- ExcludedGuard: statement 1 cuts `a.f.g`, so `a.f` is MUST/T with
  `E = {g}`. Rule 0 cannot fire. Rule 1 (`arg.MAY/T`) fires because
  `a.f` itself carries T, so `x.h` is MUST/U; rule 3 gives `y.h` MUST/T;
  rule 1 gives `z.h` MUST/U; the sink `z.MAY/U` matches. The flow exists.
  The CURRENT STAR start `a.f.*/T,D` ignores the hole at `g` and fires
  rule 0 as coarse DEMAND that nothing can confirm: the maker of §2.3 in
  a small form.

So the two changes are a verified status change, not an unverified
precision gain. They need the user's decision (§11).

### 6.2 Reference projects, M1 v3 and H1 (gate queue 3)

One launch per arm, `--last-forward-run 11`, timeout 1080 s (OWASP
1000 s). Build `dd068a66f` (M1 v3: every mark). VERIFIED (`gate/`).

| Project | Arm | End | Confirmed / provisional | Wall | Peak RSS | Rule activity |
| --- | --- | --- | --- | ---: | ---: | --- |
| OWASP | native | RUN_LIMIT, run 11 | 2,633 / 0 | 215 s | 9.27 GB | - |
| OWASP | mp | **NO_DEMAND_EDGE, run 7** | 2,633 / 0 | 208 s | 9.32 GB | M1: 54 firings, run 5 |
| OWASP | hs | RUN_LIMIT, run 11 | 2,633 / 0 | 216 s | 9.33 GB | H1: 13 rows removed at H4 |
| OWASP | both | **NO_DEMAND_EDGE, run 7** | 2,633 / 0 | 211 s | 9.29 GB | M1: 28 firings; H1: 13 at H4 |
| Stirling-PDF | native | TIMEOUT in run 11 (slow form: owner f6 = 239) | 32 / 0 | 1,112 s | 9.64 GB | - |
| Stirling-PDF | mp | **TIMEOUT in run 6** | 32 / 0 | 1,112 s | 9.31 GB | M1: 82 (run 3), 602 (run 5) |
| Stirling-PDF | both | **TIMEOUT in run 6** | 32 / 0 | 1,112 s | 9.30 GB | as mp |
| Conductor | native | TIMEOUT in run 8 | 7 / 0 | 1,129 s | 9.73 GB | - |
| Conductor | mp | TIMEOUT in run 8 | 7 / 0 | 1,127 s | 9.42 GB | M1: 18,233 / 13,175 / 16,158 (runs 3/5/7) |
| Conductor | hs | TIMEOUT in run 8 | 7 / 0 | 1,127 s | 9.47 GB | H1: 56-300 rows removed per hand-off (H2-H7) |

- OWASP: the three SARIF files of mp, hs and both have the same 2,633
  results and the same results with code flows as native
  (`compare_sarif.py`). M1 gives H5 = 18, H6 = 31, H7 = 0 in all four M1
  launches (here and §2.6, §3.4). Native OWASP is itself order-dependent:
  this native launch had H5 = 53, H6 = 109 and a period 63/90; earlier
  launches had 108/242/157/254 and 79/165/103.
- **Stirling-PDF, M1 v3: backward run 6 stalls.** Native run 6 takes
  7.6 s. With M1, run 6 makes 4,687 events in 10 s and then holds one
  event in flight with no progress for 16 min 32 s, to the timeout. The
  GC log has pauses at a steady rate in that time, so the event works;
  it is not a deadlock. H5 has fewer rows with M1 (1,038 against 1,162).
  2 of 2 M1 launches stall at the same place. A third v3 launch with
  thread dumps (`gate6/Stirling-PDF-mpv3-diag`) stalls in run 6 too: the
  event is in block-output admission
  (`BlockRunState.admitOutputs` → `ScopedEdgeStore.addPacket` →
  `TaintGroup.addAll` → `canonicalize` → `subtract`), and the heap has
  10.5 M `LeafFrame` objects (337 MB). v4 removes the stall (§6.4).
- **Conductor, M1 v3: more demand rows.** H3 15,123 → 18,439, H4
  15,267 → 18,053, H5 13,827 → 23,688 (+71%); run 6 6 min 24 s → 9 min
  40 s. Withdrawal condition 4 of M1 applies.
- **Conductor, H1: fewer rows, same end.** H4 15,267 → 14,836, H5
  13,827 → 12,817, H6 67,285 → 64,360, H7 38,619 → 37,646; run 6 6 min
  24 s → 5 min 42 s. Run 8 still times out (the native end).
- **Verdict on M1 v3: fails the gate** (Stirling-PDF run 6, Conductor
  rows). The large Conductor firing counts agree with reviewer attack R6:
  restricted runs use abstract marks, and v3 makes one FLOW MUST premise
  per exclusion. v4 (concrete marks only) is gated in §6.4.
- The Conductor native run 6 also holds one event for minutes. Its
  thread dumps (`gate/conductor-native-1/stall-run6-jstack-*.txt`) show
  the loop restriction path (`LoopOutputRestriction.restrict` → `trial`
  → `observe` → `savedRows` / `probeLoopAdmissions`, `FlowGroup.addAll`),
  the known cost of N4 and N8 of the next-iteration proposal.

### 6.3 Stirling-PDF: forms, H1 and the route census (gate queues 5 and 7)

Build `d6cbcada0` (wt-v4; the native and hs arms run the same code as
`dd068a66f`). Sink route census on in every launch. VERIFIED (`gate5/`).

| Launch | Form (owner f6) | End | Confirmed / provisional | Wall | Peak RSS | Run 7 / run 9 | NORMAL sink routes |
| --- | --- | --- | --- | ---: | ---: | --- | ---: |
| native 1 | fast (234) | RUN_LIMIT, run 11 | 32 / 2 | 154 s | 9.47 GB | 1.4 s / 1.4 s | 126 |
| native 2 | fast (234) | RUN_LIMIT, run 11 | 32 / 2 | 155 s | 9.45 GB | 1.4 s / 1.6 s | 126 (equal set) |
| native 3 | **slow (235)** | **TIMEOUT in run 11** | 32 / 0 | 1,055 s | - | 11.5 s / 3 min 13 s | 126 (runs 1-9, equal set) |
| hs 1 | fast (234) | RUN_LIMIT, run 11 | 32 / 2 | 154 s | 9.48 GB | 1.5 s / 1.4 s | 126 (equal set) |
| both 1 | fast (238) | RUN_LIMIT, run 11 | 32 / 2 | 161 s | 9.46 GB | 2.1 s / 2.3 s | 126 (equal set) |
| gate-queue3 native 1 | slow (239) | TIMEOUT in run 11 | 32 / 0 | 1,112 s | 9.64 GB | - | - |

- **Route census.** The slow form, the fast form and H1 have the same
  126 NORMAL sink routes (the same set, union over the forward runs).
  So the extra row of the slow form serves no NORMAL route that the
  fast form or H1 does not serve. VERIFIED.
- **H1 also acts in fast launches.** hs 1 removed 6 to 19 covered rows
  at each hand-off (`BIDI_PROTO_SUBSUME`), in owners other than
  `decodeMimeHeader`. The routes stay equal and H7 has fewer rows (860
  against 876-885).
- **The slow form is a large cost.** With the default timeout, a slow
  launch loses the two provisional entries of run 11 (32 / 0 against
  32 / 2) and takes 7x the wall time. 2 of the 6 native launches in this
  gate had the slow form.
- With H1, 6 of 6 launches had the fast form (4 in the Stirling report,
  hs 1 and both 1 here). In hs 1 and both 1, run 6 did not make the
  extra row (f6 is the fast native value), so these two launches do not
  test H1. The test is §5.2: in 3 of the 4 report launches run 6 made
  the extra row, H1 removed it, and run 7 had the fast-form offers.

### 6.4 M1 v4 and v5 on the reference projects (gate queues 5, 7, 9, 10)

v4 (`d6cbcada0`): concrete entry mark only. v5 (`4221a2391`): v4 and a
NORMAL actual only. VERIFIED (`gate5/`, `conductor-m1/`, `m1v5/`).

| Project | Arm | End | Confirmed / provisional | Wall | Peak RSS | M1 firings |
| --- | --- | --- | --- | ---: | ---: | --- |
| OWASP | native 2 | RUN_LIMIT, run 11 | 2,633 / 0 | 213 s | 9.27 GB | - |
| OWASP | v4 ×2 | **NO_DEMAND_EDGE, run 7** (2 of 2) | 2,633 / 0 | 212 s, 209 s | 9.24, 9.30 GB | 28 (run 5) |
| OWASP | v5 | **NO_DEMAND_EDGE, run 7** | 2,633 / 0 | 211 s | 9.26 GB | 54 (run 5) |
| Stirling-PDF | v4 ×3 | 1 fast (RUN_LIMIT, run 11); 2 slow (TIMEOUT in run 11) | 32 / 2 fast; 32 / 0 slow | 159 s fast | 9.42 GB fast | 18 / 160 / 138 / 97 / 101 |
| Conductor | native | TIMEOUT in run 8 | 7 / 0 | 1,129 s | 9.73 GB | - |
| Conductor | v4 ×2 | **OOM in run 6** (2 of 2) | 7 / 0 | 724 s | 9.43 GB | 8,062 (run 3), 6,096 (run 5) |
| Conductor | v5, to run 5 | (run 5 limit) | 7 / 0 | 300 s | 9.48 GB | 5,665 (run 3), 2,453 (run 5) |

- **OWASP.** v4 and v5 converge as v3: H5 = 18, H6 = 31, H7 = 0. The
  route census of v4 has the same result as v3 (§3.4): 5,330 against
  5,356 NORMAL sink leaves, 0 v4-only, and the 26 native-only leaves are
  covered by `arg(0).MUST/T` at the same 3 sinks.
- **Stirling-PDF.** v4 has no run-6 stall (3 of 3; v3 stalled in 3 of 3).
  The route census is equal to native (126 routes). M1 does not change
  the fast/slow split (§4). In the fast form the forward runs 7, 9 and 11
  take 0.7 to 1.1 s more than native (1 launch).
- **Suites (v4).** Fixtures: the same 7 failures and report entries as v3.
  Dataflow module: 10 failures (the v3 set without the abstract-mark
  `EmissionTest` case). jvm module and rule suite pass; M1 fires 20 times
  in the rule suite.
- **Conductor: M1 fails the gate.** v4 runs out of memory in backward
  run 6 in 2 of 2 launches; native times out in run 8. v5 has the same
  rows as v4 (table below), so the DEMAND-actual case is not the cause.

Hand-off rows to run 5 (`handoffDump`, union of method and block rows),
VERIFIED:

| Hand-off | Native | v4 | v5 |
| --- | ---: | ---: | ---: |
| H3 (forward) | 18,541 | 24,363 | 23,318 |
| H4 (backward) | 30,961 | 69,797 | 69,579 |
| H5 (forward) | 26,083 | 60,203 | 60,374 |
| H4 block-scope FLOW rows | 18,041 | - | 52,736 |
| H4 `ParametersUtils#replace` | 14,464 | - | 44,265 |
| H4 `replace`, loop block B2, `MAY/FLOW@2 => */FLOW@2` | 777 | - | 28,652 |

### 6.5 Root cause of the M1 cost on Conductor

The chain. Each step is VERIFIED unless marked. Data: Conductor to run 5
with the hand-off dump (`conductor-m1/native-r5b`, `m1v5/`). Owner
`ParametersUtils#replace(Map, DocumentContext, String)`, context `[{}]`,
map-entry loop block B2 (header port 40). `var(3)` is the iterator.

1. **M1 fires often on Conductor.** v5: 5,665 firings in run 3 and 2,453
   in run 5 (OWASP: 54, all in run 5). Each firing replaces a STAR DEMAND
   start with a NORMAL MUST start.
2. **MUST facts reach the loop.** CURRENT cuts each NORMAL MUST actual at
   a call or block entry with a concrete ANY entry to a STAR DEMAND
   start. This cut keeps MUST facts out of the callees and blocks. M1
   removes the cut, so MUST facts go into them. Example: B2 gets
   `var(3).Iterator#Element.Map$Entry#Value.MUST/T`.
3. **CURRENT makes FLOW MUST starts from them.** At an abstract ANY entry
   at the path of a MUST actual (or below it), CURRENT C2 starts a FLOW
   MUST premise (`RestrictedInitialPolicy.emit`, the `q == p` row
   `ANY_TAINT -> result(p, ANY_TAINT, actual.exclusion)` and the
   `p.startsWith(q)` row). M1 does not change these rows. They now get
   MUST actuals at the iterator aliases `var(3).X`, X in
   {`Iterator#Element`, `Map$Entry#Value`, `Map$Entry#entryData`,
   `HeaderIterator#headers`, `HeaderElementIterator#headerElements`,
   `StrTokenizer#inputContent`}. INFERENCE for the start site (H2 is not
   dumped); ablation A5 (§6.6) confirms the effect.
4. **A loop-carried FLOW relation over the alias set.** H3 for B2 has
   the rows `var(3).X.MAY/FLOW => var(3).X'.MAY/FLOW`: a FLOW MUST premise
   at `X'` (the hand-off writes MUST as MAY) and its conclusion at `X`
   after one pass: 132 rows, 6 premises and 22 conclusions. Rows of B2
   with a depth-1 FLOW entry at `var(3)`: 121 in v5, 22 in native, 22
   with A5. B2 itself has few H3
   rows (304 against 273).
5. **The backward run crosses the alias set two levels deep.** Backward
   run 4 starts each depth-1 FLOW demand one counted field deeper (the
   relative cap). So B2 gets 2-deep STAR FLOW starts `var(3).X.Y.*/FLOW`
   for every pair of aliases. One entry,
   `var(3).Iterator#Element.ImmutablePair#right.MAY/FLOW`, has 351 such
   premises (400 in the second context of the owner). H4 for B2: 16,989 rows (13,095 with a 2-deep entry) against
   3,348 in native.
6. **Run 6 runs out of memory.** H5 has 60,374 rows against 26,083.
   Backward run 6 holds 2 to 6 events for 6 minutes while the heap grows
   to the limit. The thread dump came after the OOM. Native run 6 spends
   its 6 minutes on the loop restriction path of the same owners
   (`LoopOutputRestriction.restrict`, `FlowGroup.addAll`;
   `gate/conductor-native-1/stall-run6-jstack-*.txt`). Native Conductor
   times out in run 8 in `ParametersUtils#replace` and `replaceList`
   (group-A landing report). INFERENCE: M1 run 6 does the same work on
   2.3 times the input.

So M1's own row (M1.1) does not make the cost. CURRENT's FLOW MUST rows
and the backward relative cap make it, on more MUST facts. The CURRENT
cut of §2.3 step 4 is a cost control as well as the maker of the OWASP
cycle.

### 6.6 Ablations of the Conductor cost

Each ablation is a diagnostic flag on `proto/mp5-20261127` (worktree
`wt-v4`). Conductor to run 5 with the hand-off dump, one launch per arm,
under the project lock. All arms end at the run-5 limit with 7 confirmed
and 0 provisional. VERIFIED (`m1v5/`, `gate-queue11.log` to
`gate-queue16.log`).

| Arm | What it changes | H3 | H4 | H5 | H4 `replace` | Wall |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| native | - | 18,541 | 30,961 | 26,083 | 14,464 | 293 s |
| v5 | M1 | 23,318 | 69,579 | 60,374 | 44,265 | 300 s |
| v5 + A1 | the hand-off writes a concrete MUST premise as `x.p.*/T`, not `x.p.MAY/T` | 23,687 | 70,091 | 62,650 | 44,212 | 296 s |
| v5 + A2 | A1, and a FLOW MUST premise as `x.p.*/FLOW` | 23,681 | 70,392 | 62,511 | 44,214 | 293 s |
| v5 + A3 | the backward read of a concrete MUST record demands `x.p.$/T`, not `x.p.MAY/T` | 23,687 | 70,152 | 63,008 | 44,302 | 312 s |
| v5 + A4 | the M1 start keeps the FLOW STAR companion | 23,681 | 69,917 | 60,686 | 44,214 | 302 s |
| v5 + A5 | a MUST actual at an abstract ANY entry gives a FLOW STAR start, not a FLOW MUST start | 22,664 | 46,850 | 34,983 | 18,771 | 381 s |
| v5 + A6 | the backward read of a FLOW MUST record demands `x.p.*/FLOW`, not `x.p.MAY/FLOW` | 23,673 | 76,496 | 62,267 | 46,303 | 361 s |
| native + A1 | A1 without M1 | 18,558 | 30,987 | 26,200 | 14,464 | 301 s |
| native + A2 | A2 without M1 | 18,560 | 30,995 | 26,290 | 14,462 | 293 s |
| native + A5 | A5 without M1 | 18,527 | 46,103 | 35,680 | 18,558 | 410 s |

A3 in the STAR form (`x.p.*/T`) stops in backward run 4 with "A concrete
exact premise cannot have a STAR target" (`ap/EdgeApplication.kt:25`):
the read premise is EXACT, and an EXACT premise cannot have a STAR
target. The table has the EXACT form.

Results:

- **Not the cause:** the hand-off form of the MUST premise (A1, A2: the
  T rows go back to the STAR form, `MAY/T@2 => */T@1` 253 → 2,839, but
  H4 does not change), the backward read of MUST records (A3, A6), and
  the FLOW STAR companion (A4).
- **The cause:** the FLOW MUST start rows of CURRENT C2 (A5). With A5 in
  both arms, M1 adds almost no rows: v5 + A5 against native + A5 is
  +1.6% at H4 and -2.0% at H5. Without A5, M1 adds +125% at H4 and +131%
  at H5.
- **A5 is not a fix.** A5 alone costs +49% H4 rows, +37% H5 rows and
  +40% wall time to run 5 in native. It also changes CURRENT for every
  MUST actual.
- OWASP with v5 + A1 converges (NO_DEMAND_EDGE in run 7, 2,633 / 0).

## 7. Semantic scope (proof-guide.md)

### 7.1 M1

| | CURRENT | NEW |
| --- | --- | --- |
| Changed: C2 start of a NORMAL MUST actual that fits the cap below a concrete ANY entry, forward restricted run | STAR start, DEMAND (concrete mark) + FLOW STAR companion | the actual itself, NORMAL must-premise with the actual's `E` |
| Unchanged | all other C2 rows (M1.2-M1.6), C5, the backward run, the relative cap, `fitsBudget`, K, the stores, the hand-off, report building | same |

Affected invariants and proofs: the C2 contract with exclusions
(`AnyTaintExCov.emitX_contract`) now covers the M1.1 rows directly,
because M1.1 is the spec emission (`MustStartFit.new_eq_spec`). The
relative cap (`new_depth`). The layer of the start
(`cur_start_demand`, `new_start_normal`).

Hidden changes (checked):

- **Summary keys.** The start is the key of the callee or block summary.
  A MUST key is a different key from the STAR key. So M1 changes summary
  sharing: a MUST-key summary applies only where an actual satisfies the
  must-premise (`satX`). The route census (§3.4) and the reports show no
  loss on OWASP.
- **FLOW STAR companion removed.** M1.1 makes no FLOW STAR companion. The
  FLOW STAR companion fed the helper inside-read DEMAND rows (§2.5).
  No NORMAL route is lost (§3.4).
- **Layer of downstream facts.** Facts from the M1 start are NORMAL. This
  is the intended change: it is why the cycle stops, and it is why two
  fixture entries become confirmed (§6.1).
- **Exclusion.** The NEW start keeps the actual's `E`. A location that
  the actual excludes is not covered by the start (`new_start_covers_iff`).
  CURRENT ignored `E` (STAR start with an empty exclusion).
- **MUST facts in blocks and callees (missed in the first scope; found
  by the Conductor gate).** The CURRENT cut keeps NORMAL MUST facts out of
  each block and callee with a concrete ANY entry. M1 lets them in, and
  CURRENT rows that M1 does not touch act on them: the FLOW MUST start
  rows of C2 and the backward relative cap (§6.5). This is the cost that
  fails the gate.

### 7.2 H1

| | CURRENT | NEW |
| --- | --- | --- |
| Changed: the demand rows that the hand-off projects for a lane with 2 or more TAINT edges | every stored edge | the lane normal form: covered leaves removed, empty trees removed |
| Unchanged | stores, in-run publication, compaction keys, FLOW/REACH edges, mixed-protection trees, report building | same |

Affected invariants: H1 keeps the union of the location sets of the lane
rows (`HandoffLaneSubsume.normalize_covers`) and adds no coordinate
(`normalize_sub`). H1 does NOT keep the C2 starts of the next run: a
removed deep EXACT row can take away an EXACT NORMAL start (§9 R1). This
is the store subsumption rule of ap.md, which CURRENT already applies in
one store part and in every fast launch.

Hidden changes (checked):

- **Start forms of the next run.** A removed exact row gave an EXACT
  NORMAL start; the covering MAY row gives a STAR start (DEMAND for a
  concrete mark) and a FLOW EXACT companion at the root. This is the same
  start set that a native fast launch makes. Route census for Stirling-PDF:
  §6.3.
- **Order.** H1 runs in a sorted order, so its output does not depend on
  the store order.

## 8. Proof scope and model/production differences

Lean modules (constructive: only `propext` and `Quot.sound`, see the
`#print axioms` lines):

- `spec/lean/ApSpec/MustStartFit.lean` (M1): `new_eq_cur_off`,
  `cur_on_rows`, `new_eq_spec`, `new_contract`, `cur_start_demand`,
  `new_start_normal`, `new_start_is_actual`, `new_start_covers_iff`,
  `new_depth`, and 7 `decide` vectors (the OWASP rows: MUST fits, MUST
  cut, EXACT, MAY, uncounted accessor).
- `spec/lean/ApSpec/HandoffLaneSubsume.lean` (H1): `step_sub`,
  `passZ_sub`, `normalize_sub`, `step_covers`, `passZ_covers`,
  `normalize_covers`, `step_removes_covered`, and 4 `decide` vectors (the
  Stirling-PDF lane in both arrival orders, the +3 form, a row that is
  not covered).

Differences between the models and production:

| # | Model | Production | Effect |
| --- | --- | --- | --- |
| D1 | `fitsB` counts all fields with one predicate `cnt` | `firstFieldEnd` has a STATIC anchor rule | Not modelled. In the traced owners every M1 start has an `arg(i)` or `var(i)` base (VERIFIED, `owasp/v3-routes`, 106 MUST starts); no launch shows a STATIC case. |
| D2 | No field limit K, no `fitsBudget` | `result(...)` checks the budget; null → fallback | The fallback is CURRENT (M1.2). |
| D3 | The model uses the actual's mark for the start | production uses the bound mark (`boundMark`: the entry mark, or the actual mark for a group entry) | With the v4 guard both are concrete and equal by `markMatchB` for a non-group entry. v3 (any mark) had FLOW MUST starts that the model does not cover (§9 R6). |
| D4 | Companion starts are not modelled | `emitAdmissions` adds EXACT and FLOW companions | M1 removes only the FLOW STAR companion of the replaced STAR start (§3.2, measured). |
| D5 | M1 has no direction | production checks `direction == FORWARD`; `legalInitial` rejects ANY_TAINT backward | M1.5 by code reading and the v1 → v3 fix. |
| D6 | H1: a coordinate is covered by ONE coordinate of another row; `cov` is reflexive and transitive | `alg.subtract` subtracts a whole stored tree with `at`/`below` rules, exclusions and marks | The model proves the lane law for any such `cov`. That `alg.subtract` is such a coverage is the TaintGroup law of the store, not proved here. |
| D7 | H1: the normal form depends on the order for equal rows (the later one stays) | production sorts by a launch-independent key | Not proved: order independence for every input. |
| D8 | H1: rows are lists of coordinates | rows are TaintTrees with headers (tail, exclusion) | Header coverage (`coversAny`, `atAny`) is in the production `covered` function only. |
| D9 | H1: the theorems are about location sets | the next run uses each row as a C2 entry with its own relative cap | The location union is kept; the C2 starts are not (§9 R1). The model does not claim them. |
| D10 | M1: the model has no layer | v5 starts only a NORMAL actual (M1.2b) | Not modelled. M1 is not WI (§11), so the model stays at v4. A new M1 form needs the layer guard in `MustStartFit`. |

## 9. Reviewer attack

A read-only reviewer got the code of both rules (not the verdicts of this
document) with the task to break them. Each claim below was checked
again in the code. Verdicts: **CONFIRMED** (true in the code),
**PLAUSIBLE** (possible, not shown in a launch), **REFUTED**.

| # | Attack | Verdict | Response |
| --- | --- | --- | --- |
| R1 | H1 removes a deep EXACT demand row under a MAY row. C2 is not monotone in region coverage: an EXACT entry at the actual's path gives an EXACT start (NORMAL for a NORMAL actual, `RestrictedInitialPolicy.emit`, `q == p` branch); a MAY entry above it gives a STAR start at the first counted field (DEMAND for a concrete mark). So the next run can lose a NORMAL start, and a confirmed finding can become a DEMAND target. | **CONFIRMED** (code) | The loss is not new. ap.md (store subsumption) says that `[any]` at `p` subsumes every demand fact at or below `p` with its mark, so the spec store makes the same removal. CURRENT makes it in every fast Stirling-PDF launch (completion store) and for every EXACT premise (scalar groups). H1 makes it independent of the arrival order for STAR premises too. The Stirling-PDF case is this attack: the removed row gave an EXACT NORMAL start from a STAR NORMAL actual. Real effect: SARIF identical in 14 launches; route census in §6.3. The spec rule is an open question (§11). |
| R2 | The same at depth 1 when M1 is off. | **CONFIRMED** for STAR and MUST actuals (M1 off) | With M1, a MUST actual at depth 1 gets the MUST start. A STAR NORMAL actual at depth 1 still gets a STAR DEMAND start: the Stirling-PDF case. |
| R3 | H1 can stall progress: the removed row comes back in each backward run, and the deep NORMAL start is never made. | **PLAUSIBLE** | H1 cannot make a false NO_DEMAND_EDGE (each lane keeps one row). Stirling-PDF ends at run 11 in both forms. |
| R4 | M1 drops the FLOW STAR companion; a leaf of another mark on the same path loses its route through the callee. | **PLAUSIBLE** | The companion feeds the OWASP cycle (§2.5, v2). CURRENT already has no FLOW STAR companion for a MUST actual at the entry path. OWASP route census: no NORMAL sink leaf lost (§3.4). Withdrawal condition 2. |
| R5 | A NORMAL MUST start ignores an EXACT cleaner (`Clean.kt`), so a sink behind it can be confirmed where CURRENT stays provisional. | **PLAUSIBLE** (a result change, as specified by ap.md §6.3) | Gate: no reference project result may change (§6.2). |
| R6 | v3 M1 starts an abstract-mark entry as a FLOW `[any-taint]/E` premise one field below the entry (`boundMark` keeps the entry mark `*`). The ap.md start table has no FLOW must row, and one premise per `E` loses the cross-mark sharing. | **CONFIRMED** (code) | **v4** adds the concrete-mark guard of the EXACT rule (`mark is MarkSlot.Concrete`) to `emit`, `canEmitInitial` and the oracle (`d6cbcada0`). CURRENT has the same FLOW form at the entry path; that is out of scope here. In the traced OWASP owners all 25 M1 starts had a concrete mark. v4 is gated in §6.4. |
| R7 | The test oracle mirrors M1 line by line, so the oracle tests cannot find a semantic error in M1. | **CONFIRMED** | The independent check is the Lean model: the M1 row equals the spec emission (`new_eq_spec`) and has the C2 contract (`new_contract`). |
| R8 | M1 fallback (M1.2) is dead code: `legalInitial` gives the same answer for STAR and ANY_TAINT at the same path and mark. | **CONFIRMED** | Drop the fallback in the landed form. |
| R9 | (Found by the gate, not by the reviewer.) M1 removes the cut that keeps NORMAL MUST facts out of blocks and callees; CURRENT's FLOW MUST start rows then multiply them in loops. | **CONFIRMED** (Conductor, §6.5, §6.6) | M1 is not WI. |
| - | M1 exceeds the cap; M1 at a STATIC anchor; M1 makes a NORMAL start from a DEMAND actual (a DEMAND actual gives a DEMAND start, `AdmittedInitial`); M1 in a backward run; `canEmitInitial` and `emit` disagree; M1 claims a mark the actual lacks; the H1 coverage relation is wrong for exclusions, STAR, MUST, protection; a row removed by a later-reduced row is not covered; H1 changes stores, records or targets | **REFUTED** (code) | - |

## 10. Blind spots

- **ThingsBoard.** Run 1 goes out of memory. M1 acts only in restricted
  forward runs (run 3 and later), and H1 only at a hand-off. Neither
  rule can act on ThingsBoard.
- **M1 on other projects.** M1 fires on all three projects: OWASP 28 to
  54 (run 5), Stirling-PDF 18 to 160 per forward run, Conductor 5,665
  (run 3, v5). The cost shows only on Conductor.
- **Start site of §6.5 step 3.** The dumps start at H3, so the C2 query
  that makes the FLOW MUST starts in B2 is INFERENCE. A5 confirms the
  effect, not the site.
- **One launch per ablation arm.** The row counts repeat within 2% where
  two arms must be equal (v4 against v5; A1, A2 and A4 against v5).
- **Conductor never completes.** Native times out in run 8 and M1 runs
  out of memory in run 6, so the Conductor gate compares rows, the time
  to run 5 and the end state, not complete results.
- **H1 route census.** Done for Stirling-PDF (§6.3: 126 equal routes). Not
  done for OWASP and Conductor; their results are equal.
- **H1 in module suites.** The suites do not log the hand-off lines, so
  that the test JVMs used the H1 flag is INFERENCE (the M1 flag reached
  them by the same mechanism and changed the results).
- **Source of the Stirling order.** Not isolated (§4.2).
- **Machine load.** The machine is shared. Times are supporting data;
  the claims use rows, offers and counters.

## 11. WI classification

| Rule | Improvement | Negative consequence | Verdict |
| --- | --- | --- | --- |
| H1 | Stirling-PDF: the fast form in every H1 launch, including the 3 launches where run 6 made the extra row (§5.2); a slow native launch takes 7x the wall time and loses 2 provisional entries at the timeout (§6.3). Fewer hand-off rows: Conductor H4 to H7 -2% to -9%, Stirling-PDF H7 860 against 876-885, OWASP 13 fewer at H4 (§6.2, §6.3). After H4, OWASP follows one of its order-dependent native forms (H5/H6 = 53/109, 79/165 or 108/242 in native launches); H1 launch 1 had 108/228. | None measured: results equal on all projects, Stirling-PDF SARIF byte-identical and route census equal, suites pass. R1 (an EXACT NORMAL start can go) is the CURRENT store law; it is the same start set as a native fast launch. | **WI.** The spec question of R1 is a user decision (§14, D2). 3 launches per project: §5.2, §6.3, §11.1. |
| M1 | OWASP: NO_DEMAND_EDGE in run 7 instead of the run limit, results equal, every native route served (§3.4, §6.4). | Conductor: +125% H4 rows, +131% H5 rows, OOM in run 6 in 2 of 2 launches (§6.4); 2 fixture entries change from provisional to confirmed (§6.1). | **Not WI.** Revisit after the Conductor loop cost is fixed (§14, D1). |

### 11.1 H1 replicates on OWASP and Conductor

Gate queue 17: launches 2 and 3 of the hs arm, the settings of gate
queue 3, build `73e07fdb2` (`wt-v4`; every ablation flag off, so the arm
is CURRENT + H1). Rows are `BIDI_HANDOFF_COMPACTION rows=`. VERIFIED
(`h1rep/`, `gate-queue17.log`).

| Project | Launch | End | Confirmed / provisional | SARIF against native 1 | Wall | Peak RSS | H4 | H5 | H6 | H7 |
| --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| OWASP | native 1 | RUN_LIMIT, run 11 | 2,633 / 0 | - | 215 s | 9.27 GB | 529 | 53 | 109 | 63 |
| OWASP | hs 1 | RUN_LIMIT, run 11 | 2,633 / 0 | same results and flows | 216 s | 9.33 GB | 516 | 108 | 228 | 157 |
| OWASP | hs 2 | RUN_LIMIT, run 11 | 2,633 / 0 | same results and flows | 214 s | 9.26 GB | 516 | 82 | 172 | 117 |
| OWASP | hs 3 | RUN_LIMIT, run 11 | 2,633 / 0 | same results and flows | 212 s | 9.27 GB | 516 | 82 | 172 | 117 |
| Conductor | native 1 | TIMEOUT in run 8 | 7 / 0 | - | 1,129 s | 9.73 GB | 29,920 | 25,236 | 149,889 | 85,380 |
| Conductor | hs 1 | TIMEOUT in run 8 | 7 / 0 | same results and flows | 1,127 s | 9.47 GB | 28,944 | 22,917 | 145,099 | 83,185 |
| Conductor | hs 2 | TIMEOUT in run 8 | 7 / 0 | same results and flows | 1,127 s | 9.63 GB | 29,223 | 23,921 | 146,004 | 83,291 |
| Conductor | hs 3 | TIMEOUT in run 8 | 7 / 0 | same results and flows | 1,127 s | 9.73 GB | 29,257 | 24,011 | 145,850 | 83,304 |

- H1 does not change the end or the results of OWASP and Conductor in 3
  of 3 launches. H1 is not a fix for either problem; it is the Stirling-PDF
  rule, and these launches check that it costs nothing elsewhere.
- OWASP H4 is 516 in all H1 launches (native 529). After H4, OWASP has
  its order-dependent forms in both arms (§6.2).
- Conductor has fewer rows at H4 to H7 in 3 of 3 launches (-2% to -9%).
  Peak RSS is not higher (9.47 to 9.73 GB against 9.73 GB). Wall time is
  the timeout in both arms.

## 12. Checklist

```text
[x] Failure class and real trace (project, run, owner, count)        §2.1, §4.1, §6.5
[x] Ablation result on the real case                                  §2.6, §4.4, §6.6
[x] Native prototype result: findings, time, memory, 3 launches       §5.2, §6.2-§6.4, §11.1
[x] Execution site and measured volume of each new operation          §3.5, §5.3
[x] Selected semantic scope: changed / unchanged                      §7
[x] Proof scope, and each difference between model and production    §8
[x] Withdrawal condition                                              §3.7, §5.5
[x] WI classification                                                 §11
[x] Proofs (H1; M1 is not WI, its model stays at v4)                  §8
```

## 13. Evidence paths

- OWASP: `owasp/full-a` (native, run limit 21, row census),
  `owasp/full-trace-native` (owner trace), `owasp/routes-native` and
  `owasp/v3-routes` (route census), `owasp/full-mp` (probe v1),
  `owasp/v2-trace` and `owasp/routes-mp` (probe v2),
  `owasp/single-01474-a` (EXACT control).
- Stirling-PDF: `stirling/launches/` (see the Stirling report §13).
- Gate: `gate/`, `gate-queue3.log`.
- M1 v4 and v5: `gate5/` (v4, native and the route census),
  `conductor-m1/` (Conductor native and v4 to run 5 with the hand-off
  dump, `mp-r7-diag`), `m1v5/` (v5 and ablations A1 to A6),
  `gate6/Stirling-PDF-mpv3-diag` (v3 stall dumps). Logs
  `gate-queue5.log` to `gate-queue16.log`; scripts in `scripts/`.
- H1 replicates: `h1rep/`, `gate-queue17.log`.
- Branches: `proto/cycle-trace-20261126` (diagnostics, M1 v3 at
  `3b1322f49`), `proto/must-probe-20261126` (= `3b1322f49`),
  `proto/stirling-split-20261126` (H1 at `87a315db4`, report
  `70c10d61d`), `proto/mp-hs-20261126` (both, `dd068a66f`),
  `proto/mp4-hs-20261127` (M1 v4, `d6cbcada0`), `proto/mp5-20261127`
  (M1 v5 `4221a2391`, streamed hand-off dump `578ffaf7c`, ablations A1 to
  A6 up to `73e07fdb2`).

## 14. Decisions for the user

**D1. OWASP.** The root cause is complete (§2), and M1 is the spec
emission (§3.1), but M1 cannot land while the Conductor loop cost exists.
Options:

1. **Fix the Conductor loop cost first, then gate M1 again
   (recommended).** The M1 cost lives in the backward loop summaries of
   `ParametersUtils#replace` and `replaceList` (§6.5). Native Conductor
   already times out in run 8 in the same owners, on the loop restriction
   path (§6.2). The group-A proposals P2 (semi-naive loop-block replay) and
   P3 (incremental `FlowGroup.addAll`) act on that path. So this order
   fixes a native problem first, and M1 then gets a fair gate.
2. **A MAY rule with progress for the DT cycle.** Keep the CURRENT cut,
   and make the backward answer to a DEMAND witness narrower in each
   round. Not designed: the period-2 repeat (H7 = H9, H8 = H10) shows
   that the current backward seeds give no progress, so this needs a
   progress measure first.
3. **No change for OWASP now.** The reports are final at run 3, and each
   run after run 7 takes 0.33 s or less (§2.1). The cost is the end
   status (run limit), not time.

The trivial alternatives of §3.6 stay rejected. Ablation A5 is not an
option: it removes the M1 cost but adds +49% rows in native (§6.6).

**D2. H1 and C2 monotonicity (R1).** H1 can remove an EXACT demand row
that a covering MAY row makes redundant. In the next run this can give a
STAR DEMAND start in place of an EXACT NORMAL start, because C2 is not
monotone in region coverage. CURRENT makes the same removal in every fast
Stirling-PDF launch. Decide: land H1 as it is (the store law of ap.md),
or first make the spec say which form the hand-off keeps.

**D3. Fixture status (only if M1 lands later).** Two cycle fixtures
change from provisional to confirmed with M1 (§6.1). The hand check says
that both flows exist.
