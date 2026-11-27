# OWASP non-termination and Stirling-PDF fast/slow split: root causes and three rules

Status: PROPOSAL, 27 November 2026. Three rules in two landing units:
**M1 + F1** (OWASP: M1 stops the cycle, F1 removes the cost that M1
exposes on Conductor) and **H1** (Stirling-PDF). All three are native
prototypes behind flags on proto branches. Verdict (§11): **H1 is WI.
The landing set M1 + F1 + H1 is WI with a price** (decision D1, §14):
OWASP ends with NO_DEMAND_EDGE in run 7 with equal results, routes and
time; Stirling-PDF has the fast form in every launch (5 of 5); and in
3,000 s Conductor ends run 8 in 2 of 3 launches, where native ends it in
0 of 2. Every result stays. The price: Conductor backward run 6 is +24%
to +47% slower (the cause is traced for M1 + F1 in §6.8; with H1 it is
INFERENCE), Conductor run 8 goes above the 90% memory threshold once in
each launch, and the fast form of Stirling-PDF takes up to 8% more wall
time. **M1 alone and M1 + F1 without H1 are not WI** (M1 alone runs out
of memory in Conductor run 6; M1 + F1 without H1 has run 6 +55% to +62%
and ran out of memory in run 8 in its one 3,000 s launch).
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
| A | OWASP reaches the hard run limit (run 11, or run 21 with a higher limit). The reports are final at run 3. | C2 cuts a MUST actual that fits the relative cap to a STAR start. A STAR start with a concrete mark is DEMAND. Its DEMAND witness at the sink makes the same DEMAND rows in each backward run: an exact period-2 cycle from hand-off 7 (§2). | **M1**: in a forward restricted run, a NORMAL MUST actual that fits the cap below a concrete ANY entry starts as itself (NORMAL must-premise), the start row of ap.md §6.5 (§3). | OWASP: NO_DEMAND_EDGE in run 7 in every M1 launch, results equal, every route served. M1 alone: Conductor OOM in run 6. | **Not WI alone** |
| A1 | Cost of M1 on Conductor: H4 +125%, OOM in run 6 | M1 lets NORMAL MUST facts into blocks and callees. CURRENT C2 starts them as FLOW MUST premises at abstract entries, and the C5 companion clause takes a FLOW STAR member but not a FLOW MUST member. So a FLOW MUST premise keeps only depth-1 pieces, and the loop of `ParametersUtils#replace` makes a loop-carried relation over its iterator aliases that the backward run crosses two fields deep (§6.5). | **F1**: the C5 companion clause also takes a FLOW MUST member whose concrete instance is a legal start (the instance law, §3.8). | M1 + F1: no OOM to run 7, results equal, H4 +6% to +11% instead of +125% (§6.6, §6.7). F1 alone: no change. | with M1 and H1 |
| A2 | The rest of the M1 + F1 cost on Conductor: backward run 6 +55% to +62% (+24% to +47% with H1) | A must-premise has end-exact edges (ap.md §6.5), so a backward read of its record answers at the premise path. With M1 a getter gets a FLOW MUST premise next to its FLOW STAR premise, and its shallow answer covers the deep one. The task mapper entries stay one field shallower than native and admit more DEMAND actuals, which reach the loop of `replace` (§6.8; traced without H1, INFERENCE with H1). | No rule. The precise form (FLOW STAR, ablations A5 and A5c) costs more than the depth it saves (§6.8). | In 3,000 s the landing set ends run 8 in 2 of 3 launches and native in 0 of 2 (§6.9). M1 + F1 without H1 ran out of memory in run 8 in its one launch. | the price of D1 |
| B | Stirling-PDF has fast launches (run 7 in 2-3 s) and slow launches (run 7 in 18-123 s, run 9 can time out). | The root summary store keeps an exact demand row next to a MAY row that covers it, if the exact value arrives first in run 6. The hand-off projects both rows. The exact row gives an EXACT NORMAL start that a loop wraps up to the field limit (§4). | **H1**: the hand-off normalizes each TAINT lane of a store with the removal half of the store's own TaintGroup law (§5). | Results equal on all projects, Stirling-PDF route census equal, suites pass; fewer rows; the fast form in every H1 launch. | **WI** |

The landing set is **M1 + F1 + H1**. No rule relaxes a cap, stops on
reports, cuts work by a number or switches a rule off in a scope. The
open decisions for the user are in §14.

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

Status: condition 4 holds on Conductor for M1 alone in v3, v4 and v5
(§6.2, §6.4). M1 alone is withdrawn. M1 v5 with rule F1 is gated in
§6.7 and §6.9: condition 4 still holds for the Conductor hand-offs H3 to
H5, and not for H6, H7 or the number of runs (two more runs in the same
time). §11 weighs both.

### 3.8 Rule F1: the C5 companion clause takes FLOW MUST

F1 removes the cost that M1 causes on Conductor (§6.5). M1 and F1 are
one landing unit: M1 stops the OWASP cycle, and F1 removes the cost
that M1 exposes. F1 is also gated alone (§6.7).

The principle (the **instance law**). A FLOW member is one relation for
every mark. Under a concrete-mark row it answers for the row's mark. So
C5 accepts it under that row when its concrete instance (the same path,
tail and `E` with the row mark) is a legal start under the row. CURRENT
applies this law to the FLOW STAR member only (`canStoreInitial`, the
companion clause). There the law equals the C2 image, because C2 emits
the FLOW STAR companion of each concrete STAR primary. F1 applies the
same law to the FLOW MUST member.

| Row | Run | Row entry `Dc` | Member | CURRENT | NEW |
| --- | --- | --- | --- | --- | --- |
| F1.1 | forward restricted | concrete mark, ANY tail | FLOW MUST `x.p.MUST/E/FLOW` (no excluded mark) whose concrete instance `x.p.MUST/E/T` is a legal start under `Dc` | not accepted: only the abstract rows serve it | accepted, as a FLOW STAR member with a legal concrete instance is |
| F1.2 | forward restricted | concrete mark | FLOW STAR | accepted (companion clause) | CURRENT (unchanged) |
| F1.3 | any | abstract mark | any | CURRENT | CURRENT (unchanged, Lean `new_eq_cur_abs_entry`) |
| F1.4 | backward | any | FLOW MUST | not accepted (`legalInitial` rejects ANY_TAINT backward) | CURRENT (unchanged) |
| F1.5 | any | concrete mark | FLOW EXACT, FLOW MAY, a concrete member | CURRENT | CURRENT (unchanged) |

Where the concrete instance is legal (`canEmitInitial`):

- At the entry path under an ANY entry: the CURRENT C2 row
  `ANY_TAINT -> result(p, ANY_TAINT, ...)`. This case exists without M1
  (Lean `native_equal_path`: without M1, F1 adds only members at the
  entry path).
- One counted field below an ANY entry: the M1 row (M1.1). This case
  exists only with M1.
- Never deeper than `FL(Dc)+1` (Lean `cap_stays`) and never beyond K
  (`legalInitial`, `fitsBudget`).

**Real case.** Conductor, run 3, `ParametersUtils#replace`, block B2.
With M1, the premise `var(3).HeaderIterator#headers.MUST/FLOW` meets
only the abstract rows and publishes the depth-1 pieces
`var(3).X.MAY/FLOW,D` (§6.5 step 4). With F1 it also meets the concrete
row `var(8).MAY/T => var(3).$/T`, as its STAR twin does, and gets the
depth-0 piece. The Lean vectors (`FlowMustCompanion.Vec`) have this row.

**Why the cost goes.** The depth-0 piece covers the depth-1 pieces of
the same premise in the store, so the hand-off gives the FLOW MUST
premise the depth-0 row that native gives its STAR twin. Backward run 4
then has no 2-deep crossing of the alias set. H4 `replace`: 14,464
(native), 44,265 (M1), 14,655 (M1 + F1). VERIFIED (§6.7).

**Execution site and volume.** One more tail test in the companion
clause of `canStoreInitial` for each C5 acceptance test of a FLOW
member. Each member that F1 accepts gets the row restriction
(`restrictConclusionOnly`), the exit-depth limit and the merge, the
same work as a FLOW STAR member under that row. The prototype has no
firing counter; the volume is measured as rows and time (§6.7).

**Trivial alternatives.**

| Alternative | Result | Evidence |
| --- | --- | --- |
| A5: a MUST actual at an abstract entry gives a FLOW STAR start | Removes the M1 cost, but +49% H4 rows and +40% wall time alone (a FLOW STAR premise keeps the path: one row for each path, §6.8) | VERIFIED (§6.6, A5c in §6.8) |
| A C2 FLOW MUST companion for each concrete MUST primary | Makes C5 equal to the C2 image again (R10), but adds starts: a new companion form (more MUST machinery) | Not built; the A4 companion (FLOW STAR) had no effect on rows (§6.6) |
| Cut the depth of FLOW MUST hand-off conclusions | A numeric cut of rows | Rejected by the design rules |
| Fix only the native loop cost (group A, P2 and P3) | Does not touch the C5 asymmetry; M1 would still add +125% H4 rows | INFERENCE from §6.5 |

**Withdrawal condition.** Withdraw F1 if one of these occurs:

1. A confirmed or provisional result of a reference project differs
   from the native launch (F1 alone or M1 + F1).
2. The sink route census of a reference project has a native NORMAL
   leaf that no leaf of the F1 arm at the same sink covers.
3. F1 accepts a member in a backward run, or a member deeper than
   `FL(Dc)+1`.
4. Wall time or peak memory of a reference project is worse than native
   (the gate of design-guide.md), for F1 alone or for M1 + F1.

Status: conditions 1 to 3 do not hold (§6.7). Condition 4 holds for M1 +
F1 without H1 (run 6 +55% to +62%; OOM in Conductor run 8 in its one
3,000 s launch, §6.9). For the landing set M1 + F1 + H1, Conductor gets
further in the same time and peak RSS is within 1%, but run 6 is slower,
run 8 goes above the 90% memory threshold, and the Stirling-PDF fast form
takes up to 8% more wall time: this is the price of decision D1 (§14).

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
3. **CURRENT makes FLOW MUST starts from them.** VERIFIED (owner trace
   of `replace`, run 3, `m1trace/v5-r5` against `m1trace/native-r5`).
   Native run 3 has no C2 query of `replace` with a MUST actual. v5 has
   103 C2 queries that start a FLOW MUST premise, at two sites. (a) The
   method entry: a T MUST actual `arg(0).MUST/T` (24 queries) or a FLOW
   MUST actual `arg(0).MUST/FLOW` (20) at an abstract ANY entry one field
   deeper starts `arg(0).X.MUST/FLOW` (the `p.startsWith(q)` row of
   `RestrictedInitialPolicy.emit`: `ANY_TAINT -> result(p, ANY_TAINT,
   d.exclusion)`). (b) The loop header of B2: the actual `var(3).MUST/FLOW`
   starts 11 premises `var(3).X.MUST/FLOW`, one for each alias X that
   has an abstract entry (the same row), and `var(3).MUST/FLOW` itself;
   an actual
   `var(3).X.MUST/FLOW` starts itself (the `q == p` row). M1 changes
   neither row. The aliases X include `Iterator#Element`,
   `Map$Entry#Value`, `Map$Entry#entryData`, `HeaderIterator#headers`,
   `HeaderElementIterator#headerElements` and `StrTokenizer#inputContent`.
4. **C5 gives a FLOW MUST premise only depth-1 DEMAND pieces.** VERIFIED
   (publications, run 3, B2 exit 40; code `canStoreInitial`). The C5
   companion clause accepts a FLOW STAR member under a concrete-mark row
   when its concrete STAR instance is a legal start. So a FLOW STAR
   premise `var(3).X.*/FLOW` also meets the concrete rows of B2, and a
   concrete row with a depth-0 exit (for example `Dc = var(8).MAY/T`,
   `Dp = var(3).$/T`) gives it the depth-0 DEMAND piece
   `var(3).*/FLOW,D`. The clause has no FLOW MUST case: a FLOW MUST
   premise meets only the abstract rows, and their exits are the depth-1
   aliases. Count: 6 of the 7 depth-1 FLOW STAR premises of B2 have a
   depth-0 DEMAND piece; 0 of the 6 depth-1 FLOW MUST premises have one.
   In the store a depth-0 piece covers the depth-1 pieces of the same
   premise. So the H3 row of a FLOW STAR premise has a depth-0 conclusion
   (`var(9).MAY/FLOW => var(3).HeaderIterator#headers.*/FLOW`), and a FLOW
   MUST premise keeps one depth-1 conclusion for each alias
   (`var(9).X.MAY/FLOW => var(3).HeaderIterator#headers.MAY/FLOW`).
5. **A loop-carried FLOW relation over the alias set.** H3 for B2 has
   the rows `var(3).X.MAY/FLOW => var(3).X'.MAY/FLOW`: a FLOW MUST premise
   at `X'` (the hand-off writes MUST as MAY) and its conclusion at `X`
   after one pass: 132 rows, 6 premises and 22 conclusions. Rows of B2
   with a depth-1 FLOW entry at `var(3)`: 121 in v5, 22 in native, 22
   with A5. B2 itself has few H3 rows (304 against 273).
6. **The backward run crosses the alias set two levels deep.** Backward
   run 4 starts each depth-1 FLOW demand one counted field deeper (the
   relative cap). So B2 gets 2-deep STAR FLOW starts `var(3).X.Y.*/FLOW`
   for every pair of aliases. One entry,
   `var(3).Iterator#Element.ImmutablePair#right.MAY/FLOW`, has 351 such
   premises (400 in the second context of the owner). H4 for B2: 16,989
   rows (13,095 with a 2-deep entry) against 3,348 in native.
7. **Run 6 runs out of memory.** H5 has 60,374 rows against 26,083.
   VERIFIED (`m1trace/v5-r7`, the second v5 launch to run 7, OOM in run 6
   again after 7 min). 21 thread dumps in run 6, one every 20 s: the
   runnable analyzer threads are in loop observation
   (`LoopConsumerObservation.observe`, 6), block-summary application
   (`BlockSummaryLinks.deliver`, 6), C2 initials (`DemandStore.initials`,
   4), C5 (`PreparedOutputPrograms.intersect`, 3) and other (5). GC is not
   the cost: 9 s of pauses in 420 s. The heap after GC stays at 5.1 GB
   for 4 minutes and then grows to 7.4 GB before the OOM. Native run 6
   spends its time on the same loop paths (§6.2). The intervention test is
   rule F1 (§3.8): it gives the FLOW MUST premises the companion clause,
   and with it H5 and run 6 come back near native (§6.7).

So M1's own row (M1.1) does not make the cost. CURRENT's FLOW MUST rows,
the missing FLOW MUST case of the C5 companion clause and the backward
relative cap make it, on more MUST facts. The CURRENT cut of §2.3 step 4
is a cost control as well as the maker of the OWASP cycle.

### 6.6 Ablations of the Conductor cost

Each ablation is a diagnostic flag on `proto/mp5-20261127` (worktree
`wt-v4`; F1 at `8c70ee97e`, worktree `wt-v5`). Conductor to run 5 with the hand-off dump, one launch per arm,
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
| v5 + F1 | rule F1 (§3.8): the C5 companion clause also takes a FLOW MUST member | 23,489 | 34,401 | 37,139 | 14,655 | 284 s |
| native + F1 | F1 without M1 | 18,545 | 31,043 | 27,004 | 14,477 | 301 s |

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
- **F1 removes the loop cost** (gate queue 19, `f1/`). With F1, M1 adds
  +1.3% H4 rows in `replace` (14,655 against 14,464) instead of +206%,
  and +11% H4 rows in total instead of +125%. F1 alone is near native
  (H4 +0.3%, H5 +3.5%). The F1 arms are the intervention test of §6.5
  steps 4 to 7. The rest of the H5 excess of v5 + F1 (+42%) is in other
  owners (§6.7).

### 6.7 Gate of F1 and of M1 + F1 (gate queues 19 to 29)

Build `8c70ee97e` (`proto/mp5-20261127`, worktree `wt-v5`). Arms: `f1` =
F1 alone (`mustFlowC5`); `mpf1` = M1 v5 + F1 (`mustProbe`,
`mustFlowC5`); `mpf1hs` = M1 v5 + F1 + H1 (`protoHandoffSubsume`), the
landing set. Each launch runs alone under the project lock. The machine
is shared: from about 10:25 other users' jobs raised the load to 20-24 on
20 cores. The run-1 engine time is the load control of each launch
(Conductor 23 s, Stirling-PDF 24 s, OWASP 1m 22s when the machine is
quiet); a launch with a high control is used for results, not for time.
SARIF: `compare_sarif.py`. Routes: the sink route census (§3.4) against
the native census of the same form. VERIFIED (`f1/`, `gate-queue19.log`
to `gate-queue29.log`).

**OWASP** (native reference `gate/OWASP-native-1`, routes
`owasp/routes-native`):

| Arm | Launch | End | Confirmed / provisional | SARIF | Routes (native 5,356 leaves) | Wall | Peak RSS | H5 / H6 / H7 |
| --- | --- | --- | --- | --- | --- | ---: | ---: | --- |
| native | 1 | RUN_LIMIT, run 11 | 2,633 / 0 | - | - | 215 s | 9.27 GB | 53 / 109 / 63 |
| f1 | 1 | RUN_LIMIT, run 11 | 2,633 / 0 | same results and flows | 5,386: every native leaf, 30 more | 215 s | 9.30 GB | 108 / 228 / 157 (a native order form, §6.2) |
| mpf1 | 1 | **NO_DEMAND_EDGE, run 7** | 2,633 / 0 | same results and flows | not censused | 213 s | 9.36 GB | 18 / 31 / 0 |
| mpf1 | 2 | **NO_DEMAND_EDGE, run 7** | 2,633 / 0 | same results and flows | 5,330: the 26 native-only leaves are covered (as M1 alone, §3.4) | 217 s | 9.27 GB | 18 / 31 / 0 |
| mpf1hs | 1 | **NO_DEMAND_EDGE, run 7** | 2,633 / 0 | same results and flows | 5,330, as mpf1 2 | 285 s (load: run 1 1m 36s) | 9.36 GB | 18 / 31 / 0 |
| mpf1hs | 2 (queue 38) | **NO_DEMAND_EDGE, run 7** | 2,633 / 0 | same results and flows | not censused | 215 s (run 1 1m 25s) | 9.31 GB | 18 / 31 / 0 |

OWASP time: the engine time of runs 2 to 7 is 37.3 s to 38.0 s in the
quiet M1 + F1 and landing-set launches against 37.4 s native, and
native's runs 8 to 11 take 0.3 s. So the OWASP cycle costs the end
status (run limit), not time, and the fix neither saves nor costs time
on OWASP.

**Stirling-PDF** (native fast launches `gate5/Stirling-PDF-native-1`,
`-2`; native slow launch `-3`; each arm is compared with the native
launch of the same form):

| Arm | Launches | Form (run 7) | End | Confirmed / provisional | SARIF | Routes (126) | Wall | Peak RSS |
| --- | --- | --- | --- | --- | --- | --- | ---: | ---: |
| native | 3 | fast 2 (1.4 s), slow 1 (11.5 s) | RUN_LIMIT 11 (fast), TIMEOUT in run 11 (slow) | 32 / 2 (fast), 32 / 0 (slow) | - | - | 154-155 s (fast), 1,112 s (slow) | 9.45-9.54 GB |
| f1 | 1 | slow (37 s; load: run 1 32 s) | TIMEOUT in run 11 | 32 / 0 | same as native slow | equal | 1,137 s | 9.43 GB |
| mpf1 | 3 | slow 3 (25 s, 12 s, 14 s) | TIMEOUT in run 11 | 32 / 0 | same as native slow | equal | 1,112-1,120 s | 9.13-9.55 GB |
| mpf1hs | 5 (4 and 5: queue 38) | **fast 5** (3.3 s, 2.2 s, 1.7 s, 1.4 s, 2.1 s) | RUN_LIMIT 11 | 32 / 2 | same as native fast | equal (launches 1-3) | 158-258 s; 158, 166, 167 s in the 3 launches with a quiet control | 9.38-9.54 GB |

- M1 + F1 stops the OWASP cycle in 4 of 4 launches (with or without H1)
  with the results and routes of M1 alone. F1 alone does not stop it (F1 is the cost rule).
- Neither M1 nor F1 changes the Stirling-PDF form or its results: the
  form stays order-dependent (§4). With H1 (the landing set) the form is
  fast in 5 of 5 launches, as in §5.2.
- Stirling-PDF time in the fast form, the 3 landing-set launches with a
  quiet control (run 1 23.4 s to 24.9 s): the sum of the engine times is
  89.1 s, 96.3 s and 99.5 s against 89.2 s and 89.4 s for native fast;
  wall 158 to 167 s against 154 to 155 s (+2% to +8%). The extra time is
  in runs 6 to 11 (46.0 s and 47.2 s against 39.5 s to 39.8 s) of 2 of
  the 3 launches. The load in runs 6 to 11 was about the same in these 3
  launches (12.4 to 13.3). The hand-offs H3 to H8 have 0.6% to 9% fewer
  rows than native fast, and H9 to H11 are within 3%. H1 alone has wall 154 s (`gate5/Stirling-PDF-hs-1`).
  The cause of the 2 slower launches is not traced (§10). Against the
  native slow form (1,112 s, 1 of 3 native launches) the landing set
  saves about 950 s.
- The 2 provisional entries of the fast form are the native fast-form
  entries; the slow form loses them at the timeout in every arm (§6.3).

**Conductor** (native reference `gate/conductor-native-1`; the f1prof
pair `f1prof/conductor-{native,mpf1}-r7` stops after run 7). Per-run
times are engine times (`BIDI_RUN_END`); "to the end of run 7" is the
sum of the engine times of runs 1 to 7:

| Arm | Launch | Run 1 (load control) | End | Confirmed / provisional | SARIF | Wall | Peak RSS | H4 | H5 | H6 | H7 | Run 4 | Run 6 | To the end of run 7 |
| --- | --- | ---: | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| native | 1 | 23.6 s | TIMEOUT in run 8 | 7 / 0 | - | 1,129 s | 9.73 GB | 29,920 | 25,236 | 149,889 | 85,380 | 1m 56s | 6m 24s | 655 s |
| native | f1prof r7 | 23.7 s | run limit 7 | 7 / 0 | - | - | - | - | - | - | - | 1m 57s | 6m 25s | 659 s |
| f1 | 1 | 42 s (loaded) | TIMEOUT in run 6 | 7 / 0 | same results and flows | 1,165 s | 9.44 GB | 29,926 | 25,066 | - | - | 4m 16s | - | - |
| mpf1 | 1 | 23.0 s | TIMEOUT in run 8 | 7 / 0 | same results and flows | 1,128 s | 9.47 GB | 32,688 | 33,625 | 123,933 | 53,029 | 1m 26s | **9m 56s** | **831 s** |
| mpf1 | f1prof r7 | 23.6 s | run limit 7 | 7 / 0 | - | - | - | 32,919 | 33,718 | 129,023 | 56,101 | 1m 27s | **10m 21s** | **859 s** |
| mpf1 | 2 | 32.6 s (loaded) | TIMEOUT in run 6 | 7 / 0 | same results and flows | 1,146 s | 9.43 GB | 31,813 | 33,273 | - | - | 1m 57s | - | - |
| mpf1hs | 1 | 27 s (loaded: run 2 62 s against 46 s) | TIMEOUT in run 6 | 7 / 0 | same results and flows | 1,142 s | 9.51 GB | 31,242 | 31,502 | - | - | 1m 36s | - | - |

- M1 + F1 has no OOM on Conductor (M1 alone: OOM in run 6 in 2 of 2
  launches). The results are equal in every launch. Peak RSS is lower
  (9.47 GB against 9.73 GB).
- H6 is 14-17% smaller and H7 34-38% smaller than native, and run 7 is
  faster (43-45 s against 66-69 s).
- **Run 6 is 55-62% slower** in the two launches with a quiet run-1
  control, and the time to the end of run 7 is 27-30% longer. The two
  launches agree within 5%. The root cause is in §6.8.
- At the 1,080 s timeout both arms end in run 8 with the same results, so
  the wall time is equal by construction. §6.9 has the launches with a
  3,000 s timeout.

**Suites** (`f1/fixtures-*`, `f1/unit-*`, `f1/rule-*`):

| Suite | f1 | mpf1 |
| --- | --- | --- |
| cycle fixtures (38 tests) | 0 failed | 7 failed: the 7 of M1 alone (§6.1); the report entries are byte-equal to M1 alone |
| dataflow module (2,807 tests) | 0 failed | 10 failed: the 10 of M1 v4 (§6.1: C2 table rows and native-cycle diagnostics) |
| jvm module | 0 failed | 0 failed |
| rule suite (bidirectional, 808 tests) | pass: 786 success, 0 false negatives, 0 false positives, 22 disabled; the same entries as the landing baseline | pass: the same as f1 |

F1 adds no test failure. The M1 failures are the classified set of §6.1.

### 6.8 Root cause of the remaining run-6 cost of M1 + F1 on Conductor

The chain goes backward in time, from the cost in run 6 to its start in
run 3. Each step is VERIFIED. Data: the run-6 owner time and block
counters (`f1prof/conductor-{native,mpf1}-r7-ot`, gate queue 24), the
owner traces of `getTaskInputV2` (`*-r5-gti`, queue 27) and of
`UserDefinedTaskMapper` with its callees (`*-r5-udt`, `*-r5-udt3`,
`mpf1-r5-udt4`, queues 28, 32 and 34), and the hand-off dumps
(`conductor-m1/native-r5b`, `f1/conductor-mpf1-r5`). T is the
path-traversal mark. Every trace is of M1 + F1 without H1. The landing
set M1 + F1 + H1 has no trace; that the same chain makes its run-6 cost
is INFERENCE (§10).

1. **The time is in `ParametersUtils#replace`.** Run-6 owner time: 261 s
   to 411 s (context `arg(0) == HashMap`) and 122 s to 250 s (context
   `[{}]`). Every other owner changes by less than 5 s. In the loop block,
   C2 hits grow x3.3 and x5.2, C5 plan hits x2.5 and x2.9; the external offers to
   the owner change by +7% only. So the extra work is made inside
   `replace` by more premises, not by more callers.
2. **More DEMAND premises of `replace`.** H5 root rows of `replace` in
   the context `[{}]`: 8 to 82. 77 of the new rows have the STAR DEMAND
   premises `arg(0).Map#MapKey.*/T` (59 rows) and `arg(0).Map#MapValue.*/T`
   (18 rows), each with a conclusion `ret.<path>.$/T`. Native has 4 T rows
   in this context, with the MUST premises `arg(0).Map#MapKey` and
   `arg(0).Map#MapValue` (the dump prints MUST as MAY). In the context
   `arg(0) == HashMap` the STAR T rows grow from 120 to 155.
3. **They come from DEMAND starts of `getTaskInputV2` in run 5.** With
   M1 + F1, `getTaskInputV2` starts the DEMAND actuals
   `arg(0).Map#MapKey.*`, `arg(0).Map#MapKey.MUST`,
   `arg(0).Map#MapValue.*` and `arg(0).Map#MapValue.MUST` (layer D)
   that `ParametersUtils#getTaskInput` passes from its own DEMAND
   premises. Native has no such actual: its 12 DEMAND actuals
   `arg(0).*/T,D` (one for each task mapper) are rejected in both arms.
4. **The callers keep DEMAND because their run-5 entries are one field
   shallower.** `UserDefinedTaskMapper#getMappedTasks`, H4:

   ```
   native   arg(0).TaskMapperContext#workflowTask.WorkflowTask#inputParameters.MAY/T => ret...inputData...
   M1 + F1  arg(0).TaskMapperContext#workflowTask.MAY/T                              => ret...inputData...
   ```

   The run-5 C2 queries of the mapper show the effect. Native: one query
   for each field, `{workflowTask.WorkflowTask#X.*/T},D`, and only
   X = `inputParameters` gives starts. M1 + F1: the query
   `{workflowTask.*/T},D` gives the start `workflowTask.*/T,D` (the
   CURRENT cut of a DEMAND actual, M1.2b) next to the M1 start
   `workflowTask.MUST/T,N`. So the whole object is DEMAND, and the DEMAND
   goes on to the parameter utilities.
5. **The shallow entry is a raw backward exit of run 4.** C5 input of the
   mapper, run 4, under the three `inputData` premises: M1 + F1 has the
   DEMAND exit `arg(0).workflowTask.MAY/T`. C5 keeps it: the H3 premise is
   the M1 start `workflowTask.MUST/T`, and `q == p` gives the meet. Native
   has only deep exits: `workflowTask.inputParameters.Map#MapKey.MAY/T`
   and `workflowTask.inputParameters.Map#MapValue.MAY/T`.
6. **The shallow exit is an answer of `getWorkflowTask`.** The mapper
   reads `workflowTask = taskMapperContext.getWorkflowTask()`
   (`UserDefinedTaskMapper.java:71`). Answers of the getter at
   `this.workflowTask` with the mark T and layer D, run 4 (owner trace
   `*-r5-udt3`; lines counted, P = a provisional answer):

   | Result | M1 + F1 | native |
   | --- | ---: | ---: |
   | deep, saved record: `this.workflowTask.inputParameters.MAY/T,D` (native: `...inputParameters.Map#MapKey.MAY/T,D` and `...Map#MapValue.MAY/T,D`) | 6 | 7 |
   | deep, read view: the same results | 6 | 7 |
   | shallow, read view: `this.workflowTask.MAY/T,D` | **8** | 0 |
   | shallow, read view, mark `FLOW\xss,T`: `this.workflowTask.MAY/...,D` | **25** | 0 |

   Each of the 8 shallow T answers comes from the view
   `ret.WorkflowTask#inputParameters.*/FLOW -> this.workflowTask.MAY/FLOW,D`,
   which is the read view of the FLOW MUST record (step 7).

   In the store an `[any]` fact at `workflowTask` covers the `[any]` facts
   below it, so only the shallow exit is left at the method entry.
7. **A MUST record answers at its premise path.** A must-premise starts
   end-exact (ap.md §6.5): each of its edges relates every continuation
   of the premise to every continuation of the conclusion. So the record
   of `this.workflowTask.MUST/FLOW` cannot tell that the getter returns
   the field itself, and its read view answers at `this.workflowTask`. A
   FLOW STAR premise starts with the identity, its edges keep the path,
   and its answer goes one field deeper. This deeper answer is the native
   step that moves the mapper entry from depth 1 (H2) to depth 2 (H4).
8. **The FLOW MUST premise of the getter comes from M1.** Run-3 offers of
   the mapper to `getWorkflowTask`: with M1 + F1 the mapper makes 4 MUST
   offers: `this.workflowTask.MUST/T,N` and `this.workflowTask.MUST/sqli,N`
   (M1 starts), `this.workflowTask.MUST/FLOW,N` (their FLOW companion) and
   `this.taskDefinition.MUST/FLOW,N`. Each offer at `workflowTask` gives
   the start `this.workflowTask.MUST/FLOW,N` (the CURRENT C2 row for a
   MUST actual at an abstract entry, §6.5 step 3). Native offers no MUST
   fact (0 offers): CURRENT cuts the actual at the mapper entry to
   `workflowTask.*/T,D`, whose FLOW companion `workflowTask.*/FLOW,N`
   gives only the FLOW STAR start.
9. **The same shape one call later.** `getTaskInputV2(...,
   taskDefinition)` gets a FLOW MUST premise at `arg(3)` (H3
   `ret.MAY/FLOW => arg(3).MAY/FLOW`, native: only `arg(3).*/FLOW`). Its
   36 H4 rows at `arg(3)` have the premise `arg(3).MAY/FLOW` where the 36
   native rows have `arg(3).TaskDef#inputTemplate.MAY/FLOW`. In run 4 it
   answers the mapper with the shallow `arg(3).MAY/T,D` 7 times (native:
   `arg(3).TaskDef#inputTemplate.MAY/T,D`, 3 times). C5 drops this exit
   (no H3 premise at `taskDefinition`), so it does not change the entry.

This also explains the ablations of §6.6. The T MUST actual alone gives
the FLOW MUST start of step 8, so keeping a FLOW STAR companion (A4)
does not remove it. A5 replaces exactly this C2 row (a FLOW STAR start
for a MUST actual at an abstract entry), so A5 removes both the loop
cost (§6.5) and the depth cost (this section); but A5 costs +49% rows
without M1 (§6.6). F1 removes only the loop cost.

So the remaining cost has the same origin as the cost of M1 alone
(§6.5): M1 lets NORMAL MUST facts into blocks and callees, where CURRENT
kept them out. F1 removed the loop part (the FLOW MUST premises inside
`replace` now take the companion pieces). The part that remains is the
**depth** of the backward exits: a MUST premise has end-exact edges, so a
backward run cannot find out which field of a MUST premise the method
reads. The run-4 exits stay at the depth of the MUST start, the run-5
entries stay one field shallower than native, and a shallower entry
admits more DEMAND actuals. Native deepens because its premises at the
same sites are STAR.

**Intervention test: ablation A5c** (gate queue 35, `a5c/conductor-mpf1a5c-r7`,
build `c9e4fdeeb` on `proto/mpf1-diag-20261127`, flag
`concreteMustFlowStar`). A5c is A5 restricted to a concrete-mark actual:
a concrete MUST actual at an abstract ANY entry gives the FLOW STAR
start, and a FLOW MUST actual keeps the FLOW MUST start. One launch, M1 +
F1 + A5c, Conductor to run 7, run-1 control 25.3 s:

| | native | M1 + F1 | M1 + F1 + A5c |
| --- | ---: | ---: | ---: |
| MUST offers of the mapper to `getWorkflowTask`, run 3 | 0 | 4 | 0 |
| shallow answers `this.workflowTask.MAY/T,D`, run 4 | 0 | 8 | 0 |
| H3 | 17,454-17,470 | 20,668-20,757 | 19,692 |
| H4 | 29,918-29,920 | 31,813-33,351 | **44,875** |
| H5 | 25,172-25,236 | 33,273-34,064 | 32,104 |
| Run 4 (mean load in the run) | 1m 56s-1m 57s (10.7) | 1m 27s (12.3-14.0) | **3m 41s** (11.8) |
| Run 6 (mean load in the run) | 6m 24s (7.5) | 9m 56s-10m 21s (8.5-9.0); no end in 12m 19s (14.3) | no end in 11m 37s (13.9) |

(Native: `gate/conductor-native-1`, `f1prof/conductor-native-r7`. M1 + F1
rows: `f1/conductor-mpf1-1`, `-2`, `f1prof/conductor-mpf1-r7`, `-r7-ot`;
M1 + F1 run times: the launches without the `replace` owner trace,
`mpf1-1` and `mpf1-r7`, and for the loaded run 6 `mpf1-2`. The A5c
launch has a small owner trace of `getWorkflowTask`. The load is the
mean 1-minute load average in the run.)

A5c removes the cause at the traced site: the mapper has no MUST fact at
`workflowTask`, and the getter answers only below `inputParameters`
(VERIFIED, owner trace). But the FLOW STAR premises that replace the FLOW
MUST premises keep the path and make more rows (H4 +35% to +41% against
M1 + F1), and run 4 takes 2.5 times as long at a similar load. Run 6
does not separate the arms: A5c ran it at a mean load of 13.9 and did
not end it in 11m 37s, and M1 + F1 at a load of 14.3 did not end it in
12m 19s. This is the trade-off of A5 (§6.6) again. A FLOW
MUST premise is the compact form (one relation for the whole subtree);
its price is the shallow backward answer. A FLOW STAR premise is the
precise form; its price is one row for each path. Neither start form
removes the cost. A5c is rejected.

Other alternatives for the depth cost:

| Alternative | Result | Status |
| --- | --- | --- |
| A5c (above) | worse than M1 + F1 | VERIFIED, rejected |
| A must-premise that keeps the path (a precise MUST record) | changes the end-exact law of ap.md §6.5 and every MUST record; a new MUST form | not built (more MUST machinery) |
| Drop a backward exit at the path of its own NORMAL MUST premise | the next run loses the entry of that route when no deeper answer exists (serve every route) | rejected by the design rules |
| Cut the exit depth by a number | a numeric cut | rejected by the design rules |

H6 and H7 are 14% to 38% smaller with M1 + F1 (§6.7). Which owners make
that difference is not measured (§10).

### 6.9 Conductor with a 3,000 s timeout (gate queues 33, 36 and 37)

Native Conductor never ends in 1,080 s (§6.7), so the wall time at the
1,080 s timeout is equal by construction. These launches give each arm
3,000 s of analysis time, one launch at a time under the project lock.
Build `8c70ee97e` (`wt-v5`). Arms: native (2 launches), the landing set
M1 + F1 + H1 (3 launches) and M1 + F1 without H1 (1 launch). Times are
engine times (`BIDI_RUN_END`); the number in brackets is the sum of the
engine times of runs 1 to N in seconds (the hand-off time between runs
is not counted). Rows are `BIDI_HANDOFF_COMPACTION rows=`. Heap after
GC is from the GC log (G1 Young and Full pauses only). The memory
manager (`MemoryManager.kt`) acts when the heap after a GC is above 90%
of the 8 GB heap: it clears the soft references of the engine caches
and asks for a Full GC; when the heap stays above 90% it stops the
analysis (OOM). The load is the 1-minute load average, sampled each
second by the launcher; it includes the analyzer's own threads.
VERIFIED (`f1long/`, `gate-queue33.log`, `gate-queue36.log`,
`gate-queue37.log`, `scripts/longtable.py`, `scripts/gcruns.py`).

| Run | native 1 | native 2 | landing set 1 | landing set 2 | landing set 3 | M1 + F1 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 25.3 s (load control) | 28.7 s (load control) | 23.1 s (load control) | 25.2 s (load control) | 24.6 s (load control) | 25.6 s (load control) |
| 2 | 50.8 s (76) | 55.5 s (84) | 46.3 s (69) | 50.1 s (75) | 49.6 s (74) | 50.5 s (76) |
| 3 | 10.1 s (86) | 11.6 s (96) | 14.0 s (83) | 15.0 s (90) | 15.3 s (89) | 14.5 s (91) |
| 4 | 2m 8s (214) | 2m 14s (230) | 1m 20s (164) | 1m 35s (185) | 1m 24s (173) | 1m 32s (182) |
| 5 | 9.5 s (224) | 10.4 s (241) | 20.8 s (185) | 24.7 s (210) | 20.1 s (194) | 20.5 s (203) |
| 6 | 7m 9s (653) | 7m 26s (687) | 7m 56s (661) | 9m 21s (770) | 9m 26s (760) | 11m 17s (880) |
| 7 | 1m 16s (728) | 1m 10s (757) | 41.1 s (702) | 46.0 s (816) | 40.9 s (801) | 48.8 s (929) |
| 8 | **no end in 37m 0s** | **no end in 36m 20s** | 29m 43s (2,485) | 32m 15s (2,751) | **no end in 35m 43s** | **OOM after 24m 56s** |
| 9 | - | - | 1m 59s (2,604) | 2m 21s (2,892) | - | - |
| 10 | - | - | **no end in 5m 38s** | **no end in 49.6 s** | - | - |
| End | TIMEOUT in run 8 | TIMEOUT in run 8 | TIMEOUT in run 10 | TIMEOUT in run 10 | TIMEOUT in run 8 | OOM in run 8 |
| Confirmed / provisional | 7 / 0 | 7 / 0 | 7 / 0 | 7 / 0 | 7 / 0 | 7 / 0 |
| SARIF against `gate/conductor-native-1` | byte-identical | byte-identical | same results and flows | same results and flows | same results and flows | same results and flows |
| Wall | 3,055 s | 3,058 s | 3,049 s | 3,053 s | 3,055 s | 2,536 s |
| Peak RSS | 9.54 GB | 9.48 GB | 9.48 GB | 9.59 GB | 9.40 GB | 9.64 GB |
| Run 8: max heap after a Young or Full GC (8 GB heap) | 7.01 GB, 0 Full GC | 6.13 GB, 0 Full GC | 7.20 GB, 1 Full GC | 7.21 GB, 1 Full GC | 7.21 GB, 1 Full GC | 7.22 GB, 4 Full GC |
| Run 8: heap above 90% after a GC (memory-manager events) | 0 | 0 | 1 (soft references cleared: 6,752) | 1 (soft references cleared: 6,524) | 1 (soft references cleared: 6,750) | 6 (soft references cleared: 493) |
| Run 8: mean 1-minute load (20 cores) | 11.0 (max 17) | 15.5 (max 63) | 9.5 (max 13) | 10.4 (max 16) | 21.0 (max 70) | 10.3 (max 16) |

| Hand-off | native 1 | native 2 | landing set 1 | landing set 2 | landing set 3 | M1 + F1 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| H3 | 17,511 | 17,511 | 20,623 | 20,417 | 20,596 | 20,691 |
| H4 | 29,921 | 29,909 | 31,605 | 30,938 | 31,100 | 32,602 |
| H5 | 25,063 | 25,087 | 32,373 | 31,411 | 31,579 | 33,212 |
| H6 | 149,480 | 149,950 | 118,234 | 121,035 | 119,806 | 128,705 |
| H7 | 85,043 | 86,521 | 50,373 | 51,418 | 50,344 | 55,614 |
| H8 | - | - | 309,915 | 311,727 | - | - |
| H9 | - | - | 100,999 | 101,351 | - | - |

- **Where run 8 ends.** Native ends run 8 in 0 of 2 launches, the landing
  set in 2 of 3. Landing sets 1 and 2 end run 8 in 29m 43s and 32m 15s,
  end run 9 in about 2 minutes, and stop in run 10. Run 8 starts from H7,
  which is 40% to 42% smaller with the landing set.
- **Load in run 8.** Native 1, landing sets 1 and 2, and M1 + F1 ran run
  8 at a mean load of 9.5 to 11.0. Native 2 had a load spike from 3 to 9
  minutes into run 8 (mean 52 for 3 minutes), then a load of 10 to 12 for
  27 minutes; it did not end run 8 in 36m 20s. Landing set 3 ran at a
  load of 8 to 10 for the first 21 minutes of run 8, then at 18 to 57 to
  the timeout, before the time at which landing sets 1 and 2 ended run 8.
  That this spike stopped landing set 3 is INFERENCE.
- **Memory.** No landing-set launch runs out of memory (3 of 3). In every
  launch of every arm the heap goes above 90% twice in run 2, and the
  memory manager clears about 84,700 soft references. In run 8 each
  landing-set launch goes above 90% once more, 20 to 22 minutes into the
  run: the manager clears 6,524 to 6,752 soft references, and the heap
  after the Full GC is 7.20 to 7.21 GB. Native does not go above 90% in
  37 minutes of run 8 (at most 7.01 GB after a GC). Peak RSS is 9.40 to
  9.59 GB against 9.48 to 9.54 GB.
- **M1 + F1 without H1 runs out of memory in run 8** (one launch, load
  10.3). About 25 minutes into run 8 the heap goes above 90% with only
  493 soft references left to clear; it goes above 90% 5 more times in
  11 seconds, and the memory manager stops the analysis. Its H6 and H7
  are 6% to 11% larger than in the landing set, and its run 6 takes 11m
  17s. Why H1 makes this difference is not traced (§10).
- **Results.** 7 confirmed, 0 provisional in every launch. The SARIF of
  each landing-set launch and of M1 + F1 has the same results and the same
  results with code flows as native.
- **Before run 8 the landing set is slower.** Run 6 takes 7m 56s to 9m
  26s, against 7m 9s and 7m 26s here and 6m 24s in the quiet native
  launches of §6.7. Paired by the mean load in run 6: landing set 1 (load
  8.6) against the quiet native (7.5) is +24%; landing sets 2 and 3 (10.7
  and 10.3) are +26% to +32% against native 1 and 2 (11.9), and +46% to
  +47% against the quiet native. So the run-6 price is +24% to +47%, and
  +24% to +32% for the pairs with the nearest load. The sum of the engine
  times to the end of run 7 is 702 s to 816 s against 728 s and 757 s
  here (655 s and 659 s in the quiet native launches of §6.7). Runs 4 and
  7 are faster, runs 3, 5 and 6 slower.

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
  rows of C2, the C5 companion clause and the backward relative cap
  (§6.5). F1 removes the loop part of this cost (§3.8). The depth part
  stays: a FLOW MUST record answers at its premise path (§6.8).

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

### 7.3 F1

| | CURRENT | NEW |
| --- | --- | --- |
| Changed: C5 acceptance (`canStoreInitial`) of a FLOW MUST member with no excluded mark under a concrete-mark ANY row, when its concrete MUST instance is a legal start under the row | not accepted | accepted (the instance law of §3.8) |
| Unchanged | C2 (F1 adds no start), the FLOW STAR clause, abstract-mark rows, the backward run, the relative cap, K, the stores, the hand-off, report building | same |

Affected invariants and proofs: C5 keeps every CURRENT piece
(`FlowMustCompanion.f1_keeps`), so no route that CURRENT serves is lost
by F1. The statement "C5 keys are the complete C2 image" (comment of
`canStoreInitial`) becomes the instance law: for a FLOW member, C5
accepts it when its concrete instance is in the C2 image of the row
(R10). For FLOW STAR both statements are the same.

Hidden changes (checked):

- **Store form.** A FLOW MUST premise gets more pieces. A depth-0 piece
  covers its depth-1 pieces in the store (measured, §6.5 step 4), so the
  hand-off has fewer and shallower rows for it. A piece that no existing
  piece covers is new work (reviewer R14).
- **Conclusion shape and layer at the caller.** The conclusion of a FLOW
  MUST premise under a concrete EXACT exit becomes `$`/E and then FLOW
  `*`/E (`FlowSummaryNormalization`), and it is NORMAL. CURRENT does the
  same for a FLOW STAR premise (R11, R12).
- **Empty-replay skipping.** `skipEmptyDataReplay` finds fewer empty
  plans when F1 accepts more rows. This is cost, measured in §6.7.

## 8. Proof scope and model/production differences

Lean modules (constructive: only `propext` and `Quot.sound`, see the
`#print axioms` lines):

- `spec/lean/ApSpec/MustStartFit.lean` (M1): `new_eq_cur_off`,
  `cur_on_rows`, `new_eq_spec`, `new_contract`, `cur_start_demand`,
  `new_start_normal`, `new_start_is_actual`, `new_start_covers_iff`,
  `new_depth`, and 7 `decide` vectors (the OWASP rows: MUST fits, MUST
  cut, EXACT, MAY, uncounted accessor).
- `spec/lean/ApSpec/MustStartFit.lean`, section 6 (M1 v5): `v5_normal_eq_v4`
  (on a NORMAL actual v5 is v4, so every M1 theorem above holds) and
  `v5_demand_eq_cur` (on a DEMAND actual v5 is CURRENT), and 2 `decide`
  vectors.
- `spec/lean/ApSpec/FlowMustCompanion.lean` (F1): `new_of_cur` (F1 only
  adds acceptance), `new_eq_cur_off` (the only changed row is a FLOW MUST
  member), `new_eq_cur_abs_entry` (abstract-mark rows unchanged),
  `cur_row_false` and `new_row` (on the F1 row CURRENT rejects and F1
  accepts exactly when the concrete instance is a legal start),
  `uniform` (one law for STAR and MUST), `native_equal_path` (without M1
  only members at the entry path change), `cap_stays` (an added member
  below the entry has exactly `FL(Dc)+1` counted fields),
  `admitted_mono` and `f1_keeps` (C5 keeps every CURRENT piece), and 8
  `decide` vectors (the Conductor B2 row: FLOW STAR and FLOW MUST members
  with and without M1, the equal-path member, a member beyond the cap,
  an abstract entry).
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
| D10 | M1: the v4 model has no layer | v5 starts only a NORMAL actual (M1.2b) | Closed: `MustStartFit` section 6 models the v5 guard (`v5_normal_eq_v4`, `v5_demand_eq_cur`). |
| D11 | F1: empty exclusions | a FLOW MUST member is accepted with any `E`; the STAR clause needs an empty `E` (as C2: a MUST start keeps the actual's `E`) | Not proved for a non-empty `E`. The concrete instance keeps the member's `E`, and `canEmitInitial` accepts it with any `E` on the M1 and equal-path rows. |
| D12 | F1: no mark groups, no `insideDemand` | `boundMark`, `isGroup` (a group entry mark is rejected for both tails), `insideDemand` (prefix and exclusion test) | The same checks run for both tails; with empty exclusions `insideDemand` is the prefix test of `canEmit`. |
| D13 | F1: the model is the acceptance test | production also restricts each accepted pair (`restrictConclusionOnly`), limits it to the exit depth and merges it into the store | The cost effect (a depth-0 piece covers depth-1 pieces) is measured (§6.5, §6.7), not proved. |
| D14 | F1: forward only | `legalInitial` rejects ANY_TAINT in a backward run | So neither the primary nor the F1 clause accepts a MUST member backward (reviewer attack 2, refuted). |

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
| R9 | (Found by the gate, not by the reviewer.) M1 removes the cut that keeps NORMAL MUST facts out of blocks and callees; CURRENT's FLOW MUST start rows then multiply them in loops. | **CONFIRMED** (Conductor, §6.5, §6.6) | M1 alone is not WI. Rule F1 removes the loop cost (§3.8, §6.6). |
| R10 | (F1 reviewer, a second read-only review of the F1 code.) F1 has no C2 counterpart: C2 never starts a FLOW MUST member under a concrete entry (`emitAdmissions` adds only the FLOW STAR and root FLOW EXACT companions), so C5 is no longer the complete C2 image. | **CONFIRMED** (code) | F1 is the instance law (§3.8): a FLOW member is accepted under a concrete row when its concrete instance is a legal start. For FLOW STAR this equals the C2 image. C5 wider than C2 keeps more pieces, never fewer (`f1_keeps`). The alternative (a C2 FLOW MUST companion) adds starts and a new companion form (§3.8). Spec change: §7.3. |
| R11 | A FLOW MUST conclusion under a concrete EXACT exit becomes `$`/E, then FLOW `*`/E: wider than the concrete `$`; and an abstract conclusion is kept whole under a concrete exit. | **CONFIRMED** (code: `meetConclusion`, `FlowSummaryNormalization`) | CURRENT does both for FLOW STAR premises. F1 adds no new shape. |
| R12 | F1 publishes NORMAL FLOW conclusions under rows where the concrete instance would be DEMAND (a DEMAND actual gets a DEMAND STAR start in v5). | **CONFIRMED** (code) | The FLOW STAR companion is NORMAL next to a DEMAND concrete STAR primary in CURRENT too (`emitAdmissions`). A FLOW relation is NORMAL; the layer comes from the concrete fact that applies it. |
| R13 | The STAR clause needs an empty `E`; F1 accepts a MUST member with any `E`. The Lean model assumes empty exclusions. | **CONFIRMED** | The same as C2 (a MUST start keeps `E`). Model difference D11. |
| R14 | F1 can change results (more admitted conclusions) and can add work (a new piece when no existing piece covers it). | **PLAUSIBLE** | Measured: §6.7 (results, routes, rows, time). Withdrawal conditions 1 and 4 of F1. |
| R15 | The test oracle (`SelectedDemandReference.stores`) mirrors only the STAR clause, and no test sets the F1 flag. | **CONFIRMED** | Landing: add the F1 row to the oracle and a table test with the Lean vectors of `FlowMustCompanion`. The suites with the flag on are in §6.7. |
| R16 | M1 drops the FLOW STAR companion below the entry, and F1 restores nothing where no abstract row exists: a route can still be lost with M1 + F1. | **PLAUSIBLE** | Route census with M1 + F1 (§6.7). F1 only adds pieces (`f1_keeps`), so a loss can come only from M1, whose census is §3.4. |
| R17 | (Found by the 3,000 s gate.) The Conductor gain of the landing set comes from H1, not from M1 + F1. | **CONFIRMED in part** | M1 + F1 without H1 runs out of memory in run 8 (§6.9), and H1 alone ends in run 8 like native at 1,080 s (§11.1; no 3,000 s launch of H1 alone). So the gain needs all three rules, and the share of each rule is not measured. M1 + F1 lands only with H1 (D1). |
| R18 | (Found by the 3,000 s gate.) A gate in equal time measures progress, not the time to a common state, and the landing set is slower before run 8. | **CONFIRMED** | Run 6 is +24% to +47% and the sum of the engine times to the end of run 7 is 702 s to 816 s against 728 s and 757 s (§6.9). The first common state after run 7 is the end of run 8: the landing set reaches it in 30 to 32 minutes of run 8 (2 of 3 launches); native does not reach it in 37 minutes (native 1, normal load) or 36 minutes (native 2, a 6-minute load spike). This is the price of D1. |
| R19 | (Found by the 3,000 s gate.) The landing set runs Conductor run 8 near the heap limit; another launch can run out of memory, as M1 + F1 without H1 did. | **PLAUSIBLE** | 3 of 3 landing-set launches end without OOM, but each goes above the 90% threshold of the memory manager once in run 8 and continues only because the manager clears about 6,500 soft references (§6.9). M1 + F1 without H1 had 493 soft references left at that point and stopped. Native does not go above 90% in 37 minutes of run 8. The cost source in run 8 is not traced (§10). |
| - | F1 acts in a backward run or on the run-2 rows; F1 exceeds `FL(Dc)+1` or K; F1 changes C2, the target rows or the control rows; the prepared and the native C5 paths disagree (both call `canStoreInitial`) | **REFUTED** (code) | - |
| - | M1 exceeds the cap; M1 at a STATIC anchor; M1 makes a NORMAL start from a DEMAND actual (a DEMAND actual gives a DEMAND start, `AdmittedInitial`); M1 in a backward run; `canEmitInitial` and `emit` disagree; M1 claims a mark the actual lacks; the H1 coverage relation is wrong for exclusions, STAR, MUST, protection; a row removed by a later-reduced row is not covered; H1 changes stores, records or targets | **REFUTED** (code) | - |

## 10. Blind spots

- **ThingsBoard.** Run 1 goes out of memory. M1 acts only in restricted
  forward runs (run 3 and later), and H1 only at a hand-off. Neither
  rule can act on ThingsBoard.
- **M1 on other projects.** M1 fires on all three projects: OWASP 28 to
  54 (run 5), Stirling-PDF 18 to 160 per forward run, Conductor 5,665
  (run 3, v5). The cost shows only on Conductor.
- **Start site of §6.5 step 3.** Closed: the owner trace of `replace`
  shows the C2 queries (§6.5 step 3).
- **One mapper traced (§6.8).** Steps 4 to 9 trace
  `UserDefinedTaskMapper`. The other 11 task mappers and
  `ParametersUtils#getTaskInput` are not traced one by one; step 3 shows
  their DEMAND actuals at `getTaskInputV2`.
- **H6 and H7 with M1 + F1.** They are 14% to 38% smaller (§6.7); the
  owners that make the difference are not measured.
- **F1 volume.** Landed code has no counters, and the proto branch has
  none for F1. The F1 effect is measured by rows, owner time and time
  (§6.6, §6.7), not by a firing count.
- **F1 tests.** The test oracle mirrors only the STAR clause, and no
  table test has the F1 row yet (R15). The suites ran with the F1 flag on
  (§6.7).
- **One launch per ablation arm.** The row counts repeat within 2% where
  two arms must be equal (v4 against v5; A1, A2 and A4 against v5).
- **Conductor never completes.** Native times out in run 8 with 1,080 s
  and with 3,000 s; the landing set times out in run 10 with 3,000 s at
  normal load (§6.9). So the Conductor gate compares the run that each arm reaches in
  the same time, the per-run times, rows and the results at the end. No
  arm reaches NO_DEMAND_EDGE on Conductor.
- **A5c: one launch.** Its run 4 (3m 41s against 1m 26s to 1m 41s) and
  its H4 (+35% to +41%) are far outside the spread of the M1 + F1
  launches, so one launch is enough to reject it.
- **H1 share.** Run 6 of M1 + F1 is 9m 56s to 11m 17s without H1 and 7m
  56s to 9m 26s with H1, and without H1 M1 + F1 runs out of memory in run
  8 (§6.7, §6.9). Why H1 makes this difference is not traced, and H1
  alone has no 3,000 s launch (R17).
- **The §6.8 chain is traced without H1.** Every owner trace and
  hand-off dump of §6.8 is of M1 + F1 without H1. That the landing set
  pays its run-6 price by the same chain is INFERENCE.
- **Run 8 is not traced.** The landing-set run 8 (30 to 32 minutes, one
  pass above the 90% memory threshold) has no owner time or heap census.
  Its cost source is not known (R19).
- **Long launches and load.** Conductor with 3,000 s: 2 native, 3 landing
  set, 1 M1 + F1; M1 + F1 without H1 has one launch only. Native 2 and
  landing set 3 had load spikes in run 8 (§6.9).
- **Stirling-PDF fast-form time.** 2 of the 3 quiet landing-set launches
  take 6 to 7 s more in runs 6 to 11 at the same load and about the same
  rows; the third takes the native time. The cause is not traced, and
  native fast has 2 launches only (§6.7).
- **H1 route census.** Done for Stirling-PDF (§6.3: 126 equal routes). Not
  done for OWASP and Conductor; their results are equal.
- **H1 in module suites.** The suites do not log the hand-off lines, so
  that the test JVMs used the H1 flag is INFERENCE (the M1 flag reached
  them by the same mechanism and changed the results).
- **Source of the Stirling order.** Not isolated (§4.2).
- **Machine load.** The machine is shared, and from 10:25 on 27 November
  other jobs kept the load at 14 to 24 on 20 cores. A time claim uses
  only launches whose run-1 engine time (the load control) is the quiet
  value: Conductor 23-24 s, Stirling-PDF 24-25 s, OWASP 1m 22s-1m 27s.
  The two quiet M1 + F1 Conductor launches agree within 5% on run 6.
  Rows, offers and counters do not depend on the load.

## 11. WI classification

| Rule | Improvement | Negative consequence | Verdict |
| --- | --- | --- | --- |
| H1 | Stirling-PDF: the fast form in every H1 launch, including the 3 launches where run 6 made the extra row (§5.2); a slow native launch takes 7x the wall time and loses 2 provisional entries at the timeout (§6.3). Fewer hand-off rows: Conductor H4 to H7 -2% to -9%, Stirling-PDF H7 860 against 876-885, OWASP 13 fewer at H4 (§6.2, §6.3). After H4, OWASP follows one of its order-dependent native forms (H5/H6 = 53/109, 79/165 or 108/242 in native launches); H1 launch 1 had 108/228. | None measured: results equal on all projects, Stirling-PDF SARIF byte-identical and route census equal, suites pass. R1 (an EXACT NORMAL start can go) is the CURRENT store law; it is the same start set as a native fast launch. | **WI.** The spec question of R1 is a user decision (§14, D2). 3 launches per project: §5.2, §6.3, §11.1. |
| M1 alone | OWASP: NO_DEMAND_EDGE in run 7 instead of the run limit, results equal, every route served (§3.4, §6.4). | Conductor: +125% H4 rows, +131% H5 rows, OOM in run 6 in 2 of 2 launches (§6.4). | **Not WI.** |
| F1 alone | None needed: F1 is the cost rule of M1. | None measured: OWASP and Stirling-PDF results and routes equal, Conductor rows within 0.3% to 3.5% (§6.6, §6.7), suites pass. | Lands only with M1. |
| M1 + F1 + H1 (the landing set) | OWASP: NO_DEMAND_EDGE in run 7 in every M1 + F1 launch with or without H1 (4 of 4), results, SARIF flows and routes equal; time equal (runs 2 to 7: 37.3 s against 37.4 s native; wall 215 s against 215 s at a quiet control, §6.7). Stirling-PDF: the fast form in 5 of 5 launches (native: 2 of 3), results and SARIF flows equal to native fast, routes equal (§6.7); against the native slow form it saves about 950 s. Conductor: results and SARIF flows equal in every launch, no OOM (3 of 3 with 3,000 s); it ends run 8 in 2 of 3 launches (29m 43s and 32m 15s) and stops in run 10, where native does not end run 8 in 0 of 2 (§6.9); H6 -19% to -21%, H7 -40% to -42%. | Conductor: backward run 6 +24% to +47% (+24% to +32% for the pairs with the nearest load); H3 +17% to +18%, H4 +3% to +6%, H5 +25% to +29%, so withdrawal condition 4 of M1 (§3.7) holds for H3 to H5 and not for H6, H7 or the number of runs; run 8 goes above the 90% memory threshold once in each launch and continues after the memory manager clears about 6,500 soft references (native: not above 90% in 37 minutes of run 8); peak RSS 9.40 to 9.59 GB against 9.48 to 9.54 GB. Stirling-PDF fast form: sum of engine times 89 s to 99 s against 89 s, wall 158 to 167 s against 154 to 155 s (+2% to +8%, 3 quiet launches; cause not traced). OWASP peak RSS 9.31 to 9.36 GB against 9.27 GB. 2 cycle fixtures change from provisional to confirmed (§6.1, D3). The cause of the Conductor run-6 price is traced for M1 + F1 (§6.8), and no start-form rule removes it without a larger cost; for the landing set it is INFERENCE. | **WI with a price.** The improvement is measured on every project, and the price is measured. The design guide asks for no negative consequence, so the user decides whether the price is acceptable (§14, D1). |
| M1 + F1 without H1 | As the landing set on OWASP. | Conductor run 6 +55% to +62% and the sum of the engine times to the end of run 7 +27% to +30% (2 quiet launches, §6.7); in its one 3,000 s launch it runs out of memory in run 8 (§6.9). Withdrawal condition 4 of F1 (§3.8) holds. | **Not WI.** The landing set is better on Conductor run 6, the hand-off rows H3 to H7, peak RSS and Stirling-PDF (fast form); M1 + F1 lands only with H1. |

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
[x] Proofs (H1; M1 v5: MustStartFit §6; F1: FlowMustCompanion)       §8
[x] Root cause of the measured Conductor costs (M1 loop, M1+F1 depth) §6.5, §6.8
[ ] Root cause of the Stirling-PDF fast-form time (up to +8% wall)     §6.7, §10
[x] Intervention test of the depth cause (A5c, rejected)              §6.8
[x] Conductor gate in equal time (3,000 s: 2 native, 3 landing set)  §6.9
[x] Quiet-control launches of the landing set (OWASP 1, Stirling 2)   §6.7
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
- F1 and M1 + F1: `f1/` (gate launches, suites, route census
  `*.routes`), `f1prof/` (run-6 jstack samples `*-r7`, owner time
  `*-r7-ot`, owner traces `*-r5-gti`, `*-r5-udt*`, ablation
  `mpf1a1a3-r7`), `f1long/` (3,000 s launches), `a5c/` (ablation A5c).
  Logs `gate-queue18.log` to `gate-queue38.log` (queue 38: the
  quiet-control launches `f1/OWASP-mpf1hs-2`, `f1/Stirling-PDF-mpf1hs-4`
  and `-5`, build `8c70ee97e`). Analysis scripts in
  `scripts/`: `routecmp.py` (route census coverage), `otcmp.py`
  (owner-time and block-counter comparison), `ownerprof.py` (jstack owner
  shares), `longcmp.py` and `longtable.py` (per-run and cumulative times
  of long launches), `gcruns.py` (heap after GC per run).
- Thread dumps and class histograms (`run6-sample-*.txt`,
  `stall-run6-jstack-*.txt`, `stall-run6-histo.txt`) were removed after
  the analysis, as the campaign rule asks. Their findings are in §6.2,
  §6.5 step 7 and §6.7.
- Branches: `proto/cycle-trace-20261126` (diagnostics, M1 v3 at
  `3b1322f49`), `proto/must-probe-20261126` (= `3b1322f49`),
  `proto/stirling-split-20261126` (H1 at `87a315db4`, report
  `70c10d61d`), `proto/mp-hs-20261126` (both, `dd068a66f`),
  `proto/mp4-hs-20261127` (M1 v4, `d6cbcada0`), `proto/mp5-20261127`
  (M1 v5 `4221a2391`, streamed hand-off dump `578ffaf7c`, ablations A1 to
  A6 up to `73e07fdb2`, F1 `8c70ee97e`), `proto/mpf1-diag-20261127`
  (F1 build plus diagnostics: thread owner names, per-owner run time,
  owner-trace kind filter, `ce3d36380`; ablation A5c, flag
  `concreteMustFlowStar`, `c9e4fdeeb`).

## 14. Decisions for the user

**D1. Land M1 + F1 + H1 as one set (recommended).** The OWASP fix is
designed and gated: M1 (§3) stops the cycle with the start row of ap.md
§6.5, F1 (§3.8) removes the loop cost that M1 exposes on Conductor, and
H1 (§5) is needed as well: without H1, M1 + F1 has a larger run-6 cost
and ran out of memory in Conductor run 8 (§6.9). The set improves every
project (§11): OWASP ends in run 7 at equal time, Stirling-PDF is always
fast, and in 3,000 s Conductor ends run 8 in 2 of 3 launches (native: 0
of 2). The decision is about its measured price:

- Conductor backward run 6 is +24% to +47% slower. The cause is traced
  for M1 + F1 (§6.8: the shallow backward answers of FLOW MUST records);
  with H1 it is INFERENCE. No start-form rule removes it without a
  larger cost (A5, A5c).
- Conductor run 8 goes above the 90% memory threshold once in each of 3
  launches and continues after the memory manager clears about 6,500
  soft references; no OOM. Native does not go above 90% in run 8.
- The Stirling-PDF fast form takes up to 8% more wall time (158 to 167 s
  against 154 to 155 s, 3 quiet launches). The native slow form, which
  the landing set removes, takes 1,112 s.

The alternative is to keep CURRENT for OWASP: the reports are final at
run 3, and the cost of the cycle is the end status (run limit), not time
(§2.1).

Landing work if D1 is accepted (no flags, no counters in landed code):

1. M1 v5 in `RestrictedInitialPolicy.emit` and `canEmitInitial`, without
   the dead fallback (R8); F1 in the companion clause of
   `canStoreInitial`; H1 in the hand-off projection.
2. Update the 10 dataflow tests and the 7 cycle fixtures of §6.1 to the
   NEW rows (D3).
3. Add the F1 row to the test oracle (`SelectedDemandReference.stores`)
   and a table test with the `FlowMustCompanion` vectors (R15).
4. ap.md: the instance law for FLOW members of C5 (§7.3) and the lane
   normal form of the hand-off (§7.2, D2).

**D2. H1 and C2 monotonicity (R1).** H1 can remove an EXACT demand row
that a covering MAY row makes redundant. In the next run this can give a
STAR DEMAND start in place of an EXACT NORMAL start, because C2 is not
monotone in region coverage. CURRENT makes the same removal in every fast
Stirling-PDF launch. Decide: land H1 as it is (the store law of ap.md),
or first make the spec say which form the hand-off keeps.

**D3. Fixture status (with M1).** Two cycle fixtures change from
provisional to confirmed with M1 (§6.1). The hand check says that both
flows exist. This is a result change in a test fixture, not in a
reference project; it needs your acceptance under the rule that no
result may change without a decision.
