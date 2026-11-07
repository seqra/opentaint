# STAR_OR_ANY loses refinement guidance at a loop handoff

Date: 7 November 2026. Status: native finding regression; behavior choice pending.
Language: ASD-STE100 Simplified Technical English.

The initial SOA gate passes its 23 selected tests. The first full
native gate still fails. One existing test loses its required finding after a
backward SOA row becomes a public STAR row. The next forward run cannot use that
STAR demand to admit a precise descendant into the loop repeat entry.

The [portable evidence](data/bidirectional-star-or-any-handoff-gap-20261107.json)
embeds the decisive full-gate XML, all three selected-test XML files, receipts,
exact trace lines, source excerpts and hashes. This report adds no core or test
change. It does not select a repair or weaken the finding assertion.

## Initial native results

| Gate | Tests | Failures | Result |
| --- | ---: | ---: | --- |
| Selected SOA tests | 23 | 0 | Pass in three suites |
| Full dataflow module, attempt 1 | 2,602 | 24 | Fail; review required |
| Full JVM dataflow module, attempt 1 | 462 | 0 | Pass |

The selected seven complete-program cases all report one finding. The original
four-method loop and mapper first reports at run 3 and reaches natural
`COMPLETE / NO_DEMAND_EDGE` at run 5. The other six cases first report and end
at run 3. These results do not replace the full native gate.

The successive-loops test ends naturally at run 3 with **zero** findings:

```text
AnalysisEnd(COMPLETE, run=3, FORWARD, NO_DEMAND_EDGE, FULL)
frontiers: run 1 = 13 demand rows, 0 reports
           run 2 = 14 demand rows, 0 reports
           run 3 =  0 demand rows, 0 reports
required: [two loop static sink]
actual:   []
```

The other known finding failure is
`LoopBlockDeepNoLeaveTest.exceptional ZERO normal demand keeps a four field
source through the fifth run`. Its finding assertion expects 1 and gets 0.
Its separate cause investigation is not replaced by this trace. The other
full-gate failures are not declared harmless by this report. No fresh project
campaign has been launched for this working-tree change.

## Code under analysis

This is the existing `LoopBlocksIntegrationTest` program. The test uses the
real iteration driver, block routing, physical source callback and static
write/read operations. It supplies no manual demand or saved summary.

```java
// sourceAtG creates exact mark T at a.g.
while (again1) {
    a = sourceAtG();          // physical node 2
    Box.shared = a;           // physical node 3; L1 repeat edge
}
while (again2) {
    b = get();               // physical node 5
    sinkT(b.g);              // physical node 6: required finding
}
Object get() { return Box.shared; }
```

Use `CF` for the static anchor `Box.shared`. Within this fixture capture,
`CF=[1,4]`, `g=0`, and full mark `T=1`. Both field descriptors are
`FieldAccessor("Box", name, "Box")`; the class anchor is
`ClassStaticAccessor("Box")`. IDs are local labels, not cross-run identities.
`S?` means SOA, `$` means EXACT, and `D`/`N` mean DEMAND/NORMAL. All decisive
facts below have Empty E and no protection flag.

## Captured state

The complete XML `system-out` contains the following states. The line numbers
refer to its decoded `system-out`, also indexed in the portable JSON.

| State | Exact observation |
| --- | --- |
| B2 live point rows, lines 107–118 | Raw premise `CF.S?/T`; live `CF.S?/T, D` reaches nodes 6, 5, 1, 0, 3 and 2. The backward write also produces `a.S?/T, D`. |
| B2 public L1 row, line 39 | Scope `(block2, entry10)`, exit `4`: `CF.STAR/T → CF.STAR/T, D`. |
| B2 public repeat row, line 42 | Scope `(block2, entry4)`, exit `4`: the same STAR pair, D. |
| F3 source permission, line 7 | The exact physical source occurrence at node 2 is allowed. The test's preceding source-hit and permission assertions pass. |
| F3 precise static output, lines 55–56 | L1 scopes `(block2, entry0)` and `(block2, entry4)`, exit `4`: `ZERO → CF.g.$/T, N`. |
| F3 processed rows, lines 119–126 | Processing reaches L1 nodes 1, 2 and 3. This saved list has no L2 node 4, 5 or 6, and F3 has no getter actor. |

Thus the source permission, source transfer and storage of the precise static
result succeed. The failure is not evidence that the source rule was disabled
or that the available field budget cannot represent `shared.g`: F3 uses FL2,
and that path has two counted fields.

## Derived handoff and first rejected gate

The following step is **source-derived**, not a captured C2 call/result event.
`projectBlockHandOff` reverses the two control ports and forms demand entries
from the selected conclusion. `guidancePattern` keeps the public STAR tail.
The captured B2 L1 row at line 39 therefore gives this F3 row:

```text
method/context: two loop static root [context]
B2 producer:    block2, entry10 -> exit4
public pair:   CF.STAR/T -> CF.STAR/T, D
F3 demand:     block2, entry4 -> exit10
paired entry:  CF.STAR/T
paired exit:   CF.STAR/T
```

The row at line 42 also gives a STAR pair at F3 repeat entry4/exit4. These are
real paired rows, with both ports kept. No descendant demand is synthesized.

The precise F3 output at repeat exit4 must re-enter L1 through entry4, carry
`CF.g.$/T` to the header, and then take the leave edge toward L2. The derived
admission tuple at that repeat boundary is:

```text
run=3, direction=FORWARD, fieldLimit=2
scope=(block2, entry4), caller original=ZERO
actual: CF.g.EXACT/T, N, E={}
demand: CF.STAR/T, paired with CF.STAR/T at exit10
```

The current scalar selector rejects this tuple:

```kotlin
// actual.path starts with demand.path, with one additional field g.
when (demand.tail) {
    STAR -> if (run == 2) result(demand.path, STAR, demand.E) else null
    // ...
}
// Here run == 3, so the result is null.
```

`MethodBlockRuntime.offerChild` returns on an empty initial set before it
installs the ordinary child input/link. A later adjacent demand cannot carry
the precise value through a repeat entry which did not admit it. The captured
precise output and absent later processing agree with this derived rejection.
The XML does not record the exact offered C2 packet and returned initial list,
so it is not a direct transaction capture of that return value.

This gate differs from the ordinary supplied-STAR rejection: the supplied
actual here is **EXACT**, while the demand became STAR after public SOA erasure.
The live marker's admission capability did not survive as refinement guidance
across the backward-summary/forward-demand interface.

## Scope of the result

The [selected SOA spec](../../spec/intra-procedural-star-or-any.md) requires
SOA to become STAR at public summary and demand endpoints. The native result
shows that this interface rule and the unchanged later-run STAR-demand rule
lose an existing loop finding. The required behavior for that guidance handoff
remains pending user choice. Local image and wrapper proofs do not close this
native gate.

This is one finite native path. It does not locate a first loss in Conductor
or Stirling, prove a global cause for missing project findings, establish
performance, or authorize another C2 policy. Keep the exact finding assertion,
full gate failures and source-derived status visible until the behavior is
chosen and the native gate passes.


## Follow-up: targeted review and current iteration results

A later targeted run passes **82 tests in eight suites**, with zero failures.
It includes **27 selected SOA tests**: the prior 23, three owner-retention tests,
and one bounded C2-image test. The other 55 tests check reviewed transfer,
selector, operation and fanout oracles. This targeted result does not replace
the captured full-gate ledger of 2,602/24 and 462/0 above. A fresh complete
native gate has not passed.

| Native program/result | Latest reached | Latest completed | Finding |
| --- | --- | --- | --- |
| Successive loops, full-gate attempt 1 | run 3 | run 3 | none; expected one |
| DeepNoLeave, external diagnostic attempt 3 | run 5 | run 5 | none; expected one |
| Original four-method loop and mapper, selected review | run 5 | run 5 | one; first at run 3 |
| Other six selected programs, each | run 3 | run 3 | one; first at run 3 |

The root-run external DeepNoLeave trace reproduces the missing finding. Its
XML has one test and one failure. The trace has 82 lines and records runs 1–5
as COMPLETE. The unchanged end-run assertion passes before the finding-count
assertion fails with expected 1, actual 0. The portable data embeds this XML,
the complete trace, the copied source, the corrected init and its receipt.
**Its cause remains unproved here.** This evidence must not inherit the
successive-loops cause without a separate path proof.

The first trace attempt used the wrong composite task path and did not add
the Deep source. Its three owner tests pass, but that receipt explicitly says
`deepTraceExecuted=false`. The data retains this qualification. It is not a
DeepNoLeave result. The next section records the separate third attempt.

## Follow-up: DeepNoLeave repeat queries and growth gate

Diagnostic attempt 3 again reaches and completes run 5 with no finding. The
Gradle command exits **1**, with one test and one failed finding assertion.
This is a reproduced test failure, not a passing gate. The data embeds its
complete XML, trace, source, init, console and receipt.

The run-5 statistics are captured before the diagnostic queries:

| Run-5 counter | Value |
| --- | ---: |
| Growth scalars / observations / drops | 2 / 2 / 2 |
| Proper-prefix trials / cuts | 0 / 0 |
| C2 native queries / returned rows | 2 / 0 |
| Global boundary cuts / pre-publication dead locals | 0 / 0 |

Trace lines 47–48 contain the produced loop result `ZERO → x.fff.$/T, N`
at exit5, for block2 entries1 and5. Both have Empty E. After the driver ends,
the diagnostic performs these **post-run queries** at the same repeat scope:

```text
scope: block2, entry5; actual: x.fff.EXACT/T, NORMAL, E={}
demand.initials(actual, policy): []                    // trace line 49
records.byEntry(actual):                              // trace line 50
    direction=FORWARD; x.f.STAR/FLOW → x.STAR/FLOW, NORMAL
```

The returned saved row is a shrinking repeat relation. The record query
returns a candidate; it does not prove that this row was matched, replayed or
applied during the run. The demand query is an actual native query on the
frozen run-5 configuration. It is not a capture of a live C2 transaction.

The gate location is **source-inferred**. `restrictScalar` counts one
observation per scalar and drops a scalar immediately when that baseline is
empty, before any prefix trial. The run-5 counts identify two such drops.
`onApplied` calls this restriction before it routes kept output onward.
The observer obtains saved rows from adjacent scopes; the post-run shrinking
row is instead at the repeat scope. Separately, `offerChild` replays saved
rows before it tests the C2 initial set. Thus an empty C2 list alone does not
establish that the saved repeat route cannot carry the value. The growth
observer can stop delivery before that route is tried.

This gives a distinct DeepNoLeave investigation from the first F3 two-loop
handoff rejection. The capture has no per-scalar observation contents or live
repeat replay event. It does not establish a complete necessary cause or
show that the pending guidance choice would repair DeepNoLeave. No repair is
selected here, and no fresh project campaign follows from this diagnostic.

## Follow-up: remaining harness review and GROUP diagnostic

The remaining harness review passes **78 tests in ten suites**, with zero
failures. Its receipt and all ten XML files are embedded. This review covers
raw/public SOA trace expectations and keeps the finding assertions. It does
not supersede the original full-gate failures or establish a full gate pass.

A separate GROUP diagnostic records these results:

| Execution | Latest reached | Latest completed | Finding / output |
| --- | --- | --- | --- |
| Natural driver | run 3 | run 3 | `entries=[]`; `COMPLETE / NO_DEMAND_EDGE` |
| Explicit backward replay after the driver | forced run 4 | forced run 4 | no actors or processed premises |

The forced B4 call is an explicit diagnostic invocation. The driver did
**not** reach run 4. The helper checks that all invoked runs are COMPLETE
before it returns and prints the trace. This diagnostic does not extend the
driver's reported end label.

In B2 the callee actor exists. Its processed rows have raw static
`C.f.S?/T, D`, with the same raw premise. In F3 only the root actor exists;
the callee actor is absent. The post-run `records.byEntry(callee, exact)`
queries on configs 3 and 4 both return empty lists. These are exact-entry
query results, not proof that every record or admission route is absent.
The trace also records a F3 ZERO/NORMAL identity record application. It does
not record a fine concrete callee record.

Attempt 2 has one test and one failure. Its XML reports
`NoSuchElementException` at the unchanged check that selects the missing
F3 callee actor. The trace independently records `entries=[]`; the failure
is not the later finding assertion. Its receipt, source, init, XML,
25-line trace and root log are embedded. Attempt 1 failed in a diagnostic
read of released initial storage, before the normal program assertions.
Its receipt and XML remain embedded with that qualification.

The GROUP cause remains **unproved**. This result does not establish that
the first two-loop handoff choice would repair GROUP. Two FULL behavior
questions remain pending: how to carry refinement guidance through the
public STAR handoff, and whether repeat NORMAL replay must be observed before
current gating. This report selects neither behavior. No fresh project
measurements or core commit follow from these diagnostics.

## Follow-up: local proof scope and the negative handoff model

The portable root checker passes **39 local design laws** (29 design laws and
10 obligation laws). A separate checked model passes **eight counterexample
laws**. The combined portable check passes with these groups kept separate:
39 local design laws plus 8 negative handoff laws, 47 audited statements.

The negative model supplies a finite backward concrete DEMAND row whose SOA
endpoints become STAR. Handoff keeps STAR. At run 3 a child EXACT/NORMAL
actual is rejected; the corresponding old MAY demand admits it. Same-head
and run-2 controls do not remove that later-run descendant rejection.

These eight laws prove a local counterexample, not a repair. The model uses
ordinary symbolic bases and Empty E. It does not prove native static-adapter
construction, native ownership/paired C5, the DeepNoLeave cause, whole-program
soundness, or global recovery. There is no conflict with the scoped 39-law
result: public-handoff refinement was outside its completed guarantees.
The portable data embeds the checked models and receipts with their hashes.

The public-DEMAND guidance behavior and the repeat NORMAL replay gate remain
pending user choice. No additional core repair or new project campaign follows
from these results.
