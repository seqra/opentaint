# Current canonicalization acceptance audit

**Status: selected native and model gates PASS; project quality FAIL.**
The checked tree is `10c1538144ec672387526ff01c0853d994838de2`.
Production code is unchanged from `8331bf9e326ddd1bd5083dbc50456963d6b26b52`.
The later commits add tests and documentation. This audit does not replace the
[main campaign](bidirectional-canonical-facts-normal-relations-directional-inside-performance-20261105.md).

The [portable validation receipt](data/bidirectional-canonical-current-validation-20261105.json)
contains the exact commands, complete test XML, logs, test-source hashes,
model source pins and declaration audit. The historical campaign receipts
remain unchanged.

| Current check | Result | Scope |
|---|---:|---|
| Dataflow module tests | 2,531 PASS | Includes the two added transitivity regressions |
| JVM-dataflow module tests | 461 PASS | Native JVM adapters |
| Constructive model check | 175 theorems; 249 declarations PASS | Current proof guide and production source pins |

There are no test failures, errors or skipped tests in these two modules.
The model audit permits only `propext` and `Quot.sound`; it finds no classical
axiom or incomplete proof. This check does not prove Kotlin correspondence,
whole-engine finding preservation, convergence or performance. The separate
pre-existing root acceptance-test compilation failure was not changed or
rerun.

## Requirement audit

| Requirement | Evidence and result |
|---|---|
| Implement and commit the selected optimization | Production commit `8331bf9e3`; transitivity test follow-up `b409fa007`. Implemented within the selected library scope. |
| Preserve scope | Explicit summary roles and native overlap checks pass. No new C2 policy, raw refinement history or core helper was added. |
| Run the four fixed project configurations | Complete command/config provenance in the main report data. Direct Gradle task, FULL, 16 GiB, saved timeouts, limits `1,1,2,…`; f945 was reused. |
| Preserve strict finding identities | **Not met.** Conductor loses two new identities. Stirling has three inherited missing f945 identities. Thingsboard quality is censored. |
| Explain time and memory | Main report has per-run engine/transition times, CPU/allocation profiles, RSS and GC. No memory-manager OOM was observed; three commands time out. |
| Validate profiles | All 142 continuous/window records pass 284 denominator checks. Coverage limits remain explicit. |
| Trace exact fact behavior | Actual B2 point/summary removals now have complete native post-state checks and a complete frozen explicit-view bridge. The later C2/report causal chain remains untraced. |
| Clean prior captures | All 35 manifest-listed files are absent; 1,631,812,783 bytes were recorded removed. User debugging files remain untouched. |
| Propose the next iteration | The ranked proposal has a correctness gate, then frozen-input canonicalization reuse and the bounded-input limiter fast path. No new proposal is silently implemented. |

## Project quality remains open

These are the latest main-campaign labels: reached / completed / accepted
forward iteration. No project was rerun for the current validation.

| Project | Labels | Quality |
|---|---|---|
| OWASP | run-5 / run-5 / run-5 | All 4,112 strict identities equal f945 |
| Conductor | run-15 / run-14 / run-13 | Two new missing Graal identities; five reports versus seven |
| Thingsboard | run-1 / none / none | Timeout in static completion; no accepted forward report |
| Stirling-PDF | run-16 / run-15 / run-15 | Three inherited missing and eight added versus f945; equal to recent controls |

The [Conductor appendix](bidirectional-conductor-canonical-quality-regression-20261105.md)
isolates a sufficient recovery control: disabling only proper-prefix
subtraction restores seven native rule/full-signature projections at run-5.
It is not an accepted repair or strict SARIF-fingerprint comparison. The
earliest captured frozen-demand difference is before run-3 transfer; it is
not an observed first drop.

The later [B2 point-store capture](bidirectional-conductor-canonical-quality-regression-20261105.md#actual-b2-point-store-subtraction)
now traces broad-after-narrow state subtraction under complete premises and
headers in `getTasksToBeScheduled`, Empty context and ROOT scope. Five closed
windows at instructions 17/3/2/1/54 replace explicit `arg1.taskDefinition` support
with root support, both ANY/FLOW DEMAND with identical E/mx. This is not a
mixed incoming packet: the child was in the prior point authority. The attempt
was manually stopped due to hot breakpoint overhead at run-2/run-1/run-1,
with 40 completed windows, one whole deadline drop, zero decoder drops and
no B2 snapshot. That first attempt remains partial.

The separate [completed cold capture](bidirectional-conductor-canonical-quality-regression-20261105.md#completed-cold-b2-summary-and-guidance-bridge)
now closes B2 and reaches F3, at run-3/run-2/run-1. Seven paired removals include
actual ROOT_EXIT summary-store changes in typed HashMap and Empty contexts.
All five planned collections are complete with zero capture/decoder drops.
The 113-row outgoing direct DATA view has 64 Empty and 49 typed rows; each
context retains one root pair and no explicit taskDefinition child pair.
This proves the same-attempt admitted-store to frozen explicit-view bridge,
not a later native C2 rejection or report-loss chain. The 2,992-test and 175/249
model gates, main quality and measured timings are unchanged.

A separate [conditional-source loop control](bidirectional-nd-loop-canonical-control-20261105.md)
also completes at run-5 for both current and proper-prefix-off runtimes, with
and without the feedback edge. All four cases report the NORMAL sink. This is
not a finding-loss reproducer: no captured packet contains the required
proper-prefix pair. It does not close the project-quality gap.

A [two-method direct regression](bidirectional-canonical-prefix-refinement-reproducer-20261106.md)
now reproduces a concrete refinement delay. At the run-3 checkpoint, current
code has zero NORMAL reports; the proper-prefix-off control has one. Both
converge at run-5 with that finding. The first lost retained B2 coordinate is
`arg0.f.[any]/FLOW`; the first missing executed F3 start is
`arg0.f.g.*/FLOW, NORMAL`. The optional regression task is deliberately RED on
current code. It does not change the default module tests or their historical
2,992-test receipt. This is not a permanent finding loss or a completed
Conductor causal trace.

A separate [one-marker loop reproducer](bidirectional-loop-boundary-normality-loss-20261106.md)
now fails after natural convergence: both current and prefix-off code reach,
complete and accept run-5 with zero NORMAL reports. The valid one-iteration
path needs only two concrete fields. The DIRECT native trace records a NORMAL
`s.f.g.$/T` loop result, its rewrite to DEMAND `s.f.[any]/T`, and the coarse
DEMAND `s.f.*/T` after-loop initial. The native raw/cut admission results are
already equal, so the limiter alone is not a proved cause. This is a shared
coverage gap, not evidence that prefix removal introduced it. Its separate
optional regression also remains RED. No production repair is implemented.

The semantic repair choice is still pending. The selected canonical-only C2
policy permits literal initial images to disappear. Changing that policy or
adding separate refinement guidance needs an explicit design under the
selected proposal. No such change is inferred from a passing local test.
The goal remains incomplete until the required quality contract is met and
verified on the fixed configurations.
