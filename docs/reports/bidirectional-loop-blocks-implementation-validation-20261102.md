# Loop blocks: implementation validation

Date: 2 November 2026. **Status: implementation and native validation complete.**
The project attempts exposed work-accounting and boundary-coverage defects.
The corrections pass the complete native suites. This file is not a
performance report.
The [native receipt](data/bidirectional-loop-blocks-validation-20261102.json)
records the exact tested source hashes, commands, test-class counts and log hashes.
The implementation commit will contain this receipt.

Implement the [selected proposal](../design/bidirectional-loop-blocks-restriction-implementation-20261102.md).
One original method actor now owns a block tree for a CFG with loops. A method
without loops keeps its previous transfer path. No generated method, register
pack, alias model or prescan call-graph node is added.

## 1. Implemented behavior

```text
validated immutable SCC layout, recursive AL and physical ports
    -> lazy block entry states and local post-S stores
    -> saved NORMAL replay, then scoped C2, then current local links
    -> one-traversal summaries and complete paired local C5
    -> strict growing-row gate on repeat and leave
    -> adjacent demand + saved adjacent composition/B demand + L demand
    -> scoped records, Targets, static guidance and counted handoff
```

The gate uses the selected shortest observation-preserving prefix reference.
It preserves protection annotations and complete ND execution. It changes no
field transfer, cleaner, mark, alias, source-permission or report identity rule.
Native record replay shares the existing MUST policy with real calls.

Actual method boundary transfers and rules execute once in their owning local
span, at the original instruction. The first span starts before the entry rules.
Its saved summaries thus include their effects. A cyclic first instruction
repeats its ordinary transfer without repeating entry rules. A Target or run-1
static result first completes the nearest boundary, then reaches its ancestors
through ordinary matched local-summary application. Root metadata uses the
restored original method premise. It does not run boundary rules again.

Each normal loop leave has one shared normal interface. Acyclic leave tails
stay inside the loop span until their real join. Exceptions, returns and feedback
keep their actual roles. The user accepts the existing cross-branch ND false
positive at this common join. An inner leave to an enclosing loop header keeps
the outer feedback gate, including when the inner AL is empty.

Saved local-summary application uses the existing global field limit before
result storage or another subscription. Stored summary geometry still selects
the gate. The read-only AL/B observer uses raw native composition followed by
paired C5.

Composite completion points use the existing scoped edge store. Freeze aggregates
root, child and completion scalar gauges, releases live links and stores, and keeps
only admitted snapshots and numeric diagnostics. Physical processing and internal
boundary candidates have separate counters.

## 2. ZERO, Target and static shortcuts

The user selected this explicit compatibility hack:

```text
Target conclusion -> nearest normal boundary, then ordinary parent application
backward ZERO at an actually reached exceptional exit
    -> additionally apply the complete normal-exit control demand rows
```

There is no new seed or direct block scan. DATA and native record ports stay
physical. If this borrowed ZERO produces DemandTarget, its outgoing handoff
metadata uses the borrowed normal invocation address. Live input scopes and
NormalTarget persistence do not change.

Run-1 static writes still supply marks at their physical write points. Their
shortcut first completes the nearest span. Internal static-to-static rows remain
available for parent application; only the public method store uses the existing
static-to-static erasure rule. The actual exit handler runs through a private
operation continuation. A mark request there follows registered identity links
to its real original input. A reply restores that original premise through normal
composition. This adds no writer or entry seed.

Private operation rows do not replace ordinary AL rows. The production
MarkInput/KEEP lowering must be present, so the ordinary pre-rule AL row can
guide the reversed run. The full Driver regression uses that lowering and checks
the exact paired demand. DATA admission and AP intersection remain unchanged.

Raw static output uses the internal `STATIC_SHORTCUT` port. It has not yet
executed the actual exit rules. Completed `ROOT_EXIT` output uses only the
method-metadata step, including when its conclusion is STATIC. A new regression
failed before this distinction: one exit-source assignment executed three
times in a loop with no local static write. It now executes once. The native
receipt embeds the red message, log/XML hashes and the tested runtime hashes.
The raw port reverses only in the existing narrow run-2 static Target check;
it adds no ordinary DATA ingress or NORMAL native record.

## 3. Native results and finite witnesses

The corrected complete clean serial command passes **2,369 core tests and 453 JVM tests**, with no
failure or skipped test. The benchmark, comparison and profile helpers pass
**60 Python tests**. The native receipt records the final source set. Earlier
failed commands are intermediate evidence, not final acceptance receipts.

| Finite control | Reached/completed iteration or explicit bound | Result |
|---|---|---|
| FULL source, identity loop, later sink | run-1 / run-1 | One physical finding; scoped summaries exist |
| Nonreturning source/read/sink, two fields | run-3 / run-3 | One finding; source permission retained |
| Nonreturning source/read/sink, four fields | run-5 / run-5 | One finding; permissions retained at run-3 and run-5 |
| Two successive loops, static writer then getter/sink | Complete by run-5; exact final iteration is not logged | Finding, run-2 source hit and run-3 source permission all asserted |
| Static write, loop read and guarded exit source | run-3 / run-3 | Correlated static premise, exact run-2 demand, source permission and NORMAL caller finding |
| Two mutually exclusive normal breaks, ND exit sink | run-3 / run-3 | Accepted cross-branch finding retained; run-1 split arms stay DEMAND |
| Inner leave to outer header, saved growing row | Direct run-5 frame | Both real outer-feedback routes reach paired demand; no saved span is re-executed |
| Empty BL, repeat/break/throw/return | run-1 / run-1 | Physical findings and port checks pass |
| Multi-entry loop and actual callee with guarded alias suffix | run-1 / run-1 | Findings and original method identities retained |
| Saved growing and shrinking loop relations | Direct run-5 frames, not a full campaign | AL/B retention, two shrinking repeats and complete origins asserted |

The scoped binary-read control supplies explicit physical boundary demand and
requires both reads to execute. At backward limits 1, 3, 5 and 7 it uses 27 physical
processing steps and 26 stored leaves. The flat reference has 3, 15, 63 and 255
leaves. Both keep the same three public demand images. This demonstrates avoided
work for this finite program; it does not establish a project speedup.

Other controls cover stack-safe SCC construction, nested AL order, scope
isolation, post-S placement, complete ND joins, late publications, current
requests, protection upgrades, native MUST replay, static reply lifetime, exact
record reversal, driver stopping and cleanup after a service failure. The no-loop
AP, rule, method-driver and JVM controls all pass in the complete suites.

## 4. Proof boundary

The constructive Lean models establish their finite reference and protocol laws.
The source-pinned receipt binds those laws and native correspondence controls to
the reviewed source. Hash stability is not a proof of the Kotlin implementation.
The package does not claim kernel verification of the SCC builder or the full AP
adapter, general cross-run convergence, or measured project improvement. See the
[proof dossier](../../spec/loop-blocks-implementation-proofs.md).

## 5. Fixed project campaign

The first attempt at `a992d9afa` is retained in
`../loop-blocks-restriction-20261102`. OWASP reached **run-1**, completed none,
and failed freeze because a late static boundary reply queued fresh local
delivery without counted method Work when its child initial already existed.
The regression test reproduces this failure before the correction and passes
after the conditional enqueue. This changes work accounting, not analysis rules.
The remaining campaign was stopped: Conductor reached **run-3**, completed
**run-2** and accepted **run-1**. No OOM occurred. This interrupted attempt is
not the final quality or performance result.

The second attempt at `10957156a` is retained in
`../loop-blocks-restriction-fixed-20261102`. OWASP reached, completed and
accepted **run-5**, but missed 51 baseline identities. Its source gap is recorded
in the [boundary investigation](bidirectional-loop-boundary-source-gap-20261102.md).
Conductor reached **run-4** and completed/accepted **run-3** before the campaign
was stopped. Thingsboard and Stirling-PDF did not start. No OOM occurred.
These results do not measure the corrected implementation.

The corrected campaign is prepared in
`../loop-blocks-restriction-verified-20261102`.
Run OWASP, Conductor, Thingsboard and Stirling-PDF through the direct
`runProjectAnalyzer` Gradle task. Keep FULL, 16 GiB, limits `1,1,2,3,...`, statics
and aliases enabled, and the selected timeout for each project. Reuse the fixed
`f945f92c5` finding baseline; do not rerun it.

Previous captures were removed only after their derived exports were saved.
The attempt directories retain cleanup receipts, reports, logs and baseline
bundles. The launcher requires committed runtime source and checks source,
model and baseline hashes.

The project performance report and the measurement-based next-iteration proposal
remain required deliverables. The replacement measurement must use the committed
correction and the same configuration.
