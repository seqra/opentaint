# Loop blocks: implementation validation

Date: 2 November 2026. **Status: implementation and native validation complete.**
Project measurements have not started. This file is not a performance report.
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

Actual method boundary transfers and rules execute once at the original root.
A cyclic first instruction repeats its ordinary transfer without repeating entry
rules. A block with only physical method endpoints supplies an identity interface;
it does not copy those endpoint operations. Saved local-summary application uses
the existing global field limit before result storage or another subscription.
Stored summary geometry still selects the gate. The read-only AL/B observer uses
raw native composition followed by paired C5.

Composite completion points use the existing scoped edge store. Freeze aggregates
root, child and completion scalar gauges, releases live links and stores, and keeps
only admitted snapshots and numeric diagnostics. Physical processing and internal
boundary candidates have separate counters.

## 2. ZERO, Target and static shortcuts

The user selected this explicit compatibility hack:

```text
Target conclusion -> normal exit, as before
backward ZERO at an actually reached exceptional exit
    -> additionally apply the complete normal-exit control demand rows
```

There is no new seed or direct block scan. DATA and native record ports stay
physical. If this borrowed ZERO produces DemandTarget, its outgoing handoff
metadata uses the borrowed normal invocation address. Live input scopes and
NormalTarget persistence do not change.

Run-1 static writes still supply marks at their physical write points. Their
existing summary shortcut lifts local dependencies to the original exit-rule
handler. For run-2 source Target publication, the adapter uses the registered
scoped write/bridge path with a genuine ZERO origin and the exact output port.
It does not use shared carry alone as authority. It changes neither DATA initial
admission nor ordinary AP intersection. Negative controls reject the wrong mark,
block, output, run, nonstatic input, nonzero writer and unregistered write.

## 3. Native results and finite witnesses

The final serial command passes **2,334 core tests and 453 JVM tests**, with no
failure or skipped test. The benchmark, comparison and profile helpers pass
**60 Python tests**. The native receipt records the final source set. Earlier
failed commands are intermediate evidence, not final acceptance receipts.

| Finite control | Reached/completed iteration or explicit bound | Result |
|---|---|---|
| FULL source, identity loop, later sink | run-1 / run-1 | One physical finding; scoped summaries exist |
| Nonreturning source/read/sink, two fields | run-3 / run-3 | One finding; source permission retained |
| Nonreturning source/read/sink, four fields | run-5 / run-5 | One finding; permissions retained at run-3 and run-5 |
| Two successive loops, static writer then getter/sink | Complete by run-5; exact final iteration is not logged | Finding, run-2 source hit and run-3 source permission all asserted |
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

The campaign is prepared in `../loop-blocks-restriction-20261102`. It has not yet
started. Run OWASP, Conductor, Thingsboard and Stirling-PDF through the direct
`runProjectAnalyzer` Gradle task. Keep FULL, 16 GiB, limits `1,1,2,3,...`, statics
and aliases enabled, and the selected timeout for each project. Reuse the fixed
`f945f92c5` finding baseline; do not rerun it.

The cleanup receipt records 35 verified old capture files removed, with a total
size of 2,671,483,748 bytes. Reports, logs and baseline bundles remain. The launcher
requires committed runtime source and checks source, model and baseline hashes.

The project performance report and the measurement-based next-iteration proposal
remain required deliverables. There is no new project run iteration to report yet.
