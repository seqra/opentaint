# Loop fragments and demand collapse: local models

Date: 2 November 2026. The selected boundary corrections pass the complete
native suites: **2,369 common tests and 453 JVM tests**, with no failures,
errors or skipped tests. The benchmark harness also passes 60 Python tests.
The latest project campaign is historical: OWASP completed **run-5** before
these corrections, with 51 missing baseline sink identities. A fresh project
campaign is still required; see the
[gap report](../../../../docs/reports/bidirectional-loop-boundary-source-gap-20261102.md).

Read [the spec](../../../loop-fragments-and-demand-collapse.md),
[method-owned blocks](../../../method-owned-loop-blocks.md),
[the proof dossier](../../../loop-fragments-and-demand-collapse-proofs.md),
and [the proof guide](../../../proof-guide.md). The
[implementation proposal](../../../../docs/design/bidirectional-loop-blocks-restriction-implementation-20261102.md)
and [implementation proof dossier](../../../loop-blocks-implementation-proofs.md)
define the production mapping and its proof scope.

```sh
python3 spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/check.py
# During implementation, without a claim that the runtime source pins match:
python3 spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/check.py --model-only
```

The checker uses pinned Lean `leanprover/lean4:v4.33.1`, one worker and
one CPU. Its memory limit is 768 MiB for the structural modules and
2,048 MiB for Admission and the combined audit. It audits every explicit
public definition and theorem. It permits only `propext` and `Quot.sound`
and rejects classical choice, unproved declarations, unsafe/partial or
noncomputable source and native evaluation proofs.

| Module | Scope |
|---|---|
| Control | Exact labelled CFG routing, feedback ports, self loops and supplied acyclic-body certificates |
| Geometry | Bounded scalar prefix projection, coverage, metadata and finite-image/work witnesses |
| Admission | Stated finite concrete C2 cells and rejected forced-MAY counterexample |
| Guidance | Unary ND restriction metadata; unchanged complete AND execution |
| Shape | Strict summary growth, `FL(Zero)=0`, equal/shrinking bypass and exact-suffix bounds |
| Protocol | Whole original, port/context, producer effects and separate complete-row publication |
| Restriction | Fixed complete AL/B/L observer, finite shortest-safe-cut reference and image preservation |
| Feedback | Missing internal consumer under AL/B-only gate; selected L check preserves the example |
| Decomposition | Exact ordered-region sequence, recursive AL hierarchy, empty prefix and successive-loop example |
| Blocks | One method owner, shared registers, separate post-S stores, repeat/leave gates, parent dependencies and local frontier collection |
| Discovery | Existing exceptional-exit backward overlay, explicit path witnesses and no new normal-start route |
| ExceptionalControlDemand | Reached backward exceptional ZERO borrows complete normal control demand; only its ZERO DemandTarget handoff address uses the normal invocation; paired payloads, DATA/native/live scopes and forward graph stay unchanged; finite four-field run-5 continuation witness |
| Implementation | Shape/projection/publication composition, scope retention, nonempty-image witness and local-delivery barrier |
| Usefulness | Reference investigation only; no runtime NORMAL reachability service is selected |
| EntryPrefixNativeRecords | Genuine pre-rule prefix/native replay, finite bounded producer and backward-ZERO suffix guidance cells |
| NearestBoundaryTerminals | Complete matched ancestor application, typed Targets, internal static/static retention and shared normal-join examples |
| CanonicalLoopExit | Labelled normal-exit reversal, acyclic tail certificate and context-relative enclosing-header join |
| StaticBoundaryInputRelay | Actual point request, identity-only original-input relay, canonical genuine reply and late-input order |
| MethodExitMetadataEffects | Generic ordered Holds projection and finite FULL/TAINT exit metadata/header laws |

`EntryPrefixNativeRecords.lean` is a scoped interface model
for the selected boundary-span contract. Its direct
[check receipt](EntryPrefixNativeRecords-check.json) covers 54 constructive
theorems on actual pre-rule entry composition, native replay, non-NORMAL
rejection, bounded DEMAND guidance and the existing backward-ZERO suffix
handoff exception. It is registered in `check.py` and counted by the
19-module receipt. It does not prove the Kotlin runtime adapter, scoped Target
ownership, complete ND rules or full AP correspondence. See
[proof dossier section 3.3](../../../loop-blocks-implementation-proofs.md#33-selected-boundary-span-coverage-correction).

`NearestBoundaryTerminals.lean` checks the selected nearest-boundary
Target/run-1-static publication and shared normal-exit join scope. Its separate
[receipt](NearestBoundaryTerminals-check.json) covers 54 theorems and 115
audited public definitions/theorems. A supplied complete matched application
chain constructs every ancestor row, retains exact paired ports and
annotations, rejects incomplete ND/DEMAND NormalTarget bindings, and keeps
internal static/static relations until public root erasure. It also checks
the accepted normal branch-union false positive and complete ND positives.
This model is registered in the main checker. It does not verify the
AP matcher, physical rule execution, root metadata or runtime adapter. See
[proof dossier section 3.4](../../../loop-blocks-implementation-proofs.md#34-selected-nearest-boundary-terminal-ownership).

`CanonicalLoopExit.lean` has 41 checked theorems and 99 audited public
definitions/theorems in its [standalone receipt](CanonicalLoopExit-check.json).
It separates the common normal join identity from the actual physical
route label, checks native/demand reversal and exact CFG refinement, and
keeps feedback, exceptions, returns and discovery separate. Its executable
normal-tail certificate retains the graph, headers and feedback, checks
one real normal join and an acyclic cut body, and covers the branch-tail
and nonreturning examples. Its context view also covers an inner normal
leave to an enclosing header, preserving the actual outer-feedback role
and an empty inner AL. It is registered in the main checker and does not
verify a runtime route adapter.

`StaticBoundaryInputRelay.lean` has 18 checked theorems and 42 audited
public definitions/theorems in its [standalone receipt](StaticBoundaryInputRelay-check.json).
It checks the actual operation-local FLOW request, strict-parent identity
relay, original-field supply guard, canonical inner reply and late-input
event order. It keeps the existing C.g point interest and adds no writer.
It does not prove AP materialization or the Kotlin callback traversal,
and is registered in the main checker.

`MethodExitMetadataEffects.lean` has 23 checked theorems and 48 audited
public definitions/theorems in its [standalone receipt](MethodExitMetadataEffects-check.json).
Its generic ordered scanner proves that stateful ND/report bookkeeping
does not change the pure ordered Holds list. The existing fold then gives
the same final DATA result. Finite FULL/valid-TAINT examples check root
ZERO guards, unchanged run-1/backward exceptions and the mixed EXACT/ANY
header counterexample to mask union/reordering. It does not verify full
AP checkMark or the Kotlin callbacks, and is registered in the main checker.

The [native control record](controls.md) embeds the code and traces for the
next-body case. Its finite FULL driver control completes **run-3**, with
one report. Four further native discovery checks pass, including a FULL
loop with no leave that also completes run-3. Native controls are separate
from the kernel proof receipt.

The [receipt](checks.json) hashes the exact inputs and records kernel and
audit results. A local-model PASS is not a proof of Kotlin block decomposition,
all AP application/projection adapters, whole-driver convergence or a
project speedup. The [native validation report](../../../../docs/reports/bidirectional-loop-blocks-implementation-validation-20261102.md)
and its embedded source/result receipt record the current implementation checks.
The exceptional-ZERO lookup is selected explicitly
in the ownership spec; its model does not authorize a broader control alias.
The separate `model-checks.json` receipt does not validate runtime source
pins. It cannot replace the final source-pinned check.

The current strict receipt has `runtimeChanged=true`. It verifies exact
runtime/test hashes, complete selected source-directory membership and the
embedded native validation summary. All 19 local models pass the kernel
and axiom audit: **564 theorems and 957 explicit public declarations**.
Source pinning and native tests do not prove Kotlin. The receipt keeps
`runtimeVerifiedByKernel=false`; general AP adapter coverage, whole-driver
convergence and project performance remain separate obligations.
The exact
[pre-implementation source pins](implementation-source-pins-before-implementation.json)
and [339-theorem historical receipt](checks-before-implementation.json) remain
separate historical evidence. Their `runtimeChanged=false` value describes
that earlier proposal state, not the implementation now in this checkout.
