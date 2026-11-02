# Loop-block implementation: proof dossier

Date: 2 November 2026. No analyzer implementation is changed.
Proposal section 6.1 reuses existing exceptional-exit backward discovery.
Exceptional wiring supplies discovery for nonreturning code; no new
block-start policy is selected.

Read the [implementation proposal](../docs/design/bidirectional-loop-blocks-restriction-implementation-20261102.md),
[ownership spec](method-owned-loop-blocks.md),
[restriction spec](loop-fragments-and-demand-collapse.md) and
[base proof dossier](loop-fragments-and-demand-collapse-proofs.md).
Follow [proof-guide.md](proof-guide.md).

## 1. Exact reference implemented by the proposal

```text
physical graph -> validated labelled block layout -> one method owner

one applied loop-output geometry and its scoped value F:
  non-growing -> the exact F
  growing -> fixed complete observation (next C2, composed-B C5, L C2)
          -> no observation: none
          -> otherwise shortest positive prefix preserving observation
          -> no shorter safe prefix: raw F

actual summary publication:
  normalization -> complete scoped paired C5 -> admitted store -> fresh delta
```

Typed Targets keep their existing matching and publication rules. They
are not DATA prefixes. ND unary arms select restriction precision only;
actual execution retains the complete binding. Cut transport uses the
current AP layer, including protection masks. The reference does not
introduce source permissions, caller grounding or a new NORMAL graph.

## 2. Checked implementation laws

The `Implementation` module composes the existing `Shape`, `Restriction`
and `Protocol` models. It does not replace the reference projection with
an assumed preimage oracle.

| Law | Constructive argument |
|---|---|
| Equal/shrinking bypass | The false strict-growth branch returns the exact input state |
| Growing gate | The true branch invokes the executable finite `Restriction.restrict` |
| Scope retention | Mapping the selected value changes only the fact field; method/block identity, context, whole original and port stay equal |
| Observation preservation | Each kept growing value has the raw complete observation by the shortest-safe-cut theorem; a bypassed value is identical |
| No admitted image lost at this gate | A nonempty observation constructs an explicit kept state, with a raw fallback if needed |
| No new NORMAL evidence | A NORMAL projection result must be the original input state |
| Separate paired permission | A result published after the gate has a witness row matching its original, actual port and result |
| No-row rejection | A useful loop image cannot publish when the selected demand row list is empty |
| Barrier safety | Idle requires no body work, local delivery, local publication, request or static-effect work; a pending local delivery excludes idle |

The module is parametric in the fixed complete observer. A supplied
observer is not an unproved AP truth value hidden in a theorem: its
production implementation is given in proposal section 8, using existing
C2, saved application and C5 operations. The kernel proof covers the
pipeline conditional on that adapter computing its stated signatures.
It does not verify Kotlin callback placement or all AP representations.
The scalar fact model uses concrete FULL marks; FLOW normalization is
outside that scalar scope. The production probe must use the existing
complete FLOW-pair normalization before C5, as the proposal specifies.

The prior constructive modules remain necessary:

```text
Control:       physical path lift/erasure, exact ports and reversed paths
Decomposition: recursive AL source order and empty before-region
Blocks:        method ownership, register identity, store isolation,
               local parent dependency and collected internal frontier
Admission:     32,224 finite concrete-FULL C2 projection cells
Guidance:      metadata-only ND arms and complete actual AND binding
Geometry:      prefix coverage, no NORMAL widening, bounded finite image
Restriction:   finite shortest safe cut, metadata, coverage, idempotence
Feedback:      internal next-body sink requires the third consumer
Discovery:     exceptional backward reachability, unchanged raw forward
               graph and no new route from a normal backward start
```

These give separate control and approximation results. Exact source
order is not a proof that new C5 boundaries preserve same-run findings.
The selected rule can defer a finding and must keep its refinement route.

## 3. Existing discovery contract and native evidence

The current JVM backend uses `JIRExitWiredGraph` only to build the backward
graph. It wires non-exiting nodes to the exceptional exit before reversing.
Backward ZERO starts at normal and exceptional exits. The proposed block
view must retain these edges without adding any forward return path.
The ordinary reverse-port certificate covers physical edges; it is not
permission to discard the existing discovery overlay.

`Discovery` defines a supplied raw graph, distinct normal/exceptional
exits and a dead-node classifier. Its path witnesses are Type-valued.
It constructs a backward path from an appropriate exit to every node,
given the classifier's exiting-path certificate. A dead node has an
explicit one-edge witness from the exceptional exit. Forward remains the
raw graph. Since the exceptional exit has no incoming backward edge,
any path from a different start strips to an existing raw-reverse path.
In particular, normal backward starts gain no path. The model does not
claim that all facts entering an exceptional start are ZERO, or add a new
DATA filter to the existing backend.

Four native controls pass on the unchanged runtime. Two existing graph
controls check exact edges and exit starts. The existing nonreturning
worker control completes **run-3** in GROUP. A new FULL source/read/sink
loop with no forward leave also completes **run-3**, reports one sink,
and visits neither original exit in forward runs. See the embedded
[native evidence](lean/proposals/loop-fragments-and-demand-collapse-20261102/controls.md#existing-backward-discovery-with-no-loop-leave).
These controls verify the existing machinery, not an implemented block
adapter. That adapter must still route the same edges to the correct
block control scope and physical instruction.

## 4. Builder and native adapter correspondence

The proposal gives a finite SCC builder and a certificate checker. For a
cyclic component, repeat edges are existing incoming edges to its selected
headers. Removing at least one current edge makes the recursive measure
smaller; AL also removes the selected component's vertices. Deterministic
ordering gives stable IDs. The checker must establish the finite partition,
ports and local acyclic rank used by Control/Blocks. This is an algorithm
and validation obligation, not a claim that the current Lean package has
proved Tarjan's Kotlin implementation or the proposed entire builder.

The native full-AP correspondence tests must establish:

1. C2/C5 use the correct immutable scope and direction. Each C5 image comes
   from a complete row, with its own existing exit-relative budget. Apply
   FLOW normalization first and the public-base filter at root only; local
   block conclusions can name original local registers.
2. Saved application uses current native/reversed/MUST and typed-Target
   laws, without hypothetical source/rule/static/report effects.
3. The observation includes all independent images, full annotations and
   exact consumer scopes. Ordinary Facts equality omits protection; the
   observation signature must carry it explicitly. No first-success shortcut
   discards another image.
4. Scalar packet selection clips and retains each membership annotation
   before observing, then uses existing protection transport for a cut and
   merges results with the existing exact annotation-aware union.
5. Loop outputs are gated before repeat/leave retention and subscriptions.
   In-loop instruction transfers keep their existing global limit.
6. Real calls resume the waiting block; physical method/site, aliases,
   sources and report IDs remain unchanged.
7. Static joined binding traverses valid local parents before real callers,
   before release. The run-2 shared carry and lazy completion reach internal
   scopes. Later demand lookup is local. No raw closure is retained.
8. Freeze exports all selected scoped rows. Method frontier aggregation
   cannot hide internal refinement, and no raw local MAY is an extra stop
   permission.

Run these controls before the fixed project campaign. Keep the no-loop
path as the current implementation, so its behavior is not justified by
a new decomposition assumption. The repeated-read, internal source/sink,
port-specific kill/source and two-loop recursive-AL controls in proposal
section 12 are required end-to-end tests.

## 5. Work claims and limits

The direct-consumer geometry model gives an eight-to-two image witness
for binary paths. The reference scalar selector makes at most d-1 proper
positive prefix trials for a depth-d input. Cache the raw observation once
within the call. This is the same fixed function as repeated raw lookup;
it changes evaluation work, not the selected result.

No theorem here guarantees a twofold project speedup, bounds the number
of method inputs, or proves whole-driver convergence. A useful path can
require a raw fallback. New block boundaries can add work. Measure actual
path images, call subscriptions, local delivery, saved replay and observer
cost, at the latest reached/completed/accepted run iteration.

The [checker receipt](lean/proposals/loop-fragments-and-demand-collapse-20261102/checks.json)
authenticates the exact source inputs and scoped local models. Its flags
explicitly distinguish local kernel checks, native fixtures and unverified
production correspondence. No analyzer runtime file is modified by this
proposal or these proofs.
