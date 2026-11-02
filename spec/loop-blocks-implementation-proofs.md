# Loop-block implementation: proof dossier

Date: 2 November 2026. The selected boundary corrections have checked local
models and pass 2,369 common and 453 JVM tests. The source-pinned receipt
records this native gate; it does not prove the Kotlin/AP adapters or project
quality. The latest project campaign is historical: OWASP completed
**run-5** before these corrections with 51 missing baseline sink identities.
A fresh project campaign is required.
Proposal section 6.1 uses existing exceptional-exit backward discovery.
The selected compatibility hack also lets a reached backward exceptional
ZERO apply the normal-exit paired control demand. It adds no new start.

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

Typed Targets keep their normal-exit conclusion boundary. The explicit
exceptional-ZERO lookup in section 3.1 is the only additional control
admission rule. Other matching and publication rules stay unchanged. Targets
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
ExceptionalControlDemand:
               reached exceptional backward ZERO borrows complete normal
               control rows; no other input or boundary gets that lookup
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

### 3.1 Selected normal-demand borrowing rule

The change is explicit: the old lookup reads the reached boundary's own
demand. The new lookup also reads the normal-exit control demand when
the actual invocation is backward ZERO at the exceptional exit. It keeps
Target conclusions at the logical normal exit. It does not move a Target
to an arbitrary physical ingress or wait for a normal loop return.
Only selected DEMAND Target guidance enters this borrowing rule;
NormalTarget remains ignored in backward analysis.

`ExceptionalControlDemand.lean` has 35 constructive theorems and 61 audited
explicit definitions/theorems. Each `Invocation` contains a Type-valued
path in the existing directed graph. There is no function that creates
an invocation from demand alone. `continueAlongExistingPath` appends a
supplied existing path to that actual reach witness.

The checked laws are:

| Property | Executable model/proof |
|---|---|
| Exact scope | Borrowing implies backward direction, ZERO input and the actual exceptional location |
| Unchanged other lookups | Forward, non-ZERO, normal and other boundary invocations return their ordinary rows |
| Complete row retention | The selected rows project exactly to `ordinary ++ normal` under the guard; no endpoint or annotation changes |
| Paired publication | One retained row must admit ZERO and satisfy that same row's required exit |
| No unpaired DATA permission | A DATA entry does not admit ZERO; an incompatible paired exit rejects publication |
| Actual reach | An invocation carries its path; continued routing needs a path in the same existing graph |
| No new forward edge | The forward graph remains the raw graph |
| Target boundary and witness | Terminal publication retains its reached physical sink and supplied witness kind, with the normal exit as conclusion |
| No-return example | The finite loop publishes that terminal endpoint, has no path from its sink to normal return, and uses an explicit existing exceptional discovery path |
| Required handoff address | A witnessed borrowed backward ZERO DemandTarget uses the normal invocation address in outgoing handoff metadata only |
| Unchanged payload | This metadata change preserves the complete paired row, original, Target kind, block identity and annotations |
| Unchanged other records | DATA/native, NormalTarget, non-ZERO Target and unborrowed rows retain their exact address and payload |
| Later continuation witness | With the existing scalar cut and four reads, the four-field source remains DEMAND at forward limits 1/2 and resolves at limit 4; an absent discovery port stops the finite run-3 continuation |

The row payload is opaque beyond its typed endpoints and annotations.
The model proves preservation of a complete row, not all AP C2/C5 cells
or the correctness of a Kotlin scope adapter. `normalWitness` is a supplied
callback annotation; the model does not prove the source/sink rule that
produced it. Borrowing cannot change that annotation.

`BorrowWitness` stores an actually admitted normal row and its ZERO
admission proof, together with the backward exceptional guard. Only the
handoff metadata function consumes this witness. A live/current Target
does not change scope. The outgoing paired payload is an unchanged value;
the function neither projects an AP endpoint nor forms a product of rows.

The required address trace is:

```text
R2 live:        entry=d,          ZERO -> DemandTarget, exit=ROOT_ENTRY
R2 handoff:     entry=ROOT_EXIT,  ZERO -> DemandTarget, exit=ROOT_ENTRY
F3 control:    entry=ROOT_ENTRY, (Target, ZERO),        exit=ROOT_EXIT
```

Here `d` is an actual backward discovery port absent from the forward
graph. The same law is needed at run-4 to retain the run-5 control route.
The finite `sourceFFFF` witness uses `Geometry.project` and four ordinary
field reads. It checks forward run-1/3/5 limits `1/2/4`. It proves this
continuation example, not whole-driver convergence or all AP source
permissions. The native deep-loop control must also verify source
permission at run-3 and run-5 and the final physical sink finding.

The local-model checker can run while runtime implementation changes:

```sh
python3 spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/check.py --model-only
```

This writes `model-checks.json`, with runtime source-pin validation marked
`NOT_RUN`. It does not replace `checks.json` or claim that production is
verified. The final full check must refresh and verify the reviewed source
pins after the implementation is stable. Native controls must still check
actual exceptional reach, normal-exit Target storage, unchanged DATA/native
physical ports and rejection of a DATA or non-exceptional lookup alias.

### 3.2 Existing static-shortcut paired publication

This adapter uses the existing static shortcut, not the exceptional-ZERO
admission rule. The complete witness is a registered run-1 local W row:

```text
producer: (block, entry=p), ZERO -> C.f.[any]/T, exit=STATIC_SHORTCUT
reverse:  (block, entry=STATIC_SHORTCUT), C.f.[any]/T -> ZERO, exit=p
actual:   reached run-2 STATIC original C.f.[any]/T -> DemandTarget
```

The source was visited through the supplied backward CFG. Its physical
source callback supplies the source permission; the adapter supplies no
source hit or initial. To publish its terminal result, select the registered
shortcut's exact output `p`, retain the complete reversed row, and invoke
the existing paired restriction with raw ZERO. A lazy B path can connect
the W static endpoint to the actual static original. The resulting path
must still start at a registered ZERO-origin W row. A carried static fact,
a terminal reader, or an unrelated normal demand supplies no such witness.

This instantiates the existing `Protocol.publication_requires_complete_row`
law: the witness keeps its whole original and actual output, and its
existing row predicate accepts the terminal ZERO. No endpoint product is
formed. `Protocol.no_rows_no_publication` explains the negative case when
no matching W derivation exists. The finite model is parametric in that
row predicate; it does not claim to prove the full AP/static graph matcher.
Native controls must establish that correspondence, including rejection of
another port, mark, block and a non-ZERO writer origin.

C2, ordinary AP intersection, DATA/native ports and Target handoff metadata
do not call this adapter. Its guard also requires run-2 backward mode and a
concrete STATIC original. Thus it cannot grant another input, affect a
later-run lookup, create a forward edge or change NormalTarget behavior.
The existing normal Target-to-ZERO control view can then admit the next
forward invocation from the selected outgoing terminal row.

### 3.3 Selected boundary-span coverage correction

The complete observer must use a summary of the actual adjacent span.
[Ownership section 6.1](method-owned-loop-blocks.md#61-required-coverage-of-an-original-method-boundary)
requires that span to include the original entry or exit transfer when it
reaches that boundary. The pre-correction adapter omitted this transfer. Thus the
kernel results conditional on a complete observer do not establish this
adapter's completeness. Native entry-prefix and exit-suffix controls
reproduced that gap; their no-feedback controls passed. The array-element and
named-field prefix controls fail alike. See the
[gap report](../docs/reports/bidirectional-loop-boundary-source-gap-20261102.md).

The required entry relation has the genuine pre-rule original and both
control ports. For a NORMAL entry source `ZERO -> request/MUST/T`, ordinary
composition with the before-region FLOW relation gives
`ZERO -> cookies/MUST/T`. Its eligible native reverse can discharge an
actual marked suffix to ZERO and use the existing backward ZERO-to-Target
typing. Its native forward replay needs no fresh source hit: it reuses an
already inferred NORMAL producer. This does not authorize a new source.

The symmetric requirement is important. A reverse suffix that includes
the actual exit sink can infer a NORMAL `ZERO -> x.f.$/T`. The existing
backward-ZERO exception selects this row as forward guidance, rather than
persisting it as a native backward record. Forward C2 then has the real
suffix consumer before the actual exit sink executes. A correction that
retains only NORMAL entry records does not cover this suffix or a DEMAND
entry producer.

The standalone
[EntryPrefixNativeRecords model](lean/proposals/loop-fragments-and-demand-collapse-20261102/EntryPrefixNativeRecords.lean)
has 54 constructive theorems. Its separate
[receipt](lean/proposals/loop-fragments-and-demand-collapse-20261102/EntryPrefixNativeRecords-check.json)
records a direct Lean check and the axiom audit. The module is registered
in the main model checker. Its model-only result does not verify current
production source pins or the native adapter.

| Finite law | Model result |
|---|---|
| Genuine span composition | Entry GEN followed by BL FLOW equals its pre-entry-to-loop relation; native forward and reverse replay agree with the two-segment transfer |
| Native cached producer | NORMAL replay preserves the actual waiting original and creates no new source hit |
| Wrong interface | A relabelled post-rule premise, disconnected port or unrelated control boundary cannot stand for the entry source |
| Whole-method difference | Real exit mark removal and public-base filtering can remove a result that belongs in the shorter internal prefix |
| DEMAND producer | A deep bounded or grouped producer stays DEMAND, is not a native NORMAL record, and uses its complete ordinary handoff pair |
| Existing finite C2/C5 cells | A same-prefix concrete MAY carrier remains DEMAND; the full mark, actual original and both ports remain required at terminal publication |
| Symmetric suffix | A backward ZERO-origin NORMAL suffix uses the existing handoff exception; its definite forward carrier can reach the actual NORMAL exit sink |

This model is finite and unary. It covers named and element field paths,
one finite group binding, the stated concrete C2/C5 cells and ordinary
native replay. It does not prove the full AP MUST residue, exclusions,
aliases, actual deep-source execution, complete ND rule execution, whole
GROUP coverage or Kotlin correspondence. Its suffix law assumes that the
genuine eligible suffix row exists. It does not establish run-1 scoped
Target ownership, the paired guidance interface for a new boundary span,
or complete recursive ancestor coverage. A root-completion export alone
does not discharge those obligations. Complete ND execution remains
the unchanged runtime contract; unary restriction guidance is not its proof.
The correction adds no evaluator, raw snapshot, source permission, field
policy, C2 rule or boundary alias. Native end-to-end controls and a final
source-pinned correspondence review remain required before accepting it.

### 3.4 Selected nearest-boundary terminal ownership

Publish the reached Target or run-1 static result at its nearest block
boundary, then use ordinary complete parent application. Keep an admitted
row at every selected ancestor. This supplies local handoff guidance at
the scope where the following run needs it. A root-only terminal does
not supply that local permission. Retain internal static/static rows and
apply their existing public erasure only at the method root; the complete
static seed remains there.

The constructive
[NearestBoundaryTerminals model](lean/proposals/loop-fragments-and-demand-collapse-20261102/NearestBoundaryTerminals.lean)
checks this composition contract. Its per-module
[receipt](lean/proposals/loop-fragments-and-demand-collapse-20261102/NearestBoundaryTerminals-check.json)
is also included by the registered model checker. Its kernel result is
separate from the source-pinned implementation/native receipt. The model
uses supplied, already matched bindings from the ordinary applicator.
It does not replace AP matching by independent unary execution.

| Obligation | Constructive result |
|---|---|
| Nearest ownership | The first row has the actual nearest scope, original and both control ports |
| Adjacent composition | Every successful step has one complete matching interface and the actual immediate parent |
| Ancestor coverage | A Type-valued `Lift` contains each actual application; its executable row list retains nearest and final rows for every finite chain |
| Semantic payload | Every step and finite chain keep the Target/report ID, static payload and annotations |
| NORMAL discipline | Any DEMAND member or offered DEMAND rejects NormalTarget application; complete NORMAL bindings can produce the method ZERO report |
| Complete ND | All distinct required members must match; a missing or repeated single member cannot replace another member; every contributing original is retained |
| Exact handoff | Selected DEMAND handoff reverses both genuine ports and keeps the complete paired payload |
| Root-only erasure | Internal static/static rows remain available to parents; only the public row becomes a complete static seed |
| Static phase | Raw `STATIC_SHORTCUT` survives every adjacent ancestor application; only it invokes the real exit; a completed `ROOT_EXIT` row uses metadata-only finalization |

The typed static-phase laws separate raw `STATIC_SHORTCUT` output from
completed `ROOT_EXIT` output. The raw row reaches root through the same
ordinary complete bindings. The actual exit handler supplies the semantic
result and changes only its output phase to completed. That result cannot
select the handler again, regardless of its STATIC base or local initial.
Exact handoff reverses the typed raw pair; it does not alias that port to
the operation-local `ROOT_EXIT` input or to an ordinary AL/J output. This
finite dispatch/transport model does not prove the physical handler's
implementation. The native exit-once control must establish that mapping.

The earlier per-physical-ingress alternative that removed the root
branch-union false positive is withdrawn. The selected common normal
loop exit and AL ingress retain that accepted false positive. The finite
model keeps every actual contribution and canonicalizes its normal join
owner only. It accepts the complete mixed normal-leave example, still
requires all ND members, and keeps exceptional, return, feedback and
discovery contributions outside this normal alias. Ordinary non-normal
scope rules remain in force.

[CanonicalLoopExit](lean/proposals/loop-fragments-and-demand-collapse-20261102/CanonicalLoopExit.lean)
adds 41 constructive control laws, checked by its separate
[receipt](lean/proposals/loop-fragments-and-demand-collapse-20261102/CanonicalLoopExit-check.json).
Its labelled shared-exit split erases to the original physical edge.
Stored rows keep their actual route when their join identity is shared;
opposite-direction native/demand reads reverse both physical endpoints.
Reverse refinement retains all real normal predecessors of the actual
boundary, while excluding other continuations and non-normal routes.
This is a control contract, not proof that a representative port alone
contains enough information. The runtime must preserve or reconstruct
these labels; a blind all-target dispatch is not justified by it.

The module also checks an executable normal-tail extension certificate.
It retains the original graph, headers and feedback edges, keeps the real
join outside L, checks exact normal reachability before that join and
rejects another normal exit inside the body. Every checked normal outlet
targets J. A supplied rank strictly increases on each internal edge after
the original feedback cuts. A Type-valued path therefore cannot form a
new cycle, and the checked instruction set has no duplicates. The branch
fixture expands SCC `{1,7}` by `{2,3,4,5}`, leaves J=`6` in AL and retains
both actual incoming tail edges in reverse. The finite negative controls
reject an extra cycle and two unmerged normal exits; the no-normal-leave
control adds no edge.

These laws verify the certificate, not the Kotlin postdominator search,
Tarjan implementation or the search's nearest-candidate ordering. The
runtime builder must check that correspondence and report a missing
certificate rather than introduce an unselected control approximation.

The context certificate also permits a real enclosing header outside the
current recursive region as J. Inner own feedback is still a repeat;
ancestor feedback can be normal relative to that inner loop. Only the
classification view changes. Actual ports, endpoints and feedback owner
remain intact, so the parent restores its outer repeat role. The finite
witness expands inner `{2,3}` by `{4,5,6}` up to outer header `1`, keeps
header `2` and repeat `3 -> 2`, and has an empty inner AL. A native reverse
still uses the original outer-feedback edge. Exceptions, returns and
discovery remain outside this normal alias.

This proof covers terminal ownership, matched application and collection
on a supplied ancestor chain with finite AP payload representatives.
It does not verify the AP applicator, physical boundary rule order,
root-original-dependent metadata, arbitrary CFG decomposition, the
Kotlin adapter or whole-program convergence. Existing entry-prefix,
exit-suffix, complete same-entry ND and nearest-static native controls
remain required. Their source-pinned result must be refreshed after the
adapter is complete.

### 3.5 Static-boundary input correlation

The reserved run-1 normal-exit continuation can have an outer
`C.f/FLOW -> C.g/FLOW` link and an inner canonical C.g initial. Its actual
C.g/T mark request must reach that original input through the registered
identity continuation chain. The existing input request service then
materializes the actual C.f/T answer. Forward that marked C.g/T value
through the existing continuation path under a C.g/T local initial;
retain C.f/T at the waiting outer link. The ordinary C.g/T-to-ret/U row
can then compose to C.f/T-to-ret/U. This is not evidence that C.f has T
merely because another writer supplied C.g/T.

The
[StaticBoundaryInputRelay model](lean/proposals/loop-fragments-and-demand-collapse-20261102/StaticBoundaryInputRelay.lean)
has 18 checked theorems in its separate
[receipt](lean/proposals/loop-fragments-and-demand-collapse-20261102/StaticBoundaryInputRelay-check.json).
Successful requests name the actual root link and original field. A
checked identity hop strictly decreases the scope depth and keeps the
same image field. The finite reply witness retains the outer original
and canonical inner basis, rejects another field or mark, and composes
the existing leaf relation without evaluating another rule. Concrete
inputs, missing mark requests, other scopes and other operation sites
do not use this relay. The original point pool interest remains present
and writer registrations do not change.

The late-input witness registers a new root link before queuing the real
point. Its fresh request snapshot therefore sees both old and new links,
even when the initial was already admitted. No seen/history set crosses
calls. This formalizes the event-order requirement; it does not verify a
Kotlin callback or scheduler. Existing native static materialization,
exact geometry matching, protection and layer transport remain adapter
obligations. The nearest-static native control must establish the genuine
C.f/T-to-ret/U dependency before any explicit root replay.

The full driver control also requires complete existing exit-rule
lowering: static `ContainsMark` has its MarkInput operation and keep
transfers. A real ZERO-reached normal exit in AL/J creates an ordinary
static consumer and a genuine J-to-ROOT_EXIT reader/source row. That
row reverses to a paired ROOT_EXIT-to-J obligation. The private
ROOT_EXIT-to-ROOT_EXIT operation row alone cannot satisfy that full-span
obligation; rejecting its mismatched port is correct. No model authorizes
port aliasing, a C5 bypass or a new seed to repair incomplete metadata.
The focused faithful driver control completes **run-3** with the required
NORMAL caller Target. Full-suite/native source-pin acceptance remains
separate from that focused result.

### 3.6 Existing ordered method-exit metadata

[MethodExitMetadataEffects](lean/proposals/loop-fragments-and-demand-collapse-20261102/MethodExitMetadataEffects.lean)
has 23 constructive theorems in its separate
[receipt](lean/proposals/loop-fragments-and-demand-collapse-20261102/MethodExitMetadataEffects-check.json).
An abstract ordered scanner appends every Holds part and updates an
arbitrary join/report state. Induction proves that its full annotated
part list equals the pure `filterMap` of the same immutable check in the
same literal order, for every prior state. An incomplete ND guard can
therefore change report firing without changing the parts. The model
also checks the legacy TRUE branch, the base/mark-index order, repeated
patterns and the empty FALSE index.

Equality of the ordered part lists gives equality of the existing
`without` fold. Applying the same later entry-mark removal proves the
same DATA result under the restored complete method original. The
finite examples show both wrong-original directions: a non-ZERO local
initial misses a real method-ZERO removal, and local ZERO can remove a
value whose true method original is non-ZERO. Backward adds no forward
global-drop mask; its existing entry-mark metadata still applies when
present. Run-1 keeps its existing entry-mark-removal exception.

The legal mixed EXACT/ANY witness has DEMAND layer, empty E and ANY
header, with both memberships at C.f. The original checks at C.f.g and
C.f select `[ANY]` and `[EXACT,ANY]`. Removing the first mask leaves an
EXACT-only tree whose header is canonical MUST. The second original ANY
mask then has a different header and cannot remove that survivor. Reversing
the masks or replacing them by their union instead removes everything.
The model keeps protection coordinates and layer checks explicitly.

The ordered-list theorem is generic in the part and state types. The
checkMark and header examples are finite FULL/valid-TAINT projections;
they do not prove the complete AP tree algebra or Kotlin callbacks.
Actual primitive matching, selection from the post-composition value,
fully annotated masks and root-original binding remain correspondence
obligations. No mask-distribution law, boundary rule evaluator or extra
report/source/request effect is selected.

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
   Its adjacent span includes the original entry/exit transfer when that
   span reaches the real boundary, as section 3.3 requires. Neither an
   after-rule record with a relabelled original nor a full public method
   record is a substitute for that span. Test both directions and both
   NORMAL-record and selected guidance paths.
3. The observation includes all independent images, full annotations and
   exact consumer scopes. Ordinary Facts equality omits protection; the
   observation signature must carry it explicitly. No first-success shortcut
   discards another image.
4. Scalar packet selection clips and retains each membership annotation
   before observing, then uses existing protection transport for a cut and
   merges results with the existing exact annotation-aware union.
5. Loop outputs are gated before repeat/leave retention and subscriptions.
   In-loop instruction transfers and actual local summary results keep
   their existing global limit. Native application can append a caller
   suffix, so apply that limit before a parent ChildResult or standing local
   input retains the result. Growth uses the stored summary shape before
   this cap. The pure saved-row observer instead keeps exact native
   composition followed by paired enclosing C5. Reached child completions
   use lazy one-point ScopedEdgeStore instances, so W3, protection, packing
   and output deduplication use the existing implementation.
6. Real calls resume the waiting block; physical method/site, aliases,
   sources and report IDs remain unchanged.
7. Static joined binding traverses valid local parents before real callers,
   before release. The run-2 shared carry and lazy completion reach internal
   scopes. Later demand lookup is local. No raw closure is retained.
   A raw run-1 static shortcut W row ending at STATIC_SHORTCUT retains its
   reverse Target-result permission at its exact former entry port. The
   adapter must find a registered ZERO-origin W/B derivation and apply the
   existing complete paired restriction. It must reject another output,
   mark, block, ordinary normal-demand-only row, carry-only permission,
   non-ZERO W origin and later runs. It adds no C2 or DATA/native alias.
8. Freeze exports all selected scoped rows. Method frontier aggregation
   cannot hide internal refinement, and no raw local MAY is an extra stop
   permission.
   Every external owner callback that adds local delivery work must secure
   the original method's counted Work reservation, including a static
   boundary reply whose concrete initial is already admitted. A duplicate
   initial is not evidence that no fresh link delivery exists. Joined
   static guidance remains read-only with respect to live actor queues.
9. The exceptional-ZERO adapter applies only at an actually reached
   exceptional boundary. It borrows complete normal control rows and keeps
   their paired publication test. It adds no direct start, demand scan,
   source permission, forward edge or all-entry Target alias.
   Its selected ZERO DemandTarget handoff records use the borrowed normal
   invocation address. DATA/native and live/current Target scopes remain
   physical; NormalTarget and non-ZERO rows never use this remap. The
   four-field nonreturning control must keep its run-5 continuation.

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
production correspondence. A local model receipt is not a production
verification result. Implementation and native validation are separate.
