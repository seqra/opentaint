# Loop fragments and demand-guided feedback

Date: 2 November 2026. Status: selected design with scoped local proofs.
No analyzer implementation is changed. Section 10 states the integration
proofs required before runtime implementation.

Use [proof-guide.md](proof-guide.md). The constructive models are in
[the proof package](lean/proposals/loop-fragments-and-demand-collapse-20261102/README.md).
The [proof dossier](loop-fragments-and-demand-collapse-proofs.md) separates
kernel results from the AP and runtime adapters that remain necessary.

The reviewed implementation is `821375610`. Its analyzer bytes are those
measured at `86ad3b70b5b834d60bc0fe96a91091174265c827`. This specification
extends [demand-relative summary restriction](demand-relative-summary-restriction.md),
[the AP spec](ap.md), and [exact DEMAND admission](demand-layer-exact-initials.md).
Their other rules remain in force.

## 1. Problem and selected scope

The current method owner stores results after each processed instruction.
A loop can construct many different field paths. A new path is not an
ordinary duplicate. It can traverse the body again and create new input
memberships at in-loop calls. The summary gate acts later, at method
summary admission.

The measured reference reaches Conductor **run-6**, with run-5 complete
and accepted, and Stirling-PDF **run-8**, with run-7 complete and accepted.
Conductor's remaining run-6 and Stirling's run-6/run-8 are dominated by
calls and saved replay. These measurements motivate this design; they do
not prove that every path was created by a local loop.

The design has four parts:

1. Let the method analyzer build a transparent tree of sequential and loop
   blocks. It owns all block stores and routing. Blocks share the original
   method registers; they are not generated methods. Apply decomposition
   recursively for nested and multiple loops.
2. Replay persisted summaries with the existing call machinery. Do not
   add a separate NORMAL reachability service.
3. Classify the applied body summary. Check demand only if its conclusion
   has more counted fields than its premise. Use `FL(Zero) = 0`. Equal
   and shrinking summaries propagate their results without this new gate.
4. For a growing summary, check after-block demand, enclosing-B
   demand after saved after-block composition, and next-body demand.
   Keep the union of their needed bounded images. Drop a result only if
   all three consumer families reject it.

These are explicit major changes:

| Part | Current behavior | Proposed behavior |
|---|---|---|
| Analysis units | One owner and one set of method stores | One method owner with a tree of block-local stores and continuation ports |
| Loop state | Distinct paths circulate through the original body | Traversal transfer is shared through internal block summaries |
| Cyclic admission | Ordinary global limit and post-S deduplication | Growing body summaries use the loop-output gate on repeat and leave; other summaries bypass it |
| Usefulness | Persisted replay, then demand and current subscriptions | Reuse that machinery; use AL admission and full-B exit intersection for growing loop outputs |
| Precision | Existing real-method C5 boundaries | Additional block boundaries and loop-output cuts can create DEMAND earlier |

Exact CFG splitting is not a proof that the bounded analyzer is invariant
under splitting. New C5 and loop-output boundaries can postpone a NORMAL
record or finding. They must retain the refinement needed to resolve the
path later. No same-run finding-set equality or general convergence claim
is made solely from control equivalence.

## 2. Behavior that remains unchanged

Keep:

- Existing AP input-to-output summary semantics. All internal blocks use
  the original method register IDs. Do not add a state object, private
  argument registers or an output-binding protocol.
- Original instructions, locations, rules, rule occurrences, GeneratedMark
  identities, alias information and semantic method context.
- Field reads/writes, cleaners, exclusions, mark transfer, primitive
  handling, source permissions and complete ND bindings.
- The current global field limit inside one body execution.
- Existing C2 and exact paired C5. Geometry compatibility does not grant
  permission to publish a summary.
- FLOW normalization, FLOW-backed replacement and protection transport.
- NormalTarget's NORMAL-only forward application, backward exclusion and
  already-persisted row suppression; DemandTarget's existing protocol.
- Immediate source/sink/static operation effects at their original points.
  A normal function return is not required to observe an in-loop sink or
  supply a mark at a static write.
- FULL acceptance mode, the existing GROUP limitations, positive limits,
  and the schedule `1,1,2,3,…`.

Real method entry/exit rules execute only at the original boundaries.
Internal block entry, completion and loop dispatch do not execute another
copy of those rules. There are no synthetic configured call sites.

Do not add grounding support, a new field-validity test, a raw-summary
fallback, a hidden cross-layer merge, or a new permission for ZERO.

## 3. Method-owned decomposition

[Method-owned loop blocks](method-owned-loop-blocks.md) defines the complete
ownership, storage and transition protocol. It replaces generated functions
and synthetic calls in the earlier proposal.

The method analyzer initializes an immutable block layout before its first
input. If the graph has no loop, keep one sequential root and the existing
execution path. Otherwise, build a tree:

```text
Sequential B
  Sequential BL
  Loop L
    iteration region, recursively decomposed when needed
  AL: remaining region, recursively decomposed
```

AL can contain a deep hierarchy. For `prefix; loop1; loop2; suffix`, the
root is `B1 = (prefix, loop1, AL1)` and
`AL1 = B2 = ({}, loop2, suffix)`. Thus loop2 is under AL1, not a sibling
of loop1 and not inside loop1's iteration body. Every continuation check
uses the complete AL region's demand and saved summaries. See the exact
tree and per-level checks in [the ownership spec](method-owned-loop-blocks.md#3-the-block-tree-and-the-control-graph).

The tree describes containment. Original CFG ports describe execution.
The method analyzer routes a loop result to L or AL in forward analysis,
and to L or BL in backward analysis. It restricts growing results at the
loop output before either route. Equal/shrinking results bypass that new
gate. The actual exit port remains attached; a successful consumer check
does not change repeat into leave.

Sequential regions can contain branches. For general CFGs, retain all
original entry/exit ports and return/throw/handler destinations. The two
principal route categories are not a limit of two physical edges. Keep
multi-entry and nested-loop ports distinct. Every local cycle crosses a
loop boundary, including a one-node self-loop.

Block IDs are deterministic paths under the original method. Reuse one
layout across directions and runs. They are not new MethodKeys or prescan
call-graph nodes. Each original instruction belongs to one lowest block;
its ancestors neither execute nor retain a second copy of it.

Port correlation remains necessary:

```java
while (true) {
    if (chooseExit()) {
        c.v = clean();
        break;                  // Leave port.
    }
    c.v = sourceT();             // Repeat port only.
}
sinkT(c.v);
```

The source result cannot be applied to the leave port. The physical write
on that path still kills it under the existing field-write rules.

## 4. Ownership and storage

One original method analyzer owns all block states, drains their tagged
work, performs local summary delivery and exposes the original method's
public summaries. A block has no independent method actor or runner.

Each block maintains:

```text
in-block edge storage: results after its own processed points
summary storage:      admitted local relations, labelled by entry/exit ports
demand mechanism:     frozen local C2/C5 guidance and typed rows
saved NORMAL rows:    persisted local transfers for replay
local continuations:  parent-prefix composition with child results
```

A composite stores child-completion results, not copies of child-internal
instruction facts. Root state is the original method boundary. All blocks
use the same method registers and original alias queries. A transition
needs no argument projection, bind-back rewrite or extra AP field. Shared
register access does not make another block's facts automatically visible.

Block summaries keep local initials. Parent composition keeps the parent's
complete original separately. The public root interface still uses the
original method positions. Local registers do not become public method
arguments merely because they can occur in a block-local initial.

CFG fast delivery stops at block boundaries, so it cannot bypass the loop
gate. Deduplication still stores a result at its processed point before
successor delivery. Pending local summary work contributes to the method's
existing work reservation and barrier.

At handoff, persist NORMAL and selected demand rows in their block scopes,
with stable IDs and ports. Keep internal guidance as well as root guidance.
Statics, rules and real method exits keep their original method ownership;
block exits do not run copies of real method exit rules.

## 5. Body-summary shape

Classify a body summary before applying its field suffix to a caller fact.
Use the AP count of concrete, counted accessors. Uncounted accessors stay
uncounted. For this classifier, define:

```text
FL(Zero) = 0
FL(DATA path) = number of counted concrete fields in that path
needsLoopCheck(I -> C) = FL(C) > FL(I)
```

This is a local definition for loop-summary shape. It does not change
ZERO matching, initial emission, ZERO routing or paired C5. ZERO does not
become a DATA root or a wildcard. Targets and other typed control outputs
keep their existing protocol; they are not DATA paths to cut to MAY.

```text
Body summary                 Shape              Loop-output check
Zero -> x.f.$/T              0 -> 1             required
Zero -> x.$/T                0 -> 0             bypass
x.f.*/FLOW -> x.*/FLOW       1 -> 0             bypass
x.*/FLOW -> x.*/FLOW         0 -> 0             bypass
x.*/FLOW -> x.f.*/FLOW       0 -> 1             required
```

The strict comparison is on the summary's own premise and conclusion.
It is not a comparison between the caller's full paths, or between two
successive method-entry-to-current-point edges. Check packed path members
separately. A short output must not bypass a check on a different growing
output.

For an ordinary definite suffix application:

```text
summary: alpha.* -> beta.*
input:   alpha ++ suffix
result:  beta  ++ suffix

if length(beta) <= length(alpha),
then length(result) <= length(input).
```

The premise of this statement matters. A MAY ancestor can match a deeper
summary premise provisionally. An equal/shrinking summary can then emit
more concrete fields than that ancestor had. Therefore, bypass does not
prove that every actual fact shrinks. With a fixed finite summary set,
its stored geometry and the unchanged global limit still give a bound.
Equal length also does not bound the number of bases, marks or paths.

### 5.1 ND restriction metadata

Use a unary view of a complete ND summary only for this check:

```text
executable summary:   {I1, I2} -> C
restriction view:     I1 -> C, I2 -> C
```

Classify each arm by its own shape. The union of the arms is conservative
restriction guidance. An arm that bypasses the new check can retain an
already valid full result. A growing arm uses the selected consumer tests.
The executable edge and its complete AND binding stay unchanged. The
view cannot emit C from I1 alone, create a NORMAL edge, or turn an empty
member list into a ZERO premise. When the run direction reverses, orient
each guidance pair with the existing entry/exit rule.

## 6. Existing replay and the three selected consumer tests

In source order, write the enclosing body as:

```text
B := BL ; L ; AL
```

Use `after = AL` forward and `after = BL` backward. Reverse the same
physical ports; do not build a new unrelated hierarchy for backward work.

Enter L through the existing saved-replay/demand policy, as an internal
block transition rather than a generated method call:

```text
onBodyOffer(input):
    replay persisted NORMAL summaries on the complete input
    apply the existing saved NormalTarget policy
    initials = bodyDemand.emitInitials(input)  // existing C2
    if initials is empty:
        return
    replay/subscribe to current summaries and start those initials
```

Run-1 keeps its existing first-run policy. It has no prior demand. Empty
first-run guidance cannot be used to drop all facts.

For each resulting body summary application, retain its actual port.
Both repeat and leave outputs go through the new shape test before their
selected destination is entered:

```text
onLoopOutput(summaryArm, F, actualPort):
    if FL(summaryArm.conclusion) <= FL(summaryArm.premise):
        propagate F unchanged through actualPort
        return

    // after = AL forward, BL backward.
    // Test 1: use existing C2 at the adjacent region.
    images = after.demand.emitInitials(F.conclusion)

    // Test 2: use existing application and complete paired C5.
    for saved in after.persistedSummaries:
        for fullB in composeAtOriginalBindings(F, saved):
            images += B.demand.intersect(fullB)

    // Test 3: the next iteration can contain a required observation.
    images += L.demand.emitInitials(F.conclusion)

    if there is no selected image:
        drop F
        return
    restrict F to the union of all three image families
    route each retained value through actualPort
```

Every consumer uses the same original method register IDs. L C2 is scoped
to the actual next-entry port and direction, with no argument remapping.
Keep F's complete B original separately for composed C5; it is not L's
local initial. L demand is not invented from the result.

The third check is required even when AL has no DATA consumer and B
has only typed Target guidance. Section 8 shows the reason. A positive
result from one family must not hide a different image from another.
An early stop is valid only when no unvisited family can add an image.

`F` contains the complete enclosing-B-entry-to-current-point dependency
after the existing prefix and partial-L compositions. The adjacent-region
composition therefore produces a full B edge. A local L initial premise is not a replacement for
B's original premise. Keep whole ND originals, layers, protection and
semantic context through the ordinary compositions.

Each B test uses one complete paired demand row. It cannot combine the
entry permission of one row with the exit permission of another. The
conclusion limit is the existing demand-relative C5 limit for that row.
A successful geometry test is not summary-publication permission.

A test that hypothetically composes F with AL/BL is guidance only. It emits
no B summary, executes no rule, supplies no static mark and produces no
report. Actual control must take OUT before AL executes. In particular,
a NEXT-only source result cannot report through an exit path whose write
would kill it.

There is no new global NORMAL graph, reverse-query service, rejected-fact
history or growing-graph replay protocol. Persisted replay and current
C2/C5 remain their existing operations. A cached result must include the
owner, direction, port and immutable demand/saved snapshot identities.

### 6.1 Why shrinking summaries bypass the new gate

```java
Node B(Node x) {
    while (again()) x = x.f;
    return x;
}
```

```text
Saved body summary:  x.f.*/FLOW -> x.*/FLOW
Input:               x.f.f.$/T, NORMAL
First body result:   x.f.$/T
AL/end root demand:  not yet satisfied
Second body result:  x.$/T, NORMAL
AL/end root demand:  satisfied
```

The body shape is 1 -> 0. Its first result must continue even though the
consumer rejects it at that point. This uses normal summary application;
it needs no extra reachability query.

## 7. Growing-result restriction

A positive Boolean match alone does not bound path enumeration. In a
backward loop with two field alternatives, all words over f/g can be
compatible with a root MAY consumer. Keeping all complete words leaves
the exponential family in place.

The gate must retain an image needed by each selected consumer, rather
than keep every deep fact that has some overlap. Reuse C2 for admission
and paired C5 for full-B restriction. A lossy value image has:

```text
the same complete original, context and control port
the same full mark, FLOW exclusions and transported protection
an actual retained concrete prefix, then MAY
the DEMAND layer, with empty field exclusion for the cut
```

A result that is not cut keeps its existing tail, layer and exclusions.
Do not add a field absent from the current value. Do not replace the
actual T payload by FLOW merely because a FLOW consumer selected it.
The receiving block emits its local initial through ordinary C2 on the
same method register namespace.
Keep statics' named anchors indivisible and their existing legal grammar.

For a direct concrete consumer, a scoped demand-prefix trie can keep the
requested prefix plus the first distinguishing field:

```text
Demand              Raw value                    Candidate image
x.[any]/T           x.f.g.h.$/T, NORMAL           x.f.[any]/T, DEMAND
x.f.[any]/T         x.f.a.b.c.$/T, NORMAL         x.f.a.[any]/T, DEMAND
x.g.h.$/T           x.g.h.$/T, NORMAL             unchanged
```

A direct trie is not, by itself, a preimage algorithm for AL composition.
A saved field read can remove a prefix that the B exit needs. Transport
that precision through the actual application before cutting F. Preserve
all selected images, including independent paired rows and ND metadata.

The local `Restriction` model supplies an executable conservative reference
for a fixed complete observer: try positive prefix cuts in length order,
accept a cut only when all selected C2 and composed C5 signatures remain
equal, and retain the raw value if no proper cut passes. An empty complete
observer drops the value. This is a proof reference, not a requirement to
replay every AL row for every trial in the production implementation.
An efficient adapter must prove the same preservation contract.

Do not widen a rejected precise fact merely to manufacture an image:

```text
Demand:            x.f.g.[any]/T
Raw value:         x.f.$/T, NORMAL
C2:                no initial
Correct no-match:  drop, if no other selected consumer
Rejected fallback: x.f.[any]/T, DEMAND  // adds a provisional g initial
```

The loop gate runs at a full traversal output, not between its original
instructions. Ordinary reads can cancel fields written within that step.
The existing global limit still applies inside the body.

## 8. Why next-body demand is required

AL and B-end tests alone do not cover every in-loop observation.
The selected third test closes that missing consumer family.
The case matters also for ZERO-source summaries, because
`FL(Zero) = 0`:

```java
void B(Node x) {
    while (again()) {
        sourceFF(x);  // Rule: assign T at x.f.f.$; do not clean x.f.$.
        x = x.f;
        sinkT(x);     // Rule: CM(x.$, T).
    }
}
```

```text
First body source:       Zero -> x.f.f.$/T
First body read result:  Zero -> x.f.$/T
First root check:        no hit
Body return shape:       Zero -> x.f.$/T; 0 -> 1, growing
AL consumer:             no local DATA demand
B exit:                  Target guidance does not admit local x.f/T
L entry demand:          accepts the intermediate x.f/T
Selected gate:           retain its required image for the next body

Next body preserves the old exact x.f/T while assigning at x.f.f/T.
Its read produces:       Zero -> x.$/T
Root check:              NORMAL hit
```

Dropping the first feedback value under the rejected two-test rule loses
the second-iteration observation. The required intermediate DATA value is
not an enclosing B exit value. Applying existing producer effects before
the gate does not help: the sink has not fired on the first iteration.

The native finite-driver control retains the finding at **run-3**. A
separate production-C5 control admits a growing body relation, while B's
paired Target demand rejects the intermediate DATA value. These checks
show that current C5 is not a general reason to declare this shape
impossible. They do not test an implemented outlining pass or gate; those
do not exist yet. The proof dossier records the exact tested scope.

The selected repair is the third check against L demand. It uses the same
C2 mechanism as the AL check. Do not add a separate obligation store,
source permission or ZERO exception for this case. The exact-path model
proves that retaining the L image preserves the second-iteration sink.
Production correspondence still requires the outlined demand/port adapter
to carry that image, as stated in section 10.

## 9. Storage, publication and handoff invariants

Keep results in the store of the processed statement, not its successors.
Apply the loop-output restriction before retaining a new repeat/leave
membership or creating the next current subscription. Existing exact deduplication
remains the final admission test; a different field path is not a duplicate.

Producer effects at original instructions stay before the value gate.
Actual publication still requires ordinary complete C5. All admitted
summaries, NORMAL and DEMAND, use the existing summary restriction. Do not
retain unrestricted candidates or bypass C5 because a loop image is MAY.

Needed uncertainty must reach the block summary or typed Target
frontier. A local MAY value alone does not keep the driver alive. The
proof must account for each relevant cut until its observation is resolved
or rejected. It must not force another iteration for an irrelevant cut.
The next-body case must be included in that argument, rather than treated
as an enclosing B-exit demand.

## 10. Proof scope and validation

The constructive package proves exact finite control routing; explicit
feedback handling; scalar bounded projection; finite concrete C2 cells;
method-owned block isolation and shared-register transport;
whole-original/port retention; separate complete-row publication; ND
metadata separation; the strict summary-shape classifier with ZERO
at depth zero; and the next-body counterexample and its selected repair. The dossier
states each model's scope. A local-model PASS
is not a proof of all AP tails, packed trees, the Kotlin block-layout builder or
whole-driver progress.

The old finite NORMAL reachability model is a reference investigation
only. It is not a selected runtime service. There is no pending decision
about frozen versus growing NORMAL-query graphs in this design.

Before runtime implementation, close the decomposition,
mutable-argument, AP projection, typed-control and refinement-handoff
adapters. Test binary path growth, balanced write/read bodies, repeated
shrinking reads, internal source/sink observations, complete ND binding,
status-specific effects, nested/self/multi-entry loops, exceptions, static
writes before nonreturn and original boundary-rule identity.

After implementation, repeat the selected fixed project configuration.
For each project report the latest reached, complete and accepted run,
engine/barrier times, findings, growing versus bypassed applications, raw
versus projected feedback paths, body work, subscriptions, saved replay,
admitted summaries and outgoing demand. Do not claim a twofold reduction
from a local finite witness or from splitting alone. The present spec
adds no measured project result.
