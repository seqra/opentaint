# Forward internal ZERO control

Date: 2 November 2026. Status: **DRAFT / UNSELECTED**.
Superseded on 3 November by [NORMAL ND contributor retention](normal-nd-contributors.md).
This document does not authorize implementation.
The current analyzer is unchanged by this candidate.

Follow [proof-guide.md](proof-guide.md). The separate
[conditional Lean model](lean/proposals/forward-internal-zero-control-20261102/README.md)
checks the stated interface laws. It is not part of the current implementation
proof package or its source pins.

The measured 6052 attempt completed OWASP **run-5** with 18 missing baseline
sink identities. Conductor failed **run-2**, with run-1 last complete and
accepted. Thingsboard stopped in prescan; Stirling-PDF did not start.
This is not an accepted four-project performance or quality result.

## 1. Decision and semantic scope

The candidate lets an actually admitted method-root ZERO continue through
reached internal blocks in a restricted forward run. This needs both input
admission and output transport. It is a control-policy change relative to
the current block-local filtering. It is not only a technical optimization.
It can run a previously skipped source and restore a finding.

No part of this candidate is selected yet:

| Part | Current behavior | Conditional candidate | Affected proof |
|---|---|---|---|
| Internal ZERO input | Local C2 can reject an actual reached ZERO | Inherit only a reached root-origin ZERO when ordinary C2 supplies no ZERO initial | Root authority, original/layer/port preservation |
| Internal ZERO identity output | Local C5 can reject ZERO to ZERO, stopping control | If ordinary C5 rejects the identity, use a separate live control-only completion | Real-path transport, late-input replay, no AP permission leak |
| DATA input/output | Existing C2 and paired C5 | Unchanged | Same-query DATA and paired-C5 equality |
| Target output | Existing complete witness, layers and paired C5 | Unchanged | Complete ND, NORMAL-only Target, no virtual ZERO pair |
| Source authority | Exact existing source permission and rule condition | Unchanged | No new permission or synthetic source hit |
| Public/native records | Existing matched and classified AP derivations | No bypass-only control record is exported; ordinary valid derivations can still be stored | Record separation |
| Backward/root/callee admission | Existing policies | Unchanged | Direction and boundary guards |

Keep field geometry, exclusions, marks and groups, cleaners, rule selection,
source/sink IDs, CFG edges, aliases, real call handling, stopping criteria
and report deduplication unchanged. Do not add a GroundingSupport label,
DATA annotation or field-sensitive rule to implement this control policy.
Adding a control cache must not change AP fact equality or hashing.

## 2. Terms and existing policy

A method analyzer owns internal sequential and loop blocks. These blocks
share the original registers and method context. A scope identifies the
method, context, block and actual entry port. A completion also has its
actual output port. A canonical normal join uses the existing checked
mapping to real CFG routes.

ZERO is control reach, represented by `Reach`. It has NORMAL or DEMAND
layer. DATA is a non-ZERO fact. It can carry FLOW or concrete marks and
field information. A Target is a terminal result, not a DATA path.
NormalTarget needs a complete NORMAL witness and composes only with
NORMAL input. DemandTarget retains its existing DEMAND behavior.

C2 maps a submitted fact to initial facts allowed by current demand.
C5 restricts a summary with one complete paired demand: its initial side
and conclusion side must both match. Target publication uses its existing
C5 probe with a ZERO/Reach DEMAND exit. These operations remain unchanged.

Run-1 already has its unrestricted entry policy. This candidate applies
only to restricted forward runs, such as run-3 and run-5. It does not bypass
the existing root or real-callee admission policy. Newly reached ordinary
calls can offer inputs and obtain legitimate admissions under that policy.
A method must first receive ZERO under its existing root/call policy.

Backward behavior uses the same policy for the same inputs. Additional
legitimate forward AP rows can change the inputs, method keys and work of
later backward runs. No bypass-only control row is persisted; this does
not imply equal backward inputs or equal work across the modified analysis.

Current internal routing first replays saved summaries, then uses local
C2 for current analysis. Current ZERO identities use ordinary summary
publication and local C5. Thus an empty local ZERO demand can stop an
otherwise reached control path at either boundary.

## 3. Reproduced gap

```java
// Real entry rule: ZERO -> request.$/REQ.
void method(Request request) {
    Cookie[] values = request.getCookies();
    // CM(request.$,REQ) assigns DATA to values.$ and values.[].$.
    String param = null;
    for (Cookie value : values) {
        param = decode(value.getValue());
        break;
    }
    Session session = request.getSession();
    // Active sink-pattern source: type/arity only, ZERO -> session.$/SESSION.
    session.setAttribute(param, "value");
    // Complete AND: CM(session.$,SESSION) AND CM(param.$,DATA).
}
```

These are concrete FULL marks. The specialized taint-source rule for a Cookie array
has exact root and exact element assignments. It is not inherently MUST.
The active `getSession` marker has no entry-REQ or global-static-mark check.
Its condition is the receiver type and zero arguments. It belongs to the
sink-pattern automaton, separate from the source-pattern REQ marker.

The faithful LOOP native control ends COMPLETE at run-3 with no finding;
the same code without feedback reports. Run-2 reaches the real session
source. Run-3 has that source permission and an admitted root ZERO. AL
admits `param.$/DATA`, but rejects ZERO. The call that supplies SESSION
therefore has no current control input. The sink lacks one member.

This conditional candidate does not change backward Target publication
to create another guidance row. It lets the existing admitted forward
control reach the permitted source. The final DATA/Target still needs
its ordinary complete binding and paired C5.

### 3.1 Why admission alone is insufficient

```text
Actual root ZERO, NORMAL, reaches L through the existing CFG.
Local ZERO C2 is empty. Candidate admission starts L with ZERO.
L traverses its body and produces ZERO -> ZERO at the real leave port.
Local identity C5 is empty. Ordinary publication rejects that row.
No control reaches AL; its permitted source still cannot run.
```

A complete candidate must state an output rule too. The model checks this
failing admission-only pipeline. It also checks a real finite path where
the separate control output reaches AL while Target permission stays false.

## 4. Root authority and input admission

All guards below are required:

1. The run is restricted and forward; the boundary is inside one original method.
2. The method-root ZERO has already been admitted by the existing policy.
3. The actual offered value is Reach, not DATA.
4. Its actual offered original is ZERO. Check this explicitly: the runtime
   packet predicate alone does not reject a non-ZERO-origin Reach.
5. The offer comes through an existing reached CFG route or the existing
   empty-block identity, with the same method/context and exact ports.

A global root-ZERO flag plus an unrelated DATA or non-ZERO-origin Reach
is not sufficient. The implementation must show the existing admission,
original and route evidence used by these guards. The proof path witness
does not prescribe a new runtime support annotation.

```kotlin
replaySavedNormally(actualOffer)
val ordinary = lookupCurrentC2(actualOffer)

if (ordinary already supplies ZERO) {
    useOrdinaryAdmissionUnchanged(ordinary)
} else if (isActualForwardInternalRootZero(actualOffer)) {
    addInitial(AdmittedInitial(ap.zero, actualOffer.reach.layer))
} else {
    useOrdinaryAdmissionUnchanged(ordinary)
}
```

Preserve the actual input layer. In particular, do not turn DEMAND Reach
into NORMAL through the intrinsic NORMAL ZERO start fact. The inherited
initial must retain DEMAND. Existing C2 results are not rewritten by this
candidate. DATA C2 and real callee admission use their current path.

Entering a block does not run a method entry rule. Use the existing owning
handler only when the actual span includes the real method entry. Rules,
physical operations and their identities retain their existing order.

## 5. Control-only output transport

First apply ordinary normalization and paired C5 exactly as now. If it
accepts the ZERO identity, keep that existing result, storage, layer and
delivery. Do not replace an accepted result by an unrestricted one.

The fallback applies only when ordinary C5 rejects the raw identity and
all these guards hold:

```text
restricted forward + same-method internal boundary
actual admitted root ZERO + actual offered original ZERO
raw processed summary initial ZERO + raw conclusion Reach
an actual completed path and exact output port
```

Use the raw processed Reach layer. Do not widen or strengthen it. This
identity has no field or mark image. The existing Reach path already bypasses
the DATA loop-observation/cut; do not change that gate. It follows the existing parent link
and route mapping. It does not choose a different continuation, skip an
ancestor or invent a normal leave from a nonreturning loop.

The fallback is a separate **live control completion**. It is not an AP
demand or summary row. A possible interface is:

```kotlin
publishForwardControlExit(scope, actualExit, actualReach.layer)
// Only actual ZERO standing inputs in this scope can consume it.
// The waiting parent retains its complete original and joins input/output layers.
```

The implementation draft can choose its storage, but must keep these
interfaces separate:

| View | May see bypass-only control completion? |
|---|---|
| Live internal ZERO routing and late-input replay | Yes, with all guards |
| DATA C2 or paired C5 | No |
| Target C5 / `acceptsTarget` | No |
| Current AP summary or persistent native-record lookup | No |
| Public inter-method summary/subscription | No |
| Next-run demand storage or stopping frontier | No |

This does not mean final AP stores remain identical after the fix. More
actual control can run a permitted source and infer a new ordinary result.
If that result passes its existing C5 and classification, it can be stored
or persisted normally. The exclusion applies to **bypass-only control
completion records**, not to legitimate new AP derivations.

At the real method boundary, keep the existing actual exit handler,
complete-original metadata and public C5. No fallback grants public
ZERO identity, DATA or Target publication. Actual source/sink/static
handlers can run at newly reached points; the control transport itself
performs none of those effects.

### 5.1 Late links, layers and work

A completed control path must be available to a later actual ZERO input
in the same scope. Reuse the existing standing local inputs. Do not keep
a second raw-input or request history. Exact scope/output/layer cells
and the existing initial deduplication are sufficient for this interface.

A late input keeps its complete parent original. Its result layer is the
ordinary join of the cached output layer and the actual input layer:
DEMAND on either side gives DEMAND. A cached NORMAL completion cannot
upgrade a DEMAND input. An unrelated scope, exit, DATA input or non-ZERO
original cannot use that completion.

Publish-before-input and input-before-publish must give the same delivery.
Repeating either event must not create duplicate result memberships. A
fresh pending delivery must reserve counted method Work even when no new
initial is admitted. Freeze requires all such work to be drained. Release
then clears this live state; it is not handed to another iteration.

## 6. Target, source and ND separation

The following tempting shortcut is invalid:

```text
Add virtual demand (ZERO, ZERO) to let control pass.
acceptsTarget probes C5 with Reach.DEMAND at the exit.
The virtual pair now accepts a Target that had no AP demand witness.
```

The conditional model checks that counterexample. With the separate
control cache, the same empty AP demand still rejects Target. Control
transport does not call or extend the Target permission API.

A source still needs the existing exact method, physical statement,
edge/action identity and source permission. Control cannot add a permission
or synthesize a source hit. A previously permitted source may now execute
when real control reaches it. Its condition, actions and layer rules remain
unchanged.

A sink needs its complete ND binding. NormalTarget needs all contributing
layers to be NORMAL and its usual NORMAL parent application. DEMAND
control must not become a hidden NORMAL member when ZERO is removed from
an ND premise representation. Test this explicitly.

A ZERO-premise Target still requires a complete cube satisfied by
ZERO-premise edges. A mixed ZERO/DATA cube does not get an independent
executable ZERO arm. Restriction metadata remains separate from execution.

## 7. Reference, optimization and conditional proofs

The semantic reference is actual same-method ZERO control traversal with
the guards and ordinary-first rules above. It performs the existing
physical transfers and uses the existing CFG. It does not consult local
ZERO demand to terminate an otherwise valid internal control identity.

The optimization shares one block traversal and its live control exits
between matching actual ZERO inputs. It uses scope/layer deduplication
and late-link replay. This is separate from the semantic decision to
allow that control. It does not prove equivalence to the current failing
C2/C5-filtered behavior.

The [standalone model](lean/proposals/forward-internal-zero-control-20261102/Control.lean)
uses Type-valued existing-edge paths and a root-policy admission proof.
Its ordinary semantic views are immutable inputs to one control operation.
It checks:

| Obligation | Constructive result |
|---|---|
| Root authority | No reached witness can exist under an all-false root policy |
| Original guard | A non-ZERO-origin Reach receives no inherited admission even when root ZERO exists |
| Existing C2/C5 | Existing ordinary ZERO admission and accepted identity C5 disable the fallback |
| Direction/boundary | Backward, run-1 and public admission get no new permission |
| Actual path | Continuation contains an executable path made from supplied existing edges |
| Exact transport | Origin, owner, actual target and both ports stay in the supplied interface |
| Layer | DEMAND root/input/output is never strengthened to NORMAL by control transport |
| DATA and C5 | At the same semantic state/query, adding a control cell changes no existing DATA/C5 lookup |
| Target probe | Empty AP demand still rejects Target; a rejected virtual ZERO pair would incorrectly accept it |
| Records | The control operation creates no AP/native/public record; an ordinary matched NORMAL derivation can still grow the native store |
| Source authority | The source-permission store and exact action-key lookup do not change |
| Complete ND | Missing members and DEMAND members reject NormalTarget; mixed origins do not gain a ZERO arm |
| Late replay | Either event order gives the same result; a fresh late delivery reserves Work and duplicates are suppressed |
| No invented return | A graph with only entry-to-loop and self-feedback has no path to the return vertex |
| Finite control | At most NONE-to-DEMAND-to-NORMAL gives two fresh layer admissions per reached scope |

These are conditional interface proofs. They do not prove Kotlin routing,
all AP matching, source evaluation, scheduler ownership, all inherited
field/mark semantics, or whole-driver convergence. The scope/exit mapping
and actual input proof must be established by the native adapter. In
particular, preserving an opaque view at one operation is not equality
of final findings or stores after additional sources execute.

The direct C2-only counterexample and real-path positive establish that
both admission and output transport are needed. The finite Target probe
negative separates control from AP permission. The late-link model checks
one exact cached cell and matching input; it is not a proof of all current
packed relation, ND or hierarchical scheduling implementations.

### 7.1 Work bound and limit

There are at most two fresh control layer admissions per reached scope.
The same finite layer argument applies to a fixed set of exact control
output cells. This is a bound on control identities, not on source actions,
ND joins, DATA facts, method keys or total CPU/memory. The model constructs
one control admission with any supplied number of source-action slots.

More control can add work compared with the current skipped-block path.
No twofold project improvement or whole-analysis work bound follows from
this proposal. Measure the control admissions/deliveries separately from
the ordinary work they cause. Existing cumulative packet/callback counts
can also change with batching; do not treat them as retained fact counts.

## 8. Native and review gates if selected

Before implementation, select the complete input-and-output contract,
review its major semantic change and finish the model/source correspondence.
Then use red/green native controls. Required tests are:

1. Faithful exact-array/unconditional-session LOOP and no-feedback code
   reach the same physical trust-boundary sink when the real source is permitted.
2. A two-boundary path with no local ZERO identity C5 still reaches AL;
   admission-only is insufficient.
3. No root ZERO admission, no actual route, DATA input and non-ZERO-origin
   Reach each reject inherited control.
4. DEMAND Reach retains DEMAND through local admission, cached identity and
   parent binding; a NORMAL DATA partner cannot make NormalTarget from it.
5. Missing source permission still blocks the source. Empty AP demand still
   blocks an unrelated Target after a control-only completion.
6. Ordinary C2 and C5 accepted cases keep their existing rows and layers.
   Legitimate new NORMAL AP results can persist; bypass-only cells cannot.
7. Cached exit before input, input before exit, duplicate input, duplicate
   exit and an idle-owner late delivery preserve exact results and counted Work.
8. Real callee/root admission and backward exceptional/discovery ZERO remain
   unchanged. No-loop methods retain the previous path.
9. Empty prefixes/suffixes, canonical J with late reverse targets, no-leave
   loops, actual entry/exit rules and the static shortcut keep exact routes.
10. Complete ND, NORMAL-only Target application, ZERO-arm precision, report
    identity and persisted Target suppression retain their existing rules.

The saved-Target empty-C2 Work regression uses a genuine nonzero `p.$/T`
input. Its no-child-initial expectation stays unchanged. Current-summary
replay with an existing child initial and late static/call-suffix Work
regressions also remain unchanged.

A direct `DemandStore.scope().initials(Reach)` can still return empty.
That lookup is unchanged. Only an actual qualifying internal control
invocation can use the candidate inheritance and output interface.

After native validation, compare the 18 missing OWASP identities with the
saved baselines, and run all four projects with the unchanged configuration.
State latest reached, completed and accepted iterations. A recovered native
example or partial failed campaign is not full project quality acceptance.
Do not remove this DRAFT/UNSELECTED status or update the current production
proof pins before the behavior decision and its required implementation gates.
