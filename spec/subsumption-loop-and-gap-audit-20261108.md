# Loop retrace and remaining design gaps

8 November 2026. This is a review of the latest
[combined spec](edge-subsumption-initial-emission-demand-intersection.md).
It includes the selected EXACT/FLOW prefix companion. This audit also
retains historical before-fix traces. The later selected resolutions are
sections 2.7, 3.4 and 4.5: own-ZERO loop bypass, selected PART STAR-to-ANY
cleaner result, and separate plain/protected memberships. The combined
spec is authoritative. No analyzer implementation is changed. The baseline is
`52829d5890ec3b3145cc996a1d8162d85cb8ceda`; the dirty SOA prototype is not
the selected implementation.

The run-2/run-3 worklists are now closed in §2.2–§2.3: their local paired
demand sets remain seven and three rows. The run-4 trace is corrected in
§2.4. Saved NORMAL replay does
continue to an ANY fixed point. The earlier catalog did not prove the whole
program fixed point or the reachability of every listed row. The remaining
run-5 gate result is scoped to its supplied demand snapshot. A separate
selected-cleaner example has no required NORMAL route through run-3 under
the selected cleaner rule. The Conductor MUST-admission obligation remains open.
Section 3.4 gives the selected STAR-to-ANY cleaner rule and its recovered
run-3 route. Sections 3.1-3.3 retain the before-fix trace for comparison.

**Run-5 diagnosis update:** the
[saved-repeat investigation](subsumption-loop-saved-replay-root-cause-20261108.md)
isolates a loop-gate omission. Existing saved NORMAL repeat effects are
not part of its observation. The gate can drop the actual source before
the repeat input handler applies those effects. The example therefore
does not establish that FLOW demand completion is required.

Sections 2.1-2.6 and 3.1-3.3 retain the prior rule set. Read them as
before-fix evidence, with the selected resolutions stated afterward.
They distinguish that evidence from the unselected completion candidate. They are reference-model results, not a
new project run. The latest checked loop phase is **run-5**; the cleaner
trace reaches **run-3**. Later completion feedback and natural stopping need
separate checks.

## 1. Rules used in this review

Write `F` for FLOW, `?` for ANY, `N` for NORMAL and `D` for DEMAND.
Every DATA fact uses its program variable as base. `H` is the protection flag. `Reach` is ZERO
control. Anonymous `DT` is DemandTarget; `NT(id)` is NormalTarget.

The schedule is forward run-1/limit 1, backward run-2/limit 1, forward
run-3/limit 2, backward run-4/limit 3 and forward run-5/limit 4.

- C2 never emits an ANY initial. All starts are identities.
- A concrete STAR primary starts D and also starts its same-geometry
  STAR/FLOW companion N.
- Successful ANY-demand admission of a strict descendant also starts an
  EXACT/FLOW identity N at the demand head. Keep that seed EXACT during
  execution. Normalize the whole FLOW pair at publication, before C5.
- A later STAR demand rejects a strict-descendant actual. An ordinary STAR
  actual above a deeper demand also rejects. ANY and MUST keep their own
  rules.
- C5 keeps each complete entry/output demand pair. An authorized FLOW
  companion does not bypass its paired output. A DATA output cannot meet
  a ZERO output selector. The field budget is `min(limit, FL(Dp)+1)`.
- Saved NORMAL replay runs before current admission at an input handler.
  The growing-loop-output gate runs before delivery to the next handler.
  These two order rules are different.
- A new demand selector is not a NORMAL provider. A NORMAL source fact is
  not an automatic right to cross a growing-result gate.
- In these before-fix traces, no protection, cleaner, field-transfer, Target
  or stop rule was changed. The selected addenda are sections 2.7, 3.4 and 4.5.

For the loop trace, E and mx are empty and H is false. There is one field,
one full mark, no ND, no MUST, no aliases and no statics. The finite model
uses one compatible effective repeat interface. It does not equate native
first-entry, repeat, discovery and logical Target ports.

## 2. The loop example under the latest emitter

Extract the body for the trace. `loopBody` is an analyzer block which shares
x with `deep`. Thus `x = x.f` changes the x used by the next body execution.
This presentation does not change the graph or introduce a real method call.

```java
// sourceFFFF(x): TRUE -> assign exact T at x.f.f.f.f.
// sinkT(x): CM(x.$, T).
// x has enough initialized f children for four traversals.
void deep(Node x) {
    while (true) {
        loopBody(x);
    }
}

void loopBody(Node x) {
    sourceFFFF(x);
    x = x.f;
    sinkT(x);
}
```

The first source marks the object at `x.f.f.f.f`. Four executions of the
field read bring x to that object. Later sources do not clear its mark.
Every DATA fact below starts with x. In particular, `x.f.*` is a fact;
f is a field, never a base. Use `[any]`, `$`, `*`, FLOW, T, N and D with
the meanings from §1. Each listed initial I starts the identity `I -> I`.
ZERO and Target remain the special control facts.

**Demand edges below use the current run's lookup direction:**
`entry selector -> paired output selector`. For previous edge `Dp -> Dc`,
this is `Dc -> Dp`. An arrow in this list is a permission, not an inferred
summary. The complete pair stays together during intersection.

Run-2/run-3 now close current-publication and saved-replay feedback from
reached control/source packets. The local lookup sets are unchanged, but
the earlier arbitrary transaction packets are no longer the reachability
argument. Run-4 closes its saved-repeat packet too. Native entry/discovery/
leave-port and packed-store correspondence remain open. No DATA frame is
added before or after the loop.

### 2.1 Run-1: forward, field limit 1

```java
// Demand edges:
//   none; this is run-1.
// Submitted facts:
//   ZERO,N                         [reached control]
//   x.[any]/T,D                    [source after cap and field read]
// Emitted initials:
//   ZERO,N
//   x.*/FLOW,N                     [ordinary run-1 abstraction]
//   x.*/T,D                        [answer to the actual T request]
void loopBody(Node x) {
    sourceFFFF(x); // x.f.f.f.f.$/T,N -> cap -> x.f.[any]/T,D
    x = x.f;      // x.f.[any]/T,D -> x.[any]/T,D
    sinkT(x);
}
// Emitted and retained summaries:
//   ZERO -> ZERO,N
//   ZERO -> x.[any]/T,D
//   ZERO -> Target,D
//   x.*/FLOW -> x.[any]/FLOW,D
//   x.*/T -> Target,D
```

The plain `x.*/T -> x.[any]/T,D` candidate is covered by the FLOW/D DATA
row. The T Target row remains. A removed candidate is not a hidden guide.

### 2.2 Run-2: backward, field limit 1; publication replay to fixed point

Start from reached backward ZERO. Its sink seed passes through the reverse
field read and supplies the first actual DATA input, `x.f.$/T,N`.
No independent DATA frame is supplied.

```java
// Demand edges (entry -> paired output):
//   x.[any]/T    -> ZERO
//   Target       -> ZERO
//   x.[any]/FLOW -> x.*/FLOW
//   Target       -> x.*/T
// Submitted facts after closing current-publication feedback:
//   ZERO,N
//   x.f.$/T,N                      [sink seed after reverse read]
//   x.f.[any]/T,D                  [current summaries replayed to that input]
// Emitted initials:
//   ZERO,N
//   x.f.$/T,N
//   x.f.*/FLOW,N
//   x.$/FLOW,N                     [exact prefix companion]
//   x.f.*/T,D                      [admitted after the MAY feedback arrives]
void loopBody(Node x) {
    sourceFFFF(x);
    x = x.f;
    sinkT(x);
}
// Emitted and retained summaries at the fixed point:
//   ZERO -> ZERO,N
//   ZERO -> x.f.$/T,N
//   x.f.$/T -> ZERO,D
//   x.f.$/T -> Target,D
//   x.f.*/FLOW -> x.f.[any]/FLOW,D
//   x.*/FLOW -> x.f.*/FLOW,N
//   x.f.*/T -> ZERO,D
//   x.f.*/T -> Target,D
```

The worklist must include publication replay, even when an input was
processed before the summary existed:

| Worklist step | New work and result |
| --- | --- |
| Reached ZERO | Publish the ZERO rows; offer `x.f.$/T,N`. |
| First DATA admission | Analyze the exact T initial, field FLOW initial and exact FLOW prefix. Publish the exact-origin source controls, FLOW/DEMAND row and NORMAL grower. |
| Replay new publications | Apply both DATA summaries to the already waiting `x.f.$/T,N`; each supplies `x.f.[any]/T,D`. |
| Re-offer MAY | C2 now emits `x.f.*/T,D`. Analyze it and publish the remaining STAR-origin source controls. |
| Drain again | Every DATA result is already represented by the exact/MAY input set. No new initial or publication remains. |

Both DATA producers are concrete, computed relations:

```text
Current x.f.*/FLOW -> x.f.[any]/FLOW,D
  applied to x.f.$/T,N
  = x.f.[any]/T,D

Current x.*/FLOW -> x.f.*/FLOW,N
  applied to x.f.$/T,N
  = raw x.f.f.$/T,N
  -> global field limit 1
  = x.f.[any]/T,D

Reapply either relation to x.f.[any]/T,D
  = x.f.[any]/T,D again
```

The second relation is a **current** NORMAL publication in run-2, not a
saved row. Its raw initial was `x.$/FLOW,N`; after one reverse read and
whole-FLOW normalization it becomes the shown STAR relation.

The late MAY input selects STAR/T, not exact/T: the demand head is x and
the actual is at its first child with an ANY tail. Thus the earlier listed
`x.f.$/T,D` initial was not established by this feedback. The initial
`x.f.$/T,N` still produces DEMAND source controls because its reverse read
crosses the field limit. Initial support and result support are different.

Closing the worklist gives the same eight local publication families as
the old transaction catalog. It establishes their reached repeat-component
route instead of assuming every input in a broad universe was offered.
Seven complete paired rows enter run-3. The nonzero NORMAL grower is saved.
Backward ZERO-premise DATA rows enter guidance but are **not persisted as
saved DATA providers**.

### 2.3 Run-3: forward, field limit 2; close saved and current replay

Run-2's source hits permit the real source. Reached normal ZERO control is
kept separate from DATA. Valid forward ZERO control records can carry it;
there is no saved inverse of run-2's `ZERO -> x.f.$/T,N` DATA row.

```java
// Demand edges (entry -> paired output):
//   ZERO           -> ZERO
//   x.f.$/T        -> ZERO
//   ZERO           -> x.f.$/T
//   Target         -> x.f.$/T
//   ZERO           -> x.f.*/T
//   Target         -> x.f.*/T
//   x.f.[any]/FLOW -> x.f.*/FLOW
// Submitted scalar DATA shapes after replay closure:
//   x.f.[any]/T,D                  [real source image]
//   x.f.$/T,D                      [paired exact C5 image]
//   x.[any]/T,D                    [NORMAL shrinker applied to MAY image]
//   x.$/T,D                        [NORMAL shrinker applied to exact image]
// Reached control: ZERO,N.
// Emitted initials:
//   ZERO,N
//   x.f.$/T,D
//   x.f.*/FLOW,N
//   x.f.$/FLOW,N                   [from the separate exact scalar offer]
void loopBody(Node x) {
    sourceFFFF(x); // x.f.f.f.f.$/T,N -> cap2 -> x.f.f.[any]/T,D
    x = x.f;      // -> x.f.[any]/T,D
    sinkT(x);
}
// Emitted and retained summaries at the fixed point:
//   ZERO -> ZERO,N
//   ZERO -> x.f.[any]/T,D
//   ZERO -> x.f.$/T,D
//   x.f.*/FLOW -> x.*/FLOW,N
//   x.f.$/T -> Target,D
```

The scalar list shows offered shapes, not a claim that a packed canonical
store must retain each as a separate row. The proof also checks that the
MAY offers alone can infer these same local publications; the separate exact
offer and its exact FLOW initializer are not needed for the result.

Two NORMAL providers have the same shrinking geometry:

- The saved opposite view of run-2's prefix grower.
- The newly published run-3 body relation.

```text
Saved/current x.f.*/FLOW -> x.*/FLOW,N

x.f.[any]/T,D -> x.[any]/T,D
x.f.$/T,D     -> x.$/T,D
```

Their stored shape shrinks from one field to zero, so the growing-result
gate does not block either application. Actual T and DEMAND support remain
unchanged. The FLOW hypothesis does not become a real FLOW input, or a
NORMAL T input, at the next body invocation.

The worklist then closes:

| Re-offered fact | C2 and saved/current application |
| --- | --- |
| `x.[any]/T,D` | Re-emits the already known `x.f.$/T,D` and `x.f.*/FLOW,N` initials. ANY can also match the shrinker's deeper premise; application returns the same `x.[any]/T,D`. |
| `x.$/T,D` | Cannot read the missing f and cannot satisfy the deeper DATA demand; emits nothing. |
| The original `x.f` offers | Replay the same source/sink/shrinker work; no new publication. |

The native ANY-ancestor lane matters in the first row. The older `applyFlow`
helper implemented only at/below matching and was insufficient to close
this replay step. The new model uses the raw native AP summary kernel.
It proves one more complete worklist round changes neither inputs nor
publications, and therefore any further round is unchanged.

The incoming scalar/source facts remain DEMAND. The conditional FLOW
initials are NORMAL, but applying their summaries does not upgrade those
facts. No NORMAL sink witness is created by this closure.

The five local publication families give exactly these outgoing paired
rows for run-4:

```text
x.f.[any]/T -> ZERO
x.f.$/T     -> ZERO
Target      -> x.f.$/T
```

Thus the previous run-3 demand set is unchanged in this repeat component.
What was missing was the explicit route and fixed-point check. The parent
point facts `x.[any]/T,D` and `x.$/T,D` are not additional local
`ZERO -> x...` summaries: local body execution still starts under its C2
initial, while summary application preserves the enclosing original.

Backward nonzero source Reach results are converted to DemandTarget. They
must not be re-offered as fresh ZERO DATA control. Full entry/discovery/leave
ports, enclosing publication and native packed-store correspondence remain
separate obligations; this closure is not a whole-driver proof.

### 2.4 Run-4: backward, field limit 3; close saved replay first

**Correction:** the earlier five-row list was calculated by applying one
body traversal to each initial in a broad transaction universe. That is not
an execution of the saved-summary worklist. It omitted the repeat fixed point
and treated a raw three-field candidate as an already delivered input.

The saved NORMAL forward relation is:

```text
x.f.*/FLOW -> x.*/FLOW,N
```

Run-4 reads it in the opposite direction:

```text
x.*/FLOW -> x.f.*/FLOW,N
```

Starting with the actual sink requirement after its reverse field read:

| Repeated application | Input | Raw saved result | Result kept by loop gate |
| --- | --- | --- | --- |
| 1 | `x.f.$/T,N` | `x.f.f.$/T,N` | `x.f.f.$/T,N` |
| 2 | `x.f.f.$/T,N` | `x.f.f.f.$/T,N` | `x.f.f.[any]/T,D` |
| 3 | `x.f.f.[any]/T,D` | `x.f.f.f.[any]/T,D` | `x.f.f.[any]/T,D` again |

The global limit is 3, so it does not cut the second raw result. The loop
gate cuts it to two fields. Its complete repeat C2 observation is:

```text
Submitted x.f.f.f.$/T,N:
  initial x.f.f.*/T,D
  initial x.f.f.*/FLOW,N
  initial x.f.$/FLOW,N

Submitted cut x.f.f.[any]/T,D:
  the same three initials

Submitted cut x.f.[any]/T,D:
  initial x.f.*/T,D
  initial x.f.*/FLOW,N
  // Different keys; this shallower cut is not permitted.
```

Thus the second cut is the first safe cut. On the third application, the
same two-field ANY result reaches the same completion point with the same
whole original. There is no fresh delta. This replay route has reached its
fixed point; it must not stop before that.

The same holds when starting with a STAR fact:

```text
x.f.*/T,D -> x.f.f.*/T,D -> x.f.f.[any]/T,D
                              -> x.f.f.[any]/T,D again
```

The full run can finish only after all current publications, saved replay,
control and ordinary queued work are drained. The calculation above proves
this repeat component's fixed point, not an early exit rule for the analyzer.

For the reached repeat component, the annotations are:

```java
// Demand edges (entry -> paired output):
//   x.f.$/T     -> ZERO
//   x.f.[any]/T -> ZERO
//   Target      -> x.f.$/T
// Submitted facts:
//   ZERO,N
//   x.f.$/T,N                      [actual reverse sink seed/read]
//   x.f.f.$/T,N                    [first saved application]
//   x.f.f.[any]/T,D                [second saved application + loop cut]
//   x.f.$/T,D                      [if control carries DEMAND support]
//   x.f.f.$/T,D                    [that supported saved replay]
// Emitted initials:
//   ZERO,N
//   x.f.$/T,N
//   x.f.$/T,D
//   x.f.f.$/T,N
//   x.f.f.$/T,D
//   x.f.f.*/T,D
//   x.f.f.*/FLOW,N
//   x.f.$/FLOW,N                   [exact prefix companion]
void loopBody(Node x) {
    sourceFFFF(x);
    x = x.f;
    sinkT(x);
}
// Emitted and retained local summaries for this closed packet domain:
//   ZERO -> x.f.$/T,N
//   x.f.f.*/T -> ZERO,D
//   x.f.f.*/T -> Target,D
```

`E21Run4SavedReplayClosure` checks closure of all five DATA shapes above
under saved replay and the gate. Re-entry from the delivered ANY fact starts
local `x.f.f.*/T,D`. Its reverse body produces `x.f.f.f.*/T,D`, which can
reach the source requirement at `x.f.f.f.f`. The local source ZERO/Target
summaries above remain available.

**The ANY completion and a published summary are different objects.**
Saved application keeps the parent's original. Here it produces:

```text
Parent completion at the repeat point:
  ZERO -> x.f.f.[any]/T,D
```

That is real work. It is stored in the parent's completion store and offered
to the next body execution. It is not inserted into the child's summary
storage. On re-entry the child's original is its new local initial,
`x.f.f.*/T`, not the parent's ZERO.

The current local DATA candidate and the prefix candidate still face their
own complete paired ZERO output. That output rejects DATA. It does not
block the saved replay described above, and it does not remove the parent's
ANY completion. In the baseline, `scopedSummaries()` exports block summary
stores; it does not export parent completion stores.

The earlier extra `x.f.*/T -> ZERO/Target,D` rows require another submitted
shape, such as `x.f.[any]/T,D`. This repeat closure does not produce that
shape. They are valid transactions in the old upper-bound universe, but
have not been established as reached rows of this program. A distinct
first-entry/leave-port provider could change the full program closure; it
must be traced with its own interface rather than assumed from repeat.

### 2.5 Run-5: forward, field limit 4; consequence of that repeat closure

The three locally retained run-4 rows above give:

```java
// Demand edges (entry -> paired output):
//   x.f.$/T -> ZERO
//   ZERO    -> x.f.f.*/T
//   Target  -> x.f.f.*/T
// Submitted facts on the source route:
//   ZERO,N
//   x.f.f.f.$/T,N                  [proposed repeat delivery]
// Emitted initials:
//   ZERO,N
//   none for the proposed DATA repeat input
void loopBody(Node x) {
    sourceFFFF(x); // x.f.f.f.f.$/T,N fits the field limit.
    x = x.f;      // Produces x.f.f.f.$/T,N.
    sinkT(x);
}
// Emitted source-route summary after paired intersection:
//   ZERO -> x.f.f.f.$/T,N           [paired x.f.f.*: budget 3]
```

There is no shorter DEMAND source image from this packet's handoff. The
previous `ZERO -> x.f.f.[any]/T,D` image required the unestablished shallower
run-4 row. It must not be called reached merely because it exists in an
upper-bound transaction catalog.

For the precise source result, the reduced gate still has no after-loop
DATA consumer; the enclosing exit is typed control; next-body `x.f.$/T`
rejects the deeper fact. The source is dropped before saved shrinking replay.
This is a gate failure for the supplied reached-repeat demand snapshot.
It is not yet a complete native-program counterexample: entry/discovery,
leave ports and enclosing publication must be closed too.

Saved run-4 replay does continue from STAR and reaches ANY. Current rules
do not automatically turn every internal ANY completion into an outgoing
summary/demand row. However, this does not establish a need to add one:
the existing NORMAL repeat reader can already carry the precise run-5
source result to the exact-f demand. The later investigation identifies
the gate-before-saved-repeat ordering as the local loss. See the
[no-completion trace](subsumption-loop-saved-replay-root-cause-20261108.md#3-the-existing-route-with-no-completion).

### 2.6 Optional completion and the old shorter-image claim

This is a query workaround comparison, not the root-cause repair selected
for E21. The existing NORMAL continuation is omitted by the loop gate.

Completion can derive `(x.f.f.[any]/FLOW -> x.f.f.[any]/FLOW)` from the
actual deeper run-4 source-origin row. Under the same compatible interface:

| Submitted fact | Emitted primary initial |
| --- | --- |
| `x.f.f.f.$/T,N` | `x.f.f.f.*/FLOW,N` |
| `x.f.f.[any]/T,D` | `x.f.f.*/FLOW,N` |
| `x.f.[any]/T,D` | `x.f.f.*/FLOW,N` |

The cut values in this table are hypothetical gate trials. They are not
assertions that the current source emits all those values. The proper cuts
lose the fine command, so the gate keeps the precise NORMAL fact. Saved
NORMAL replay then gives:

```text
x.f.f.f.$/T,N -> x.f.f.$/T,N -> x.f.$/T,N -> x.$/T,N -> NormalTarget(id),N
```

The old larger catalog also admitted a shorter DEMAND source image and
checked its possible DemandTarget/FLOW feedback. Those calculations remain
valid **if that image is supplied**. This corrected repeat trace does not
supply it. They are not evidence that this program must create that feedback
or cannot stop after finding the sink.

Completion is not selected; keep this calculation as historical comparison.
Neither the old transaction catalog nor this smaller repeat closure proves
complete native-port correspondence or whole-driver convergence. The larger
run-6/run-7 formal attempt is still unverified.

### 2.7 Selected ZERO-premise loop repair: run-5

This addendum overrides the old gate outcome in section 2.5. Use the
[own-ZERO bypass](zero-premise-loop-output-bypass-candidate.md), after C5
and the global limit. Deliver the admitted NORMAL source result to the
repeat input. The ordinary saved-first route is:

```text
ZERO -> x.f.f.f.$/T,N             own-ZERO loop bypass
saved x.f.*/FLOW -> x.*/FLOW,N    gives x.f.f.$/T,N
same saved summary               gives x.f.$/T,N
existing exact-f admission        starts x.f.$/T,N
ordinary body read + sink         local x.f.$/T -> NormalTarget(id),N
ordinary Target application       parent ZERO -> NormalTarget(id),N
```

No new ANY demand, Target conversion or source permission is added.
The checked run-2/run-3 repeat fixed points stay unchanged. Full native
physical-port and stopping validation remains required. The general
DATA-premise saved-continuation proof is not closed by this exception.


## 3. A separate counterexample: direct exact-root selected cleaning

This example has no loop, statics, aliases, ND or field-limit cut. It shows
that the latest prefix probe is not a complete repair for all admission
gaps. All objects are initialized; g is one counted field.

```java
// Fixed rules:
// sourceG(p): TRUE -> assign exact T at p.g.
// cleanRootT(p): TRUE -> RemoveMark(p,T,reach=Exact), empty field path.
// sinkT(p): CM(p.$,T).
void example() {
    Box b = initializedBoxWithInitializedG();
    sourceG(b);
    Box r = m(b);
    sinkT(r.g);
}
Box m(Box p) {
    cleanRootT(p);
    return p;
}
```

The cleaner removes the mark at p itself. It does not clean p.g. Direct
ordinary transfer of actual `p.g.$/T,N` returns `ret.g.$/T,N`; the sink
should have a NORMAL witness. This is not a named-field cleaner lowered to
read/temp/write, and it is not RemoveAll.

### 3.1 Run-1: global FLOW mark exclusion hides a disjoint concrete path

```java
// Demand: none. Actual submitted: p.g.$/T,N.
// Run-1 FLOW abstraction: p.*/F,N.
// Cleaner requests T. The descendant answer is p.*/T,D, not p.g.$/T.
Box m(Box p) {
    cleanRootT(p);
    // FLOW branch: same geometry/support, mx={T}.
    // Concrete STAR branch: partial clean; surviving STAR/T,D,H=true.
    return p;
}
// Complete helper rows:
//   ZERO -> ZERO,N
//   p.*/F -> p.*/F,mx={T},N
//   p.*/F -> ret.*/F,mx={T},N
//   p.*/T -> p.*/T,D,H
//   p.*/T -> ret.*/T,D,H
// Actual call result: ret.g.$/T,D,H. Sink produces DT, not NT.
```

The protected T rows remain. Plain FLOW cannot subsume them, and the FLOW
also excludes T. No NORMAL argument/return provider is omitted from the
catalog.

### 3.2 Run-2: requested STAR preserves a STAR handoff

```java
// Demand pair for the returned value: (ret.*/T, p.*/T).
// Submitted from exact sink reversal: ret.g.$/T,N.
// Requested-STAR run-2 cell starts ret.*/T,D and ret.*/F,N.
// The NEW exact-prefix rule does not apply: the selector is STAR, not ANY.
Box m(Box p) {
    cleanRootT(p); // Reverse body still excludes T from FLOW.
    return p;     // Analyzed in reverse before the cleaner.
}
// Without completion, current DATA catalog:
//   ret.*/T -> p.*/T,D,H
// FLOW candidate has mx={T}; original paired T output rejects it.
// Actual application reaches p.g.$/T,D,H and the real source action.
// Thus run-3 DOES have source permission.
```

With completion, extra NORMAL FLOW rows can be inferred. Every such row
still excludes T. Completion is therefore included as a positive query
variant, not assumed absent.

### 3.3 Run-3: the precise source is blocked

```java
// Original demand pair: (p.*/T, ret.*/T).
// Actual source submission: p.g.$/T,N, in budget since run-1.
// Later STAR demand rejects this strict descendant: no T initial.
Box m(Box p) {
    cleanRootT(p);
    return p;
}
// Saved NORMAL rows cannot transport T: all have mx={T}.
// Without completion: no new DATA command for this actual.
// With completion: p.g.*/F,N and the new p.$/F,N can start.
// Both keep ordinary cleaner behavior and acquire mx={T}.
// No saved/current result reaches the sink with T.
```

Increasing the field limit does not itself change this same STAR-versus-g
admission cell. This is a checked missing run-3 continuation in the finite
helper/source/sink catalog, both with and without completion. A claim about
the complete native driver's final result still requires its Target/root,
packed-store and stopping adapters.

The conflict is between three retained policies: run-1 answers the cleaner
at the coarse STAR key; nonstatic selected FLOW cleaning excludes T from
the whole value; later STAR demand rejects the precise descendant. The new
ANY-only prefix companion cannot repair the original STAR selector.
Changing any of these policies is a semantic choice. This review makes no
such change and does not promote the protected DEMAND survivor to NORMAL.

### 3.4 Selected: change a partial STAR/T survivor to ANY/T

**We can do this.** For this partial selected-cleaner survivor, replace only
the conclusion tail. Keep the STAR premise, T, DEMAND layer and H:

```text
Before cleaner: p.*/T -> p.*/T,D
Current result: p.*/T -> p.*/T,D,H
Candidate:      p.*/T -> p.[any]/T,D,H
```

STAR preserves the same suffix on both endpoints. ANY forgets that
correlation. Every pair in the old STAR relation remains in the ANY relation.
The broader result must remain DEMAND. This is a cleaner-transfer candidate,
not a change to initial emission: there is still no ANY initial or premise.
The preceding audit kept cleaners unchanged, so it did not assume this rule.

For the same code, the candidate produces this trace:

```java
// Run-1, forward, limit 1.
// Demand edges: none.
// Submitted fact: p.g.$/T,N.
// Emitted initials: ZERO,N; p.*/FLOW,N; requested p.*/T,D.
Box m(Box p) {
    cleanRootT(p); // Partial concrete survivor -> p.[any]/T,D,H.
    return p;
}
// Emitted summaries:
//   ZERO -> ZERO,N
//   p.*/FLOW -> p.*/FLOW,mx={T},N
//   p.*/FLOW -> ret.*/FLOW,mx={T},N
//   p.*/T -> p.[any]/T,D,H
//   p.*/T -> ret.[any]/T,D,H
```

```java
// Run-2, backward, limit 1.
// Demand edges (entry -> paired output):
//   p.[any]/T   -> p.*/T
//   ret.[any]/T -> p.*/T
// Submitted fact: ret.g.$/T,N from the exact sink reversal.
// Emitted initials:
//   ret.g.$/T,N
//   ret.$/FLOW,N                    [exact prefix companion]
Box m(Box p) {
    cleanRootT(p); // p.g.$/T is outside exact cleaning at p; it survives N.
    return p;
}
// Emitted and admitted summary:
//   ret.g.$/T -> p.g.$/T,N,H
// FLOW output still excludes T and fails the paired T output selector.
```

The ANY entry selects the precise one-field exact initial. The concrete
body result is NORMAL because this exact child is not cleaned. Applying
that record to the real sink requirement reaches the real source, so source
permission is retained. No completion is required for this route.

```java
// Run-3, forward, limit 2.
// Current DATA demand from m's run-2 summary: none; that summary is NORMAL.
// Saved NORMAL summary: p.g.$/T -> ret.g.$/T,N,H.
// Submitted fact: p.g.$/T,N from the actual source.
// Emitted current initial: none needed; saved replay runs first.
Box m(Box p) {
    cleanRootT(p);
    return p;
}
// New current summary needed for this call: none.
// Saved application result: ret.g.$/T,N,H.
// The caller's sink at r.g has a NORMAL witness -> NormalTarget(id).
```

The cost is a broader DEMAND relation. With actual `p.f.$/T`, the old STAR
result preserves the f suffix; an ANY result can also select another suffix,
such as g, on DEMAND. Later analysis must refine those extra candidates.
The change never promotes this partial survivor to NORMAL or removes H.
Exact/disjoint concrete outputs and FLOW mark exclusions stay unchanged.

`CleanerMaySurvivorCandidate` checks relation inclusion, retained layer/H,
the complete run-1 catalog, run-2 admission/intersection, source permission
and the recovered run-3 NORMAL finding for this program. It does not prove
a general cleaner/loop convergence theorem. This section is now selected in the combined spec. It changes the
specified cleaner survivor, while runtime code remains unchanged. The
generic rule additionally requires the selected PART branch and keeps all
disjoint, other-mark, already-EXACT, MAY/MUST and RemoveAll results unchanged.


## 4. Other findings from the spec review

### 4.1 E29: the Conductor admission obligation remains

The real query pattern is actual `p.f.MUST/T,N` with a retained root
`p.?/F` demand. The latest complete C2 stream is:

```text
root ANY/FLOW demand + actual p.f.MUST/T,N:
  p.f.*/FLOW,N
  p.$/FLOW,N                      // latest exact prefix

removed child p.f.ANY/FLOW demand + that same actual:
  p.f.MUST/FLOW,N
```

The new exact prefix cannot read f. The child STAR probe can read f, but
loses uniformity on a further read. Thus removing the child demand changes
the complete C2 observation even after the latest addition. Spatial
coverage alone does not close this obligation.

The existing finite uniform-source example shows delayed reporting, not
a new permanent false negative. The real two Conductor findings and their
rollback evidence remain in [E29](subsumption-principal-examples-20261107.md#e29-conductor-a-covered-location-set-can-lose-a-refinement-head).
This audit does not claim that the latest design recovers them.

### 4.2 E27 is not a native guarded-pass counterexample

The serialized type accepts a pass condition. The pinned native compiler
logs a residual mark condition and lowers the pass without that condition.
The pass form is unconditional. Therefore the old `CM(p.f,T) -> Pass(p,ret)`
example is only an abstract rule-language anti-promotion example. It cannot
serve as a native false-guard trace at the selected baseline. Keep the
general requirement for a real NORMAL provider, but remove this example as
native evidence for that requirement. No pass/compiler behavior is changed.

### 4.3 ND and protection are not shortcuts around the gaps

Backward conjunctive source arms retain their `may`/DEMAND support. They
cannot supply guessed NORMAL unary producers. A pass does not create H.
Protected concrete cleaner survivors remain protected. An OR-rendered flag
is not the authority for hidden plain coverage. These contracts still need
their native delivery/restore checks; no extra whole-program failure is
claimed from those checks here.

### 4.4 Hidden plain coverage is not delivered by a visible-only delta

There is also a delivery-contract gap in §2.1 of the combined spec. It keeps
separate plain U and protected H coverage, but its pseudocode publishes only
changes to the OR-rendered rows. The following legal producer can offer the
same exact summary once with H and once without H:

```java
// Conditional initial: P=p.$/T,N.
Object branch(Object p) {
    Object x = p;
    if (flag) removeTBelow(x); // Selected T only; root itself survives.
    return x;
}
// Same summary owner and coordinate:
//   P -> ret.$/T,N,H          [surviving selected-cleaner branch]
//   P -> ret.$/T,N,plain      [ordinary branch]

Object wrapper(Object p) {
    Object r = branch(p);
    return r;
}
```

The exact root is disjoint from BELOW. The existing cleaner protects its
surviving selected T; ordinary copies only carry that flag. This is not the
prohibited RemoveAll-below rule.

Let E denote the complete summary/result geometry. A is its producer and B
is a subscriber with the ordinary bound result. Under render-only delivery:

```text
H first:
  A.offer(E,H) -> A.U={}, A.H={E}; visible E/H -> B.H={E}
  A.offer(E,U) -> A.U={E}, A.H={E}; visible unchanged -> no delivery
  B.U is still empty.

Plain first:
  A.offer(E,U) -> deliver E/U -> B.U={E}
  A.offer(E,H) -> deliver E/H -> B.H={E}
  B.U={E}, B.H={E}.
```

A ends with identical authoritative views and one visible H row in both
orders. B does not. A pass cannot reconstruct the missing plain certificate
from that visible row. Local insertion/restore laws alone do not establish
delivery across owners.

The six-law `RenderedDeliveryCounterexample` checks this contract using the
existing U/H reference operations. In their fixed MAY/T/DEMAND domain it
also shows a coverage consequence: a later plain child is retained only in
the H-first case. That MAY consequence is separate from the exact Java
producer above; an EXACT parent is not claimed to cover field descendants.
No native false negative or current-engine bug is established here.

The missing invariant must specify how a changed authoritative coverage
view reaches its consumers even when OR rendering is unchanged, or how the
consumer reads the same authority. This review does not select a new event,
archive or store to implement that invariant.

### 4.5 Selected delivery resolution: keep both edges

The OR-rendering counterexample above is historical. The selected contract
now keeps both plain and protected memberships at the same geometry. A new
plain membership after a protected one is visible, retained and published;
its subscriber performs plain-class insertion. The symmetric order also
publishes both. Same-class duplicates produce no new work. Passes retain
the supplied class and cannot create H.

The selected [delivery model](lean/proposals/subsumption-initial-demand-20261107/PlainCoverageDelivery.lean)
checks exact two-class identity, freshness, arbitrary delivery sequences in
its canonical scalar domain, both arrival orders and the child-coverage
control. Native packed-store, queue, cache and restore adapters must retain
both memberships. No hidden plain certificate or new protocol is selected.

## 5. Evidence and limits

The historical round-closure root check passed **1,107 declared laws**. Read the
[receipt](lean/proposals/subsumption-initial-demand-20261107/component-checks-1107.json)
and [complete axiom audit](lean/proposals/subsumption-initial-demand-20261107/component-axioms-1107.txt).
This count includes historical, negative and local component results. It is
not a count of complete analyzer proofs. The last 24 laws close run-2/run-3
publication and saved-replay feedback. Eighteen preceding laws close the
run-4 saved-repeat component. Ten other laws check the optional cleaner
candidate, without changing selected cleaner behavior.

The [proof package](lean/proposals/subsumption-initial-demand-20261107/README.md)
contains the executable operators, pinned baseline imports and root-owned
checks. E21 uses the same latest emitter as the generic exact-prefix model.
The historical models check bounded transaction families, subset
classifications and gate results for their supplied demand snapshots. The
new run-4 model closes the saved-replay/gate component and separates the
parent completion from local publication. A catalog row is not thereby
proved reachable. Full native schedule/port correspondence remains open.

The new `RootExactCleanerGap` model uses the actual baseline cleaner and
correlated AP application. It computes the run-1 request answer, all helper
argument/return rows, paired C5, saved NORMAL replay, actual source permission
and run-3 sink result. `MustAdmissionAudit` checks the latest complete
E29-shaped C2 streams and the read barrier. Neither model assumes an absent
NORMAL provider as a free input.

The [native source excerpts and hashes](lean/proposals/subsumption-initial-demand-20261107/cleaner-and-pass-native-source-audit-20261108.json)
are embedded in the repository. The larger, unchecked late-loop attempt and
its failure log are also retained; the smaller checked model does not claim
its B6/F7 results.

The [run-4 ownership excerpts](lean/proposals/subsumption-initial-demand-20261107/e21-run4-ownership-source-pins-20261108.json)
pin saved-first replay, parent completion and the exported summary stores
at baseline 528. They also show that a backward ZERO-premise NORMAL row is
not persisted. Older supplied `savedZeroReverse` helpers cannot be cited as
an actual saved provider for the selected analyzer.

The [run-2/run-3 publication excerpts](lean/proposals/subsumption-initial-demand-20261107/e21-run2-run3-publication-source-pins-20261108.json)
pin both sides of the publication/input join, saved-first delivery, native
backward Reach-to-Target conversion and initial-layer admission bits. The
[round catalog](lean/proposals/subsumption-initial-demand-20261107/review-e21-run2-run3-worklist-1107.txt)
records the computed offered packets and retained local rows.

The review does not establish complete native correspondence, Conductor
recovery, GROUP correctness or natural convergence. No analyzer implementation,
configuration, project report or stop policy was changed. The next design
decision must close the remaining Conductor and general continuation
obligations before implementation acceptance. The three selected resolutions
above are included in the updated combined spec.
