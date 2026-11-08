# Loop source loss before saved repeat replay

**Selected resolution:** the later
[combined spec](edge-subsumption-initial-emission-demand-intersection.md#63-zero-premise-loop-output-bypass)
now exempts a summary with its own effective ZERO premise from the extra
loop gate. This report retains the before-fix diagnosis and evidence. Its
statement that the investigation selected no repair is historical.


8 November 2026. Latest analyzed phase: **run-5**, forward, field limit 4.
The selected source baseline is `52829d5890ec3b3145cc996a1d8162d85cb8ceda`.
This investigation changes no analyzer code or selected behavior.

The loss is at the loop output gate. The gate can drop an actual source
fact before delivery to a repeat input. That input would first apply an
existing NORMAL summary. The gate checks current repeat demand, but does
not check saved repeat effects. The source fact can therefore have a useful
NORMAL continuation even when the gate reports no observation.

The proposed FLOW demand completion is not needed for the route below.
It makes another query positive instead of restoring the omitted saved
continuation. This example does not justify selecting that completion.

## 1. Code and the existing provider

`loopBody` below is an analyzer block. It shares the method register x.
It is not a Java call with a private copy of x.

```java
// sourceFFFF(x): TRUE -> assign T exactly at x.f.f.f.f.
// sinkT(x): CM(x.$, T).
// The initialized object chain has at least four f links.
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

Write N for NORMAL and D for DEMAND. The mark is the full mark T.
Field and mark exclusions are empty. No aliases, statics, cleaners,
protection or ND premises occur.

The body already has this saved NORMAL relation at its repeat interface:

```text
x.f.*/FLOW -> x.*/FLOW, N
```

It performs the ordinary field read. Applied to a concrete actual, it
preserves the actual mark, tail and layer and removes one leading f.
This is a below-premise match. The opposite-direction-only STAR inside
rule is not involved: the actual has an explicit f and an EXACT tail.

The selected finite trace derives this relation in run-3 and persists it.
Run-4 uses the reverse view, `x.* -> x.f.*`, and closes its saved replay
to a two-field ANY fixed point. That does not require publishing a new
one-body NORMAL specialization. Read the
[run-2 through run-4 trace](subsumption-loop-and-gap-audit-20261108.md#22-run-2-backward-field-limit-1-publication-replay-to-fixed-point).

## 2. Run-5: the exact lost operation

The demand arrows below mean **entry selector -> paired output selector**
in the current lookup direction. They are not inferred transfer edges.
The finite repeat component has these three complete pairs:

```java
// Demand edges at the repeat entry:
//   x.f.$/T -> ZERO
//   ZERO    -> x.f.f.*/T
//   Target  -> x.f.f.*/T
// Submitted control: ZERO,N, reached through the real CFG.
// Emitted control initial: ZERO,N.
// Saved summary at repeat entry:
//   x.f.*/FLOW -> x.*/FLOW,N
void loopBody(Node x) {
    sourceFFFF(x); // ZERO -> x.f.f.f.f.$/T,N; depth 4 fits.
    x = x.f;      // ZERO -> x.f.f.f.$/T,N.
    sinkT(x);     // This source result has no T at x itself yet.
}
// Local summary after paired C5:
//   ZERO -> x.f.f.f.$/T,N.
// Its application under parent ZERO gives the same NORMAL fact.
// Current gate: DROP before the repeat input handler receives it.
```

The ZERO input pair permits the local source row. Its paired output has
two fields, so C5 permits three fields. The global limit is four.
Neither summary intersection nor the global field limit removes this row.

The next steps in the selected baseline source are:

```text
publish the admitted local ZERO -> x.f.f.f.$/T,N row
apply it to the standing reached ZERO input
classify stored summary growth: FL(ZERO)=0 < FL(x.f.f.f)=3
enter the loop output gate
    adjacent current initials: empty
    adjacent saved effects through enclosing C5: empty
    repeat current initials: empty
        x.f.$/T rejects the deeper exact x.f.f.f.$/T
        ZERO/Target control pairs do not admit that DATA fact
    saved repeat effects: NOT QUERIED
drop the fact
```

There is no offer to the repeat handler. Thus its saved-first policy
cannot run. No prefix trial takes place after an empty observation.

## 3. The existing route, with no completion

For diagnosis, deliver that one actual NORMAL source result to the repeat
input. Keep all C2, C5, mark, layer and Target rules unchanged.
This is a bounded counterfactual order check, not a selected general fix.

| Step | Actual at the repeat input | Existing operation | Result |
| --- | --- | --- | --- |
| 1 | `x.f.f.f.$/T,N` | Replay saved `x.f.* -> x.*` before C2 | `x.f.f.$/T,N` |
| 2 | `x.f.f.$/T,N` | Replay the same saved summary before C2 | `x.f.$/T,N` |
| 3 | `x.f.$/T,N` | Existing exact repeat demand | Start `x.f.$/T -> x.f.$/T,N` |
| 4 | That exact initial | Execute `x=x.f`, then `CM(x.$,T)` | Local `x.f.$/T -> NormalTarget(id),N` |
| 5 | Standing actual `x.f.$/T,N`, parent original ZERO | Ordinary local Target application | Parent `ZERO -> NormalTarget(id),N` |

The two saved applications have stored shape one field -> zero fields.
They are not growing summaries, so they bypass the loop growth gate.
The parent original remains ZERO throughout. The saved reader does not
generate T or upgrade a DEMAND actual to NORMAL.

The current actor at step 3 is:

```java
// Existing demand pair: x.f.$/T -> ZERO.
// Submitted fact: x.f.$/T,N, from the two saved reads.
// Emitted initial: x.f.$/T,N.
void loopBody(Node x) {
    sourceFFFF(x); // A DATA initial does not create a fresh ZERO source.
    x = x.f;      // x.f.$/T -> x.$/T,N.
    sinkT(x);     // The exact NORMAL witness emits NormalTarget(id).
}
// Emitted terminal summary:
//   x.f.$/T -> NormalTarget(id),N.
```

Only the first delivery is missing. No new `x.f.[any]` demand or initial
is needed to run this NORMAL route.

## 4. What subsumption does here

The existing NORMAL read covers aligned specializations, for example:

```text
x.f.*       -> x.*       / FLOW,N
x.f.f.*     -> x.f.*     / FLOW,N   [covered specialization]
```

It can also back an eligible unprotected concrete relation under the
selected FLOW/T rules. Retaining covered one-body variants does not make
the saved read more capable.

Three other relations are different:

- `ZERO -> x.f.f.f.$/T` generates an actual mark. The FLOW read does not.
- `x.f.f.* -> x.*` describes two body executions. It is a composition,
  not an aligned specialization of one read. Repeated application of the
  original summary can execute it without storing this composed row.
- `x.f.$/T -> NormalTarget(id)` records the sink observation. A DATA FLOW
  transfer cannot replace a typed terminal result.

Thus subsumption supports removing redundant read specializations. It
does not support dropping the actual source before an applicable read.

## 5. ZERO, Target and the loop boundary

The source summary triggers the problem because ZERO has field length
zero: `ZERO -> x.f.f.f.$/T` is classified as growing. A summary with the
same DATA geometry and a sufficiently long nonzero premise could bypass
the gate. This explains the connection to ZERO in this example.

But the missing operation is DATA delivery, not a required Target-to-DATA
conversion. The checked handoff preserves the typed control pairs:

- A previous source discharge gives current ZERO/Target control guidance.
- ZERO/Target controls can admit canonical ZERO, not arbitrary DATA.
- A real Target result follows the terminal path to the enclosing owner.
  It does not need the DATA growth gate.
- No NormalTarget exists before the source fact reaches the real sink.
  Replaying or changing a NormalTarget store cannot restore that read.

The loop gate adds an extra filter in front of the next saved-first input
handler. An ordinary function call applies saved NORMAL summaries before
it checks current demand. It has no equivalent intervening loop-output
filter. The identified ordering gap is therefore loop-specific. Other
growing DATA producers could expose the same omission; ZERO/Target are
not a proof that every occurrence of this gap requires a control bug.

## 6. Fixed point and repair boundary

Run-4 does reach a saved-replay fixed point in the checked repeat
component. Run-5 can also drain all queues under the current algorithm:
the useful source fact was dropped before enqueue. More rounds over the
same remaining queues cannot recover it. This is an incomplete transfer
at the boundary, not evidence that a pending callback was ignored by the
stop test.

Any repair must preserve useful saved repeat continuations as well as
current-demand continuations. It must not treat an arbitrary saved match
as progress: `x.* -> x.*` can return the same deep fact without approaching
a consumer. Counting that identity as useful would defeat the growth
restriction. Equal-length cycles, branches, ports and later summary
arrival need the same explicit check in a general repair.

This report selects no bypass, completion or new lookup strategy.
The bounded diagnostic route establishes where the current gate loses
an already executable NORMAL continuation.

## 7. Evidence and limits

The local Lean model
[E21SavedRepeatGateDiagnosis](lean/proposals/subsumption-initial-demand-20261107/E21SavedRepeatGateDiagnosis.lean)
uses the reached run-3 reader and the closed run-4 packet. It checks the
empty run-5 gate, two native AP saved applications, exact NORMAL admission,
the ordinary body sink result, its paired guidance, the retained ZERO
parent and the DEMAND negative control. It adds no completion rows.
It does not prove the complete native program or all physical ports.
The [receipt](lean/proposals/subsumption-initial-demand-20261107/component-checks-1121.json)
and [axiom audit](lean/proposals/subsumption-initial-demand-20261107/component-axioms-1121.txt)
check the 14 added diagnostic statements with the existing components.
The package total is not a count of whole-analyzer proofs.

The historical native run reached **run-5** and lost the finding. Its
physical catalog has a repeat-entry-5 exact-f DATA selector at output 11,
ZERO/Target control selectors at output 5, and the saved repeat-5 NORMAL
reader. It records two drops of the NORMAL three-field source image,
at two distinct first-entry/repeat scopes, and zero prefix trials. These
are two physical offers, not NORMAL and shorter DEMAND source variants.

That capture is from the later withdrawn SOA prototype. It is not a new
baseline-528 run or a native execution of the selected plain-STAR design.
Its raw trace and receipt are already embedded under
`priorSeparateDeepCase.artifacts` in the
[repository data](../docs/reports/data/bidirectional-concrete-static-flow-provider-20261107.json).
Trace SHA-256:
`a1e2fd988c1aa907627b8da0f57d6b3c730db9e495585a965b67f133762b00ee`.

Baseline source has the same gate/replay asymmetry. The new native
component check uses that frozen baseline and explicit scoped demand
inputs. It derives its NORMAL reader through the real field-read
micro-edge. **All five tests pass**, including real ZERO source/read/C5,
the gate drop, saved-first AP replay and exact NORMAL admission, a real
`RunMethodLocalServices.checkSinks` evaluation, queued parent Target joins
in both arrival orders, and DEMAND/identity negative controls.

This is not a full multi-iteration run. The
[test source](lean/proposals/subsumption-initial-demand-20261107/native-loop-saved-repeat-20261108/LoopSavedRepeatGateDiagnosisTest.kt),
[test result](lean/proposals/subsumption-initial-demand-20261107/native-loop-saved-repeat-20261108/tests.xml)
and [evidence receipt](lean/proposals/subsumption-initial-demand-20261107/native-loop-saved-repeat-20261108/receipt.json)
are in the repository. The receipt embeds the baseline source excerpts
and their hashes. No production source was changed for this investigation.
