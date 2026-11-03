# Loop blocks: a missing ZERO producer after a loop

Date: 2 November 2026. **Historical pre-correction investigation.**
Measured revision: `6052e2ea2d400a7f1f47c0f5fe4497bae23e2ace`.

Update, 3 November: the selected correction keeps prior NORMAL ND
contributors at the condition point. The SESSION leaf can then join with
current DATA without admitting ZERO to AL. See
[the selected spec](../../spec/normal-nd-contributors.md). The two ZERO
design options below record the earlier investigation; neither is selected.
The native SESSION/DATA regression now passes the focused tests. Full
native checks and the new project campaign determine final acceptance.

Current project evidence: OWASP reaches, completes, and accepts run-5. It reports 4,094 identities rather than the saved 4,112. The 18 losses are all trust-boundary identities. The native counterexample reaches, completes, and accepts run-3, then stops with `NO_DEMAND_EDGE` and no finding.

The root executed `LoopBlockTrustBoundaryFindingTest`: four tests, one failure. The exact-array/unconditional-session loop case fails. The same code with only feedback removed passes. Both uniform-source/conditional-session controls pass. No analyzer policy was changed for this investigation.

```java
// Entry metadata: request.$/REQ, NORMAL.
void m(Request request) {
    Cookie[] cookies = request.getCookies();
    // Source: CM(request,REQ) assigns cookies.$/DATA and cookies.[].$/DATA.
    while (again()) {
        Cookie cookie = cookies[i];
        param = cookie.getValue(); // Ordinary CopyAllMarks(This,Result).
        if (match()) break;
    }
    Session session = request.getSession();
    // Independent sink-pattern metadata: ZERO -> session.$/SESSION, NORMAL.
    session.putValue("key", param);
    // Sink: CM(session,SESSION) AND CM(param,DATA).
}
```

The serialized rule audit confirms these principal operations. The source and sink automata use separate generated prefixes. The first `getSession` metadata step checks the fixed call's type and zero arity; it does not require the source automaton's REQ mark. Array specialization creates two exact DATA actions. It does not create a uniform-taint source. No static/global marker is required for this specialization.

Let `I = param.*/DATA`. For this native graph, the after block is block 3, with forward entry `J=PortId(10)` and terminal exit `ROOT_EXIT`.

| Run | Observed fact or row | Effect |
|---|---|---|
| run-1 | BL stores NORMAL `ZERO -> cookies.$/DATA` and `ZERO -> cookies.[].$/DATA` | The complete normal source prefix is available for ordinary saved replay. |
| run-1 | AL stores NORMAL `ZERO -> session.$/SESSION` | The independent metadata source executes correctly in the initial run. |
| run-1 | AL's joined sink sees DEMAND data and a NORMAL ZERO-produced session marker | Its outgoing terminal row is `I -> DemandTarget`. The ZERO arm is not an independent all-ZERO sink witness and is not emitted as one. |
| run-2 | The original `getSession` source at instruction 6 is physically hit | The run-3 source permission for its exact action is **true**. Missing source permission is not the failure. |
| run-2 | AL retains NORMAL `ZERO -> param.$/DATA` toward J | The next forward run can admit the refined data input. |
| run-2 | AL has raw `ZERO -> DemandTarget`, but no outgoing local Target row | The paired terminal restriction has a DATA exit from `I -> DemandTarget`. It does not accept a ZERO/Target result at that exit. |
| run-3 | AL processes NORMAL `param.$/DATA` at instructions 6, 7, and 8 | The data path is recovered. |
| run-3 | AL processes no ZERO and no SESSION fact | The permitted independent source is not executed in the current AL body. |
| run-3 | No sink, no outgoing demand | The driver stops normally with the real finding absent. |

The retained run-1 `ZERO -> session.$/SESSION` AL summary is a whole-block output relation. Saved replay can emit that value at the block exit. It cannot inject it before the already-passed in-block sink. There is no saved NORMAL Target for this sink, because its run-1 data witness was DEMAND.

The precise contract conflict is local to the new block interface. The AP/Target restriction rules and the rule actions each perform their selected operation. Their combination does not supply a current ZERO entry for the after block's independent producer while that block is analyzed for data. A source permission by itself does not admit ZERO. The normal source summary at the block exit does not replace an internal observation that must join that source with admitted data.

This is a native correctness counterexample for transparent block decomposition, not a performance problem and not a proposed permission change. It is not a proof of the exact first lost runtime event for every one of the 18 project identities. Their shared serialized rule shape and matching source families support the diagnosis. The native control supplies the complete per-run causality.

The first receipt preserves the XML, root command log, and complete fact trace. The follow-up diagnostic confirms `C2(AL, ZERO) = []` and `C2(AL, param.$/DATA) = [param.$/DATA, NORMAL]`. It also prints the existing saved session rows. The finding assertion stays unchanged. A new ZERO/block policy requires an explicit design decision and proof; this investigation does not modify the original method-level ZERO guidance policy.


## Decision to make

The original method already has permission for ZERO. The new block boundary
filters that reached control fact. There are two possible designs.

1. **Inherit reached ZERO in forward blocks.** Keep method-level ZERO admission
   demand-guided. When ordinary routing delivers ZERO to an internal block, admit
   it with its existing layer even if that block has no local ZERO demand. Its
   actual internal `ZERO -> ZERO` completion must also pass to the next block;
   otherwise local C5 can stop control before AL. Do not create a new entry seed.
   Keep DATA admission, DATA/Target C5, public method C5, source permissions,
   NormalTarget composition and the no-independent-ZERO-sink-arm rule unchanged.
   Backward block admission stays unchanged. This is the smaller correction. It
   lets the permitted metadata producer run before the current in-block sink.
2. **Keep local ZERO admission demand-guided.** Define additional local control
   guidance for the independent ZERO contributor. It must preserve the source
   without treating that contributor as a complete ZERO-only sink witness. This
   needs a separate representation, handoff rule and completeness proof.

The first choice changes block-local forward ZERO admission and ZERO identity
completion. A C2-only change is insufficient. It must not treat a ZERO identity
permission as permission for `ZERO -> DemandTarget`: the current terminal probe
also uses `Reach.DEMAND`, so a general synthetic `(ZERO, ZERO)` demand can change
Target acceptance by accident. Keep that probe paired with its original demand.

Additional retained NORMAL ZERO identities can participate in ordinary saved
replay in backward runs. This is an indirect consequence to prove, even though
the backward C2 and seed rules do not change.

The first choice changes the selected block-local forward ZERO rules.
It does not change the original method-level AP rule. It must be stated and
proved explicitly before implementation. No choice is implemented by this report.

The [embedded evidence](data/bidirectional-loop-block-zero-control-gap-20261102.json)
contains all 18 lost identities, the four-test native receipt, complete fact trace,
exact test source, and serialized rule metadata. The loop control finishes at
**run-3** with no report; the identical no-feedback control reports the sink.
