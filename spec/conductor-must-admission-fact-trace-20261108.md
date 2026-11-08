# Conductor: the missing MUST probe

8 November 2026. This example explains the local admission issue. It does
not prove that this one query causes Conductor's two missing findings.
The latest analyzed phase is run-5. Sections 5-6 extend the small mapper
under the updated spec; they are not a new full Conductor project run.

`F` means FLOW, `N` means NORMAL, and `D` means DEMAND. `MUST` means
`[any-taint]`: every position in the subtree has the mark. `*` means a
correlated suffix. E and mx are empty and H=false in this example.

## 1. The small runnable program

Use [UniformPrefixRefinementReproducer](../core/opentaint-dataflow-core/opentaint-dataflow/src/uniformPrefixReproducer/kotlin/org/opentaint/dataflow/bidi/UniformPrefixRefinementReproducer.kt).
It has two analyzed methods, a real source action and a real sink rule.
It supplies no demand, initial, summary or source permission. There is no
loop, ND rule, static field or explicit alias path.

```java
void root() {
    Root p = initializedRoot();
    sourceUniformT(p.f);       // Real rule: p.f.MUST/T, NORMAL.
    Result mapped = mapper(p);
    sinkExactT(mapped.e.h);    // Real rule: CM(mapped.e.h.$, T).
}
Result mapper(Root p) {
    Result out = initializedResult();
    if (flag) out.e.h.extra = p;
    else out.e.h = p.f.g;
    return out;
}
```

`e` is the fixture's `Element` slot; it counts as one accessor. The objects
and the e/h slots are initialized. The allocation notation states this
precondition. The source and sink names denote rules, not extra analyzed
methods. The source taints the entire p.f subtree, including p.f.g.

Keep both mapper branches. The deep copy produces a coarse root demand;
the read produces a finer p.f demand. Removing either branch removes the
specific root-versus-child comparison.

The [native evidence](../docs/reports/bidirectional-uniform-prefix-refinement-reproducer-20261106.md)
uses FULL mode and field limits `1,1,2,3,4,...`. Historical Current first
reports in run-5; the proper-prefix-off control first reports in run-3.
Both naturally finish run-5 with one report. Thus this runnable program
proves a reporting delay, not a permanent false negative.

## 2. Run-1: where the demand comes from

The following DATA trace follows the selected field operations. Run-1
behavior is unchanged. It also matches the captured run-1 summaries.
The unchanged ZERO control rows are omitted; they provide no return DATA.

```java
// Run-1, forward, field limit 1.
// root starts from ZERO/N.
void root() {
    Root p = initializedRoot();
    sourceUniformT(p.f);       // p.f.MUST/T,N; depth 1 fits.
    Result mapped = mapper(p); // Submits arg0.f.MUST/T,N.
    sinkExactT(mapped.e.h);    // Gets a DEMAND candidate through coarse return.
}
// Relevant root result: ZERO -> DemandTarget, D.

// Demand: none; this is the first run.
// Submitted: p.f.MUST/T,N.
// Initial: P = p.*/F; start p.*/F,N.
Result mapper(Root p) {
    Result out = initializedResult();
    if (flag) out.e.h.extra = p;
        // P -> out.e.ANY/F,D after the limit-1 cut.
    else out.e.h = p.f.g;
        // Read from the abstract p.* gives an ANY result.
        // The write is cut to out.e.ANY/F,D too.
    return out;
}
// NORMAL summary: p.*/F -> p.*/F.              // unchanged argument
// DEMAND summary: p.*/F -> ret.e.ANY/F.
// There is no NORMAL return summary.
```

The argument-preservation summary really exists. It cannot produce a
returned value: its conclusion base is p, not ret. The example does not
assume that an ordinary NORMAL identity is absent.

## 3. Run-2: root ANY removes the finer ANY head

This block recomputes the seam with the **latest selected C2**. It is not
a new native run. In the historical logs, the initial below was
`ret.e.ANY/F,D`; latest C2 instead emits `ret.e.*/F,N`. The two backward
paths still produce the relevant MAY conclusions under the same original.

```java
// Run-2, backward, field limit 1.
// The sink gives mapped.e.h.$/T; the limit-1 offer is mapped.e.ANY/T,D.
void root() {
    Root p = initializedRoot();
    sourceUniformT(p.f);       // Backward T requirements can reach this source.
    Result mapped = mapper(p); // Submits ret.e.ANY/T,D backward.
    sinkExactT(mapped.e.h);
}
// Root control/source-permission handling is the existing fixture pipeline.
// This block recomputes mapper DATA; it is not a new whole-driver run.

// Complete demand pair from run-1:
//   Dc = ret.e.ANY/F; Dp = p.*/F.
// Submitted: ret.e.ANY/T,D.
// Latest initial: P = ret.e.*/F; start ret.e.*/F,N.
// No exact-prefix companion: submitted and demand have the SAME head.
Result mapper(Root p) {
    Result out = initializedResult();
    if (flag) out.e.h.extra = p;
        // Backward out.e.* reaches inside the deeper write.
        // Candidate: P -> p.ANY/F,D.
    else out.e.h = p.f.g;
        // Backward write gives an ANY requirement on the RHS value.
        // Reverse the f.g read; limit 1 gives P -> p.f.ANY/F,D.
    return out;
        // Backward return binding starts with out.e.*/F,N.
}
// Before MAY canonicalization, SAME P and same headers:
//   P -> p.ANY/F,D
//   P -> p.f.ANY/F,D
// Retained summary: P -> p.ANY/F,D.
// Removed summary:  P -> p.f.ANY/F,D, covered spatially by the parent.
```

The two resulting forward demand pairs would be:

```text
D0 = (p.ANY/F,   ret.e.*/F)     retained
D1 = (p.f.ANY/F, ret.e.*/F)     removed
```

They have the same paired exit. The child is not removed because of a
different caller, mark, protection flag or port. Root ANY covers its set
of locations. The issue is that it does not select the same initial tail.

## 4. Run-3: the latest prefix companion does not restore MUST

These C2 lists are checked by
[MustAdmissionAudit](lean/proposals/subsumption-initial-demand-20261107/MustAdmissionAudit.lean).
The body annotations follow ordinary field transfer. No updated native
campaign is claimed for the complete program or its final finding time.

```java
// Run-3, forward, field limit 2.
// The real source still supplies p.f.MUST/T,N; this packet was not removed.
void root() {
    Root p = initializedRoot();
    sourceUniformT(p.f);
    Result mapped = mapper(p); // Submits arg0.f.MUST/T,N.
    sinkExactT(mapped.e.h);    // Listed coarse mapper return is ANY/T,D.
}
// Listed coarse return gives a DemandTarget, not a NormalTarget.
// The historical Current run-3 also had no NORMAL finding.

// Retained demand: D0 = (p.ANY/F, ret.e.*/F).
// Submitted: p.f.MUST/T,N.
// COMPLETE latest initial list from D0:
//   J1 = p.f.*/F,N             // primary: first new field
//   J0 = p.$/F,N               // NEW exact-prefix companion
// Both start as identities. Neither is p.f.MUST/F.
Result mapper(Root p) {
    Result out = initializedResult();
    if (flag) out.e.h.extra = p;
        // J1: writes a path longer than limit 2 -> out.e.h.ANY/F,D.
        // J0: exact root goes to out.e.h.extra.$/F, then is cut
        //     at limit 2 -> out.e.h.ANY/F,D.
    else out.e.h = p.f.g;
        // J1: first read f leaves an unknown correlated suffix;
        //     the g read gives RHS.ANY/F,D.
        // J0: p.$ cannot read p.f; no result on this branch.
        // J1's write gives out.e.h.ANY/F,D.
    return out;
}
// Relevant admitted DEMAND returns under the latest two originals:
//   p.f.*/F -> ret.e.h.ANY/F,D
//   p.*/F   -> ret.e.h.ANY/F,D   // raw J0 normalizes only at summary boundary
// There is no NORMAL return from these two probes.
// The saved run-1 p.* -> p.* argument identity still has no ret conclusion.
```

For comparison, **if the removed D1 were retained**, its SAME submitted
actual would add one stronger initial. This is a comparison of admission,
not a selected instruction to retain discarded history:

```java
// Counterfactual additional demand: D1 = (p.f.ANY/F, ret.e.*/F).
// SAME submitted actual: p.f.MUST/T,N.
// Additional initial: J2 = p.f.MUST/F,N. Same-head C2 preserves MUST.
Result mapper(Root p) {
    Result out = initializedResult();
    if (flag) out.e.h.extra = p;
        // This deep branch can still give a cut ANY/DEMAND result.
    else out.e.h = p.f.g;
        // MUST at p.f includes g: RHS.MUST/F,N.
        // Write: out.e.h.MUST/F,N; depth 2 fits.
    return out;
}
// Additional NORMAL summary: p.f.MUST/F -> ret.e.h.MUST/F,N.
// Additional DEMAND summary: p.f.MUST/F -> ret.e.h.ANY/F,D.
// Apply NORMAL return to the real p.f.MUST/T,N:
//   mapped.e.h.MUST/T,N -> the exact sink has a NORMAL witness.
```

This is why another STAR/FLOW probe is insufficient. A uniform fact says
that g has T. A correlated STAR query does not say that every suffix has T.
The exact prefix query can analyze the root, but cannot read the missing
first field. It is useful for other transfers; it does not supply J2 here.

The historical control records these two additional return rows, including
the NORMAL MUST row. Its first report is run-3. Historical Current reaches
the NORMAL finding in run-5. The late route is traced in sections 5-6. Native component checks derive
its mapper publications; whole-driver and full Conductor validation remain
separate obligations.

## 5. Run-4: exact backward analysis restores a NORMAL read

Run-4 has field limit 3. Keep both run-3 return originals. The latest
exact-prefix probe added the second one; omitting it would lose one paired
C5 result below.

```java
// Demand from root's run-3 sink: Target -> ZERO.
// Submitted at the reached backward root exit: ZERO,N.
// Emitted control initial: ZERO,N.
void root() {
    Root p = initializedRoot();
    sourceUniformT(p.f);       // Incoming p.f.g.$/T,N lies inside this source.
    Result mapped = mapper(p); // Backward result: p.f.g.$/T,N, plus p.f.ANY/T,D.
    sinkExactT(mapped.e.h);    // Starts mapped.e.h.$/T,N; depth 2 fits limit 3.
}
// The precise requirement reaches the actual uniform source at p.f.
// Source discharge uses the existing DemandTarget/source-permission path.
// Relevant control row: ZERO -> DemandTarget,D.

// TWO complete incoming demand pairs, from the TWO run-3 originals:
//   (ret.e.h.ANY/F, p.f.*/F)
//   (ret.e.h.ANY/F, p.*/F)
// Submitted: ret.e.h.$/T,N.
// ONE raw initial: ret.e.h.$/F,N. Start it as an EXACT identity.
// No prefix companion: actual and entry demand have the same head.
Result mapper(Root p) {
    Result out = initializedResult();
    if (flag) out.e.h.extra = p;
        // Backward: out.e.h.$/F cannot descend to extra.
        // This branch produces no p requirement.
        // A strong keep can retain local out.e.h.$/F with E={extra};
        // that local does not become an argument/return summary.
    else out.e.h = p.f.g;
        // Backward write: out.e.h.$/F -> RHS.$/F,N.
        // Reverse read f.g: RHS.$/F -> p.f.g.$/F,N.
    return out;
        // Backward execution starts here: ret.e.h.$/F -> out.e.h.$/F,N.
}
// Raw good-path candidate: ret.e.h.$/F -> p.f.g.$/F,N.
// Normalize the WHOLE FLOW pair only at publication:
//   ret.e.h.*/F -> p.f.g.*/F,N.
// Apply BOTH complete C5 pairs:
//   NORMAL: ret.e.h.*/F -> p.f.g.*/F,N.
//   DEMAND: ret.e.h.*/F -> p.f.ANY/F,D.
```

Both outputs come from the same raw exact analysis:

| Paired output selector | C5 budget | Selected result |
| --- | --- | --- |
| `p.f.*/F` | `min(3,1+1)=2` | `p.f.g.*/F,N`: two fields fit |
| `p.*/F` | `min(3,0+1)=1` | `p.f.ANY/F,D`: cut after one field |

The NORMAL STAR result does not subsume the broader ANY/DEMAND result.
Their tails, field paths and layers differ. In this exact mapper analysis,
there is no same-original root `p.ANY` output to remove the child demand:
the deeper bad write cannot consume the live EXACT fact.

**Do not execute the normalized STAR as the initial.** Doing that can make
the bad branch produce a root ANY requirement again. EXACT is the live
read barrier; STAR is the stored FLOW summary form.

At handoff, save the NORMAL row in its backward direction. Reverse only
the DEMAND row into the next forward demand:

```text
Saved backward NORMAL:
    ret.e.h.*/F -> p.f.g.*/F,N
Forward read of that saved record:
    p.f.g.*/F -> ret.e.h.*/F,N

Actual run-5 demand from the DEMAND row:
    Dc=p.f.ANY/F, Dp=ret.e.h.*/F
```

The child head missing at run-3 has therefore been produced by real
backward analysis in run-4. It was not recovered from discarded history.
The full root source-permission bookkeeping is unchanged; the native
component also checks the source-shaped discharge of `p.f.g.$/T,N`.

## 6. Run-5: two NORMAL routes, with a remaining DEMAND result

Run-5 has field limit 4. The uniform source at p.f is in budget. Saved
replay runs before current C2 admission.

```java
// Incoming root control demand follows the run-4 source discharge.
// Submitted control: reached ZERO,N. Emitted control initial: ZERO,N.
void root() {
    Root p = initializedRoot();
    sourceUniformT(p.f);       // Real p.f.MUST/T,N, with source permission.
    Result mapped = mapper(p);
        // Saved NORMAL inverse reader accepts p.f.MUST/T,N:
        // p.f contains g uniformly, so no STAR guess is required.
        // Result: mapped.e.h.MUST/T,N.
    sinkExactT(mapped.e.h);    // NORMAL exact witness -> NormalTarget(id).
}
// Source/saved-call/sink route: ZERO -> NormalTarget(id),NORMAL.

// Saved opposite NORMAL read:
//   p.f.g.*/F -> ret.e.h.*/F,N.
// Current complete demand pair:
//   (p.f.ANY/F, ret.e.h.*/F).
// Submitted: p.f.MUST/T,N.
// Current initial: p.f.MUST/F,N; same-head ANY admission keeps MUST.
Result mapper(Root p) {
    Result out = initializedResult();
    if (flag) out.e.h.extra = p;
        // Copy p's tainted f subtree to out.e.h.extra.f.MUST/F,N.
        // Four fields fit the GLOBAL run-5 limit 4.
    else out.e.h = p.f.g;
        // Read f, then g from the uniform region: RHS.MUST/F,N.
        // Write: out.e.h.MUST/F,N; depth 2 fits.
    return out;
}
// Apply the current pair's budget: min(4,depth(ret.e.h)+1)=3.
// Current NORMAL return:
//   p.f.MUST/F -> ret.e.h.MUST/F,N.
// Current DEMAND return from the bad branch:
//   p.f.MUST/F -> ret.e.h.extra.ANY/F,D.
```

There are two useful routes, not just the new initial:

1. Saved NORMAL replay already transports the real T to the sink. Its
   effective deeper STAR premise is satisfied by a MUST ancestor. The
   STAR-only ancestor restriction does not reject a definite MUST input.
2. Current C2 now has the regenerated same-head child demand and starts
   the missing MUST probe. Its good branch also gives a NORMAL result.

The old NORMAL argument identity still exists, but it is not the return
provider. The return provider used here is the row actually derived at
run-4. Neither route turns an actual DEMAND fact into NORMAL.

The bad-branch DEMAND is also real: its four-field raw output passes the
global limit but exceeds this paired C5 budget of three. The exact sink
at mapped.e.h does not read the deeper mapped.e.h.extra region. Still,
the callee has a DEMAND summary. Do not infer natural completion at run-5
from the NORMAL finding alone.

### What this establishes

For this small example, the updated operators restore a NORMAL sink route
at run-5. The missing run-3 MUST probe is a refinement delay; it is not,
by itself, proof of permanent finding loss. There is no need to assume
that the deleted child row is available during run-3.

Historical Current naturally finished run-5 with one finding. That runtime
used different MAY initials and a different later frontier. The updated
trace has the additional exact-prefix original and the run-5 DEMAND output
above. Its natural stop and complete later frontier require a whole-driver
check. No new full Conductor measurement or recovery claim is made here.

### Checked evidence for the late trace

The new [native component source](lean/proposals/subsumption-initial-demand-20261107/native-conductor-late-iterations-20261108/ConductorUniformLateIterationsTest.kt)
and [receipt](lean/proposals/subsumption-initial-demand-20261107/native-conductor-late-iterations-20261108/receipt.json)
record three passing checks on frozen baseline 528. They use the two traced
F3 paired rows as inputs and generate the B4/F5 summaries through real
method forms, live initials, normalization and C5. They also check the
opposite NORMAL reader on actual ancestor-MUST T and the typed source-shaped
discharge. No NORMAL method provider is supplied without a matching generated
B4 row. These checks do not run the full root/callee iteration driver or
register a real source-occurrence callback. The root control annotations
above show the required existing route, not a new captured root execution.

The [Lean late-iteration model](lean/proposals/subsumption-initial-demand-20261107/ConductorLateIterations.lean)
computes the latest F3 C2 initials and both ordinary mapper branch outputs,
then derives the B4 raw EXACT result, normalization and separate C5 images.
It computes the saved inverse and child handoff and checks F5 MUST admission
and both paired output restrictions. MUST values remain in a four-tail
representation; they are not passed through the older three-kind codec.
Native MUST body production is covered by the component checks, not silently
assumed to be a theorem of that older codec.

The [complete proof receipt](lean/proposals/subsumption-initial-demand-20261107/component-checks-1245.json)
and [axiom audit](lean/proposals/subsumption-initial-demand-20261107/component-axioms-1245.txt)
include the 36 new late-iteration statements. Their scope is the stated
operators and component route, not the full project or natural stop.

## 7. The exact captured Conductor query

The [E29 catalog](subsumption-principal-examples-20261107.md#e29-conductor-a-covered-location-set-can-lose-a-refinement-head)
and [snapshot report](../docs/reports/bidirectional-conductor-must-demand-snapshot-20261106.md)
contain the real event. The relevant call is Ops `startWorkflow` to
`createAndEvaluate`, Empty context, call 9, stage 3, ROOT scope `(0,-1)`,
run-3, global limit 2. Write `wfDef` for
`WorkflowModel.workflowDefinition:WorkflowDef` and `listener` for the
captured `this.taskStatusListener` field.

```text
Actual in BOTH native variants:
    arg0.wfDef.MUST/Graal, NORMAL, E={}, H=null.

Current row15, complete pair:
    (arg0.ANY/FLOW, this.listener.ANY/FLOW)

Control B row0:
    (arg0.ANY/FLOW, this.listener.ANY/FLOW)
Control B row16, additional complete pair:
    (arg0.wfDef.ANY/FLOW, this.listener.ANY/FLOW)

Captured historical Current returned:
    arg0.wfDef.STAR/FLOW,N
    arg0.wfDef.STAR/Graal,D

Captured historical B also returned:
    arg0.wfDef.MUST/FLOW,N
```

The full Current local snapshot has 77 paired rows; B has 175. There is no
Current wfDef.ANY entry in that complete DATA/ZERO projection. Static
completion/shared carry are absent. Target-entry rows cannot match this
nonzero DATA offer. These are the exact relevant pairs, not an assertion
that the callee has only one demand row globally.

Under latest C2, applying the retained root pair also adds
`arg0.$/FLOW,N`. Applying the removed child pair would still add the
distinct `arg0.wfDef.MUST/FLOW,N`. That local conclusion is established by
the admission model. Which additional demands and saved summaries the
latest full Conductor analysis would produce has not been measured here.

B later uses the extra MUST initializer as the original premise of an
actual `createAndEvaluateWithLock` call. This links the stronger initial
to real downstream work. It does not prove that this one event uniquely
causes either missing final report. The two exact Graal sink identities,
the successful historical rollback and all scope qualifications remain
in E29. A final Conductor recovery claim needs the complete selected
analysis, not just this local C2 equation.
