# Definite MUST replay: termination approach update

16 November 2026. Synthetic data-flow reachability. FULL marks.
Revised complete reference stop: **run-5** for each of the three concrete
replay examples. Earlier multi-owner references retain their stops, latest
**run-15**. Unchanged native diagnostic captures complete **run-31** at the
policy cutoff. Production is unchanged.

Follow [proof-guide.md](../../spec/proof-guide.md).
[Current consolidated rules](../design/bidirectional-demand-termination-approach-20261115.md).

## 1. Root cause and selected change

The new counterexample is not a field-cut cycle. All relevant paths fit one
field. A saved native MUST premise can currently use two input lanes:

```text
definite lane: actual proves the uniform premise
residual lane: actual only overlaps it; results become DEMAND after return
```

The second lane can reproduce the same provisional output forever, although
current demand is empty. A current MUST summary already rejects this input.

**Selected major change:** use that existing definite MUST check for saved
native MUST records too. Omit the residual lane. Keep every NORMAL record,
the original actual and ordinary C2 lookup. Apply the shared rule at calls,
inner block links, loop replay and saved-service probes. Concrete and FLOW
MUST inputs use the same rule. The existing opposite-direction reverse
views are unchanged; they do not create a backward MUST initial.

```text
nativeSavedLanes(matchedActual, initial):
    if initial.tail != MUST:
        return existingNonMUSTLanes(matchedActual, initial)
    actual = currentSatisfying(matchedActual, initial)
    return [] if actual is empty else [Lane(actual, pendingDemotion=false)]

onCallOffer(original):
    apply saved records through nativeSavedLanes
    plan = ordinary complete C2 lookup(original)
    if plan nonempty:
        emit its initials
        apply and subscribe to current summaries as before
```

A rejected saved record does not mean that the method cannot produce a
result. It only means that this record's premise is not proved. The method's
ordinary demand admission still handles required new input patterns.

This changes saved premise matching. It is not a storage optimization and
is not a new general subsumption rule. It adds no query, head, cache, suffix
evidence or method replay channel. It does not retire observations because
their reports are already confirmed. Such retirement would not repair the
same unsupported reply at an unconfirmed observation.

## 2. Uniform input coverage

For MUST actual A and MUST requirement P, retain all existing base and mark
checks. Uniform coverage requires:

| Geometry | Required check |
|---|---|
| A and P have the same head | A.E is a subset of P.E |
| A is a strict ancestor of P | The first field towards P is not excluded by A.E |
| A is below P or disjoint | Reject |

At the same head, the actual must prove every point which the premise has
not excluded. At a descendant head, the parent exclusion stays at its own
scope. Do not copy it onto the child.

```text
actual p.MUST/T {f}; required p.MUST/T {f,g}: accepts
actual p.MUST/T {f}; required p.MUST/T {}:    rejects
actual p.MUST/T {g}; required p.f.MUST/T {g}: accepts (f != g)
actual p.MUST/T {f}; required p.f.MUST/T {}:  rejects
actual p.f.MUST/T;   required p.MUST/T:      rejects
```

In the last case p itself is an explicit required location not proved by
the child fact. This does not declare p unmarked. It declines to treat an
unproved uniform requirement as satisfied.

Use the existing `ops.satisfying` operation, not a new scalar production
matcher. Packed inputs can have supported and unsupported members. Retain
the supported lane unchanged. Keep its full original, ports, mark, E/mx, H
and call continuation. A valid ND execution still needs all required arms.

## 3. New different-path example

```java
class Box { Box f; Box g; }
Box make(Box p) {
    Box r = new Box();
    // Rule 0: CM(p.g.MAY,T) => assign U at r.MUST.
    // Rule 1: CM(p.MAY,T)   => assign U at r.f.MUST.
    return r;
}
void root() {
    Box a = new Box(); // Entry marking: a.f.MUST/T,N.
    Box b = new Box(); // Entry marking: b.MUST/T,N.
    Box x = make(b);
    Box y = make(a);
    // Observe U anywhere under x and under y.
}
```

The two methods are straight-line. The call graph is acyclic. There is no
cleaner, pass rule, alias, static, unresolved body or intrinsic MAY target.
The rules generate distinct U from T. The full historical per-run trace is
[embedded here](bidirectional-different-uniform-reply-nontermination-20261116.md).
The revised model uses the same C2, qualified heads, bounded children, raw
C5, real cuts, packet canonicalization, source permissions and Target rules.
Only saved MUST lane selection changes.

### Cold states

| Completed run | Current make demand for the next run | Retained NORMAL U records | NORMAL reports | Root D Target |
|---|---:|---:|---|---|
| run-1 | 2 qualified rows | 0 | none | yes |
| run-2 | 7 paired rows | 0 | none | yes |
| run-3 | 2 qualified rows | 5 | 0 | yes |
| run-4 | 2 paired rows | 5 | 0 | yes |
| run-5 | empty | 7 | 0, 1 | **no — natural stop** |

Runs 1–4 are exactly the historical states, not a selected warm start. The
model retains the additional p.g queries and all seven scalar NORMAL
members:

```text
p.g.MUST/T -> ret.$/U,N
p.g.MUST/T -> ret.MUST/U,N
p.MUST/T   -> ret.MUST/U,N
p.g.MUST/T -> ret.f.$/U,N
p.MUST/T   -> ret.f.$/U,N
p.f.MUST/T -> ret.f.$/U,N
p.f.MUST/T -> ret.f.MUST/U,N
```

### Decisive run-5 trace

```java
// Demand: [p.f.MAY/T | ret.f.$/U], [p.f.MAY/T | ret.f.*/U].
// Submitted: p.MUST/T,N from b; p.f.MUST/T,N from a.
// Emitted initial: p.f.MUST/T -> p.f.MUST/T,N.
Box make(Box p) {
    Box r = new Box();
    // p.f is incomparable with p.g: rule 0 does not fire.
    // Rule 1 gives r.f.MUST/U,N.
    return r;
}
// Published new NORMAL summaries:
//   p.f.MUST/T -> ret.f.$/U,N
//   p.f.MUST/T -> ret.f.MUST/U,N
// Published D: none. All five older NORMAL members remain.

// Demand: [Target | ZERO]. Initial: ZERO -> ZERO,N.
// Entry marking permissions from run-4: {a,b}.
void root() {
    Box a = new Box(); // ZERO -> a.f.MUST/T,N.
    Box b = new Box(); // ZERO -> b.MUST/T,N.
    Box x = make(b);   // Broad MUST premise is definitely satisfied.
                      // x.MUST/U,N and x.f.$/U,N remain.
    Box y = make(a);   // Broad parent premise: reject its saved lane.
                      // p.g premise: disjoint, reject.
                      // Precise f premise: y.f.$/U,N; y.f.MUST/U,N.
    // Both observations have NORMAL witnesses.
}
// New: ZERO -> NormalTarget(1),N. Report 0 is already retained.
// New DemandTarget: none. No DATA demand. The forward stop rule applies.
```

The repair does not depend on waiting for another reply. With only the
broad record present, the unsupported input still gives no reply. No
confirmed-report set is consulted. If observation 1 instead checks U at
the exact root y, the precise child reply does not prove it. The proof and
native checks explicitly exclude an invented root result.

### Uncapped result

The complete revised state after run-5 has empty DATA and Target frontiers,
both retained reports and all seven NORMAL records. If forced to continue,
run-6 has no backward observation seed and is idle. Constructive induction
proves `history(n+6)=idle` for every natural n. This is independent of the
run-11 policy, field-limit growth or a finite capture.

## 4. Earlier exact and uniform cases

Their rule checks T somewhere under p, then generates U exactly at r or
uniformly at r. Both have the original actuals b.MUST/T and a.f.MUST/T.
No field pass is introduced.

```text
run-3: demand p.MAY/T; actual p.f.MUST/T,N
       C2 starts p.f.*/T,D plus its existing FLOW companions
       producer generates U,D; ordinary C5 retains the demand

run-4: reversed producer requires p.MAY/T
       paired p.f.* permission selects p.f.MAY/T

run-5: actual p.f.MUST/T,N now starts p.f.MUST/T,N
       producer generates U,N under the precise p.f premise
       broad saved p.MUST premise is rejected for this actual
       precise current p.f premise applies normally
```

Thus removing provisional saved replay does not remove their true field
input route. Their ordinary current demand supplies it. Their cold states
through run-4 stay unchanged, and both now stop at **run-5**. The exact case
retains both NORMAL records. The uniform case retains all four scalar
NORMAL records, including the additional exact outputs. Both retain both
findings. Each has an uncapped no-revival proof.

The earlier identical definite-reply absorption remains a valid ready-packet
rule. Its historical run-7 references remain unchanged proof dependencies.
The new matching rule prevents the unsupported provisional reply before
that filter is needed. It does not broaden cross-path reply subsumption.

## 5. Earlier reference set and scope

The prior 18 multi-owner cold references use `OverwriteReplay.apply`, which
already requires definite MUST coverage, including real E. A generic Lean
function-equality theorem proves that adding the new gate changes none of
those read results. Their owner execution, calls, current admission and
native reverse views therefore keep the existing complete cold certificates.
Their terminal frontier and report sets are rechecked together.

| Prior reference | Natural final run, unchanged |
|---|---:|
| Two calls in the body | run-15 |
| Growth | run-11 |
| Long reader | run-5 |
| Nested saved reader | run-9 |
| Deep nested write | run-5 |
| Exact nested-write input | run-3 |
| Larger nested-write path | run-11 |
| Nested-write negative | run-3 |
| Nested-write positive | run-3 |
| Nested-write survivor | run-5 |
| Original BB variant | run-5 |
| Original method variant | run-5 |
| Ordinary two-branch body | run-3 |
| Saved replay with overwrite/E | run-9 |
| Postfix wrapper | run-13 |
| Prefix wrapper | run-9 |
| Prefix/postfix wrapper | run-11 |
| Round-trip wrapper | run-9 |

These preserve their existing reference report sets, including both empty
sets. Existing independently documented model-alignment limits are not
silently repaired. The protected uniform closure already requires uniform
input support and retains its run-3 proof. The selected root cleaner has no
saved MUST replay step and retains its run-1 result. No excluded special-pass
model is added to the acceptance scope.

This is not a global completeness or termination proof for arbitrary code.
In particular, preserving every old NORMAL final DATA output does not alone
prove preservation of every possible later finding: removed D guidance can
affect later source permissions. The complete supplied cold traces prove
that those permissions remain sufficient in these cases. Native integration
must validate the same property for broader alias/call/static workloads.
An inapplicable record is not a semantic proof that the method has no effect.
The proposal adds no fallback when current demand is empty.

## 6. Proof and work bounds

[Proof package](../../spec/lean/proposals/definite-must-replay-20261116/README.md):
**64 new constructive claims; 2,395 audited claims across 121 modules**.
Every prior dependency source hash is checked. Only `propext` and
`Quot.sound` are permitted. No custom assumptions, proof holes, classical
choice or external decision oracle is used.

The generic lane proof treats the original continuation as an executable
function. A retained lane passes the identical actual to it. Its fields,
marks, E/mx, H, ports and original are not rewritten. Removing a lane adds
no output; any old final DATA output with NORMAL support must have come
from a definite lane and is preserved. The uniform-region proof constructs
the suffix showing that every required location is supported by the actual.

This does not preserve every effect of the old unsupported branch: that
branch and its return/alias callbacks are deliberately not run. Effects on
valid definite branches stay unchanged. The generic normal-output theorem
must not be cited as a proof about all independent callback side effects.

No additional input or summary family is created. The native read already
computes the definite part. Omitting residual construction can also avoid
its subtraction, demotion, return work, output propagation and resulting
observations. Fixed-input saved work and output are subsets of the old work.
No suffix composition or path expansion is needed to obtain this saving.

## 7. Native validation and reproduction

Production revision: `966a40c3647268cc006e5776591d6b68849379d0`.
The test-only adapter filters the existing `matchRecord` lanes, then invokes
the real `applyMatchedRecord` operation. Seven new tests cover:

1. Rejecting a lone unsupported broad MUST, without a replacement reply.
2. Preserving a precise field reply and an actual DEMAND layer.
3. Equality with current application in 56 concrete matching cells.
4. Literal protected output and real output E.
5. A definite application followed by a real caller-side cut: D survives.
6. Unchanged ordinary STAR service.
7. FLOW MUST matching and the ordinary correlated STAR provider.

Together with the existing support class and three native cycle classes,
**24 tests pass**. The three unchanged driver captures still complete
**run-31** with their two NORMAL reports and recurring Target. They remain
controls for the unpatched production policy. The native adapter does not
claim integrated production termination; the latest-policy cold models
provide the run-5 results.

```bash
python3 spec/lean/proposals/definite-must-replay-20261116/check.py \
  --out /tmp/definite-must-replay-proofs
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.DefiniteMustReplayNativeTest \
  --tests org.opentaint.dataflow.bidi.DefiniteReplySupportNativeTest \
  --tests org.opentaint.dataflow.bidi.DifferentUniformReplyCycleTest \
  --tests org.opentaint.dataflow.bidi.ProvisionalMustReplayCycleTest \
  --tests org.opentaint.dataflow.bidi.ProvisionalUniformReplayCycleTest
```

Bulk proofs and logs are outside the repository at
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/definite-must-replay-20261116/`.
No new project scan or production change is included.
