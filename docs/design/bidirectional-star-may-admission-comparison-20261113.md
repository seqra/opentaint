# STAR emission and MAY admission: comparison

13 November 2026. Design analysis only; production code is unchanged.
Source baseline: `374fa3c6f`; documentation HEAD at this check: `2bed8939b`.
Follow [the proof guide](../../spec/proof-guide.md).

The user proposes emitting STAR instead of MAY, interpreting submitted STAR
like MAY during initial emission, and keeping MAY as an explicit loss of
precision. This replaces the EXACT/MAY-start candidate, not the production
implementation. The production implementation already emits STAR in the
old MAY-start cells.

## 1. Concrete difference

Write F for FLOW, T for a full mark, N for NORMAL and D for DEMAND. The
table shows spatial primary admission; existing companions, layers, marks,
budget, static anchors and exclusion guards remain separate obligations.

| Demand | Submitted | Production C2 | Proposed STAR-as-MAY submitted view |
| --- | --- | --- | --- |
| `x.[any]/F` | `x.[any]/T` | `x.*/F` | `x.*/F`: already the same |
| `x.[any]/F` | `x.*/T` | `x.*/F` | `x.*/F`: already the same |
| `x.[any]/F` | `x.f.g.[any]/T` | `x.f.*/F` | `x.f.*/F`: already the same |
| `x.f.[any]/F` | `x.[any]/T` | `x.f.*/F` | `x.f.*/F`: already the same |
| `x.f.[any]/F` | `x.*/T` | No initial | `x.f.*/F`, if actual E admits f: new admission |

The new admission makes a STAR offer survive nested calls whose demand
head is deeper. It does not require a new tail or a STAR_OR_ANY marker.

This comparison interprets “treat STAR as MAY” on the **submitted** side.
Interpreting a STAR **demand** as MAY too is a separate change: it would
remove the selected later-run rejection of deeper inputs under STAR demand.
That additional change is not assumed here.

Do not erase actual E to create a descendant binding. MAY's Empty E cannot
make an excluded field accessible. Do not change intrinsic concrete STAR
layers or upgrade a projected caller's D support to N as part of a rename.
The truncation certificate and the C5 image also need the new admission;
changing only the scalar C2 tail test leaves their contract inconsistent.

Production source: [C2 and its family](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/RestrictedInitialPolicy.kt),
[ordinary field transfer](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Reference.kt),
[FLOW normalization](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/FlowSummaryNormalization.kt).

## 2. What remains after the rename

At a fact level, STAR and MAY can both stand for an unknown suffix. At a
relation level, STAR-to-STAR preserves the **same** suffix. A MAY output
can lose the relation between the input suffix and the output suffix.
That distinction exists in production before this proposal.

The new STAR-start query reproduces the two branches below using ordinary
native field micro-edges. There is no admitted MAY view in this trace.

```java
// Conditional FLOW query start:
//   x.f.*/F -> x.f.*/F, N
Object choose(Object x) {
    if (b) return x.f;
    // Same-head read:
    //   x.f.*/F -> ret.*/F, N

    return x.f.g;
    // Read below the unknown suffix:
    //   x.f.*/F -> ret.[any]/F, D
    // The suffix correlation was lost here. No field-limit cut is needed.
}
// Candidate relations before any demand-specific output selection:
//   S: x.f.*/F -> ret.*/F,     N
//   R: x.f.*/F -> ret.[any]/F, D

// Original precise offer at a caller:
//   x.f.g.$/T, N
// S application: ret.g.$/T, N
// R application: ret.[any]/T, D
// Executing the second branch on that precise binding: ret.$/T, N
```

Both offered-value and result tails are legal in the proposed policy.
The starred start fixes the premise mismatch from the older MAY-start
candidate, but genuine MAY output from the second branch remains.
This is the intended distinction. **R is not selected for subsumption by
S**, because their conclusion tails differ. This trace does not expose an
unresolved gap in the user's proposed same-tail subsumption. The earlier
interpretation that every genuine MAY-loss row had to be deleted was wrong.

The precise correlation issue can be written without tail terminology:

```text
S(s,t) := t = s
R(s,t) := true                 // approximation after correlation loss

s = g, t = epsilon:
    R(s,t) holds; S(s,t) does not hold.
```

Thus S does not cover R's original-offer application, and the selected
conclusion-tail guard correctly retains R. No new NORMAL-provider view
service is needed to erase R: erasing it is not part of the selected rule.

## 3. Effect on FL+1 repetition

STAR-as-MAY admission is not itself a workload reduction. The new cell
admits an offer which production rejects. It can add starts and resulting
work. Later NORMAL discoveries and existing subsumption could compensate,
so admission counts alone do not prove a net regression either.

Truncation evidence is a separate potential reduction. The selected
empty-binding filter has this behavior:

```text
Cut:      x.f.g.h.[any] -> x.f.[any]
Evidence: g.h.[any]; epsilon is excluded

Offer x.f.$:    reject the exact empty payload binding
Offer x.f.*:    do not reject the whole region: it includes g.h
Offer x.f.g.*:  compatible with a nonempty refinement
```

For the broad STAR offer, the proposed emitter can start x.f.* again.
Changing its admission meaning to MAY does not make it a singleton empty
binding. The empty-only certificate therefore does not prove that this
STAR-driven recurrence is eliminated. Unknown/uncut contributions also
widen the certificate to allow epsilon, by design.

The mechanism can remove proved irrelevant exact-root offers. It has no
proved benefit for a cycle whose regenerating offers remain STAR. Before
claiming an FL+1 fix, trace a complete repeated handoff row through both
directions under this policy and identify the exact operation that either
advances its known field prefix or removes its next recurrence. A tail
rename, an extra admission, or a same-tail subsumption opportunity alone
is not that progress proof. Use an uncapped iteration driver; the temporary
run-11 limit supplies no evidence of convergence.

## 4. Checked evidence

The [native regression](../../scripts/demand_experiments/dual-starts/ProjectedMayCoverTest.kt)
passes against the current AP implementation. Its STAR-start assertions
check both candidate relations and both original-offer applications above.

[StarAdmissionComparison.lean](../../spec/lean/proposals/exact-may-evidence-policy-20261113/StarAdmissionComparison.lean)
constructively checks the new descendant-admission cell, the unchanged MAY
cell, the loss event, the concrete relation witness, and the difference
between original and coarsened application. It also checks that the
conclusion-tail guard retains the genuine MAY row and that empty-only
evidence does not reject a broad STAR. Ten additional declarations
pass; the complete component package now audits 66 declarations. These are
component proofs, not a proof of a complete new STAR policy.

Frozen native data: `exact-may-evidence-policy-20261113/star-start-cover-v1/`.
Frozen Lean data: `exact-may-evidence-policy-20261113/proofs-v4/`.
Both are under the [external data root](../reports/EXTERNAL_DATA.md).

No new project scan was run. Historical latest reached/completed/accepted
forward positions remain OWASP **run-11/run-11/run-11**, Conductor
**run-8/run-7/run-7**, and Stirling-PDF **run-11/run-10/run-9**.
