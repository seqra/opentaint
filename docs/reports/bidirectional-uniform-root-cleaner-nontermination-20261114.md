# Historical termination counterexample: uniform source and root cleaner

**Status after the 14 November decision:** this is no longer a termination
counterexample under the selected specification. The root-only selected
cleaner now preserves a same-head MUST and its input layer. The revised
reference stops at **run-1**. Sections 1–9 preserve the old-policy proof and
native **run-21** evidence; section 10 gives the new behavior and its
exact-root false-positive consequence. Production is unchanged.

14 November 2026. Follow [proof-guide.md](../../spec/proof-guide.md).
This counterexample includes the [non-empty-MAY spec](../../spec/non-empty-may.md),
[bounded refinement](../design/bidirectional-bounded-demand-refinement-20261114.md)
and [NORMAL uniform NE coverage](../design/bidirectional-normal-uniform-ne-coverage-20261114.md).
Production semantics are unchanged. A regression test is added.

**Result:** the same `ZERO -> DemandTarget, DEMAND` is generated in every
forward and backward run. The native test reaches and completes **run-21**;
it stops only at its test policy. The constructive proof has no iteration
limit. This sample has no loop, recursion, pass rule, static, alias, ND
condition, field cut or predefined method summary.

## 1. Code and rules

```java
void main() {
    Node x = sourceTreeT();
    removeTAtRoot(x);
    sinkTreeT(x);
}
```

These are configured rule APIs, with no analyzed bodies:

| API | Rule |
| --- | --- |
| `sourceTreeT()` | Ordinary unconditional source: assign T to the return value and all its descendants, `MUST/T`, NORMAL |
| `removeTAtRoot(x)` | Selected `RemoveMark(T)` at `x.$` with EXACT reach; remove T at the root only |
| `sinkTreeT(x)` | Ordinary unary sink: `ContainsMark(x.[any], T)` |

There is **no pass rule**. Ordinary call binding and identity transport
remain the normal interpreter machinery. The cleaner is the already
supported selected exact-root cleaner, not RemoveAll or a below-only
RemoveAll action. The sink includes both root and descendants.

The source contract can supply an object with a non-null `f` child.
After cleaning the root, that child still has T. Thus the example has a
real allowed source-to-sink route; it does not ask the analyzer to confirm
a cleaned exact-root sink. The field f is a concrete witness of that route,
not a field query added to the analysis.

Notation:

```text
U = [any-taint] / MUST; M = [any] / MAY
N = NORMAL; D = DEMAND; H = protected
Z = ZERO; DT = anonymous DemandTarget
[Dc ; Dp] = one paired incoming demand row
```

## 2. The unchanged cleaner row causes the loss

The current scalar and tree kernels agree:

```text
removeTAtRoot(x), input x.U/T,N:
    cleanPos = PART
    output   = x.U/T,D,H

removeTAtRoot(x), input x.M/T,D:
    cleanPos = PART
    output   = x.M/T,D,H

controls:
    input x.$/T   -> killed
    input x.f.$/T -> kept on its original layer, protected
```

The first row preserves the MUST shape but loses NORMAL support. It does
not prove that the cleaned root still has T. This is the existing partial
cleaner approximation; it is not a new cleaner or mark-group rule.

Native anchors:

- [cleanPos and concPart](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Reference.kt)
  classify a root-only cleaner against a same-root MUST as PART. It is
  outside the special one-field-below and BELOW cases, so concPart marks
  the result DEMAND without changing its tail.
- [TaintClean](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Clean.kt)
  implements the same scalar row.
- [ApOps.clean](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/ApOps.kt)
  retains the selected survivor's protection.

The survivor's explicit field length is zero. Increasing the field limit
cannot change this operation. There is no discarded concrete suffix.

## 3. Run-1: forward, limit 1

The only analyzable block is main. The source, cleaner and sink act at
their ordinary statement positions.

```java
// Demand: unrestricted run-1.
// Submitted: Z,N at the method entry.
// Emitted initial: Z -> Z,N.
void main() {
    Node x = sourceTreeT(); // Z -> x.U/T,N. Source permission is implicit in run-1.
    removeTAtRoot(x);       // Z -> x.U/T,D,H. No field cut occurred.
    sinkTreeT(x);           // U overlaps the sink, but its support is D.
                            // Emit Z -> DT,D and remember this sink seed.
    return;
}
// Published NORMAL: Z -> Z.
// Published DEMAND: Z -> DT.
// Published DATA: none; x is local and main returns void.
// Handoff to run-2: [Target ; Z]. Sink seed: sinkTreeT's real occurrence.
```

The source's `Z -> x.U/T,N` is a rule effect at its own statement.
It is not a method-exit DATA summary after the cleaner.

## 4. Run-2: backward, limit 1

As requested, backward publications are above the block; demands,
submitted facts and emitted initials are below it.

```java
// Published NORMAL: Z -> Z.
// Published DEMAND: Z -> DT.
// Published DATA: none.
// Source hit: sourceTreeT; permit that source in run-3.
void main() {
    Node x = sourceTreeT(); // Reverse application of the NORMAL source:
                            // x.M/T,D,H overlaps its whole-object T image.
                            // The reversed ZERO result becomes Target.
                            // Emit Z -> DT,D; record the actual source hit.
    removeTAtRoot(x);       // Backward x.M/T,D -> x.M/T,D,H.
                            // A possible descendant survives root-only cleaning.
    sinkTreeT(x);           // Seed Z -> x.M/T,D at this sink occurrence.
    return;
}
// Demand: [Target ; Z].
// Submitted: Z,N at the method's backward entry, the normal exit.
// Emitted initial: Z -> Z,N.
// Statement-generated sink requirement: Z -> x.M/T,D.
// Handoff to run-3: [Target ; Z]. Source permission: sourceTreeT.
```

`x.M/T` above is a **conclusion generated by the sink**. It is not an
owned initial or a MAY premise. The only owned initial remains ZERO.
Backward matching uses the existing weak native view of the NORMAL
whole-object source; no backward MUST initial is introduced.

## 5. Every later forward run

For every k >= 1, run-(2k+1) has field limit 2k and this same trace:

```java
// Demand: [Target ; Z].
// Submitted: Z,N. Source permission: sourceTreeT, from the preceding run.
// Emitted initial: Z -> Z,N.
void main() {
    Node x = sourceTreeT(); // Z -> x.U/T,N.
    removeTAtRoot(x);       // Z -> x.U/T,D,H, exactly as in run-1.
    sinkTreeT(x);           // Z -> DT,D; no NORMAL witness is available.
    return;
}
// Published NORMAL: Z -> Z.
// Published DEMAND: Z -> DT.
// Published DATA: none.
// Handoff: [Target ; Z]. Sink seed: sinkTreeT.
```

In particular, run-3 and run-5 emit the **literal same** nonempty demand
set. This is not only repetition involving the special first run.

## 6. Every later backward run

For every k >= 1, run-(2k+2) has field limit 2k+1:

```java
// Published NORMAL: Z -> Z.
// Published DEMAND: Z -> DT.
// Published DATA: none.
// Source hit: sourceTreeT.
void main() {
    Node x = sourceTreeT(); // x.M/T,D,H -> reversed ZERO -> Target,D.
    removeTAtRoot(x);       // x.M/T,D -> x.M/T,D,H.
    sinkTreeT(x);           // Z -> x.M/T,D from the retained sink seed.
    return;
}
// Demand: [Target ; Z]. Submitted: Z,N at the normal exit.
// Emitted initial: Z -> Z,N.
// Handoff: [Target ; Z]. Source permission: sourceTreeT.
```

## 7. Why the complete proposed approach cannot retire it

| Mechanism | Result in this example |
| --- | --- |
| Non-empty-MAY field cuts | No concrete field is cut; all analyzed DATA paths have length zero |
| MAY/MAY C2 splitting | No DATA C2 query exists; only ZERO is admitted |
| Bounded next-field refinement | There is no local DATA original to split or next field lost by a cut |
| Original paired C5 | Target accepts ZERO; paired ZERO exit accepts Target, so the terminal passes |
| NORMAL precoverage before relative C5 cuts | There is no relative cut or duplicate NORMAL DATA relation |
| New NORMAL uniform FLOW-to-NE law | The method exports a typed ZERO-to-Target terminal, not a FLOW/MUST-to-FLOW/NE relation |
| Mark and protection isolation | The intermediate survivor is concrete T and protected; the new neutral FLOW rule cannot remove it |
| NORMAL persistence | There is no NORMAL sink witness or `Z -> NormalTarget` to replay |
| Target policy | DemandTarget counts as outgoing refinement demand; NormalTarget's duplicate rule does not apply |

Even extending a path limit to infinity would leave this particular
partial-cleaner operation unchanged. A hypothetical cleaner FLOW complement
excludes T and cannot supply a NORMAL T witness either. No such companion
analysis is needed in this root-only program.

## 8. Uncapped proof

Let R = `[Target ; Z]`. Let F be the forward capture consisting of NORMAL
`Z -> Z`, DEMAND `Z -> DT`, and the sink permission. Let B contain the same
summaries and the source permission. The executable model computes:

```text
F1([], no source permission) = F
handoff(F) = {R}
B({R}, F.sinkPermission) = B
handoff(B) = {R}
for every n >= 0:
    F_(n+3)({R}, B.sourcePermission) = F

therefore, by induction on complete forward/backward rounds:
    for every k >= 0:
        handoff(F_(2k+1)) = {R}
        handoff(B_(2k+2)) = {R}
```

Every target is recomputed from a source/cleaner/sink execution. No old
demand or permission is copied unconditionally. A missing source or sink
permission causes the corresponding model run to emit nothing; the cycle
itself supplies both permissions. Each round has a finite constant fact
domain. The failure is infinite outer refinement, not a nonterminating
method work queue.

The [constructive Lean model](../../spec/lean/proposals/uniform-root-cleaner-cycle-20261114/RootCleanerCycle.lean)
checks these equations, the induction, cleaner rows, zero-length bounds,
paired control intersection and the absence of NORMAL targets. Its checker
first rechecks the complete preceding approach and its old/new regressions.
Result: **20 new claims, 312 including dependencies, 18 modules**, all
passing without classical/custom axioms or proof holes.

This is a counterexample under the explicitly retained selected-cleaner
semantics. It introduces no semantic change or suggested production fix.

## 9. Native regression and controls

[UniformRootCleanerTerminationTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/UniformRootCleanerTerminationTest.kt)
builds this program from the ordinary source rule, cleaner action and sink
rule, without predefined method summaries or DATA handoff injection.
It observes one `Z -> DT` and zero DATA method summaries in every run
from **run-1 through run-21**, with no NormalTarget. The explicit 21-run
test policy is only a finite observation bound; the induction above is
the non-termination proof.

| Native control | Result |
| --- | --- |
| Remove the cleaner | NORMAL finding, stop at run-1 |
| Clean T at-and-below the root | No finding, stop at run-1 |
| Keep root-only cleaner; make sink exact-root | No finding, stop at run-3; backward cleaning kills its seed |
| Replace the uniform source with precise `x.f.$/T` | Child survives normally; finding and stop at run-1 |

All **5 new native tests** and **5 existing selected-cleaner tests** pass.
The native core does not yet implement NE, but the proposed new-tail,
refinement and coverage paths are provably inapplicable here. Their full
earlier proof package is included in the counterexample's checker.

Reproduce:

```sh
python3 spec/lean/proposals/uniform-root-cleaner-cycle-20261114/check.py \
  --out /tmp/uniform-root-cleaner-proof

cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests 'org.opentaint.dataflow.bidi.UniformRootCleanerTerminationTest' \
  --tests 'org.opentaint.dataflow.bidi.SelectedStarCleanerRepairTest' \
  --console=plain --max-workers=1
```

External proof receipt: `uniform-ne-counterexample-20261114/proofs-v2/receipt.json`
under the report-data archive. Native receipts and XML are stored beside it,
outside Git. No project scan was run. Historical reached/completed/accepted
forward positions remain OWASP **run-11/11/11**, Conductor **run-8/7/7**,
Stirling-PDF **run-11/10/9**.

## 10. Selected MUST-preserving revision

Scope: selected T, EXACT reach, same base and path as a concrete MUST/T.
Keep the input layer and the existing survivor protection. This does not
change exact-point facts, MAY/STAR partial rows, other positions or whole-
position cleaning.

```text
before: x.MUST/T,N -> x.MUST/T,D,H
after:  x.MUST/T,N -> x.MUST/T,N,H

input already DEMAND:
        x.MUST/T,D -> x.MUST/T,D,H    // no upgrade to NORMAL
```

Updated complete trace:

```java
// Run-1, limit 1. Demand: unrestricted. Submitted: ZERO,N.
// Initial: ZERO -> ZERO,N.
void main() {
    Node x = sourceTreeT(); // ZERO -> x.MUST/T,N.
    removeTAtRoot(x);       // ZERO -> x.MUST/T,N,H, by the new rule.
    sinkTreeT(x);           // ZERO -> NormalTarget(treeSinkId),N.
    return;
}
// NORMAL summaries: ZERO -> ZERO; ZERO -> NormalTarget(treeSinkId).
// DEMAND summaries: none. Handoff demand: empty. Stop at run-1.
// Run-2 and later: not executed.
```

This closes the repetition. It also changes the earlier exact-root sink
control. Under the original concrete cleaner, the root loses T, but the
retained NORMAL MUST still asserts it:

```java
// Run-1. Demand: unrestricted. Submitted/initial: ZERO,N.
void main() {
    Node x = sourceTreeT(); // x.MUST/T,N.
    removeTAtRoot(x);       // x.MUST/T,N,H under the selected revision.
    sinkExactlyAtRootT(x);  // NormalTarget(rootSinkId),N: a false positive
                            // under the original concrete cleaning behavior.
    return;
}
// No DEMAND. Stop at run-1, so later refinement cannot discard that report.
```

The [policy model](../../spec/lean/proposals/uniform-root-cleaner-cycle-20261114/RootCleanerPolicy.lean)
constructively checks layer preservation, unchanged non-MUST rows,
run-1 completion and the exact-root NORMAL false-positive witness. It does
not claim that this revision preserves all precise findings under the old
concrete cleaner meaning. No other cleaner or Target rule is changed.

Latest proof package: **321 audited claims in 19 modules**, including
**9 checks for the new policy** and the 20 historical counterexample claims.
The fresh external receipt is
`uniform-ne-counterexample-20261114/must-preserving-policy-v1/receipt.json`.
The native test still measures the old production rule; implementing the
selected revision will require updating that baseline test's expectations.
