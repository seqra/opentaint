# Demand policy review: complete models and directional composition

Date: 28 October 2026. Status: verification note. Runtime code is unchanged.

This note reviews the four proposed changes to
[demand storage](../../spec/demand-storage-and-spring-cleanup.md) and its
[lookup rules](../../spec/demand-storage-lookup.md). It does not silently
replace the previous semantic contract. The main counterexample uses FULL
marks, the current default. It does not require another analyzer configuration.

## 1. Findings

| Proposal | Finding |
|---|---|
| Predefined summaries are complete; do not analyze the method | Valid trusted-model boundary. Specify control, exceptional outcomes and rule observations too. Transfer completeness alone does not preserve sink reports. The old ZERO-actor design must be removed or replaced explicitly. |
| Stop when no further result can be added | Valid with a result-coverage certificate. Location coverage or `Facts.equals` is insufficient. |
| A FLOW demand does not emit T from an actual T | Correct local AP rule. The further claim that an absent direct T demand proves T irrelevant is false for a wrapper with a marked operation. |
| FLOW may be refined on the left; a marked left result cannot instantiate a right FLOW premise | This removes some required completed demands under the current request mechanism. It also makes binary composition non-associative. It must not change ordinary executable FLOW application. |

For composition below, arrows have the same **forward seed orientation** as
the lookup spec: writer, bridge, then reader. Backward demand is obtained
by swapping the completed endpoints. Changing orientation changes which
operand supplies the mark need; these rules cannot be transferred between
orientations without a proof.

## 2. Complete predefined models

Selected update: predefined methods skip method entry and exit rules. They
create no analyzer or boundary observer. Call-site rules remain active. The
current [implementation proposal](bidirectional-demand-storage-predefined-summaries-implementation-20261028.md)
implements this decision. The counterexample below records the intentional
boundary-observation difference; it is no longer an unresolved choice.

Select the new contract explicitly:

```text
predefined model present:
    summaries are authoritative and complete
    do not create a method analyzer, including a ZERO-only analyzer
    do not append inferred, unresolved or default identity summaries
```

A model must state its normal control return and any exceptional returns.
Absence of a data row is not an unknown-effect fallback. Ordinary caller-local
handling and independently configured call-site effects keep their declared
owners; they must not disappear through an accidental plan bypass.

### 2.1 Counterexample to completeness of transfer rows alone

```java
void main() {
    __spring_dispatcher__.__cleanup__();
}
```

Configured rule:

```text
MethodExitSink:
    method = generated cleanup, or anyFunction()
    condition = true
    occurrence = cleanup-exit
```

The current provider permits a generic exit sink on generated cleanup.
Genuine ZERO reaches the ordinary cleanup exit, so this rule reports.

The proposed complete transfer rows can be exactly correct:

```text
ZERO -> ZERO
S.__spring_registry__.* / FLOW -> S.__spring_registry__.* / FLOW
```

Applying only these rows preserves returned facts but emits no `cleanup-exit`
observation. The report changes even though the transfer relation is complete.

Two contracts were considered: evaluate boundary effects at the modeled call,
or exclude method-boundary rules for predefined methods. The user selected
the second contract. It is an explicit rule-semantics change. There is no
event-aware boundary adapter in the selected design.

The previous ZERO-actor proposal is superseded. Transfer completeness still
needs proof, but old cleanup method-boundary reports are not preserved.

## 3. Early stopping

### 3.1 Initial admission

Coverage is over **emitted initial keys**, including path, tail, field E and
mark selector. It is not coverage of the incoming fact's locations.

```text
actual: C.g.* / U
local carry result: I(C.g.* / U)
remaining inherited B target: C.g.$ / U
remaining AP result: I(C.g.$ / U)
```

The STAR key covers the same field location broadly, but it does not replace
the EXACT key. Their initial body facts and later restriction behavior differ.
This is an explicit EXACT demand, not automatic query completion.

A useful sufficient certificate is a conservative bound on remaining keys.
For each remaining target geometry, apply the unchanged emitter with the
possible abstract selector and the actual mark selector. It need not enumerate
all marks: a colored entry can emit only the compatible actual mark, while an
abstract entry emits shared FLOW. Account for all tails, E and ZERO adapters.
Stop when every key in that bound is already in the result set.

For example, if the only remaining target geometry is `C.g.*`, E is empty,
and the bound is exactly `{I(C.g.* / FLOW), I(C.g.* / U)}`, local carry plus
an own FLOW B can already cover both. The prefix search can then stop. An
unexamined EXACT or deeper target invalidates that certificate.

### 3.2 Summary restriction

Coverage must retain the whole original premise, layer, field/mark exclusions,
typed output geometry and protection. `TaintTree.equals` deliberately ignores
the protection mask; it is not a completion test.

For STAR/EXACT output leaves, AP restriction retains or rejects the existing
typed leaf. Retaining every raw leaf and its protection is a useful sufficient
bound for this case. Require the existing canonical payload/layer contracts.

ANY and MUST output leaves need a stronger bound:

```text
offered G: p.[any] / T
local paired Dp: p.* / T       -> keeps p.[any] / T
remaining paired Dp: p.$ / T   -> yields p.$ / T
```

These are different typed outputs. A deeper Dp can also rebase an ANY output.
Do not stop because the raw broad G was retained unless a separate replacement
proof covers these results. Both rows must still pass their complete Dc tests;
this example assumes that they do.

This stop policy is an optimization. It must not introduce another semantic
subsumption rule under the name of coverage.

## 4. A returning wrapper needs a marked internal start

### 4.1 Code and rule contract

```java
Object convert(Object x) {
    return new Object();
}

Object wrap(Object p) {
    C.f = p;
    C.g = convert(C.f);
    return C.g;
}

void main() {
    sinkU(wrap(sourceT()));
}
```

Configured effects:

```text
sourceT: assign T to its result
convert: CM(argument 0, T) -> assign U to its result
sinkU:   check U on argument 0
```

The conversion returns a fresh value. There is no argument-to-result FLOW
relation that can replace the `T -> U` effect. Use distinct full T and U.
No extra rule checks U on the return inside wrap.

### 4.2 Run-1 facts

Run-1 can retain these frozen seeds at wrap, with static-related relations
on the DEMAND layer:

```text
W: p.* / FLOW   -> C.f.* / FLOW
B: C.f.* / T    -> C.g / U
R: C.g.* / FLOW -> ret.* / FLOW
```

`C.g / U` can have the existing EXACT source-target tail; that does not
change the example. Static composition joins its location with the reader's
STAR premise by the existing overlap rule.

Why the marked read is not guaranteed: static read activation starts FLOW.
The sink in main later asks for U on its call result. A static-origin answer
resumes the saved point **in main**. It does not replay wrap's getter/return
as a U method initial. This is the current operation-local request design.
Thus, wrap need not have a direct `ret/U` demand.

That absence is not subsumption. `p/T -> ret/U` is a cross-mark relation;
a diagonal FLOW summary cannot replace it. Nor is it evidence that U is
unimportant: the outer sink explicitly requires U.

### 4.3 Current completed demand

The existing static closure yields:

```text
B ; R:       C.f/T -> ret/U
W ; B ; R:   p/T   -> ret/U

backward pairs:
    (ret/U, C.f/T)
    (ret/U, p/T)
```

For actual `ret/U`, ordinary AP emission from an authorized colored pair
starts the marked initial. Backward execution reaches conversion result/U,
follows the reversed `U -> T` rule, and can reach p/T. C5 has the required
paired permission to return that result.

### 4.4 Proposed no-color admission

Under decisions (3) and (4), the marked B cannot compose with the FLOW R.
The local return entry remains `ret/FLOW`.

```text
actual at wrap:       ret/U
local demand entry:  ret/FLOW
only initial:        I(ret/FLOW)

backward body:
    ret/FLOW
    C.g/FLOW
    convert.Result/FLOW
    concrete U reverse gate: rejects FLOW
```

Static carry preserves the actual static FLOW position; it cannot manufacture
U there. The restricted run emits no mark request. The normal-record route
has no cross-mark FLOW replacement for this conversion.

The caller cannot repair this by instantiating an already inferred wrapper
FLOW answer: no complete diagonal argument-to-result relation crosses the
fresh-value conversion. The needed `ret/U -> p/T` route has been lost inside
the wrapper before an answer is returned.

This is the gap in the inference “if U mattered, wrap would already have
ret/U demand.” The present request mechanism does not establish that invariant.

### 4.5 Why a plain getter is not a counterexample

```java
void main() {
    setStaticFromSourceT();
    sinkT(getStatic());
}
```

A shared getter FLOW answer can return its static dependency to main.
Ordinary summary application instantiates that dependency with the caller's
actual T. The preceding setter then receives T and can reach its source.
Do not reject this case solely because the getter has no marked initial.

The returning wrapper is different: its FLOW analysis must cross the concrete
gate before returning an answer to the caller. That is where the mark is needed.

The same issue can occur with an unconditional static source and read in one
wrapper: `wrap() { seedStaticT(); return C.f; }`, where the void seed operation
assigns T directly to C.f. Run-1 can retain `ZERO -> C.f/T` and the FLOW reader
without a local marked return. A backward FLOW initial cannot match the source's
concrete T reverse gate. This is the direct ZERO-producer form of the 9.13 gap.

## 5. Directional composition is not general relation composition

The proposed table is:

```text
FLOW ; mapped(T,U)        allowed
mapped(T,U) ; FLOW        rejected
mapped(T,U) ; mapped(U,V)  allowed
```

It is non-associative:

```text
(mapped(T,U) ; FLOW) ; mapped(U,V)     rejected
mapped(T,U) ; (FLOW ; mapped(U,V))     yields mapped(T,V)
```

A fixed right-to-left, consumer-driven procedure can have such a policy,
but it then needs its own direction and terminal-demand contract. Do not
reuse proofs of unrestricted associative closure or arbitrary path shortcuts.
The wrapper's `FLOW ; mapped(T,U) ; FLOW` path fails in either association.

Keep ordinary executable FLOW application unchanged. An actual T passed
through a FLOW identity must still return T. The proposed prohibition can
only be considered for demand construction, with a proved replacement for
the marked routes it omits.

## 6. Required contract before adoption

The local AP emission part of (3) is already correct: one FLOW entry alone
emits shared FLOW. The unresolved part is completeness of the demand catalog
after suppressing colored static composition.

A safe revision needs one of these proofs:

- Every necessary concrete barrier already has the correct terminal marked
  demand at each enclosing method before that method starts; show how the
  current point-local requests deliver it through the wrapper example.
- A retained executable FLOW relation replaces each omitted marked path,
  including marked source and selected-cleaner barriers and paired handoff.
- A new consumer-directed need mechanism supplies the missing marked demand
  with explicit provenance. Do not silently restore general StrongQueries.

Until that invariant is supplied, absence of a direct mark demand cannot
justify rejecting the completed colored demand. Keep (1) as the selected
complete-model boundary and (2) with precise coverage. Do not claim a no-FN
proof for (3)/(4) merely from local AP emission.

The affected existing claims are colored initial coverage, C5 pair completeness,
mark-changing/cleaner handoff, targeted FLOW-prefix traversal and static-path
closure. Their previous proofs describe the previous relation. They do not
authorize changing it without replacement proofs.

The follow-up [FLOW-replay invariant proposal](bidirectional-flow-refinement-invariant-20261028.md)
gives a sufficient query-specific condition, separates exact lookup savings
from omitted marked execution, and retains the marked wrapper in this note
as a negative control.
That proposal is not selected. The current design uses the conservative
[reader mark rule](../../spec/demand-storage-lookup.md#51-reader-mark-rule)
without a residual or internal-observation classifier.

## 7. Evidence and limits

Source checks use these runtime paths:

- `Run1PointResume`: read activation strips the supplied mark to FLOW;
  `request` and `materializeScalarImages` retain and resume the requesting point.
- `Run1Abstraction.emit`: static inputs do not become ordinary callee-entry seeds.
- `RunMethodLocalServices.sourcePredicateActionsAt`: conditional source effects
  retain their triggering origin; backward transfers use the concrete mark gate.
- `MarkGate.flowMarks`: concrete premises reject actual FLOW in restricted transfer.
- `RunMethodAnalyzer.forceRun1Layer`: static origins/results remain DEMAND.
- `Reference.emit`, `meetConclusion` and `restrict`: shared initial emission,
  EXACT/ANY behavior and paired output restriction.

Two new constructive local models accompany the review:

| Model | Audits | Scope |
|---|---:|---|
| [DirectionalCompositionCheck.lean](../../spec/lean/proposals/demand-storage-next/DirectionalCompositionCheck.lean) | 14 | Shared-FLOW wrapper failure, successful marked start, plain-getter control, carry limitation and non-associativity |
| [SpringCleanupObservationGap.lean](../../spec/lean/proposals/demand-storage-next/SpringCleanupObservationGap.lean) | 4 | Equal transfer with unequal reports, and an event-aware repair for the example |

Receipts are beside the models. All 18 audits pass without axioms. The models
are reduced executable witnesses, not a whole-JVM equivalence proof. The code
counterexamples are supported by source inspection; no JVM regression or
project campaign was run for this review. Do not present this note as a new
performance result or as an observed project-level finding loss.
