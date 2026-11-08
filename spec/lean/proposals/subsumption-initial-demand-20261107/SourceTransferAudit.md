# Negative source guard and the FLOW seed-layer change

Read-only source result, 2026-11-07. No native or proof job was run. The new
FLOW/STAR identity starts NORMAL whereas the old FLOW/ANY identity starts
DEMAND. That is an explicit selected change. The proposed example below does
**not** establish a new false NORMAL result under the baseline rule semantics.

## The negative-only source is already a ZERO source

```text
Rule text: if !CM(p,T), assign U(ret)
Source form: ZERO/$/ZERO -> ret/EXACT/U
```

At baseline 528 and in the current tree, JVM source/sink compilation first
folds signed Boolean expressions, then approximates surviving negative mark
literals by TRUE. A lone `!CM(p,T)` therefore becomes TRUE, not a runtime
absence check on p. `JIRRuleForms.source` emits the existing ZERO source edge
for a TRUE predicate. It does not attach an abstract p premise to that source.

Exact source anchors:

- `JIRRuleForms.kt:150–169`: `projectNegatives=true` is the default; source/sink
  normalization passes `negativeLiteralsAreTrue=projectNegatives`.
- `SignedConditionNormalizer.kt:37–54`: surviving negative leaves become TRUE.
- `JIRRuleForms.kt:355–359`: `fullPredicate` also performs that normalization
  before predicate compilation. The signed-only entry-eligibility calls are
  not an alternate signed runtime source evaluator.
- `JIRRuleForms.kt:466–484`: a TRUE source emits
  `PathEdge(ZERO_FACT, markTarget(...), EmptyE)` through `sourceEdge`.
  The ordinary `Assign U(ret)` target is EXACT; an explicit any-accessor
  source target would instead use ANY_TAINT (`sourceFact`, line 109).
- `JIRRulePredicates.kt:44–46`: a dynamic source/sink leaf must be positive;
  a remaining negated literal is rejected by an assertion.

These five implementation files, including `SourceRuleOccurrence.kt` and
`MarkGate.kt` as recorded in `source-pins.json`, are byte-identical to 528.
The approximation is a baseline rule-language property, not a new C2 rule.
Signed contradictions are folded before projection; this does not claim that
every formula containing a negative literal becomes TRUE.

## An ordinary concrete source action cannot generate U from FLOW

Suppose a mixed condition leaves a genuine positive requirement after the
negative approximation, for example `CM(p,V) && !CM(q,T)`. The compiled unary
source operation has a selected concrete premise and target:

```text
edge:  p/$/V -> ret/EXACT/U
P:     p/STAR/FLOW
input: p/STAR/FLOW, NORMAL, mx=X
```

`SourceRuleOccurrence.transfer` builds the ordinary leaf-to-action edge.
`RunMethodLocalServices.transfer` calls `applyEdge` with the original complete
premise and returns `sink(premise,result,actionId)`. It does not replace this
dependency with ZERO. Multi-leaf source evaluation instead checks concrete
mark evidence and keeps the complete combined premise.

The native FLOW lane cannot produce a concrete result from that input:

```text
MarkGate.flowMarks(X) = null              // premise is Concrete(V)
MarkGate.flowRequest(X) =
    V, if FULL and V is not excluded; otherwise null
EdgeApplication.flowHit:
    if run1, request V when eligible;
    otherwise emit nothing.
```

This is independent of whether the FLOW packet's layer is N or D. In a later
restricted run, changing the identity layer to N does not convert the failed
mark gate into a concrete U. In run 1, the native path may request V, but it
does not synthesize V or U from the FLOW packet. The run-1 abstract-base STAR
route already exists under the baseline; later mark-materialization and
conditional-source results still use their own actual concrete evidence.

Native anchors are `MarkGate.kt:19–26`, `EdgeApplication.kt:74,129–134`,
`SourceRuleOccurrence.kt:35–39`, and
`RunMethodLocalServices.kt:169–180,193–200,217–232`. A FLOW input to a
multi-leaf mark check likewise yields only a run-1 request or no answer,
never `MarkCheck.Holds` (`MarkCheck.kt:21–25`).

## Concrete layer and exclusion trace

For the negative-only rule, whenever the existing ZERO control reaches the
operation, the baseline can already derive the following, subject to the
unchanged source permission and ordinary limit rules:

```text
R1, forward:
  P=ZERO, input=Reach/N
  ZERO-source edge -> ret.EXACT/U,N
  an ordinary U sink can yield NormalTarget under P=ZERO.

B2:
  any backward source-hit/permission path uses the same ZERO-source operation;
  it does not need an ANY/FLOW initial at p.

F3:
  replaying an authorized ZERO source has the same original P=ZERO.
  New p.STAR/FLOW,N versus old p.ANY/FLOW,D adds no U through this source.
```

This is a source-derived conditional trace, not a measured R1–B2–F3 run and
not a proof that every source operation is reachable in R1. If the operation
is not reached by ZERO, a p/FLOW input still cannot apply its ZERO-based
source edge: the native base check rejects it (`ApOps.kt:54–58`). Thus the
missing reachability cannot be supplied merely by the FLOW layer change.

FLOW mark exclusions are not evidence for a negative mark guard. They must
not be discarded to enable a positive source action. For an actual FLOW X,
the abstract-to-abstract lane retains X and unions the edge's exclusions
(`MarkGate.flowMarks`). A selected concrete premise instead takes the
request/no-output lane; in FULL mode V excluded by X cannot even be requested.
A distinct authorized ZERO source may assign U, including when some unrelated
FLOW packet excludes U. That is new source data under ZERO, not restoration
of an excluded mark in the FLOW packet or a FLOW-backed concrete relation.

## Safe conclusion and remaining obligation

The exact negative-guard GEN example is not a new NORMAL-U counterexample to
the selected C2 layer change. It relies on a runtime negative-CM evaluator
which the pinned source/sink forms do not expose. For a legal remaining
positive source guard, a later FLOW packet cannot itself satisfy the guard
or generate a concrete result. This source audit does not prove the whole
combined redesign, ordinary FLOW summary NORMALity, all conditional joins,
or global report equivalence. Those obligations remain separate; no new
grounding store, field transfer, source permission or default provider is
proposed here.
