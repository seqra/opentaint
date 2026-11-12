# Equivalent demand output selectors

Status: checked campaign predicate. No production optimization is selected.
The proof package and per-edge certificates are under
`docs/reports/data/redundant-demand-20261110/q-empty-exclusion-exit-equivalence-proof-v1`.

The first case is Conductor `ParametersUtils.replaceVariables`, with the
complete context `{arg(0) == java.util.HashMap}`. X repeats at run-5/run-7.
Removal is after run-7. The original project reached run-8, completed run-7
and accepted forward run-7.

## 1. Exact scope

This candidate removes only a raw outgoing edge's contribution to next-run
demand. It keeps the raw edge, NORMAL records, source and sink observations,
source permissions, reports, seeds and current-run effects.

The candidate compares these paired DATA demand rows:

```text
R: same owner/context/block/ports, entry A, exit x.p.[any]/M, E={}
S: same owner/context/block/ports, entry A, exit x.p.*/M,     E={}
```

These are output selectors. The candidate does not replace an initial,
submitted fact, summary endpoint or C2 entry from MAY to STAR. Those positions
can distinguish the two tails. No field transfer or matching rule changes.

Use the pinned FULL runtime and configured built-in iteration policy. The
removal barrier is a completed forward run, at least run-5. Thus the next
run and all later runs use local demand; run-1/run-2 static completion is
outside this scope. A custom policy that reads exact diagnostic counts is
outside this proof.

## 2. Predicate and actual witnesses

Let U be the complete fixed repeated-edge universe. Let `project(X)` be the
complete next-run projection rows contributed by outgoing scalar edge X.
Keep every ND member in the original edge. Do not use a sampled projection.

```python
def output_key(row):
    key = copy(row)
    # This key is for DATA output queries only. Keep entry unchanged.
    if key.exit.tail == ANY and key.exit.field_exclusion == EMPTY:
        key.exit.tail = STAR
    return key

def redundant_by_equivalent_outputs(X, original_outgoing, U):
    rows = project(X)
    require(rows and all(is_nonzero_data_pair(r) for r in rows))
    require(any(r.exit.tail == ANY and r.exit.E == EMPTY for r in rows))
    witnesses = []
    for r in rows:
        Y, s = find_actual_outgoing_projection(
            original_outgoing,
            raw_origin_outside=U,
            same_complete_query_key=output_key(r),
            projection_key=output_key,
            canonical_representative=True)
        if Y is None:
            return NO_CERTIFICATE
        witnesses.append((r, Y, s))
    return CANDIDATE_CERTIFICATE(X, witnesses)
```

`canonical_representative` keeps an actual STAR exit for a converted MAY row.
All unchanged coordinates must match: project, full method key, context,
block identity, physical ports, complete entry, exit base/path/mark and field
exclusion. Hashes are indexes only; compare the complete canonical values.

Every Y is an actual selected outgoing origin after the later barrier and
is outside all of U. This candidate and every other campaign predicate can
therefore remove all their selected U edges together without removing Y.
Do not use a raw unselected summary, a NORMAL lookalike or a future provider.
Each projected row needs its own saved witness.

The general proof permits full-state predicates. This candidate uses complete
summary/projection sets and does not need a submitted-initial history premise.
The original observer did not record that history; it must not be invented.

## 3. Before and after

Before removal, the next demand store has R and S. Both authorize the same
entry A. For every current summary, both return the same paired C5 result
with the same field budget. After removal, S still supplies those answers.
The C2 entry set and owner support stay equal. Diagnostic row and callback
counts can decrease.

The selected case has these original outgoing edges:

```text
X: arg(0).[any-taint]/FLOW -> ret.content.[any]/FLOW(mx15), DEMAND
Y: arg(0).*              /FLOW -> ret.content.[any]/FLOW(mx15), DEMAND
```

X is repeated. Y is an actual run-7 edge outside U. Handoff produces:

```text
R: entry ret.content.[any]/FLOW; exit arg(0).[any]/FLOW
S: entry ret.content.[any]/FLOW; exit arg(0).*     /FLOW
```

Handoff clears FLOW mark exclusions and maps MUST to MAY, as it already does.
The candidate changes neither rule. It compares the resulting queries.

The original code is a delegation wrapper:

```java
// Same original context in both runs: arg(0) == java.util.HashMap.
private Object replaceVariables(
        String paramString, DocumentContext documentContext, String taskId) {
    return replaceVariables(paramString, documentContext, taskId, 0);
}
// Run-5 and run-7 contain X above. Run-7 also contains Y above.
```

`mx15` denotes the original fifteen full-mark exclusions, listed in the exact
case witness. The following is an operator example, not a claim about an
uncaptured project input stream:

```text
Submitted: ret.content.[any]/T, DEMAND
C2 entry under either row: ret.content.[any]/FLOW
Emitted identity: ret.content.*/FLOW -> ret.content.*/FLOW, NORMAL

Provided C5 candidate, actually observed in original run-6:
    ret.content.*/FLOW -> arg(0).[any]/FLOW(mx15), DEMAND
Paired C5 result under either R or S:
    ret.content.*/FLOW -> arg(0).[any]/FLOW(mx15), DEMAND
Field budget under either row: 1
```

The code's unusual context does not make it dead. The current resolver can
derive that context through aliases. This predicate needs no type-name
unreachability assumption and no claim about the four-argument callee's body.

## 4. Scalar output law

For empty exit field exclusion, native `restrictConclusionOnly` returns the
same result under `x.p.[any]/M` and `x.p.*/M` for every legal current conclusion:

| Current conclusion | Result under both selectors |
| --- | --- |
| Same path, EXACT or STAR | Keep it. |
| Same path, MAY | Keep MAY. |
| Same path, MUST with E | Keep MUST with E. Union with empty E has no effect. |
| Strictly below x.p | Admit the suffix and keep the conclusion. |
| Above x.p, MAY | Select x.p with MAY and empty E. |
| Above x.p, MUST | Select x.p with MUST and empty E. |
| Above x.p, STAR | Keep the correlated conclusion if its own E admits the suffix. |
| Above x.p, EXACT, or disjoint | Emit nothing. |

Base and mark tests are equal. Keep current field and mark exclusions, layer,
protection and the complete caller original. A STAR conclusion stays STAR;
the exit selector does not split its correlation.

The row's relative field budget is `min(runLimit, FL(exit.path) + 1)`.
Both paths are equal. Selection precedes this same cut on both sides.

## 5. Demand services and future behavior

C2 uses entries only. R and S have equal entries, so every submitted fact
gets the same complete initial-emission family, including FLOW companions,
layers and field paths. Caller admission and subscription decisions stay equal.

Paired C5 checks the same entry and physical exit port. The scalar law and
equal budgets give the same result for every singleton or full ND original.
Prepared output programs must satisfy this law too; their indexes use the
same base/path. A budget overflow must fall back to complete native C5.

Loop restriction uses the same C2 and C5 observations, saved summaries and
Targets. Current cursor witnesses must not enable an unproved shortcut:
the pinned runtime's `certifiedFirstBudget` returns null. Representation
order and diagnostic work can differ; complete semantic answers cannot.

ZERO and Target rows are separate. These nonzero DATA rows cannot admit a
Reach result. The proof keeps all control rows and seeds.

Each removed row has an independently retained row at the same owner and
scope. Method-key support and empty-demand stopping stay equal. The configured
field-limit schedule and run cutoff stay unchanged.

After the one-time removal, the next run has extensionally equal demand
services for all inputs, with equal records and seeds. Its complete semantic
fixed point, source permissions, NORMAL persistence, Targets and report
identities must therefore remain equal. Handoff is rebuilt from those current
stores. The following run starts from equal semantic state again. This is
the required future argument; equal historical counts alone do not supply it.

## 6. Proof and validation gate

The constructive model is
`spec/lean/proposals/redundant-demand-20261110/EquivalentOutputSelectors.lean`.
It proves the scalar restriction law, complete paired store equality,
entry emission equality, physical scope preservation, retained-anchor union,
owner support and future-state preservation. No existence or future-safety
checkbox can replace an executable witness.

Native tests must cover every tail, ancestor/equal/descendant/disjoint paths,
full marks and FLOW exclusions, current field exclusions, both protection
classes, singleton/ND originals, scoped ports, prepared loop plans and cuts.
Include two negative controls: nonempty concrete STAR exit exclusion, and
changing a C2 entry from MAY to STAR. Neither is this optimization.

The independent source audit checks 21 pinned files. Six native tests pass,
including freshly executed method and block matrices and complete loop
observations. Twenty generic Lean audits and seven observed-package audits
pass with only `propext` and `Quot.sound`. All 153 certificates and 116
outside-U anchors pass independent native projection and encoding checks.
All 269 explicitly encoded emissions are complete; unrelated emissions stay
arbitrary, rather than being set to empty.

Joint removal with the prior 181 accepted filters preserves the complete
canonical query set, owner/port support and control rows. It removes 116
distinct duplicate selector rows from Conductor's explicit frontier. This
is an offline set check, not a new engine run or a measured speedup.
No runtime or performance change is claimed by this document.
