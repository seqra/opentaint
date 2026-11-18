# Unadmitted NORMAL return blocks completion

Historical counterexample to whole-return completion. The
[mark-scoped terminal-service repair](bidirectional-mark-scoped-point-service-20261116.md)
now stops this unchanged reference naturally at run-5 (run-7 with delayed
receipts). The run-9/run-10 recurrence below remains the checked before-change
result. Production is unchanged; its finite diagnostic still reaches run-31.

16 November 2026. Synthetic data-flow reachability. FULL mode.
Latest finite reference and unchanged native diagnostic: **run-31**.
The proof below has **no iteration limit**. Production is unchanged.
Follow [proof-guide.md](../../spec/proof-guide.md).

This is a counterexample to the
[current consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md),
including the complete NORMAL exact-point return service. Its complete
states repeat **run-9/run-10 forever**, with **70/82 qualified demand rows**,
ten saved NORMAL records and one genuinely completed exact-query key.
All selected global/Dc+1 entry caps and paired Dp+1 output caps remain.
No new field-limit exception is used.

The previous exact-input example stopped after its exact T query obtained
a complete NORMAL return service. Two additional ordinary unary marking
rules prevent this certificate: that query now has a NORMAL V return which
C5 correctly discards. Its remaining h/U service is incomplete. The new
pruning rule therefore cannot omit the coarse root-MAY/U reply. The old
bidirectional demand cycle remains.

## 1. Fully analyzed code and rules

```java
class Box { Box f; Box g; Box h; Box k; Box s; }

// Entry marking rule: assign T only at a.f.g.$.
void root(Box a) {
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observation rule: CM(z.M,U).
}

Box make(Box p) {
    Box r = new Box();
    // Rules at this ordinary program point:
    // 1. CM(p.f.g.g.M,T) => assign U to r.MUST.
    // 2. CM(p.M,T)       => assign U to r.h.MUST.
    // 3. CM(p.f.g.g.M,U) => assign T to r.MUST.
    // 4. CM(p.M,U)       => assign T to r.h.MUST.
    // 5. CM(p.M,T)       => assign V to r.k.MUST.
    // 6. CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
```

`$` is EXACT; `*` is correlated STAR; M is MAY; NE is non-empty MAY;
MUST is uniform taint. N/D are NORMAL/DEMAND. All literal H memberships
and field/mark exclusions are empty/plain in this example.

The call graph has root -> make only. Three sequential calls are not
recursion. The code has no loop, cleaner, pass rule, field overwrite,
unresolved method, library model or predefined summary. Allocation and
return are analyzed; the configured operations are ordinary positive unary
marking/observation rules. There is no conjunctive-rule approximation.

Every mark is both assigned and checked by an executable rule:

```text
Assigned = {T,U,V}
CM-used  = {T,U,V}
Assigned intersect CM-used = {T,U,V}
```

Rule 6 runs in the same reachable method. It cannot be discarded by
mark-set specialization. Its s region is disjoint from the k region
assigned by rule 5. No actual V value enters that s check. Recognizing
this geometric fact does not change the selected provider reduction.

## 2. The exact query and the lost service

At run-3 and later, the first call supplies p.f.g.$/T,N. The frozen
qualified demand already permits the exact query within both input caps:

```text
broad demand:     [p.M/T    | ret.*/U] -> p.f.*/T,D + FLOW companions
qualified demand:[p.f.NE/T | ret.*/U] -> p.f.g.$/T,N
FL(p.f.g)=2 <= globalLimit and FL(p.f)+1
```

Its complete raw return effects are:

```text
p.f.g.$/T -> ret.h.MUST/U,N
p.f.g.$/T -> ret.k.MUST/V,N
```

The deep f.g.g guard rejects: an exact mark at f.g is not a mark below g.
The two broad conditions in rules 2 and 5 are satisfied. Both outputs have
one concrete return field, so the V result is not a truncation artifact.

After run-2, relevant paired output selectors have T or U, not V. C5
admits the h/U result and rejects the k/V result due to its full mark:

```text
ret.k.MUST/V intersect ret.*/U = empty
ret.k.MUST/V intersect ret.h.$/U = empty
```

The V-side demand introduced during bootstrap asks for s, where rule 6
would consume V. It cannot accept k:

```text
ret.k.MUST/V intersect ret.s.M/V = empty     (k != s)
```

No uncut V summary is retained in an auxiliary archive; the selected
policy stores admitted summaries only. All NORMAL summaries are restricted
as required. The V result is absent from both the steady current store
and saved NORMAL basis.

The completion checker must cover **every** raw return of the exact query.
Therefore:

```text
CompleteReturnService(p.f.g.$/T) = false
```

It is insufficient to observe the ready NORMAL h/U child. The complete
service rule explicitly forbids such a partial certificate. This failure
persists at every later global field limit, because C5's mark rejection
does not depend on that limit.

A different query, **p.h.$/U**, does complete. It has only a NORMAL h/T
return. This key is present in the cache from run-3 onward. The completion
mechanism, native application receipt and pruning guard remain enabled.
This counterexample does not replace the latest policy with its predecessor.

## 3. The surviving cycle

The coarse p.f.*/T,D query still has the unknown suffix that can reach the
deep guard. It produces a root-MAY return:

```text
p.f.*/T -> ret.M/U,D
```

Its native application to p.f.g.$/T,N is permitted. The complete-point
pruning guard fails because that exact T query is not complete. The NORMAL
h/U output cannot whole-region cover root MAY. Both actual replies remain.

The root-MAY path passes through the three ordinary calls, alternating
T/U. The complete packets also carry the independent NORMAL h path. The
observation emits both its retained NormalTarget(id) and an anonymous
DemandTarget. The latter still requires another iteration.

Two representative repeated members are:

```text
forward current summary:  p.f.*/T -> ret.M/U,D
backward current summary: ret.*/U -> p.M/T,D
```

The shared make owner serves all three actual submissions. Other qualified
rows preserve the origins needed by these two members; these rows are
included in the full trace and state proof. The two displayed rows alone
are not claimed to be a self-contained two-edge evaluator.

Backward application renews the broad p.M/T input need and the root's
entry-marking permission. Next forward analysis again projects the exact
source point to the existing p.f.STAR/T query. Its separate exact query
again loses the V return at C5 and cannot complete. No observed state
changes once the run-9/run-10 pair is reached.

## 4. Cold prefix and all subsequent iterations

| Run | Direction | Field limit | Qualified demand rows | Saved NORMAL records | Completed exact keys | Root control / observation |
|---|---|---:|---:|---:|---:|---|
| run-1 | forward | 1 | 6 | 0 | 0 | DemandTarget |
| run-2 | backward | 1 | 16 | 0 | 0 | source permission |
| run-3 | forward | 2 | 26 | 6 | 1 | DemandTarget + NORMAL observation |
| run-4 | backward | 3 | 42 | 6 | 1 | source permission |
| run-5 | forward | 4 | 44 | 10 | 1 | DemandTarget + retained NORMAL observation |
| run-6 | backward | 5 | 69 | 10 | 1 | source permission |
| run-7 | forward | 6 | 68 | 10 | 1 | DemandTarget + retained NORMAL observation |
| run-8 | backward | 7 | 82 | 10 | 1 | source permission |
| run-9 | forward | 8 | 70 | 10 | 1 | DemandTarget + retained NORMAL observation |
| run-10 | backward | 9 | 82 | 10 | 1 | source permission |
| run-(9+2n) | forward | 8+2n | 70 | 10 | 1 | exact run-9 state |
| run-(10+2n) | backward | 9+2n | 82 | 10 | 1 | exact run-10 state |

[Complete per-block fact trace](bidirectional-unadmitted-return-trace-20261116.md)
contains every demand row, submitted fact, emitted initial, admitted
NORMAL/DEMAND summary and completion key through run-10. Forward inputs
are above each method body and outputs below it; backward placement is
reversed. The rejected raw V effect is also identified.

## 5. Constructive non-termination proof

[Lean package](../../spec/lean/proposals/unadmitted-return-cycle-20261116/README.md).
No custom axioms, holes, classical choice, native evaluation oracle or
iteration cutoff is used.

1. Execute the cold prefix from the ordinary entry marking, including V
   offers and the V query in run-1. No cycle state is assumed as a seed.
2. Prove every complete cold state and its within-run fixed point through
   run-10. Eight reference rounds are sufficient because the next round
   equals the last state; they are not a timeout or stopping budget.
3. For arbitrary n >= 0, prove each delivery/publication stage at field
   limit n+8. These equalities include completion and delivery receipts.
4. Prove run-index invariance for all regular forward/backward runs,
   including the new run>=3 completion and pruning guards.
5. Inductively construct the complete repeated states:

```text
forall n >= 0:
    State(9+2n)  = State(9)
    State(10+2n) = State(10)
```

6. Exhibit the same nonempty demand members in each forward/backward state,
   prove a live root DemandTarget and renewed source permission, and prove
   that no earlier forward run stopped. Natural uncapped termination is
   impossible under this reference contract.
7. Check Empty E throughout, the original global/Dc+1 entry bounds for
   actual offers and complete prepared families, and unchanged paired
   Dp+1 output restriction. The NORMAL-MUST/real-E exception is ineligible.
   No Target is retracted when the NORMAL observation arrives.

The model changes the **analyzed program only**: two new unary marking
rules and their ordinary V query at bootstrap. Admission, complete-point
checking, native matching, suppression, output restriction, storage,
normalization, packet coverage and the iteration controller keep their
selected definitions. The checker compares these bodies with the previous
proposal to guard against silently disabling a fix.

Validation: **171 new constructive claims; 5,475 cumulative audited claims
in 275 source-hash-checked modules**. The only permitted axiom dependencies
are `propext` and `Quot.sound`.

## 6. Native controls and scope

**Nine native tests pass:** three new program/component controls and six
existing complete-service controls. The new checks cover:

- the six-rule, three-call program's unchanged native run-31 diagnostic;
- actual NORMAL V output discarded by paired C5, with the precise initial
  admitted and no field cut involved;
- the disjoint k/s V check and the original exact/coarse guard distinction.

The uncapped proof runs the selected scalar proposal, not production.
The native engine has not integrated the entire NE/completion proposal;
its diagnostic still reaches **run-31/POLICY**, with zero NORMAL reports.
The reference has a NORMAL observation from run-3. The inherited scalar/native
report-count alignment gap remains explicit. No complete JVM/front-end,
alias-expansion or whole-engine equivalence theorem is claimed.

The formal counterexample uses the same fully specified synthetic core
scope as the earlier example. It does not depend on a missing adapter for
an unsupported rule operation: all six conditions are positive and unary,
and the leaf body has ordinary allocation/return. No repair is selected
in this report. In particular, it does not propose keeping unrestricted
NORMAL records, enlarging field caps or canceling Targets.

## 7. Reproduction

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/unadmitted-return-cycle-20261116/check.py \
  --out /tmp/unadmitted-return-proofs

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.UnadmittedReturnCycleTest \
  --tests org.opentaint.dataflow.bidi.CompletePointServiceNativeTest --console=plain
```

For faster proof rebuilds, pass `--dependencies` with the checked
complete-point-service proof output. Source hashes are verified before reuse.
Compiled artifacts and full captures are outside the repository under
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/unadmitted-return-cycle-20261116/`.
The code, full readable trace and proof sources remain in the repository.
