# Definite reply support closes both concrete replay cycles

16 November 2026. Synthetic data-flow reachability. FULL mode.
Follow [proof-guide.md](../../spec/proof-guide.md).
[Complete consolidated contract](../design/bidirectional-demand-termination-approach-20261115.md#definite-full-reply-support).
Production is unchanged.

**Revised cold references: both naturally stop at run-7.** The earlier 18
complete references retain their stopping positions, latest **run-15**.
Unchanged native counterexample captures still reach **run-31**, policy
ceiling. No iteration ceiling is used in either new stopping proof.

## 1. One support law

```text
same complete actual reply key K:
    (K,N), (K,D) -> retain (K,N)

K includes owner/direction/scope/ports/resume route, complete caller original,
base/path/tail, full concrete mark, real E and literal H.

Eligible definite values: EXACT with Empty E; MUST with its real E.
```

The previous rule covered exact points only. This revision also covers an
identical uniform MUST region. This is a **semantic extension of DATA
subsumption**. It can remove uniform demand guidance and change timing.
Every NORMAL member and geometric value remains; nothing is promoted.

NORMAL MUST proves the mark at every represented location except its real
field exclusions. Its identical DEMAND copy cannot supply a new location,
full mark, geometric initial or complete binding. The NORMAL value is an
explicit retained witness for the whole region, without enumerating suffixes.

The provider is the **composed result**, with actual support already known.
Do not compare raw callee hypotheses or summary records. A D input remains
D under a NORMAL record. Keep the existing record basis, C2/C5, cuts,
normalization, Source/Target permissions, rule conditions and protected
memberships. No Target cancellation or new initial kind is introduced.

## 2. Before and after on the new case

```java
Box make(Box p) {
    Box r = new Box();
    // Producer: CM(p.M,T) => assign U at r.MUST.
    return r;
}
void root() {
    Box a = new Box(); a.f = new Box(); // Producer: a.f.MUST/T,N
    Box b = new Box();                 // Producer: b.MUST/T,N
    Box x = make(b);
    Box y = make(a);
    // Observe CM(x.M,U) and CM(y.M,U).
}
```

For the field input, broad saved input guard p.MUST is only provisionally
matched, while p.f.MUST is definitely matched. The raw saved reply batch has
four scalar members under the latest empty/nonempty C2 policy:

```text
ret.$/U,D       ret.MUST/U,D       ret.$/U,N       ret.MUST/U,N

exact-only:    ret.$/U,N; ret.MUST/U,N; ret.MUST/U,D
new rule:     ret.$/U,N; ret.MUST/U,N
```

The new rule compares identical tails; the exact and uniform members are
not merged. All four scalar NORMAL summary members remain persisted:
root-MUST and field-MUST input guards, each with exact and uniform outputs.

| Run | Cold behavior under the new rule |
|---|---|
| run-1 F/1 | Conditional uniform U result is D; publish root D Target |
| run-2 B/1 | EXACT/STAR U initials produce MAY/T requirements; both T producers permitted |
| run-3 F/2 | Infer broad NORMAL exact/uniform U members; field query stays D; first NORMAL report |
| run-4 B/3 | Paired C5 refines T requirement to p.f.MAY; both producers still permitted |
| run-5 F/4 | Infer field NORMAL exact/uniform U members; a previously delivered provisional reply can still emit D Target |
| run-6 B/5 | No helper body; saved reads renew only the a.f/T permission |
| run-7 F/6 | Complete saved batch drops both D copies; no new DATA/Target demand; ordinary driver stop |

Run-7 annotations use the existing variables and boundaries:

```java
// Current demand: empty. Marked submitted input: p.f.MUST/T,N from a.
// Emitted initials: none. No current subscription or body actor.
// Ready saved batch after folding: ret.$/U,N and ret.MUST/U,N.
Box make(Box p) {
    Box r = new Box();
    // CM(p.M,T) => assign U at r.MUST.
    return r;
}
// Fresh summaries: none. All saved NORMAL members remain.

// Demand: [Target | ZERO]. Submitted: ZERO,N. Initial: ZERO->ZERO,N.
void root() {
    Box a = new Box(); a.f = new Box(); // a.f.MUST/T,N
    Box b = new Box();                 // no new T permission needed
    Box x = make(b);                   // NT(0) retained
    Box y = make(a);                   // y.$/U,N and y.MUST/U,N only
    // CM(x.M,U); CM(y.M,U).
}
// No outgoing DEMAND DATA or Target. Retain NT(0), NT(1).
```

The earlier exact-output case also stops at run-7, with its complete cold
prefix and both NORMAL records retained. The new proof computes both
prefixes through run-6 rather than assuming ready providers at the start.
After the empty run-7 frontier, hypothetical run-8 is idle; induction proves
that arbitrarily many forced later steps cannot revive demand.

No retraction is needed for an early D Target or callback. Different ready
batch schedules can stop sooner. Once both providers are in the finite
saved snapshot, enumeration order cannot change the supported result.

## 3. Soundness guards and consequences

| Case | Behavior |
|---|---|
| Same concrete exact or uniform value, same full context/H/E, N and D | Keep N |
| Uniform E is nonempty but identical | Keep that same E on N |
| Different E, mark, path, tail, H, original or continuation | Keep both |
| Only provisional D reply | Keep D |
| Actually D input with only NORMAL records | Composed results remain D; no N provider exists |
| NORMAL exact root plus DEMAND uniform root | Keep both; the point does not prove descendants |
| MAY/NE/STAR/FLOW | Outside this support rule |
| ND | All arms remain required; compare the complete composed original |
| Layer-sensitive alias routes differ | Preserve their existing effects/routes before folding at a common continuation |

The generic Lean kernel proves an explicit retained NORMAL witness for each
deletion, normal-member and complete-key preservation, idempotence, merging,
arrival-order membership and output-subset laws. The definite instance
preserves each represented location, real E and H. Same-head C2 creates the
same field shapes for identical inputs in either layer. Generic support-
monotone transfers and complete AND bindings can use the stronger witness.
Subsequent genuine loss still yields D by the existing support/loss join.

These continuation claims do not justify skipping an unexecuted alias route
selected only for D. Resolve the existing guard, keep routes separate, or
fold after their native effects. The new cases have equal nonidentity return
routes. Existing controls, static-pool notifications and Source/Target
channels remain independent.

The filter uses the existing complete ready reply batch. It adds one
temporary NORMAL-key set and one filter pass, O(n) expected key lookups
for n scalar members, or O(n*L) including path hashing with interned context
keys. Output membership is a subset. There is no new field, mark, input
history, subscription, child query, discarded-suffix evidence or origin
product. No bound on whole-program iterations follows from this local law.

## 4. Old references and native checks

The new filter is inert on every recorded reply packet at every cold
iteration in all 18 previous complete references. The new theorems compare
full AP/layer memberships, not just final finding counts. Protected closure
packets are also unchanged. Existing complete stopping proofs therefore
continue to apply in that model scope.

| Previous reference | Natural stop |
|---|---|
| Nested; Prefix; RoundTrip; Overwrite | run-9 |
| PrefixPostfix; Growth | run-11 |
| Postfix | run-13 |
| Double | run-15 |
| OldMethod; OldBB; LongReader | run-5 |
| OrdinaryTwo | run-3 |
| NestedNegative; NestedPositive; NestedExact | run-3 |
| NestedSurvivor; NestedDeep | run-5 |
| NestedLarger | run-11 |
| Protected uniform closure | run-3 |
| Selected standalone MUST-preserving cleaner | run-1 |
| Earlier exact-output concrete replay | run-7 |
| New uniform-output concrete replay | run-7 |

**90 new constructive claims pass.** With source-hash-checked dependencies,
the receipt covers **2,300 declarations in 115 modules**. No proof hole,
custom axiom, classical choice or external decision oracle is accepted.

**52 native tests pass**, including eight new adapter checks: exact and
uniform replay, both orders, actual D input, lone D, real exclusions,
protected versus plain support and complete original/continuation keys.
The unchanged counterexample driver still reaches **run-31**; component
adapters test the proposed filter on its real native outputs. The native
core has not installed the full NE/support proposal, so an integrated
native run-7 completion is not claimed.

```bash
python3 spec/lean/proposals/definite-reply-support-20261116/check.py \
  --out /tmp/definite-reply-proofs
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.DefiniteReplySupportNativeTest \
  --tests org.opentaint.dataflow.bidi.ProvisionalUniformReplayCycleTest \
  --tests org.opentaint.dataflow.bidi.ProvisionalMustReplayCycleTest
```

[Proof dossier](../../spec/lean/proposals/definite-reply-support-20261116/README.md).
No production implementation or project scan is changed. The whole analyzer's
universal termination and JVM-front-end equivalence are not proved. Native
integration must preserve complete keys, resolved continuation routes,
pending demotion and surviving effects. Bulk JSON, logs and compiled proofs
remain outside the repository under
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/definite-reply-support-20261116/`.
