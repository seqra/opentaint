# NORMAL uniform actual DATA covers redundant demand

16 November 2026. Synthetic data-flow reachability. FULL marks. Proposal
and checked reference models; production is unchanged.

**Result:** the alternating conditional-generator example naturally stops
at **run-5**, with its NORMAL observation retained. All 18 earlier ordinary
references, the three concrete replay references, the protected closure and
the selected cleaner reference still finish with their expected observations.
The largest completed reference is **run-15**. The unchanged native diagnostic
still completes **run-31** at its finite policy limit.

## 1. Selected change

Compare DATA **after native application**, at one forward continuation:

```text
N: NORMAL  a.u.MUST/T {E}
D: DEMAND  a.v.K/T

same complete owner, caller original premise, instruction/stage, ports and H
K ∈ {EXACT, MUST, MAY, NE}; concrete FULL mark T
wholeRegion(D) ⊆ uniformRegion(N)

=> keep N; omit D from further delivery at this continuation
```

The NORMAL value must already exist. It can be in the current complete
reply packet or the NORMAL column of the existing post-statement/stage
store. Do not construct a new MUST value, promote D to N, or use a future
publication as evidence. Every stored NORMAL provider remains retained. In particular, keep a NORMAL
EXACT alongside a NORMAL MUST when their admission services differ; the new
law removes covered DEMAND memberships only.

This is a **new cross-layer, cross-tail DATA coverage law**. Previously,
EXACT/MUST support required identical full value keys. The new law can also
remove MAY/NE, and can cover a concrete point or smaller uniform region.

Keep concrete STAR outside this new law. Keep FLOW outside it. Keep GROUP
mode and backward delivery unchanged. Their existing rules still apply.
NormalTarget, DemandTarget, source permission, C2, paired C5, field limits,
NE cuts, cleaners, rules, alias effects and NORMAL persistence stay unchanged.

Fewer offered DATA facts can produce fewer C2 starts. This is an intended
consequence; this proposal does **not** claim identical raw C2 families.
It preserves the required refined observations of the supplied cases. It
adds no initial or probe and changes no C2 cell.

## 2. Why application must precede coverage

The two callee relations have different premises:

```text
p.f.*/T    -> ret.MAY/U, D
p.f.MUST/T -> ret.MUST/U,N
```

Neither globally removes the other. Apply them to the same actual
`p.f.MUST/T,N`. The caller now has:

```text
ZERO -> x.MAY/U, D
ZERO -> x.MUST/U,N
```

The second value establishes U at every position represented by the first.
The caller can omit the MAY value before the next dependent stage.

A raw NORMAL record is insufficient. For example,
`p.MUST/T -> ret.MUST/U,N` does not supply a NORMAL result to actual
`p.f.MUST/T,N`. The retained definite native MUST read rejects that guard.
With no applied NORMAL provider, keep the MAY demand.

Compare complete caller originals and physical continuations. A result for
`root`'s call at `x` cannot discharge a question at its different call at `y`.
Do not compare distinct hypothetical callee initial keys before binding.
Within an existing owner point, use its full original premise column, as for
ordinary fact deduplication. Do not add a new per-input history cache.

## 3. Whole-region test

First check the full mark, base, original/context and literal H. Preserve
plain and protected memberships independently; an H=0 provider never covers
H=1 and conversely. H=1 to H=1 coverage retains a protected NORMAL carrier.

Let `u` be the NORMAL MUST head and `v` the candidate head:

| Geometry | Coverage condition |
|---|---|
| Incomparable heads, or N below D | Reject. |
| `u=v`, D is EXACT | Accept; field exclusions do not remove the root point. |
| `u=v`, D is MUST with E2 | Require `E ⊆ E2`. |
| `u=v`, D is MAY/NE | Require `E` empty; these candidates have empty E. |
| `v=u.f.rest` | Require `f ∉ E`; the old E stays scoped at u. |

Examples:

```text
N x.MUST/T          covers D x.MAY/T
N x.MUST/T          covers D x.f.MUST/T
N x.MUST/T {f}      covers D x.$/T
N x.MUST/T {f}      covers D x.g.MAY/T      when g != f
N x.MUST/T {f} does NOT cover D x.MAY/T or D x.f.MAY/T
N x.f.MUST/T   does NOT cover D x.MAY/T
```

No JVM type, finite field alphabet, rule identity or iteration history is
used. Use each real exclusion at its original head. Do not turn E into a
promotion ban or add an artificial exclusion to a demand.

Use only legal post-application DATA. Perform ordinary matching, actual
layer joins, binding, aliases, field cuts and block-boundary checks first.
An uncut NORMAL record whose applied result becomes NE/DEMAND is not a
NORMAL provider at that continuation.

## 4. Delivery and ownership

```text
onForwardDataResult(S, callerP, stage, delta):
    delta = existingNativeResultProcessing(delta)
        // Includes actual matching, binding/aliases, limits and block checks.
    delta = existingPacketCanonicalization(delta)
    normal = existingNORMALData(S, callerP, stage) + NORMAL leaves in delta

    for d in delta:
        if d is concrete FULL DEMAND and d.tail in {EXACT,MUST,MAY,NE}
           and some retained n in normal is MUST with the same mark/H
           and n covers the WHOLE region of d:
            omit d
        else:
            use the existing fresh-result storage and delivery

    // Keep result storage at S, as now, not at its successors.
    // An added NORMAL can also retire covered pending DATA work at this point.
    // Already executed effects are not undone.
```

For calls and blocks, the candidates are their actual bound replies. Use the
existing owned stage/continuation and store. For ordinary owned DATA, the
same comparison is a fact-store coverage check. It is not a rule for
`MethodEdgeStore` to validate hypothetical guard bindings. No grounding
support, new summary premise, new tail or raw candidate archive is required.

A late NORMAL does not cancel a DemandTarget that already ran. On later
forward runs, saved NORMAL replay still runs first. An already owned NORMAL
provider then blocks a later duplicate coarse DATA delivery. A whole-run
barrier or an unbounded pending packet is not required.

Keep a candidate if its provider is not ready, does not match the actual,
is cut to demand, has a hole, differs in original/ports/H, or covers only
part of its region. The new law never retires Target rows directly and
never stops analysis based on a confirmed report.

## 5. New example: the changed trace

Use the code and rules from the
[alternating counterexample](bidirectional-alternating-conditional-nontermination-20261116.md):

```java
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.MAY,T) => assign U to r.MUST.
    // CM(p.MAY,T)     => assign U to r.f.MUST.
    // CM(p.f.g.MAY,U) => assign T to r.MUST.
    // CM(p.MAY,U)     => assign T to r.f.MUST.
    return r;
}
void root(Box a) { // Entry producer: a.f.MUST/T,N.
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observe CM(z.MAY,U).
}
```

Run-1 and run-2 retain the previous behavior. They produce coarse root-MAY
questions and finer `p.f.NE/m` questions. No NORMAL provider is assumed in
those runs. The new rule cannot remove their coarse demand prematurely.

Run-3, forward, limit 2:

```java
// root demand: [Target | ZERO]. Submitted/initial: ZERO.
void root(Box a) {
    // Actual producer: a.f.MUST/T,N.
    Box x = make(a);
    // Raw actual replies include x.MAY/U,D and x.MUST/U,N.
    // Keep x.MUST/U,N; omit covered x.MAY/U,D before the next call.
    // NORMAL exact-point replies remain present too.
    Box y = make(x);
    // Definite uniform U starts the existing MUST queries.
    // y.MUST/T,N and the other required NORMAL replies survive.
    Box z = make(y);
    // z.MUST/U,N reaches the observation.
}
// Published root: ZERO -> NormalTarget(id),N. No fresh DemandTarget.

// Demand includes [p.MAY/m | ret.*/flip(m)] and
//                  [p.f.NE/m | ret.*/flip(m)].
// Submitted a at call one: p.f.MUST/T,N.
// Coarse initial: p.f.*/T,D, with its old companions.
// Fine initial:   p.f.MUST/T,N.
Box make(Box p) {
    Box r = new Box();
    // Same four rules and ordinary return.
    return r;
}
// Coarse and fine summaries can both be published. They are not globally
// collapsed across their different raw initial keys.
```

The complete marked-return/control model has these handoffs:

| Completed run | Current marked DATA demand rows | Root has fresh forward DemandTarget | Persisted NORMAL return rows | NORMAL report retained |
|---|---:|---|---:|---|
| run-1 F/1 | 4 | yes | 0 | no |
| run-2 B/1 | 14 | backward producer permission renewed | 0 | no |
| run-3 F/2 | 3 | no | 18 | yes |
| run-4 B/3 | 0 | no observation seed | 18 | yes |
| run-5 F/4 | 0 | no | 18 | yes; natural stop |

The three remaining run-3 rows come from already admitted coarse work. Keep
them. Do not cancel their queries or delete their method summaries by
inspection of a caller's finding. With no root DemandTarget, the existing
backward ZERO gate launches no corresponding work in run-4. The next
forward handoff is empty and the existing stop rule ends run-5.

The unchanged-policy control model still has root demand through **run-13**
and the earlier uncapped proof remains its non-termination proof. The new
proof constructs all states from run-1, checks within-run quiescence, checks
the source/Target gates, and proves that forced continuation after the quiet
state never recreates the demand. A finite run count does not prove stopping.

## 6. Earlier cases

All results below use the same explicit ZERO/Target control gates. The
baseline column is a diagnostic with the old DATA law in that same model;
it avoids attributing an older control-model difference to this change.
The new column has checked cold states and uncapped no-revival proofs.

| Reference | Same-control baseline stop | New stop | Expected observation |
|---|---|---|---|
| Double | run-15 | run-15 | retained |
| Growth | run-11 | run-7 | retained |
| LongReader | run-5 | run-5 | retained |
| Nested | run-9 | run-9 | retained |
| NestedDeep | run-5 | run-5 | retained |
| NestedExact | run-3 | run-3 | retained |
| NestedLarger | run-9 | run-11 | retained |
| NestedNegative | run-3 | run-3 | absent |
| NestedPositive | run-3 | run-3 | retained |
| NestedSurvivor | run-5 | run-5 | retained |
| OldBB | run-5 | run-5 | retained |
| OldMethod | run-5 | run-5 | retained |
| OrdinaryTwo | run-3 | run-3 | retained |
| Overwrite | run-9 | run-9 | retained |
| Postfix | run-13 | run-13 | retained |
| Prefix | run-7 | run-7 | absent |
| PrefixPostfix | run-11 | run-11 | retained |
| RoundTrip | run-9 | run-9 | retained |

The historical ungated data-only certificates used run-11 for NestedLarger
and run-9 for Prefix. Their input/control scope is different. Do not count that older baseline
change as a speedup. With accumulating Target effects, new NestedLarger
needs two more iterations than the same-control baseline. Removing MAY DATA
changes which C2 families run; a Target that fired before its later NORMAL
provider must still guide refinement. This is a real scheduling cost, not
an extra field expansion or a Target cancellation. All previous code,
topology, source paths and call counts are reused.

The concrete exact, uniform and different-path replay controls all still
stop at **run-5**, with both observations and all their NORMAL records.
They can omit some redundant caller/source activity earlier; the proof does
not falsely assert complete intermediate state equality.
The protected closure still stops at **run-3**. The separately selected
MUST-preserving cleaner still stops at **run-1**. Its accepted cleaner
semantics are unchanged by this repair.

## 7. Soundness and work limits

The new predicate proves whole-region containment. Every concrete point
which could refine the removed candidate already has a retained NORMAL
uniform witness, with the same mark, caller original and literal H.
Use that same point in any finite concrete continuation. For a complete
AND binding, keep all other operands and replace only that operand's
support. A remaining DEMAND operand still makes the join DEMAND.
Do not infer absence, cleaner success or a missing mark from removal.

This is not raw C2-image equivalence. A covered MAY fact could previously
have enabled additional hypothetical EXACT/STAR starts. They can now be
absent. The concrete point argument gives the semantic coverage; the full
cold references check its interaction with the selected C2/C5, source and
Target mechanisms. No global whole-engine bisimulation is claimed.

At a fixed delivery plan the filtered list is a subsequence. It adds no
DATA, C2 query, callback, summary or field suffix. An existing NORMAL prefix
index can find a provider for one scalar candidate in O(L) path traversal,
plus the existing mark/H/E tests; a simple implementation scans k NORMAL
providers in O(k*L). Reuse the store's mark masks and ordinary prefix layout.
There is no cross-call suffix product, full truncation evidence, new global
index, new retained input set or repeated whole-program ownership census.

The new case's return fragment has 26 raw rows at run-3 instead of 48 in
the unchanged-policy control, and no current rows at run-5 instead of 80.
These are reference-model counts, not new project performance measurements.
All NORMAL records already produced remain persisted. Fewer future queries
can infer fewer additional unused NORMAL records; equality of final record
sets is not required for the new case's eventual observation result.

## 8. Validation and scope

[Proof package](../../spec/lean/proposals/normal-must-actual-coverage-20261116/README.md).
The package checks **1,286 new constructive claims; 3,723 audited claims in
170 modules**, using source-hash-checked dependencies. Only `propext` and
`Quot.sound` are permitted. All 18 ordinary cold cases and the new case have selected accumulating-Target
certificates, checked data/publication/quiescence witnesses and uncapped
no-revival proofs. Four earlier data-only control snapshots could forget a
Target that fired before later normalization. They are not used as the
selected control semantics: `UniformSticky` accumulates every such effect.
The three replay controls and protected/cleaner checks are also included.

**20 native tests pass:** ten new coverage adapter tests, the three original
alternating-case tests and seven definite-MUST controls. They check native
binding and guard rejection, arrival order, late providers, real exclusions,
protection, contexts and a genuine field cut. The native production driver
still completes **run-31**; it has not been patched with the proposal.

```bash
python3 spec/lean/proposals/normal-must-actual-coverage-20261116/check.py \
  --out /tmp/normal-uniform-actual-proofs
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.NormalUniformActualCoverageTest \
  --tests org.opentaint.dataflow.bidi.AlternatingConditionalCycleTest \
  --tests org.opentaint.dataflow.bidi.DefiniteMustReplayNativeTest
```

All selected known examples now pass in their stated reference scopes.
There is no universal termination proof for arbitrary programs, GROUP mode,
intrinsic-MAY rule targets or unmodeled side effects. Unsupported coverage
keeps the demand. Production integration and project measurements remain
separate work. No iteration limit, normal report count or later-run data is
used as a redundancy certificate.
