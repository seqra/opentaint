# Demand-edge redundancy patterns

12 November 2026. The user stopped the investigation campaign.
This document collects its accepted patterns. It adds no analyzer behavior.
The production runtime remains `14d7b63369d94f49d4c551be8405ed7719f267cc`.
Large evidence is stored outside Git. See the
[external-data guide](../reports/EXTERNAL_DATA.md) before opening `data/...` links.

## 1. Final results

| Project | Repeated origins | Individually redundant | Unresolved | Latest reached / completed / accepted forward |
| --- | ---: | ---: | ---: | --- |
| OWASP | 1,824 | 759 | 1,065 | run-11 / run-11 / run-11 |
| Conductor | 25,786 | 7,833 | 17,953 | run-8 / run-7 / run-7 |
| Stirling-PDF | 1,021 | 323 | 698 | run-11 / run-10 / run-9 |
| Total | 28,631 | **8,915** | **19,716** | |

The separate joint plan removes **6,955** origins. It keeps **1,960**
individually redundant origins as providers. Do not remove all 8,915 together.
No project necessity case passed the required sole-edge sink-loss test.
Unresolved does not mean necessary. No runtime removal or speedup is claimed.

Evidence: [accepted classification](../reports/data/redundant-demand-20261110/q-separated-individual-joint-v1/acceptance.json),
[individual ledger](../reports/data/redundant-demand-20261110/ledger.jsonl.gz),
[joint plan](../reports/data/redundant-demand-20261110/joint-retirement-plan.json).

## 2. Scope and notation

Use the pinned FULL analyzer. Remove guidance only after a completed forward
run, at run-5 or later. For a repeated edge at runs `i` and `i+2`, remove
after `i+2`. Do not change run-i. The campaign cuts are OWASP run-11,
Conductor run-7 and Stirling-PDF run-9.

Let:

```text
O          = all original outgoing guidance origins at the removal barrier
X          = one origin: complete raw edge membership, owner, context and ports
emit(X)    = every native next-run demand row from X
K          = retained origins
q = (u,e,o)= one demand row: owner u, typed entry e, paired output o
E          = field exclusion
T, U       = full concrete marks
FLOW       = abstract mark
$, *, MAY, MUST = EXACT, STAR, [any], [any-taint]
```

An origin can emit several rows, including all ND member projections.
Keep method and generated inner-block identities. Keep physical ports.
Compare complete decoded field and mark keys; names and hashes are not enough.

`remove X` means omit its next-run guidance contribution. Keep its current
raw summary and all saved NORMAL records. Keep ND premises, protection
memberships, NormalTargets, seeds, source permissions and reports unchanged.

Allowed pattern inputs are demands, summaries and submitted initial facts.
Do not use source code, CFG properties, JVM types, rule forms or report state
as eligibility guards. Treat owner/type strings as opaque identities.
Missing input history is unknown, not empty.

All accepted proofs allow arbitrarily many later iterations and new fields.
The temporary run-11 limit is not a proof premise.

## 3. Pattern A: identical projected guidance

```math
P_exact(X,K) := emit(X) ≠ ∅ ∧
               ∀q ∈ emit(X), ∃Y ∈ K : q ∈ emit(Y)
```

```text
X emits {q1, q2}
Y emits {q1, q3}
Z emits {q2, q4}

Keep Y and Z; omit X's guidance.
The complete demand-row union stays equal.
```

Use actual retained origins as witnesses. Different X rows can use different
origins. A shared display shape or one covered ND arm is insufficient.

The first checked version required witnesses outside the repeated set.
The later basis proof permits any witness that survives the selected cut.

Proof: [UnchangedProjectionCover](../../spec/unchanged-projection-cover.md).
This pattern alone may save no next-run work: the demand builder already
deduplicates identical rows.

## 4. Pattern B: equivalent query coordinates

The following are comparison keys. Do not rewrite actual facts or summaries.

### B1. Equivalent output selectors

For the same base, complete path and full mark M:

```math
(x.p.MAY/M, E=∅) ≡out (x.p.*/M, E=∅)
```

Keep the row's entry, owner and physical exit equal. The law is symmetric.
It also applies when the unchanged typed entry is ZERO or Target.
Other control coordinates remain literal.

```text
qX = (u, entry A, output x.p.MAY/T)
qY = (u, entry A, output x.p.*/T)

Same C2 admission.
Same paired C5 output and relative field budget.
Keep qY's origin; qX needs no separate contribution.
```

This law concerns a demand output selector. It does not equate MAY and STAR
submitted facts, initials or C2 entries. Do not erase nonempty output E.

Proofs: [output selectors](../../spec/equivalent-demand-output-selectors.md),
[symmetric use](../../spec/symmetric-equivalent-demand-output-selectors.md).

### B2. Equivalent concrete-point entries

At restricted run-3 and later:

```math
(x.p.*/T, any legal E) ≡entry (x.p.$/T, E=∅)
```

T must be the same full concrete mark. Keep the base and path equal.
Supported legal bases are This, Argument, Return, LocalVar, Exception and
ClassStatic. Keep the native static grammar. Exclude literal and internal
cleaner bases. FLOW and group marks do not use this law.

Both entries give the same complete C2 family and C5 entry image:

```text
Primary initial: x.p.$/T, with the same actual-derived layer
FLOW companion: none
MAY precision cursor: none
```

Define executable comparison keys:

```text
entryKey(e):
    if e is a supported legal FULL-concrete point:
        require e.tail == STAR or (e.tail == EXACT and e.E == empty)
        return copy(e, tail=EXACT, E=empty)
    return e                              # includes its typed kind

outputKey(o):
    if o is DATA and o.tail == MAY and o.E == empty:
        return copy(o, tail=STAR)
    return o

queryKey(q) = (complete owner and ports, entryKey(q.entry), outputKey(q.output))
```

Thus Pattern A extends to equal `queryKey` values.
Proof: [concrete point queries](../../spec/concrete-point-demand-queries.md).

## 5. Pattern C: split admission and output coverage

A row supplies two services:

```text
C2(q, submitted)       = complete initial family and admission support
C5(q, original, raw,k) = paired summary restriction and output support
```

One retained row can preserve C2. Another can preserve C5.
This is the main generalization of the duplicate-query patterns.

Define:

```text
C2Check(q,z):
    same complete C2 owner and physical entry
    entryKey(q.entry) == entryKey(z.entry)
    # z's output and physical exit can differ

C5Check(q,y):
    same complete owner, physical exit and typed output kind
    outputKey(q.output) == outputKey(y.output)
    entryKey(q.entry) == entryKey(y.entry)
        or PointMayImageContains(y.entry, q.entry)
```

The checks preserve layers, FLOW companions, precision cursors, prepared
output support and the complete original ND premise. C5 always uses one
row's paired entry/output. Do not create a new pair from unrelated coordinates.

### C1. Point-to-MAY output coverage

This adapter supplies C5 containment, not C2 equivalence:

```math
q.entry = a.p.point/T
y.entry = a.r.MAY/T, E=∅
p = r  OR  p = r ++ CLASS* ++ c
c.kind ∈ {FIELD, ELEMENT}
```

The suffix ends at its first counted accessor. FIELD and ELEMENT count;
CLASS does not. Keep all other entry coordinates equal. The supported bases
are This, Argument, Return and LocalVar. This adapter excludes statics and
Exception. The q entry must satisfy B2's legal full-concrete point rules.

```text
q = (u, entry a.f.point/T, output Q)     # selected row
z = (u, entry a.f.point/T, output R)     # retained C2 witness
y = (u, entry a.MAY/T,     output Q)     # retained C5 witness

z emits exactly q's initial family.
Every stored original accepted by q is also accepted by y.
y applies the same output program and field cut to that original/raw packet.
```

Y alone is insufficient. On `a.f.*/T, DEMAND`, q emits `a.f.$/T`.
Y can emit a STAR primary and FLOW companions instead. Z must preserve q's
exact admission service. Same-path MAY coverage has the same requirement.

### C2. Complete-origin certificate

```text
checkCut(O, R, certificates):
    K = O - R
    for X in R:
        require emit(X) is complete and nonempty
        for q in emit(X):
            (Z,z), (Y,y) = certificates[X,q]
            require Z in K and z in emit(Z)
            require Y in K and y in emit(Y)
            require C2Check(q,z)
            require C5Check(q,y)
    return SAFE_GUIDANCE_CUT
```

All witnesses end at actual final retained origins. Recheck every affected
certificate when the cut changes. Do not accept circular support.

The existing witnesses preserve each removed service. Retained rows add no
new service: they were already in O. Therefore the full demand oracle stays
equal. With the other barrier state unchanged, later semantic observations
stay equal for every finite continuation. Diagnostic callback counts may vary.

Proofs: [retained service basis](../../spec/retained-demand-service-basis.md),
[individual service cover](../../spec/individual-retained-query-service-cover.md).
They generalize the [retained query basis](../../spec/retained-demand-query-basis.md)
and its earlier whole-row patterns. No new proof is claimed by this summary.

## 6. Individual classification versus joint removal

```math
IndividualRedundant(X) := checkCut(O, {X}, certificateX)
JointSafe(R)           := checkCut(O, R, jointCertificates)
```

An individual certificate can use any other original edge. It can use an
edge that also has an individual REDUNDANT verdict.

```text
emit(A) = emit(B) = {q}; no other origin emits q.

Remove only A: safe; B remains.
Remove only B: safe; A remains.
Remove A and B: not certified; no q provider remains.
```

A joint plan can keep an individually redundant representative. This does
not make that representative necessary. The accepted plan is not claimed
to be a minimum basis or a maximum removal set.

## 7. Rejection rules and evidence limits

| Proposed shortcut | Why it is insufficient |
| --- | --- |
| X repeats at i and i+2. | Repetition selects a target; it proves no future redundancy. |
| A similar NORMAL summary exists. | It may preserve a concrete transfer while losing C2, C5 or later source permission. |
| C2 is covered. | A different paired output can still admit a required future summary. |
| C5 is covered. | A required exact initial or precision profile can still be lost. |
| Most ND arms or ports are covered. | Every emitted row needs a retained witness. |
| Witness survived an earlier removal. | It must survive the final joint cut. |
| No later finding before run-11. | The proof must allow unbounded later iterations. |
| No captured submitted facts. | Missing history cannot prove an empty input set. |
| Generic test loses a sink. | It does not classify a project edge without its complete route/provider mapping. |

The original source/CFG-based P, source-safe replay, closed FLOW-frontier,
hard-cutoff and final-report patterns are withdrawn under this contract.
Their old evidence remains archived. They are not accepted removal rules.

The campaign ended with OPEN cases, including OWASP `4378d285...`.
Their component proofs and synthetic cases remain research evidence.
They do not extend the accepted patterns above.

Use the [campaign report](../reports/bidirectional-redundant-demand-campaign-20261110.md)
for the full investigation history and the
[predicate catalog](../reports/data/redundant-demand-20261110/predicate-catalog.json)
for versioned proof links. A later production change needs a separate
implementation proposal and validation.
