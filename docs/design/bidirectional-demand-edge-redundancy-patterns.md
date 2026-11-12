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

Let `j = i+2`. Every pattern decision is computed during the `j → j+1`
handoff, before run-(j+1) starts. No pattern can read results from run-(j+1).

Let:

```text
O_j        = all original outgoing guidance origins from completed run-j
O          = O_j
X          = one origin: complete raw edge membership, owner, context and ports
projectDemand(X) = rows computed from X by the current handoff projection
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

### 2.1 Handoff projection is available now

Earlier documents called this operation `emit(X)`. That name does not mean
"observe what run-(j+1) emits." It means compute the demand rows **for**
run-(j+1), from completed run-j summaries. Use `projectDemand` below.

For a DATA summary, the existing handoff reverses its endpoints:

```math
X = {I_1, ..., I_n} → C
projectDemand(X) = { (nextOwner(X), g(C), g(I_k)) | 1 ≤ k ≤ n }
```

Here `g` is the existing `guidancePattern` normalization. For packed results,
apply this formula to every conclusion leaf. Keep every ND premise member.
For an inner block, reverse the physical boundary ports too.

```text
projectDemand(X):                         # runs inside the run-j handoff
    owner = reverseBoundaryOwner(X.owner)
    if X.conclusion is DemandTarget:
        return { typedRow(owner, Target, g(I)) for I in X.premise.members }
    return { typedRow(owner, g(C), g(I))
             for C in conclusionLeaves(X)
             for I in X.premise.members }

g(pattern):
    if pattern.tail == MUST:
        pattern = copy(pattern, tail=MAY, fieldExclusion=empty)
    if pattern.mark is FLOW:
        pattern = copy(pattern, markExclusion=empty)
        if pattern.tail == STAR:
            pattern = copy(pattern, fieldExclusion=empty)
    return pattern
```

`typedRow` keeps DATA, ZERO and Target distinct. `g(ZERO)` is the same
canonical ZERO. NormalTarget is not outgoing refinement demand. These are
the existing method/block handoff rules, not additional analyzer execution.

```text
At the end of run-j, before any work in run-(j+1):

X: a.f.*/T → ret.MAY/T, DEMAND
projectDemand(X): entry ret.MAY/T; output a.f.*/T

Y: {a.f.*/T, b.$/U} → ret.MAY/T, DEMAND
projectDemand(Y): entry ret.MAY/T; output a.f.*/T
                 entry ret.MAY/T; output b.$/U

Y already supplies X's projected row at this handoff.
The next run need not submit a fact or produce a summary to establish this.
```

The implementation computes these rows in
[`HandOff`](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/HandOff.kt)
and [`BlockHandOff`](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/BlockHandOff.kt).

### 2.2 Input availability

| Pattern input | Available at the run-j handoff? |
| --- | --- |
| O_j and complete method/block edge identities | Yes: completed run-j stores. |
| `projectDemand(X)` for X in O_j | Yes: the pure projection above. |
| Candidate repetition at j-2 and j | Yes, if the earlier edge identities were retained. Missing history cannot prove repetition. |
| Entry/output keys and point-to-MAY geometry | Yes: compare projected rows from O_j. |
| Witness membership in final K | Yes: K is a selected subset of O_j, fixed at this handoff. |
| Generic C2/C5 equivalence laws | Already proved. Their use requires no future calls to C2/C5. |
| Actual submitted facts, C2 initials or summaries from run-(j+1) | No. They cannot decide removal. |
| A provider first learned during run-(j+1) | No. It cannot witness a removal at handoff j. |

Patterns A–C need no submitted-fact history. Their C2/C5 laws hold for every
legal future query. Future query values are proof variables, not runtime
inputs to the pattern checker. Earlier submitted facts may support research;
they do not replace a missing current retained provider.

The handoff-state review checked all accepted certificates: 20,256 witness
memberships for 8,915 individual cases and 16,168 for the 6,955-origin joint
plan. Every witness is in its original removal-barrier snapshot. No later-run
witness is used. Counts and classifications are unchanged.

### 2.3 Example conventions

Each example below is a state at completed forward run `j = i+2 ≥ 5`.
T and U are full concrete marks. E is empty unless stated otherwise.
All listed origins share one method/block owner and the same boundary ports.
Their layer is DEMAND. Other analyzer state stays unchanged.

The left column contains current summaries. The right column is computed
from that same column during this handoff. It is not a future-run trace.
O contains the listed origins; K is the proposed retained subset of O.

## 3. Pattern A: identical projected guidance

```math
P_exact(X,K) := X ∈ O_j ∧ K ⊆ O_j \ {X} ∧ projectDemand(X) ≠ ∅ ∧
               ∀q ∈ projectDemand(X), ∃Y ∈ K : q ∈ projectDemand(Y)
```

**State after i+2:**

| Current summary | `projectDemand`, written as `(entry; output)` |
| --- | --- |
| X: `a.f.*/T → ret.MAY/T` | `(ret.MAY/T; a.f.*/T)` |
| Y: `a.f.*/T → ret.MUST/T` | `(ret.MAY/T; a.f.*/T)` |

```text
O = {X,Y}; K = {Y}
q = (ret.MAY/T; a.f.*/T)
projectDemand(X) = {q} = projectDemand(Y)
therefore P_exact(X,K) = true
```

**Reason:** handoff normalization turns Y's MUST conclusion into a MAY entry.
The same demand pair remains through Y. Omit only X's guidance contribution;
keep both raw summaries. No fact from run-(i+3) is needed.

Use origins already present in O_j as witnesses. Different X rows can use different
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

**State after i+2:**

| Current summary | `projectDemand` `(entry; output)` |
| --- | --- |
| X: `a.f.MUST/T → ret.MAY/T` | qX = `(ret.MAY/T; a.f.MAY/T)` |
| Y: `a.f.*/T → ret.MAY/T` | qY = `(ret.MAY/T; a.f.*/T)` |

```text
O = {X,Y}; K = {Y}
qX.entry = qY.entry = ret.MAY/T
outputKey(qX.output) = outputKey(qY.output) = a.f.*/T
queryKey(qX) = queryKey(qY)
```

**Reason:** C2 uses the same entry. The empty-E MAY/STAR output law gives
the same C5 result and field cut. Keep Y; omit X's guidance. The symmetric
law also permits keeping X instead. The choice must remain consistent in
the joint plan.

**Target-entry variant:** replace both current conclusions with DemandTarget.
The computed entries are then both Target; the outputs remain `a.f.MAY/T`
and `a.f.*/T`. The same output-selector law applies at this handoff.

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

**State after i+2:**

| Current summary | `projectDemand` `(entry; output)` |
| --- | --- |
| X: `a.*/T → ret.*/T` | qX = `(ret.*/T; a.*/T)` |
| Y: `a.*/T → ret.$/T` | qY = `(ret.$/T; a.*/T)` |

```text
O = {X,Y}; K = {Y}
entryKey(qX.entry) = entryKey(qY.entry) = ret.$/T
qX.output = qY.output = a.*/T
queryKey(qX) = queryKey(qY)
```

**Reason:** these late full-concrete entries have equal complete C2 families
and equal C5 entry images. Their paired outputs are identical. Keep Y;
omit X's guidance. The checker compares keys; it does not wait to observe
which submitted fact the next run will provide.

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

These expressions state the operator laws. The checker below does not call
them with observed run-(j+1) facts. It compares current projected row keys.

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

**State after i+2:**

| Current summary | `projectDemand` `(entry; output)` |
| --- | --- |
| X: `b.*/U → a.f.$/T` | q = `(a.f.$/T; b.*/U)` |
| Z: `c.*/U → a.f.$/T` | z = `(a.f.$/T; c.*/U)` |
| Y: `b.*/U → a.MAY/T` | y = `(a.MAY/T; b.*/U)` |

```text
O = {X,Z,Y}; K = {Z,Y}
C2Check(q,z) = true           # same owner and exact entry; output can differ
C5Check(q,y) = true           # same output; f is the first counted extension
```

**Reason:** Z preserves q's complete admission service. Y's entry image
contains q's exact point, and Y supplies the same output program. Both
witnesses already exist in O. Neither depends on a new summary or initial
from run-(i+3).

Y alone is insufficient. On `a.f.*/T, DEMAND`, q emits `a.f.$/T`.
Y can emit a STAR primary and FLOW companions instead. Z must preserve q's
exact admission service. Same-path MAY coverage has the same requirement.
This is a symbolic operator comparison, not a next-run input to the checker.

### C2. Complete-origin certificate

```text
checkCut(O, rows, R, certificates):
    require O is the frozen completed run-j outgoing set
    require rows == {X: projectDemand(X) for X in O}
    require R is a subset of O
    K = O - R
    for X in R:
        require rows[X] is complete and nonempty
        for q in rows[X]:
            (Z,z), (Y,y) = certificates[X,q]
            require Z in K and z in rows[Z]
            require Y in K and y in rows[Y]
            require C2Check(q,z)
            require C5Check(q,y)
    return SAFE_GUIDANCE_CUT
```

All witnesses end at actual final retained origins. Recheck every affected
certificate when the cut changes. Do not accept circular support.

**State after i+2, with a multi-row origin:**

| Current summary | Complete `projectDemand` `(entry; output)` |
| --- | --- |
| X: `{b.*/U,c.*/U} → a.f.$/T` | q1 = `(a.f.$/T; b.*/U)`; q2 = `(a.f.$/T; c.*/U)` |
| Y: `b.*/U → a.MAY/T` | y = `(a.MAY/T; b.*/U)` |
| Z: `c.*/U → a.f.$/T` | z = `(a.f.$/T; c.*/U)` |

```text
O = {X,Y,Z}; R = {X}; K = {Y,Z}
certificate[X,q1] = (C2: Z/z, C5: Y/y)
certificate[X,q2] = (C2: Z/z, C5: Z/z)
checkCut(O, rows, R, certificate) = true
```

**Reason:** every projected ND member has both services. q1 uses the
point-to-MAY adapter; q2 uses an identical row. X's complete AND premise
stays in current summary storage. If Z is also removed, this certificate
fails: q2 and the shared C2 witness lose their retained provider.

The existing witnesses preserve each removed service. Retained rows add no
new service: they were already in O. Therefore the full demand oracle stays
equal. With the other barrier state unchanged, later semantic observations
stay equal for every finite continuation. Diagnostic callback counts may vary.

Proofs: [retained service basis](../../spec/retained-demand-service-basis.md),
[individual service cover](../../spec/individual-retained-query-service-cover.md).
They generalize the [retained query basis](../../spec/retained-demand-query-basis.md)
and its earlier whole-row patterns. No new proof is claimed by this summary.

### C3. Decision order within the handoff

```text
atHandoff(j, completedRun, earlierEdgeIds):
    require completedRun.index == j and completedRun.status == COMPLETE
    require j is FORWARD and j >= 5
    O = allOutgoingGuidance(completedRun)   # includes methods and inner blocks
    rows = {X: projectDemand(X) for X in O}
    candidates = repeatedOrigins(earlierEdgeIds[j-2], O)

    # Separate individual classifications. No candidate is removed here.
    for X in candidates:
        individual[X] = findCertificates({X}, O - {X}, rows)

    # Reference joint selection: every trial rechecks its complete cut.
    R = empty
    certificates = empty
    for X in candidates with a checked individual certificate:
        trial = R union {X}
        trialCertificates = findCertificates(trial, O - trial, rows)
        if trialCertificates exists and checkCut(O, rows, trial, trialCertificates):
            R = trial
            certificates = trialCertificates

    require checkCut(O, rows, R, certificates)
    nextDemand = buildDemand(union(rows[Y] for Y in O - R))
    return nextDemand                    # only then start run-(j+1)
```

`findCertificates` searches finite current row indexes with `C2Check` and
`C5Check`. If a required witness is missing, the trial fails. It does not
start the next engine, test a future offer or wait for another provider.
The reference order is not an implementation complexity claim.

Keep the ordinary handoff's seeds, NORMAL persistence and other state.
Build its demand counts and apply its stop check after the checked selection.
Missing repetition history leaves the origin unselected. This clarification
changes no transfer rule, proof predicate or accepted classification.

## 6. Individual classification versus joint removal

```math
IndividualRedundant(X) := checkCut(O, rows, {X}, certificateX)
JointSafe(R)           := checkCut(O, rows, R, jointCertificates)
```

An individual certificate can use any other original edge. It can use an
edge that also has an individual REDUNDANT verdict.

**State after i+2:** use Pattern A's two current summaries, named A and B:

```text
A: a.f.*/T → ret.MAY/T
B: a.f.*/T → ret.MUST/T
q = (ret.MAY/T; a.f.*/T)
O = {A,B}; projectDemand(A) = projectDemand(B) = {q}

Individual cut {A}: K={B}; safe.
Individual cut {B}: K={A}; safe.
Joint cut {A,B}:    K={};  fails the retained-witness check.
Joint cut {A}:     K={B}; safe, even though B is individually redundant.
```

**Reason:** the final retained set is chosen at this handoff. Future
providers cannot repair a failed joint certificate at the removal point.

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
| A matching provider appears in run-(j+1). | It was unavailable at handoff j and cannot be a witness. |
| Sampled next-run C2/C5 results look equal. | The accepted checker needs current structural keys and a proved universal law. |
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
