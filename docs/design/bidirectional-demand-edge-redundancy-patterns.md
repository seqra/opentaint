# Handoff compaction: summary subsumption and demand redundancy

12 November 2026. This review separates two contracts. **Native summary
subsumption can compact saved relations. Demand-query subsumption can compact
next-run guidance. One proof does not automatically establish the other.**
No analyzer behavior changes. The reference runtime remains
`14d7b63369d94f49d4c551be8405ed7719f267cc`, FULL mode.
The investigation campaign remains stopped.

## 1. Reclassification of the earlier patterns

| Earlier item | Result of the review | Saved NORMAL records | Next demand |
| --- | --- | --- | --- |
| A: identical projections | Exact demand-row duplication. Projection forgets information. | No deletion follows from equal projections alone. | Proved. |
| B1: MAY/STAR output selectors | Demand-query equivalence. The displayed weaker-premise raw direction is a generalization candidate. | The symmetric query law is insufficient. | Proved, in either orientation. |
| B2: concrete-point entry keys | Demand-query equivalence, not a general stronger-postcondition law. STAR preserves a suffix. | No raw replacement follows. The displayed DEMAND rows are not persisted. | Proved for late FULL concrete points. |
| C1: point-to-MAY coverage | C5 containment plus a separate C2 witness. | X-by-Y raw subsumption is not proved. | Proved with both services covered. |
| C2: complete-origin certificate | Coverage of every projected ND row. | Not a proof of arbitrary ND summary deletion. | Proved. |
| C3: decision order | A procedure, not another algebraic rule. | Use native summary rules. | Use demand rules. |
| Individual versus joint removal | A constraint on retained representatives. | No new raw subsumption rule. | Keep final witnesses; reject circular support. |

The detailed [demand-query catalog](bidirectional-demand-query-compaction-patterns.md)
keeps the old labels, handoff-state examples and accepted proof links.
Sections 3–5 below identify the native rules and the proposed generalizations.

## 2. The handoff state and the two contracts

Let `j = i+2`. Compute all decisions after run-j completes, before run-(j+1).
Inputs are current demand/summary edges and any retained earlier initial
history. No input first learned in run-(j+1) is allowed. Source code, CFG,
JVM types and report state are not pattern eligibility guards.

```text
O_j       = complete current outgoing guidance origins
N_j       = legal new and previously saved NORMAL records
G(X)      = existing handoff projection of current origin X
K         = final retained origins for a checked demand cut
$, *, MAY, MUST = EXACT, STAR, [any], [any-taint]
```

For a current DATA summary, G is computed now:

```math
G({I_1,...,I_n} → C) = { (nextOwner, g(C), g(I_k)) | 1 ≤ k ≤ n }
```

Apply this to every conclusion leaf and ND member. Reverse block ports.
`g` maps MUST to MAY and clears its field exclusion. It clears FLOW mark
exclusions and FLOW/STAR field exclusions. Other coordinates follow the
existing typed handoff rules. DemandTarget gives a Target entry; NormalTarget
is not refinement demand. G does not execute the next run.

The two proof obligations are different:

```text
Native summary compaction:
    retained relations must reproduce the removed relation's supported
    current/direct/opposite applications, with the required correlation,
    complete originals, layers, protection and interface.

Demand compaction:
    retained projected rows must preserve complete C2 admission and paired
    C5 restriction, including owner/port/precision support and the stop test.
```

Do not infer either contract merely from an abstract set of output locations.
In particular:

| Tail | Meaning relevant to this review |
| --- | --- |
| EXACT | The specified location. |
| STAR | A suffix correlated with the input; it is not uniform taint. |
| MAY | An unknown location represented by a DEMAND approximation. |
| MUST | Uniform taint over the admitted region. |

## 3. Part I: validated native summary-subsumption rules

### S1. Literal payload inclusion under an identical complete premise

```math
X = (Γ, P, C_X),  Y = (Γ, P, C_Y)
LiteralLeaves(C_X) ⊆ LiteralLeaves(C_Y)
────────────────────────────────────────
Y covers X
```

Γ contains the complete owner/context, direction, block, ports and compatible
native headers. Keep the same layer and the full premise P. Each covered leaf
has the same path, tail, full mark, exclusions and protection membership.
This is literal relation inclusion, not MAY/STAR or MUST/EXACT conversion.
Both compared packets must be legal native values.

**State after i+2:**

```text
X, NORMAL: p.*/FLOW → ret.f.*/FLOW
Y, NORMAL: p.*/FLOW → {ret.f.*/FLOW, ret.g.*/FLOW}

Persist Y's payload once. X adds no literal relation leaf.
In the opposite view, Y still has the identical ret.f → p leaf.
For any outgoing rows, G(X) is also a subset of G(Y).
```

The same literal check applies to guidance when both origins contribute
outgoing rows. Saved persistence uses only eligible NORMAL records; it does
not start persisting DEMAND or ND rows. Equal complete ND premises can use
literal payload inclusion in their current store without weakening AND.

Proof: [literal payload component](../../spec/lean/proposals/handoff-subsumption-review-20261112/RelationAndQuery.lean).
The native bridge is the existing per-premise union and per-leaf direct/
opposite application. All non-summary handoff state stays unchanged.

### S2. Correlated NORMAL FLOW specialization

This is an existing validated summary rule, not a new campaign result:

```math
S, NORMAL: a.u.* / EiS → b.v.* / EoS
L, NORMAL: a.u.r.* / EiL → b.v.r.* / EoL
```

The same r must extend both endpoints. Require the same full interface and
protection class. Set `ES = EiS ∪ EoS` and `EL = EiL ∪ EoL`.
Require `mxS ⊆ mxL`, and:

```text
r is empty:     ES is a subset of EL
r is nonempty:  ES admits r's first field
```

Keep legal static anchors intact. For packed conclusions, check each removed
output against a real retained output with that same shift. The witness for
a suffix `tau` in L is `r ++ tau` in S, in both directions.

**State after i+2:**

```text
S, NORMAL: p.*/FLOW   → ret.*/FLOW
L, NORMAL: p.f.*/FLOW → ret.f.*/FLOW

Persist S; omit L.
Actual p.f.g.$/T maps to ret.f.g.$/T through S as well as L.
Both unary NORMAL rows contribute no next refinement demand.
```

Use the existing overlap matcher and directional inside policy. Do not
extend this rule to a shift on only one endpoint or to arbitrary tails.
The already selected FLOW-backed concrete cells retain their separate
layer, mark and protection guards; this review does not widen them.

Full contract: [relation subsumption, section 3](../../spec/edge-subsumption-initial-emission-demand-intersection.md#3-relation-subsumption).

## 4. Part II: validated demand-query compaction

These rules can run at every supported late handoff. Repetition was the
campaign's candidate filter; their algebraic checks need no earlier repeat.
They compact **projected demand rows**. They do not, by themselves, remove
saved NORMAL providers.

### D1. Canonical query equivalence: earlier A, B1 and B2

```text
entryKey(e):
    if e is a supported legal late FULL concrete point:
        # STAR with legal E, or EXACT with empty E
        return copy(e, tail=EXACT, E=empty)
    return e

outputKey(o):
    if o is DATA and o.tail == MAY and o.E == empty:
        return copy(o, tail=STAR)
    return o

queryKey(q) = (full owner/ports, entryKey(q.entry), outputKey(q.output))
```

Equal query keys can share one retained demand-row representative. Literal
ZERO/Target kinds remain distinct. The point rule does not apply to FLOW or
GROUP entries. Keep the original legal-base and exclusion guards.

**Why B1 is not symmetric raw subsumption:** its displayed raw summaries are

```text
X: a.f.MUST/T → ret.MAY/T, DEMAND
Y: a.f.*/T   → ret.MAY/T, DEMAND
```

Y has the weaker raw premise. The reverse replacement is not valid for
current application: exact input `a.f.$/T` satisfies Y but not X. Yet their
projected output selectors are equivalent. A proof of that symmetric query
law cannot be reused as a symmetric raw summary law. The weaker-premise
raw direction remains a separate generalization opportunity.

**Why B2 is not a general stronger-postcondition rule:**

```text
X: a.*/T → ret.$/T, DEMAND
Y: a.*/T → ret.*/T, DEMAND
Actual: a.f.$/T, NORMAL

apply(X, Actual) = ret.$/T,   DEMAND
apply(Y, Actual) = ret.f.$/T, DEMAND
```

Y does not reproduce X's root result. STAR carries f; it does not assert
uniform taint. After handoff, the concrete STAR and EXACT entries have an
equal late C2 key, which is a different statement. Also, concrete STAR
initials are DEMAND and are not legal native NORMAL record premises.
The [native controls](../../spec/lean/proposals/handoff-subsumption-review-20261112/native-receipt.json)
verify both distinctions. These are operator counterexamples, not a new
whole-project finding-loss claim.

### D2. Split service coverage: earlier C1 and C2

```text
C2Check(q,z): same C2 owner and equal canonical entry keys
C5Check(q,y): same paired output/port and
             (equal entry keys or proved point-to-MAY image containment)

Covered(q,K) =
    exists z in K: C2Check(q,z)
    and exists y in K: C5Check(q,y)
```

The point-to-MAY case permits the same path or its first counted extension,
with the same full mark and the existing ordinary-base guards.

**State after i+2:**

| Current DEMAND summary | Computed demand `(entry; output)` |
| --- | --- |
| X: `b.*/U → a.f.$/T` | qX = `(a.f.$/T; b.*/U)` |
| Z: `c.*/U → a.f.$/T` | qZ = `(a.f.$/T; c.*/U)` |
| Y: `b.*/U → a.MAY/T` | qY = `(a.MAY/T; b.*/U)` |

Keep qZ and qY. qZ preserves qX's C2 family; qY preserves qX's paired C5.

**Why Z appears:** this sufficient proof preserves exact admission replies.
On the symbolic offer `a.f.*/T, DEMAND`:

```text
C2(qX): a.f.$/T, DEMAND
C2(qY): a.f.*/T, DEMAND
        a.f.*/FLOW, NORMAL
        a.$/FLOW, NORMAL
```

Y does not supply the same exact initial. The native control confirms the
difference and confirms that both C5 entries accept the stored exact point.

This does **not** prove that Z is necessary for every possible sound rule.
A Y-only rule could use a stronger proof about the different starts. That
proof is not supplied by the campaign. A missing initial alone is not a
proof of a lost sink.

Nor is Y's MAY output a stronger definite postcondition: `a.MAY/T` can refer
to g rather than f. C5 image containment alone does not prove raw X-by-Y
summary subsumption.

For a complete outgoing origin, check every projected row. Keep all ND
members and ports. This gives the accepted whole-origin certificate; it
does not replace native ND execution by unary OR execution.

## 5. Generalization candidates: weaker premises and stronger postconditions

The requested logical template is valid for ordinary positive Horn rules:

```math
Pre_X ⇒ Pre_Y,  Post_Y ⇒ Post_X
───────────────────────────────
(Pre_Y ⇒ Post_Y) entails (Pre_X ⇒ Post_X)
```

In particular:

```text
Y: P → C
X: P AND Q → C

Y logically subsumes X.
```

The [constructive component](../../spec/lean/proposals/handoff-subsumption-review-20261112/RelationAndQuery.lean)
proves the premise-subset case. It does not identify correlated AP tails
with ordinary independent propositions.

To promote B1 or the ND example to a general native rule, prove its application
and handoff bridges. Preserve complete caller originals, actual-derived
layers, inherited/cycle protection, both saved read directions and the
required demand admission. Do not infer these bridges from field-set
inclusion or from one removed query reply.

Thus the review yields useful generalization targets, but not an approved
blanket "weaker premise plus larger field region" compactor. Only validated
native cells belong in Part I. Missing bridge proofs stay explicit.

## 6. Handoff procedure and the missing C3 example

Freeze the original outgoing set before either compaction. Do not build
next demand solely by projecting the compacted NORMAL store.

```text
handoff(j, completedRun, savedRecords):
    require completedRun is COMPLETE
    O = snapshotAllOutgoingGuidance(completedRun)
    rows = {X: projectDemand(X) for X in O}       # computed now

    normal = savedRecords union legalNormalRecords(completedRun)
    normal = compactWithValidatedNativeRules(normal)  # Part I

    K, certificates = selectRetainedDemandBasis(O, rows)
    require every removed origin's complete rows pass D1/D2 against final K
    demand = buildDemand(union(rows[Y] for Y in K))   # Part II

    persist(normal)
    preserve ordinary seeds, NormalTargets and other handoff state
    publish demand and its counts
    apply the ordinary stop/continue check
```

**State after i+2:**

```text
NORMAL:
  N0: p.*/FLOW   → ret.*/FLOW
  N1: p.f.*/FLOW → ret.f.*/FLOW
DEMAND:
  X: b.*/U → a.f.$/T
  Z: c.*/U → a.f.$/T
  Y: b.*/U → a.MAY/T

Computed now:
  qX = (a.f.$/T; b.*/U)
  qZ = (a.f.$/T; c.*/U)
  qY = (a.MAY/T; b.*/U)

Native S2: keep N0, remove N1 from saved records.
Demand D2: qX uses qZ for C2 and qY for C5.

Persisted result: {N0}
Next demand:     {qZ,qY}
```

All inputs and witnesses are present at this handoff. The two results use
different proof contracts. No actual run-(i+3) offer or summary is inspected.
This is a proposed compaction organization; production is unchanged.

**Joint representative example, earlier section 6:**

```text
A: a.f.*/T → ret.MAY/T
B: a.f.*/T → ret.MUST/T
G(A) = G(B) = { (ret.MAY/T; a.f.*/T) }

Removing only A is safe for demand; B remains.
Removing only B is safe for demand; A remains.
Removing both fails: no representative remains.
```

This symmetric demand statement does not make the raw conclusions equal.
If a validated native rule prefers the stronger MUST provider, retain it.
Representative selection is a constraint on a compactor, not another
subsumption theorem.

## 7. Evidence, results and unchanged scope

The campaign remains stopped with 8,915 individually redundant origins,
19,716 unresolved origins and a separate checked 6,955-origin joint plan.
Those counts concern demand contributions. They are not counts of removable
saved records. No original project necessity case passed the sole-edge
sink-loss gate.

| Project | Latest reached / completed / accepted forward |
| --- | --- |
| OWASP | run-11 / run-11 / run-11 |
| Conductor | run-8 / run-7 / run-7 |
| Stirling-PDF | run-11 / run-10 / run-9 |

The review's 13 constructive component claims pass. Isolated native scalar
application and C2/C5 controls pass. They ran no engine iteration or project
scan and prove no new whole-engine deletion rule. Existing broader native
rules retain their existing proofs and scope.

See the [proof receipt](../../spec/lean/proposals/handoff-subsumption-review-20261112/lean-receipt.json),
[native receipt](../../spec/lean/proposals/handoff-subsumption-review-20261112/native-receipt.json),
[demand-query catalog](bidirectional-demand-query-compaction-patterns.md) and
[campaign report](../reports/bidirectional-redundant-demand-campaign-20261110.md).
Large evidence remains outside Git; use the
[external-data guide](../reports/EXTERNAL_DATA.md).

A new raw summary law can change analyzer semantics even when motivated by
compaction. Prove its full contract before selecting an implementation.
Keep source, sink, field transfer, marks, layers, protection and stop behavior
unchanged unless a separate semantic change is explicitly selected.
