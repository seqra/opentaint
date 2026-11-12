# Demand-query compaction patterns

12 November 2026. This is the demand-only part of the
[handoff compaction review](bidirectional-demand-edge-redundancy-patterns.md).
The historical A/B/C labels remain in parentheses. These rules remove
redundant guidance. They do not authorize removal of saved NORMAL records.
This catalog describes the historical pattern proofs. Use the updated
[campaign specification](bidirectional-redundant-demand-elimination-campaign-20261110.md)
to bind them to retained post-handoff rows before reuse.

## 1. State available at handoff

Use the pinned FULL runtime, after a completed forward run `j=i+2 ≥ 5`.
The next run has not started. Each example uses the same complete owner,
context, direction and physical ports. E is empty unless stated otherwise.
T and U are full concrete marks. Current example edges are DEMAND.

```text
O = all current outgoing guidance origins
G(X) = existing handoff projection, computed from current X
K = final retained origins
q = (entry; paired output), with its complete owner and ports
```

For every conclusion leaf and premise member:

```math
G({I_1,...,I_n} → C) = { (nextOwner, g(C), g(I_k)) | 1 ≤ k ≤ n }
```

Reverse block boundary ports. `g` maps MUST to MAY and clears its E; it
clears FLOW mark exclusions and FLOW/STAR E. Keep the other native typed
coordinates. DemandTarget projects to a Target entry. NormalTarget is not
refinement demand. This is the existing projection, not a next-run trace.

Only demands, summaries and submitted-initial history are legal pattern
inputs. The rules below need no submitted history. They use no source/CFG/
JVM type/report guards, iteration cutoff or provider learned after j.

## 2. Equal demand-query keys

### D1a. Identical projection (earlier A)

```math
G(X) ≠ ∅ ∧ ∀q∈G(X), ∃Y∈K : q∈G(Y)
```

**State after i+2:**

```text
X: a.f.*/T → ret.MAY/T
Y: a.f.*/T → ret.MUST/T
G(X) = G(Y) = { (ret.MAY/T; a.f.*/T) }
```

Keep Y; omit X's guidance. MUST-to-MAY handoff normalization gives the
same row. Keep the raw summaries. Equal projections do not imply equal
raw postconditions. Each row of a multi-row origin needs a witness.

Proof: [unchanged projection cover](../../spec/unchanged-projection-cover.md).

### D1b. Equivalent output selectors (earlier B1)

```math
(x.p.MAY/M, E=∅) ≡output (x.p.*/M, E=∅)
```

Keep the same complete entry, owner, physical exit, path and mark. The law
is symmetric. It also applies to an unchanged ZERO or Target entry with a
DATA output. Keep control kinds literal.

**State after i+2:**

| Current summary | G, written as `(entry; output)` |
| --- | --- |
| X: `a.f.MUST/T → ret.MAY/T` | `(ret.MAY/T; a.f.MAY/T)` |
| Y: `a.f.*/T → ret.MAY/T` | `(ret.MAY/T; a.f.*/T)` |

The entries give equal C2 admission. The output-selector law gives equal
paired C5 results and relative field budgets. Either demand representative
can remain. Replacing both current conclusions by DemandTarget gives the
same example with Target entries.

Y's weaker premise gives a valid directional DEMAND-edge subsumption at
handoff: keep Y and omit X's obligation. The existing query proof is even
symmetric. The asymmetry of current raw premise matching does not refute
this joined-handoff rule. Neither orientation authorizes changing NORMAL
replay. See [DS-PRE](bidirectional-demand-edge-redundancy-patterns.md#ds-pre-weaker-premise-same-demand-conclusion-b1).

Proofs: [output selectors](../../spec/equivalent-demand-output-selectors.md),
[symmetric use](../../spec/symmetric-equivalent-demand-output-selectors.md).

### D1c. Equivalent concrete-point entries (earlier B2)

At restricted run-3 and later:

```math
(x.p.*/T, legal E) ≡entry (x.p.$/T, E=∅)
```

Use the same full T, base and path. Supported legal bases are This,
Argument, Return, LocalVar, Exception and ClassStatic. Keep the native static
grammar. Exclude literal/internal cleaner bases. FLOW and GROUP do not use
this law. Both entries have the same exact concrete C2 family, actual-derived
layer and stored-entry image; neither gives a FLOW companion or MAY cursor.

**State after i+2:**

| Current summary | G `(entry; output)` |
| --- | --- |
| X: `a.*/T → ret.*/T` | `(ret.*/T; a.*/T)` |
| Y: `a.*/T → ret.$/T` | `(ret.$/T; a.*/T)` |

The entries share the concrete point key and their outputs are identical.
Because X and Y are DEMAND edges at the joined handoff, keep Y's STAR
conclusion and omit X's exact obligation. This is a valid DEMAND-edge
subsumption. Each resulting late concrete initial is EXACT at that same head.
The actual submitted fact need not itself be EXACT.

The earlier raw-transfer trace distinguishes STAR from EXACT during direct
application. That trace does not refute this handoff-only deletion. It still
prevents lifting this proof to arbitrary NORMAL replay. See
[DS-POINT](bidirectional-demand-edge-redundancy-patterns.md#ds-point-same-head-concrete-exactstar-demand-conclusions-b2).

Proof: [concrete point queries](../../spec/concrete-point-demand-queries.md).

### Executable keys

These are comparison keys, not fact rewrites:

```text
entryKey(e):
    if e is a supported legal full-concrete STAR/EXACT point:
        return copy(e, tail=EXACT, E=empty)
    return e                         # includes its typed kind

outputKey(o):
    if o is DATA and o.tail == MAY and o.E == empty:
        return copy(o, tail=STAR)
    return o

queryKey(q) = (full owner/ports, entryKey(q.entry), outputKey(q.output))
```

Do not erase other exclusions or canonicalize MUST into STAR. Keep full
marks, typed controls and literal protection on the unchanged raw state.

## 3. Split admission and output coverage (earlier C1)

```text
C2Check(q,z):
    same complete C2 owner and physical entry
    entryKey(q.entry) == entryKey(z.entry)

C5Check(q,y):
    same complete owner, physical exit and typed output kind
    outputKey(q.output) == outputKey(y.output)
    entryKey(q.entry) == entryKey(y.entry)
        or PointMayImageContains(y.entry, q.entry)
```

For the point-to-MAY adapter, q has a legal full-concrete point entry.
Y has the same base/full mark and an empty-E MAY entry. Its path equals q's
path or is its prefix with suffix `CLASS* ++ c`, where c is one FIELD or
ELEMENT and is the first counted extension. Supported bases are This,
Argument, Return and LocalVar. Exclude static and Exception adapters.

**State after i+2:**

| Current summary | G `(entry; output)` |
| --- | --- |
| X: `b.*/U → a.f.$/T` | qX = `(a.f.$/T; b.*/U)` |
| Z: `c.*/U → a.f.$/T` | qZ = `(a.f.$/T; c.*/U)` |
| Y: `b.*/U → a.MAY/T` | qY = `(a.MAY/T; b.*/U)` |

```text
Keep Z and Y.
C2Check(qX,qZ): same exact entry; outputs may differ.
C5Check(qX,qY): same output; f is the first counted extension.
```

Z is required by this sufficient certificate. On the symbolic offer
`a.f.*/T, DEMAND`, the native operators return:

```text
C2(qX): a.f.$/T, DEMAND
C2(qY): a.f.*/T, DEMAND
        a.f.*/FLOW, NORMAL
        a.$/FLOW, NORMAL
```

The exact initial is absent from qY's family, although both C5 entries
accept that stored exact point. This does not prove Z necessary for every
sound design, or prove a lost sink. A Y-only rule needs a new proof about
the different initial families. That generalization remains open.

For the proposed DEMAND-only rule, Y need not give a stronger definite
postcondition. It gives a less restrictive permitted-refinement set. Thus
`a.MAY/T` semantically covers the exact f obligation. The missing proof is
that current admission/restriction and later iterations simulate the required
fine flows without Z. It is not a proof that the abstract inclusion fails.
See [DS-COVER](bidirectional-demand-edge-redundancy-patterns.md#ds-cover-proposed-conclusion-coverage-rule-c1-generalization).

## 4. Complete-origin coverage (earlier C2)

An origin is a complete outgoing edge membership, not one projected row.
Preserve all ND members, current layers/protection, owners and physical ports.

```text
checkCut(O, rows, R, certificates):
    require rows == {X: G(X) for X in frozen O}
    require R is a subset of O
    K = O - R
    for X in R:
        require rows[X] is complete and nonempty
        for q in rows[X]:
            (Z,z), (Y,y) = certificates[X,q]
            require Z in K and z in rows[Z]
            require Y in K and y in rows[Y]
            require C2Check(q,z) and C5Check(q,y)
    return SAFE_GUIDANCE_CUT
```

**State after i+2:**

```text
X: {b.*/U,c.*/U} → a.f.$/T
Y: b.*/U → a.MAY/T
Z: c.*/U → a.f.$/T

G(X) = {q1=(a.f.$/T; b.*/U), q2=(a.f.$/T; c.*/U)}
G(Y) = {y =(a.MAY/T; b.*/U)}
G(Z) = {z =(a.f.$/T; c.*/U)}

Remove only X's guidance:
  q1: C2 witness Z/z; C5 witness Y/y.
  q2: C2 witness Z/z; C5 witness Z/z.
```

Every projected ND row remains serviced. Keep the raw ND summary and its
AND execution. This certificate does not prove arbitrary raw ND deletion
or an intersection-based inference from unary conclusions.

The general retained-service proof establishes complete C2/C5 oracle equality,
including precision/owner/port support, for all later finite continuations.
Future inputs are quantified proof variables, not pattern inputs.

Proofs: [service basis](../../spec/retained-demand-service-basis.md),
[individual service cover](../../spec/individual-retained-query-service-cover.md).
The [query basis](../../spec/retained-demand-query-basis.md) is its earlier
whole-row case. All witnesses must end at actual final retained origins.

## 5. Individual verdicts and a joint basis

```math
IndividualRedundant(X) := checkCut(O,rows,{X},certificateX)
JointSafe(R)           := checkCut(O,rows,R,jointCertificates)
```

**State after i+2:** use D1a's two current origins:

```text
G(A) = G(B) = {q}; O={A,B}.
Individual cut {A}: K={B}; safe.
Individual cut {B}: K={A}; safe.
Joint cut {A,B}:    K={};  fails.
Joint cut {A}:     K={B}; safe; B is still individually redundant.
```

This is a selection constraint, not another subsumption theorem. The symmetric
demand classification does not equate the raw MUST and MAY postconditions.
Prefer a stronger native representative where a separate validated native
rule permits that choice. Recheck every certificate when its witness leaves K.

## 6. Handoff order (earlier C3)

C3 is a procedure. The main review gives its
[complete worked handoff state](bidirectional-demand-edge-redundancy-patterns.md#6-handoff-procedure-and-the-missing-c3-example),
including NORMAL and DEMAND rows and both compacted results.

```text
O = snapshot all current outgoing origins
rows = project every origin now
find individual certificates against O minus only X
select a joint cut R and certificates against the same final K=O-R
require checkCut(O,rows,R,certificates)
build next demand from rows of K
preserve ordinary NORMAL persistence, seeds and NormalTargets
compute demand counts and the ordinary stop decision
only then start the next run
```

Selection and witness lookup use finite current row indexes. They do not
execute a future C2 query or wait for a future provider. The safe selected
cut need not be maximal. Hashes are indexes; compare full decoded values.

## 7. Results and limits

The accepted publication has 8,915 individual redundant origins and a
separate 6,955-origin joint plan; 19,716 targets remain unresolved.
Those are guidance classifications, not saved-record deletion counts.
Latest reached/completed/accepted forward: OWASP run-11/11/11,
Conductor run-8/7/7, Stirling-PDF run-11/10/9.

The handoff-state audit checked 20,256 individual and 16,168 joint witness
memberships in the original removal-barrier snapshots. No later witness
is used. No new classification or production filter is installed.
The campaign's source/CFG/report/hard-cutoff patterns remain withdrawn.

Large proof/corpus data remains external; see the
[archive guide](../reports/EXTERNAL_DATA.md). The
[bounded review model](../../spec/lean/proposals/handoff-subsumption-review-20261112/RelationAndQuery.lean)
and [native controls](../../spec/lean/proposals/handoff-subsumption-review-20261112/native-receipt.json)
confirm the raw-versus-query distinctions, not a new general native compactor.
