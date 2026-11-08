# Descendant output intersection and FLOW demand completion

7 November 2026. Design review only. No analyzer implementation change or
new project run. Follow [proof-guide.md](proof-guide.md). Use the
[combined spec](edge-subsumption-initial-emission-demand-intersection.md)
and its pinned pre-implementation baseline.

## 1. The proposed descendant rule

Suppose the output selector d has a strictly longer path than current
conclusion c. Check the base, mark overlap and excluded first field first.

| c tail | Operation in the question | Difference from the current spec |
| --- | --- | --- |
| ANY | Rebase ANY to d.path, then intersect with d.tail | None |
| MUST | Rebase MUST to d.path, then intersect with d.tail | None |
| EXACT | Reject | None |
| STAR | Reject | Removes the correlated-STAR result retained by C5 |

The MAY/MUST cases keep the supplied mark, support and H. Rebasing under an
excluded branch still rejects. A MUST rebased under concrete EXACT becomes
EXACT. Under STAR it keeps MUST and the selector's applicable exclusions.
An ANY result selected by EXACT stays DEMAND. A concrete selector does not
turn FLOW into a full mark.

The changed STAR case has a nonempty requested relation. For example:

```text
Current NORMAL relation: p.f.f.* / FLOW -> ret.* / FLOW
Output selector:         ret.f.* / FLOW
Executable suffix:       tau = f
Concrete pair:           p.f.f.f.$ / T -> ret.f.$ / T
```

Keeping STAR preserves this suffix relation. Moving only the conclusion to
`ret.f.*` would lose the correlation; rejecting it removes the displayed
pair. C2's rejection of an ordinary STAR actual above a deeper initial
demand is a separate operation. It does not prove that this current summary
has no useful suffix.

## 2. A real two-read body, with no saved NORMAL return provider

Use these two rules:

```text
sourceFFF(b): true -> assign exact T at b.f.f.f
sinkT(v): CM(v.$,T)
```

The source action executes at its caller instruction. It is not a separate
saved source-return summary. All constructors are clean. b and r are method
locals and are dead at main's exit. This prevents an unused marked argument
from creating an unrelated public DATA frontier.

```java
void main() {
    Node b = new Node();
    b.f = new Node();
    b.f.f = new Node();
    b.f.f.f = new Node();
    sourceFFF(b);
    Node r = getFF(b);
    sinkT(r.f);
}
Node getFF(Node p) {
    return p.f.f;
}
```

Write each getter demand as `(Dc,Dp)`. The trace below first uses the current
C5 rule, with completion disabled. Limits are `1,1,2,3,4`.

```java
// Run-1, forward, limit 1.
// Submitted: p.f.ANY/T,D, from the real source cut.
// Initial: p.*/FLOW,N, from ordinary run-1 abstraction.
Node getFF(Node p) {
    return p.f.f; // First root read gives ret.ANY/FLOW,D; second stays ANY.
}
// Return summary: p.*/FLOW -> ret.ANY/FLOW,D.
// No NORMAL return provider. Any requested-T diagonal has the same D image.
// Separate unchanged-argument summary: p.*/FLOW -> p.*/FLOW,N.

// Run-2, backward, limit 1.
// Demand: (ret.ANY/FLOW,p.*/FLOW), from that real return summary.
// Submitted: ret.f.$/T,N, from backward sinkT(r.f).
// Initial: ret.f.*/FLOW,N.
Node getFF(Node p) {
    return p.f.f; // Reverse reads prepend f,f; global cap yields p.f.ANY/FLOW,D.
}
// Return relation in backward direction:
//   ret.f.*/FLOW -> p.f.ANY/FLOW,D.
// No NORMAL relation from ret to p. The argument identity cannot read ret.

// Run-3, forward, limit 2.
// Demand: (p.f.ANY/FLOW,ret.f.*/FLOW), from the run-2 result.
// Submitted: p.f.f.ANY/T,D, from the same real source cut at limit 2.
// Initial: p.f.f.*/FLOW,N.
Node getFF(Node p) {
    return p.f.f; // Strip both known fields: ret.*/FLOW,N.
}
// Before C5: p.f.f.*/FLOW -> ret.*/FLOW,N.
// Current C5 keeps this correlated relation and saves it.
// Proposed STAR rejection removes it: ret.f strictly extends ret.

// Run-4, backward, limit 3, under the current C5 route.
// Submitted: ret.f.$/T,N, from the sink.
Node getFF(Node p) {
    return p.f.f; // Apply the saved opposite NORMAL relation first.
}
// Caller result: p.f.f.f.$/T,N. It reaches the real source action.
// That source occurrence is permitted for run-5; no invented FLOW source hit.

// Run-5, forward, limit 4, under the current C5 route.
// Submitted: p.f.f.f.$/T,N. Source depth 3 now fits the limit.
Node getFF(Node p) {
    return p.f.f; // Apply the saved NORMAL relation first.
}
// Caller result: ret.f.$/T,N; sinkT(r.f) has a NORMAL witness.
```

The missing relation is produced by two ordinary reads. It is not an id
summary assumed absent after run-1. At run-3 there is no more precise input
which can replace it: limit 2 represents the source as p.f.f.ANY/T.

The unchanged-argument summaries remain in the model. They return facts on
p, not ret. In main they preserve b and cannot supply r.f or the sink.
They must not be silently renamed to return facts.

### 2.1 Interaction with completion

Completion adds a root-p FLOW/ANY self permission. The same run-3 actual can
then select an additional coarser `p.f.*/FLOW,N` initial. Two reads produce
`ret.ANY/FLOW,D`. The original complete demand row, not a mixed pair, admits
this candidate and rebases it to `ret.f.ANY/FLOW,D`.

```text
Run-3 extra bridge: p.f.*/FLOW -> ret.f.ANY/FLOW,D
Run-4 reverse input: ret.f.$/T,N
Run-4 inferred: ret.f.*/FLOW -> p.f.f.ANY/FLOW,D
    The paired output head is p.f, so FL+1 cuts at depth 2.
Run-5 input: p.f.f.f.$/T,N
Run-5 initial: p.f.f.f.*/FLOW,N
Run-5 inferred: p.f.f.f.*/FLOW -> ret.f.*/FLOW,N
```

Thus the proposed STAR rejection and completion must be evaluated together.
Under STAR rejection, the extra bridge can preserve a route which the
principal NORMAL candidate no longer supplies. Under the current STAR rule,
this example does not require completion.

Completion can also produce argument-output demand rows. Keep them in the
full catalog. A return-route proof is not a proof that those extra demands
terminate naturally or that completion has no workload cost.

### 2.2 The missing coarse run-2 analysis

The run-2 trace starts only `ret.f.*/FLOW`. It never starts `ret.*/FLOW`.
The submitted fact is `ret.f.$/T`; current C2 keeps its first concrete field
under the `ret.ANY/FLOW` demand. There is no additional root command.

This identifies another repair. If run-2 also analyzes a coarse NORMAL
`ret.*/FLOW` identity, its two reverse reads and global limit 1 produce:

```text
Additional run-2 summary:
    ret.*/FLOW -> p.f.ANY/FLOW, DEMAND

Additional run-3 demand pair:
    (p.f.ANY/FLOW, ret.*/FLOW)

Run-3 submitted: p.f.f.ANY/T,D
Run-3 initial:   p.f.f.*/FLOW,N
Run-3 result:    p.f.f.*/FLOW -> ret.*/FLOW,N
```

The output now has the same head as its paired selector. It passes the
proposed STAR-rejection rule, without completion or a STAR-ancestor output
case. Its saved opposite reaches the real source in run-4; saved forward
application produces the NORMAL sink witness in run-5.

`GetFFCoarseFlowRun2` checks that alternative separately. The coarse start
passes the existing constructive C5 image test, but current C2 does not emit
it for this actual offer. Adding it is an initial-admission policy change.
This review does not silently replace the current emitter or define a
general prefix-admission policy.

Thus E30 proves a gap in the combination of current C2 and STAR rejection.
It does not prove that retaining the STAR output case is the only repair.
This alternative addresses E30; it does not settle E21's loop gate.

### 2.3 Selected emission: keep the prefix probe EXACT during execution

The selected addition is more precise than starting a live coarse STAR.
For an ANY demand which successfully admits a strictly deeper actual, retain
the primary and also start an EXACT/FLOW identity at the demand prefix.

```text
Demand:          ret.ANY/FLOW
Submitted:       ret.f.$/T,N
Run-2 commands:  ret.f.*/FLOW,N             // existing primary
                 ret.$/FLOW,N               // new prefix companion

Raw companion result: ret.$/FLOW -> p.f.ANY/FLOW,D
Stored FLOW summary:  ret.*/FLOW -> p.f.ANY/FLOW,D
Run-3 output demand:  ret.*/FLOW
```

`GetFFExactFlowPrefix` derives the actual extra command and its summary.
The updated emitter then infers the run-3 NORMAL getter even under the
reviewed STAR-rejection rule, with completion disabled. Its actual backward
source check permits run-3; saved replay later permits run-5 and finds the
NORMAL sink. All argument/return candidates are still checked.

The exact prefix does not replace the field-specific initial. Forward
`p.f.$/FLOW` cannot read `p.f.f`; the existing descendant primary supplies
that route. Exact tails become STAR only at complete FLOW summary admission.
Strong-write E, cleaner mx and ANY/DEMAND residuals keep their existing laws.
This changes C2 admission, not field transfer.

The raw C2 image grows for concrete ANY demands. Its normalized C5 image
does not: the public prefix STAR/FLOW key already has an executable old
root-STAR or concrete-STAR-companion witness. The generic companion proof
checks this equivalence; no new paired-output permission is added.

## 3. A counterexample to removing all completion under the current loop gate

**8 November correction:** the catalogs below compute one-body transactions
over a bounded input universe. They do not close saved-first loop delivery.
The [corrected repeat trace](subsumption-loop-and-gap-audit-20261108.md#24-run-4-backward-field-limit-3-close-saved-replay-first)
does reach ANY in run-4. It separates parent completion from local summary
publication. The old five-row handoff and shorter run-5 source image are
not proved reached; their off/on gate calculations remain conditional on
the supplied rows. Do not cite this section as a full program fixed-point
or convergence proof.

Keep the current C5 STAR behavior for this comparison. The example is E21:

```java
// x has enough initialized f descendants for the first four traversals.
// sourceFFFF: true -> assign exact T at x.f.f.f.f.
// sinkT: CM(arg0.$,T).
void deep(Node x) {
    BL: { }
    L: while (true) {
        sourceFFFF(x);
        x = x.f;
        sinkT(x);
    }
    AL: { } // No physical forward leave.
}
```

The first source's T reaches x after four traversals. Each traversal moves x
one field forward. Later source calls do not remove that T.

The issue is not absence of a saved NORMAL shrinker. Run-3 derives
`x.f.* / FLOW -> x.* / FLOW`, NORMAL, without completion. The issue is that
the loop gate can drop the source fact before it is offered to that saved
summary on the next traversal.

### 3.1 All reference families, not an assumed three-row snapshot

The closed model generates raw candidates from the source/read/sink body,
latest C2, all complete C5 pairs and handoff. It keeps projected EXACT
source results as well as MAY results. It assumes no new cross-tail pruning.

Write `x` for the empty path and `F` for FLOW. All rows have Empty E/mx and
H=false. Reach is ZERO control; Target in these tables is DemandTarget.
Rows describe one compatible repeat interface and its typed control view.
Native first-entry, repeat, discovery and logical Target ports are a separate
adapter. These tables do not authorize merging those ports.

| Run | Retained reference summary families without completion |
| --- | --- |
| run-1 | `ZERO -> Reach,N`; `ZERO -> x.ANY/T,D`; `ZERO -> Target,D`; `x.*/F -> x.ANY/F,D`; `x.*/T -> Target,D` |
| run-2 | `ZERO -> Reach,N`; `ZERO -> x.f.$/T,N`; `x.f.*/F -> x.f.ANY/F,D`; `x.f.$/T -> Reach,D`; `x.f.$/T -> Target,D`; `x.f.*/T -> Reach,D`; `x.f.*/T -> Target,D` |
| run-3 | `ZERO -> Reach,N`; `ZERO -> x.f.ANY/T,D`; `ZERO -> x.f.$/T,D`; `x.f.*/F -> x.*/F,N`; `x.f.$/T -> Target,D` |
| run-4 | `ZERO -> x.f.$/T,N`; `x.f.*/T -> Reach,D`; `x.f.*/T -> Target,D`; `x.f.f.*/T -> Reach,D`; `x.f.f.*/T -> Target,D` |

This table uses the emitter before §2.3's exact prefix companion. The new
`E21PrefixExactCompanion` model recomputes every family with the selected
emitter. Run-2 gains NORMAL `x.*/FLOW -> x.f.*/FLOW`; it is saved but does
not enter demand handoff. Run-3, run-4 and the complete run-5 demand view are
unchanged. In run-4 the new raw exact FLOW prefix can produce a NORMAL DATA
candidate, but every complete paired ZERO exit rejects it. This is not a
raw candidate which can be saved before C5.

The loop counterexample therefore still applies with the selected exact
companion. Another saved shrinking summary cannot process a fact which the
earlier gate has dropped. The new model checks every admitted source image
and every new run-4 prefix body, rather than assuming the old result.

In run-1, the real plain FLOW/DEMAND row covers the requested plain T DATA
row. Its T Target still remains. There is no discarded T DATA row used as
extra run-2 guidance.

The run-2 sink seed is inside the ZERO actor. It passes through the backward
field read before reaching another loop-entry C2 call. Thus the boundary
fact is x.f.$/T, not x.$/T. A root FLOW transaction is not assumed reachable.

In run-3, every FLOW DATA result is NORMAL, even before canonicalization.
Every nonzero T Target has exact x.f.$/T as its original. Therefore no
FLOW/DEMAND DATA pair or T-STAR Target is added to run-4 by an omitted family.
These classification laws also hold for subsets of the raw families; the
argument does not assume that canonicalization of an upper bound preserves
all possible narrower native bases.

Run-4 DATA-entry pairs all have ZERO output selectors. A concrete STAR seed
can add its FLOW companion, but that same ZERO exit rejects the companion's
DATA result. The ZERO actor can emit DATA only through the exact-f Target
selector. It cannot emit a longer DATA result through that selector.

Ownership matters: applying a body summary to a parent's ZERO-origin edge
does not turn the body original into ZERO. Repeat DATA delivery starts a
DATA initial. Reclassifying it as a local ZERO result would create different
demand families and would change the selected block ownership contract.

### 3.2 Run-5 without completion

Reversing all five run-4 rows gives this entire reference demand view:

```text
(x.f.$/T, ZERO)
(ZERO,   x.f.*/T)
(Target, x.f.*/T)
(ZERO,   x.f.f.*/T)
(Target, x.f.f.*/T)
```

The only DATA entry selector is exact x.f.$/T. Extra ZERO/Target control
entries cannot create a DATA initial from a DATA offer.

```text
Fresh source at limit 4:       x.f.f.f.f.$/T,N
After x=x.f:                  x.f.f.f.$/T,N
Current paired C5:            keeps that depth-3 result
Applied summary classification: ZERO -> depth 3 is growing

AL demand:                    no physical DATA consumer
Enclosing B exit:             typed control; rejects the DATA result
L DATA demand:                x.f.$/T rejects the deeper actual
FLOW companion:               none, because the primary rejects

Gate result:                  no image; drop before repeat delivery
Saved x.f.* -> x.*:            present, but the fact never reaches its input
```

The source's NORMAL result is real. Its C5 budget is 3 from the paired
x.f.f.* head, so it is not cut there. The loss occurs at the next loop gate.

### 3.3 Run-5 with endpoint self completion

The real run-4 source-Reach row has x.f.f.*/T as its original. Its reversed
ZERO row has that DATA endpoint. Completion derives the same-interface pair:

```text
(x.f.f.ANY/FLOW, x.f.f.ANY/FLOW)
```

This changes the repeat observation:

| Offered fact | C2 key from this pair |
| --- | --- |
| Raw `x.f.f.f.$/T,N` | `x.f.f.f.*/FLOW,N` |
| Cut `x.f.f.ANY/T,D` | `x.f.f.*/FLOW,N` |
| Cut `x.f.ANY/T,D` | `x.f.f.*/FLOW,N` |

Both proper cuts lose the fine key. The unchanged gate therefore keeps the
raw fact at budget 3. The real saved NORMAL shrinker can now act:

```text
x.f.f.f.$/T,N -> x.f.f.$/T,N -> x.f.$/T,N -> x.$/T,N
```

Shrinking applications bypass the growing-result gate. Saved replay runs
before current admission. The actual T at the root gives a NORMAL Target;
FLOW itself never satisfies CM(T) or invents a source permission.

This is a constructive counterexample under the reference ownership and
kept-gate contract: removing all completion loses the modeled run-5 finding.
It is not a new Kotlin/native failure receipt.

### 3.4 The shorter admitted source image does not repair the missing route

All complete C5 rows contribute. The same fresh source also produces
`ZERO -> x.f.f.ANY/T,D` through the shallower paired budget. The proof checks
both admitted images, rather than discarding this DEMAND piece:

```text
Without completion:
  x.f.f.f.$/T,N -> gate rejects
  x.f.f.ANY/T,D -> gate rejects
  all resulting Targets = empty

With completion:
  the precise NORMAL image reaches NormalTarget
  the shorter DEMAND image can still reach DemandTarget
```

Thus completion restores the finding in this model, but it does not prove
that refinement stops. The remaining DemandTarget still counts under the
selected stopping rule. This review does not add a rule which removes it.

## 4. What the evidence justifies

- With current C2, keep the correlated STAR branch or supply another
  refinement route. A coarse run-2 FLOW start supplies that route in E30.
  The MAY/MUST simplification already matches the existing rebasing rules.
- Under the current loop gate order, extra endpoint guidance is necessary
  in E21. The tested completion supplies it. Moving saved shrinking replay
  before the gate would be a different design and may remove this need.
- E21 proves the need for an endpoint self-permission in this design. It
  does not prove that paired-head FLOW erasure is necessary. The id example
  E28 cannot justify that part. The two-read alternative also uses self-pairs.
- The earlier E19 static interface can infer its NORMAL FLOW frame from the
  selected companion under the original T pair. Completion is not needed
  for that particular interface; a same-field write still kills both seeds.

Do not label the entire broad completion policy minimal or free of extra
demand. The examples justify the stated routes, not every generated selector.

## 5. Proof scope

The latest root check passed **1,015 local declarations**, including 59
added for the selected exact-prefix emitter and its principal routes. See the
[receipt](lean/proposals/subsumption-initial-demand-20261107/component-checks-1015.json),
[axiom audit](lean/proposals/subsumption-initial-demand-20261107/component-axioms-1015.txt)
and [proof package](lean/proposals/subsumption-initial-demand-20261107/README.md).

The portable proof package checks the descendant-policy comparison,
complete finite getFF catalogs, E19 companion control and E21 closed scalar
families. E21 includes pre-canonical classification/subset laws, separately
constructed real source/read witnesses, ownership separation and the same
gate with completion off/on. An additional check covers every admitted
run-5 source image. Its final demand is computed, not supplied.

The E21 grammar has one field, T/FLOW, Empty E/mx, no MUST, ND, aliases or
statics. Source/read/replay preserve that grammar. Its effective compatible
port view, enclosing-control reduction, source callbacks, root scheduling
and complete native loop observer still require correspondence checks.
No global soundness, convergence or project-performance claim follows.
