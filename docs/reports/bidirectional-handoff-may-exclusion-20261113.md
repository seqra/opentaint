# Handoff MAY exclusion: the child boundary must remain covered

13 November 2026. Candidate investigation. No production or canonical spec
change. Follow [the proof guide](../../spec/proof-guide.md).

**The general rule is not sound as stated.** A child `a.f.NE` does not cover
the exact point `a.f.$`. Removing the whole f branch from the broad MAY
demand can therefore remove all admission for a real sink requirement.

The later [NORMAL-only variant](bidirectional-handoff-normal-summary-exclusions-20261113.md)
uses a genuine NORMAL child and includes saved replay. NORMAL status alone
still does not establish complete field-branch coverage.

The latest [STAR-only update](bidirectional-handoff-star-only-exclusions-20261113.md)
preserves direct concrete refinements, so this document's whole-branch
rejection is no longer its policy. The updated trace tests a coarse STAR
offer delivered through a wrapper instead.

## 1. Clarified candidate

For the same complete original X, the user selected this meaning:

```text
before: X -> a.MAY
        X -> a.f.NE

after:  X -> a.MAY with f excluded from its admission region
        X -> a.f.NE, still active
```

The previous premise X is unchanged. The exclusion is anchored at a, not
at a.f. A STAR initial selected at a inherits `{f}`. A submitted fact
strictly below a through f is rejected by the broad selector; copying `{f}`
to an initial already at a.f would instead exclude a.f.f, a different region.

This requires new demand-admission behavior: current loss-created MAY
selectors have Empty E. For this investigation the candidate has an explicit
exclusion guard before ordinary C2. The existing rule remains: a failed
primary admission emits no companion or conditional FLOW prefix probe.
We do not invent a new probe permission to repair the candidate.

All examples use matching marks, support classes, owners, ports and H=false.
The concrete counterexample below uses two DEMAND conclusions, so a new
restriction to DEMAND rows alone does not close the gap.

## 2. The uncovered C2 cell

```text
Previous same-premise rows:
    ret.*/FLOW -> p.MAY/FLOW, D
    ret.*/FLOW -> p.f.NE/FLOW, D

Next submitted fact:
    p.f.$/T, NORMAL
```

| Selector | Initial emission |
| --- | --- |
| Original p.MAY/FLOW | p.f.$/FLOW,N and conditional p.$/FLOW,N |
| Broad p.MAY/FLOW with f excluded | none: descent through f is excluded |
| Retained p.f.NE/FLOW | none: EXACT at the same head has no nonempty suffix |

The union of the two new families is empty. Keeping the child NE demand
does not preserve the missing point.

Spatially, for suffix alphabet Sigma:

```text
a.MAY                     = a.Sigma*
a.MAY with f excluded     = a.{epsilon or a suffix not starting with f}
a.f.NE                    = a.f.Sigma+

a.f.$ belongs to the old region and neither new region.
```

This proves a local admission loss. The next section shows that the missing
point can be a real required flow, rather than a removable approximation.

For the previous cycle's next **forward** admission at p, the same rewrite
has these effects:

| Submitted at p.f | Broad demand with f excluded | Separate p.f.NE demand |
| --- | --- | --- |
| MUST/T,N | none | dedicated p.f.MUST/FLOW,N |
| NE/T,D | none | p.f.STAR/FLOW,N |
| EXACT/T,N | none | none |

Thus it improves the uniform-source admission in that example, but an
uncertain NE offer can still reopen STAR without naming a new field. The
exact-point row is the soundness gap that must be closed before treating
the rewrite as a general handoff rule. No whole-cycle termination result
is claimed for this partial candidate.

## 3. Loop-free code that needs the missing admission

```java
class Box { Box f; Box g; Box h; }

void main(boolean flag) {
    Box a = sourceAtG();         // Source: T at a.g and ALL its descendants.
    Box r = choose(a, flag);
    sinkExact(r.f);              // Sink: exact T at r.f.$.
}

Box choose(Box p, boolean flag) {
    if (flag) {
        return p.g;
    } else {
        Box u = new Box();
        u.h = p;
        Box q = new Box();
        q.f = u;
        return q;
    }
}
```

FULL mode, aliases disabled, Empty E/mx and H=false. The two writes in the
false branch transport the fact through u.h and q.f.h without alias inference.
`sourceAtG` and `sinkExact` are external configured rule APIs. They are not
hidden analyzed loops or predefined summaries.

The true branch returns a.g. The source marks all descendants of a.g,
including a.g.f. Thus `sinkExact(r.f)` is a real finding on that branch.
The false branch instead transports this source below r.f.h.g; it does
not mark the exact object r.f.

The counterexample works at method-level handoff, including when BB
summarization is enabled: the method admission can reject the offer before
any child BB can answer it.

## 4. Run-1: both rows are derived from code

```java
// MAIN: no demand; submitted ZERO,N; initial ZERO,N.
void main(boolean flag) {
    Box a = sourceAtG();         // a.g.MUST/T,N; field g fits limit 1.
    Box r = choose(a, flag);     // Coarse return supplies r.MAY/T,D.
    sinkExact(r.f);              // Candidate exact check -> DemandTarget,D.
}
// MAIN published: ZERO -> DemandTarget,D; no NORMAL report for this path.

// CHOOSE: unrestricted run-1, field limit 1.
// Submitted p.g.MUST/T,N; abstract initial p.*/FLOW,N.
// Ordinary mark requests supply the corresponding concrete T query.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.g;             // p.* -> ret.MAY/FLOW,D.
    } else {
        Box u = new Box();
        u.h = p;                // p.* -> u.h.*/FLOW,N.
        Box q = new Box();
        q.f = u;                // q.f.h.*/FLOW,N exceeds limit 1.
                                // It becomes q.f.NE/FLOW,D.
        return q;
    }
}
// Return candidates with the SAME original X=p.*/FLOW:
//     X -> ret.MAY/FLOW,D
//     X -> ret.f.NE/FLOW,D
// No NORMAL DATA return provider exists for this run-1 abstraction.
```

Existing MAY canonicalization normally removes the child NE row. The
candidate needs the child available before that removal. We grant it both
rows, as requested; the counterexample does not rely on the current storage
having already erased the child.

After the candidate handoff, next-run selectors are:

```text
[ret.MAY/FLOW excluding f ; p.*/FLOW]
[ret.f.NE/FLOW             ; p.*/FLOW]
```

## 5. Run-2: backward admission becomes empty

```java
// MAIN: the necessary DATA route produces no source completion.
void main(boolean flag) {
    Box a = sourceAtG();         // No related DATA requirement arrives here.
    Box r = choose(a, flag);     // Submitted to choose: ret.f.$/T,N.
                                // Saved DATA return providers: none.
                                // Candidate C2 union: EMPTY.
    sinkExact(r.f);              // Reverse seed: r.f.$/T,N.
}
// MAIN incoming [Target ; ZERO]; submitted ZERO,N; initial ZERO,N.

// CHOOSE: no new DATA summary or NORMAL read provider is published.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.g;             // Required backward read is never visited.
    } else {
        Box u = new Box();
        u.h = p;
        Box q = new Box();
        q.f = u;
        return q;
    }
}
// Incoming pairs:
//   [ret.MAY/FLOW excluding f ; p.*/FLOW]
//   [ret.f.NE/FLOW            ; p.*/FLOW]
// Submitted ret.f.$/T,N; emitted initials: NONE from either pair.
```

Unrelated ZERO completions and unchanged-parameter identities do not satisfy
this return-base DATA requirement. Choose has no local source or sink that
could independently recreate it. Under the selected unanswered-demand rule,
failure to admit an initial causes no special continuation.

## 6. The original admission preserves the real finding

Without the exclusion rewrite, run-2 uses the broad MAY pair:

```java
// Published NORMAL: ret.*/FLOW -> p.g.*/FLOW,N.
// Also possible: ret.f.*/FLOW -> p.g.NE/FLOW,D after the actual child cut.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.g;             // Raw structural probe ret.$/FLOW gives
                                // p.g.$/FLOW,N, wholly within limit 1.
    } else {
        Box u = new Box();
        u.h = p;
        Box q = new Box();
        q.f = u;
        return q;
    }
}
// Incoming [ret.MAY/FLOW ; p.*/FLOW].
// Submitted ret.f.$/T,N.
// Initials ret.f.$/FLOW,N AND conditional ret.$/FLOW,N.
// Complete FLOW normalization of the latter result publishes:
//     ret.* -> p.g.*, NORMAL.
```

The ordinary backward route also reaches the actual source region, so the
next forward source permission is valid. In run-3, persisted NORMAL replay
uses the read provider before current demand lookup:

```text
source actual:       p.g.MUST/T,N
saved opposite view: p.g.*/FLOW -> ret.*/FLOW,N
result:              ret.MUST/T,N
sink at ret.f.$/T:    satisfied with NORMAL support
```

The candidate loses this provider and its required source-to-sink route.
Additional iterations or a larger global limit do not reconstruct an
unanswered call permission on their own. The run-11 hard limit is not part
of the counterexample.

## 7. What must be proved before excluding f

The proposed optimization is a partition of the broad demand's service.
The mere existence of a positive child row is not an absence proof for the
other parts of that field branch.

At the spatial level the removed region is **all** `a.f.Sigma*`:

| Child output | What remains uncovered by that shape alone |
| --- | --- |
| a.f.NE | a.f.$ |
| a.f.$ | descendants such as a.f.h.$ |
| a.f.h.MAY | a.f.$ and other child branches |
| a.f.STAR | Correlated output is not an independently arbitrary suffix |
| a.f.MAY | Covers the complete spatial branch with compatible headers |

Even complete spatial coverage is not the entire operational proof. C2
families include conditional FLOW prefix probes, and paired C5 has row-local
budgets. A replacement must preserve required analysis/saved-summary service,
support, full marks, exclusions, flags and physical ports. In particular,
admitting a narrow point alone does not recreate the old coarse prefix probe.

For the selected `ret.* -> p.MAY` plus `ret.* -> p.f.NE` case, the precise
missing piece is the f boundary point. One could investigate preserving
point permission as well as the NE region, or a full child MAY selector.
Neither repair is silently added or claimed proved here.

## 8. Constructive checks

[Exclusion.lean](../../spec/lean/proposals/handoff-may-exclusion-20261113/Exclusion.lean)
checks the missing-region witness, ordinary read/write derivation of the
two same-premise rows, complete C2 rejection union, the original structural
probe's NORMAL C5 provider, and its real uniform source application. It
imports the selected C2/C5 reference and prefix transfers. This is a scalar
specification counterexample, not execution of a production new-tail core.
The code/Target embedding is traced above; the model does not implement the
whole driver, BB decomposition or actor queues.

```sh
python3 spec/lean/proposals/handoff-may-exclusion-20261113/check.py \
    --out /tmp/handoff-may-exclusion-check
```

Result: **PASS, 6 modules, 119 audited declarations**, including 19 new
checks and 100 dependency checks. The external receipt is
`handoff-may-exclusion-20261113/proofs-v2/receipt.json` under the
[report data archive](EXTERNAL_DATA.md).

No project scan was run. The model trace reaches run-2 for the rejected
route and run-3 for the original NORMAL finding. Historical project latest
reached/completed/accepted-forward positions remain OWASP **run-11/11/11**,
Conductor **run-8/7/7**, Stirling-PDF **run-11/10/9**.
