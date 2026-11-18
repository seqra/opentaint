# Demand progress and proved retirement

The [relational loss-evidence proposal](bidirectional-relational-loss-evidence-proposal-20261113.md)
is **withdrawn**: full cross-call evidence composition recreates analysis
outside the field abstraction. The normal-return identities and selected
progress requirements below remain useful, but the full-evidence planner
and retirement workflow are not an accepted bounded algorithm. A replacement
must preserve the abstraction at method and block-summary boundaries.

13 November 2026. Design investigation under
[proof-guide.md](../../spec/proof-guide.md). The field-ban candidates are
retired. Production, C2/C5 and the selected non-empty-MAY spec are unchanged.

## 1. Selected correctness target

Each new forward iteration must advance effective precision. If refinement
continues indefinitely, a finding must not remain supported forever only
by the same unresolved approximation. A repeated demand can leave the
refinement frontier only with a redundancy proof. Provisional completion
and the temporary run-11 limit are not substitutes for that proof.

Here “precise” is relative to the analyzer's full-field AP semantics. This
does not remove the analyzer's separately accepted path/alias/ND false
positives or redefine NORMAL witnesses as concrete JVM executions.

The progress measure must describe the unresolved question, not just the
iteration number, global field limit or number of demand records. Demand
counts can grow while a finer question replaces a coarse one.

Two conditions are needed:

```text
Progress:
    every launched forward round resolves an outstanding question,
    splits one into strictly finer questions, or proves it redundant.

Fairness:
    every persistent unresolved question is eventually selected again;
    unrelated progress cannot starve it.
```

These are requirements for the next design, not properties already proved
for the current analyzer. “New key processed” alone is not semantic progress.

## 2. The acyclic example has two different losses

Use the [two-call program](../reports/bidirectional-non-empty-may-acyclic-nontermination-20261113.md)
and its [BB retrace](../reports/bidirectional-non-empty-may-basic-block-retrace-20261113.md):

```java
Box choose(Box p, boolean flag) {
    if (flag) return p.f.g;
    Box q = new Box();
    q.f = p;
    return q;
}
```

Once inferred, its two complete NORMAL return relations are:

```text
R: p.f.g.* / FLOW -> ret.* / FLOW
W: p.*     / FLOW -> ret.f.* / FLOW
```

The method-only trace keeps:

```text
forward:  p.*   -> ret.MAY, DEMAND
backward: ret.* -> p.MAY,   DEMAND
```

The first route loses the input-suffix condition when reading from STAR.
No field is cut on that repeating route. Raising the cut limit alone cannot
remove it. The backward NORMAL reader R is available by run-4 in the trace;
its presence still does not cancel the lossy query.

In the BB trace a second source remains after the local reader is precise:

```text
NORMAL W applied to p.f.MUST -> ret.f.f.MUST, NORMAL
method C5 with Dp=ret.*     -> ret.f.NE, DEMAND
next call admits p.f.*     -> saved opposite R produces ret.MAY, DEMAND
```

The method's paired budget is always `FL(Dp)+1 = 1`, regardless of the
larger global limit. The same known NORMAL transfer is re-cut forever.
Both losses need to be addressed; a new tail alone does not do so.

## 3. Prove redundancy against retained NORMAL derivations

The proposed direction is to retain the exact NORMAL derivation as the
provider and retire its redundant refinement work. Do not delete a coarse
edge merely because another edge has a similar head.

### 3.1 Recognize covered NORMAL work before it becomes a cut demand

For example, W already covers this raw NORMAL specialization:

```text
saved W: p.*   -> ret.f.*
raw L:   p.f.* -> ret.f.f.*

input p.f.suffix:
    W produces ret.f.f.suffix
    L produces ret.f.f.suffix
```

After C5 cuts L to `ret.f.NE`, the suffix equality is no longer present in
its public shape. Comparing only that shape with W cannot recover the
proof. The raw NORMAL candidate therefore needs its cover check before
the cut, or a finite cut witness that permits the same check at handoff.
This is a use for truncation evidence without banning any field or input.

The proposal does not propagate or persist an unrestricted candidate.
The provider must be a legally retained NORMAL record. Rule observations
already made on the in-block edge remain. Native C2/C5 service equivalence,
source/Target handling, protection and both provider arrival orders still
need proof before this becomes an implementation rule.

### 3.2 Preserve the guard behind an unknown-read loss

The coarse forward MAY from `return p.f.g` is backed by the exact relation
R. A precise result through that branch has the form:

```text
input:  p.f.g.suffix
output: ret.suffix
```

R already represents every such result, including future longer suffixes.
The backward coarse MAY from the writer has the corresponding W witness.
Once those origins are covered, repeatedly increasing the limit for the
same coarse projection adds no precise return relation for this body.

This is **derivation coverage**, not the invalid claim that two NORMAL
relations contain every point pair admitted by `p.* -> ret.MAY`. That MAY
relation also contains spurious pairs. They need not survive refinement.

For this two-branch prefix body, the formal reference proves complete
coverage for every finite input point and every source/sink predicate.
For the real analyzer, a certificate must cover every origin of the
retired demand, including side effects and control observations. A sample
of observed results or the mere presence of R and W is not such a certificate.
Multiple origins collapsed into one edge need complete coverage of their
union. A retained witness cannot depend on another retired demand.

For the original source at `a.f.MUST/T`, exact replay is particularly clear:

```text
call 1 actual p.f.MUST/T:
    R -> b.MUST/T, NORMAL
    W -> b.f.f.MUST/T, NORMAL

call 2 actual b.MUST/T:
    R -> c.MUST/T, NORMAL
    W -> c.f.MUST/T, NORMAL

call 2 actual b.f.f.MUST/T:
    R -> no match: the known second f differs from g
    W -> c.f.f.f.MUST/T, NORMAL
```

Every result fits run-5's global limit 4. No actual call in this replay
needs a MAY loss. The MAY/NE side route is introduced by resummarizing
coarse queries, not by missing precision in the original source.

The corresponding joint retirement would work as follows in this prefix
reference. At the run-5 handoff, retain R, W, source records, NormalTargets
and root Target guidance. Retire the helper's DATA refinement obligations
only after all their intrinsic-read and cut origins have coverage witnesses.
Do not retire one coarse row while leaving an equivalent uncovered origin.

```java
// REFERENCE run-6, BACKWARD, limit 5.
// Main still has its Target/ZERO pair. Saved reverse W delivers a.MAY/T,D
// to the real source at a.f.MUST/T and renews source permission.
// choose publishes no fresh DATA demand: its current demand is empty.
Box choose(Box p, boolean flag) {
    if (flag) return p.f.g;
    Box q = new Box();
    q.f = p;
    return q;
}
// Submitted facts include ret.MAY/T,D; current initials: none.
// Saved R/W still apply before that empty-demand check, as usual.

// REFERENCE run-7, FORWARD, limit 6.
// Main demand: [Target ; ZERO]. Submitted/initial: ZERO,N.
void main(boolean flag) {
    Box a = sourceAtF();         // a.f.MUST/T,N.
    Box b = choose(a, flag);     // b.MUST/T,N; b.f.f.MUST/T,N.
    Box c = choose(b, flag);     // c.MUST/T,N; c.f.MUST/T,N;
                                // c.f.f.f.MUST/T,N.
    sinkAnywhere(c);            // NORMAL witnesses -> NormalTarget(id).
}
// No new DemandTarget in this reference replay.
// Helpers have no fresh DATA demand; the frontier becomes empty.
```

This trace uses the existing persisted-first call order and ignores no
actual offer. It does not require MUST to subsume MAY across layers,
change STAR admission, or promote a DEMAND edge to NORMAL. It removes
covered obligations before they can force another coarse query. The typed
actual replay is checked in Lean; the whole post-cut scheduling/Target
trace remains a native-test obligation, not a recorded execution.

### 3.3 Keep broad relay handling until its work is covered

The [wrapper example](../reports/bidirectional-handoff-promotion-ban-20261113.md)
still supplies an important regression:

```text
demand entries: ret.MAY and ret.f.MAY
actual offer:   ret.*
C2:            the first starts ret.*; the second emits nothing
```

The broader query must remain if it is the only route that can expose the
missing reader `p.h.* -> ret.f.*`. A NORMAL writer `p.* -> ret.f.*` has a
different suffix correlation and cannot certify that reader. Retain the
ordinary coarse relay while refining its unmet obligation upstream. Do not
turn “no current child initial” into a negative flow fact.

## 4. Refinement scheduling and closure

A prospective planner needs questions for both real cuts and unknown-read
losses. It must preserve the reason and the full paired scope rather than
only the lossy AP head. This is new analyzer bookkeeping; it is not an
additional taint mark, protection flag, field exclusion or fact identity.
Its storage and boundedness are not selected by this investigation.

```text
for each unresolved demand origin:
    if a finite certificate proves all its precise effects covered
       by independently retained state:
        retire that refinement obligation
    else:
        identify its next unresolved distinction
        schedule a strictly finer question, or subscribe to the
        upstream question that must expose the required input

launch the next forward round only for a nonempty refinement plan
finish only after every remaining obligation has a checked closure proof
```

A cycle in the demand-evolution graph is a place to search for a joint
closure invariant. Equality across two runs is not that invariant. The
certificate must cover legal future inputs, field limits, providers and
deliveries. No JVM-type assumption or next-run observation can be a handoff
predicate input. Extra loss evidence, if required, must be designed explicitly.

## 5. Unbounded depth is not an asymptotic-precision proof

Even fair field-depth growth does not by itself prove that every surviving
finding becomes precise. Consider two path languages:

```text
written paths: f^n.g, for n >= 0
read paths:    f^m.h, for m >= 0, with g != h
```

They are disjoint. At every finite depth k, however, choosing n=m=k+1
cuts both paths to `f^k.NE`. A false overlap can survive every depth even
though each individual finite pair is eventually separated. The confusing
pair simply moves deeper each time.

Thus “every fixed path eventually gets enough fields” is weaker than the
requested finding-level guarantee. For cyclic path families we need a
finite invariant over the whole family, such as a checked path-language
separation in an edge-composition graph. Observed NORMAL edges alone do
not establish completeness of that graph; open derivations must remain
explicit. This is a further proof direction, not an accepted generic
retirement predicate or a demonstrated native program run.

## 6. Checked scope and next proof gates

[Progress.lean](../../spec/lean/proposals/demand-progress-20261113/Progress.lean)
provides a finite acyclic prefix reference. Its structural evaluator has
no iteration fuel and preserves exactly its inductive reachability relation.
For the two-call example it has at most four results per input point.
It proves the NORMAL specialization identity, the lost correlation after
cutting, both existing unbounded cycle witnesses, and the disjoint-language
overlap at every finite cut depth. The actual MUST replay through both
calls is checked separately. The package passes **146 audited declarations
in seven modules**, including 21 new checks. Reproduce it with
`spec/lean/proposals/demand-progress-20261113/check.py --out <fresh external directory>`.
The receipt is `demand-progress-20261113/proofs-v5/receipt.json` under the
[external archive](../reports/EXTERNAL_DATA.md).

This establishes that finite exact NORMAL replay can serve as a retirement
witness in the declared prefix scope. It does not establish a native
C2/C5 deletion predicate, prove a termination theorem for the whole core,
or certify arbitrary methods from a finite history. The reference excludes
rules, aliases, exclusions, ND and native control routing. It treats branch
choices as the AP model's nondeterministic union.

Next, prove one native retirement rule for the covered raw NORMAL cut,
then the complete-origin rule for the intrinsic reader. Re-run the original
and BB cases uncapped, plus the retained-child wrapper and delayed-finding
regressions. Each rule needs a joint retained basis and arrival-order checks.
General cyclic termination requires the stronger family invariant above.

No project was scanned. The model reproduces the existing run-5 onward
cycle witnesses and computes a finite reference, not new engine timings.
Historical reached/completed/accepted forward positions remain OWASP
**run-11/11/11**, Conductor **run-8/7/7**, Stirling-PDF **run-11/10/9**.
