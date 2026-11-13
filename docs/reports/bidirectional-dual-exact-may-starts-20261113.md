# Dual exact and MAY starts

13 November 2026. Candidate investigation at
`374fa3c6f5f73b24ccca00fc829da8c83a322d3f`. No production change or campaign
continuation. Follow [the proof guide](../../spec/proof-guide.md).

The local checks support the proposed separation: an EXACT/FLOW probe
can infer a reusable NORMAL relation, while a MAY start keeps uncertain
delivery. Six native AP tests and eleven constructive Lean declarations
pass. A complete engine policy and handoff-subsumption proof are not yet
provided. The current store does not implement the proposed cross-tail
subsumption automatically.

No new driver or project run was performed. The prior truncation wrapper
baseline ends at **run-7** with its finding; the direct-filter control ends
at **run-5** without it. Neither used a hard iteration cap. Historical
project reached/completed/accepted-forward positions remain OWASP
**run-11/run-11/run-11**, Conductor **run-8/run-7/run-7**, Stirling-PDF
**run-11/run-10/run-9**.

## 1. Candidate starts

For a matching-head MAY demand and MAY input, use two distinct FLOW keys:

```text
x.$/FLOW     -> x.$/FLOW,     NORMAL
x.[any]/FLOW -> x.[any]/FLOW, DEMAND
```

Clarification: the redesigned refinement starts are EXACT or MAY, not STAR.
The earlier assumption that the old ordinary-STAR start remains available
was incorrect. STAR is a public summary form after normalization.

Keep the exact probe EXACT during instruction processing. Apply the existing
complete FLOW summary normalization only at summary publication. Do not
replace its live fact by STAR at entry.

This scope is FLOW. A concrete T exact initial derived from MAY support
must retain DEMAND. Existing normalization does not turn its `$` into STAR.
A proposal for concrete starts must state whether the exact probe is a
separate FLOW companion; it cannot silently promote uncertain T to NORMAL.

These changes would reverse the selected no-MAY-initial rule and require
coordinated C2 image, runtime validation, C5 and control-premise updates.
No new tail, grounding label or field-transfer change is selected here.

## 2. Copy: the proposed favorable case

```java
// Demand: x.[any]/FLOW. Submitted: x.[any]/T, DEMAND.
// Starts: x.$/FLOW -> x.$/FLOW,N;
//         x.[any]/FLOW -> x.[any]/FLOW,D.
Object copy(Object x) {
    Object y = x;
    return y;
}
// Exact lane, before normalization: x.$/FLOW -> ret.$/FLOW,N.
// Exact lane, stored form S:        x.*/FLOW -> ret.*/FLOW,N.
// MAY lane, candidate W:            x.[any]/FLOW -> ret.[any]/FLOW,D.
```

On a same-head `x.[any]/T,D` offer, both S and W produce
`ret.[any]/T,D`. A NORMAL FLOW relation transports the uncertainty of the
actual input. It does not confirm T.

Thus S supplies the same immediate application result as W on this
restricted input class. Native AP checks confirm this for FLOW and concrete
T inputs, in both run directions, with empty exclusions.

## 3. Getter: where the exact probe helps, and where it cannot

```java
// Backward demand and submitted: ret.[any]/FLOW.
// Starts: ret.$/FLOW,N and ret.[any]/FLOW,D.
Object getG(Object x) {
    return x.g;
}
// Exact lane: ret.$/FLOW -> x.g.$/FLOW,N.
// Stored S:  ret.*/FLOW -> x.g.*/FLOW,N.
// MAY lane:  ret.[any]/FLOW -> x.g.[any]/FLOW,D.
```

The exact returned point can traverse the inverse read. Field g fits this
local test's limit. The NORMAL relation addresses the historical missing
getter record while the MAY lane remains available during analysis.

In the **forward** direction, starts at `x` behave differently:

```text
x.$/FLOW,N     through read x.g -> no DATA result
x.[any]/FLOW,D through read x.g -> ret.[any]/FLOW,D
```

Do not assume that the exact probe always creates a covering NORMAL summary.
Retain the MAY relation when no admitted provider exists. A future opposite
analysis can infer another provider, but it is not available merely because
the source code is a getter.

## 4. The proposed subsumption needs a specific contract

The checked local application law is:

```text
S = x.p.*/FLOW -> y.q.*/FLOW, NORMAL
W = x.p.[any]/FLOW -> y.q.[any]/FLOW, DEMAND

same complete owner/context/ports and compatible marks/headers
W matches only the selected same-head MAY input class

for each allowed A = x.p.[any]/M:
    Apply(S,A) = Apply(W,A) = y.q.[any]/M,DEMAND
```

This law is about abstract-fact application. Ordinary concrete-pair inclusion
does not prove it: W has independent input/output suffixes, while S correlates
them. Current aligned relation compaction accepts NORMAL STAR endpoints;
it does not compare this MAY-premise/DEMAND row against S.

The exact input class matters. If W also accepts `x.p.f.[any]/T`, the native
operators give different immediate results:

```text
S -> y.q.f.[any]/T,D
W -> y.q.[any]/T,D
```

These need not have equal future C2 behavior. This is a counterexample to
extending the local equality proof, not a whole-program finding-loss proof.
Any wider coarsening/removal law needs its own correctness argument.

Before deleting W from next-run demand, also prove that S and the remaining
guidance preserve every required future analysis. Equality on present MAY
offers alone does not establish that handoff property. Require S to be
actually admitted, published and available to the applicable replay path.
Check both arrival orders and persistence; retain W when that proof fails.
Do not remove protected memberships through a plain provider.

## 5. The earlier wrapper needs both old MAY-emission cells

The [history audit](bidirectional-may-initial-history-20261113.md) found two
old MAY emitters: same head and an ancestor MAY submitted to a deeper demand.
The [truncation example](bidirectional-truncation-evidence-20261113.md) uses
the second cell:

```text
wrap demand:    ret.f.[any]/FLOW
wrap submitted: ret.[any]/T
```

Changing only same-head MAY/MAY emission leaves this conversion to STAR
unchanged. To preserve MAY through that example, the candidate must also
define its two starts at the selected deeper head:

```text
ret.f.$/FLOW     -> ret.f.$/FLOW,N
ret.f.[any]/FLOW -> ret.f.[any]/FLOW,D
```

This is a required extension of the stated example cell, not an implemented
behavior or a tested full-program recovery. State the complete new C2 table;
do not retain old STAR-producing cells by default. A complete implementation
must also check first-new-field admission and every source of live call
inputs against the intended start domain.

## 6. Checked evidence and remaining scope

The [Lean package](../../spec/lean/proposals/dual-exact-may-starts-20261113/README.md)
checks the distinct starts, FLOW normalization, same-head MAY application,
support preservation, non-inclusion of raw concrete relations, forward-read
non-provider case, backward getter provider and descendant-input difference.
Its axiom audit has no classical choice, `sorryAx` or custom axioms.

The [native fixture](../../scripts/demand_experiments/dual-starts/DualStartsTest.kt)
has six passing AP tests. It constructs candidate raw starts through the
existing AP factory and checks real transfer, normalization and application
operators. It does not enable MAY initials in the method engine, install
MAY-only matching, or implement the new subsumption rule. It proves no
whole-project finding or performance result.

Evidence is external under [the data policy](EXTERNAL_DATA.md):

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/
  docs/reports/data/dual-exact-may-starts-20261113/native-v2/
```

It contains the exact source, Gradle command and init, JUnit XML, console
trace, source/classpath pins and receipt. The compile-only failed preparation
is separate. No production test assertion was changed.

Required next validation for a complete design: C2/C5 agreement, the proposed
MAY-only matching domain, handoff service coverage, literal protection,
cleaner/field-write exclusions, ND, Targets, block ports, and the historical
getter, nested-wrapper, two-loop and truncation-evidence driver programs.
Run these without an iteration cap before claiming eventual finding
preservation. Nothing here resumes the paused elimination campaign.

## 7. Combined with truncation evidence: does repetition stop?

The combination has two distinct opportunities:

```text
lost known suffix -> nonempty evidence -> reject a proved irrelevant
                    empty-chain offer, while MAY delivery preserves
                    the broad route through wrappers

exact probe -> admitted NORMAL provider -> remove a covered MAY demand,
              if application AND future-guidance coverage are proved
```

These address truncation-driven non-progress and redundant uncertainty for
an already modeled transfer. They do not establish termination or eliminate
every recurring MAY demand.

### Correction: the old STAR recurrence is not a new-policy counterexample

The earlier argument retained ordinary STAR admission from the old table.
The user clarified that the new emission uses EXACT or MAY, and STAR is
introduced only by summary normalization. Under that intended domain,
this historical operation is not a reachable-start counterexample:

```text
NORMAL micro-edge: x.f.* -> y.*
old live actual:   x.*, NORMAL
old result:        y.[any], DEMAND
```

The new local read instead has:

```text
EXACT start x.$ -> no result for read x.f
MAY start x.[any] -> y.[any], DEMAND
```

Its uncertain relation has a MAY original. It is not the old STAR-origin
relation. The formal model now proves that both starts have no live STAR,
and explicitly labels the old STAR operation as historical only. A full
no-live-STAR invariant must still cover method/block admission, producers,
cutting, cleaners, calls, saved-record application and reverse-MUST adapters.
Applying a normalized STAR summary must preserve the supplied EXACT/MAY
shape; it must not inject its stored STAR representation into live facts.

The [old OWASP capture](bidirectional-demand-row-campaign-20261112.md)
contains six STAR offers and zero MAY offers at the selected method in
each of run-9 and run-11. Those are old-policy observations. They cannot
be carried unchanged into the new policy or used to refute it. The prior
negative inference from these counts is withdrawn. The counts and original
operator evidence remain valid historical measurements.

The remaining repetition question is therefore a **new MAY-to-MAY
recurrence**: can a MAY-owned result survive NORMAL-provider compaction,
retain no useful nonempty-suffix evidence, and recreate the same guidance?
The old STAR-origin recurrence does not answer this question.

The combined design can change both the STAR-driven ambiguity loop and
truncation-driven non-progress. It is a plausible solution to the original
problem. No checked counterexample here proves that the clarified combined
policy still repeats. Equally, local start/application proofs do not prove
that every remaining MAY recurrence is eliminated. Validate the whole
combined policy on the uncapped wrapper, getter and project traces before
claiming convergence or measured savings. No campaign target or verdict
was changed by this correction.
