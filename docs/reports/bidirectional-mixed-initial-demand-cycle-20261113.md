# Mixed initial shapes can hide refinement progress

13 November 2026. A pinned native AP component refutes an unconditional
local depth-progress claim for coarse C5 replacement. An EXACT start and
a STAR start can share one normalized summary premise. The STAR start can
then hide the next demand from the EXACT start.

This is **not** a necessary-edge verdict. The component assumes the initial
rows and future offers. It does not establish their complete program
history, a repeated run-3/run-5 pair, or valid sink loss in a whole scan.
The actual OWASP 1025 target and all campaign counts stay unchanged.
Production behavior is unchanged.

The archived project positions remain:

| Project | Latest reached | Latest completed | Latest accepted forward |
|---|---|---|---|
| OWASP | run-11 | run-11 | run-11 |
| Conductor | run-8 | run-7 | run-7 |
| Stirling-PDF | run-11 | run-10 | run-9 |

The component runs one initial AP stage labelled run-22 and 12 following
stages labelled run-23 through run-34. These are
operator calls, not completed engine runs or new project measurements.
It uses no run limit as a correctness assumption.

## Proposed law under test

```text
X = (entry A; exit B)
Z = (entry A; exit B0), where B0 is a strict ancestor of B

C2_X = C2_Z
C5_Z keeps a coarser DEMAND result when C5_X keeps a NORMAL result.

Candidate conclusion: Z alone must eventually recover the precise result.
```

The component shows that this conclusion needs further assumptions.
The C2 and C5 operators can be correct at each step, while summary
normalization and canonicalization remove all subsequent local progress.
This result does not disprove every ancestor-output deletion predicate.
In particular, this case has an ANY entry. The 31 Conductor STAR-entry
cases need their own complete-state argument.

## Complete component inputs

`N` means NORMAL and `D` means DEMAND. All field exclusions, mark
exclusions and protection flags are empty. Mark T is a full mark.
Two additive NORMAL FLOW micro-edges belong to one abstract instruction:

```text
S:      p.a.g.*/FLOW   -> ret.f.h.h.h.*/FLOW, N
reader: p.a.g.f.*/FLOW -> ret.*/FLOW,         N
```

The opposite direction uses their native reversed micro-edges. No retained
composite S or inverse S is assumed. The initial NORMAL provider set is empty.

The first stage has these legal incoming rows:

```text
X: (entry p.a.[any]/FLOW; exit ret.f.h.h.*/FLOW)
Z: (entry p.a.[any]/FLOW; exit ret.*/FLOW)
```

The kept control uses X and Z. The cut control uses Z. Each original-direction
stage receives both of these independent offers:

```text
p.a.g.$/T,    N
p.a.g.*/FLOW, N
```

Each opposite-direction stage receives:

```text
ret.f.h.h.h.$/T, N
ret.*/FLOW,      N
```

The component assumes these offers. It does not derive them from source
rules or caller contexts. The bases are native Argument(0) and Return.
The initial component direction is BACKWARD; it is not a JVM-lowered method.

## First restriction and complete cycle

With X and Z, C2 starts `p.a.g.*/FLOW` and its `p.a.$/FLOW`
companion. X's output budget is 4. It keeps S NORMAL. The resulting
persisted relation maps the actual `p.a.g.$/T` offer to
`ret.f.h.h.h.$/T`, NORMAL.

Cutting only X leaves the same C2 starts. Z has output budget 1:

```text
C5_Z(S):      p.a.g.*/FLOW -> ret.f.[any]/FLOW, D
C5_Z(reader): p.a.g.*/FLOW -> ret.[any]/FLOW,   D

Canonical native store:
    p.a.g.*/FLOW -> ret.[any]/FLOW, D

Next demand A:
    (entry ret.[any]/FLOW; exit p.a.g.*/FLOW)
```

The root MAY covers the child MAY in the same layer and under the same
premise. That canonicalization is valid; it removes the more precise next
query from this component.

From A, all offers and both micro-edges give:

```text
C2 starts:
    ret.f.*/FLOW, N
    ret.$/FLOW,   N
    ret.*/FLOW,   N

Canonical admitted summaries:
    ret.f.*/FLOW -> p.a.g.[any]/FLOW, D
    ret.*/FLOW   -> p.a.g.[any]/FLOW, D
    ret.*/FLOW   -> p.a.g.f.*/FLOW,   N

Next demand B:
    (entry p.a.g.[any]/FLOW; exit ret.f.*/FLOW)
    (entry p.a.g.[any]/FLOW; exit ret.*/FLOW)
```

From B, the exact T offer and the abstract STAR offer emit distinct starts:

```text
p.a.g.$/FLOW, N
p.a.g.*/FLOW, N
```

The exact start can produce a child MAY after C5 cuts its deep NORMAL
result. The STAR start also produces root MAY through `reader`.
Both starts normalize to the **same** stored premise:

```text
normalize(p.a.g.$/FLOW) = normalize(p.a.g.*/FLOW) = p.a.g.*/FLOW

Canonical admitted summary:
    p.a.g.*/FLOW -> ret.[any]/FLOW, D

Next demand: A again.
```

The complete local state repeats after stages 2 and 4. It includes the
NORMAL provider below; the cycle does not discard it.

## Persisted replay is included

The opposite reader produces this real NORMAL provider:

```text
ret.*/FLOW -> p.a.g.f.*/FLOW, N
```

The component retains it and replays all retained providers **before C2**
on every fixed external offer. It uses the native direct/opposite read
roles and native record application. It inspects the replay results; it
does not schedule caller feedback or turn those results into extra offers.

In the original direction, the saved opposite view requires `p.a.g.f`.
The actual `p.a.g.$/T` is exact at its parent, so that view cannot produce
the required NORMAL result. The abstract STAR offer can produce MAY;
it still supplies no NORMAL exact point at `ret.f.h.h.h/T`.
All 12 native stages check both results. No hidden composite provider is
installed to make the cycle pass.

## Formal and executable checks

The [constructive scalar model](../../spec/lean/proposals/redundant-demand-mixed-initial-cycle-20261113/MixedOfferCycle.lean)
implements the selected empty-exclusion FLOW cells of C2, prefix transfer,
paired C5, relative output caps, summary normalization, MAY canonicalization
and NORMAL-provider retention. Eleven checked claims prove the two-state
closure and absence of a precise NORMAL provider at **every** later local
step. The kept control has that provider. The axiom audit contains only
`propext`; no Classical choice or assumed finite cutoff is used.

The pinned native component uses the production operators from revision
`14d7b63369d94f49d4c551be8405ed7719f267cc`. It checks all primaries and
companions, canonical storage and saved replay. It agrees with the model.
The Lean model is not a full-engine correspondence proof. Its `step` retains
NORMAL providers but does not feed their replay results into the next
query. `pointSupported` checks their precise point service separately.
Only the reached EXACT/STAR/ANY cells have native correspondence checks;
the unused MUST branches are not a complete MUST model. The native
component also keeps its external offers fixed. Caller feedback can add
other routes in a complete execution and remains an open obligation.

A separate restricted search tested 19,502 serial NORMAL prefix-rewriter
bodies with one precise offer per direction. Every case recovered a fresh
NORMAL point provider within 14 tested stages. Four path/progress lemmas
passed. That positive result needs its narrow scope: the mixed-offer case
uses an additional legal STAR offer and defeats the simple monotone-prefix
argument. The search is not a general deletion theorem.

The external package is:

```text
report-data-archive/opentaint-w3/docs/reports/data/
    redundant-demand-rows-20261112/cases/prefix-flow-query-model-v1/
```

It contains the native source, full stage trace, serial model, local cycle
model, Lean audit, pinned commands, checker and receipt. Large data follows
[the external-data policy](EXTERNAL_DATA.md).

## Remaining global obligations

Before this can become a necessary-edge example, construct an ordinary
method/block history that produces repeated X and Z, preserves every other
row and NORMAL provider at the later barrier, and supplies both actual
shapes through real caller contexts. Then remove only X at that barrier and
show valid sink loss with unlimited iterations.

A possible test design delays S through a deep temporary relay, so S is not
NORMAL before the cut, and uses a second wrapper context to supply the
abstract STAR offer. This is an untested design, not a completed finding-loss
example. It can also expose a retained inverse or regeneration route which
makes the deletion safe. Those routes must remain in the test.
