# Nonzero source admission after the Target and ZERO changes

Date: 31 October 2026. Latest reached iteration: **run-3 COMPLETE**, with
field limits **1, 1, 2**. This report uses small production-engine tests.
It does not contain a new project performance campaign.

The latest combined FULL correction retains the real positive and rejects
the negative caller. The production regression passes at **run-3 COMPLETE**
with the report set **{"both inputs"}**. It preserves concrete exact
DEMAND admissions and marks a run-1 origin arm DEMAND when that arm drops
a required origin. Section 8 records this implementation result.

Sections 2–7 preserve the earlier measured failures: first a FULL false
negative, then a NORMAL false positive after the ordinary-layer correction.
Their old decision and validation statements describe those historical
phases. The new concrete admission and projection policy is specified in
[the exact-DEMAND specification](../../spec/demand-layer-exact-initials.md).
GROUP remains available; the acceptance scope for this correction is FULL.
This nonstatic case is separate from the static C5 gap.

## 1. Reproduction and rules

The permanent positive regression is
[FullConditionalSourceDemandTest.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/FullConditionalSourceDemandTest.kt).
It uses the production driver, an AND predicate, source actions, sinks, call
bindings, and field-write micro edges. It uses no predefined summaries,
static fields, constants, or synthetic witness reconstruction.

The following code shows its operations. The two local source actions are
at caller entry in the fixture. The source calls below show equivalent
local actions. They are configured call-site sources, not analyzed source
helpers with independent cached return summaries.

```java
// Source A: assign T1 to the result of externalSourceA().
// Source B: assign T2 to the result of externalSourceB().
// Producer: CM(p, T1) AND CM(q, T2) -> assign U to its result.
// Sink: CM(value, U).

Object make(Object p, Object q) {
    return configuredProducer(p, q);
}

void main() {
    Object a = externalSourceA();
    Object b = externalSourceB();
    Object r = make(a, b);             // Both source conditions are true.
    Box z = new Box();
    z.g = r;
    Box y = new Box();
    y.f = z;
    Object bad = make(a, new Object()); // The second condition is false.
    sink(y.f.g);                      // Required positive: "both inputs".
    sink(bad);                        // Required negative: "missing second input".
}
```

Notation: `Z` is ZERO; `N` is NORMAL; `D` is DEMAND. `$` is an exact
location, `*` is a correlated tail, and `[any]` is a MAY tail. Field
exclusions are empty in the decisive rows. `p` and `q` are the two method
arguments. The FULL runtime marks are `T1`, `T2`, and `U`.

## 2. FULL trace before the ordinary-layer correction

### Run-1, forward, limit 1

```text
Caller source results:
    Z -> a.$/T1                         N
    Z -> b.$/T2                         N

Actual inputs at the good make(a,b) call:
    a.$/T1                              N
    b.$/T2                              N

Run-1 concrete initials inside make:
    p.$/T1 -> p.$/T1                    D
    q.$/T2 -> q.$/T2                    D

The complete AND binding is available. Run-1 emits atomic origins:
    p.$/T1 -> ret.$/U                   D
    q.$/T2 -> ret.$/U                   D

After caller binding and the two field writes:
    Z -> r.$/U                          D
    Z -> z.g.$/U                        D
    Z -> y.f.[any]/U                    D   // f.g exceeds limit 1.
```

The former nonzero-origin rule kept the conditional outputs in DEMAND.
The corrected FULL ZERO policy does preserve the caller's two source
results as NORMAL. Those results have local bases. They are not exported
method summaries. There is no saved forward source relation that can
supply `b/T2` at the next caller entry.

The helper has no NORMAL forward producer for `ret/U`. A later native
candidate can be the BACKWARD identity `ret.$/U -> ret.$/U`; that relation
does not create `U` or supply either input mark.

### Run-2, backward, limit 1

The relevant paired demands in `make` are:

```text
(Dc = ret.$/U, Dp = p.$/T1)
(Dc = ret.$/U, Dp = q.$/T2)
```

The good sink's exact `y.f.g/U` seed is cut to `y.f.[any]/U`. The two
reversed field writes produce a MAY return query at the good call:

```text
sink seed:               Z -> y.f.[any]/U    D
reverse y.f = z:         Z -> z.[any]/U      D
reverse z.g = r:         Z -> r.[any]/U      D
callee offer:                ret.[any]/U    D
callee demand entry:         ret.$/U
current C2 result:            no initial
```

The exact demand cannot be satisfied by the MAY offer. The current rule
rejects it and creates no refinement obligation for that unanswered call.
Saved effects are tried before this gate, but no NORMAL forward producer
exists here. The backward identity does not repair the missing producer
or the missing input dependency.

The bad sink supplies an exact `ret.$/U` query to `make(a,clean)`. That
query is admitted. Its backward conditional branches require `p/T1` and
`q/T2`. Caller binding maps these requirements to `a/T1` and `clean/T2`.
Thus it reaches source A, but not source B.

Actual observations, in both the original CONJ test and the smaller
source-rule regression:

```text
B2 make current initial:      ret.$/U
B2 good-call C2 admission:    []
B2 root source hits:          source A only
F3 root source permissions:   source A only
Saved forward U producer:    none
Saved source B producer:     none
```

### Run-3, forward, limit 2

```text
make demand entries:
    p.$/T1
    q.$/T2

Actual source emission:
    a.$/T1                       emitted
    b.$/T2                       not emitted: no source B permission

Actual make initial:
    p.$/T1                       only

AND condition:                  incomplete
Root NORMAL Targets:           none
Outgoing refinement demand:    empty
Final report:                  {}
Stop:                          run-3 COMPLETE, NO_DEMAND_EDGE
```

The negative remains negative. The positive is missing. A field limit of
2 can represent `y.f.g` exactly, but the required second mark no longer
enters the analysis.

## 3. Matched GROUP and FULL observations before the correction

Before the ordinary-layer correction, the original `CurrentSequenceTest.CONJ`
was also run with a temporary FULL configuration. All other program operations stayed the same. The
configuration and diagnostic edits were then removed. Its positive
assertion was not changed.

| Observation | GROUP | FULL |
| --- | --- | --- |
| Latest reached iteration | run-3 COMPLETE | run-3 COMPLETE |
| Field limits | 1, 1, 2 | 1, 1, 2 |
| Caller source inputs in run-1 | group values, DEMAND | exact full marks, NORMAL |
| Helper's nonzero source outputs | DEMAND | DEMAND |
| B2 good-call offer | `ret.[any]/U` | `ret.[any]/U` |
| B2 current entry demand | `ret.$/G_U` | `ret.$/U` |
| B2 good-call admission | empty | empty |
| B2 root source hits | A only | A only |
| F3 source permissions | A only | A only |
| F3 helper concrete initials | `p.$/T1` only | `p.$/T1` only |
| Actual report | empty | empty |
| Required report | good sink only | good sink only |

GROUP marks in B2 demand select their corresponding full marks. The mark
ownership match is not the failed test. The EXACT/MAY geometry test fails
in both modes.

## 4. Factory cases

The explicit GROUP F76 factory has a separate positive loss with the same
admission failure. Its principal code is:

```java
Object factory() {
    Object ret = sourceAllT(); // Uniform T: ret.[any-taint]/T.
    ret.name = clean;
    ret.k = sourceU();        // Exact U: ret.k.$/U.
    return ret;
}
// Caller reads ret.email/T and ret.k/U, puts each below a.b, then checks it.
```

Its measured values are:

```text
Mode:                         GROUP
Latest reached iteration:     run-3 COMPLETE; limits 1,1,2
B2 U demand entry:            ret.k.$/G_U
B2 U offer:                   ret.k.[any]/U
B2 U current admission:       []
B2 factory concrete initials: ret.name.*/T, ret.email.*/T
B2 source hits:               source T only
F3 factory initial:           Z
F3 source permissions:        source T only
F1 NORMAL group TAINT records: none
Final NORMAL report:          {"F76 admitted email T"}
Missing positive:             "F76 exact k U"
```

The F1 barrier snapshot, not a later record-store query, establishes the
absence of group TAINT records. Record-store views remain live read-only
views. A query through an old configuration after run-3 can see later
records and returns spatial candidates before mark matching. Such a query
must not be described as an F1 snapshot or a matching U producer.

The default FULL `HistoricalFixedResidualTest` factory is different.
**Both expected findings already pass.** Its only stale assertion required
the old GROUP reference's exact source-seed set. The corrected FULL source
policy gives a NORMAL `Z -> ret.k.$/U` in the frozen run-1 result. That
summary is persisted and replayed before current admission. The U finding
therefore does not require another U source permission. T still needs its
source permission because the run-1 overwrites demote its residual.

The migrated test retains the two-finding assertion and verifies the
frozen NORMAL F1 U summary, the saved U relation, NORMAL caller U facts in
run-3, native crossings, and the still-required T permission. It does not
require identical source-seed sets across the old and selected policies.

## 5. Historical FULL result after the ordinary-layer correction

Latest reached iteration: **run-3 COMPLETE**; field limits **1, 1, 2**.
The production test above now reports:

```text
Expected: {"both inputs"}
Actual:   {"both inputs", "missing second input"}
Run list: [1, 2, 3]
```

FULL now keeps the ordinary AP-computed layer. An exact nonstatic concrete
initial is NORMAL. A concrete STAR initial still starts in DEMAND. Field
cuts, required exclusion loss, and the existing static policy can still
produce DEMAND. GROUP still puts its group-valued results in DEMAND. This
correction does not change the EXACT/MAY admission table.

These are the measured raw run-1 rows in `make`. The mark identifiers are
`T1 = 1`, `T2 = 2`, and `U = 3`. All exclusions are empty.

```text
Raw exact initials:
    {p.$/T1} -> p.$/T1                   N
    {q.$/T2} -> q.$/T2                   N

After the complete AND binding has been satisfied:
    {p.$/T1} -> ret.$/U                  N
    {q.$/T2} -> ret.$/U                  N

Run-1 stored summaries:
    {Z} -> Z                            N
    {p.$/T1} -> ret.$/U                  N
    {q.$/T2} -> ret.$/U                  N

Saved native candidates for ret.$/U:
    FORWARD p.$/T1 -> ret.$/U            N
    FORWARD q.$/T2 -> ret.$/U            N
```

The initial and local-output rows are from actual processed packets. The
summary rows are from the frozen run-1 analyzer. The native query records
the two saved FORWARD candidates after the run. They are the same two
unary relations shown in that run-1 snapshot; they are not a reconstructed
AND relation. No saved NORMAL relation retains both origins together.

This change supplies the native alternative that the earlier trace
lacked. The positive assertion now passes. The exact-admission control
also passes: a DEMAND `ret.[any]/U` still cannot create an initial for an
exact `ret.$/U` demand.

However, one saved unary relation is sufficient for the bad caller:

```text
Actual bad-call input:       a.$/T1                       N
Required second input:      clean.$/T2                   absent
Saved unary relation:       p.$/T1 -> ret.$/U            N
Caller binding:             Z -> bad.$/U                 N
Sink result:                Z -> NormalTarget("missing second input")
```

The original complete rule guard was true for the good caller. The
run-1 all-origin emission then split its result into the two unary
relations. Each unary relation is NORMAL after this correction. Applying
one in another caller no longer checks the other origin. The observed
NORMAL finding is therefore an effect of the split, not a failure to
await the complete binding when the rule first runs.

The current test preserves both assertions: it requires the good finding
and forbids the bad finding. Only the bad-negative assertion fails. The
old FULL false negative is fixed; a NORMAL false positive remains.

## 6. Cause and decision required at that stage

The earlier nonstatic positive losses used this sequence:

1. An exact conditional/group producer was retained only as DEMAND.
2. A field cut in the caller produced a MAY query in the backward run.
3. C2 rejected that MAY offer for an exact entry demand.
4. An unanswered demand created no work or continuation obligation.
5. The next forward run could emit a fresh source only with its backward
   source permission, unless a saved NORMAL effect supplied it.

The ordinary-layer FULL correction changes step 1. Its persisted NORMAL
producer restores the positive without an admission bypass. GROUP keeps
the previous DEMAND policy and its known losses. The source-summary
Target correction acts after a successful summary application; it does
not make a rejected current initial pass C2.

The remaining FULL problem is a different consequence of the same
run-1 origin split: a complete AND result becomes independently usable
NORMAL unary relations. A NORMAL unary relation is also not selected as
outgoing refinement demand. Thus changing its layer affects both caller
precision and the next-run frontier.

The required decision is whether FULL must retain the complete ND
premise, or whether this split and its extra NORMAL finding are an
accepted approximation. No ND policy change is selected by this report.
The complete-binding positive and bad-caller negative assertions remain
unchanged. The ordinary FULL layer correction is already applied.

No static pool, static transition composition, static C5 pair, constant
base, field exclusion, or ND Cartesian product is involved in this
example. No silent C2/C5 bypass, source-permission path, or continuation
obligation was added.

## 7. Historical validation

The focused run for that phase contained nine tests. Eight pass, including all six
`Run1FullLayerPolicyTest` controls and both native FULL source replay
controls. `FullConditionalSourceDemandTest` reaches **run-3 COMPLETE**.
Its good finding assertion passes, and its bad-negative assertion fails
with the two-finding set shown above. The test also verifies the raw
NORMAL exact initials, the frozen run-1 NORMAL source output, its absence
from outgoing DEMAND, persisted FORWARD producer candidates, and the
unchanged strict EXACT/MAY admission rule.

```bash
JAVA_HOME=/usr/lib/jvm/temurin-17-jdk-amd64 ./gradlew \
  :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.FullConditionalSourceDemandTest \
  --tests org.opentaint.dataflow.bidi.Run1FullLayerPolicyTest \
  --tests org.opentaint.dataflow.bidi.ExactDemandMaySourcePermissionTest \
  --console=plain
```

A separate scalar-oracle check passes both
`SelectedFullReferenceTest` tests, all three
`SelectedReferenceBoundaryTest` controls, and `NaiveClosureTest`. It checks
that SELECTED FULL retains ordinary exact NORMAL and STAR DEMAND layers.
The labelled PRE_TARGETS and historical references remain unchanged.

The pre-correction receipt remains evidence for the old FULL failure: its
positive assertion failed at **run-3 COMPLETE**, while its negative passed.
All three `HistoricalFixedResidualTest` tests passed after the seed-only
migration. That default FULL factory already had a saved NORMAL ZERO
producer and retained both expected findings.

That phase also recorded two GROUP positive failures: F76 lacked the
exact-k/U producer; CONJ lacked the good finding. Their measured iteration
was **run-3 COMPLETE**. These are historical observations, not a new GROUP
acceptance result. Temporary diagnostic changes to those tests were restored.


## 8. Latest implemented correction: concrete exact DEMAND and origin support

Latest reached iteration: **run-3 COMPLETE**; field limits **1, 1, 2**.
`FullConditionalSourceDemandTest` now passes both the positive and negative
assertions. Its current report set is:

```text
Expected: {"both inputs"}
Actual:   {"both inputs"}
Absent:   "missing second input"
```

This result is from the production Kotlin driver. The earlier Lean model
trace remains a separate proof artifact. It is not used as a substitute
for this runtime result.

The implementation keeps the ordinary FULL layer for definite evidence.
It also checks which origins each run-1 projected arm retains. For an arm
P, NORMAL support requires a complete NORMAL binding that can use P or
ZERO in every required column. The existing factored origin domains
supply this check. The analyzer does not enumerate input-origin products,
create executable ND edges in run-1, or attach support labels to ordinary
method edges.

For this example, the condition needs two distinct origins. The measured
run-1 initial and summary assertions are now:

```text
Definite exact initials:
    p.$/T1 -> p.$/T1                    N
    q.$/T2 -> q.$/T2                    N

After the complete AND condition is available:
    p.$/T1 -> ret.$/U                   D
    q.$/T2 -> ret.$/U                   D

Saved NORMAL FORWARD producer for ret.$/U:
    none from these weakened arms
```

Each arm remains available as demand guidance. Neither unary arm proves
U for a caller that lacks the other input. The regression checks that the
frozen run-1 source output is DEMAND and that no matching NORMAL FORWARD
native producer was saved.

The good caller still produces a cut backward MAY offer at limit 1. The
new concrete rule admits the required point provisionally:

```text
Good call in run-2:
    submitted: ret.[any]/U              D
    guide:     ret.$/U
    initial:   ret.$/U -> ret.$/U        D

Independent exact bad-sink requirement in run-2:
    submitted: ret.$/U                  N
    guide:     ret.$/U
    initial:   ret.$/U -> ret.$/U        N
```

The same InitialAp key now has two entry memberships, N and D. The test
observes both layers in the helper's run-2 processed starts. Repeating an
offer in the same layer creates no further start. Neither membership
suppresses the other. A guide's origin in a previous DEMAND edge does not
force a later definite input into DEMAND.

The backward condition transfer recovers the two required input marks.
The later forward run uses the existing complete ND relation and
same-call binding:

```text
Run-3 good call:
    actual inputs: p.$/T1 N and q.$/T2 N
    complete relation: {p.$/T1, q.$/T2} -> ret.$/U N
    result: good sink -> rooted NormalTarget("both inputs")

Run-3 bad call:
    actual input: p.$/T1 N
    required q.$/T2: absent
    complete relation: not satisfied
    result: no NormalTarget("missing second input")
```

The correction also applies cause-specific DEMAND to projected sink
origins. A complete multi-origin NORMAL sink witness cannot publish
independently usable unary NormalTargets. Its weakened arms publish
DemandTarget and retain the full physical sink seed. A separate unary
NORMAL witness can still publish NormalTarget. NormalTarget's existing
normal-only caller application and backward exclusion remain unchanged.

The selected scope is concrete marks. FLOW normalization, FLOW admission,
ZERO permission and starting policy, paired C5, native replay before C2,
source-action identity, static composition, and ignored END effects keep
their specified behavior. Actual field exclusions still gate descent;
invalid concrete exact demands with nonempty E are rejected.

Runtime validation in the latest focused run includes:

- `FullConditionalSourceDemandTest`: positive and negative pass at run-3.
- `InitialEmissionContractTest`: six tests pass, including directed
  same-prefix/ancestor MAY admission, actual-layer preservation, actual-E
  scalar boundaries, concrete/group mark checks, query coverage, and C5.
- `InitialFactStoreTest`: three tests pass, including both layer arrival
  orders, same-layer deduplication, intrinsic STAR, and GROUP/ZERO floors.

The final complete recheck passes 2,207 core tests and 452 JVM tests, with
no failures, errors, or skips. The earlier GROUP CONJ failure in the focused
receipt used superseded admission and stop assertions. Its updated
positive/negative control also passes. FULL remains the project acceptance
scope; these controls do not establish general GROUP correctness.

The finite test uses `FixedLimits(1,1,2)` and completes at run-3. This is
not a proof of general convergence. A permanent opaque MAY result can
keep supplying a provisional exact DEMAND point as field limits grow.
No promotion to NORMAL, fabricated source hit, or equal-count stopping
rule was added to hide that case.
