# OWASP: repeated forward demand after run-4

Date: 29 October 2026. Runtime: `c2bc5e78dfdb13f95bda970c5f4e0c247acbac29`.
Field limits: `1,1,2,3,...`. Run-1 mark mode: FULL. Statics and aliases are enabled.

The investigation confirms a repeated forward frontier. An isolated trace
finds exactly the same 162 selected summaries and 162 next-demand patterns
in run-5 and run-7. All are abstract FLOW relations. Their conclusions have
the `[any]` tail and DEMAND layer. No selected relation has a concrete mark,
an ND premise or a protected conclusion.

Representative traces and source code show a modeled field read below a
broad FLOW root. It loses the field correlation and emits `[any]` in DEMAND
before field-limit cutting.
A larger field limit does not change that operation while its input stays
broad. Fresh DEMAND work keeps the driver's stop counter positive. The
selected policy then starts another backward run. This is repeated
refinement across complete engines; the evidence does not show an infinite
work queue inside a completed engine.

## 1. Measurements and scope

The saved 8g campaign and the new 16g campaign both reach run-12, complete
run-11 and accept the forward report from run-11, at field limit 10. Both
stop on timeout during run-12. See the
[16 GiB comparison](bidirectional-repeat-run1-16g-performance-20261029.md)
for complete times, memory curves and controls.

| Completed forward run | Limit | Saved 8g outgoing D | New 16g outgoing D |
|---|---:|---:|---:|
| run-3 | 2 | 392 | 394 |
| run-5 | 4 | 162 | 162 |
| run-7 | 6 | 162 | 162 |
| run-9 | 8 | 162 | 162 |
| run-11 | 10 | 162 | 162 |

In both primary logs, the owner/count map is equal at runs 5, 7, 9 and 11,
including across the two heaps. The 162 memberships belong to 121 method
keys: 80 have one membership and 41 have two. All these methods are named
`doSomething`. The primary logs contain counts, not full demand payloads.

After the four primary runs closed, an isolated OWASP diagnostic exported
the actual handoff storage and selected summary payloads at run-5 and run-7.
It used 16g and the same schedule, models and time limits. It completed and
accepted run-7. A diagnostic-only POLICY stop then ended the test, after
the original stop checks and policy allowed continuation. The production
driver would have started run-8. Diagnostic times are not performance data.

The [embedded evidence](data/bidirectional-owasp-demand-convergence-20261029.json)
contains the complete 162-relation catalog and next-demand catalog, counter
data, representative IR witnesses, source hashes and diagnostic controls.
The exact payload equality claim applies to the diagnostic runs 5 and 7.
Payload equality at primary runs 9 and 11 was not measured.

## 2. The exact repeated frontier

Let `p` be argument 1, the `String param` argument after the request argument.
Let `H` be the synthetic field `java.lang.String.<string-bytes>`. `FLOW` is
the abstract mark; `N` and `D` mean NORMAL and DEMAND. Field exclusions are
empty in all selected rows.

| Selected summary shape | Number |
|---|---:|
| `p.* / FLOW -> ret.[any] / FLOW, D` | 121 |
| `p.* / FLOW -> ret.H.[any] / FLOW, D` | 41 |
| Concrete-mark, static, ND or protected selected rows | 0 |

Every selected conclusion carries two mark exclusions for the
trust-boundary rule. The catalog retains their full names and groups.
These exclusions are carried through the traces below. They are omitted
from the short notation. This does not mean that the facts have concrete
trust-boundary marks.

The forward-to-backward handoff swaps the two pattern sides and normalizes
the FLOW mark exclusions. For example:

```text
Selected relation:
    p.* / FLOW -> ret.[any] / FLOW, D

Actual next backward demand:
    entry = ret.[any] / FLOW
    exit  = p.* / FLOW
```

The `ret.H.[any]` relation gives the corresponding field-valued entry.
There are 162 distinct patterns after normalization. The complete selected
sets and complete next-demand sets are equal between diagnostic run-5 and
run-7, including owner, context, endpoints, marks, exclusions and layers.

This is not equality of the whole analyzer state. The raw relations of
these owners decrease from 1,161 scalar rows to 1,133: 28 NORMAL concrete
EXACT rows disappear, with no added rows. Their FLOW and ZERO sets remain
equal. Counter totals also change. Equal outgoing demand alone therefore
does not establish a safe new stopping rule.

## 3. Base64 helper: where the demand starts

`BenchmarkTest00996$Test.doSomething` contains this code:

```java
String bar = "";
if (param != null) {
    bar = new String(Base64.decodeBase64(
        Base64.encodeBase64(param.getBytes())));
}
return bar;
```

`BenchmarkTest01927.doSomething` has the same relevant operation chain.
The selected model for `String.getBytes()` includes a storage read:

```text
this.H.* / FLOW -> result.* / FLOW
```

It also has a root-copy route. The storage read does not have an explicit
`[any]` target. The model is in
[java-lang.yaml](../../model/java/config/stdlib/java-lang.yaml#L1507).
`JIRRuleForms.pass` compiles the copy to STAR sides.

The AP application distinguishes an ancestor leaf from a leaf at the
premise. See
[EdgeApplication.flow](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/EdgeApplication.kt#L78).

```text
Method initial:             p.* / FLOW
Start fact:                 p.* / FLOW, N
Bind getBytes receiver:     this.* / FLOW, N
Read this.H.*:              result.[any] / FLOW, D
Field cut, limit 4 or 6:    result.[any] / FLOW, D
```

The root leaf is above `H`. The operation cannot keep the suffix relation
for that read, so it emits ANY/DEMAND. The result has no concrete field
path to shorten. Increasing the cut budget does not repair this particular
loss.

The actual trace first captures `%2 / ANY / FLOW, D` at IR instruction 4:

```text
%3 = org.apache.commons.codec.binary.Base64.encodeBase64(%2)
```

This is the successor point after `param.getBytes()`. A matching CALL-cut
witness has DEMAND before and after cutting. The cut witness has no producer
instruction; the source/model review identifies the read above. The normal
exit at IR instruction 11 publishes the selected
`p.* -> ret.[any]` DEMAND relation.

For this one storage-read micro-edge, a more specific `p.H.*` FLOW initial
would give `result.* / FLOW, N`: the read reaches its premise exactly. This
does not prove that `p.H.*` resolves the whole helper. Other modeled reads,
including the String constructor's array-element route, can need a longer
initial such as `p.H.[*].*`.

## 4. StringBuilder helper: the same loss at a different model read

`BenchmarkTest01050$Test.doSomething` contains:

```java
StringBuilder sbxyz75528 = new StringBuilder(param);
String bar = sbxyz75528.append("_SafeStuff").toString();
return bar;
```

Let `R` be the synthetic `CharSequence.<rule-storage>` field. The constructor
copies the parameter to the builder root and storage. The append model has
both a root copy and a storage read. See
[java-lang-stringbuilder.yaml](../../model/java/config/stdlib/java-lang-stringbuilder.yaml#L2191).

```text
Root FLOW route from the constructor:
    p.* -> builder.*, N

Append storage read:
    this.R.* -> result.*
    builder.* above R -> result.[any], D

At the following instruction:
    bar = %2.toString()
    %2 is already ANY/FLOW, D
```

The captured successor is IR instruction 3. The CALL-cut witness again
starts with DEMAND. The normal exit at IR instruction 6 has both selected
results: `ret.[any]` and `ret.H.[any]`, under the same root FLOW premise.
The catalog and IR records retain both results. The trace does not claim
the first derivation of every returned `H` path.

A normal root copy cannot replace the storage-read relation in general:

```text
Input:          p.H.q / T
Root copy:      result.H.q / T
Storage read:   result.q / T
```

The output locations differ. Dropping the demand merely because a NORMAL
root-copy summary exists could lose the second relation.

## 5. Why the broad initial can return in the next forward run

Later initial admission uses `DemandStore.initials`. For a nonstatic input
in run-5 or run-7, it reads local demand entries. It does not consult the
persistent record store. Abstract admission uses `flowForm(entry)`, which
preserves the entry's base/path and maps an ANY abstract tail to STAR.
See [Reference.emit](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Reference.kt#L150)
and [DemandStore.initials](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/DemandStore.kt#L26).

Thus the observed root `p.* / FLOW` initial proves that a local root
abstract demand entry admitted it. A larger limit does not make that entry
field-specific.

NORMAL backward records take a separate path:

```text
Backward NORMAL singleton summary
    -> persist as a record
    -> omit from outgoing demand selection
    -> replay as an answer at a caller

Backward selected coarse demand
    -> next forward local demand entry
    -> C2 initial admission
```

A precise record can therefore coexist with a coarse demand. The record
does not replace the C2 entry or delete a different demand. This follows
from `selectDemand`, `RecordStore.persist`, `HandOff.toForward` and
`SubscriptionManager.replayRecords` in the source-bound evidence.

The models also permit a repeated coarse backward route. Reverse the
String constructor storage write to a field read. A broad returned-String
FLOW root can produce a bytes ANY/DEMAND result. Reverse root copies
through Base64 and getBytes can carry this back to `p.[any] / FLOW`.
The next C2 admission turns that root abstract entry into `p.*` again.
A parallel precise NORMAL route can still exist.

This last route is a source-level construction, not an exported actual
backward trace. The probe did not export the full run-6 paired demand or
record payloads. It proves the current root admission and the separation
of records from admission; it does not prove that a precise backward route
was absent or identify the exact paired exit that admitted each owner.

## 6. Why the driver starts the next iteration

There are three different quantities: outgoing demand patterns, report
candidates and the stop counter `RunResult.demandLayerEdges`.

| Diagnostic quantity | run-5 | run-7 |
|---|---:|---:|
| Outgoing demand patterns / owners | 162 / 121 | 162 / 121 |
| Report DEMAND candidates | 9,179 | 9,179 |
| Report CONFIRMED candidates | 0 | 0 |
| Incoming DEMAND presence contributions | 10 | 10 |
| Fresh point contributions | 26,948 | 13,538 |
| Fresh raw-summary contributions | 364 | 362 |
| Actual `demandLayerEdges` total | 27,322 | 13,910 |

The counter rows are global contributions across method actors, not a
census of 162 retained summary rows. Their sums equal the actual driver
counter. Fresh point and summary work is sufficient to keep it positive;
this is not only a stale incoming-input flag.

The production stop order in
[IterationDriver.barrier](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/IterationDriver.kt#L140)
is:

```kotlin
if (forward && !report.hasDemandVulnerability()) stop(STOP_RULE)
if (forward && !run1 && result.demandLayerEdges == 0L) stop(NO_DEMAND_EDGE)
if (forward && !policy.continueAfter(...)) stop(POLICY)
startNextRun()
```

Both measured forward runs have candidates, so STOP_RULE is false. A
NORMAL sink edge alone is not a confirmation certificate; unverified
witnesses remain DEMAND. The work counter is positive, so NO_DEMAND_EDGE
is false. `IncreasingLimits.continueAfter` always returns true. It compares
neither counts nor payload sets. The completed probe confirms that all
three production checks allow continuation.

The policy raises the field limit, but the traced broad-root/model-read
operation is unchanged. This explains why more heap and a larger field
limit do not remove this recurring forward frontier by themselves.

## 7. The cost of continued refinement

The forward frontier stays small, but the following backward work grows.
These are the primary 16g measurements:

| Backward run | Limit | Engine seconds | Outgoing D |
|---|---:|---:|---:|
| run-4 | 3 | 39.733 | 203,966 |
| run-6 | 5 | 49.338 | 330,881 |
| run-8 | 7 | 88.705 | 772,627 |
| run-10 | 9 | 304.586 | 2,543,694 |
| run-12 | 11 | 172.288 TIMEOUT | No completed frontier |

Backward ZERO control and seeded work repeat. The selected design also
publishes backward ZERO-premise seed paths without ordinary C5 restriction.
These mechanisms permit more work as the bound grows. The exact path-family
cause of the backward growth was not captured by this probe; the table is
not a per-path attribution. The primary run-12 timeout retains the report
from run-11.

## 8. Controls, limits and next design work

No production core or rule change was made for this investigation. The
trace patch is in a detached worktree and is embedded with its source,
class, command and test receipts. It adds joined-barrier serialization,
three counter splits and bounded witnesses. It does not change transfer,
admission, equality or storage keys. It does not enable the observers that
would disable batching.

The first isolated probe failed in run-5 because its trace codec rejected a
legal cleaner temporary. It reached run-5, completed run-4 and accepted
run-3. It produced no complete demand catalog. The trace-only codec fix
permits temporaries in samples; strict demand/summary keys still reject
them. All 36 selected tests pass. The corrected single retry completes
run-7 and produces both catalogs. Failed evidence remains separate.

The catalogs are complete. Point/cut witnesses are bounded and have explicit
omission counts. The cut hook records no NORMAL-to-DEMAND field-limit
bucket in these selected owners; representative records show DEMAND before
the cut. This is not a global causal census of every transfer or backward
path. Parent and independent source checks confirm payload equality,
counter sums and the modeled-read mechanism.

The next design issue is how to avoid repeating a coarse FLOW route while
retaining its required correlation. Two areas need separate proofs: more
precise admission or reuse of answers, and a stop policy that can distinguish
new refinement from repeated approximation. A stable count, or this one
stable selected set, is insufficient by itself. Neither change is
implemented or declared safe by this report.

All catalog data needed to inspect the 162 relations is in the linked JSON.
Full raw trace logs remain outside Git under:

```text
/drive-testcomp/opentaint-go-rules/repeat-run1-16g-20261029/convergence-investigation
```

## 9. Small executable reproducer

[OwaspDemandCycleTest](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/OwaspDemandCycleTest.kt)
now reproduces the cycle with two methods and one model field. The helper
has one argument; the request argument from OWASP is not needed.

```java
main() {
    sink(helper(sourceAll()));
}

helper(p) {
    bytes = getBytes(p);
    return newString(bytes);
}
```

The test supplies the relevant library transfers directly. Base64 root
copies are omitted. `H` represents the named String storage field.

```text
getBytes:
    p.*       -> bytes.*
    p.H.*     -> bytes.*
newString:
    bytes.*   -> out.*
    bytes.*   -> out.H.*
return:
    out.*     -> ret.*
```

All these helper transfers have STAR tails and at most one field. There is
no supplied ANY target. `sourceAll` is an ordinary whole-object source with
a full mark `T`; the sink checks `T`. The real AP operations create the
abstract ANY/DEMAND relation.

```text
Forward:
    p.* / FLOW, N -> bytes.[any] / FLOW, D -> ret.[any] / FLOW, D
Backward:
    ret.* / FLOW, N -> bytes.[any] / FLOW, D -> p.[any] / FLOW, D
Next C2 admission:
    p.[any] / FLOW demand -> p.* / FLOW initial
```

The test uses the production driver, engine, reversal, handoff, demand
store and record store. A test policy delegates the production schedule and
continuation decision, then adds a safety cap after run-9. Both production
stop checks must allow continuation before this policy is called.

| Test | Latest reached / complete / accepted | Result |
|---|---|---|
| Named storage routes | run-9 / run-9 / run-9 | Only the test POLICY cap stops the driver |
| Root copies only | run-3 / run-3 / run-3 | Production NO_DEMAND_EDGE stops the driver |

The first test checks exact selected demand equality at runs 5, 7 and 9,
actual handoff equality after runs 5 and 7, root abstract admission in each
later forward run, and processed FLOW/ANY DEMAND points. It also checks that
a precise NORMAL backward `ret.* -> p.H.*` record exists beside the coarse
demand. The control keeps the same source and sink and removes only the
named storage routes. Its last stop counter is zero.

This bounded test reproduces continued refinement after a repeated frontier.
It does not run an unbounded test or install a convergence fix. Both tests
pass. See the [summary and demand workload investigation](bidirectional-summary-demand-workload-20261029.md)
for the test command, receipts and related operation-count probes.

## 10. Lean model and initial-emission follow-up

The [initial-emission investigation](../design/bidirectional-initial-emission-refinement-20261029.md)
now models the small cycle in Lean and captures its actual call inputs.
The test still completes through **run-9** and stops at the test cap.
The latest project run remains **run-12 reached / run-11 complete**.

In run-3, the helper receives a NORMAL concrete MUST-T fact. Current C2
replaces it with `p.*/FLOW`, the same abstraction analyzed in run-1. The
Lean model proves the local alternating demand repeats for any positive
field-limit schedule. A concrete MUST initial instead preserves NORMAL
results through this helper and passes its demand gates.

This does not justify dropping every unchanged ANY initial. Two new
diagnostics show required backward source discovery and forward internal
sink observation under unchanged ANY initials. Both complete run-3; the
source case stops with `NO_DEMAND_EDGE`, and the sink case uses a POLICY cap.
Their full traces, test source and validation receipts are
[embedded](data/bidirectional-initial-emission-refinement-20261029.json).
No production admission rule or stop rule has changed.

The refinement clarification permits ANY-with-ANY intersection. The two
observation examples reject a strict-progress gate; they do not require
exceptions to ordinary intersection. The follow-up now includes a Lean
matrix for EXACT, ANY, MUST, field prefixes, and supplied STAR.
