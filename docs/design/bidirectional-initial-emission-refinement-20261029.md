# Initial emission and ANY refinement

Date: 29 October 2026. Analyzed revision: `557450fecb3e7432a60ecd1547ccf0acc0470e3e`.
This is an investigation and a formal model. It does not change the analyzer.

The selected goal is to refine the previous demand from the submitted fact.
A restricted forward run must not start the same broad FLOW analysis again.
In particular, run-3 must not emit `p.* / FLOW` only because its demand entry
is `p.[any] / FLOW`. Run-1 already analyzed that abstraction.

The current emission rule does exactly that. It replaces an abstract ANY
demand with STAR/FLOW. It uses the submitted fact only for the overlap test.
The Lean model reproduces the resulting cycle.

There are also edge cases. An unchanged ANY initial can be required to reach
a source in a backward run or an internal sink in a forward run. Thus a general
rule that drops every unchanged ANY intersection needs a complete observation
contract. Section 7 gives the measured examples. This decision is still open.

## 1. Scope and latest iterations

The named-storage reproducer completes **run-9**, forward, field limit 8.
The test cap stops it. Each engine completes. The root-copy control stops
at **run-3**, with `NO_DEMAND_EDGE`. A separate source-discovery example also
stops at **run-3**. These are small tests, not new project measurements.

The latest full OWASP measurement reaches **run-12**, completes **run-11**,
and accepts the run-11 forward report. See the
[project investigation](../reports/bidirectional-owasp-demand-convergence-20261029.md).
The local Lean recurrence does not prove non-termination of the whole driver.

The model has one nonstatic helper, one named storage field `H`, and one
full mark `T`. All exclusions are empty. It has no ND edges, static fields,
cleaners, aliases, type filters, or conditional source rules. A list of facts
represents alternative derivations. It does not represent the packed JVM tree.

All captured boundary facts, processed facts, summaries, receipts and model
validation results are embedded in the
[evidence file](../reports/data/bidirectional-initial-emission-refinement-20261029.json).

## 2. Original, current, and proposed behavior

The original concrete restricted-run design uses the intersection
`submitted fact ∩ demand entry`. It keeps the submitted concrete mark.
It reuses NORMAL records through a separate call-answer path.

The later F72 change adds abstract sharing. For an abstract demand entry,
it emits the demand's FLOW form. An ANY entry becomes STAR/FLOW. This is a
semantic policy, not an accidental storage choice. It is explicit in
[the history](../../spec/ap-history.md) and
[current section 6.3](../../spec/ap.md#63-restricted-run-the-emission).

| Part | Original concrete design | Current F72 behavior | Direction under review |
|---|---|---|---|
| Initial under abstract demand | Intersect actual input and demand; keep actual mark | Test overlap; emit demand FLOW form | Keep actual-supported refinement; do not restart broad FLOW |
| ANY demand | Meet with actual tail and path | Replace entry ANY with STAR | Resolve uncertainty from actual evidence |
| Whole-object T input | Retain concrete MUST information | Can replace it with FLOW | Retain MUST when the meet permits it |
| Persisted NORMAL records | Reuse at calls | Reuse at calls | Keep this path |
| Previously seen initial | No general completion certificate | Per-run deduplication only | Do not add a new completion cache |
| Unchanged ANY | Can reach sources and internal observations | Can reach sources and internal observations | Observation coverage decision remains open |

The relevant production paths are
[Reference.emit](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/Reference.kt#L150),
[DemandStore.initials](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/DemandStore.kt#L26),
and [RunMethodAnalyzer.addLink](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/RunMethodAnalyzer.kt#L120).

## 3. The exact OWASP reproducer

```java
main() {
    sink(helper(sourceAll()));
}

helper(p) {
    bytes = getBytes(p);
    out = newString(bytes);
    return out;
}
```

The fixture supplies only STAR micro-edges:

```text
getBytes:   p.*     -> bytes.*
            p.H.*   -> bytes.*
newString:  bytes.* -> out.*
            bytes.* -> out.H.*
return:     out.*   -> ret.*
```

`N` means NORMAL. `D` means DEMAND. `MUST` means the concrete
`[any-taint]` tail: every admitted descendant has T. It differs from MAY
`[any]`, which does not establish T at every descendant.

| Run | Submitted to helper | Local entry demand | Current emitted initial |
|---|---|---|---|
| run-1 | `p.MUST/T, D` | Unrestricted | `p.*/FLOW` |
| run-2 | `ret.[any]/T, D` | `ret.[any]/FLOW` | `ret.*/FLOW` |
| run-3 | `p.MUST/T, N` | `p.[any]/FLOW` | `p.*/FLOW` |
| run-4 | `ret.[any]/T, D` | `ret.[any]/FLOW` | `ret.*/FLOW` |
| run-5 through run-9 | Same alternating packets | Same alternating entries | Same alternating FLOW initials |

The forward demand exit is `ret.*/FLOW`. The backward demand exit is
`p.*/FLOW`. Caller premise is ZERO in both cases. The forward input in
run-3 is definite whole-object T. It is not an irreducible MAY input.

The current forward path is:

```text
actual p.MUST/T, N
  -> C2 emits p.*/FLOW, N
  -> read below p.H
  -> bytes.[any]/FLOW, D
  -> out.[any]/FLOW, D
  -> ret.[any]/FLOW, D
  -> selected demand for the backward run
```

The backward constructor route has the same ancestor loss. It returns
`p.[any]/FLOW, D`, which again admits `p.*/FLOW` in the next forward run.
The field paths never exceed one field. Lean proves that any limit at
least 1 leaves every intermediate result unchanged. A larger limit alone
does not change this local transfer and admission pattern.

The diagnostic captures actual links, initial premises and processed deltas.
It recomputes C2 results after the run from each link and the same immutable
demand snapshot. It does not hook the live return from C2. The actual
processed initial premise confirms the recomputed result.

## 4. Why record reuse does not stop this admission

Run-1 has both kinds of output under `p.*/FLOW`:

```text
p.* -> ret.*,       N
p.* -> ret.H.*,     N
p.* -> ret.[any],   D
```

The first two rows become records. The last row becomes demand. The next
run can apply the records at calls. C2 reads only demand. Its initial store
is new for each engine. Thus it can emit the same broad premise again.

This does not require a new global set of completed initials. A NORMAL
output proves one relation, not that every output under that initial is
complete. For example, a root-copy record maps `p.H/T` to `ret.H/T`. It
does not replace the storage-read relation from `p.H/T` to `ret/T`.
Skipping an initial only because some NORMAL record has the same premise
can lose the second relation.

The required change is to the refinement policy. Record existence alone
does not define that policy. The earlier F56 review also removed a closed
initial shortcut because it lost internal sink checks. Do not restore that
shortcut as a cache optimization.

## 5. What must count as refinement

ANY refinement must concern uncertainty, not just the tail name or record
count. The following cases need separate treatment:

| Demand entry | Actual evidence | Result to consider |
|---|---|---|
| `p.[any]/FLOW` | `p.H.$/T` | Known field and exact location |
| `p.[any]/FLOW` | `p.MUST/T, N` | Definite whole-object mark; same path, stronger evidence |
| `p.[any]/FLOW` | `p.H.[any]/T, D` | Longer known prefix, but uncertainty remains below H |
| `p.[any]/T` | `p.[any]/T, D` | No field refinement; source discovery or sink observation can still be new |
| `p.[any]/FLOW` | `p.[any]/T, D` | Mark is known; field uncertainty is unchanged |
| `p.H.[any]/T` | `p.H.K.$/T` at a larger limit | Field-limit refinement can reveal a real path |

Replacing ANY with STAR at the same path is not, by itself, a refinement.
STAR and ANY can cover equal sets of locations but give different summary
relations. STAR correlates the input and output suffix. ANY permits loss
of that correlation. Lean gives an executable witness for this difference.

Do not infer MUST from MAY. A heap with T only at `p.K` satisfies a MAY
root but does not establish T at `p.H`. A whole-object source does establish
T at H. The model checks both statements constructively.

## 6. Checked candidate for the named-storage cycle

For the actual run-3 packet, the concrete intersection gives:

```text
demand:     p.[any]/FLOW
submitted:  p.MUST/T, N
initial:    p.MUST/T
start:      p.MUST/T, N
```

The unchanged micro-edges then produce only NORMAL concrete results,
including `ret.MUST/T` and `ret.H.MUST/T`. Both pass the existing entry and
exit demand gates. No local result goes to the next DEMAND frontier.
This checks the helper pipeline, not complete driver termination under a
new policy.

Two simpler replacements fail:

```text
meet, then erase the mark:
  exact T -> abstract EXACT       // illegal initial
  MUST T  -> abstract MUST        // illegal initial

keep FLOW/ANY:
  FLOW/ANY starts DEMAND          // MUST evidence is still lost
```

Returning to concrete intersections changes F72 sharing. Initials can
again differ by mark and by actual geometry. This is a major semantic and
workload change. It must be explicit in a future implementation spec.
It must not be hidden in a cache, equality rule, or field transfer helper.

## 7. Counterexample to an unconditional no-refinement gate

```java
main() { sink(helper()); }
helper() { return sourceAll(); }
```

The real test has the following behavior:

```text
run-1:
  ZERO -> ret.MUST/T, D
  // Run-1 concrete output is DEMAND. No NORMAL source record replaces it.

run-2:
  demand:     ret.[any]/T -> ZERO
  submitted:  ret.[any]/T, D
  initial:    ret.[any]/T
  source hits: 1

run-3:
  source seed enables ZERO -> ret.MUST/T, N
  stop: NO_DEMAND_EDGE
```

Run-2 does not refine its entry path or tail. It discovers the source that
the next forward run must execute. Dropping its sole nonzero initial removes
that discovery path. ZERO traversal alone does not register that source hit.

The source fixture supplies an ordinary source edge. Current run-1
`forceRun1Layer` moves its TAINT output to DEMAND. The fixture does not
request that layer or create a field-limit cut. This is current run-1
behavior; do not attribute it to every older AP version.

The test measures the existing path. It does not install the proposed skip
rule. The loss under that rule follows from removing the only nonzero
requirement that reaches the reversed source.

### 7.1 An internal sink also needs an unchanged forward input

```java
main() {
    x = sourceAllT();
    y = mayModel(x);
    check(y);
}

check(p) { sinkT(p); }
```

The model operation is a valid pass edge `x.*/FLOW -> y.[any]/FLOW`.
It represents an unknown suffix mapping. The real forward diagnostic gives:

```text
run-3:
  check demand: p.[any]/T -> none
  submitted:    p.[any]/T, D
  initial:      p.[any]/T
  observation:  internal sink, DEMAND report in run-3
```

The test completes run-3 and stops at its POLICY cap. This is not a
convergence claim. There is no return demand. A native return record cannot
replay this internal sink check. The reporter replaces DEMAND findings at
each complete forward run. Dropping this initial can therefore remove the
unresolved observation from the next report.

This diagnostic also leaves the skip policy unimplemented. It checks the
current entry and observation path. The Lean model separately checks that
the same non-refining MAY fact triggers the sink predicate.

### 7.2 The remaining behavior decision

The no-refinement goal needs an observation contract. Retain unchanged ANY
starts for unresolved source discovery and internal observations, or provide
another complete path for those obligations before skipping the starts.
The backward source-discovery question is pending with the user. The forward
sink example shows that a direction test alone is insufficient.

Do not apply a blanket gate to either direction before proving this coverage.
The proof must account for observations, not only returned summary pairs.

## 8. Formal model and verification

[Cycle.lean](../../spec/lean/proposals/initial-emission/Cycle.lean) uses the
existing executable C2, transfer, C5 and limit operators. It proves the local
selected demand repeats for every finite number of alternating rounds, for
any schedule of field limits at least 1. Its inputs are the captured packets,
supplied afresh. The recurrence has no admission history or cross-round
record application. It is not an induction over the complete interprocedural
driver state.

[Policies.lean](../../spec/lean/proposals/initial-emission/Policies.lean)
checks the concrete intersection's local coverage and satisfaction contract,
the complete helper candidate, illegal abstract initials, MAY/MUST witnesses,
and field-limit and relation counterexamples.

[AdmissionHistory.lean](../../spec/lean/proposals/initial-emission/AdmissionHistory.lean)
checks three candidate forms of ANY refinement, the difference between a
handled initial and completed relations, and both local observation
counterexamples. Its history object is proof data, not a runtime cache
proposal. Its refinement predicate is a scoped test, not the selected
complete admission policy.

The existing Lean library has a historical concrete-STAR start row that
differs from current Kotlin. Cycle.lean states the current row explicitly.
The models do not use the historical row to claim current concrete-STAR
behavior. The older meet model also differs from Kotlin's MUST/STAR cell.
The checked OWASP candidate uses MUST/ANY and an explicit MUST flag.

Verification commands, from `spec/lean`:

```sh
lake build ApSpec.AnyTaintExDefs ApSpec.AbsDefs
lake env lean proposals/initial-emission/Cycle.lean
lake env lean proposals/initial-emission/Policies.lean
lake env lean proposals/initial-emission/AdmissionHistory.lean
```

Lean version is `4.33.1`. All three files compile. The executable cycle check is
`true`. Axiom audits show only Lean's `propext` and `Quot.sound`; there is no
`Classical.choice`, `sorryAx`, or user axiom. Existence proofs give executable
witnesses.

There are 80 checked theorem declarations across the three files. The
named-storage trace runs both existing tests. Each additional diagnostic
runs those tests plus its one temporary example. Every batch passes.
The Kotlin test is restored byte for byte after each diagnostic. The
evidence file contains the temporary test sources and JUnit output.

## 9. Required work before an implementation

Specify a refinement relation for MAY, MUST, exact paths, concrete STAR,
and marks. Keep submitted-input evidence separate from a backward requirement.
Then prove that skipped starts lose no unresolved relation, source hit, sink
observation, or rule action. Include ZERO, source subtrees, cleaners, mark
changes, ND rules, static demand, exclusions, and records.

Keep field transfer, overwrite behavior, summary restriction, record
application, source filtering, and the stop rule unchanged unless a separate
change is selected. The current local proofs do not authorize changes to
those mechanisms. In particular, they do not justify a new completion cache
or a new input provenance mechanism.
