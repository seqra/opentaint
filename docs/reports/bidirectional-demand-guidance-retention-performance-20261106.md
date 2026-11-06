# Demand-guidance retention: project measurements

Runtime: `4182adae6152b4600a5401b78512b2b5b581998f`, 6 November 2026.
Status: measurements and profile review complete; quality acceptance remains open.

The FLOW-demand producer correction restores the two small prefix tests, but
the project campaign does not show a general performance improvement.
Conductor times out in run-4. Stirling-PDF times out in run-5. Thingsboard
still times out in run-1, during static completion. OWASP completes run-5.
The separate shared-loop program still completes run-5 without its expected
finding. Do not treat the native test pass as project quality acceptance.

Here, C2 means initial-fact admission against demand. C5 means summary
restriction against paired demand. FLOW is an abstract mark; T is a concrete
mark. `[any]` is the MAY field tail. `*` is the STAR tail. A guide position
is an explicit path in a demand relation; it can select a different C2 initial
even when an ancestor covers the same possible data.

The [portable evidence](data/bidirectional-demand-guidance-retention-performance-20261106.json)
contains complete finding identities, changed SARIF entries, every run table,
CPU/allocation/GC/resource results, hot-owner counters, source and capture
hashes, failed-attempt/retry metadata, and the complete small-program logs.
It stores repeated identities and symbols once. Its included pure Python
decoder reconstructs all seven original derived documents; all seven content
hashes pass after the repository copy. No table row is removed by this sharing.

## Measurement boundary

Use FULL marks, a 16 GiB heap, field limits `1,1,2,3,...`, aliases on and
run-1 statics on. The four project configurations and their analysis budgets
are unchanged. Runs use the direct `runProjectAnalyzer` Gradle task. The
saved `f945`, `52f` and `8331` controls were not rerun.

The initial Conductor command ended with a Gradle daemon stop after run-2
started. It took 96.454 seconds and produced no SARIF. This is an
infrastructure failure, not an empty finding set. The caller of the stop
command is unknown. The later retry used an isolated Gradle daemon registry.
Its captured analyzer arguments and classpath paths match the initial
attempt, except for output paths. Existing classpath bytes match; the same
two build-output directories are absent in both captures. The Gradle registry property is absent from
the analyzer JVM arguments. Keep the initial attempt and its cost separate.

## Current project outcomes

Labels mean latest reached / completed engine / accepted forward report.
A completed backward engine does not create a new accepted forward report.

| Project | Status | Labels | Command seconds | Peak process RSS GiB |
| --- | --- | --- | ---: | ---: |
| OWASP | OK | run-5 / run-5 / run-5 | 204.308 | 17.753 |
| Conductor, retry | TIMEOUT | run-4 / run-3 / run-3 | 1129.758 | 17.935 |
| Thingsboard | TIMEOUT | run-1 / none / none | 1131.904 | 18.180 |
| Stirling-PDF | TIMEOUT | run-5 / run-4 / run-3 | 1109.606 | 16.021 |

RSS includes Java heap and nonheap memory. It is not retained Java heap.
The Thingsboard SARIF has no accepted forward snapshot; quality is censored.

## Exact finding differences

The comparison uses complete strict identities, including rule, method,
location and fingerprint. A finding at another return is not an equal identity.

| Project | Current identities | Missing / added versus fixed f945 | Missing / added versus 52f | Missing / added versus 8331 |
| --- | ---: | --- | --- | --- |
| OWASP | 4,112 | 0 / 0 | 0 / 0 | 0 / 0 |
| Conductor | 5 | 2 / 0 | 2 / 0 | 0 / 0 |
| Thingsboard | 0 in provisional export | censored | censored | censored |
| Stirling-PDF | 21 | 4 / 8 | 1 / 0 | 1 / 0 |

Conductor's five identities and SARIF bytes equal the saved `8331` result.
The two missing fixed-baseline identities are still GraalJS findings in
`PythonEvaluator.evaluate(String,Object)` and `ScriptEvaluator.getSource(String)`.
The current accepted report is run-3; the saved `8331` accepted report is
run-13. The current timeout does not prove permanent loss or recovery of
either finding. The earlier [paired-guide investigation](bidirectional-conductor-must-demand-snapshot-20261106.md)
and the two repaired prefix tests establish the guide mechanism, but do not
establish the complete causal path for these two project findings.

Stirling's additional missing recent-control identity is the path-traversal
finding at `LicenseKeyChecker.getLicenseKeyContent`, `Files.exists(path)`,
IR14, line 98. The saved `8331` run-3 frontier also has 21 reports; its run-5
frontier has 22. Current run-5 times out before an accepted frontier. This
supports a later-report explanation, but there is no saved per-run identity
snapshot that assigns this particular identity to old run-5.

The other three Stirling fixed-baseline gaps and all eight added identities
already exist in both recent controls. They are documented in the
[previous baseline audit](bidirectional-canonical-facts-normal-relations-directional-inside-performance-20261105.md):
one `ProcessExecutor` command-injection path has a receiver-label transfer
discontinuity; two XSS findings have different representative return locations.
The actual project's first loss for the command path remains untraced.
These inherited gaps are not waived. Current accepted run-3 and the shared-loop
failure prevent a no-FN acceptance claim.

## Where the time and work go

The largest new cost is loop-consumer observation. This is a pure query used
to decide whether a loop result can be cut. It is different from executing
the method body or delivering an ordinary call summary.

```text
loop summary applies -> growing scalar result F
  -> observe F
     -> compute adjacent and repeat C2 admissions
     -> select saved consumer records
     -> apply those records to F
     -> normalize each result and perform enclosing C5
     -> union the complete scoped, port-labelled result
  -> compute the first possible cut budget
  -> observe trial cuts and compare complete observations
  -> emit the safe cut, keep F, or drop F
```

Current code computes the complete first observation before it asks whether
any cut budget can succeed. `LoopRestrictionSession.certifiedFirstBudget`
uses only labelled C2 admissions, but it is called after saved consumer replay
and enclosing C5 have already run. The same expensive queries are also made
for trial cuts whose C2 admissions alone can differ. This is work that can be
avoided without changing the selected fact or its layer.

The table uses Java `ExecutionSample` counts. Allocation is weighted
`ObjectAllocationSample` data, not retained heap. Scope shares are disjoint;
inclusive parent frames must not be added to them.

| Current window | Java samples | Loop observation share | Observation allocation share | Process CPU seconds | GC pause seconds |
| --- | ---: | ---: | ---: | ---: | ---: |
| Conductor run-4, TIMEOUT | 108,237 | 60.57% | 51.96% | 3,664.74 | 10.041 |
| Stirling run-4, COMPLETE | 11,167 | 78.80% | 85.60% | 439.30 | 0.952 |
| Stirling run-5, TIMEOUT | 16,269 | 82.01% | 88.15% | 646.34 | 1.270 |

Weighted allocation estimates are 5,172.81 GiB, 1,141.05 GiB and 1,664.67 GiB
for those windows. They show repeated temporary work, not multi-terabyte
retained heaps. Conductor uses about 3.88 process CPU cores on average in
run-4. Stirling uses about 1.13 in run-4 and 1.05 in run-5. These process CPU
totals include native GC and JIT work. They do not prove a scheduler defect,
but they show that the delay is not explained by GC pauses alone.

In the observation-specific classifier, saved record application accounts for
49.33% of Conductor run-4 observer samples, 43.62% of Stirling run-4 and 60.77%
of Stirling run-5. These are conditional observer shares, not whole-run shares.
Ordinary current delivery is only 2.23%, 0.02% and 0.01% of the respective
whole-window Java samples. A new ordinary pub/sub match cache is therefore
not the first measured target. Local block delivery already caches native
matches within an offer.

### The hot owners

| Current run / owner | Observation calls | Coverage |
| --- | ---: | --- |
| Conductor run-4, `ParametersUtils.replaceList` | 38,542,715 | 11-method aborted joined-owner sample |
| Conductor run-4, virtual `Map.replaceAll` lambda in `getTaskInputV2` | 37,769,171 | Same sample |
| Conductor run-4, `ParametersUtils.replace` | 11,591,290 | Same sample |
| Stirling run-4, `decodeMimeHeader` | 9,348,344 | 18 of 18 reported loop methods |
| Stirling run-5, `decodeMimeHeader` | 20,605,556 | Seven-owner aborted sample |

Conductor's sample has 92,395,185 observation calls. It is not an all-method
total. Stirling's named owner accounts for 99.51% of logged run-4 observations
and 99.56% of the logged run-5 sample.

In Stirling run-5, the same hot owner has only 36 ordinary local native
matches and 55 local data callbacks, but 76,514,141 saved selected records and
26,550,064 prepared C5 queries. The large work multiplier is in pure consumer
replay and demand checking. These counters are operations, not unique facts
or physical instruction executions.

Conductor run-4 `replaceList` records 35,708,630 scalar queries, 2,834,085
trials, 2,834,085 cuts and 32,874,544 raw fallbacks, with zero drops. Almost
all completed scalars have a certificate. The exact count that can skip
enclosing replay is unknown: current counters do not join the certificate
with the required nonempty cheap-admission test. The corresponding certified
zero-trial candidate group is about 32.87 million, before that test. In
Stirling run-4 `decodeMimeHeader`, it is 3,086,928. Stirling run-5 has a much
weaker bound, 0 to about 422,054; this shortcut alone is not a proved run-5 fix.

### Demand programs still scan empty buckets

`PreparedOutputPrograms.intersect` uses an output trie to select scalar
matches. It then allocates a bucket array for every compiled program and
loops over every program. A program with no selected bucket can only reject.
That final empty-bucket visit has no data effect.

Global Conductor run-4 counters have 3,620,680,565 C5 row attempts and
3,353,003,323 exact rejections, or 92.61%. Stirling run-5 has 2,347,095,605
attempts and 2,168,381,261 rejections, or 92.39%. These counters mix prepared
program rejections and native C5 rejections. They are **not** a measured
empty-program fraction or a prediction of the sparse-loop saving. Separate
touched, visited and null-program counters are required.

### Thingsboard remains a different workload

Run-1 logs 535.446 engine seconds and another 341.194 seconds in static
completion, which times out. These stages must not be merged into a completed
run-1 claim. In the reconstructed static-completion window, there are 25,725
Java samples: canonicalization 49.78%, CURRENT summary matching 26.89%, binding
residual 21.99%, candidate pruning 0.33%. Weighted allocation shares for the
first three scopes are reported in the portable data.

The binder canonicalizes an immutable `input.actual` inside each writer/input
visit. Reusing that pure canonical view is still a valid design target.
The source and samples do not establish the exact number of equal visits or
a twofold wall-time improvement. No static premise, mark group, field or
writer can be omitted under this proposal.

## Comparison with the previous implementation

The small prefix correction restores the earlier report checkpoint, but
retained guide positions also permit more current-run work. This is an
intentional effect of the selected repair, not a new scalar C2 rule.

| Observation | Saved 8331 control | Current 4182 |
| --- | --- | --- |
| OWASP command / accepted report | 198.198 s / run-5 | 204.308 s / run-5 |
| Conductor latest reached / complete / accepted | run-15 / run-14 / run-13 | run-4 / run-3 / run-3 |
| Conductor run-4 engine | 6.424 s, COMPLETE | 943.985 s, TIMEOUT |
| Stirling latest reached / complete / accepted | run-16 / run-15 / run-15 | run-5 / run-4 / run-3 |
| Thingsboard run-1 engine / static completion | 512.052 s / 440.336 s, TIMEOUT | 535.446 s / 341.194 s, TIMEOUT |

These are different demand trajectories, not equal-work speed ratios. The
current cost centre is a source-level repeated-work pattern with measured
CPU and operation counts. The data does not assign all added work to one
specific retained guide coordinate. Both Thingsboard static stages are
unfinished prefixes; a shorter prefix is not proof of faster completion.

The demand increase is mainly within the same analyzed methods:

| Completed frontier | Saved 8331 demand rows / keys | Current 4182 demand rows / keys | Analyzed nonzero method keys, old / current |
| --- | --- | --- | --- |
| Conductor run-1 | 114,411 / 6,763 | 120,059 / 6,763 | 11,129 / 11,129 |
| Conductor run-2 | 228,911 / 9,366 | 257,888 / 9,366 | 9,336 / 9,336 |
| Conductor run-3 | 12,986 / 634 | 174,269 / 660 | 7,282 / 7,282 |
| Stirling run-1 | 73,573 / 2,023 | 78,057 / 2,023 | 2,222 / 2,222 |
| Stirling run-2 | 265,614 / 4,204 | 299,262 / 4,204 | 4,184 / 4,184 |
| Stirling run-3 | 701 / 142 | 4,682 / 146 | 3,696 / 3,696 |

Only the three selected production files differ between these runtime
revisions: `Groups.kt`, `SpatialCanonical.kt` and `DiagonalRelations.kt`.
Keeping guide coordinates exposes a more expensive refinement trajectory;
the hot pure-query path then multiplies its work. Removing those coordinates
again would undo the demonstrated prefix correctness fix. The next design
must reduce the work of processing valid guidance.

## Memory and capture coverage

No current project reports MemoryManager OOM or JVM OutOfMemoryError. There
is no heap-dump artifact. The watcher records three Thingsboard high-memory
warnings, but no OOM capture trigger. No retained-owner or dominator result
can be inferred from an absent heap dump.

Whole-command GC pause times are OWASP 6.095 s, Conductor 17.785 s,
Thingsboard 58.814 s and Stirling 6.181 s. Thingsboard has three explicit full
GC pauses. Their before/after heap samples are approximately
15.052/9.258 GiB, 9.298/9.258 GiB and 14.594/12.261 GiB. Young-GC occupancy
is not a retained-object census; even these full-GC samples give no owner map.

The root reader used one 2 GiB, one-CPU direct-JFR JVM at a time, after every
benchmark and retry ended. It selected each continuous recording once and
did not add overlapping end snapshots. All 71 continuous/window rows pass
both sample-scope and allocation-scope checks: 142 invariants.

Thingsboard's first retained selected event is at 13:09:36.713 UTC, about
145.497 seconds after run-1 START. Its early engine sample coverage is
incomplete. The continuous event envelope does cover the reconstructed late
static-completion window. Envelope coverage is not proof that there are no
internal event gaps. Resource and GC logs have their own independent coverage.

The offline reader explicitly allowed only an unrelated, identified scratchpad
Gradle worker, with at least 8 GiB available memory. This exception applied
after measurements, to read immutable captures. It did not permit or change
analyzer measurements. Analyzer process CPU, elapsed time and profile samples
remain distinct measures; host contention is not ruled out by these records.

Before this campaign, root removed 40 owned old `8331` JFR files, totalling
2,432,059,567 bytes. It checked that there were no open readers and rechecked
22 retained evidence files. The cleanup receipt is embedded in the portable
data. Earlier cleanup is not counted again. Baseline data, source, user debug
directories and the current captures were preserved.

## Per-run time and outgoing frontier

Engine time excludes the separately logged joined static-binding time. The
barrier column is the logged report/handoff barrier. Counts describe handoff
demand rows, not unique runtime facts. A missing timeout frontier is unknown.

| Project | Run / direction / limit | Status | Engine s | Static binding s | Barrier s | Outgoing demand rows / keys | Target demand |
| --- | --- | --- | ---: | ---: | ---: | --- | ---: |
| OWASP | 1 / F / 1 | COMPLETE | 79.903 | 0.403 | 2.276 | 176,313 / 4,446 | 14,087 |
| OWASP | 2 / B / 1 | COMPLETE | 30.097 | — | 0.631 | 28,406 / 4,354 | 2,463 |
| OWASP | 3 / F / 2 | COMPLETE | 13.502 | — | 0.739 | 178 / 78 | 80 |
| OWASP | 4 / B / 3 | COMPLETE | 0.361 | — | 0.305 | 135 / 44 | 42 |
| OWASP | 5 / F / 4 | COMPLETE | 0.650 | — | 0.441 | 0 / 0 | 0 |
| conductor | 1 / F / 1 | COMPLETE | 15.650 | 1.963 | 1.717 | 120,059 / 6,763 | 7,896 |
| conductor | 2 / B / 1 | COMPLETE | 28.037 | — | 1.256 | 257,888 / 9,366 | 404 |
| conductor | 3 / F / 2 | COMPLETE | 61.863 | — | 0.878 | 174,269 / 660 | 1,831 |
| conductor | 4 / B / 3 | TIMEOUT | 943.985 | — | — | unknown | unknown |
| thingsboard | 1 / F / 1 | TIMEOUT | 535.446 | 341.194 | — | unknown | unknown |
| Stirling-PDF | 1 / F / 1 | COMPLETE | 19.412 | 0.428 | 0.648 | 78,057 / 2,023 | 5,400 |
| Stirling-PDF | 2 / B / 1 | COMPLETE | 32.809 | — | 0.940 | 299,262 / 4,204 | 469 |
| Stirling-PDF | 3 / F / 2 | COMPLETE | 6.047 | — | 0.732 | 4,682 / 146 | 136 |
| Stirling-PDF | 4 / B / 3 | COMPLETE | 388.219 | — | 0.536 | 39,006 / 116 | 96 |
| Stirling-PDF | 5 / F / 4 | TIMEOUT | 615.617 | — | — | unknown | unknown |

## Native validation and remaining coverage gap

The [native validation](bidirectional-demand-guidance-producer-validation-20261106.md)
records 3,009 passing tests and 39 finite-model lemmas. Scalar C2, initial
layers, field transfer and NormalTarget rules stay unchanged. The repair
retains explicit FLOW/DEMAND/ANY positions. Existing C2 can therefore emit
additional refinement initials from the retained positions.

Both prefix fixtures first report in run-3 and naturally complete run-5 with
one report. The shared-loop fixture naturally completes run-5 with zero
reports and fails its expected-one-report check.

The new shared-loop capture contains all 143 requested B2 trace events, with
zero size, limit, serialization or sink drops. All three frozen snapshots
are complete. F3 AL scope `(block=3, entry=7)` has one control pair:
`s.[any]/T -> ZERO`, paired exit `-2`. It has no DATA row, but its control
entry participates in C2 lookup. Its B2 producer is
`ZERO -> s.[any]/T`, DEMAND, at scope `(3,-2)`, exit `7`. The one captured
concrete C5 offer is already coarse before summary admission. This evidence
does not attribute that loss to the root summary's TAINT canonicalization.
Four separate native mechanism controls pass; they do not recover the program.

### Exact concrete-guide rejection

The later diagnostic uses current source plus five read-only hooks in an
external class directory. It changes no production source or transfer
decision. All class families from both instrumented files are present and
their code locations are checked. Its 173 trace events, nine complete
before/after point transactions and 12 whole snapshots have zero drops or
errors. Analysis completes run-5 with no finding; the unchanged finding
assertion then fails.

This is schematic code for the native fixture. `temp`, `next` and `out`
denote initialized, unmarked object bases. `Element` is the analyzer's
collection element slot. Unmarked object creation has no marked transfer
to add at these initial points.

```java
// sourceT assigns T exactly to its result; sinkT checks exact T.
s = sourceT();
do {
    temp.g = s;
    next.f = temp;
    s = next;
} while (again());
mapped = mapper(s);
sinkT(mapped.Element.h);

Box mapper(Box q) {
    if (flag()) out.Element.h = getG(getF(q));
    else        out.Element.h = q;
    return out;
}
Box getF(Box q) { return q.f; }
Box getG(Box q) { return q.g; }
```

After one loop body, `s.f.g` is the source object. The getter branch can
reach the sink. This test injects no demand, saved record or source permission.
The actual backward run-2 trace is:

```text
mapper summary, original ret.Element.[any]/FLOW:
    arg0.{root, f, g}.[any]/FLOW DEMAND
    // The FLOW repair retains all three positions.

call application transaction 10, sequences 65/66:
    arg0.f.[any]/FLOW DEMAND -> arg0.f.[any]/T DEMAND
call binding, sequence 67:
    -> s.f.[any]/T DEMAND

point transaction 11, sequences 68/69:
    scope (block=3, entry=-2), point 5, full original ZERO
    before: contains s.[any]/T DEMAND
    offer:  s.f.[any]/T DEMAND
    after:  same literal complete bucket; fresh delta is empty

summary and handoff:
    B2 producer (3,-2), exit 7: ZERO -> s.[any]/T DEMAND
    F3 AL scope (3,7), paired exit -2: s.[any]/T -> ZERO
```

The `g` position is rejected in the same way at transaction 8, sequences
57/58. These captured facts have empty field exclusions and no protection.
The adapter and binding preserve both children. The first demonstrated
removal of required `f` is point admission, before C5:
`BlockRunState.admitOutput -> ScopedEdgeStore.addAll -> ConclusionGroup ->
TaintGroup.addAll -> subtractSubsumed`. This early rejection occurs before
`canonicalTaintState`. FLOW-to-TAINT conversion is not the removing operation.

The passing native C2 control explains the operational difference:

```text
demand s.[any]/T:
    raw s.f.g.$/T NORMAL   -> s.f.*/T DEMAND
    cut s.f.[any]/T DEMAND -> s.f.*/T DEMAND

demand s.f.[any]/T:
    raw s.f.g.$/T NORMAL   -> s.f.g.$/T NORMAL
    cut s.f.[any]/T DEMAND -> s.f.[any]/T DEMAND
```

The lost position can distinguish the precise raw fact from its cut through
unchanged C2. This does not prove that one storage change repairs the whole
program or either Conductor finding. A concrete-demand extension needs a
design, both arrival orders, all storage adapters and tests. It changes the
selected boundary that kept TAINT compaction unchanged. It is not included
in `4182adae6`.

The [next proposal](../design/bidirectional-lazy-loop-observations-sparse-demand-programs-next-iteration-20261106.md)
keeps this correctness issue separate from measured work-removal targets.
No quality recovery or speedup is claimed here.
