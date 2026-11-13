# Post-handoff demand capture audit

12 November 2026. This is an evidence audit for the
[demand campaign](../design/bidirectional-redundant-demand-elimination-campaign-20261110.md).
The initial inventory audit made no analyzer run. Later sections record
the separate source build and passive OWASP capture. Production analyzer
source remains unchanged.

The later micro-capture also completed and accepted run-11. Its 2,633
finding locations and stable sink fingerprints match the original capture.
The [active investigation report](bidirectional-demand-row-campaign-20261112.md)
describes its constructor observations and the remaining proof limits.

## Result

The historical corpus contains the required native demand rows after
handoff. A new project scan is not needed to build the repeated-row
inventory. It is needed only if a later proof requires missing execution
history.

The native row inventory has **25,389 repeated rows**. The old ledger's
28,631 repeated summary origins are a different unit. Do not import its
verdict counts as row verdicts.

| Project | Earlier rows | Later rows | Repeated rows | Earlier only | Later only | Repeated units | Repeated methods |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| OWASP, run-9/run-11 | 1,153 | 1,153 | 1,153 | 0 | 0 | 534 | 463 |
| Conductor, run-5/run-7 | 30,646 | 88,792 | 23,303 | 7,343 | 65,489 | 281 | 166 |
| Stirling-PDF, run-7/run-9 | 1,105 | 986 | 933 | 172 | 53 | 131 | 59 |
| Total | 32,904 | 90,931 | 25,389 | 7,515 | 65,542 | 946 | 688 |

| Project | Repeated DATA rows | Repeated control rows | Latest reached / completed / accepted forward |
| --- | ---: | ---: | --- |
| OWASP | 121 | 1,032 | run-11 / run-11 / run-11 |
| Conductor | 19,553 | 3,750 | run-8 / run-7 / run-7 |
| Stirling-PDF | 796 | 137 | run-11 / run-10 / run-9 |

The run positions are the original capture results. This audit adds no
new performance measurement or necessity verdict.

## Authoritative files and native bridge

Use the external archive described in [External report data](EXTERNAL_DATA.md).
Let `A` be its `docs/reports/data/redundant-demand-20261110` directory.

```text
root(OWASP)       = A / v1-preflight
root(Conductor)   = A
root(Stirling)    = A

rows(project, r) = root(project) / snapshots / project /
                   run-r-projections.jsonl.gz
origins          = same directory / run-r-edges.jsonl.gz
originLinks      = same directory / run-r-projection-links.jsonl.gz
normalPackets    = same directory / run-r-persisted-packets.jsonl.gz
catalog          = root(project) / project-catalogs.json
reconciliation   = root(project) / project-reconciliation.json
```

Use the literal project names `OWASP`, `conductor` and `Stirling-PDF` in
these paths. Each decoded row contains `project`, `run`, `unitId`, `edgeId`,
`sourceEvent` and the complete native `edge`. DATA rows keep `entry` and
`exit` together. Control rows also keep their distinct entry/exit kinds.

`A/tools/Capture.java` hooks the return of `HandOff.Companion.of`. At that
point it reads the returned `HandOff.demand`:

```text
byMethod[method].rows
controls[method]
scoped[(method, scope)].data.rows, paired with rowPorts
scoped[(method, scope)].controls
```

Thus `PROJECTION_DATA` and `PROJECTION_CONTROL` are direct exports of the
retained native stores. Their event names do not mean that they are only
pre-insertion projections. The observer saves outgoing summary origins
separately. `A/tools/decode.py` checks each origin projection against the
native rows and saves all producer links.

The capture source revision is `3b73e74151bc19b5d49530cd5cded8dffc81d6b0`.
`git diff` for `core`, `model`, `rules` and `scripts` is empty between that
revision and the campaign's runtime
`14d7b63369d94f49d4c551be8405ed7719f267cc`.

## Checks performed

This audit decoded the nine earlier, intervening and later snapshots. Each
has zero duplicate row IDs and zero unresolved unit/port keys. The row
counts equal the corresponding `BARRIER_END` explicit demand counts.

| Project | Captured rows across the selected three runs |
| --- | --- |
| OWASP | run-9: 1,153; run-10: 2,292; run-11: 1,153 |
| Conductor | run-5: 30,646; run-6: 151,148; run-7: 88,792 |
| Stirling-PDF | run-7: 1,105; run-8: 1,123; run-9: 986 |

All three reconciliation records contain an `END` marker with zero errors.
They contain both selected `BARRIER_END` markers and report zero new errors
at each barrier. Their native projection checks have no missing or extra
rows. The terminal receipts are under `A/receipts/original-launch/`.
Conductor and Stirling time out only after the required pair has completed.

For OWASP, use the accepted immutable metadata overlays under
`A/metadata-supplement/` for saved providers whose geometry was not captured
in runs 1 and 2. In particular, `definitions-v2/acceptance.json` checks all
12,082 method definitions. `A/inventory/acceptance.json` binds the complete
method/block inventory and reports zero missing definitions or unresolved
provider units. These overlays add geometry only. They do not import
activity, summary availability, demand rows or submitted facts from another
execution. All selected native row scopes already resolve without an
overlay.

Native demand rows have no layer or protection coordinate. Keep these
coordinates on all summary origins, but do not add them to demand-row
equality. Likewise, keep each complete ND origin and all its projection
links; do not turn an ND conjunction into an OR relation.

## Reconstruction and remaining evidence gaps

Build the new inventory from native rows, not from the old repeated-origin
files:

```python
old = read_unique_native_rows(project, earlier_run)
new = read_unique_native_rows(project, later_run)
assert complete_barriers_and_resolved_units(old, new)
repeated = old.keys() & new.keys()   # row key includes the unit and ports
earlier_only = old.keys() - new.keys()
later_only = new.keys() - old.keys()
for row in repeated:
    save(row, all_original_producers(row), status="OPEN")
```

Verify the native IDs against canonical JSON and bind each new output to
the input file hashes. Preserve all empty method/block definitions in a
separate complete inventory. Do not infer them from nonempty row scopes.
Recheck historical proofs against removal of the whole row and all its
origins. Removing one producer while another emits that row is not a
row-deletion test.

The barrier observer does **not** capture submitted packets, pre-normalized
C2 initials, C5 derivation parents or rule-contributor events. Summary rows
and projection links suffice for the target inventory and origin-to-row
mapping. They do not supply a complete demand-evolution graph. A stored
STAR premise does not establish whether C2 emitted STAR or EXACT.

Use existing case captures only where their receipt proves the required
scope and coherent execution. Mark an absent transition as missing
provenance, not an unreachable transition. If a proof needs missing
submitted facts or C2/C5 parents, capture a coherent run pair with a passive
observer. Do not splice a second run's dynamic events into this original
execution.

## First FLOW target: evolution evidence

The coordinator selected native row `a76bfe144f2f2ecd…` in
`BenchmarkTest01985#doSomething(HttpServletRequest, String)`, method key
`5ed0dcd7694133e8…`. Its exact paired selectors are:

```text
entry: ret.bytes.[any]/FLOW
exit:  arg(1).bytes.[].*/FLOW
```

The row is present after both run-9 and run-11. Its only summary origin at
each barrier is `f0a91b60bd71c197…`:

```text
arg(1).bytes.[].*/FLOW → ret.bytes.[any]/FLOW, DEMAND
```

The original snapshots show this sequence. The table reports stored facts,
not an invented causal link between them.

| Run | Incoming demand from the previous handoff, relevant row | Submitted facts and emitted initials | Stored summary, relevant row | Outgoing demand, relevant row |
| --- | --- | --- | --- | --- |
| run-9 | `arg(1).bytes.[].[any]/FLOW → ret.bytes.*/FLOW` | Not captured | `arg(1).bytes.[].*/FLOW → ret.bytes.[any]/FLOW,D` | `ret.bytes.[any]/FLOW → arg(1).bytes.[].*/FLOW` |
| run-10 | `ret.bytes.[any]/FLOW → arg(1).bytes.[].*/FLOW` | Not captured | `ret.bytes.*/FLOW → arg(1).bytes.[].[any]/FLOW,D` | `arg(1).bytes.[].[any]/FLOW → ret.bytes.*/FLOW` |
| run-11 | `arg(1).bytes.[].[any]/FLOW → ret.bytes.*/FLOW` | Not captured | `arg(1).bytes.[].*/FLOW → ret.bytes.[any]/FLOW,D` | `ret.bytes.[any]/FLOW → arg(1).bytes.[].*/FLOW` |

All method demand rows and summaries were extracted, not only these displayed
rows. The six run-9 demand rows equal the six run-11 rows. The six run-8
rows equal the six run-10 rows. The 20 forward scalar summary memberships
at run-9 equal those at run-11. The 15 backward memberships at run-8 equal
those at run-10. The saved NORMAL basis has 25 scalar memberships at run-8
and 29 at runs 9, 10 and 11.

This is a native recurrence candidate. Its actual admission and C5 parent
links remain missing. The row equality and unchanged saved basis do not
prove future closure or authorize removal.

The old `OWASP-4378-passive-v4` capture cannot fill this gap. Its
`Selection.java` selects only method `17c642cb382ded12…`,
`BenchmarkTest01418$Test#doSomething`. The complete 860-record stream has
exactly one METHOD and zero occurrences of the new selected method key.
It records no submissions, C2 families or raw summary candidates at runs
9, 10 or 11, even for that old owner. That fresh owner's demand ends after
run-5 and its saved basis has 10 packets, while the original old-owner
basis has 16 packets. This is a different execution and a different owner.

The v4 observer and its validators can inform a new passive observer. Their
data cannot be joined to the current target's original snapshots. A complete
evolution graph needs one coherent capture that includes the selected owner,
actual offers and initials, raw C5 candidates/results, all retained producers
and cross-owner summary dependencies. Async initial admissions need explicit
lineage; a possible prior literal match is not a unique producer certificate.

The external evidence case is
`docs/reports/data/redundant-demand-rows-20261112/cases/owasp-flow-evolution-preparation-v1/`
inside the archive. It contains the read-only `prepare.py`, complete owner
extracts for runs 8–11, source file hashes and `receipt.json`. The script
checks native origin links, repeated sets and v4's owner scope. No new
project run, demand deletion or classification was made. Latest original
OWASP reached/completed/accepted forward remain run-11/run-11/run-11.

## Source-built runtime for the next capture

The pinned runtime was built from source with Gradle in the main checkout.
The build used an external source overlay and external output directories
for `opentaint-dataflow` and `opentaint-jvm-dataflow`. It changed no
production source and used no worktree, Git reset or downloaded analyzer.
The other runtime files retain the original capture's hashes.

The first attempt, `pinned-runtime-source-build-v2`, failed before compilation.
Its source check found that KotlinCompile did not see three Java source
files after the source-directory change. The separate v3 attempt adds the
same pinned Java directory to that compile task. The strict checks then
passed for all 472 source files: 385 Kotlin and three Java files in the
common module, and 84 Kotlin files in the JVM module.

The v3 build completed in **33.073 seconds**, with exit code 0. This is a
source-build time, not an engine-run measurement. Its receipt pins Kotlin
2.1.0, Gradle 8.10, Java 17.0.18, effective compiler arguments, build logic
and dependency contents. Each input source was also compared directly with
Git revision `14d7b63369d94f49d4c551be8405ed7719f267cc`.

The concrete 92-entry runtime classpath replaces exactly two jars. All 436
other file memberships, including 349 root class files, still match their
original hashes. The new jars are:

```text
opentaint-dataflow.jar
  249194d2984619cdf7cbead35b8f2e3f183506b95f29c619ffe4876db8c03313
opentaint-jvm-dataflow.jar
  4ffeff78852ea1821c73f3f36a40e32ed977a8329323d6a5cd78cd6ec90a49d0
```

These are source-pinned binaries. They are not byte-identical to the
historical jars. The jars contain build timestamps, and the complete hash
tree of 1,096 bidirectional classes also differs. Do not attribute all
differences to timestamps or claim full historical bytecode parity.

The offline bytecode check confirms all 14 old native hook signatures,
call anchors and return counts. It also confirms the declarations of eight
classes against the archived transformed classes. Of 532 non-hook methods,
530 have the same opcode and call shapes. The other two differ by one NOP
each, in `MethodBlockRuntime`'s constructor and `successorsRoot`. This
bounded comparison is not a full operand or bytecode equivalence proof.
The next observer must bind its hook contract to the newly built jars.

The external case
`docs/reports/data/redundant-demand-rows-20261112/cases/pinned-runtime-source-build-v3/`
contains `receipt.json`, `terminal.json`, `gradle.log`, the strict source
validator, compiler/build pins, `bytecode-audit.json`, and the verified
`runtime-classpath.json` and `runtime-classpath.txt`. The v2 failure remains
in its separate directory. No observer or project scan was launched. No
new engine run was reached; the original project run positions remain as
listed above.

## Observer and launch preflight

The independent diagnostic preflight passed for observer v3. Its smoke has
219 records, 84 decoded packets, 51 balanced causal contexts and zero
errors or dropped records. The review checks the typed caller/callee
coordinates, opposite-direction conclusion demand flag, shared-container
ambiguity and native transformation sites. Some payload checks call the
serializer directly with native values. This does not prove a complete
project evolution graph. Implicit exceptions are not universally unwound;
any nonzero frame depth or error must reject the resulting lineage.

The source-Gradle launch configuration also passed a dry run. It keeps the
original 8 GiB, 1000-second, FULL `1,1,2,...` settings. All 22,912 project
input files and the rule/configuration hashes match the original capture.
The harness uses a live serial file lock and a 1200-second outer timeout.
Its 92-entry runtime classpath contains no test fixture. It changes only
the two source-built engine jars described above.

The external `owasp-causal-recapture-launch-preparation-v1` case preserves
the earlier unsealed manifest under `history/` and has the final manifest,
strict pre-execution gates, independent review and `run.py`. No observer
or project was launched by this preflight. No new engine iteration is
reported. The next capture remains a diagnostic with explicit missing
provenance; zero observer errors alone cannot establish completeness.

## Fresh source-pinned OWASP result

The coordinator then ran the sealed source-Gradle capture once. It reached,
completed and accepted **run-11**. All **2,633 findings** match the original
capture's exact rule/location multiset and stable sink-fingerprint multiset.
The observer trace has 39,787 records, 20,752 decoded packets and 37,004
packed nodes. All 11 handoff markers, terminal counts, packet catalogs and
CRC checks pass. The 7,808 causal contexts and initial-message identities
balance; no observer error, dropped record or pending context remains.

The new 11-owner frontier differs from the original. It has **24** retained
FLOW rows after both run-9 and run-11, in four owners. Each of these rows
also occurs in the original corpus. These four owners have identical
native demand sets in every comparable run, run-3 through run-11:

| Owner | Full method ID | Repeated rows |
| --- | --- | ---: |
| `BenchmarkTest00996$Test#doSomething` | `689f957728f4e05e9054a0d427468d2dbfdfe476a12596810608f57035d52ea2` | 6 |
| `BenchmarkTest01009$Test#doSomething` | `a9bfa69aa69d7cfcca99089abcfcfc64bf5fb5ebe856c92ed5dd489d1f833263` | 6 |
| `BenchmarkTest01000$Test#doSomething` | `f994412d86d64f6f124b2ddc7bb286089e04d134e70fad172a351f200a9fedd5` | 6 |
| `BenchmarkTest01874#doSomething` | `e396eec3744814227d0e6e9921355802965bb9eb67234e3b480cb2b338e49e15` | 6 |

The other seven owners have no demand after run-5 in the fresh execution.
Their first comparable demand-set difference is run-5; their run-3 and
run-4 demand sets match the original. The complete scalar DATA NORMAL
provider sets match through run-6 for all 11 owners. For the seven owners,
the provider sets first differ at run-7. For the four owners above, these
provider sets also match through run-11. This comparison does not include
ZERO provider services or recover the original submitted facts.

For the earlier selected `BenchmarkTest01985` row, run-9 and run-11 each
have five actual offers and zero emitted initials. There is no late raw
C5 candidate, current summary or retained demand for that owner. This
fresh absence does not classify the original row as redundant. The two
executions stay separate.

The external capture case's `reconciliation-v1` directory contains all
99 owner/run demand comparisons, complete DATA NORMAL comparisons, actual
offer/family pairs, the finding comparison, and the full 24-row table with
original target IDs. The portable decoder is
[decode_causal_capture.py](../../scripts/demand_campaign/decode_causal_capture.py).
Its six focused tests pass. It refuses live execution input and preserves
the distinction between actual offers, service queries and native boundary
observations. Its output still declares `completeGraph=false`.

An additional class-resource audit checks the historical binary question
without running an analyzer. It reapplies the frozen historical observer
to the source-built classes, then compares all field/constant operands,
branches, switches, exception regions and calls with eight archived
transformed classes. Seven classes match exactly after removal of debug
attributes and frame tables. `MethodBlockRuntime` has only two additional
NOP instructions; removing these NOPs makes all eight match. No semantic
operand difference is found in that eight-class scope. The original full
1,096-class binaries are unavailable, and `RestrictedInitialPolicy`'s body
is outside that archived set. No whole-runtime historical byte-equivalence
claim follows. The external `historical-bytecode-semantic-audit-v1` receipt
records these limits and confirms that it created no AP fact or engine run.

## Second capture: selected native operations

The separate `owasp-micro-recapture-v1` scan exited successfully in
235.587 seconds, including preparation and diagnostic overhead. It reached,
completed and accepted run-11, with the same 2,633 finding locations and
sink fingerprints. This duration is not a production performance result.

The terminal stream has 64,247 records, 33,358 decoded packets and 60,509
decoded nodes. All 3,362 synchronous micro-frames closed. The observer has
zero errors, drops or unclosed frames, and all 1,104 initial-event messages
were delivered. It records 28 genuine NORMAL-to-MAY callbacks: six compiled
constructor operations and 22 boundary LIMIT operations. The decoder checks
actual leaves, not only the shared tail tag of a packed TAINT value.

The frozen observer passed an independent preflight. An additional audit
of the classes from the actual project scan checked 16 classes and 341
methods. All 2,525 native call operands and 988 field accesses retain their
order. At 28 result sites the observer duplicates the existing stack
arguments and then invokes the original result callback. This is a bounded
bytecode audit, not a whole-program semantic-equivalence proof.

For the selected `BenchmarkTest01000$Test` unit, demand sets at every barrier
from run-3 through run-11 and complete saved NORMAL packets match the first
fresh execution. Its demand sets also match the original corpus. The whole
11-owner frontier differs: the second scan retains 48 repeated rows in
eight owners, compared with 24 in four owners in the first. The four extra
owners are `BenchmarkTest01418$Test`, `BenchmarkTest02326`,
`BenchmarkTest01446$Test` and `BenchmarkTest01474$Test`. No scheduling cause
is established. Neither capture fills the original missing input history.

Use `owasp-1025-micro-analysis-v1/project-v2/` for the complete trace and
analysis receipt. The earlier `project-v1` human rendering is superseded:
constructor formals must be labelled `callee.arg(0)` and `callee.this`, not
the enclosing method's `request` and `this`.

The micro-IDs prove synchronous nesting only. They do not record every
work-queue parent or establish a unique micro-output-to-summary link.
No full causal graph, future-closure proof or new row verdict is claimed.
