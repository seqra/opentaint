# Cost fixes for useful demand-refinement rules

The isolated rule campaign found five candidates that stopped at least
one native repetition. This follow-up retains the native FULL analyzer
at `758ad99ff` as the control. Its production engine and project runner
match `0438facd2`. Each change has a separate detached worktree.
[Specification](../../spec/demand-refinement-and-termination.md)
[Original rule results](bidirectional-demand-refinement-rule-prototypes-20261118.md)

## Changes and native checks

| Rule | Work removed | Termination fixture |
| --- | --- | --- |
| R13 | An EXACT FULL fact cannot use the nested keep. Defer legacy geometry checks until an EXACT ancestor can use them. Compare paths without constructing an array. | Nested overwrite stops at run-3. The one provisional observation from the invalid nested keep disappears. |
| R26 | Skip the observer check for excluded owners. Reuse one structural result for successive offers at the same selected root cleaner. Check the actual leaf on each use. | The root EXACT cleaner stops at run-1 with the same observation confirmed. The exact-point observer still finds nothing. |
| R35 | Reuse the closed suffix and empty resolved callee check at the descendant EXACT cleaner. | The descendant EXACT cleaner stops at run-1 with the same observation confirmed. The erased point remains unreachable. |
| R36 | Leave same-head and one-field cleanup on the native path. Build one residual trie for consecutive heads with the same mask. | The deep BELOW, AT_AND_BELOW and RemoveAll cases stop at run-3 with their observations confirmed. The residual tests check the original exclusion and repeated fields. |
| R41 | Skip unnecessary compaction indexes and rebuild saved-record indexes once. Use the saved work to pay for a complete local or run-level check within its scope. | The scoped observer proof stops the synthetic global-cut, root-MAY and nested replay cases at run-5. The closed run-pair proof stops the selected compiled helper at run-11 with both observations. |

The native checks use a run-101 cutoff. Every stop in the table is a
natural stop. Earlier runs of the same fixtures reached the cutoff.
The combined prototype passed 153 tests across 92 instrumented cases.
Eight cases changed from the cutoff to natural completion. All
confirmed observations were retained.
The combined build with the loop-observation shortcuts also passed
153 tests across the same 92 cases, with the same eight natural
stops and no confirmed observation removed.
The source changes, positive assertions, native XML and comparison
receipts are in the detached worktrees. The constructive checks cover
the lazy EXACT guard, cached form result, packed residuals, C2 shortcut
and frozen geometry reuse.
[Lean checks](../../spec/lean/proposals/termination-rollback-20261118/UsefulRuleCosts.lean)

The full core suite exposed an old scalar expectation for R13's
strict descendant. The scalar reference now makes the same FULL
nonstatic selection as the packed operator. All 2,766 tests pass on
R13 after the reference and its example were updated. The complete
combined suite also exposed five old scalar cleaner expectations.
The R36 reference models the bounded residual as separate scalar
facts for comparison with the packed result. All 2,772 core tests
pass on the revised R36 and combined prototypes. R13 and the
combined prototype also passed all 467 JVM dataflow tests.

A paired native check exercised 216 forms of a nested field write.
For example, `clear(p.f.g); return p.f` must keep a mark at
`p.f.h` available at `ret.h`. The test varies exact and uniform
inputs, sibling paths, branch alternatives and a wrapper. Run the
same binary with the strict keep off and on. Both runs confirm
the same 84 observations. Sixty-six cases change their stop or
report metadata. The latest reached iteration is run-7.

The final loop-assisted combined build passed all 2,773 core tests and all
467 JVM dataflow tests. Both suites recorded zero failures, errors, or skips.

The generation-based combined build passed 2,708 core tests and
468 JVM tests, plus 15 focused tests with the bounded stop enabled.
The first run of its suite still contained 13 expectations for the
native nested write and cleaner behavior. The revised fixtures
check the exact surviving facts, the earlier stops and the erased
point controls. The final suites recorded zero failures, errors or
skips.

### Local workload measurements

| Operation | Earlier build | Revised build |
| --- | ---: | ---: |
| R26 structural checks for 32 offers at one root cleaner | 32 | 1 |
| R35 structural checks for 32 offers at one descendant cleaner | 32 | 1 |
| R13 allocated bytes per sampled STAR FLOW transfer | 808 native / 824 first revision | 688 with lazy maps, 568 with a direct first slot |
| R36 allocated bytes per cleanup over 12 repetitions of the same field | 48,576 | 6,720–6,959 |
| Selected native root EXACT cleaner fallback | 1,816 B | 1,816 B across R26, R35 and R36 |
| Native whole-subtree cleaner fallback at one field | 1,880 B | 1,880 B across R26, R35 and R36 |
| Handoff allocation per group of 280 origins with distinct C2 keys | 402,416 B | 107,104–109,289 B |
| Handoff allocation per group of 280 origins with one shared C2 key | 512,480 B | 221,256 B |
| Build and select 280 origins in different one-origin scopes | 2,670,000 B native / 2,345,200 B with indexes skipped | 434,480 B with order keys deferred |

The cleaner guard probes use 32 branches that supply sibling MUST heads
to one call. Each version stops at run-1 with the same confirmed
observation. The R36 allocation probe compares the earlier residual
partition and the packed version on the same marked input and cleaner.
It measures current-thread allocations after warmup. The native
component test checks the decoded residuals separately.
The R13 allocation revision retains one result key and root directly.
It builds the ordered map when a second distinct key is accepted. The
revision passed 147 native tests and still stops the nested overwrite
at run-3. The preceding lazy-map revision reached run-101 on the
compiled OWASP helper with both confirmed observations.
The handoff probes keep all 280 origins in both versions. The revised
point-tail test also avoids constructing a set for each shared-key test.
The singleton probe measures projection and selection together. A
singleton still keeps all its projected pairs. It needs neither an
index nor a string for deciding its order.
Each cleaner fallback measurement uses the same native input and action
in the control and each prototype. It records three samples of 80,000
applications after warmup with batch compilation.

## R41 on the selected compiled helper

| Run-4 handoff | Geometry attempts | Geometry builds | Retired origins | C5 row-index insertions bypassed |
| --- | ---: | ---: | ---: | ---: |
| Geometry-only experiment | 2 | 1 | 2 | 6 |
| Geometry-only experiment, backward root outputs only | 1 | 1 | 1 | 6 |
| Caller-checked variant | 0 | 0 | 0 | 6 |

Both geometry experiments stop at run-7 with the same two confirmed
observations. The narrower experiment retains the origin for
`ret.content.*`. It removes the single origin for `ret.*`, which
projects two paired rows for the two modeled byte fields. It removes
zero origins at the run-5, run-6 and run-7 handoffs.

The caller-checked variant requires one root and a complete closed
consumer scope. The selected compiled scan starts both the selected
entry method and the generated Spring dispatcher. It reaches run-101
with both observations under this guard. Even if the dispatcher can be
excluded from the affected scope by call reachability, the primary
entry still contains a loop and several consumers of the returned
value. The shortcut saves index work at run-4. The six skipped
insertions alone do not certify a budget for the continuation check.
The prototype uses a fixed 12,000-step diagnostic quota. The spec
requires an allowance paid for by lower-bounded savings in the same
handoff. The native runs have yet to verify that accounting while
the R41 certificate remains useful.

The missing check is whether a saved replay preserves the next native
uses, including C2 admission and source permissions. A `p.*/FLOW`
demand can admit a coarse `p.MAY/T` offer in run-5 and reject a precise
`p.f.$/T` offer. A proof that the saved relation covers the concrete
suffix therefore cannot replace the continuation check.

A separate native search compared 144 acyclic cases in the same build
with geometry retirement off and on. It varied the input field path,
exact or uniform marks, copy/read alternatives, the observed field and
a consumer that overwrites one field. Geometry retirement changed 58
final frontiers or stop results. It gave 36 new natural stops and
preserved each native confirmed observation in this set. The latest
reached iteration in the search was run-11. This check leaves the
general continuation proof open.

### Replies that require a continuation check

The selected-helper trace compares replies before resuming the caller.
At run-5 the native and root-only geometry runs have the same 12
distinct offers, 34 direct saved offer/reply pairs and 22 opposite-role
pairs. The current-summary pairs drop from 27 to 1.

| NORMAL offer | Native current reply absent from saved replay | NORMAL saved reply at the return root |
| --- | --- | --- |
| `arg(1).MUST/T` | `ret.MAY/T,D` | `ret.MUST/T` |
| `arg(1).bytes.$/T` | `ret.MAY/T,D` | `ret.$/T` |
| `arg(1).<string-bytes>.$/T` | `ret.MAY/T,D` | `ret.$/T` |

The saved reply at the return root can supply a consumer that uses
that point. A field read can distinguish it from `ret.MAY/T,D`.
For a proof limited to the return-root origin, follow the affected
return carrier from its binding. A use that can read a descendant,
export the value, require a different mark, or admit a different C2
initial still needs its own retained provider. The trace identifies the
three offers that need this proof at run-5. The proof must also cover
the offers that a later run could submit.

The root-output check used 1,565 counted steps at the run-4 handoff.
Reusing native prefix indexes reduced that to 1,475. Moving existing
sets through single-successor copy steps reduced it to 1,255. Starting
separate copy computations for the two byte field heads increased the
indexed case to 1,753 steps. The selected checker shares the base-level
geometry and clips the two fields afterward.

A diagnostic restored the three missing run-5 replies while the
run-4 origin was still retired. It kept both confirmed observations
and stopped naturally at run-9. The run-5 handoff retained seven
pairs versus four without restoration. Preserving those replies for
the affected transition can still break the observed cycle. A
general replacement needs to determine all required replies from
the sealed state and prove their later service.

Restoring the same replies on every eligible forward offer reaches
run-101 with the same two observations. From run-5 through run-101,
each completed forward handoff has seven Target pairs and each
following backward handoff has 22 pairs. With run-5-only restoration,
the forward counts at run-5, run-7 and run-9 are seven, four and zero.
The recurring replies renew six Target rows at the caller's post-loop
block plus one at method scope. Permanently replaying the coarse
outputs therefore preserves the measured repetition. The continuation
proof must show exactly which consumers can use a saved precise route
and when that route also supplies the needed source permissions.
Restoring only the MUST-backed reply keeps five forward Target pairs
through run-101. Restoring only the two exact-backed replies keeps
three forward Target pairs from run-7 through run-101. Both
experiments preserve the two confirmed observations. Each reply
family can sustain the repetition on its own.

The observer trace narrows that check. In the post-loop block, the
restored MAY replies yield six DEMAND witnesses at one observer
instruction. All six check the same exact marked receiver. Three
origins also produce an identical NORMAL witness in that block
in run-5. They are the MUST input at the block argument root and
the two exact byte-field inputs. The other three origins use
correlated STAR and have only exact-point NORMAL counterparts.
The equality at the three witnessed origins identifies concrete
continuation candidates. It does not establish that every enclosing
binding supplies those origins at NORMAL, or that a STAR origin
admits only the corresponding point.

The compiled caller suffix passes the returned value through
unresolved builder operations, binding and alias stages, and a
resolved downstream call. A post-loop scope removes the unrelated
cookie loop from the forward closure check. That cut still leaves
these call effects to prove.

The decoded call forms show where a root-only continuation proof
fails. The first append that takes the helper's result has both
`arg(0).*/FLOW → ret.*/FLOW` and
`arg(0).*/FLOW → ret.content.*/FLOW`. The next append has
`this.content.*/FLOW → ret.*/FLOW` as well as the root copy.
Thus there is a named-field consumer even though the later
observer checks a root. The exact reply can serve that read
through the explicit `content` write at the first append.
Completeness also requires the alias outputs, the mark-dependent
producer at the next call, and the resolved `printResults` input.
The annotated diagnostic reached run-101 with the same two
observations. It establishes the actual call forms, including
branches where a blanket root-only check would be unsound.

The existing NORMAL condition-contributor cache can supply stored
condition leaves at a physical action site. Its restore path requires
a current accepted leaf first. A stored leaf alone does not prove
that narrowing the helper reply starts the same conditional action
or grants the same reverse permission. A complete checker can reuse
that evidence where the ordinary activation has a separate witness.

### Observer census and global field-limit checks

A scope in which all possible observer identities already have retained
root NORMAL receipts could replace the continuation check. The receipts
remain available even if later admissions or source permissions change.
This requires a complete upper bound on future observer identities.
The compiled native census walked 21 method contexts and 360
instructions from both roots. It found 117 observer keys at the run-4
handoff and two confirmed keys. Evaluating all positive rule conditions
over the globally producible mark set still left 115 unconfirmed keys.
The census therefore cannot discharge this origin. The selected scan
reached and completed run-101 with both confirmed results.
[Observer receipt proof](../../spec/lean/proposals/termination-rollback-20261118/ObserverCensus.lean)

The native global limit remained active after the repeated guide first
appeared. At run-5, run-7 and run-9 it cut 244, 129 and 24 packets
respectively. The diagnostic recorded zero global cuts, entry-depth
rejections and paired caps bound by the global limit at run-10 and
later. At the run-9 handoff, the ordered demands already match run-7
but the saved-record basis differs. At the run-11 handoff, the audit
matches run-9 on ordered demands, seeds, saved-record index order,
condition contributors, retained NORMAL Targets, confirmed identities
and latest reached identities. The run-10 and run-11 transitions are
the first observed pair that meets both checks.

The audit-only scan completed run-101 with two confirmed observations.
A separate diagnostic applies a forward stop when the pair passes the
state and limit checks, each run has one active root and one effective
unit, and every latest reached identity has a NORMAL receipt. It
completed naturally at run-11 with both report identities. This uses
the pair check even when the configured limit is run-101.
Reversing the root order and clearing the soft caches before each
transition of that pair gave the same run-11 stop and reports. A
separate diagnostic kept the stop disabled through run-101. It
repeated the counted queue sequence and payloads
of eight forward and four backward events at the higher limits
through run-101. In both directions the one active unit received
no routed non-root events for another unit.

Using the same pair check to retire only the copy demand at the
run-11 handoff removes six of 17 rows. The eleven control rows
continue through the native pipeline. That scan stops at run-15
with the same two confirmed observations. A whole-pair stop and R41
copy retirement therefore have different completion checkpoints.

The candidate is a different driver rule from the local R41
continuation check. It still needs source correspondence for the
complete scheduled transitions at higher field limits, including
stable cache rebuild and event ordering, and a verified resource
bound for recording and comparing the state. The selected run
also offered one nonidentical NORMAL packet in run-10 and two in
run-11. Equality of the retained records requires examining the
native merge, since checking for exact duplicate offers alone
would reject those transitions.
[Closed run-pair proof](../../spec/lean/proposals/termination-rollback-20261118/ClosedRunPair.lean)

The closed-root R41 prototype still stops the synthetic global-cut
and root-MAY cases at run-7 with their confirmed observations. At the
run-5 seal, the two checks counted 140 and 137 proof visits,
respectively. Each omitted index pass has six records and six output
positions. Both seals skip one compaction index row. The measurements
leave the local verifier's resource allowance open for these small
scopes as well as for the compiled case.

Reusing the closed-root shape and bounded copy geometry across seals
reduced the global-cut proof at its first successful handoff from
140 to 36 visits. The root-MAY case first became eligible at its
successful handoff and still needed 137 visits. The prototype kept
both natural run-7 stops. It exercised only structural reuse.
Current saved providers were still checked for each candidate.

The complete-report alternative bypasses the geometry check. It
stopped the synthetic global-cut case at run-3 and the root-MAY
case at run-5 after 52 and 51 closure visits respectively. It
also stopped the nested saved-replay and overwrite fixtures at
run-5. Each has one confirmed observation. The two provisional
controls still reached run-101 with their original provisional
reports. All 14 focused tests passed. The closed-pair alternative
by itself retained the run-101 result on the two copy fixtures
because each uses more than one active unit. The two prospective
stopping conditions cover different scopes.

A streaming proof visits the compiled observer lists and call
alternatives. It borrows existing FULL forward forms and returns
Unknown on a missing cache slot. In the two copy fixtures it
completed in 29 visits with no form rebuild. A two-observer test
confirmed one identity in run-1 and both in run-3. The streaming
variant stopped only when both were confirmed. The 15 focused
native tests passed.

The first executable allowance omits the intermediate index pass
and credits its record and output-position visits. It has a
scan-wide balance capped at 128 visits. At the run-5 seal the
global-cut and root-MAY cases reserved 42 and 46 visits respectively
and used 30 each, including receipt enumeration. Both stopped with
their confirmed result. The two-observer test also stopped in
run-5 with both identities. The two provisional controls still
reached run-101. This prototype verifies the counted item visits.

The compiled run-pair prototype also stops at run-11 with the
same two confirmed reports. It reserves 512 item visits before
capturing the ordered record references and 1,792 before
capturing and comparing the other views. Both reservations use
work saved by omitted rebuilds in completed seals of that scan.
The comparison reserves 54 field-word reads for the two demand
views and leaves 416 in its field balance. It uses identity for
record and contributor rows, accepts the native predicate seed
and requires empty demand masks for this accounting path.
`owasp-paid-pair-field/owasp.json` records the stop. Full key,
allocation and runtime witness accounting still needs
verification on the integrated path.

The same paid pair check ran with the revised R13, R26, R35 and
R36 implementations and the loop replay shortcuts. The selected
compiled helper completed run-11 with `STOP_RULE`. Its two confirmed
reports match the native run-101 control by rule and full location.
The run-11 witness retained the same 17 demand pairs, one predicate
seed, 98 contributor rows and 22 retained Target rows.

The narrower audit counted actual accepted root starts and checked
the two field-limit-dependent cleaner branches introduced in the cost
fixes. All five global limit controls were stable in run-10 and
run-11. The run-11 ordered queue matched its previous forward
execution. The audited scan stopped at run-11 with the same two
confirmed reports. The driver took 2.138 seconds versus 7.608 seconds
to reach the run-101 cutoff in the native diagnostic. The project
comparison measures cost without storing complete event traces.

The combined build also passed 15 focused native tests. The global-cut,
root-MAY, nested-replay and two-observer cases stopped at run-5 with
their confirmed reports. The R13 nested overwrite stopped at run-3
without the provisional report. Two acyclic provisional controls kept
their run-101 outcome. The guarded build for the full project comparison
tests scope eligibility before enabling the bounded proof work.

The next prototype stores the generation of the ordered record view
and the generation of the contributor root. Retained NORMAL Targets
and confirmed entries use their counts because each new view starts
with the complete old ordered prefix. The verifier reserves 768 item
visits for the other views at run-11, down from 1,792. It uses the
same 54 field-word allowance and retains both confirmed reports at
the natural run-11 stop. The order comparison is now part of the
existing index traversal. The fused version also stopped at run-11
with both reports and the same reservation, with queue tracing
disabled. [Generation proof](../../spec/lean/proposals/termination-rollback-20261118/RecordIndexSeal.lean)

### Rebuild the saved-record indexes once

The driver merges NORMAL method summaries and then NORMAL block
summaries. Each merge currently rebuilds all four saved-record
indexes. No worker or barrier stage reads the intermediate result.
The detached prototype builds the indexes once after both merges.
It passed all 31 focused tests, including a new ordered comparison of
public and scoped entry and exit lookup across successive forward and
backward seals.

In a same-binary comparison, both arms reached and completed run-101
with identical report locations and status. The normalized trace
matched all 1,571 recorded persisted packets, 1,617 summary packets,
2,327 demand rows and 1,206 Target rows. The comparison replaces
process-local field and mark IDs with names and retains scope, port,
layer, exclusions and protection.

The prototype reduced index rebuilds from 202 to 101. It skipped
36,799 record visits and entry insertions, and 40,243 output
insertions. At the run-4 handoff alone the removed pass contained
362 records and 391 output positions. These operations can fund a
bounded verifier in their respective work classes. The current
continuation checker still needs a complete proof, including field
word costs. Index savings alone do not establish retirement.
[Index proof](../../spec/lean/proposals/termination-rollback-20261118/RecordIndexSeal.lean)

At the run-11 seal, the omitted pass has 368 record visits, 403
output positions and 59 field words in indexed paths. The detector
compares 17 demand rows with 27 field and field-exclusion words on
each side, one seed, 98 condition contributors and 22 NORMAL
Target rows. The retained record order also matches by reference.
Use these counts to bound each comparison class. They measure the
inputs to an allowance and do not charge the diagnostic trace
collection, state copying or helper proof against it.

The index change passed all 2,702 core tests and 467 JVM tests.
The project run isolates the joined index seal and keeps the
ordinary stopping rules. It matched every accepted location and
iteration checkpoint at the configured budgets.

| Project | Reached / completed / accepted | Wall (s) | Peak RSS (GiB) | Record visits / output positions removed |
| --- | --- | ---: | ---: | ---: |
| OWASP | run-11 / run-11 / run-11 | 232.562 | 9.551 | 2,526,160 / 2,620,205 |
| Conductor | run-8 / run-7 / run-7 | 1,128.843 | 10.088 | 1,299,283 / 1,367,408 |
| ThingsBoard | run-1 / none / none | 345.727 | 13.787 | 0 / 0 |
| Stirling-PDF | run-11 / run-10 / run-9 | 1,107.246 | 9.736 | 2,023,128 / 2,052,209 |

Conductor's fresh control peak was 9.944 GiB. The candidate's
10.088 GiB sample came during SARIF generation after the run-8
timeout. Its highest sampled engine RSS was 9.994 GiB. The most
recent post-GC heap before the two full-process peaks was 5,079
MiB in the fresh control and 5,091 MiB in the candidate. The
run-6 handoff took 2.663 seconds in the fresh control and 1.368
seconds in the candidate. These measurements record the RSS
difference and the work removed at the seal.

A same-binary Conductor control with the joined seal disabled
reached run-8, completed run-7 and accepted run-7. Both arms
reported the same seven locations. The JVM high-water mark was
10.048 GiB in this control, 0.040 GiB lower than the candidate.
The profiling launcher lost `JAVA_HOME` during the scan. The JVM
continued, and the reattached sampler recovered its kernel peak
and run-end evidence. The missing mid-run profile windows limit
the direct comparison of engine memory. The guarded candidate
uses native indexes for the full project scopes.

## Matched project runs

The comparison uses the same FULL mode, project models, rule set, field
limits, run-11 cutoff, heap budgets and source Gradle runner as the
original rule campaign. Report the latest reached, completed and
accepted iteration for each scan. Check the exact accepted locations,
wall time and peak memory against both native samples.

| Native repeat | Reached / completed / accepted | Wall time (s) | Peak RSS (GiB) | Outcome |
| --- | --- | ---: | ---: | --- |
| OWASP | run-11 / run-11 / run-11 | 225.123 | 9.483 | Run limit |
| Conductor | run-8 / run-7 / run-7 | 1,126.546 | 9.944 | Timeout |
| ThingsBoard | run-1 / none / none | 360.775 | 13.851 | Memory guard |
| ThingsBoard, quiet R35 control | run-1 / none / none | 334.259 | 13.661 | Memory guard |
| Stirling-PDF | run-11 / run-10 / run-9 | 1,108.888 | 10.167 | Timeout |

| Revised rule | Project | Reached / completed / accepted | Wall time (s) | Peak RSS (GiB) | Accepted locations added / removed |
| --- | --- | --- | ---: | ---: | ---: |
| R13, lazy maps | OWASP | run-11 / run-11 / run-11 | 235.568 | 9.520 | 0 / 0 |
| R13, lazy maps | Conductor | run-8 / run-7 / run-7 | 1,124.161 | 10.398 | 0 / 0 |
| R13, lazy maps | ThingsBoard | run-1 / none / none | 358.776 | 13.908 | No accepted report |
| R13, lazy maps | Stirling-PDF | run-9 / run-8 / run-7 | 1,114.082 | 10.474 | 0 / 0 |
| R13, direct first slot | OWASP | run-11 / run-11 / run-11 | 222.765 | 9.711 | 0 / 0 |
| R13, direct first slot | Conductor | run-8 / run-7 / run-7 | 1,120.120 | 9.955 | 0 / 0 |
| R13, direct first slot | ThingsBoard | run-1 / none / none | 346.918 | 13.766 | No accepted report |
| R13, direct first slot | Stirling-PDF | run-9 / run-8 / run-7 | 1,109.777 | 10.022 | 0 / 0 |
| R13, guard only | Stirling-PDF | run-9 / run-8 / run-7 | 1,108.907 | 9.634 | 0 / 0 |
| R13 with loop replay and C5 shortcuts | OWASP | run-11 / run-11 / run-11 | 226.516 | 9.493 | 0 / 0 |
| R13 with loop replay and C5 shortcuts | Conductor | run-8 / run-7 / run-7 | 1,125.731 | 9.796 | 0 / 0 |
| R13 with loop replay and C5 shortcuts | ThingsBoard | run-1 / none / none | 342.444 | 13.757 | No accepted report |
| R13 with loop replay and C5 shortcuts | Stirling-PDF | run-11 / run-11 / run-11 | 147.732 | 9.754 | 2 / 0 |
| R13 with loop replay and C5 shortcuts, repeat | Stirling-PDF | run-11 / run-10 / run-9 | 1,112.336 | 10.245 | 0 / 0 |
| R26 | OWASP | run-11 / run-11 / run-11 | 231.549 | 9.624 | 0 / 0 |
| R26 | Conductor | run-8 / run-7 / run-7 | 1,122.109 | 9.989 | 0 / 0 |
| R26 | ThingsBoard | run-1 / none / none | 354.520 | 13.862 | No accepted report |
| R26 | Stirling-PDF | run-11 / run-10 / run-9 | 1,109.202 | 9.881 | 0 / 0 |
| R35 | OWASP | run-11 / run-11 / run-11 | 244.586 | 9.783 | 0 / 0 |
| R35 | Conductor | run-8 / run-7 / run-7 | 1,120.726 | 10.029 | 0 / 0 |
| R35 | ThingsBoard | run-1 / none / none | 425.305 | 13.824 | No accepted report |
| R35, quiet repeat | ThingsBoard | run-1 / none / none | 341.559 | 13.807 | No accepted report |
| R35 | Stirling-PDF | run-11 / run-10 / run-9 | 1,111.679 | 10.212 | 0 / 0 |
| R36 | OWASP | run-11 / run-11 / run-11 | 229.537 | 9.644 | 0 / 0 |
| R36 | Conductor | run-8 / run-7 / run-7 | 1,121.517 | 10.392 | 0 / 0 |
| R36 | ThingsBoard | none / none / none | 387.622 | 13.313 | Prescan exception |
| R36, quiet repeat | ThingsBoard | run-1 / none / none | 333.918 | 13.761 | No accepted report |
| R36 | Stirling-PDF | run-11 / run-11 / run-11 | 147.997 | 9.575 | 2 / 0 |
| R41 | OWASP | run-11 / run-11 / run-11 | 229.524 | 9.627 | 0 / 0 |
| R41 | Conductor | run-8 / run-7 / run-7 | 1,120.073 | 10.128 | 0 / 0 |
| R41 | ThingsBoard | run-1 / none / none | 342.203 | 13.780 | No accepted report |
| R41 | Stirling-PDF | run-11 / run-11 / run-11 | 152.871 | 9.656 | 2 / 0 |
| Combined | OWASP | run-11 / run-11 / run-11 | 236.171 | 9.924 | 0 / 0 |
| Combined | Conductor | run-8 / run-7 / run-7 | 1,121.260 | 10.413 | 0 / 0 |
| Combined | ThingsBoard | run-1 / none / none | 340.592 | 13.911 | No accepted report |
| Combined | Stirling-PDF | run-11 / run-10 / run-9 | 1,108.815 | 10.174 | 0 / 0 |
| Combined with loop shortcuts | OWASP | run-11 / run-11 / run-11 | 225.569 | 9.618 | 0 / 0 |
| Combined with loop shortcuts | Conductor | run-8 / run-7 / run-7 | 1,121.578 | 9.772 | 0 / 0 |
| Combined with loop shortcuts | ThingsBoard | run-1 / none / none | 338.032 | 13.744 | No accepted report |
| Combined with loop shortcuts | Stirling-PDF | run-11 / run-10 / run-9 | 1,109.473 | 9.805 | 0 / 0 |

R26 and R35 matched the native progress checkpoints and accepted
locations on all four projects. The quiet ThingsBoard comparison
resolved the first R35 run's engine slowdown.
R36 matched the ThingsBoard checkpoint in its repeat. A later kernel
high-water comparison checks the Conductor RSS spike below. The lazy-map,
direct-slot and guard-only R13 builds all lost two completed
Stirling-PDF iterations. The loop-work variant recovered progress
in its first scan and in the repeat with a larger workload. It also
matched the other three project checkpoints.
The local R41 checker still needs a complete native continuation
proof for the compiled helper. The run-level witness established
above uses a different stopping condition. The compaction
measurements establish savings for the independent compaction change.

The OWASP R13 run is between the two native samples on both wall time
and peak RSS. Its run-11 handoff retains 975 pairs. The two native
samples retain 1,111 and 1,153. Both native samples and R13 accepted the
same 2,633 locations.
R26 also kept those locations and 975 outgoing pairs. Its closed-root
cleaner is ineligible in this scan. The handoff count alone does not
attribute the drop to R13.
The direct-slot R13 revision matched the accepted OWASP locations and
run-11 checkpoint. Its peak RSS stayed within the two native samples.
On ThingsBoard it reached the same run-1 memory guard. It spent
191.902 seconds in the engine versus 190.267 in the fresh control.

R26 matched every native progress checkpoint and all accepted
locations. The Conductor and ThingsBoard RSS increases against the
fresh repeat were 0.045 and 0.011 GiB, smaller than the differences
between the native samples on those same projects. The original
budgets still leave three projects incomplete. There is no
higher-heap completion result for this prototype yet.

R35 reached the same ThingsBoard memory guard at run-1. It processed
4.014 million events, compared with 4.237 million in the fresh control.
Its engine took 244.100 seconds versus 190.267. The cleaner rule was
ineligible for all project scopes. In the 30-second CPU profile,
ordinary cleaner frames accounted for 48 of 24,076 samples versus
475 of 42,389 in the control. Across the command, young and full GC
pauses took about 10.7 seconds longer. These samples do not attribute
the longer time to the selected cleaner transfer. The R36 core
and R13 JVM validation builds overlapped the first part of this
scan. The first telemetry sample above one million events was
40 seconds later than in the fresh control. The same lag held
through three million events. The quiet repeat without concurrent
validation builds reached the same memory guard in 183.937 engine
seconds versus 184.278 in its paired native control. The two runs
recorded 3.973 and 3.982 million events, respectively. Peak RSS was
13.807 versus 13.661 GiB, within the three native ThingsBoard samples.
The same R35 pass kept every accepted location and matched the last
completed runs on all four projects. On Stirling-PDF, `decodeMimeHeader`
issued 6,388,941 boundary offers in run-9, versus 4,347,234 in the
fresh control. Run-9 still completed, and run-10 completed before
both scans timed out in run-11. The selected R35 cleaner was
ineligible here as well.

The R36 ThingsBoard scan spent its 324-second prescan allowance
before reaching run-1. The legacy workers then failed to join in
the 30-second cancellation window. The bidirectional engine did
not start. This outcome failed the configured progress comparison.
A quiet repeat used the same heap, timeout and patch. It reached
the run-1 memory guard with 3.978 million events and a 182.422-second
engine time. The fresh native control reached the guard with 4.237
million events and a 190.267-second engine time. R36 is restricted
to runs after run-1.

R36 completed run-11 on Stirling-PDF with the same 32 confirmed
locations and two provisional locations at the cutoff. The native
repeat accepted run-9 and did not reach that cutoff. The R36 branch
recorded zero activations through run-11. In run-9,
`decodeMimeHeader` processed 16,419 boundary offers with no cuts.
The native repeat processed 4,347,234 offers and made 1,899,974
cuts. The earlier R36 prototype also reached run-11 with zero
activations and zero cuts at this method in run-9. This is evidence
of a distinct loop workload across executions, with no measured
deep-cleaner work to explain it.
On Conductor, where the new branch also stayed inactive, the run-7
post-pause heap peak was 7,304 MiB versus 7,307 MiB in the native
repeat. The process peak was 10.392 GiB versus 9.944 GiB. These
samples do not show growth in the retained post-pause JVM heap for
that run.

The isolated R36 Conductor repeat captured the kernel high-water
mark through shutdown. The matched native scan reached run-8,
completed run-7, and accepted the same seven confirmed locations
as R36. Wall time was 1,123.221 s natively and 1,127.192 s with R36
at the same timeout. Peak RSS was 10.236 versus 9.993 GiB.
The 10.392 GiB sample from the first R36 cost build did not recur.
R36 activated zero times through run-8. This closes the observed
large-scope RSS regression in the isolated repeat. The synthetic
deep-cleaner probes exercise the active branch and show its
allocation savings separately.

R41 used the caller-check guard on the full OWASP project. It attempted
zero retirements. The independent compaction shortcut bypassed 14,909
C5 index insertions out of 45,929 projected rows through run-11.
The measured compaction steps took 0.256 seconds versus 0.289 in
the native repeat, which projected 46,157 rows. Both scans kept all
2,633 accepted locations.

On Conductor the R41 build bypassed 216,598 index insertions through
run-7, including 215,127 in the run-2 handoff. It made zero retirement
attempts. The run-8 timeout and the seven accepted locations match the
native repeat. RSS peaked at 10.128 GiB in run-7, above the fresh
native peak of 9.944 GiB. Run-7 heap measured immediately after GC
pauses peaked at 7,304 MiB versus 7,307 MiB and had medians of 5,046
and 5,067 MiB, respectively. Post-pause heap excludes non-heap process
residency and is a sampled measurement. In run-6, engine time was 374.7 seconds
and sampled process CPU was 900.06 seconds, versus 489.9 and 1,183.71
in the fresh native repeat. These are resource results for the
compactor build. The useful R41 proof was ineligible in both project
scans.

On ThingsBoard, the R41 build reached the run-1 memory guard before
the first handoff. It recorded 3.935 million events, versus 4.237
million in the fresh control. The run-1 engine took 185.102 seconds
versus 190.267. These two incomplete runs exercise neither R41 nor
the compaction change.

Stirling-PDF completed run-11 and retained all 32 confirmed locations.
The two extra locations were provisional at the cutoff. The build
bypassed 133,135 C5 index insertions through run-11 and attempted no
retirements. Run-9 `decodeMimeHeader` recorded 38,509 boundary offers
and zero cuts, also seen in other fast executions. The native repeat
recorded 4,347,234 offers. This gap is much larger than the measured
work avoided by the compaction shortcut.

The combined OWASP scan preserved all 2,633 locations through
run-11. One sample rose to 9.924 GiB around the run-9 boundary,
between adjacent samples of 9.676 and 9.706 GiB. The native peak
range was 9.483–9.781 GiB. In run-9, the combined post-pause
heap peaked at 3,507 MiB, versus 3,784 MiB in the fresh native
repeat. The excess process sample still needs a matched repeat
before classifying the combined memory result.
The combined Conductor scan kept the seven accepted locations
and completed run-7 before timing out in run-8. Its 10.413 GiB
RSS peak occurred in run-7. The run-7 post-pause heap maximum
was 7,201 MiB versus 7,307 MiB in the fresh native control.
Two consecutive RSS samples rose by 480 MiB above the adjacent
samples and returned to 9.944 GiB. The same 480 MiB jump occurred
in the first R13 revision. The control's peak was a one-sample
224 MiB jump. The process samples leave the allocation category
unidentified. The queued same-binary comparison records anonymous,
file-backed and private-dirty residency around those samples.
The loop-shortcut Conductor scan reproduced a 224 MiB run-7 spike.
Its `smaps_rollup` samples put the full increase in anonymous
private-dirty pages. File-backed residency stayed at 0.231 GiB
and the extra pages disappeared within about one second. The
samples identify the category for this execution. They leave the
mapping owner and the larger spikes open.
The combined ThingsBoard scan reached the run-1 memory guard after
4.074 million events and 189.043 engine seconds. It reached the
same configured checkpoint as both native samples.
The combined Stirling-PDF scan timed out in run-11 after completing
run-10 and kept all 32 accepted locations. Its run-9 took 167.580
seconds, with 1,933,594 offers at `decodeMimeHeader`. This workload
matches the smaller cut count observed with R26. The run-11 timeout
sample contains 4,425 CPU samples, including 46.26% under loop
restriction and 12.52% under the prepared C5 programs. The samples
overlap. The largest owner submitted 7,033,313 boundary offers
before the interruption. The combined build matches all four native
progress checkpoints. Its observed memory increases on OWASP and
Conductor still need attribution.

The combined run with the loop shortcuts kept all 2,633 OWASP
locations through run-11. Peak RSS was 9.618 GiB, within the two
native samples. This run did not reproduce the previous combined
build's isolated 9.924 GiB spike.
The same build matched Conductor through completed run-7 and
kept all seven accepted locations. Its 9.772 GiB process peak
was within the native sample range. The run-7 mapping sample
captured a brief 96 MiB anonymous private-dirty increase with
steady file-backed residency. It did not reproduce the earlier
480 MiB spike.
ThingsBoard reached its run-1 memory guard with a 13.744 GiB peak,
within the native samples. The combined build had no completed
iteration at that budget.
On Stirling-PDF the same build timed out in run-11 after completing
run-10. It kept all 32 accepted locations. Run-9 took 141.997
seconds, versus 167.580 in the earlier combined build. The dominant
context processed 1,933,064 versus 1,933,594 offers and made the
same 837,747 cuts. It skipped 9,670,433 saved DATA replays in run-9
and 43,963,058 before the run-11 timeout. The four configured
comparisons keep the native progress and accepted sets. Each
loop-assisted project peak fell within the native sample range.

### Guarded stop-proof build

The compiled project build checks the root bound before enabling
the paid proof. Large scopes use the existing two-phase record
index and keep no proof snapshot. The small compiled helper and
synthetic tests exercise the paid path independently.

The full OWASP scan reached, completed and accepted run-11 with
all 2,633 native locations and 9.659 GiB peak RSS. Its 279.972 s
wall time includes a concurrent prototype build. Run-7 through
run-11 took 42.8 s versus 21.0 s in the preceding combined build.
Median one-minute host load during that phase was 5.76 versus 2.36.
The guarded scan also carried 1,153 forward demand pairs versus
975 in the preceding combined build. The fresh native control
had 1,153. The guarded repeat with no simultaneous validation
build reached run-11 in 233.795 s with all 2,633 locations and
9.729 GiB peak RSS. It retained 1,111 forward demand pairs at
run-11. The repeat falls within the earlier native wall-time
and RSS ranges. The immediately following native scan reached
run-11 in 225.719 s with 9.503 GiB peak RSS. The guarded engine's
run-1 took 81.130 s versus 80.209 s. Run-9 took 6.079 s versus
3.378 s. The median host loads across the two commands were 3.92
and 2.87 respectively. The original 280 s result did not recur.

Conductor reached run-8, completed run-7 and accepted run-7 with
all seven locations. Run-6 took 387.227 s versus 489.909 s in
the fresh native control. On entering run-8, the maximum RSS so
far was 9.937 GiB versus the control's 9.944 GiB. The guarded
build spent another 145 s in run-8 before the same enclosing
timeout. Its engine peak of 10.056 GiB occurred 1.1 s into run-8.
Its full-process peak of 10.079 GiB followed the timeout. Wall
time was 1,131.595 s. The matching checkpoint supports progress
parity. The last GC pause before the run-8 startup peak left
5,088 MiB in the guarded build versus 5,148 MiB during the native
startup window. The corresponding frontiers were 85,320 and
84,985 demand rows. The process memory comparison remains open.

The next native Conductor scan reproduced a startup spike 1.47 s
into run-8. A half-second `/proc` sampler saw 10.185 GiB RSS,
including 9.954 GiB anonymous memory and 0.231 GiB file-backed
memory. The benchmark's one-second sampler had peaked at
9.966 GiB by that point. The kernel high-water mark records
the spike even when individual RSS samples miss it.

The generation-based build and that native control both reached
run-8, completed run-7 and kept all seven accepted locations.
Their wall times were 1,129.496 s and 1,123.221 s. The generation
build peaked at 10.503 GiB, 3.14 s into run-8. The native peak
was 10.236 GiB. The two peaks exceeded their samples from the
preceding completed checkpoint. A separate set of mapping samples
from the generation build shows 204 MiB of later anonymous growth
during report completion, with Java heap RSS fixed at 8,184 MiB.
The run-8 peak occurred before those mapping samples. The next
prototype joins the record-index rebuild outside the proof scope
to remove the redundant handoff allocations. It measures mappings
at run-8 startup.

The joined build reached run-8, completed run-7 and kept all seven
locations. It took 1,123.335 s versus 1,123.221 s in the same
native control. Its kernel high-water mark was 9.980 GiB versus
10.236 GiB. Run-6 engine time fell from 400.729 s to 375.689 s.
The run-7 handoff took 0.579 s versus 0.919 s. The highest
engine-phase sample was 9.897 GiB, and the run-8 startup sample
was 9.803 GiB. The larger startup peak did not recur after the
joined rebuild in this scan. Its startup mapping held 1,616 MiB
in unnamed regions outside the Java heap. The earlier generation
build held 1,853 MiB there at its steady run-8 sample. Both mapped
about 8,185 MiB of resident Java heap.

The first joined test run activated the local retirement diagnostic
and both stopping proofs together. It moved one acyclic stop to
run-7 and stopped six recursion controls early. The measured profile
selects one proof per configured root scope. Its observer walk
rejects active call cycles. The scoped joined build passed all
2,708 core and 468 JVM tests. Both useful acyclic cases and the
nested replay case stop at run-5. The recursion controls preserve
their original run outcomes, and the compiled helper stops at
run-11 with both confirmed locations.

The scoped joined OWASP scan reached run-11 with the same 2,633
locations. It took 230.918 s and peaked at 9.584 GiB. The quiet
native control took 225.719 s at 9.503 GiB. The run-9 engine took
6.611 s versus 3.378 s. Both runs performed 2,653 saved replay
invocations, inspected the same number of candidates (12,488) and
accepted the same number of raw initial keys (1,561). They processed
158,277 and 156,325 packets respectively. GC pauses took roughly
0.10 s in each run.

The run-9 allocation samples put more weight in ordinary trie
operations. `IdentityHashMap` allocation samples represent 2.56 GB
in the joined scan and 0.79 GB in the native scan. The largest joined
stacks are graft during aligned FLOW coverage, structural trie
equality during canonicalization and map traversal during protection
transport. These are weighted samples. They locate allocation
sites independently of the replay and admission counts. The next
prototype avoids comparison scratch on a single-child prefix and
the postorder memo on a childless trie.

Stirling-PDF reached run-11, completed run-10 and accepted run-9
with the same 32 locations. Run-9 took 145.300 s versus 402.995 s
in the fresh native control. The enclosing timeout left wall time
at 1,110.070 s. Peak RSS was 10.096 GiB versus 10.167 GiB. The
match measures the same accepted output with the loop replay and
C5 shortcuts enabled.

ThingsBoard reached the run-1 memory guard after 160.640 engine
seconds, with no completed or accepted run. It took 315.683 s
overall and peaked at 13.862 GiB. This scan omitted the heap dump
to keep the experiment within available disk space. The native
repeat with the same capture settings reached the run-1 guard
after 159.106 engine seconds. Its wall time was 314.626 s and
peak RSS was 13.943 GiB. Neither scan accepted a report.

### Scoped joined build

The final joined profile enables changes to FULL transfer for R13,
R26/R35 and R36, and one selected R41 proof per small scan.
The project scans were outside both stopping-proof scopes. They still
exercise common transfer, handoff compaction and the single saved-index
rebuild. The selected-entry and synthetic tests exercise the stopping
proofs separately at run-101. The prototype limit audit assumes one
scan per process. The spec requires a scan-owned audit before
adoption in a runner that can analyze scans concurrently.

| Project | Reached / completed / accepted | Accepted confirmed locations | Native → prototype wall (s) | Native → prototype peak RSS (GiB) |
| --- | --- | ---: | ---: | ---: |
| OWASP | run-11 / run-11 / run-11 | 2,633 | 225.719 → 230.918 | 9.503 → 9.584 |
| Conductor | run-8 / run-7 / run-7 | 7 | 1,123.221 → 1,123.335 | 10.236 → 9.980 |
| Stirling-PDF | run-11 / run-10 / run-9 | 32 | 1,108.888 → 1,109.532 | 10.167 → 10.072 |
| ThingsBoard | run-1 / none / none | No accepted report | 314.626 → 351.769 | 13.943 → 13.761 |

The accepted location multisets and confirmation counts agree in all
three completed comparisons. The native OWASP repeats span 225.123 to
266.022 s and 9.483 to 9.781 GiB. The joined build lies in both ranges.
Its run-9 increase warrants a separate comparison because it recurred
in the guarded build. Conductor shows a lower kernel high-water mark
and a faster completed run-6. Stirling-PDF completes run-9 in 149.265 s,
from 402.995 s in the selected control. Both Conductor and Stirling-PDF
end at the configured timeout.

ThingsBoard reached the configured run-1 memory guard at 159.106 s
in the selected native engine and 184.282 s in the joined engine.
The last recorded event counts were 3.939 and 3.999 million. The
full-process GC logs account for 46.013 and 52.671 s of pauses.
Median one-minute host load was 5.53 and 7.06. Earlier native runs
reached the same guard at 184.269 and 190.267 engine seconds.
The new same-capture pair reproduced the gap.

| ThingsBoard repeat | Reached / completed / accepted | Wall (s) | Run-1 engine (s) | Peak RSS (GiB) |
| --- | --- | ---: | ---: | ---: |
| Native | run-1 / none / none | 334.731 | 169.786 | 13.737 |
| Scoped joined | run-1 / none / none | 383.979 | 200.071 | 13.814 |

The joined run consumed about 2,058 sampled engine CPU seconds
versus 1,882 in the native run and recorded fewer events before the
guard. Median host load during the engine was 15.00 versus 10.95.
Total GC pauses were 55.465 versus 47.413 s. Higher host load explains
some wall time. At the three-million-event sample, estimated process
CPU increased from 1,153 to 1,346 s in the first pair and from
1,262 to 1,506 s in the repeat. Events can contain different work.
Both runs stop before the first handoff, so the repeat establishes
a run-1 cost gap for this profile. It leaves the before-handoff
cause open.

The next isolated change restores the earlier direct first-result
slot in the joined prototype. The joined profile eagerly allocates
two ordered maps per result collector. In the
ThingsBoard repeat, 956 JFR allocation samples have a result
collector frame. The weighted totals include 3.38 GiB for
`LinkedHashMap`, 1.73 GiB for its entries and 1.32 GiB for its
entry sets. The sample counts locate a common allocation site and
do not measure how much the new collector will save.
The direct slot preserves the same callback order and merge operands.
It removes those maps for a single canonical key. The earlier R13
prototype already tested this layout and its native correspondence.
The new worktree changes only the operation collector, so the
comparison can test whether this saving closes the run-1 gap.

The direct-slot pilot reached the same run-1 memory guard after
166.920 engine seconds. It took 339.764 s overall, peaked at
13.901 GiB, and finished no iteration. It recorded 4.076 million
events, up from 3.733 million in the joined repeat. The closest
native repeat reached the guard in 169.786 engine seconds with
3.999 million events. Median host load was 11.28 for the direct
slot and 10.95 for that native run. At three million events,
the sampled CPU estimates were 1,254 and 1,262 seconds. The
direct-slot pilot recovers the previous early workload loss
at a similar host load. GC pauses total 45.821 s, down from
55.465 s in the joined repeat. Its peak RSS is inside the native
range. The pilot has 526 allocation samples with a result
collector frame. With that frame among the top six, no sample
is a `LinkedHashMap`, map entry, map entry set or Boolean array.
These samples corroborate the removal of the common allocations.
The full comparison repeats ThingsBoard and uses this same source
patch for the other projects.

| Final ThingsBoard pair | Reached / completed / accepted | Wall (s) | Run-1 engine (s) | Peak RSS (GiB) |
| --- | --- | ---: | ---: | ---: |
| Native | run-1 / none / none | 340.759 | 167.232 | 13.651 |
| Direct slot | run-1 / none / none | 355.932 | 187.746 | 13.829 |

The later pair records 4.028 million native events and 4.006 million
with the direct slot. The prototype took 1296 sampled CPU seconds
to reach three million events, versus 1224 natively. Full-process
GC pauses were 52.589 versus 46.992 s. The direct slot reduced the
earlier gap at common work and did not close it in this pair.

The next candidate bypasses protection transport at a field-limit
operation that cannot cut a fully protected packet. The late ThingsBoard
allocation profile has 2.97 GiB of weighted samples under field-limit
callbacks with protection transport or mask intersection on the stack.
The count is inclusive. A bounded packet can deliver its original
mask and membership directly. The next worktree applies only this
additional limit optimization to the direct-slot prototype.

The bounded-limit build passed 35 focused tests. At the ThingsBoard
run-1 guard, wall time was 318.621 s versus 319.670 s in the paired
native scan. Engine time was 164.436 versus 162.993 s. Both recorded
about four million events. The time to the three-million-event
sample was 115.16 versus 114.88 s. Sampled process CPU to that
point fell from 1,184 to 1,169 s. Peak RSS was 13.848 versus
13.563 GiB. The time gap closed in this pair. The native scan
had the lowest peak RSS among the measured ThingsBoard controls.
The memory comparison still needs a repeat or a stronger cost fix.

The whole-protection trial passed 36 focused tests. It reached
the same ThingsBoard run-1 guard with 3.993 million events versus
3.988 million natively. Its peak RSS was 13.741 versus 13.796 GiB.
Its run-1 engine took 195.907 versus 158.964 s and used about
1,372 versus 1,148 sampled CPU seconds by three million events.
Median host load during these runs was 13.39 versus 8.38.
This pair did not demonstrate time parity for whole-protection
replay. Keep that worktree as a separate experiment.

The next prototype starts from the bounded-limit build and
removes the trial routing and queue hooks. An eligible closed
pair records one accepted non-start post per runner at the
channel admission. This also covers direct deliveries that the
router never sees. The standard router and dequeue loop have
their native structure. The proof uses the recorded set of
runners with accepted posts. The compiled helper and an
alternating-order ThingsBoard pair test this change.

The routing build passed 35 focused tests. The selected compiled
helper stopped naturally at run-11 with both confirmed locations.
It recorded one actual admitted root and one effective unit,
with no foreign non-start posts. The native helper reached run-101.
The same routing build passed 2,709 core tests and 468 JVM tests,
with zero failures, errors or skips.

In the ThingsBoard pair the routing build ran first. Both reached
the run-1 memory guard with no accepted report. The prototype took
153.474 engine seconds and 314.843 s overall. The native run took
180.985 engine seconds and 336.802 s overall. Peak RSS was
13.835 versus 13.847 GiB. At three million events, sampled engine
CPU was 1,126 versus 1,326 s and the elapsed engine time was
111.69 versus 129.12 s. Median host load was 11.39 and 13.97.
The pair compares the complete run-1 profile under the original
budget. The reverse-order pair used a native run first.

| Routing profile on ThingsBoard | Native engine (s) | Prototype engine (s) | Native peak RSS (GiB) | Prototype peak RSS (GiB) |
| --- | ---: | ---: | ---: | ---: |
| Prototype first | 180.985 | 153.474 | 13.847 | 13.835 |
| Native first | 152.584 | 155.136 | 13.802 | 13.796 |

The native-first run used 1,195 sampled CPU seconds to reach three
million events, versus 1,220 with the prototype. Median host load
was 8.93 and 8.95. The wall times were 306.672 and 309.625 s.
Both reached the run-1 guard with about 3.95 million events. End-to-end
timing and memory stayed within the variation measured across the
native controls. The 25–30 s engine increases seen with the earlier
joined build did not recur in either order.

The routing project's OWASP scan reached, completed and accepted
run-11 with the same 2,633 confirmed locations. Wall time was
234.884 s and peak RSS was 9.639 GiB, within the observed native
ranges. The run-9 engine took 3.315 s in this build and 3.378 s
in the matched native scan. The earlier run-9 increase did not
recur.

The routing project's Conductor scan reached run-8, completed
run-7 and accepted the same seven confirmed locations. Wall time
was 1,124.085 versus 1,123.221 s. Run-6 took 385.328 versus
400.729 s. During the first 60 seconds of run-6 the sampled
post-pause heap peaked at 6,661 versus 7,355 MiB. The medians were
4,838 and 4,860 MiB. The process high-water mark was 10.392 versus
10.236 GiB. It came from a short anonymous-residency spike during
run-7. File-backed RSS stayed near 0.230 GiB. A native Conductor
repeat with the same quarter-second sampler reached run-8, completed
run-7 and accepted the same seven confirmed locations. It used
1,123.350 s and reached 10.292 GiB during shutdown. Both scans used
the same recorded inputs and instrumentation settings. The routing
build's first peak was 0.100 GiB above this native control.
The routing repeat reached run-8, completed run-7 and accepted
the same seven confirmed locations. It used 1,121.809 s, with
10.010 GiB peak process RSS and no sampled outlier. The native
repeat used 1,123.350 s and 10.292 GiB. Run-6 took 370.317 s
in the routing repeat and 372.986 s in the native repeat.
The first routing build's run-7 peak did not recur.

Stirling-PDF run-9 took 347.111 s in the routing build, versus
402.995 s in the native control. The largest loop owner processed
4,375,190 boundary offers and 1,931,956 cuts. The native owner
processed 4,347,234 offers and 1,899,974 cuts. The routing and
control runs were in the same high-workload range at this owner.
The read-only observer skipped 21,367,156 saved DATA replays.
Both scans timed out in run-11, completed run-10 and accepted
run-9 with the same 32 confirmed locations. Peak RSS fell from
10.167 to 9.903 GiB. Wall time was 1,108.888 versus 1,109.776 s
at the same timeout.

The selected profile preserved the accepted locations and completed
checkpoints on the four configured workloads. The comparisons found
no reproducible time or memory increase at those resource budgets.
Stirling-PDF's completed run-9 was 55.884 s faster. The whole-project
OWASP scan still reached its run-11 limit. The selected helper used
the run-101 test limit and stopped at run-11 under the certificate.
Conductor and Stirling-PDF reached their configured timeouts.
ThingsBoard reached the memory guard in run-1 in both orders, so
this comparison establishes parity at the guard.

The direct-slot OWASP run reached, completed and accepted run-11.
It kept exactly the same 2,633 confirmed locations. Wall time
was 232.065 s and peak RSS was 9.639 GiB, within the observed
native ranges. Run-9 engine time was 4.879 s versus 6.611 s in
the joined build and 3.378 s in the matched native control.

The direct-slot build reached Conductor run-8, completed run-7 and
accepted the same seven confirmed locations. Run-6 took 390.645 s
versus 400.729 s natively. Wall time at the same timeout was
1,125.174 versus 1,123.221 s. Engine RSS peaked at 9.948 GiB.
The process high-water mark reached 10.294 GiB during shutdown,
against the native control's 10.236 GiB. The repeat matched
all seven confirmed locations and the same checkpoints. Its
whole-process high-water mark was 10.108 GiB and its engine
peak was 9.930 GiB. It completed run-6 in 388.704 s. Wall time
was 1,136.717 s at the same timeout. The earlier 60 MiB shutdown
excess did not recur with the same kernel measurement.

Stirling-PDF reached run-11, completed run-10 and accepted run-9
with the same 32 confirmed locations. Peak RSS fell from 10.167
to 9.748 GiB at the same timeout. Run-9 engine time fell from
402.995 to 146.674 s. The largest `decodeMimeHeader` owner
processed 1,933,997 boundary offers and 837,747 cuts, in the same
workload range as the joined loop-shortcut build.

#### Trie scratch trial on OWASP

The trie-only change on top of the joined prototype passed 81 focused
tests and reached, completed and accepted run-11 with the same 2,633
confirmed locations. The run-9 engine fell from 6.611 to 3.898 s
with no input configuration changes. The native control took 3.378 s.
The trie build's run-1 engine took 99.526 s, versus 78.830 s in the
joined build and 80.209 s in the native control. End-to-end wall
increased from 230.918 to 264.186 s and peak RSS from 9.584 to
9.780 GiB. Keep the joined prototype for the project acceptance
comparison. The trie trial establishes a possible run-9 saving.
Adoption needs a separate all-run cost result.

### R13 memory attribution on Conductor

| Run-6 metric | Native repeat | Previous R13 | Revised R13 |
| --- | ---: | ---: | ---: |
| Engine seconds | 489.909 | 388.747 | 401.299 |
| Sampled process CPU seconds | 1,183.71 | — | 960.59 |
| Loop boundary offers | 25,204,141 | 24,849,844 | 24,994,032 |
| Median post-pause Java heap (MiB) | 5,397 | 5,346 | 5,381 |
| Median RSS (GiB) | 9.683 | 9.966 | 9.938 |
| Peak RSS during run-6 (GiB) | 9.750 | 9.969 | 10.398 |

The revised transfer keeps all seven accepted locations through run-7
and does less observed boundary work than the native repeat. The
process RSS remains higher. Three run-6 samples exceed 10.1 GiB.
The R36-only scan reached a similar process peak, 10.392 GiB, with
zero deep-cleaner activations. A peak near 10.4 GiB is therefore
possible without the R13 transfer change. It still needs the paired
memory comparison.
The direct-slot revision reached the same run-8 timeout and kept
all seven accepted locations. Its peak RSS was 9.955 GiB, 0.011 GiB
above the fresh native repeat. In run-6 the peak was 9.856 GiB and
the engine took 382.0 seconds. Its post-pause heap median was
5,416 MiB, with a maximum of 7,346 MiB. These measurements narrow
the earlier RSS difference. A same-binary strict-on/off prototype
can separate the transfer from process-memory variation if a
larger difference returns.
With the loop shortcuts, Conductor kept all seven locations and
matched the run-7 completion checkpoint. Peak RSS was 9.796 GiB.
Its run-6 engine and process CPU times were 412.0 and 1,013.72
seconds, versus 489.9 and 1,183.71 in the fresh native repeat.

### R13 workload on Stirling-PDF

The revised scan kept the 32 accepted locations. It timed out in
run-9. The native repeat completed run-10 and accepted run-9.
The revised scan fails the progress comparison.

| Run-7 metric | Native repeat | Original R13 | Lazy maps | Direct first slot |
| --- | ---: | ---: | ---: | ---: |
| Engine seconds | 22.841 | 9.540 | 111.078 | 73.313 |
| `decodeMimeHeader` boundary offers | 413,815 | 170,608 | 1,728,209 | 1,420,042 |
| `decodeMimeHeader` boundary cuts | 149,682 | 61,578 | 683,249 | 565,841 |
| `decodeMimeHeader` prepared C5 queries | 1,410,538 | — | 5,666,231 | 4,682,539 |
| `decodeMimeHeader` live input groups | 111 | 65 | 133 | 94 |

The two R13 kernels select the same ancestor results under the same
input. The revised scan processed more loop offers. Its run-9
profile placed 51.7% of CPU samples under loop observation or
restriction. A separate experiment tests reuse for an exact duplicate
boundary result. It keys the result by the frozen policy, complete
route, original premise and raw packet.

Stirling-PDF with the R26 guard ineligible reached run-11. Its
run-7 took 10.988 seconds and submitted 200,502 loop boundary offers
in `decodeMimeHeader`. The native repeat submitted 413,815. These
counts vary even when the selected cleaner never changes a transfer.

Three unchanged scans also differ in run-9. Their top loop owner
recorded 6,389,744, 4,347,234 and 4,375,223 boundary offers. R35
recorded 6,388,941 with the same 2,830,587 cuts as the first native
sample. R13 and the inactive R26 variant recorded 1,913,082 and
1,933,963 offers, with the same 837,747 cuts. These repeated cut
counts identify several observed workload shapes. A single macro
sample cannot show whether an isolated transfer change causes one
shape to replace another.

The direct-slot version also entered the heavier run-7 workload.
A later timeout in run-9 left it at the same completed run-8
checkpoint as the lazy-map build. Its top loop owner issued
12,368,308 boundary offers and 47,297,282 prepared C5 queries before
the timeout. All 32 accepted locations agree with the control.
A guard-only comparison uses the same strict transfer and scalar
reference with the native result collector. It separates the R13
transfer from a change to allocation across all result-collector
callers. The guard-only native suite passed all 147 tests and
kept the run-3 stop. Its Stirling-PDF run-7 took 93.541 seconds,
with 1,728,510 offers and 683,249 cuts at `decodeMimeHeader`.
The lazy-map build had the same cut count. The collector change
is unnecessary for this high-workload regime to occur.
The guard-only build then timed out in run-9 after completing
run-8. Its largest loop owner had 9,958,588 boundary offers and
52,476,501 prepared C5 queries. It retained all 32 locations.
The direct-slot and R41 scans each handed off 973 pairs after run-7.
Both recorded 11,551 engine events and 32 observations. Their
largest `decodeMimeHeader` owners performed 1,420,042 and 35,330
loop boundary offers, respectively. Frontier and event counts do
not expose the repeated boundary work within one owner.

A second prototype reuses the pure restriction result after the global
cut, keyed by enclosing scope, loop, full original premise and bounded
packet. Each physical delivery still uses its own native completion
store. The observer reads frozen demand, records, ports and exit
metadata. A third prototype skips a saved DATA replay when the enclosing
plan has no output program for its result base. This check uses the
existing same-direction guard and also applies at the method boundary,
where exit metadata can only remove data. The planned comparison
measures avoided restriction evaluations and saved replay separately.

The prepared lookup in the third prototype also validates the original
against the plan's exact templates without constructing another list of
patterns. The sampled selected FLOW query allocates 6,096 bytes against
6,360 in the control. The rejected-base query allocates zero against
240 bytes. Native prepared-output and demand-plan tests pass.

A further experiment reuses the C5 answer for overlong FLOW facts
in the read-only loop observer. Use it when the plan has one output
program, the program’s demanded head is shorter than its cut, and
every leaf in the raw packet is strictly beyond the same counted
cut prefix. The prefix and its next field relative to the selector
then determine the native match. The cut removes the suffix and
field mask. Layer becomes DEMAND and the mark mask stays in the
cache key. The observer still applies the normal program to the cut.
Test cases with an uncut sibling or changed mark mask exercise the
ordinary query or a new lookup.

In the local workload, 128 distinct long field chains all cut to
the same prefix. The prepared query allocated 6,240–6,242 bytes
per call. The scope-local reuse case allocated 56 bytes and kept
the same output for all 128 chains. The real-project comparison
still needs to establish how often Stirling-PDF meets these conditions.
The revised check compares a cached prefix directly against the
incoming trie and builds a key only after an eligible miss. A second
probe checks one miss and 127 hits with FLOW inputs. It records about
5,392 bytes without reuse and 40–56 bytes with reuse. Native
prepared-output and loop boundary tests pass on that version.

In the Stirling-PDF comparison this build completed run-11 in
147.732 seconds. It kept all 32 confirmed locations and added two
provisional locations at the cutoff. The loop counters recorded
576,322 saved DATA replays skipped and 7,804 prefix cache hits
from 19,519 eligible queries. The largest `decodeMimeHeader` context
had 38,259 boundary offers, zero cuts, 146,710 skipped replays
and zero prefix hits in run-9. It was in the lighter workload
seen in the R36 and R41 scans. The run verifies the shortcuts can
coexist with the R13 fix and identifies the skipped work. It does
not show that prefix reuse can rescue the heavy workload.

The repeat timed out in run-11 after completing run-10. It kept
all 32 accepted locations and matched the native progress checkpoint.
In run-9 it processed 1,912,489 offers and 837,747 cuts
at `decodeMimeHeader`. The original R13 build had 1,913,082 offers
and the same 837,747 cuts. The repeat skipped 9,580,217 replays
at that owner, with zero prefix hits there. Run-9 engine time was
142.060 seconds versus 171.459 with the original R13 build. The
interrupted run-11 processed 7,934,248 offers at the same owner
and skipped 43,288,521 replays. The prefix cache again had zero
eligible lookups at this owner.

## Reproduction

The detached prototypes, source patches, native test receipts and
project measurements are in the archive directory
`demand-refinement-rule-prototypes-20261118.n00xyl/`. The comparison
scripts record the model and build settings separately from the
measurements. `useful-cost-closure-joined/verified-source.patch` is
the scoped joined build. Its `closure-receipts.json` records the
focused tests and compiled stop proofs, and `full-with-scoped-join.log`
records the complete core and JVM unit suites.
`latest-useful-cost-comparison.json` compares the project inputs,
checkpoints and accepted locations. Each project directory has its
analyzer log and measurement manifest. `R41-index-seal/recovered-index-control.json`
records the Conductor RSS recovery for the isolated compaction work.
`R36-cost/conductor-repeat-comparison.json` records the exact locations
and kernel high-water check for isolated R36.
`useful-cost-closure-trie/verified-source.patch` and
`project-comparison-useful-cost-closure-joined.json` in the same directory
record the independent trie trial.
`useful-cost-closure-inline/verified-source.patch` adds the direct
result slot. `thingsboard-run1-progress-comparison.json` records
run-1 event milestones, CPU estimates and GC time for each fixture.
`useful-cost-closure-routing/verified-source.patch` includes bounded
field-limit delivery and the accepted-post audit. Its
`closure-receipts.json` verifies the compiled helper stop.
`routing-useful-cost-comparison.json` records the final build's first
scan on each project. `routing-first-vs-native-conductor-repeat-comparison.json`
compares the first Conductor scan against the second native control.
`routing-conductor-matched-repeat-comparison.json` compares the final
Conductor pair with exact accepted and confirmed report identities.
`useful-cost-lean-final.log` contains the axiom check for the 56
local and closure theorems.
An archived checkout has its base commit and complete diff under
`retired-checkout/`. To recreate the final prototype, make a clean
detached checkout at `758ad99ff` and apply `verified-source.patch`.
The patch was checked against that exact base. Old duplicate heap
dumps and obsolete raw profiles were removed after preserving the
result manifests, test receipts, logs and summaries used here.
[External report archive](EXTERNAL_DATA.md)
