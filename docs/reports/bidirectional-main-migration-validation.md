# Main migration: implementation and validation

9 November 2026. The implementation is committed. **Acceptance has not passed.**
All eight baseline/current project commands and all offline heap/profile
analyses have stopped. The full rule suite is still in progress. This report keeps
real finding failures visible and selects no unplanned core fix.

## Source and scope

| Source | Pin |
| --- | --- |
| Selected bidirectional core before migration | `13357151d` |
| Fresh main baseline and rebase target | `54ad708fe1c4f551956d3d572866de1534415fa1` |
| Migration implementation | `9b21b3716404b490d522bd65d7df916a8069dfe6` |
| Measured source HEAD; documentation only after implementation | `03cf52fa90f9eb5273334bb37b2cc4914100e1cd` |

The user authorized a fresh baseline because no saved result exists for the
exact main pin. The baseline used an external, clean, detached source clone.
All implementation work is in the primary repository. The rebase kept merge
history. Commit `7288c1bda` removed obsolete side-branch variants retained by
historical merge replay. Common bidirectional production and test code matches
the selected pre-migration trees exactly. Main's configuration, IR and model
changes remain in place.

The adapter implements the [specification](../../spec/main-migration.md) and
[implementation proposal](../design/bidirectional-main-migration-implementation-20261109.md):

- Decode main's `Exact` and `AnyAccessorAfter` action positions.
- Use explicit array, Spring and String-byte reach.
- Keep source-definition reset scope through the existing cleaner primitive.
- Use default getter rules only when the prepared explicit rule list is empty.
- Keep branch rule selection, mark ownership, aliases and prescan hooks.
- Ignore the legacy iteration cap in bidirectional mode and log it once.

The four tails, C2/C5, layers, fields, protection, subsumption, Targets, loops,
static handling and field-limit schedule are unchanged. This comparison is
legacy main versus the migrated bidirectional engine. It does not isolate the
performance effect of the migration from all earlier bidirectional work.

The [actual file inventory](data/bidirectional-main-migration-actual-files.csv)
classifies each change as `works-as-on-main` or `works-as-on-bidir`. Shared files
have separate responsibility rows. Extra paths adapt shared API constructors,
Go schema consumers and existing report observers; they also add small native
coverage cases. They do not introduce another analyzer algorithm.

## Project results

All runs use source Gradle `runProjectAnalyzer`. The new core uses FULL marks,
`1,1,2,3,...`, aliases and static propagation. No 16 GiB override or alternate
schedule was used. Heap limits are 8 GiB, except Thingsboard at 12 GiB. OWASP
has a 1,000 s IFDS budget; the other projects have 1,080 s. All outer budgets
are 1,200 s.

| Project | Main status; command s; findings | Current status; command s; findings | Latest reached / completed / accepted forward |
| --- | --- | --- | --- |
| OWASP | OK; 156.357; 2,633 | TIMEOUT; 1,037.496; 2,633 | **run-185 / run-184 / run-183** |
| Conductor | OOM; 187.377; 7 | TIMEOUT; 1,122.473; 7 | **run-8 / run-7 / run-7** |
| Thingsboard | OOM; 439.637; 15 | OOM; 376.632; 0 | **run-1 / none / none** |
| Stirling-PDF | OK; 52.106; 24 | TIMEOUT; 1,107.492; 32 | **run-11 / run-10 / run-9** |

Main uses the legacy engine. A bidirectional `run-N` label does not apply to it.
A started or engine-complete run does not prove that its report was accepted.
Thingsboard failed before its first report barrier; zero exported findings
is not proof that no sink was reached internally.

| Project | Main peak RSS, bytes | Current peak RSS, bytes |
| --- | ---: | ---: |
| OWASP | 9,207,869,440 | 10,333,851,648 |
| Conductor | 10,050,641,920 | 10,886,615,040 |
| Thingsboard | 14,477,676,544 | 14,699,008,000 |
| Stirling-PDF | 8,137,457,664 | 10,683,338,752 |

RSS includes native memory. It is not the configured Java heap or retained
object size. Main's Conductor and Thingsboard reports are partial OOM outputs.
Matching those outputs cannot prove complete program coverage.

### Finding locations

Identity uses rule ID, sink fingerprint and full method signature. Physical
and logical locations are also compared. Report IDs and trace counts are not
cross-version identity keys. Model, rule and input pins match in all four
comparisons.

| Project | Shared exact identities | Baseline only | Current only | Interpretation |
| --- | ---: | ---: | ---: | --- |
| OWASP | 2,633 | 0 | 0 | All baseline locations retained; current run still times out. |
| Conductor | 7 | 0 | 0 | All seven partial-baseline locations retained. |
| Thingsboard | 0 | 15 | 0 | First-run resource abort prevents report acceptance. These are observed output losses, not 15 proved transfer defects. |
| Stirling-PDF | 16 | 8 | 16 | Eight changed return anchors and eight new method exits; see below. |

All eight Stirling baseline-only locations have a current report for the same
rule and full method signature. Exit rules join at one synthetic normal exit.
`SinkKey` and the report descriptor contain that boundary, not the concrete
return which carried the witness. With no full trace, the SARIF renderer picks
the last return. This explains the changed anchors, including null/error
returns. It does not prove preservation of each original source path.

| Stirling method | Baseline line | Current line |
| --- | ---: | ---: |
| `ConvertEmlToPDF#convertEmlToPdf` | 133 | 148 |
| `PipelineController#handleData` | 90 | 130 |
| `JobController#getFileMetadata` | 278 | 291 |
| `AdminSettingsController#getSettingValue` | 381 | 388 |
| `InviteLinkController#generateInviteLink` | 242 | 246 |
| `InviteLinkController#acceptInvite` | 477 | 482 |
| `InviteLinkController#validateInviteToken` | 387 | 391 |
| `UserController#inviteUsers` | 518 | 521 |

The eight new method exits are four `FilterController` methods, two
`WebResponseUtils` methods, `AuthController#login` and `UserController#register`.
Some return caller-supplied files, bytes or user records. The current Simple
reports have no source-to-sink codeFlow. Do not classify an added report as a
false positive from its count or final null display anchor. The attachment,
content-type, guard and stored-state routes still need exact current traces.

The [finding data](data/bidirectional-main-migration-stirling-findings.json)
embeds all 24 changed occurrences, old full codeFlows, exact source excerpts
and the limits of each classification. No external `shape-probe-results`
directory is needed to read this evidence.

## Time and workload

The [iteration data](data/bidirectional-main-migration-iterations.json)
contains every observed run, its engine/barrier time, frontier and report
commit evidence. A handoff pattern count includes normalized DATA, ZERO,
Target and block insertions. It is not an AP-only count. Raw outgoing Target
rows use another representation; do not add them to that count. Record
crossings are runtime events, not stored record cardinality.

| Project | run-1 engine s | First barrier s | run-2 engine s |
| --- | ---: | ---: | ---: |
| OWASP | 82.464 | 2.368 | 27.131 |
| Conductor | 19.706 | 2.007 | 37.452 |
| Thingsboard | 224.047, OOM | Not reached | Not reached |
| Stirling-PDF | 20.972 | 0.752 | 12.899 |

Thingsboard's engine time includes its 27.909 s OOM snapshot. OWASP exceeds
the 60 s run-1 engine target. Conductor and Stirling meet that target. No
completed transition measurement exists for Thingsboard.

| Conductor run | Direction | Engine s | Handoff patterns | Owner keys | Record crossings |
| --- | --- | ---: | ---: | ---: | ---: |
| run-3 | Forward | 7.191 | 17,867 | 329 | 262,775 |
| run-4 | Backward | 132.278 | 30,926 | 192 | 293,028 |
| run-5 | Forward | 10.946 | 30,614 | 174 | 298,262 |
| run-6 | Backward | 438.346 | 149,140 | 171 | 958,367 |
| run-7 | Forward | 157.081 | 88,169 | 170 | 362,859 |
| run-8 | Backward | 239.078, timeout | Unavailable | Unavailable | Unavailable |

Two contexts of `ParametersUtils#replace(Map,DocumentContext,String)` account
for 128,141 of the run-6 pattern insertions (85.92%) and 65,952 of run-7
(74.80%). These are normalized insertions by owner key. They are not the
number of stored scalar summary edges.

| Stirling run | Direction | Engine s | Handoff patterns | Owner keys |
| --- | --- | ---: | ---: | ---: |
| run-5 | Forward | 0.981 | 1,344 | 116 |
| run-6 | Backward | 7.328 | 1,333 | 112 |
| run-7 | Forward | 22.351 | 1,081 | 79 |
| run-8 | Backward | 17.343 | 1,138 | 75 |
| run-9 | Forward | 554.056 | 975 | 70 |
| run-10 | Backward | 17.850 | 1,133 | 70 |
| run-11 | Forward | 387.938, timeout | Unavailable | Unavailable |

The largest late Stirling run is forward. Few final demand patterns do not
bound the number of generated facts, summary applications or pure loop
queries. The cause must be checked at those stages, before frontier export.

OWASP reaches all 2,633 accepted findings in run-3, then continues to run-185.
Later forward runs repeatedly have 1,111 normalized handoff patterns; later
backward runs have 2,264. Equal counts alone do not prove equal geometry or
non-termination. Report stability is not a valid stopping criterion.

The complete run-82 incoming state has **103 DATA pairs and 1,008 control
pairs**, exactly the 1,111 normalized rows from run-81. All have empty method
context; there are no duplicate normalized rows. DATA entry paths have at most
one accessor and exits at most two, while the global limit is 81. Controls
comprise 438 unscoped Target-to-ZERO, 381 unscoped Target-to-DATA and 189
scoped Target-to-DATA rows. Current selected summaries also have at most two
accessors. This is shallow feedback, not a depth-81 frontier.

A concrete source example is `BenchmarkTest01000.Test#doSomething`:

```java
public String doSomething(HttpServletRequest request, String param) {
    String bar = "";
    if (param != null) {
        bar = new String(Base64.decodeBase64(
            Base64.encodeBase64(param.getBytes())));
    }
    return bar;
}
```

All following facts have FLOW, empty exclusions and no protection:

```text
saved forward NORMAL:
  param.<string-bytes>.[].[any-taint] -> ret.<string-bytes>.[any-taint]

native backward read of that record:
  ret.<string-bytes>.* -> param.<string-bytes>.[].[any], DEMAND

run-82 incoming backward demand includes:
  ret.<string-bytes>.[any] -> param.<string-bytes>.[].*

run-82 current output includes:
  ret.<string-bytes>.* -> param.<string-bytes>.[].[any], DEMAND
```

`Reference.kt.mustRecordReadView` deliberately produces that ANY/DEMAND native
reverse view. The uncertainty is not a global-limit truncation. Short NORMAL
STAR rows also exist, but suffix correlation means their presence alone does
not prove that this MAY relation is covered. One mid-run snapshot does not
prove full cross-run equality or explain every control row.

### CPU evidence and a source-level amplifier

All-thread CPU samples include GC and compiler threads. JFR execution samples
cover Java stacks. Inclusive shares overlap and are not wall-time percentages.
Allocation weights estimate churn; they are not retained heap bytes.

| Window | Loop restriction, inclusive samples | Full loop observer, inclusive samples |
| --- | ---: | ---: |
| Conductor run-8, 30 s | 54.96% | 53.80% |
| Stirling run-11, near limit | 42.40% | 40.71% |
| Thingsboard run-1, normal window | 0.58% | Not observed |

`LoopOutputRestriction.restrictScalar` observes the full raw result, then tries
budgets 1 through depth minus one. Each trial can replay saved summaries and
repeat C2 and enclosing C5. `LoopRestrictionSession.certifiedFirstBudget`
currently returns null: its old certificate does not cover the new complete
initial family. Thus growing paths can pay for several complete pure queries
per summary application. This is a measured late-run cost. It does not explain
Thingsboard run-1, where this restriction is bypassed.

The complete JFR run-8 Java sample split is more precise: **85.91% loop-observer
C2**, 0.55% loop-observer C5, 1.41% ordinary C5, and 5.28% saved replay outside
the gate. Total C5 is about 2%. `DemandStore` in a stack is not sufficient to
call the work C5: the hot chain is `DemandStore.initials ->
InitialDemandResults.offer -> RestrictedInitialPolicy.emitAdmissions ->
ApManager.initial`. Trial observations construct and intern initials which
may never be delivered.

Stirling has another split. Run-9 spends 52.08% of Java samples in actual
saved replay, 20.84% in virtual replay inside the observer and 18.62% in other
observer work. Run-11 has 44.42%, 22.93% and 22.77%, respectively. C5 is about
0.03% in run-11. Canonicalization/subtraction is a frequent leaf path.

Sampled allocation is about 1.260 TB in Conductor run-6, 420.17 GB in run-8,
1.519 TB in Stirling run-9, and 1.086 TB in run-11. These are weighted churn
estimates. GC pauses are only 1–3 s in these phases, but concurrent GC still
uses substantial CPU. Thingsboard run-1 has about 1.025 TB sampled churn and
50.553 s of GC pause. It spends about 45% of Java samples in direct calls,
7.49% in current delivery and only 0.55% in the loop gate.

Late OWASP runs allocate about 8.7 GB per 3–5 s engine and spend about 72–74%
of Java samples in direct call processing. Condition/form builders appear
in allocation stacks. Source confirms a deterministic cache purge: every
engine and barrier calls a memory-guard wrapper which clears all managed soft
references in `finally`, even while memory is healthy. Method/form owners
survive those scopes. This is an avoidable rebuild path, distinct from the
intrinsic reverse-MUST demand feedback.

The [CPU windows](data/bidirectional-main-migration-loop-cpu.json) and
[complete phase profile data](data/bidirectional-main-migration-profiles.json)
retain denominators, disjoint scopes, allocation estimates and exact stacks.

### Where Conductor paths grow

The run-8 heap has 83,646 incoming DATA rows plus 4,523 controls.
`ParametersUtils.replace` and `replaceList` own 75,987 DATA rows (90.84%).
Selected caller points in `getTaskInputV2` and `getTaskInput` hold 41,898 rows,
mostly NORMAL FLOW. Premises have field length at most one; current admitted
summary conclusions are at most two. Yet point conclusions reach field length
six: 17,240 NORMAL points have length five, 10,600 length four and 4,800 length
six. Raw accessor length can be larger than counted field length.

```text
NORMAL point; empty field E; excluded marks {75,81}:
ret.headers.* ->
  arg0.[].MapValue.Iterable.Element.HttpHeaders.headerValues.
       HttpHeaders.headerValues.HeaderIterator.headers.*
```

This is caller-side expansion before the next summary restriction. Restricting
all published summaries does not bound every fact produced by their application.
The virtual loop observer can repeat this same application work.

The repeated header fields are synthetic model slots. Actual Spring
`HttpHeaders` has no `headerValues` field; Apache `HeaderIterator` is a
fieldless interface. Its model has both `this -> result` and
`this.headers -> result` CopyAllMarks rules. The alias adapter makes them
symmetric, allowing an iterator/content alias cycle. This is a concrete
possible expansion mechanism, not proof that it produced every native row.
There are 1,789 adjacent `headerValues` repetitions in the 41,898 points.
The exact native producer action/dispatch chain still needs tracing.

A conservative native audit finds 3,685 covered STAR point relations out of
37,375. For example, saved NORMAL `ret.* -> arg0.MapValue.Iterable.Element.*`
covers the suffix-correlated relation
`ret.HeaderIterator.headers.* ->
arg0.MapValue.Iterable.Element.HeaderIterator.headers.*` in the same context
and exclusions. Other shorter paths have different prefixes. They cannot
be deleted from name resemblance alone. This covered subset is not a 2x
remedy, and a method-exit relation alone does not justify deleting an internal
point observation.

### Stirling's intermediate paths and live memory

The active run-9 snapshot has 930 incoming DATA pairs plus 208 control pairs,
matching the run-8 total of 1,138. Of the DATA rows, 796 are FLOW/ANY to
FLOW/STAR. `decodeMimeHeader` owns 359 DATA rows in two keys/scopes. Selected
current state has 34,874 point rows and 1,688 current scalar summaries.

The actual method uses Pattern.matcher, Matcher.group and replaceAll while
decoding MIME text. An exact NORMAL FLOW point in its loop has:

```text
IR local21.$ ->
  encodedText.Matcher.pattern.Pattern.regex.Matcher.pattern.Pattern.regex
             .Matcher.pattern.Pattern.regex.$
E={}, mark exclusions={}, protection=false.
```

`local21` is the actual IR register, not a guessed source variable. Model
slots are virtual tracking fields, so this is not grounds for an automatic
Java field-type rejection. The matched models include both taint-copy root
transfers and structured `Matcher.pattern.Pattern.regex` transfers. Alias
extraction makes CopyAllMarks symmetric. Thus it can equate text, matcher
and modeled pattern contents, creating a cycle without opposite-direction
replay. The exact native producer history is not retained in this heap.
2,879 of 7,882 decode-method points contain at least two such pairs.

Some relevant models have `taintCopyOnly=true`, but both main and the branch
lose that flag in binding before alias extraction. This predates migration.
Honoring it would be a separately selected alias-policy change, with tests
for required true aliases and automaton state flow.

Other point work is static registry state: 11,971 conclusions have STATIC
base, versus 16,883 locals, 2,524 arguments, 2,168 returns, 1,296 ZERO and
32 This. Registry/repository accessor occurrence counts overlap; they are not
additional disjoint fact populations. The maximum counted point field length
is eight; admitted summary conclusions are at most five.

The reachable object graph at capture is **2,608,757,576 bytes**, not the
9.53 GB physical all-objects HPROF size. It does not show an 8 GiB retained
heap blow-up. The large sampled allocation and repeated replay/canonicalization
show a transient-work problem at that point. It does not exclude a larger
live peak elsewhere in the run.

| Current snapshot | Reached run at capture | Reachable bytes | Reachable objects |
| --- | --- | ---: | ---: |
| OWASP | run-82 backward | 2,304,263,768 | 69,387,016 |
| Conductor | run-8 backward | 4,956,412,248 | 141,344,076 |
| Stirling-PDF | run-9 forward | 2,608,757,576 | 73,260,836 |

Conductor's IR storage owns 3,228,159,688 bytes (65.13%); its retained NORMAL
record store owns 364,160,632 bytes. Stirling's IR owner has 977,749,312 bytes
and its NORMAL store 332,688,224 bytes. These are selected mid-run snapshots,
not whole-run memory peaks. IR representation is outside this proposal. The
[semantic heap data](data/bidirectional-main-migration-semantic-heaps.json)
contains the complete decoded category totals and scope/selection limits.

## Thingsboard run-1 memory

The OOM snapshot contains **308,490,787 reachable objects and
11,367,904,728 reachable shallow bytes**. The physical HPROF file is
18,548,492,436 bytes; file size is not live heap size. The following ownership
groups partition top-level dominators and can be added. Arbitrary per-class
retained sizes cannot be added this way.

| Owner | Retained bytes | Share of reachable heap |
| --- | ---: | ---: |
| Unit runners | 4,300,717,992 | 37.83% |
| RAM IR storage | 1,619,097,160 | 14.24% |
| Subscription manager | 998,326,344 | 8.78% |
| Run manager | 882,615,752 | 7.76% |
| JVM rule provider | 805,517,792 | 7.09% |
| JVM method entries | 775,884,160 | 6.83% |

There are 4,101,442 bound `TaintMethodExitSink` objects, about 4.15 million
caller-input accumulator key/entry pairs, 2,927,057 `CallerRef` objects,
2,110,906 publication members and 1,949,346 Target summaries. These counts
include auxiliary state; they are not all distinct data facts. Caller-side
subscription inputs are not the old removed callee added-fact store.

Only 11 compiled forward/reverse form payloads and four rule statements are
live in this snapshot. More than one million soft references exist, but this
is not evidence that compiled form payloads dominate the heap. Strong owner
and cache drilldowns are recorded below. IR storage changes remain out of scope.

The static service has only **997 writer rows**, but **119,310 point
subscriptions and 3,274,730 pending wanted memberships**. The histogram has
2,741,433 `Run1PointResume.PendingFlowImages` objects. Thus millions of static
writers are not the cause in this heap. Standing requests and their actor
resumption state remain a separate candidate. Per-mark images can share one
FLOW geometry; the complete targeted census is in the next subsection.

Only 129 serialized exit-sink templates exist. Bound sink specialization can
retain an original sink through `RuleSpecializationIndices.originalRule`.
The 4.10 million sink objects versus 2.05 million `TaintSinkMeta` objects is
consistent with an original/selected-copy multiplier. It is not proof of
4.10 million independent method queries. Resolver caches use method and
role/flags, not caller context. Prescan and actual exit processing both bind
exit rules; the exact per-epoch distribution is still being checked.

The [heap data](data/bidirectional-main-migration-thingsboard-heap.json) embeds
the complete class histogram and the displayed dominator partition. The
top-200 root-class display covers 99.99152% of reachable bytes; 964,176 bytes
remain in smaller undisplayed root groups. The class histogram is uncapped.

### Strong owner and request detail

The subscription input directory owns 998,305,576 bytes. Its accumulated values
own 623,590,856 bytes and its indexes 305,638,376 bytes. These are subtrees of
the directory, not extra heap to add to the top-level table. All 4,146,431
caller input groups were classified. No current input has a STATIC base, but
746,887 groups (18.01%) have a STATIC original premise and a nonstatic image.
Most retained groups have ordinary This/argument origins. Therefore, current
base alone cannot identify static-related work, and statics are not the
majority of these caller groups.

RunManager summary storages own 826,258,200 bytes; the global static service
itself owns only 56,327,240 bytes. UnitRunner actor maps own 3,438,618,256 bytes.
Nested block runtimes own 1,963,305,896 bytes; root and child edge stores own
820,508,136 and 281,457,056 bytes. These nested/reference-field values overlap;
do not add them as a second heap partition.

The actor point census has 99,692 rows with 2,741,433 pending marks. Of these,
88,106 rows share one identical FLOW root among all their marks; they contain
93.50% of pending memberships. There are only 251,351 point/root pairs.

| Original static premise | Pending memberships | Point rows |
| --- | ---: | ---: |
| `TenantId.tenants` | 1,357,740 | 54,926 |
| `TenantId.SYS_TENANT_ID` | 1,153,847 | 40,929 |
| `TbMsgCallback.EMPTY` | 178,927 | 2,828 |

The two TenantId fields account for 91.61% of pending memberships. `TenantId`
is an ordinary final class, not an enum. `tenants` is a mutable canonicalization
cache. `SYS_TENANT_ID` is a fixed canonical ID; `EMPTY` is a stateless callback.
The existing enum alias filter does not exclude them. A broad Map-value alias
model can connect cache contents to returned objects, but the exact derivation
of every native SYS_TENANT_ID image is not yet proved.

Static conclusions are not relayed through calls in run-1. The STATIC original
premise still follows a nonstatic image through ordinary calls. Callee mark
requests match that image, then return to its static origin. This explains
2,516,034 call-stage pending memberships (91.78%), versus 122,571 boundary
and 102,828 cleaner memberships. Few local static reads can thus cause many
downstream continuations.

An exact sampled continuation is:

```text
RuleChainActorMessageProcessor.onUpdate, instruction76, line134,
CallStageInput(stage3), block2/entry32:
  S.TenantId.SYS_TENANT_ID.*/FLOW -> this.[any]/FLOW, DEMAND, E={}
  221 pending FULL marks share one immutable FLOW root at the empty path.
  They span 13 rule groups: 146 XSS, 56 unsafe-Jackson and 8 path-traversal
  marks are the largest families.
```

Another sample has 221 distinct FLOW roots which all encode the same 28 paths.
Thus physical-root identity understates equal-geometry duplication. This
supports bulk image/mark storage, while it does not prove a whole-heap speedup
or justify discarding the static requests. The complete source-bound
[owner detail](data/bidirectional-main-migration-thingsboard-owner-details.jsonl.gz),
[pending aggregates](data/bidirectional-main-migration-thingsboard-pending-roots.jsonl.gz)
and [six point samples](data/bidirectional-main-migration-thingsboard-point-samples.jsonl.gz)
are in the repository.

## Baseline OOM attribution

The baseline uses the legacy engine; run labels are not applicable. Latest
Conductor guard heap has 7.678 GB reachable memory: IR storage owns 2.257 GB,
unit runners 2.000 GB and unit summary stores 851 MB. The histogram contains
6.02 million field-unfold requests, 7.75 million side-effect summaries and
7.62 million access paths. This is legacy request/AP/summary retention, not
the new core loop observer.

The latest Thingsboard guard snapshot was captured after cancellation. Its
reachable heap is 9.225 GB, with 1.627 GB in IR storage. A 6.121 GB main-thread
owner resolves to 2.328 GB of summary stores, 1.497 GB of rule configuration,
1.378 GB of runners, 332 MB of method contexts and 266 MB of subscriptions.
These are a disjoint child partition, not additional heap beside that owner.
The rule configuration contains about 799 MB of ordinary sink configuration
and 511 MB of exit-sink configuration. The largest unit summary map is
1.500 GB. The histogram has 43.93 million concurrent-map nodes, 18.67 million
condition atoms, 11.72 million ContainsMark objects and 9.11 million
field-unfold requests.

Snapshot phases differ: current Thingsboard is an active run-1 abort; this
legacy snapshot is later in cancellation. Do not treat their live-byte ratio
as a controlled before/after memory reduction. The
[baseline owner packet](data/bidirectional-main-migration-baseline-oom.json)
contains both full histograms, owner partitions, capture costs and hashes.

## Native gates and small failures

| Gate | Tests | Failures/errors | Skipped | Result |
| --- | ---: | ---: | ---: | --- |
| Common dataflow | 2,535 | 0 | 0 | PASS |
| JVM bidirectional adapter | 351 | 0 | 0 | PASS |
| Configuration equality | 5 | 0 | 0 | PASS |
| Go selected view | 10 | 0 | 0 | PASS |
| Final post-commit root selectors | 153 | 11 / 0 | 3 | FAIL |
| Explicit bidirectional cleaner reach | 3 | 0 | 0 | PASS |
| Query/compiler suite | 276 | 0 | 26 | PASS with existing disabled cases |
| Lean component laws | 70 | 0 | — | PASS |

The three root environment skips were run separately with bidirectional mode
and passed. The query skips are existing disabled/environment cases. All 13
Sequence cases and all six local-static writer cases now pass. No expected
finding was removed and no test was disabled to make this migration pass.

The 11 real failures comprise five cleaner-matrix cases, two small cleaner
cases, two Spring dispatcher cases and the same two predefined-cleanup cases.
The 70 Lean laws are 51 specification laws plus 19 seam laws, with 14 finite
examples. They do not prove all native behavior or whole-program convergence.

### Exact root cleaning does not refine

```java
// Entry source assigns T at x.$ and x.[any-taint].
// clean removes T at its exact root; sink checks exact T.
void shallowAfterRootClean(Node x) {
    clean(x);
    sink(x.next);
}
```

Both this case and the two-read case complete **run-9**, then stop by `POLICY`
without the required finding. The trace is:

```text
run-1: source ZERO -> x.MUST/T NORMAL
       exact-root clean retains MUST but makes it DEMAND
       read -> temporary.MUST/T DEMAND -> DemandTarget
run-2: backward sink reaches x.next.$/T NORMAL at the entry source
       source hit saves the original ZERO -> x.MUST/T action and action ID
run-3: permission replays that same source MUST; cleaner demotes it again
run-4 through run-9: the same refinement route repeats
```

The source is reached and its permission survives. The replay does not keep
the child query geometry. Simply adding a child MUST beside a root MUST is
insufficient: canonicalization can remove the child before cleaning. A fix
must prove source projection, canonicalization and partial cleaning together.
This example has no loop, static field, alias or interprocedural read chain.
The implicated common core code is unchanged by the migration; this is not
an isolated proof that the adapter caused the failure.

### Spring loses a ZERO route

Both cleanup modes reach and complete **run-3**, then stop with
`NO_DEMAND_EDGE`, missing `inside-static`. Direct and registry findings remain.

```text
run-1: dispatcher contains writer ZERO -> S.outside/T
       and reader S.outside/T -> DemandTarget
run-2: method-level static completion admits dispatcher-body ZERO
       store and its wrapper export ZERO -> DemandTarget
       entry-source permission is saved
       inner dispatcher exports NORMAL ZERO -> S.outside/T and ZERO -> ZERO,
       but no method-level DemandTarget
run-3: inner dispatcher admits registry DATA, but no ZERO
       wrapper/controller do not start; inside-static remains absent
```

The immediate loss is between the wrapper's backward terminal and the inner
body's next forward ZERO admission. Saved NORMAL ZERO replay at a caller does
not execute the skipped callee body. Two scoped block Targets failed C5, but
the saved trace does not contain their exact block/port tuples. A source review
found a possible split between STATIC_SHORTCUT and ROOT_EXIT completion views.
That is a candidate attribution, not a proved explanation of those two rows.
Do not add blanket ZERO seeds or rerun run-1 static closure as an unreviewed fix.

## Captures, limits and remaining work

Before this campaign, 44 old raw capture files were removed: 2,787,014,646
bytes. Logs, SARIF and decoded evidence remain. JFR is bounded to 256 MB per
recording. OOM snapshots are taken at MemoryManager events. Main needs an
external observer; the current core has its native snapshot hook.

Main Conductor warning/OOM dumps cost 14.151 s and 14.647 s. Main Thingsboard
captures cost 97.848 s in total. Its automatic normal CPU capture overlapped a
manual window and failed; a clean recovery window was captured. Current
semantic snapshots cost 8.527 s (OWASP run-82), 10.782 s (Conductor run-8),
13.885 s (Stirling run-9), and 27.909 s (Thingsboard run-1 OOM). These costs
are included in observed command/engine times. The receipts identify every
capture and failed/in-flight request. Do not subtract them and call the result
an uninstrumented benchmark.

All measured project analyzers stopped before heavy offline decoding or the
full rule suite started. The rule suite runs beside offline MAT/JFR decoding;
its times are diagnostic and are not project performance measurements. Its
heap remains 8 GiB and default timeout remains 10,000 s per Java sample. Fresh
sample build, coverage, Go source build, autobuilder and Java/Go model checks
passed. Current declarations are 609 Java and 201 Go samples; older 353-Java
counts are stale. Declarations do not prove collection or successful execution. The actual Java analyzer emits bidirectional events. At 16:32 UTC, 348 Java analyses had completed and the upload sample had
reached **run-490337**, completed **run-490336** and accepted forward
**run-490335**. Its final result was unavailable; the full gate is still live.
The auditor calls a missing end marker INTERRUPTED, but the observed process
is alive, so that label is not a terminal interruption or timeout. Neither
completed analysis counts nor a partial matching finding prove the JSON gate.
A 3.546 s live snapshot records that case without changing its source or budget.

Remaining work: finish the Java and Go rule result gates. All current semantic
heaps, both baseline OOM owner analyses and all eight project JFR streams have
been decoded. The [next-iteration proposal](../design/bidirectional-main-migration-next-iteration-20261109.md)
ranks measured work reduction and lists separate correctness blockers. The
[validation data](data/bidirectional-main-migration-validation.json) retains
source pins, exact project summaries, native failures and memory tables.

The first next-iteration C2 candidate has a source audit and
[nine local Lean laws](../../spec/lean/proposals/main-migration-work-reduction-20261109/README.md).
A captured trie probe removes 4,664 impossible descendant emitter calls. A
separate reconstructed prefix example has four baseline C2 starts and 466
candidate starts; one actual extra descriptor proves that budget cannot
match. These are local work bounds, not measured speedups or a whole-program
proof. No C2 optimization is implemented in the measured runtime.

## Additional rule-suite evidence while the full gate runs

At 17:38 UTC, the original rule-suite JVM was still active. A bounded streaming
audit covered 348 completed Java analyses: 194 declared positive and 154
negative. Their final accepted report-identity counts all match the declared
expectation. This is **provisional**, not the final `test-result.json`
classification: trace conversion and final output still matter. The
[per-sample evidence](data/bidirectional-main-migration-rule-prefix.json)
records each completed run and excludes the active sample.

The active upload case had reached **run-964027** at that observation. Its
configured 10,000 s budget is unchanged. An external observer now watches the
original process for memory warnings/OOM without changing JVM arguments or
restarting it. Post-status captures are labelled as possibly after release.
No OOM had been observed when the observer started.

### A small control/Target refinement cycle

The existing live-only upload heap identifies its actual run as **run-57799**
forward, field limit 57,798. The receipt's pre-jcmd log was ten runs earlier;
the frozen active RunManager is authoritative. Its incoming state has **zero
paired DATA rows and 26 controls**, all paths of depth at most two. Those
controls are 24 DATA-to-ZERO, one ZERO-to-ZERO and one Target-to-ZERO. There
are no incoming seeds, including source permissions.

```java
void doPost(HttpServletRequest request, HttpServletResponse response) {
    ServletFileUpload upload = new ServletFileUpload();
    List<FileItem> files = upload.parseRequest(request); // source T2
    for (FileItem file : files) {
        File targetFile = new File("/var/www/uploads/" + file.getName());
        streamFile(response, targetFile);
    }
}

void streamFile(HttpServletResponse response, File file) {
    try (FileInputStream fis = new FileInputStream(file)) { // report key 0
        // Copy bytes to the response.
    }
}
```

The native IR maps local4 to the implicit iterator. Use `iterator` below only
as that proved desugared variable. All following exclusions are empty.

```text
retained NORMAL prefix producer, doPost BL:
  ZERO -> iterator.Element.[any-taint]/T2

root repeat demand:
  iterator.[any]/T2 -> ZERO

production C2 family for that offered NORMAL producer fact:
  iterator.Element.*/T2, DEMAND
  iterator.Element.*/FLOW, NORMAL
  iterator.$/FLOW, NORMAL

same-path demand iterator.Element.[any]/T2 instead emits:
  iterator.Element.[any-taint]/T2, NORMAL
```

This cell is executed by the current production emitter, not only inferred
from its source. It shows how a known uniform fact can also create an
uncertain initial under another demand. It does not prove that this exact
packet arrived at the later sink in the sampled iteration.

The retained records include NORMAL FLOW STAR and MUST identities and empty
mark exclusions, so a missing FLOW provider or excluded T2 does not explain
the continuation. The root already retains `ZERO -> NormalTarget(0)`. All
19 saved NormalTarget memberships use ID 0. Source/IR inspection identifies
the selected physical sink at `streamFile`, instruction5, line375.

| Completed run | Direction | Normalized handoff patterns | Raw outgoing Targets | Reports | Seeds |
| --- | --- | ---: | ---: | ---: | ---: |
| run-57798 | Backward | 26 | 1 | 1 | 0 |
| run-57799 | Forward | 27 | 27 | 1 | 3 |
| run-57800 | Backward | 26 | 1 | 1 | 0 |
| run-57801 | Forward | 27 | 27 | 1 | 3 |

These are separate counters. Equal values in the forward rows do not prove a
normalized DATA/control partition. The captured configuration is the only
retained RunConfig; the next backward demand store is absent. The 27 outgoing
Targets alone provide continued control guidance.

`RunMethodLocalServices.witness` gives a NORMAL witness a stable report ID,
but a DEMAND witness captures sink seeds and emits an anonymous DemandTarget.
The existing persisted-NormalTarget suppression does not compare that anonymous
Target with the already reported key. DATA/FLOW subsumption does not retract
such a Target either. This is a concrete demand-lifetime issue to investigate;
more field capacity cannot expose a missing depth-57,798 path here.

The early snapshot has no current sink seeds or Targets yet. The three final
seeds and 27 final Target rows are known from logs, not frozen native objects.
Thus final anonymous provenance and a complete two-run fixed-point proof are
still unproved. Do not suppress arbitrary DemandTargets because some report
exists. A future repair must distinguish a settled root report from a merely
conditional NormalTarget, and preserve other unresolved sinks and source
guards. The [complete case data](data/bidirectional-main-migration-upload-cycle.json)
keeps these limits explicit.

### Native bridge for the next C2 proposal

A small isolated JVM invoked production `RestrictedInitialPolicy.emitAdmissions`
from the measured 92-entry runtime classpath. It made no analyzer/project run
and changed no source. It confirms the three/one upload families above and
the four/466 Conductor families, preserving captured field IDs and exclusions.
The [native receipt](data/bidirectional-main-migration-native-c2-probe.json)
records class hashes, exact origins and complete output. This strengthens the
operator correspondence; it does not prove the whole optimized observer.

## Acceptance audit at this checkpoint

| Required part | Evidence | State |
| --- | --- | --- |
| Selected migration and inventory | Runtime commit, source comparison, file classifications | Implemented; no extra core algorithm applied |
| Wrapper, explicit reach, fallback, cap controls | Native JVM/configuration/compiler results | Passing focused controls |
| Spring and complete native quality | Eleven unchanged real finding expectations fail | **Failed; no waiver** |
| Exact project locations and completion | Fixed-config receipts and comparisons | Recorded; no-FN/completion acceptance not established |
| Full Java/Go rules | Original source Gradle driver is live | **Pending** |
| Profiles and OOM root causes | Current and baseline decoded packets | Complete for measured project scans |
| Next proposal | Ranked work reduction, explicit semantic gaps, local laws | Written; not selected or implemented |

The successful build, component laws and provisional rule prefix do not close
the failed or pending gates. The current iteration does not silently add a
cleaner, Target, alias, admission or stopping-policy change to make them pass.

### Exact declared Java coverage

A classfile audit of the frozen source build covers all 609 Java declarations
and all 326 compiled classes. It finds 585 analysis-eligible declarations,
22 declarations in 11 explicitly disabled rules, and two unresolved fixtures.
All use default mode; no Spring-app mode needs generated entrypoints here.

The two unresolved declarations are RMI interfaces:

- Positive `UnsafeDeserializationSamples.DangerousRemoteService#invoke`,
  source line235.
- Negative `UnsafeDeserializationSamples.SafeRemoteService#invokeById`,
  source line252.

Both methods exist, but their classes are abstract interfaces and their
methods have no Code/LineNumberTable. `resolveMethods` rejects those classes
before method selection. Both also have exact preamble `No sample found`
markers. There are no other missing classes, missing methods, anonymous-class
rejections or normalized-name collisions. This is a runner/fixture coverage
gap, not an executed pass, disabled case or observed new-core false negative.
The [fixture data](data/bidirectional-main-migration-java-fixtures.json)
contains all declaration outcomes, class flags/hashes and method descriptors.
The final result must still reconcile 585 executed analyses, 22 disabled
records and these two explicit omissions; declaration counts alone do not
prove execution.
