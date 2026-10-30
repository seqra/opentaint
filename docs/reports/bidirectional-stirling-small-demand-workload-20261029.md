# Stirling: small demand and excessive instruction work

Date: 29 October 2026. Runtime: `bb74cef6cf483db167c161020a8a4cca576ca005`.
The clean campaign reached **run-6**, completed **run-5**, and accepted the
**run-5** forward report. Run-6 ended on TIMEOUT, without OOM.

Status: closed investigation. The isolated diagnostic replay also reached
**run-6**, completed **run-5**, and accepted **run-5**. It ended on TIMEOUT,
without OOM. Its run-6 engine time is 357.522 seconds. Do not use instrumented
times as replacement benchmark times.

The diagnostic run-5 is complete. One method accounts for **99.961%** of all
processed items: **1.581 billion** items from **147 initials**. Its work is
**99.600% unchanged routing**. A bounded equality probe proves **7,751,326**
repeated visits after repeat-set resets. This is a work-count problem.

## 1. What the small frontier does, and does not, restrict

The small demand frontier does not bound the work that this engine performs.
It restricts new method initials and selected summary output. It does not
restrict each instruction visit, native-record reuse, or ZERO control work.
The main observed run-5 problem is repeated instruction work in a method with
nonzero initials. A faster demand index would not remove this work.

| Clean measurement | run-5: forward, limit 4 | run-6: backward, limit 5 |
|---|---:|---:|
| Incoming paired demand memberships | 13,901 | 1,304 |
| Incoming distinct entry patterns | 11,525 | 630 |
| Engine seconds | 612.328 | 393.611, TIMEOUT |
| Method input arrivals | 272,759 | 1,280,154 |
| C2 intersection outputs, including repeated offers | 23,930 | 9,298 |
| Fresh initial admissions, including ZERO | 8,647 | 7,914 |
| Accepted subscription-input deltas | 189,337 | 581,374 |
| New ordinary subscription-input groups | 33,836 | 8,910 |
| Ordinary group growth updates after the first update | 155,501 | 554,740 |
| Productive native-record crossings | 304,527 | No complete frontier |
| Selected outgoing demand memberships | 1,304 | No complete frontier |

Counters are END minus START for each run. C2 outputs are initial offers, not
successful input queries. One input can produce several offers. The fresh
initial counter includes direct root and backward-ZERO starts. The run-6
counts describe performed work in an incomplete run.

Whole-window Java samples put C2 and C5 together at about **0.040%** in run-5
and **0.043%** in run-6. The problem is the work after, or outside, those gates.
The clean measurements and CPU data are in the
[campaign report](bidirectional-demand-refinement-workload-20261029.md) and
its [data](data/bidirectional-demand-refinement-workload-20261029.json).

## 2. Diagnostic method and limits

The replay uses an isolated checkout of the same runtime. It keeps 16g,
FULL marks, field limits 1,1,2,..., statics enabled, aliases enabled, and the
1080-second analysis deadline. The proposed stopping fix is not applied.
The production analyzer is unchanged.

Passive actor-owned counters record each processed work item, its lane,
fact kind, premise kind and base. They also record fresh initials, unchanged
offers and repeats, repeat-set resets, work yields, and cached logical tree
sizes. The final dump includes timeout actors before they are released.
Tree size means node occurrences in the logical trie, not unique heap nodes.
These are packets entering `process()`. The counters do not census cumulative
point-store trees, every synchronous subscription callback, or CPU time by
analyzed method. A small processed packet can grow a much larger stored tree.

A bounded witness table tests full equality at selected instructions. Its key
contains the method, instruction, complete premise, full fact and separate
protection mask. Ordinary fact equality alone is insufficient for that last
field. The table starts after one million processed items, selects instructions
by their hash, retains at most 256 keys, and accepts only trees and masks of
at most 1,024 node occurrences. It proves the recorded exact repeats. It does
not estimate a global duplicate percentage.

The input audit checks 7,230 project classes, dependencies, model sources,
toolchain files and copied rule files against the clean campaign. Contents
and scope inventories match. Model, normalized JVM arguments, runner arguments
and Gradle init also match. The diagnostic patch changes passive observers
and adds a focused test. It does not change a transfer or admission decision.

Frontier counts still differ before the active probe starts at run-5:

| Completed run | Clean outgoing demand | Diagnostic outgoing demand |
|---|---:|---:|
| run-1 | 26,469 | 26,469 |
| run-2 | 455,608 | 455,605 |
| run-3 | 52,089 | 52,041 |
| run-4 | 13,901 | 15,827 |
| run-5 | 1,304 | 1,693 |

Run-4 source-seed counts are 900 and 898. The largest run-4 owner difference
is `AdminSettingsController.getNestedProperty`, with 2,060 versus 3,775 rows.
These are not merely callback-count differences. Their cause and semantic
identity equivalence are not established. Do not claim a proved race or
harmless variation from these counts. The diagnostic execution has its own
frontier and is not an identical event trace. No optimization speedup is
calculated between the two runs.

## 3. Run-5: repeated unchanged work in PipelineProcessor

The captured hot owner is:

```text
stirling.software.SPDF.controller.api.pipeline.PipelineProcessor
    #runPipelineAgainstFiles(java.util.List, PipelineConfig)
```

The diagnostic run-5 takes 650.857 seconds. Its final joined actor census is:

| Counter | PipelineProcessor method | All 7,257 method actors |
|---|---:|---:|
| Processed items | 1,581,415,551 | 1,582,038,093 |
| Changed items | 6,332,629 | 6,399,046 |
| Unchanged items | 1,575,082,922 | 1,575,639,047 |
| Direct STATIC-fact items | 471,969 | 572,591 |
| Nonstatic-fact items | 1,580,943,582 | 1,581,465,502 |
| Fresh ZERO initials | 1 | 7,257 |
| Fresh FLOW initials | 21 | 710 |
| Fresh TAINT initials | 125 | 980 |
| Productive native-record crossings | 260,049 | 303,203 |
| Repeat-set clears with changed work pending | 6,190,624 | 6,227,993 |
| Sampled exact repeated processed keys across clears | 7,751,326 | 7,751,326 |
| Processed packets with a protection mask | 0 | 7,104 |

The next largest actor has only 74,192 processed items. Of the hot method's
items, 712 are Reach, 182,102,373 are FLOW, and 1,399,312,466 are TAINT.
The premise-kind counts are the same. Its largest processed spatial tree has
seven logical node occurrences. It averages **248.7 unchanged visits per
changed item**. This ratio describes work volume; it is not a measured neutral
region length or a removable-work percentage.

This owner spends more than 99% of its instruction visits on unchanged facts.
Its large work count does not come from large spatial trees or protection in
the observed owner. Direct STATIC-fact visits are a very small part of its
work. It is mainly nonstatic data under nonzero FLOW and TAINT premises.
The tree-size counter does not bound mark-set width at each leaf. A nonstatic
current fact can also have a static source earlier in its derivation.

The witness table records this identical complete relation twice at node 464,
first in reset epoch 4,722 and then in epoch 4,723:

```text
T = java/security/ssrf.yaml:ssrf#source#1;0;$UNTRUSTED;2

premise:    arg(0).[572,5796].*/T, E=empty; canonical initial id=944
conclusion: var(92).MapValue.Element.<collection-storage>.Element.[any]/T
layer:      DEMAND
field E:    empty
protection: none
```

The premise accessor IDs are retained exactly as logged. They belong to the
live accessor interner; their names were not captured. The readable conclusion
uses `Map#MapValue`, `Iterable#Element` and `Collection#<rule-storage>` from the
probe.

A separate metadata reader reproduces the 712-instruction method from the
same class bytes and selected transformers. It verifies that node 464 is
`parameters.entrySet()` at source line 202, and var(92) is the multi-input
request `body`. The Spring and lambda transformers append replacement blocks
and preserve these original node/local IDs. The reader does not run another
analysis or reconstruct the live accessor interner.

```java
MultiValueMap<String, Object> body = new LinkedMultiValueMap<>();
for (Resource file : matchingFiles) {
    body.add("fileInput", file);
}
// Repeated witness: I944 -> body.MapValue.Element.<storage>.Element.[any]/T, D.
for (Entry<String, Object> entry : parameters.entrySet()) { // IR node 464.
    // This call reads parameters. It does not touch the body fact.
    // The existing call-plan gate therefore routes that fact unchanged.
    if (entry.getValue() instanceof List<?> values) {
        for (Object value : values) body.add(entry.getKey(), value);
    } else {
        body.add(entry.getKey(), entry.getValue());
    }
}
```

Nodes 464 through 482 do not read or assign var(92). Node 483 copies it to
the next loop-carried body local. That copy is an ordinary relevant operation
and must still execute. The method's outer backedge is 642 to 20. The exact
preceding changed producer for each sampled repeat was not recorded. Do not
claim that all 6.3 million changed items themselves are duplicates.

The analyzed method has an outer pipeline-operation loop and nested loops over
files, extensions, parameter entries and list-valued parameters. Its main shape
is shown below. This is a shortened source outline, not an exact IR trace.

```java
PipelineResult runPipelineAgainstFiles(List<Resource> outputFiles, Config config) {
    for (Operation op : config.getOperations()) {
        List<Resource> next = new ArrayList<>();
        for (Resource file : outputFiles) {
            for (String extension : inputFileTypes) {
                for (Entry<String, Object> entry : parameters.entrySet()) {
                    if (entry.getValue() instanceof List<?> values) {
                        for (Object value : values) {
                            body.add(entry.getKey(), value);
                        }
                    } else {
                        body.add(entry.getKey(), entry.getValue());
                    }
                }
                processOutputFiles(sendWebRequest(body), next);
            }
        }
        outputFiles = next;
    }
    return result;
}
```

Container paths produce changed results at operations that use a fact. Each
such result can then walk many other instructions that do not change that
fact. The dynamic instruction cost can be large even when the number of
boundary demand rows is small. The exact-repeat witness below establishes
that part of this work repeats an already processed relation.

## 4. Why the repeat gate permits this work

The current paths are different:

```kotlin
// A changed result uses the durable method point store.
edges.add(successor, premise, facts)?.let { push(it) }

// An unchanged result uses a short-lived repeat set.
worklist.addUnchanged(EdgeDelta(premise, successor, facts))

// This reset can run while changed work is still pending.
fun afterProcess() {
    if (unchangedEmpty) seen.clear()
}
```

Unchanged work has priority over the next changed producer. One producer can
therefore drain a complete unchanged traversal. The repeat set is then cleared.
Another pending producer can send an equal packet through the same instructions.
The durable point store does not check these unchanged admissions.
The producers have distinct admitted points before the join. They converge
through unchanged successors. Two equal changed outputs submitted directly
to the same point would already be deduplicated by `MethodEdgeStore`.

```text
changed queue: [producer L, producer R]

process R:
    F at join -> neutral 1 -> ... -> neutral N
    unchanged queue becomes empty -> clear seen
    producer L is still pending

process L:
    the same F at join is admitted again
    repeat neutral 1 -> ... -> neutral N
```

Here F includes the entire premise, layer, paths, marks, exclusions and
protection mask. This is stronger than observing the same mark or base twice.
The diagnostic replay catches such equal keys after different reset epochs.

A finite model of the current queue policy gives 10,000 unchanged visits for
100 producer packets followed by the same 100-node neutral chain. Each common
node is visited 100 times. The terminal queue is empty and there is one distinct
sink observation. The same model rejects a repeat within one closed unchanged
cycle. Thus a pure unchanged loop is not sufficient to explain an infinite run.
The clean run-5 actually completes. Its problem is excessive finite work.

## 5. Run-6: subscription growth and protected-tree work

The clean run-6 has a different direct cost. Of 563,650 accepted ordinary input
deltas, 554,740 grow an existing group. This is 98.42%, with 63.26 accepted
deltas per new ordinary group on average. These are fresh updates, not duplicate
input calls rejected by storage.

The whole-window Java profile puts 55.74% of samples in protection and 31.27%
at the mask-intersection leaf. The late native capture puts 28.35% inside mask
intersection and 40.69% in GC workers. The denominators differ and the shares
overlap. This is consistent with repeated work on cumulative trees and masks.
It is not evidence that the small C2/C5 demand lookup is expensive.

The diagnostic timeout census now identifies the following work:

| Diagnostic run-6 counter | Count |
|---|---:|
| Processed items | 217,127,496 |
| Unchanged items | 186,388,894, or 85.843% |
| ZERO-premise items | 216,119,741, or 99.536% |
| Nonstatic current facts | 216,872,413, or 99.883% |
| Fresh initials | 7,257 ZERO; 569 FLOW; 41 TAINT |
| Productive native-record crossings | 519,904 |
| Processed packets with protection | 736,382 |
| Sampled exact repeated keys across clears | 370,545 |

These are final performed-work counts at timeout, not a completed demand
frontier. All 7,257 actors admitted ZERO. Only 74 admitted a nonzero initial.

| Diagnostic owner | Processed items | Unchanged items | Protected packets |
|---|---:|---:|---:|
| PipelineProcessor.runPipelineAgainstFiles | 180,207,469 | 158,056,350 | 0 |
| GetInfoOnPDF.getPdfInfo | 31,949,685 | 24,722,374 | 0 |
| ShowJavascript.extractHeader | 2,196,589 | 1,553,937 | 0 |
| AdminSettingsController.updateSettings | 362,774 | 158,959 | 362,581 |
| AdminSettingsController.updateSettingsSection | 362,213 | 245,672 | 361,804 |

The two settings methods account for 724,385 protected packets, or 98.371%
of the observed protected packet traffic. Each has only a ZERO initial.
Their largest processed root and mask each have seven node occurrences.
The largest processed tree anywhere in run-6 has 644 occurrences, in
`PipelineController.handleData`; the largest processed mask has seven.
This does not measure the cumulative trees inside AP output groups, method
stores or summary stores. A processed-packet census is not a heap census.

One final settings sample is:

```text
T = java/security/xss.yaml:xss#sink#1#source#1;0;$UNTRUSTED;2
premise: ZERO
result:  var(31).MutablePair.left.MutablePair.left.StrTokenizer.<rule-storage>
             .ImmutablePair.right.HeaderElementIterator.<rule-storage>.[any]/T
layer: DEMAND; E=empty; protection covers the same whole sampled path/T
```

Another sample reaches the static `AdminSettingsController.pendingChanges`
with four consecutive `StrTokenizer#<rule-storage>` accessors. The source
declares that static as a `ConcurrentHashMap<String,Object>`. These mixed
synthetic container paths are an important next trace target. Their presence
alone does not prove that type pruning is valid under the model/alias contract.
Do not remove them without identifying their producer and proving the change.

The field alphabet has a concrete source in the library models. Pair accessors
read alternative `ImmutablePair` and `MutablePair` fields. Iterator implementation
models read fields such as `StrTokenizer#<rule-storage>`. Model specialization
makes subtype arms available to a generic interface call under type conditions.
An admitted read arm reverses as follows:

```text
Forward:  iterator.storage.* / FLOW -> result.* / FLOW
Backward: result.* / FLOW           -> iterator.storage.* / FLOW

Given:    result.suffix.[any]/T, D
Produce:  iterator.storage.suffix.[any]/T, D
```

This prepends a modeled field; the field limit bounds the word but does not
validate all adjacent field-owner types. `StatementSummary.reversed()` drops
both input and result type filters. This is deliberate behavior in the current
interpreter spec, I5. It is not a new probe defect. Alias metadata can amplify
the model alternatives: its provider discards conditions and turns
`CopyAllMarks` actions into alias assignments. The captured path's exact producer
sequence has not been traced, so the report does not attribute it solely to aliases.

For a receiver-owned storage slot, `ConcurrentHashMap -> StrTokenizer.storage`
has incompatible declared classes. In contrast, `Pair.left/Object ->
MutablePair.right/Object` can be valid: Object can contain the next receiver.
The current forward checker also accepts a valid field prefix without checking
the complete remaining field word. Simply enabling its filters backwards is
not a complete solution. Early rejection needs a defined synthetic-slot type
contract and a proof. It could remove an entire candidate family; rejecting
all mixed names or changing backward filters silently would be a major
unselected semantic change.

Source review finds repeated containment validation after exact root/mask
unions. The clean late profile places 12.85% of samples in mask intersection
under `withRoot -> TaintGroup.add -> transportProtection`, and 11.52% under
`withProtection -> TaintGroup.add -> transportProtection`. These shares are
disjoint captured stack contexts, not separate whole-engine savings estimates.
Removing redundant validation is already a candidate. The more structural
target is to reduce how often compatible result updates enter these groups.
The present evidence does not measure cumulative group width or CPU by owner.
It therefore does not prove that the settings methods own all mask CPU, or
that one containment fix alone will give a two-times improvement.

The diagnostic late CPU capture has 8,792 weighted samples. It independently
puts 32.50% in mask intersection, 39.35% in `TaintGroup.add`, and 43.37% in
`transportProtection`. These inclusive shares overlap. This agrees with the
kind of cost in the clean capture despite the different frontier counts.

## 6. Other work outside the explicit demand count

Every iteration starts the same 3,719 configured roots with ZERO. These include
public/protected project entries and the generated Spring entry. A forward
callee also has implicit ZERO admission. Backward `ZeroIn`
starts ZERO directly. Moreover, the call pipeline registers and replays native
records before it asks C2 to admit new callee body initials:

```text
call input
    -> subscribe and replay existing/native records
    -> apply native results in the caller
    -> ask C2 for new callee initials
```

This order follows the original AP native-reuse contract. It lets known NORMAL
results feed a current demand even when no new callee initial is required.
A focused isolated test derives `ZERO -> ret.$/T` in run-3. With no current
explicit demand or source seed in its caller, replaying that record in run-5
still routes T over each unrelated local statement. Increasing that neutral
chain from one to nine statements adds exactly eight marked visits.

These paths explain why an explicit demand count is not an execution bound.
They do not establish the main run-5 owner: the actor census does that.
Do not remove ZERO or gate all native reuse on local demand. Return summaries
do not preserve all internal sink observations or mixed ZERO/nonzero ND joins.
Such a change would require a new semantic contract.

## 7. Work-removal target

The first Stirling run-5 target is to stop repeated unchanged traversal. Making
`emitUnchanged` a little faster does not address the measured multiplier.
Two designs need a separate proposal and proofs before implementation:

1. Keep exact relation coverage across producer waves at retained neutral
   boundaries. Process only the uncovered part. Preserve the complete premise,
   typed fact header and pointwise protection. Do not retain an unbounded scalar
   copy of every packet at every instruction.
2. Route an unchanged fact directly across a certified neutral region. Reuse
   the same immutable fact at each required boundary. Handle branches and closed
   cycles explicitly. Stop where a transfer, call input, alias, rule observation,
   exit or join can affect that fact. A linear-only certificate can be an initial
   scope, but it may leave the nested-loop multiplier largely intact.

The two designs address different costs: repeated equal relations versus each
required relation's long unchanged route. Changed-packet merging alone does
not remove either cost when only one packet is pending at a time.

Prove path simulation, observation preservation, complete premise preservation,
protection preservation, later join/publication delivery, and fair termination.
Use the actual nested-container loop as a regression case. Measure processed
items, distinct retained relation memberships, exact repeated visits, memory
and time. The counters support a major work-removal target; they do not yet
prove a two-times project speedup.

The analyzer runtime is unchanged by this investigation. The separate next
iteration stopping proposal still applies to OWASP run-5. It cannot stop
Stirling run-5 because that run has 1,304 selected outgoing demand memberships.

## 8. Evidence and checks

The [embedded data](data/bidirectional-stirling-small-demand-workload-20261029.json)
contains the complete final counters for all 7,257 actors in each observed run,
the progress samples and bounded fact witnesses, clean phase counters and
owner maps, input-control audit, passive probe patch, reader source, focused
test receipt, and the source/CFG reconstruction. `actorRowsByRun` uses the
columns in `probe.runs[run].allFinalColumns`. No temporary file is required
to read those counters or the quoted examples.
Rendered method labels are not unique: 7,257 actor rows have 7,254 distinct
labels in each run. Keep rows separate and identify them by run and array
position. Do not merge their counters or join the two runs by label alone.

The isolated observer build passes compilation. Its focused native-replay
test passes all four controls: one versus nine neutral instructions, with
and without the real NORMAL record derived in run-3. It is one test method
with four cases. This validates that small reproduction; it does not prove
a proposed optimization or whole-project semantic equivalence.

Both diagnostic processes are closed. No production core source differs from
the measured runtime. There is no new optimization implementation, no new
baseline run, and no new retained-heap claim. The final status remains
**reached run-6 / complete run-5 / accepted run-5** in both executions.
