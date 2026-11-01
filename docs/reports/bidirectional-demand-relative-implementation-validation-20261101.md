# Demand-relative summary restriction: implementation checks

Date: 1 November 2026. Language: ASD-STE100 Simplified Technical English.

This note records implementation checks for
[demand-relative summary restriction](../../spec/demand-relative-summary-restriction.md)
and its [implementation proposal](../design/bidirectional-demand-relative-summary-restriction-implementation-20261101.md).
It does not replace the project performance and finding report.

## 1. Selected change and fixed scope

For a previous selected edge `Dp -> Dc`, the current complete demand row
is `(entry=Dc, exit=Dp)`. The new summary path is:

```text
normalized candidate A -> B
    -> exact paired C5
    -> existing AP limit at min(runLimit, FL(that row's Dp)+1)
    -> admitted summary store
    -> publication of its fresh delta
    -> eligible NORMAL persistence / final-header outgoing selection
```

Both NORMAL and DEMAND DATA candidates use this path. A cut can turn a
NORMAL result into MAY/DEMAND. Rejected raw summaries have no stored copy.
This is the selected semantic change. It is not only a storage change.

The implementation must keep C2, initial layers, instruction transfer,
field and mark exclusions, cleaners, aliases, original ND premises, source
permissions, typed Targets, every-offer saved replay, and the global body
limit. It does not add local widening or previous-point guidance.

For DATA, every relevant complete row must be considered. A precise
NORMAL result from one row cannot stop a shorter DEMAND result from another
row. For fixed Reach, one accepted complete row gives the only possible
Reach value, so that query can stop. AP-form ZERO exits from static lookup
use the control path before any field-budget calculation.

## 2. Proof-first evidence

Before the DemandStore runtime edits, this command passed:

```sh
python3 spec/lean/proposals/demand-relative-summary-restriction-implementation-20261101/check.py
```

It compiled ten constructive modules. It checked 182 theorems, including
20 adapter theorems, and audited 303 public declarations. Its only axiom
dependencies were `propext` and `Quot.sound`. The check rejected classical
choice, `sorry`, unsafe, partial, and noncomputable source. At that point,
its reviewed runtime was the unchanged `c4a71246519ee5432879ce82518823f1703f3aa4`.

The [proof dossier](../../spec/demand-relative-summary-restriction-implementation-proofs.md)
states the exact scope. The models establish local paired-gate properties,
cut coverage, finite leaf/delta union, Reach saturation, and final admitted
views. They do not prove the Kotlin implementation, all packed AP adapters,
whole-program convergence, report equivalence, or performance improvement.
A runtime hash is correspondence evidence, not a Kotlin proof.

The same checker passed after implementation with
`--runtime-commit 0ffa5ed8b42dbe193973b4fb4701af28b35716b3`. It binds the
reviewed implementation bytes and the same 182 theorems. The updated
[receipt](../../spec/lean/proposals/demand-relative-summary-restriction-implementation-20261101/checks.json)
explicitly states that source binding does not prove Kotlin correctness.

## 3. Production TDD evidence

The new `DemandRelativeRestrictionTest` uses production `DemandStore`,
`ApOps.restrict`, packed Facts, `ApOps.limit`, and frozen static completion.
The first valid red run had ten tests: nine failed and the exact-rejection
control passed. The failures occurred before the DemandStore change:

| Red case | Old behavior exposed |
|---|---|
| Depth-zero Dp, NORMAL and DEMAND candidate | Deep selected conclusions remained at global depth |
| Two row budgets, both row orders | No required precise-N plus short-D result set |
| Static class anchor and array element | No Dp-relative field cut |
| Protected TAINT and excluded FLOW | No short cut image with transported annotations |
| ZERO-entry DATA | No Dp-relative DATA cut on the control route |
| Precise local result plus composed static row | Raw coverage stopped the shorter static result |
| Full ND original | No short result under its unchanged complete original |
| Finite scalar reference | Packed result did not equal exact-C5-then-per-row-cut |
| Optional numeric counters | The selected cut counters did not exist |

After the runtime change, the first focused receipt reported all ten
DemandRelativeRestriction tests passing. The final source adds a shared
static-carry budget test and an uncut FLOW exclusion assertion. The latest
focused run passed all eleven DemandRelativeRestriction tests.

The added carry test first used an EXACT static initial and expected a
descendant result. Exact C5 correctly rejected it. The final test uses a
concrete STAR initial at DEMAND, with a descendant result. No runtime
matching rule changed to satisfy this test.

The red command and focused command used the Gradle test task directly:

```sh
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.DemandRelativeRestrictionTest \
  --console=plain
```

The final focused run passed 48 tests with zero failures:

| Test class | Tests | Failures |
|---|---:|---:|
| DemandRelativeRestrictionTest | 11 | 0 |
| AnyTaintIterationTest | 7 | 0 |
| GeneratedCurrentProgramTest | 3 | 0 |
| NaiveClosureTest | 15 | 0 |
| ScheduleFuzzerTest | 7 | 0 |
| OneRunAcceptanceTest | 5 | 0 |

Its source changes include a current SELECTED scalar oracle. That oracle
now applies exact C5 and an independent scalar per-row cut before it
records admitted summaries. It selects the final layer for outgoing
rows. The frozen HISTORICAL and PRE_TARGETS branches retain their old
summary rules.

Literal regression assertions now distinguish point results from admitted
summaries. Cleaner, alias, and returned-value tests still check the full
post-exit point result. They require only demand-selected results in the
summary relation. The F76 source case now expects its demanded email
subtree in the NORMAL record, rather than the unrequested whole object.
Its finding and source-seed checks still pass.

Local development logs are `/tmp/relative-demand-red.log`,
`/tmp/relative-oracle-tests2.log`, and `/tmp/relative-full-tests.log`.
They are temporary evidence. The final
repository receipt below must state the final suite result; these paths
are not required inputs for a reader.

## 4. Adapter and regression coverage

| Area | Production check and limit |
|---|---|
| Per-row cap | Literal depth-zero, deeper Dp, global clamp, and both row orders |
| Paired permission | Exact rejection before cut; another initial cannot supply the missing paired permission |
| Packed result | Mixed deep/short leaves compared with an independent finite scalar exact-C5 then scalar-limit enumerator |
| Accessor counting | Static class accessor costs zero; field and array element each cost one |
| Protection | A cut preserves the protected TAINT leaves; existing FLOW-backed store tests cover monotone protection and prohibited replacement |
| FLOW exclusions | Cut clears field E, retains mark exclusions; an uncut result keeps its later-run nonempty E and mark exclusions |
| ND | C5 uses a member only as witness; the complete original remains unchanged |
| Lookup routes | Direct rows, typed ZERO/DATA, shared static carry, and a composed static row after a precise local hit |
| Reach/Target | NORMAL and DEMAND Reach keep their layer; `acceptsTarget` reuses the complete paired query |
| Static lookup differential | `DemandStorageDifferentialTest` compares all three-method call graphs with an independently saturated finite static relation |
| Controls | `ControlDemandTest`, `VirtualZeroExitTargetTest`, and `StaticTargetClosureTest` cover explicit and virtual ZERO permissions and negative pairs |
| Actor ownership | `RestrictedDemandProtocolTest` checks rejected NORMAL absence and cut-before-store/publication/native behavior |
| One-store views | RunSummaryStore, handoff, record, FLOW-backed, and census tests check admitted state and filtered outgoing views |
| Frozen actor | Handoff must read the stable direction and must not query released actor config |
| Diagnostic scope | Counter test checks row/packet counts and depth bins; diagnostics do not modify semantic keys or equality |

The scalar differential case covers a finite field domain and several
budgets, including `Int.MAX_VALUE`. It checks ordinary scalar conclusions.
Separate annotation tests check protection and E/mx. This is not a general
proof that every packed annotation operation equals the scalar model.
The full common and JVM regression suites remain required.

## 5. Final suite receipt

The root implementation task owns the final integrated run:

```sh
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  :opentaint-dataflow-core:opentaint-jvm-dataflow:test --console=plain
```

Implementation commit: `0ffa5ed8b42dbe193973b4fb4701af28b35716b3`.
The final full run passed on fixed source bytes:

| Suite | Tests | Failures | Errors | Skipped |
|---|---:|---:|---:|---:|
| Common dataflow core | 2,232 | 0 | 0 | 0 |
| JVM dataflow | 452 | 0 | 0 | 0 |
| Campaign/profile Python tools | 54 | 0 | 0 | 0 |

The Gradle command also built the analyzer classes. The
[receipt](data/bidirectional-demand-relative-implementation-validation-20261101.json)
records the XML aggregate hashes, source hash, and command. All 738 common
Kotlin source files kept the same bytes during the final run. No test was
skipped or disabled to accept the change. A further 25 cleanup, runner, and
body-statistics tests passed with optimization statistics enabled.

Transfer tests now read the actual completed instruction boundary when
they need to check a result before C5. Summary tests read only admitted
results. The independent SELECTED scalar closure uses exact paired C5 and
its own scalar per-row cut. Its frozen historical controls keep their
original semantics.

The DLINK production driver control still finds its one report and stops
with an empty outgoing frontier. It now finishes at **run-7**, rather than
run-5. Its run limits are `1,1,2,3,4,5,6`. Its run-3 sink witness remains
DEMAND and cannot become a NORMAL report through caller composition.
This is evidence that the selected restriction can require more refinement
iterations. Per-run speed alone is not sufficient for acceptance.

Optional body diagnostics use only numeric counters and bounded copied
samples. Completed runs capture these before actor release. An incomplete
run still exports no actors or stores. If its worker jobs have joined,
the manager can read stopped-owner counters and bounded hot-method samples
before release. A failed join permits no such read. These measurements do
not grant summary, source, Target, or handoff permissions.

## 6. Diagnostics and experiment limits

Optional C5 counters use the existing
`org.opentaint.bidi.optimizationStatistics` switch. Their populations are:

```text
c5RowAttempts          DATA complete-row restriction attempts
c5ExactRejectRows      attempted DATA rows with no exact C5 packet
c5SelectedPackets     exact C5 result packets before the cut
c5LimitCalls           one AP limit call per selected packet
c5LimitResults         limit callback packets, before exact result union
c5CutInputs            selected packets whose maximum counted depth exceeds budget
c5NormalToDemandPackets limit callback packets demoted from NORMAL to DEMAND
c5LocalRows            direct indexed DATA row attempts
c5VirtualRows          primitive/composed static DATA row attempts
c5ControlRows          DATA rows from control lookup, explicit or derived
c5CarryRows            shared-static-carry DATA row attempts
```

`c5MaxDepth{Raw,Dp,Budget,Selected,Admitted}_{bin}` gives marginal packet
maximum-depth or scalar-budget histograms. Bins 0 through 15 are exact;
`16plus` includes all larger values. Packed maximum depth uses cached DAG
metadata. The observer does not enumerate logical paths to count them.

These are attempts and packets, not unique facts, scalar memberships,
per-leaf provenance, or disjoint leaf outcomes. One selected packet can
produce both an uncut packet and a cut packet. A packet max-depth bin does
not state that every leaf has that depth. ControlRows combines explicit
and derived control rows because the existing callback combines them.
`c5Covered` now counts only Reach saturation returns.

Bounded `BIDI_C5_ROW_SAMPLE` observations capture the first 16 DATA row
attempts and then every 4,096th attempt. They retain only the last 64
copied strings. A sample includes the method, route, matching member,
complete Dc/Dp, row budget, and raw/selected/admitted descriptors. Method
text is capped at 300 characters, paths at 12 accessors, exclusions at
eight elements, and mark examples at four. It also records maximum FL and
a protection-presence flag. A rejected row has null selected/admitted
values. No Facts, trie nodes, or method-key references enter this sample
buffer. The example path is a first branch, not necessarily the deepest
branch. These bounded samples do not claim full candidate coverage.

The post-implementation campaign must distinguish body path growth later
collapsed by C5, current-summary input products, repeated equal call-stage
work, exhaustive C5/static search, and reduced native reuse. Marginal cut
counts alone cannot identify the root cause. Use per-method body data,
profiles, bounded captured examples, and reduced production controls as
required by the implementation proposal.

The [completed project report](bidirectional-demand-relative-summary-restriction-performance-20261101.md)
measures identical analyzer bytes at `86ad3b70b`. Latest reached/completed/
accepted iterations are Stirling-PDF **run-8/7/7**, Conductor **run-6/5/5**,
Thingsboard **run-2/1/1**, and OWASP **run-5/5/5**. No project reports OOM.
All current-runtime finding identities remain, and two Conductor baseline
findings return. The pre-existing Thingsboard/Stirling baseline gaps remain
open; test success does not establish their full project acceptance.
