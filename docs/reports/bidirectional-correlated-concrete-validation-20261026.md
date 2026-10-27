# Correlated concrete implementation: validation

Date: 27 October 2026. **The final runtime and local checks are complete.**
The project performance and finding gates have separate outcomes in the
[performance report](bidirectional-correlated-concrete-performance-20261026.md).

The implemented runtime is `fcfe2e90558665d813bd74207832d4ae3fc83aec`, core
`57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`. The pre-iteration runtime is
`583a58063ab67ad18b8664d45badee065e68fd85`, core
`e3ede1a36d3b04d79a23cc93285f385ecd968dbf`. The intermediate `85dc2bbf8`
runtime is superseded. Its project measurements do not validate the final
runtime.

The implementation follows the [proposal](../design/bidirectional-correlated-concrete-implementation-20261026.md)
and [general contract](../../spec/run1-correlated-concrete-initials.md).

## Implemented behavior

A concrete STAR initial emits a correlated STAR DEMAND identity in all
runs and mark modes. Transfers retain STAR when their shared suffix is
valid. Deeper reads, field cuts and explicit may targets can still emit ANY.
Existing independent static pool values remain ANY or EXACT; they do not
become correlated initials by relabeling.

Raw, selected and publication summary owners use FLOW replacement in all
runs. STAR requires equal output paths and sufficient suffix admission;
ANY uses an annotated FLOW prefix. Complete premise, base, tail, mark,
exclusion and layer gates remain. Protected, cross-mark and unsupported
EXACT/must/ND cases remain explicit. The alias-effect exception is removed
under the selected positive input-alias-closure contract.

Protection uses the triggering conclusion atom. Source/assignment protection,
restored-atom cycles and surviving selected cleaners keep their required
marked dependencies. Late flags emit annotation deltas. Native and reversed
NORMAL records retain flags and legal nonempty initial/output exclusions.
No extra alias-closure store or reference-manager change is introduced.

The final correction makes packed TAINT admission follow the existing scalar
ANY/STAR law across output headers. An existing ANY can cover a later STAR
offer; the opposite order retains the existing nonminimal STAR behavior.
Same-tail exclusion merging, late flags and atomic packet fallback agree
with scalar admission. This is not a new FLOW replacement cell. The correction
retains current residuals, without a scalar history or a duplicate index.

Run-1 field exclusions remain empty under the existing cover rule. Later
strong updates, field limits, rule conditions, source/sink/exit behavior,
ND premise sets after run-1, queue barriers, mark identities, static routing,
requests, writer registration, IR and cache managers are unchanged.
`StrongQueries` remains in later-run execution; the formal replacement
models use the original AP demand-guidance contract and do not model that
authorization policy as an optimization. The performance report explains
this boundary.

## Constructive and local controls

The initial constructive build passed 193 jobs. The final typed-admission
module, updated audit and aggregate entry point each compiled successfully.
The audit checks **356 declarations and 26 executable controls**, with only
the permitted `propext` and `Quot.sound` axioms. There is no Classical choice
or `sorry`. Read the [proof dossier](../../spec/correlated-concrete-implementation-proofs.md)
and [typed-admission proof](../../spec/diagonal-typed-admission-proofs.md)
for the Kotlin/IR correspondence scope.

The admission correction passes 31 focused Kotlin controls. Eight of its ten
new controls fail on the intermediate implementation. Five JVM alias controls
cover both event orders, field aliases and a later demanded alias target;
they reach run-3. These local controls do not prove whole-engine correctness,
termination or complete real-project no-FN behavior.

All broad suites executed afresh on the final runtime. Their source guards
confirm that runtime sources did not change during the commands.

| Suite | Tests | Failures | Skips |
| --- | ---: | ---: | ---: |
| Common dataflow | 1,929 | 0 | 0 |
| JVM dataflow | 440 | 0 | 0 |
| Go dataflow | 1,323 | 0 | 0 |
| Configuration equality | 5 | 0 | 0 |
| Application | 1,039 | 11 | 13 |

The application suite is not green. The fresh pre-iteration run has the same
eleven failures and thirteen skips. All pre-existing statuses and failure
assertions match; the final correction adds ten passing common controls.
The five additional application cases are passing alias controls. Nine
application failures are existing cleaner extras; two are existing Spring
fixture setup failures. Set-print order is the only ignored assertion-text
difference. No existing case is removed or newly skipped.

## Project evidence and limits

The fixed final commands use direct Gradle `runProjectAnalyzer`, configured
heap/timeouts, FULL run-1, statics enabled and default aliases. Thingsboard,
Conductor and PDF reach run-2 and complete/accept run-1. OWASP reaches run-9,
completes run-8 and accepts run-7. Run-1 engine time improves on the three
real projects and regresses 29.69% on OWASP. The 60-second target still fails
on Thingsboard and OWASP. Three actual guard heaps have complete source-bound
offline analyses.

The final exports retain the native-main locations on Conductor and OWASP.
The separate Thingsboard run-1 diagnostic retains all thirteen native-main
locations; the timed export is unavailable. Nine PDF strict native locations
remain missing: seven descendant-guard losses and two marker-present export
fallbacks. The same native-core catalog control reproduces the losses, and
the final export equals the fresh pre-iteration branch export. These are
explicit failed comparison gates, not a complete no-FN claim. The branch
OWASP raw-count gate also fails: 9,179 occurrences versus the expected 4,112,
despite 4,112 unique result bodies. No unrelated catalog or exporter fix is
part of this implementation.

The [machine-readable report](bidirectional-correlated-concrete-performance-20261026.json)
binds the source, commands, test receipts, profiles, heaps, joined run-1
shape partitions, full representative FLOW witnesses and finding cases.
The proposal's required post-implementation investigation keeps stored
memberships, removal events, protection-only blockers and actual work
counts separate. Raw and selected owners are not added. Diagnostic times
are excluded from the timed performance comparison.
