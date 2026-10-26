# Correlated concrete implementation: local validation

Date: 26 October 2026. Status: **implementation and local gates complete;
real-project measurements and the run-1 shape investigation remain pending**.

The implementation follows the [selected proposal](../design/bidirectional-correlated-concrete-implementation-20261026.md)
and [general contract](../../spec/run1-correlated-concrete-initials.md).
The pre-change revision is `583a58063ab67ad18b8664d45badee065e68fd85`, with core
`e3ede1a36d3b04d79a23cc93285f385ecd968dbf`. The implemented core is
`f809c4552dd4a7a797fd61595f0932595e56537c`.

The real-project candidate has not started. Its latest reached, completed
and accepted iteration are **unavailable**. The real JVM alias controls
reach **run-3**, including a later marked demand. These controls do not
supply project performance results.

## Selected behavior and scope

A concrete STAR initial now starts as a STAR DEMAND identity. It retains
its field exclusion and shared suffix in all runs and mark modes. Copies
and summaries retain STAR when the suffix relation remains valid. A deeper
read, explicit may target or field cut can still produce ANY.

FLOW replacement now applies to each raw, selected and publication owner
in every run. STAR requires equal output paths and sufficient suffix
admission. ANY retains its prefix coverage rule. The alias-class exception
is removed. Protected, cross-mark and unsupported exact/must/ND rows remain
explicit. Diagonal packets retain their actual tail and exclusion.

Protection uses the triggering conclusion atom in every run. Late flags
remain observable without adding a new join member. Conjunction annotation
replay uses the existing product operation; no product archive is added.
Native and reversed records retain flags. NORMAL FLOW records retain legal
nonempty input and output exclusions.

Independent static pool values remain ANY or EXACT. A selected canonical
initial uses the correlated seed. This change does not relabel an existing
ANY writer image as STAR. Existing static routing, writer registration,
request sets and summary erasure remain unchanged.

Run-1 field exclusions stay empty under the existing cover rule. Later
strong field operations retain exclusions. Field bounds, rule conditions,
source targets, sink semantics, ND premise sets after run-1, queue policy,
run-1 local packing, mark identities, IR and cache managers are unchanged.
No GroundingSupport, new request index, added-facts archive or runtime alias
closure store is introduced.

## Formal and local checks

The constructive Lean build passes 193 jobs. The implementation audit checks
318 declarations and 26 executable controls, with no unexpected axioms.
The [proof dossier](../../spec/correlated-concrete-implementation-proofs.md)
states the model and Kotlin/IR correspondence boundary.

All five broad suites executed afresh. The source guard confirms that the
runtime source did not change during these commands.

| Suite | Current result |
| --- | --- |
| Common dataflow | 1,919 tests; no failures or skips |
| JVM dataflow | 440 tests; no failures or skips |
| Go dataflow | 1,323 tests; no failures or skips |
| Configuration equality | 5 tests; no failures or skips |
| Application | 1,039 tests; 11 failures; 13 skips |

The application gate is not green. A fresh pre-change application run has
1,034 tests, the same 11 failures and 13 skips. Every existing test has the
same status. No test is removed or newly skipped. The five additional tests
are passing alias controls. The complete failure assertions match, allowing
only printed set order to vary. The compared finding sets contain no missing
expected findings and no changed findings. Nine failures are existing cleaner
extras; two are existing Spring fixture setup failures.

The controls cover generic STAR/E seeds, scalar/tree transfer, deeper-read
widening, cleaners, flags and repeat idempotence, exact packet decoding,
STAR/ANY coverage, protected record reversal and nonempty-E native records.
Five actual JVM controls cover both alias/mark event orders, field aliases
and a later demanded alias target. No runtime alias mechanism was added.

The evidence root is
`/drive-testcomp/opentaint-go-rules/correlated-concrete-20261026`.
The [fresh gate receipt](../../../correlated-concrete-20261026/validation/candidate-tests/terminal.json)
contains commands, source hashes and XML hashes. The
[application comparison](../../../correlated-concrete-20261026/validation/application-comparison.json)
contains all existing case statuses and exact failed assertions. The
[alias controls](../../../correlated-concrete-20261026/validation/alias-controls/)
retain the targeted command and XML. The application test heap stays at
4 GiB; the Gradle/compiler process uses 2 GiB. No analyzer heap or timeout
is changed by these test commands.

## Remaining project gates

Measure the committed implementation with the four fixed project commands.
Compare findings with fresh main using main's own rule catalog. Use the same
branch catalog for the pre-change/current optimization comparison. The initial
shared-catalog main commands are supplemental: they report 929 OWASP traces
and do not satisfy the CI expectation of 4,112. The native-main correction
has separate commands and artifacts. Do not substitute those 929 traces for
the required main correctness baseline.

Keep engine time, report barriers, dump pauses and command time separate.
Include latest reached, completed and accepted iterations. Analyze every
actual memory-guard snapshot. Run the read-only section 13 census at the
joined run-1 barrier, with the updated STAR/ANY predicates. Separate retained
memberships, protection-only blockers, other reasons and removal events.
Write the performance report and next-iteration proposal from these new
measurements. This local report claims no project speedup or run-2 completion.
