# FLOW-backed concrete relations: implementation validation

Date: 24 October 2026. Status: implementation and local validation complete;
fixed project measurements pending.

The selected contract is
[Concrete relations backed by FLOW](../../spec/run1-flow-backed-concrete-relations.md).
The scalar reference runtime is `40e20d16f03ab046df75a53a489bb331b065a9c1`.
The implementation commit will pin the closed local checks. No new project
performance result is available yet. The previous
Thingsboard measurement reached **run-1 OOM**, with no COMPLETE or accepted run.

## Selected behavior

The implementation keeps a separate non-subsumable output mask on a TAINT
tree. The mask is not part of ordinary fact equality, hashing, mark ownership,
or report identity. Admission has two deltas: ordinary membership and new
protection. An unchanged ordinary fact can therefore carry new required
guidance. Repeated identical protection has no delta.

Rule assignment checks the actual triggering conclusion. Same-mark assignment,
local and call restoration cycles, and selected cleaner survivors retain their
marked guides. Multi-input rules keep all contributing original premises and
the original all-ZERO test. Accepted input protection can update an already
emitted rule result. Canonical callee hypotheses do not inherit caller flags.
The caller subscription keeps the flags for composition.

Method-point storage shares diagonal FULL mark geometry. It retains concrete
memberships for local CM and rule evaluation. Summary raw storage, selected
demand storage, and the publication index use the same normalization law.
Only the proved ANY/ANY cell with the same alias-effect class removes a plain
diagonal TAINT output. The FLOW output must admit the mark and have sufficient layer strength.
One annotated FLOW tree path must prefix the TAINT path. Protected, cross-mark,
same-path identity/alias, EXACT, MUST, and unsupported cells keep their required
scalar residuals. A late FLOW compacts current rows. A late protected offer
restores the marked relation. No answered marked-payload archive is retained.

One immutable geometry and exact mark masks represent eligible diagonal rows.
The decoder restores the original marked premise and TAINT header. It never
produces a product of input and output marks. Unsupported geometry keeps the
original typed fallback.

FULL run-1 gives eligible FLOW work priority in the existing nonzero phase.
ZERO policy is unchanged. Changed TAINT work can use a pending diagonal mask.
A certified plain statement applies its geometry once to that mask. Calls,
rules, static operations, mark-dependent filters, endpoints, and observer hooks
use the scalar path. A quantum takes a bounded mask slice and retains the
remainder before successors or barriers. Unchanged work keeps its scalar order
and repeat lifetime.

The uniform ANY continuation passes a `DiagonalDelta` directly to method
storage and the worklist. Storage admits the exact mask before it constructs
any scalar tree. Same-geometry ordinary and protection deltas use set union
and difference. A conflicting overlapping geometry returns the fallback
decision before mutation. Partial protection and unsupported tails are also
classified before decoding. This closes the initial implementation's extra
scalar decode/repack step; shared AP application alone was insufficient.

No field-transfer rule, field limit, source guard, sink condition, static
protocol, IR representation, reference manager, or general query-admission
policy is changed. The removal of covered marked demands and the protection
mask are the selected changes to the handoff contract. The next run consumes
the original FULL guides; it does not consume a new mark identity.

## Local evidence

The constructive Lean build passes 191 jobs. The selected audit checks 460
declarations and 32 executable controls, with no unexpected axioms. This proves
the stated models and local laws. It does not establish a mechanized refinement
of the complete Kotlin/IR engine.

All broad commands are closed. Source hashes before and after the commands
match. Each test suite executes afresh and saves its XML.

| Suite | Fresh scalar reference | Current implementation |
| --- | --- | --- |
| Common dataflow | 1,793 pass | 1,896 pass |
| JVM dataflow | 440 pass | 440 pass |
| Go dataflow | 1,323 pass | 1,323 pass |
| Configuration equality | 5 pass | 5 pass |
| Application | 1,034 tests; 11 failures; 13 skips | 1,034 tests; 11 failures; 13 skips |

The complete case multiset and exact failed assertions match the reference.
There is no new failure, changed failed assertion, or missing baseline case.
The application test heap remains its default 4 GiB. The saved init script
selects cached protoc 3.25 for the Go test build; it changes no analyzer source.

The controls include:

- FLOW tree prefix coverage, exclusions, layers, unsupported tails, deep paths,
  and cancellation.
- Exact diagonal decoding, partial masks, late FLOW, late protection, mixed
  scalar fallback, and current publication replay.
- Triggering-conclusion assignment, local and call cycles, cleaner residuals,
  metadata-only admission, both merge orders, and protected EXACT under ANY.
- Late multi-input protection, all contributing origins, all-ZERO precision,
  local marked observations, and canonical callee ownership.
- Original AP emission, restriction, and summary application without a general
  StrongQueries permission; a field-sensitive same-mark source retains its
  run-2 producer witness.
- Actual neutral engine batching, quantum remainders, barrier drain, endpoint
  fallback, observer fallback, and rule-stage fallback.

One new control caught an annotation idempotence bug before project execution:
an empty subtraction was treated as an absent old mask and re-offered all
protection. The implementation now distinguishes these states. Test fixture
errors and a missing import are preserved as failed attempts in the evidence.

A later review found another flag-loss boundary in the two invocation-local
field-cleaner deduplication sets. Equal plain and protected alias images could
retain only the plain result. These collections now OR their metadata while
keeping the original ordinary key. The actual actor regression fails before
the fix and passes after it, in both arrival orders and in the compiled FULL
cleanup block. The targeted GREEN command passes 17 tests. This is part of
the selected flag-propagation contract; it does not change cleaner transfer.

The [fresh comparison](../../../run1-flow-backed-20261024/validation/local-test-comparison.json)
retains the complete case and failed-assertion checks. The evidence root is
`/drive-testcomp/opentaint-go-rules/run1-flow-backed-20261024`.
Proof logs are under `validation/proofs/`. Current test commands, source hashes,
XML, and terminal receipts are under `validation/current-tests/`.

## Remaining checks

The project campaign must run OWASP, Conductor,
Thingsboard, and Stirling-PDF with their fixed heaps and timeouts through Gradle
`runProjectAnalyzer`. It must compare locations with fresh main, capture CPU
profiles and OOM heaps, and report the latest reached, COMPLETE, and accepted
iteration. No speedup, project precision result, or OOM resolution is claimed
from the local tests.
