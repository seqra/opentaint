# Restricted demand: candidate repairs for the open contracts

Date: 27 October 2026. Status: **candidate design; user decisions pending**.

Update, 28 October: the user selected ignoring field E on abstract STAR
demand. Section 2's exclusion-union candidate is superseded; do not
implement it. See the [follow-up review](bidirectional-restricted-demand-followup-20261028.md)
and the updated selected spec. The previous live pre-exit writer-directory
candidate is also under review in favor of a separate killed-write store
used only during transition. The rest of this document is historical
candidate evidence, not a new selection.

This document makes the proposed repairs concrete for review. It does not
select their behavior. The runtime remains at the intermediate state in
[the validation report](../reports/bidirectional-restricted-demand-validation-20261027.md).
The active implementation contract is
[restricted-demand-static-closure.md](../../spec/restricted-demand-static-closure.md).
Follow [proof-guide.md](../../spec/proof-guide.md).

No project scan was made for these candidates. The last referenced
Thingsboard campaign reached **run-2**, completed **run-1**, and accepted
**run-1**. The failed local handoff cases reach and complete **run-3**.
Their final forward report is empty and is incorrect. Controls without
the static exit kill keep the finding.

## 1. Decisions, semantic scope and acceptance

The intermediate implementation of the selected pipeline exposed three
counterexamples. The user has been asked to select each behavior. A
passing proof of a candidate does not select that candidate.

| Contract | Current selected behavior | Candidate repair | Semantic effect |
|---|---|---|---|
| Abstract STAR demand with field E | Reject nonempty E under a producer invariant which the actual cleaner disproves | Accept it; keep the shared FLOW start if it satisfies the input; otherwise use the proved same-path E intersection | Extend restricted initial selection in the formerly unsupported case |
| Concrete named static field at a run-2 call | STAR can be emitted as an initial, but the next input validator rejects it | Accept bounded named-field STAR with legal E; retain the concrete anchor and direction guards | Extend the valid actual-input domain; preserve correlation |
| Pre-exit static dependencies | Only post-exit W/R and post-exit B contribute to handoff closure | Retain the reached pre-exit dependencies needed by internal reads and preserve their actual caller bindings | Extend guidance permission after an exit kill; no new executable normal summary |

The third repair must cover FLOW as well as colored dependencies, static
copies as well as nonstatic writers, and returning wrappers. Keeping only
the already added concrete producer-pool channel does not satisfy it.
Source/ZERO dependencies must also have a defined route. The detailed
candidate in section 4 states the route and the remaining proof limits.

Keep these mechanisms unchanged in all three candidates:

- Strong field writes, cleaners, field limits and AP transfer.
- Concrete-mark eligibility: FLOW cannot establish T for a concrete entry.
- C5 paired summary restriction, full ND guards, raw NORMAL records and
  the original backward-ZERO return.
- Rule identities, source/sink occurrences, mark ownership, primitive
  tracking, FULL/GROUP modes and the selected run schedule.
- The run-1 static approximation of call order and context.
- Normal-exit rule order, immediate producer effects, and the prohibition
  on normal-summary publication from a producer-effect callback.
- The exclusion of GroundingSupport, added-fact history, IR storage changes
  and new cache/reference owners.

If a detailed repair needs another major change, state it and obtain its
intended behavior before runtime implementation. Do not use an exception,
cast, coarse query, or normal record to hide one of these counterexamples.

Implementation can continue after the behavior decisions, in this order:

1. Update the selected spec from the chosen repairs. Discharge the required
   adapter and coverage proofs below before dependent runtime changes.
2. Change the two demand/input boundary adapters. Keep scalar and packed
   behavior equal, including MUST inputs in later forward runs.
3. Implement the complete pre-exit guidance route. Freeze it only after
   its counted work and ordinary run-1 work reach quiescence.
4. Turn each reproduced failure into a passing correctness regression.
   Keep no-kill controls, both mark modes, static-copy cases, ZERO sources
   and returning wrappers. Keep the negative grammar tests.
5. Run the complete required local checks. Record the eight existing
   cleaner FP-only cases separately from any new missing finding.
6. Commit the implementation. Run only the configured four-project
   campaign on that commit. Reuse the fixed baseline without rerunning it.
7. Report findings, iteration times, transition work, CPU and heap data.
   Use those measurements to rank the next optimization proposal.

The five existing missed-finding tests must not be disabled or changed to
expect an empty report. Diagnostics which currently reproduce validator
rejection must be changed to assert the selected valid behavior once that
contract is implemented. The final campaign and next optimization proposal
remain required deliverables of task.md.
## 2. Candidate: retain excluded STAR demand and refine the FLOW initial

Status: **candidate; not selected**. The user must select the behavior
before implementation. The proof below proves the candidate operation.
It does not select that operation or change the current runtime contract.

### 2.1 The open contract and the required semantic change

The selected spec preserves STAR and field exclusion E at handoff. It
also rejects an abstract STAR entry with nonempty E. That rejection needs
a producer invariant. The invariant is false for supported later-run
operations. Run-1's empty-E rule does not prove it for later runs.

```text
// Code under analysis. removeAllBelow has RemoveAllMarks(x.[any]).
method(x, y) {
    x.f = y;
    removeAllBelow(x);
    return x;
}

// One legal later-forward FLOW path. y has no fact in this path.
initial:       x/STAR/{}/FLOW
strong write:  x/STAR/{f}/FLOW     NORMAL
partial clean: x/STAR/{f}/FLOW     DEMAND
return:        ret/STAR/{f}/FLOW   DEMAND
handoff entry: ret/STAR/{f}/FLOW   // Current builder rejects it.
```

`JIRRuleForms.unconditional` lowers `RemoveAllMarks` on an `[any]`
position to `CleanReach.BELOW`. The current packed AP probe confirms
this path with a real strong-keep edge, that cleaner, and a return rebase.
The partial cleaner keeps the existing conservative DEMAND result. This
candidate does not change the cleaner or the strong write.

The candidate accepts the preserved abstract STAR/E demand. It changes
**initial selection** when the ordinary shared FLOW initial cannot apply
to an actual input. This is a semantic extension of the selected demand
protocol. It is not a field-transfer or storage-only change.

| Mechanism | Current selected contract | Candidate contract |
|---|---|---|
| Abstract STAR/E demand, E nonempty | Reject; require a producer proof | Accept the preserved demand |
| Ordinary shared FLOW initial already satisfies actual input | Emit the FLOW form of demand | Keep that same initial |
| Same-path excluded regions with neither satisfaction test true | Builder rejection; bypassing it can emit an unusable initial | Emit a STAR/FLOW initial with the union of the two field exclusions |
| Concrete T entry | Require an eligible actual concrete mark; use the existing location intersection | Unchanged |
| Actual field exclusions | Keep them on the input fact | Unchanged; compute a separate initial |
| Initial tail and layer | Use the existing start table | Unchanged; the new abstract initial has STAR tail and starts FLOW in NORMAL |
| Summary restriction and records | Apply C5; retain legal native exclusions | Unchanged; the complete new initial, including E, remains its original |
| Field writes, cleaners, field limits, aliases, protection | Use the selected current operations | Unchanged |
| Demand authority | Only fixed demand can start restricted work | Unchanged; no actual-input query or new exit permission is added |

### 2.2 Why accepting the demand alone is insufficient

Let f, g and h be distinct fields. Both the demand and the actual input
admit `x.h`. The old shared initial cannot serve the actual input:

```text
demand:        x/STAR/{f}/FLOW
actual:        x/STAR/{g}/FLOW
old initial:   x/STAR/{f}/FLOW

inside(initial, actual)     = false // Initial admits g; actual does not.
applicable(initial, actual)= false // Actual admits f; initial does not.

candidate:     x/STAR/{f,g}/FLOW
inside(candidate, actual)   = true
insideDemand(candidate,d)   = true
candidate covers x.h       = true
```

The original Lean counterexample `Abs.vec_emitW_starE` proves the same
failure with two incomparable exclusions. `Abs.emitW_needs_patTail`
shows that the old C2 claim is false without its guard. Thus, removing
only the builder check would leave a real coverage gap.

### 2.3 Candidate emission algorithm

Keep the existing concrete branch. In the abstract branch, first test
the old shared initial. Use the fallback only when that initial does
not satisfy the actual input.

```kotlin
// Candidate only. Do not apply before the behavior decision.
fun emitCandidate(entry: Pattern, actual: Pattern, marks: MarkTable): Pattern? {
    if (entry.fact.mark != MarkSlot.STAR) {
        return commonPart(entry, actual, marks) // Existing concrete branch.
    }
    if (!overlap(entry, actual)) return null

    val shared = flowForm(entry)
    if (satisfies(shared, actual, restricted = true)) return shared

    // The local proof isolates this one unresolved geometry cell.
    check(entry.fact.base == actual.fact.base)
    check(entry.fact.path == actual.fact.path)
    check(entry.fact.tail == Tail.STAR)
    check(actual.fact.tail == Tail.STAR || actual.fact.tail == Tail.ANY_TAINT)
    return shared.copy(exclusion = entry.exclusion.union(actual.exclusion))
}
```

E is the **field** exclusion. It is not a mark exclusion. The fallback
keeps the entry base, path, STAR tail and FLOW mark. It does not copy an
actual concrete T into the initial. It does not copy actual FLOW mark
exclusions into the shared mark. The caller retains the actual fact for
ordinary summary matching and application.

`Tail.ANY_TAINT` is the runtime spelling of MUST. It does not mean the
uncorrelated ANY tail. The fallback guard must remain exact:

| Geometry after overlap succeeds | Candidate action |
|---|---|
| Shared initial satisfies actual | Return it, including when one E contains the other |
| Same path; entry STAR/Ed; actual STAR/Ea; shared initial fails | Return STAR/(Ed union Ea)/FLOW |
| Same path; entry STAR/Ed; actual MUST/Ea; shared initial fails | Same STAR/(Ed union Ea)/FLOW; never emit MUST/FLOW |
| Actual path strictly below entry | Keep the old shared initial; entry E must admit the first step |
| Actual path strictly above entry | Keep the old shared initial; actual E must admit the first step |
| Same path; actual EXACT or ANY | Keep the old shared initial; no fallback is needed |
| Different base or divergent paths | No initial |

In the two different-path cases, E belongs to its own path. Do not union
an ancestor's E into an initial at a different path. The already selected
concrete-emission rebasing rule stays separate.

The boundary changes would be limited to these operations:

```kotlin
// DemandStore.Builder, only if this candidate is selected:
check(entry.fact.mark !is MarkSlot.Star ||
    entry.fact.tail == Tail.ANY || entry.fact.tail == Tail.STAR)
// Keep normalized marks, no MUST demand, no abstract EXACT typed initial,
// the exact-exit paired guard, valid field E, and static anchor checks.

// Restricted entry processing stays the same:
for (d in fixedDemand.near(method, actualPattern)) {
    for (j in ops.emit(d, actualFacts)) addInitial(j)
}
```

The initial interner and start-once store already include E in their
identity. Use them as now. Two actual marks with the same resulting E
share one FLOW body. This candidate adds no mark catalog or request store.

The mark gates remain asymmetric:

```text
entry T, actual FLOW            -> no initial
entry T, actual FLOW excluding U-> no initial, even if U != T
entry T, actual T               -> existing concrete intersection
entry FLOW, actual T            -> FLOW initial, possibly with refined field E
```

### 2.4 Proofs and limits

The candidate model is
[ExcludedFlowCandidate.lean](../../spec/lean/proposals/restricted-demand/ExcludedFlowCandidate.lean).
It imports the original AP algebra. Its executable operation keeps the
old FLOW form when `satW` accepts it. Otherwise, it unions the two E values
in the same-path STAR cell. Concrete entry emission stays exactly equal
to the old operation.

| Audited declaration | Result |
|---|---|
| `shared_satisfies_outside_same_star` | Every common-location case outside same-path STAR/STAR already satisfies the shared FLOW initial |
| `same_star_union_contract` | The union-E initial covers each common location, satisfies the actual input, and lies wholly inside demand |
| `choose_contract` | The chosen initial satisfies C2 for arbitrary excluded STAR demand in the original `Kind` algebra |
| `candidate_star_contract` | The executable candidate emits a coverage witness for each common location of an abstract demand and actual input |
| `concrete_unchanged` | The concrete-entry operation is unchanged |
| `no_exact_flow` | Typed abstract ANY or STAR/E entries produce STAR, never abstract EXACT or MUST |

All six audits compile constructively. Only `propext` and `Quot.sound`
occur in their axiom lists. There is no classical choice, new axiom or
unproved placeholder. The checked command and output are in
[excluded-flow-candidate-checks.json](../../spec/lean/proposals/restricted-demand/excluded-flow-candidate-checks.json).

The model's original `Kind` has EXACT, ANY and STAR. It does **not** have
the current MUST constructor or the complete typed packed runtime. The
MUST row remains an explicit adapter obligation. Under a STAR initial,
a MUST/E actual input has the same location and first-accessor-exclusion
tests as STAR/E. Implementation acceptance must prove that projection for
the current satisfaction functions and compare scalar and packed results.
This local observation is not a whole-analyzer proof.

The proof also does not establish call binding, compiler lowering,
iteration completeness, record reversal, or the complete AP extension.
Those contracts remain separate. No new project experiment was made for
this candidate. The latest project campaign referenced by the selected
spec reached **run-2**, completed **run-1**, and accepted **run-1**.

### 2.5 Sharing and expected cost

The current shared FLOW form remains the first choice. Comparable E
values, EXACT and ANY actual inputs, and different-path inputs retain
that sharing. The fallback adds at most one initial per scalar actual/demand
pair before canonical deduplication. Its key differs only by field E.
It adds no per-mark body execution and enumerates no concrete marks.

Different incomparable E values can produce different FLOW initials.
Thus, accepting this candidate can increase the number of method bodies
relative to rejecting the input or widening E away. No speedup or memory
bound is claimed. The purpose is to preserve excluded demand and satisfy
C2. A future measurement must count ordinary shared starts, fallback
attempts, distinct fallback initials and their work by run iteration.

The direct fallback cost is an E union plus canonical initial lookup.
The satisfaction test is local geometry and exclusion matching. An
implementation can retain its proved empty-E fast path; it must not
change the selected result. No new queue limit or cache owner is needed.

### 2.6 Alternatives this candidate does not select

- Keep the producer assumption: the supported strong-write/partial-cleaner
  trace above refutes it. Empty run-1 E is insufficient for later handoffs.
- Accept excluded STAR demand but emit only the old shared form: the
  incomparable-E counterexample refutes C2.
- Drop the demand: this can remove the only guide for the required path.
- Widen only unsupported abstract STAR/E entries to ANY/empty E: this is
  a possible separate user decision. It loses the preserved correlation
  and field E, so it does not implement this candidate.
- Restore all actual-input queries or StrongQueries: that changes demand
  authority and summary permission outside this local repair.
- Change field writes, cleaners or actual input E to prevent the producer:
  that changes the selected field semantics.

A proof of this candidate supplies no permission to select it. Keep the
current rejection until the user selects the intended contract.

### 2.7 Regression and acceptance plan if selected

1. Keep the producer trace as a regression. Assert the preserved excluded
   STAR demand, successful emission and a correct applied answer after
   the handoff. Do not change the existing write or cleaner result.
2. Check equal, subset, superset, disjoint and overlapping E values,
   Empty and Universe E, and ancestor/same/descendant path relations.
3. Extend the finite scalar/packed entry matrix with abstract STAR/E.
   For every admitted common location, check coverage, whole-demand
   containment and satisfaction. Keep concrete T/FLOW mismatch controls.
4. Prove and test the MUST projection. The emitted abstract initial must
   remain STAR/FLOW; its start must not acquire a MUST guarantee.
5. Check sharing across actual full marks and mark exclusions. Repeated
   identical E unions must not restart a method. Actual caller facts and
   their mark exclusions must remain intact.
6. Check C5, native NORMAL records with nonempty initial E, reversed
   record application, and both input/answer arrival orders.
7. Run the complete common, JVM and application suites. Then run only
   the configured OWASP and selected project campaign. Report the latest
   reached and completed run, handoff cost, fallback work, and findings.
## 3. Candidate: admit bounded named-field STAR inputs in run-2

**Status: pending user decision. This section does not authorize a runtime
change.** The current runtime remains unchanged for this item.

The current run-2 input validator accepts concrete named-field inputs with
EXACT or ANY tails. The restored emitter can produce a concrete STAR initial.
Its start fact also has STAR. An ordinary FLOW copy can keep that tail until
the fact reaches another call. The static input validator then rejects the
fact. The selected AP representation can represent that fact.

This is a change to the accepted input domain. It is not a storage-only
optimization. It changes the validator at a run-2 call or seed boundary.
It does not change rule guards, field transfer, marks, layers, exclusions,
caller bindings, or the increasing field-limit schedule.

### 3.1 Current and candidate domains

T below is an actual FULL mark. G used as a guide remains metadata. A guide
must not turn G into an executable FULL mark without an actual FULL input.
The class accessor C costs zero fields. The named field f costs one field.
Thus `S.C.f` has field depth 1. Run-2 keeps field limit 1.

| Actual input after the existing field cut | Current validator | Candidate validator |
|---|---|---|
| `S.C.f / EXACT / {} / T` | Accept | Accept |
| `S.C.f / ANY / {} / T` | Accept | Accept |
| `S.C.f / STAR / {} / T` | Reject | Accept |
| `S.C.f / STAR / E / T`, with legal nonempty E | Reject | Accept and retain E |
| `S.C.f / EXACT or ANY / nonempty E / T` | Reject | Reject |
| `S.C / EXACT / {} / T`, an exact global class marker | Accept | Accept |
| `S.C / STAR or ANY / E / T`, a class-wide input | Reject | Reject |
| `S / any tail / E / T`, a broad static-root input | Reject | Reject |
| MUST, with any static position or E | Reject | Reject; backward MUST facts are forbidden |

E can be Empty, a finite field exclusion, or Universe when the existing
STAR representation permits it. The validator does not move E to another
path. EXACT and ANY have Empty E. The exact class marker stays distinct
from every named field of that class.

The normal field cut still handles a longer named-field path. For example,
`S.C.f.g / STAR / E / T` can become `S.C.f / ANY / {} / T` under limit 1.
This is the existing field-limit operation. The validator does not perform
that cut. It also does not convert a bounded `S.C.f / STAR / E / T` to ANY.
The existing backward fact contract must reject MUST before a cut could
hide that invalid tail.

### 3.2 The relay which exposes the domain gap

These are legal AP shapes under the correlated-concrete extension:

```text
Actual supplied input:  ret / ANY / {} / T
Fixed entry guide:      ret / STAR / {} / T

ordinary demand intersection:
  initial = ret / STAR / {} / T

ordinary start:
  (ret / STAR / {} / T) -> (ret / STAR / {} / T), DEMAND

ordinary backward copy of a static read:
  ... -> S.C.f / STAR / {} / T

static projection at the next call:
  S.C.f / STAR / {} / T       // unchanged

current input validator: reject
candidate validator:     accept
```

The fixed concrete STAR guide and the actual FULL input are premises of
this trace. The trace does not claim that a getter alone creates that guide.
A getter and an earlier transparent call can carry the resulting fact:

```java
Object wrap() {
    relay();
    return get();
}
Object get() {
    return C.f;
}
void relay() { }
```

Backward execution can bring the static requirement from `get()` to the
input of the earlier `relay()` call. Statics are projected as is. A method
must have fixed demand before it emits an initial; accepting the input does
not itself authorize an initial. The normal AP emitter and paired summary
restriction still decide what can start and what can be published.

With nonempty E, the same-slot relay keeps E at `S.C.f`. Existing reads,
writes, cleaners and path intersections can still change or reject the
fact under their own rules. This proposal adds no new E update.

### 3.3 Candidate validator change

The input check stays after the existing field cut. The existing anchor
check also remains on producers before the cut. A deeper producer output
can have the same named-field anchor before the bound is applied.

```kotlin
// Candidate only. Apply after the user selects this domain repair.
fun validateRun2StaticFullInput(ap: ApManager, actual: Pattern): Boolean {
    val field = validateRun2StaticFullAnchor(ap, actual) ?: return false
    val fact = actual.fact

    if (field) {
        check(fact.path.size == 2)
        check(fact.tail == EXACT || fact.tail == ANY || fact.tail == STAR)
    } else {
        // The anchor helper has proved: one class accessor, exact marker.
        check(fact.path.size == 1 && fact.tail == EXACT)
    }
    check(actual.exclusion == Empty || fact.tail == STAR)
    return field
}
```

The helper still rejects a FULL static root and a class-wide FULL input.
Actual FULL marks and guide group selectors keep their current separate
roles. Global backward checks still forbid MUST. The return value still
identifies a named field; it is not an initial-emission permission.

No StrongQueries state is added. No actual-input query is registered. No
ANY-to-EXACT start is added. The selected STAR-preserving normalizer stays
as specified. Run-1 initial shapes and its Empty E rule stay unchanged.

After a decision, the required checks are:

- A named-field STAR input with Empty E passes both seed and caller-input
  validation. It can start only through a matching fixed guide.
- A named-field STAR input with each legal E keeps its path, tail, mark and
  E through same-slot projection and an unmodified FLOW identity.
- EXACT and ANY inputs with nonempty E still fail. Broad FULL roots,
  class-wide FULL inputs and backward MUST still fail.
- The exact class marker stays exact. It does not match a named field.
- Scalar and packed AP operations give the same accepted relation. An
  actual concrete mark is not created from FLOW or from a group selector.

### 3.4 Constructive proof and its limits

[StaticInputGrammar.lean](../../spec/lean/proposals/restricted-demand/StaticInputGrammar.lean)
contains 15 local audited declarations. They check the old and candidate
FULL static grammars, the new STAR cell, rejected broad roots and class-wide
inputs, rejected MUST and group-valued actuals, same-slot projection, the
existing field bound, and any finite number of bounded STAR relays.

Two laws use the existing correlated AP reference directly:
`actual_AP_identity_keeps_concrete_star` keeps the complete STAR/E fact
through a FLOW identity, without the historical STAR erasure;
`actual_AP_limit1_keeps_named_star` keeps the fact under field limit 1 when
the class accessor is uncounted and the field accessor is counted.

The checked assumptions are explicit. The caller must really supply the
FULL input. Static projection is identity. The adapter must identify the
class and field accessors correctly. Backward MUST is outside the input
domain. The proof subdomain rejects a GROUP-valued actual; this does not
add a runtime rejection to the existing non-FULL metadata path. This
local model does not prove method reachability, demand
completeness, caller-subscription fairness, or the complete JVM adapter.
It does not authorize the separate pre-exit producer-demand proposal.

The successful command was:

```sh
cd spec/lean
LEAN_PATH=.lake/build/lib/lean lean -j 1 -M 2048 \
  proposals/restricted-demand/StaticInputGrammar.lean
```

[The audit receipt](../../spec/lean/proposals/restricted-demand/static-input-grammar-candidate-checks.json)
records all 15 successful audits. They use at most `propext`. There is no new axiom, choice, or proof
placeholder. The first 512 MiB attempt ran out of proof-process memory;
the successful audit used 2 GiB. These are proof-tool settings, not project
measurement settings. No project run or runtime test was performed for
this candidate section.

## 4. Retain pre-exit writer dependencies for guidance

**Candidate only. The user has not selected this contract.** It changes
which relations can guide run-2. Do not implement it, commit the runtime,
or start the project campaign before the decision and the proof gates below.

The finite failing controls reached and completed **run-3**. Run-1 found
the sink, but the run-3 report lost it. This happens in FULL and GROUP
mode. Local W, one or two returning wrappers, and a local static/static B
copy fail. The three controls without the exit kill pass. These are finite
engine controls, not project performance results.

### 4.1 Current behavior and the proposed change

```java
main() { sink(wrap(sourceT())); }
wrap(p) { return get(p); }
get(p) {
    C.f = p;
    return C.f;
    // NormalExit rule removes the outgoing C.f value.
}
```

```text
run-1, get:
  before exit:  arg0/FLOW -> C.f/FLOW     // writer dependency PW
  after exit:   no outgoing arg0 -> C.f
  retained:     C.f/FLOW -> ret/FLOW      // reader R

current run-2 demand for get:
  ret/FLOW -> C.f/FLOW

body-derived run-2 answer:
  ret/FLOW -> arg0/FLOW                   // C5 rejects this answer

candidate additional guidance:
  arg0/FLOW -> ret/FLOW
  reversed: ret/FLOW -> arg0/FLOW
```

The actual paired guide must also exist in `wrap`. Merely retaining the
callee's formal `arg0 -> C.f` at `get` cannot establish it in `wrap`.
The caller must use its real input binding to obtain
`arg0_wrap -> C.f`, then compose that relation with its own
`C.f -> ret_wrap` reader relation.

| Mechanism | Current implementation | Candidate |
|---|---|---|
| Writer killed by exit rules | Absent from the handoff writer inventory | Retain its bounded pre-exit dependency as guidance input |
| B copy killed by exit rules | Absent from the post-exit B inventory | Retain its pre-exit B dependency as guidance input |
| Nonstatic or ZERO writer at a callee | No guide-only caller binding if its outgoing summary was killed | Replay and bind the pre-exit relation through existing actual caller inputs |
| Static/static relation at a callee | Only post-exit B can use detached call-graph visibility | Both pre-exit and post-exit B use that same static visibility rule |
| Outgoing executable summary | Exit rules decide its actual value | Unchanged: only its post-exit value can be an ordinary summary or record |
| Live global pool | Its independent producer-effect route preserves the earlier write | Unchanged: guidance alone never supplies a group |

These are major changes to guidance construction. They are not a field
transfer change. Keep the current marks, complete rule guards, singleton
run-1 originals, field limit, field exclusions, cleaners, aliases, static
call-order/context approximation, and FULL/GROUP specialization unchanged.
Keep C5 and demand-only restricted emission. Do not restore SQ permission,
unconditional actual queries, or a raw-answer scan.

### 4.2 Relation inventory

Use these names so a prefix dependency cannot be mistaken for an exit
summary:

```text
PW[M] : J -> S       // reached pre-exit writer, ordinary or real ZERO J
PB[M] : S1 -> S2     // reached pre-exit static/static writer
W[M]  : J -> S       // existing post-exit outgoing writer
R[M]  : S -> Y       // existing post-exit productive reader
B[M]  : S1 -> S2     // existing post-exit static/static seed
```

S is a valid named static field/path or an allowed EXACT class marker.
A broad root/class carry is still a separate same-position family. Do not
use that broad carry as a graph vertex which connects unrelated fields.

Capture each result after its existing guard, diagnostic gate, run-1 cover
and field bound. Capture it **before** routing it to NormalExit or applying
later exit rules. Keep every contributing singleton original. Do not
capture a partial ND guard or change a nonzero original to ZERO.

Include all actual static producers, not only plain assignment syntax:
local write/alias/source micro-edges, completed guarded source actions,
and their relevant call-bound dependency results. A call-bound result does
not register a new local writer. Passive unchanged static facts remain
suppressed.

Retain FLOW relations and all colored relations. A FLOW dependency is a
diagonal mark relation. A colored dependency keeps the complete input and
output selectors, including a restored T-to-U-to-T path. ZERO uses the
existing real ZERO original and private NoInput selector, not a new mark.
Do not remove a colored guidance relation because FLOW covers its geometry.

### 4.3 Stores and owners

| Store | Owner and contents | Lifetime |
|---|---|---|
| Shared prefix-key interner | Immutable writer geometry, complete original and mark-relation blocks; no input Facts or callbacks | Run-1, then only the keys used by the frozen view |
| Prefix memberships | Per-method actor; exact IDs for PW/PB and caller-bound dependencies | Run-1, then immutable handoff memberships |
| Outgoing prefix-guidance index | Callee's existing run-owned summary directory; PW keys, including FLOW and ZERO, with ordinary replay/notification ownership | Run-1 only |
| Existing caller subscriptions | Actual caller original, input, call/stage and layer | Unchanged; no second added-fact history |
| Existing producer-effect index | Its current concrete nonzero/nonstatic actual bindings for the global pool | Unchanged; not the complete guidance inventory |
| Frozen completion | Prefix/post-exit keys, method memberships, detached call graph and existing W/R attachments | Incoming run-2 only |

A prefix key is thin data. For example:

```kotlin
// Pseudocode. A production adapter keeps packed mark blocks and paths.
data class PrefixKey(
    val original: CompleteInitialKey,
    val image: PackedEndpointKey,
    val marks: MarkRelationBlock,
)

class PrefixMemberships {
    val ids: MutableSet<PrefixId> = exactSet()
}
```

Do not retain a full `Facts` packet, statement, call plan, continuation,
runner, source-rule object, or new support object in a frozen key. Share
identical keys across methods. Keep only exact method memberships locally.
Use packed mark blocks rather than one full relation object per mark.
Scalar expansion is suitable for the small reference model, not a required
production representation.

For live caller binding, preserve the raw mark exclusion and tail data
needed by the ordinary AP operation. Normalize guidance only after that
binding. Dropping mx or changing MUST to ANY before binding can enlarge
the actual binding relation; this candidate does not select that change.
Protection is not a new equality flag on executable facts. Frozen guidance
keeps colored rows independently of FLOW coverage.

### 4.4 Capture and caller propagation

```kotlin
fun observeBoundedStaticProducer(at: OperationInput, bounded: Facts,
                                continueRules: ResultSink) {
    // Existing validation, complete guard and bound have already run.
    val original = at.premise as InitialAp
    val key = prefixKeys.intern(original, bounded)
    if (prefixes.add(key)) {
        if (original.base == STATIC) {
            // PB is inherited at handoff. No B call-chain relay.
        } else {
            prefixDirectory.publish(key) // Includes FLOW and genuine ZERO.
        }
    }
    preserveExistingProducerEffects(original, bounded)
    val boundary = at.site as? ResumeSite.BoundaryInput
    if (boundary != null && !boundary.atStart) {
        continueRules(original, bounded) // Already inside exit rules.
    } else {
        routeBoundedRun1StaticToExit(original, bounded)
    }
}
```

An exit-rule-produced write is observed at its operation boundary, then
continues the current exit pipeline. It must not run NormalExit rules a
second time. Keep the existing body-versus-exit `ResumeSite` distinction;
add no AP flag. Passive exit output is not a second producer capture.

Use a separate delivery kind for prefix guidance. Do not put it in the
ordinary publication index. Do not change AP or `Publication` equality.
A binding callback has this behavior:

```kotlin
fun bindPrefix(sub: Subscription, key: PrefixKey) {
    val initial = key.original.asInitial(ap)
    val actual = ops.satisfying(sub.added, initial, run1Mode) ?: return
    key.withTransientResult(ap) { result ->
        ops.applySummary(actual, initial, result, run1Mode,
            original = sub.ref.premise,
            out = { value ->
                existingBoundAndRun1Cover(value) { bounded ->
                    // No CFG or normal-exit work is produced by this callback.
                    captureBoundPrefix(sub.ref.caller, sub.ref.premise, bounded)
                }
            })
    }
}

fun captureBoundPrefix(owner: MethodKey, original: InitialAp, value: Facts) {
    val id = prefixKeys.intern(original, value)
    if (!prefixes(owner).add(id)) return
    if (original.base != STATIC) prefixDirectory(owner).publish(id)
    // A static original makes this a PB row at this owner.
}
```

Actual input projection is still required for nonstatic arguments. It is
already present in `sub.added`. Only the resulting static position keeps
its coordinates. No extra static input projection or BIND_BACK is added.
Do not copy a callee formal to a caller by method reachability alone.

Register a caller subscription before replay. Replay earlier PW keys on a
new actual input, and notify existing inputs on a new PW delta. Apply the
same full AP predicate in both orders. New protection or value packets use
the existing admission rules; a duplicate key does not relay again.
Delivery is queued and counted, including same-unit delivery. The callback
cannot mutate a caller directory while that directory is being visited.

The prefix-guidance callback performs **no** global-pool supply, mark
request, read/write registration, call suffix, exit rule, source hit,
normal summary, selected publication or record. The existing independent
producer-effect channel performs the real group supply. A shared immutable
key may serve both owners, but membership and delivery roles stay explicit.

### 4.5 ZERO and returning wrappers

```java
main() { sink(wrap2()); }
wrap2() { return wrap1(); }
wrap1() { return get(); }
get() {
    C.f = sourceT();
    return C.f;
    // NormalExit removes the outgoing C.f value.
}
```

```text
get prefix:       ZERO_get -> C.f/T
get reader:       C.f/FLOW -> ret_get/FLOW

real ZERO call-control binding at wrap1:
                  ZERO_wrap1 -> C.f/T
wrap1 reader:     C.f/FLOW -> ret_wrap1/FLOW
composition:      ZERO_wrap1 -> ret_wrap1/T

real ZERO call-control binding at wrap2:
                  ZERO_wrap2 -> C.f/T
wrap2 reader:     C.f/FLOW -> ret_wrap2/FLOW
composition:      ZERO_wrap2 -> ret_wrap2/T
```

The outgoing W row at `get` is absent. The current producer-effect index
also cannot supply these caller guidance keys: it relays only concrete
**nonzero nonstatic** dependencies, while a genuine ZERO producer updates
the pool directly. Therefore the new prefix-guidance directory must
include ZERO PW keys and replay them through reached ZERO control ports.
Do not fabricate such a port or infer it from prescan reachability alone.

ZERO remains valid only when the executed source action has complete
ZERO-origin support. An ND cube can produce a ZERO original only if the
whole cube is satisfied by ZERO-origin inputs. A hypothetical nonzero
condition must keep its original through capture and actual binding.
`set(p) { C.f = p; }` is not a ZERO producer merely because it has been
called: its callee PW row must first match the actual caller input. A
caller ZERO may appear only as the genuine original of that matched input.

### 4.6 Freeze and compose

Finish body work, exit-rule resumes, mark requests, pool effects, ordinary
publications, and prefix-guidance notifications before freeze. A method's
queue-empty barrier can batch deliveries; it is not the complete-run
snapshot barrier. A pending guide delivery is still counted work.

```text
visible static graph at M:
  PB and B owned by M or its resolved transitive callees

local writer attachments at M:
  PW already bound to M's actual method originals, plus post-exit W

reader attachments at M:
  existing productive R at M

complete through static middles only:
  B;B, PW;B, W;B, B;R, PW;R, W;R, and arbitrary static chains
```

The existing CALLER rule stays limited to B. ZERO and nonstatic PW rows
reach callers by the actual-binding route above, not by CALLER. No ordinary
endpoint is composed as an internal graph vertex. In particular, ZERO is
an allowed true source, not a shortcut between independent effects.

Do not bind every materialized closure product to callers. Relay primitive
PW and their actual-bound descendants before freeze. Copy PB/B through
the detached graph, then use the factored static closure. At the relation
level, `bind(PW ; B)` can factor into `bind(PW) ; inherit(B)` because the
static middle keeps its coordinates. This factorization needs its AP
adapter proof before the production optimization is accepted.

After quiescence, freeze shared keys and method memberships. Release the
live prefix directory and subscription references as usual. Add the
frozen relation view only to incoming run-2 demand. Normalize and reverse
its endpoints under the selected AP boundary rules. Do not persist it as
a normal record or copy this completion automatically to later runs.

Finite bounded endpoint/mark schemas, exact admission and finite owners
bound the conceptual relation universe. Cycles add no new key after their
fixed point. No arbitrary loop cap, new memory quota, or completed-answer
history is needed. Factored storage avoids retaining all virtual composed
pairs, but this candidate makes no measured speedup claim.

### 4.7 Proof scope and remaining acceptance gates

The candidate's conceptual completeness argument uses a finite default
path with the same run-1 grammar, layers, source/sink rules, singleton
origins, field bound and static approximation. Capture each required
writer before exit effects. Keep each existing reader. Lift B through the
same finite call route. Lift ZERO/nonstatic writers through their actual
call bindings. Compose at the same static middle. Subject to the capture
and binding obligations below, this constructs the paired guide for that
finite path. C2/C5 then govern real run-2 execution.

For an ordinary call, the concrete relation has the shape
`inputBinding ; writer ; reader ; outputBinding`. Its static middle is
shared, so it factors into
`(inputBinding ; writer) ; (reader ; outputBinding)`. The input/output
bindings remain present. This is not an unbound copy of a formal.

The candidate local model is
[`PreExitGuidanceCandidate.lean`](../../spec/lean/proposals/restricted-demand/PreExitGuidanceCandidate.lean).
Its `transport` function assumes explicit seed coverage,
`forall e in old, e in captured`; it does not prove that the JVM collector
establishes that premise. Its nine constructive audits cover finite
primitive-inventory transport,
source provenance, the current missing-arg-return case, a FLOW-diagonal
instance for arbitrary marks, two actual-bound wrappers, ZERO through two
wrappers, and explicit call-factorization witnesses. Only the standard
`propext` axiom appears. It does not prove the JVM interpreter or scheduler.

[The complete audit receipt](../../spec/lean/proposals/restricted-demand/pre-exit-guidance-candidate-checks.json)
records the command result, source hash and all axiom audits.

**The following are acceptance obligations before runtime changes or the
project campaign. They are not proved by that local model.**

1. Prove prefix/origin factorization for the actual engine. The default
   algorithm can carry `p -> local` where the new run-1 code carries a
   prefix `p -> S` and a current fact `S -> local`. A later caller binding
   must preserve this decomposition. Do not assume identical originals
   or silently assume that the needed p-origin subscription already exists.
2. Prove that every required default writer/read primitive is captured or
   covered under the selected real-write activation and mark-group rules.
   Include completed ND guards, ZERO-supported GEN, guarded nonzero GEN,
   alias writes, source actions, late callbacks and exit-rule writes.
3. Prove the AP call-factorization adapter, including full initial
   containment, actual mark tests, static coordinate identity, raw mx,
   field bounds, tail correlation, and caller originals. The model's list
   of bindings is supplied as input; it does not establish their existence.
4. Prove that delaying static composition until freeze covers binding a
   composed writer. Reader transport through returning wrappers and the
   inherited PB/B graph must supply the other half at every exact MethodKey.
5. Prove packed/thin key extraction and replay equivalent to the scalar
   reference, with FULL/GROUP colors, T-to-U-to-T, class markers and source
   ZERO. Guidance must not enumerate full group members or discard colors.
6. Prove counted quiescence, snapshot detachment, and separate channel
   ownership. A guide must not become a pool supply, source hit, CFG fact,
   outgoing summary, record or new local writer.
7. Keep and pass all five observed failing controls, the no-exit-kill
   controls, and add the ZERO-source/return-wrapper cases above. Test both
   delivery orders, late inputs, recursive calls, repeated keys, cancellation
   and the existing mark/tail restrictions. Resolve the other open STAR/E
   and static-STAR-input contracts separately; this candidate does not
   choose a workaround for them.

No complete soundness theorem is claimed until these interface obligations
are discharged. If actual input capture cannot establish the required
origin decomposition, stop and specify that gap. Do not add GroundingSupport,
a second caller-fact store, a SQ permission exception, or a new field rule
to hide it.
