# NORMAL uniform FLOW coverage of NE demand

14 November 2026. Proposed addition to
[bounded demand refinement](bidirectional-bounded-demand-refinement-20261114.md).
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
The [working goal](bidirectional-may-may-progress-task-20261113.md) retains
both old examples and the new ordinary-code counterexample.

## 1. Approach and semantic scope

Keep the bounded refinement proposal for unknown reads. Add one egress
coverage rule for the new global-cut cycle:

```text
same qualified complete original P, where P is a singleton MUST/FLOW:

N: P -> a.u.MUST/FLOW, NORMAL
X: P -> a.u.v.NE/FLOW, DEMAND

N covers X, including v=empty.
```

MUST proves every location in its admitted region. NE describes some
nonempty suffix in a region. Every possible point of X is already covered
by the legally retained NORMAL uniform result. No particular suffix from
the discarded cut is needed.

This is a **new summary subsumption rule**. The selected non-empty-MAY
spec currently forbids a blanket MUST-to-NE deletion. The initial activation
is deliberately narrower:

- forward, one fixed method/block interface, owner, context and physical ports;
- identical complete singleton original P, with MUST tail and FLOW mark;
- NORMAL FLOW/MUST provider, DEMAND FLOW/NE candidate;
- unprotected memberships, same nonstatic output base;
- empty real field and mark exclusions on both original/output interfaces.

Keep unsupported classes unchanged: concrete/mark-changing originals,
protected rows, ND, static protocols, nonempty exclusions, independent MAY,
STAR originals and backward views. No new NORMAL fact is inferred from NE.

The comparison runs **after each candidate's own C5**. The provider is
either an admitted NORMAL row or a legal transient image of a retained
NORMAL record, as specified below. Do not borrow another demand row's
entry permission or output budget.

| Mechanism | Current proposal | Proposed addition |
| --- | --- | --- |
| Summary coverage | NORMAL correlated STAR coverage; no MUST-to-NE rule | NORMAL uniform FLOW can cover NE under the same complete uniform FLOW original |
| Real field cuts | Over-limit path becomes NE/DEMAND | Unchanged; compute the cut before comparison |
| Admission and intersections | Selected C2, own-row paired C5 | Unchanged |
| Local rules and observations | Evaluate during body processing | Unchanged; coverage only filters egress publication/guidance afterward |
| Native MUST matching | Definite uniform lane and existing provisional lane | Unchanged; virtual NORMAL witnesses require definite whole-premise support |
| Source permission and Targets | Existing paired controls and normal-only confirmation | Unchanged; remove no Target directly |
| Caller MUST/MUST canonicalization | Existing same-premise/mark/layer/H law | Reuse it; do not retain a covered NORMAL uniform child as a separate offer |

There is no full suffix evidence, new tail, artificial exclusion, raw edge
archive, initial-key metadata or field-limit increase.

## 2. Why it solves the ordinary counterexample

Use the [double-read/double-write program](../reports/bidirectional-bounded-refinement-ordinary-cycle-20261114.md).
At forward limit L, its conditional query starts at `x.f^(L-1).MUST/FLOW`.
Both branches have the same original P:

```text
read branch:
    P -> ret.f^(L-3).MUST, NORMAL       // or uniform root when L=2
    own C5 may select ret.f^(L-1).MUST, still NORMAL

write branch:
    P -> ret.f^(L+1).MUST, NORMAL
    global cut -> ret.f^L.NE, DEMAND
```

The normal read result covers the entire cut region. The old STAR
precoverage rule could not remove that NE. The new uniform coverage rule
can. The current query still performs both writes and the real cut; its
covered demand is omitted from publication and the next refinement view.

Without that first-call NE answer, there is no second-call NE offer which
creates the at-limit STAR query and the next deeper demand. Normal actual
results remain. Existing same-layer MUST canonicalization keeps the broad
NORMAL root instead of its covered NORMAL descendants.

The old read-`f.g`/write-`f` case still uses local child routing and the
existing NORMAL writer precoverage. Uniform coverage does not replace
those mechanisms: an unknown-suffix STAR read is not a uniform provider.

## 3. Retained records can supply a virtual provider

The old precoverage optimization may already omit a redundant MUST row
because a retained NORMAL STAR relation supplies its exact native image.
Do not require that duplicate MUST row to be physically stored.

For a candidate with raw original P, read the retained NORMAL provider
through the existing native applicator using P's **whole uniform hypothesis**:

1. Require a definite normal result; a provisional/weak result is insufficient.
2. Require the image to fit the current global limit.
3. Apply the candidate's own raw-entry authority and paired C5 to that image.
4. Use it only if it remains a NORMAL FLOW/MUST row with exactly original P.
5. Keep the retained native record as the provider. Do not publish or store
   this transient duplicate.

Example:

```text
retained R: x.f.f.* -> ret.*, NORMAL
query P:   x.f.f.f.MUST/FLOW

native definite image: P -> ret.f.MUST, NORMAL
own C5 output selector ret.f.f.f.*:
                       P -> ret.f.f.f.MUST, NORMAL
covered candidate:    P -> ret.f.f.f.f.NE, DEMAND
```

The retained writer alone cannot create this proof: its image grows past
the limit and fails the normal-view test. A cut result never becomes a
NORMAL virtual view. A STAR original also cannot borrow MUST output.

## 4. Pipeline

Use existing publication batches and NORMAL-first processing. Filter
pending demand and handoff against the final provider basis. A late
provider can retire a pending covered membership; previously executed
callbacks are not claimed to be reversible. The reference fixed points
below use owner-local batches after ready NORMAL work has completed.

```text
onBoundaryCandidate(rawP, rawC, ownRow):
    Xs = existingPairedC5(rawP, rawC, ownRow)       // normal limits/cuts
    for X in Xs:
        if not eligibleForwardUniformNE(X):
            submitThroughExistingPipeline(X)
            continue

        covered = false
        for N in currentOrSavedNormalUniformRowsWithSameOriginal(X.P):
            if sameQualifiedFrame(N, X) and uniformRegionCovers(N, X):
                covered = true
                break

        if not covered:
            for S in retainedNormalRecordsRelevantTo(rawP):
                N = nativeDefiniteImage(S, rawP)   // no weak/provisional lane
                if N.empty or N.layer != NORMAL: continue
                if fieldLength(N.C) > globalLimit: continue
                N = existingPairedC5(rawP, N.C, ownRow)
                if N.isNormalUniformFlowWithOriginal(X.P)
                   and uniformRegionCovers(N, X):
                    covered = true
                    break

        if not covered:
            executionSummaries.add(X)
            refinementView.add(X)
            pendingPublication.add(X)

beforePublicationAndHandoff():
    recheckCoveredNEAgainstFinalRetainedProviders()
    useExistingExecutionAndRefinementCompaction()
```

`uniformRegionCovers` checks equal complete originals and qualified headers,
then that the provider output path is a prefix of the NE output path.
The initial empty-exclusion activation needs no other spatial search.
Use existing original/output indexes; the transient-provider path reads
matching NORMAL records and computes bounded images, not path products.

Only eligible NE summaries pay this extra lookup. The comparison uses
bounded paths; no unbounded evidence is composed through a call.
Actual calls still apply persisted summaries to the **original actual**,
then use demand for current admission. A DEMAND actual retains DEMAND
support even when its provider is NORMAL. It cannot create NormalTarget.

## 5. Closed reference results

The [annotated reference traces](../reports/bidirectional-uniform-ne-coverage-reference-20261114.md)
list demand, submitted facts, initials and published summaries for the
method-only, inner-block and new ordinary-code examples.

The proofs execute all return candidates from the relevant run-3 C2
families, both body branches, global cuts and each original row's C5.
They then deliver the first call's real normal result to the second call
and check that another closure round changes nothing.

| Case | Current bounded proposal | With this addition |
| --- | --- | --- |
| Old method-only read `p.f.g`, write one f | Earlier conservative reference finishes run-5 | Closed canonical reference finishes run-3, NORMAL finding retained |
| Old read/write BB version | Earlier reference includes extra weak-MUST guidance | Read block, write block and parent finish run-3; finding retained |
| Longer read after `p.f` | Reader is not assumed NORMAL beforehand | Its result is derived from the real `p.f.MUST` input for any remaining read chain |
| New read `x.f.f`, write two f fields | Checked uncapped recurrence; exploratory execution reaches run-31 | Complete run-3 packet has no demand; both calls and root finish normally |
| New case with NORMAL read/write records already retained | Old precoverage still leaves globally cut NE | Legal virtual uniform views remove the redundant NE; original replay suffices |
| Exact-root selected cleaner | Nonempty concrete repair required | Repair is unchanged; precise descendant still survives |
| Wrapper/child-demand case | Child EXACT query and full NORMAL h reader required | Both remain; no artificial E or loss of its f descendant |

The earlier run-5 model retained NORMAL MUST descendants in its intermediate
actual lists. This reference applies the already selected same-layer
MUST/MUST canonicalization before submitting the next call. That explains
the earlier run-3 stop; no new actual MUST-to-NE deletion is used. Native
tests already check same-layer MUST canonicalization in both arrival orders
and before C5.

The new rule retires the original root `ZERO -> DemandTarget` **indirectly**:
the redundant NE is not delivered, so no new DEMAND sink witness is created.
NormalTarget does not erase DemandTarget and no hard limit is used.

## 6. Proof obligations and practical scope

The [Lean package](../../spec/lean/proposals/normal-uniform-ne-coverage-20261114/README.md)
checks executable prefix coverage and a constructive point witness for
every covered NE point. Under the identical complete uniform premise,
the NORMAL provider already supplies all those marked output points.
Ordinary positive source-to-sink observations in these programs are
therefore preserved. The provider is retained; a removed demand never
serves as its own proof.

The closed traces additionally check C2/C5, the root/field MUST actuals,
normal-only confirmation, source/cleaner repair, inner BBs, native weak
reverse behavior and warm-record projection. This is more than showing
that the previous cycle witness disappears: every relevant run-3 DATA
packet, both actual deliveries and the complete reference frontier are
computed to a fixed point.

This is a proof for the declared positive field-transfer scope, not a full
Kotlin/JVM/native-service correspondence theorem or a global termination
theorem. Before native activation, bind the predicate to the complete
same-premise native service, including legal marks, scope/ports and alias
closure. Unsupported cases keep the current implementation. No new
cleaner, mark-changing, ND, static, exclusion or provisional-MUST behavior
is authorized by these component proofs.

The special-pass intrinsic-MAY example remains outside the required goal.
It has no qualifying NORMAL uniform provider, so this rule does not claim
to terminate that model. Neither stable counts nor a run-11 cutoff are
proofs of redundancy.

Production is unchanged. Eleven existing native tests passed for the
reused MUST canonicalization and Conductor uniform-input mechanisms.
The NE rule itself is modeled in Lean; NE is not implemented in the current
core, so these tests do not validate its native integration.

The constructive checker passes **51 new declarations**, **292 including
dependencies**, across **17 modules**. The fresh source-hashed receipt is
`normal-uniform-ne-coverage-20261114/proofs-v4/receipt.json` under the
external report-data archive. The package README gives the reproduction
command. All audited declarations use only the permitted `propext` and
`Quot.sound` axioms; no classical or custom axiom is used.

No project scan was run. Historical reached/completed/accepted-forward
positions remain OWASP **run-11/11/11**, Conductor **run-8/7/7** and
Stirling-PDF **run-11/10/9**. The new closed references finish at **run-3**.

## 7. Subsequent ordinary-rule counterexample

The [uniform-source exact-root cleaner case](../reports/bidirectional-uniform-root-cleaner-nontermination-20261114.md)
still fails to terminate under this addition and bounded refinement. It
has no loops, recursion or pass rules. A selected partial cleaner demotes
a concrete whole-object MUST before a whole-object sink; backward MAY
renews its source permission. The root's `ZERO -> DemandTarget` repeats
forever, with no field truncation or DATA initial. Native observation
reaches **run-21**; a constructive induction has no iteration cap.

This is outside the new law's neutral FLOW/MUST-to-NE shape. It does not
invalidate the earlier provided-example closures, but it prevents a claim
that those closures establish termination of all ordinary source/cleaner/
sink programs. No cleaner or Target change is included in this proposal.

Subsequent user decision: preserve MUST and its layer for same-head
selected EXACT-root cleaning. The case now stops at **run-1** in the
updated model and is withdrawn as a counterexample to the revised
contract. This is a separate cleaner semantic change, specified in
[non-empty-may.md](../../spec/non-empty-may.md), including the resulting
NORMAL exact-root false-positive risk under the original concrete cleaner.
The old **run-21** reproduction describes unchanged production.

The next [protected concrete growth counterexample](../reports/bidirectional-protected-cleaner-growth-nontermination-20261114.md)
does retain that MUST decision. The same cleaner precedes the ordinary
double-read/double-write helper. Its recurring nonempty facts keep their
layers, but concrete protected field cuts cannot use this FLOW-only law.
The root DemandTarget repeats indefinitely even with a NORMAL finding.
The formal replay reaches **run-31**; a generic induction proves the
uncapped recurrence. Native **run-3** component checks validate the shared
cleaner/body/C5 shapes. This is a known limit, not a change to this law.
