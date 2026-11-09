# Next iteration: remove repeated canonical, static-guidance and loop-query work

8 November 2026. **Proposal only. No further core change is implemented.**
Use measured runtime 334234c24e9008f4a2614b8213b8b2e73b6ba9e1.
Follow the proof-first process in [the proof guide](../../spec/proof-guide.md)
and [the implementation guide](../../spec/impl-proposal-guide.md).

The [current report](../reports/bidirectional-subsumption-initial-demand-performance-20261108.md)
is the evidence authority. Latest reached / committed / accepted:
OWASP run-5 / run-5 / run-5; Conductor run-14 / run-13 / run-13;
Thingsboard run-2 / run-1 / run-1; Stirling run-52 / run-51 / run-51.

## 1. Selection and semantic boundary

Rank by expected workload impact, supported by the latest measurements:

| Rank | Change | Evidence and expected effect |
| --- | --- | --- |
| 1 | Maintain only changed canonical regions | Stirling backward run-30 spends 89.19% of Java CPU samples in FLOW canonicalization. Thingsboard and Conductor also rebuild marked projections. Avoid old-state work, temporary trees and related GC. |
| 2 | Factor joined static guidance by complete input premise and parent support | Thingsboard uses 292.71 seconds and 780.24 GB of allocation weight in binding. It visits 462.37 million inputs and makes 33.10 million bound callbacks. Avoid repeated matching and equivalent thin-guidance outputs. |
| 3 | Prepare the complete loop query across prefix trials | Conductor run-12 spends 67.91% of Java CPU samples in complete loop observation. Run-10 makes 21.39 million extra prefix trials. Avoid repeating whole C2/replay/C5 queries. |

These are proposed work changes with **the same selected analysis semantics**.
They must produce the same canonical support and observations as the current
reference path. They do not authorize a new transfer, widening, subsumption
law, source permission, alias policy, Target rule or stopping rule.

Keep independent plain/protected memberships, all selected MAY/MUST laws,
both arrival orders, opposite-record-only STAR inside matching, the full
C2 command family, paired C5 and its caps, exact field exclusions, physical
ports, ND conditions, run-1 origin splitting, ordinary static supply,
killed-write guidance and the own-ZERO gate exception. Keep FULL default.
No new tail, grounding support, WeakIdentityCache or unrestricted fact
history is part of this proposal.

Each optimized cell needs a constructive equivalence proof first. Keep the
current reference path for unsupported cells. A failed proof does not permit
a hidden semantic change. Present any new required behavior for a separate
decision.

The measured project no-FN gate still fails. The receiver-reset failure and
three other strict omissions must remain visible. These optimizations must
not waive them or silently change the associated rules.

Terms used below: C2 admits initial facts from a submitted fact and demand.
C5 restricts a summary with its paired demand. An owner includes method or
block scope, direction and physical ports. P is the complete original premise.
H is the existing FLOW-subsumption protection flag; retain its plain and
protected memberships separately. STAR shares a suffix across edge endpoints;
ANY is an independent unknown suffix; MUST is uniform taint outside exclusions.
A W attachment connects an entry origin to a static output. A B bridge connects
static regions in frozen guidance. Neither is a pool supply.

## 2. Incremental canonical admission

### Current versus proposed

Current FLOW admission inserts an offer, then canonicalizes all retained
headers against other retained headers, performs MUST merge/fill passes,
scans again and computes deltas against the old basis. It also does this
when insertion found no fresh support.

Current diagonal admission decodes the existing selected mark/class
projection into a temporary TaintGroup. It then tests the offer. A successful
offer clears that mark/class from all scoped rows and encodes its full new
projection. The baseline used full reconstruction only for conflicting
headers; the new selected canonical laws require more cases, but do not
require rebuilding unrelated retained state.

Proposed: retain a canonical owner invariant. First reject a provably absorbed
offer without mutation. Otherwise update the changed geometry/header frontier.
Revisit old rows only if the new support, exclusion merge or MUST-hole fill
can affect them. Keep the generic current normalizer as a reference/fallback.

    admit(owner, offer):
        require owner.isCanonical

        if exactOrProvedAbsorption(owner, offer):
            return EMPTY                     // no mutation and no full old-state scan

        changes = insertWithLocalDelta(owner, offer)
        work = affectedFrontier(changes)       // header, path, mark and H class

        while work.hasNext():
            changed = work.take()
            for neighbor in owner.relatedRows(changed):
                result = applyExistingCanonicalRules(changed, neighbor)
                work.add(result.changedRows)
                owner.update(result)          // update derived indexes too

        return exactFreshSupportSinceBefore() // include broader E/mx annotations

This is proposed pseudocode, not an existing API. A generic insert returning
null is not enough to justify skipping work if that insert already mutated
headers. The early absorption test must be read-only, or prove that no
retained change occurred.

### Principal fact example

Consider a backward block which reads several fields written by a loop:

    Node copy(Node x) {
        while (again()) {
            x.a = readA();
            x.b = readB();
            x.c = readC();
        }
        return x;
    }

One legal owner cell after ordinary transfer/cutting is:

    P = arg(0).* / FLOW
    stored conclusion = {x.a.[any], x.b.[any], x.c.[any]} / FLOW, DEMAND
    offered conclusion = x.a.[any] / FLOW, DEMAND

Current handling can reject the offer in insert, then still visit the retained
MAY forest and headers during canonical passes. Proposed handling proves
that the canonical owner already contains the offered membership and emits
nothing. It visits only the needed lookup frontier. This is an owner-level
example; it does not claim a complete measured trace for this short program.

For diagonal storage, keep two masks at one geometry:

    presentPlain = {T, U}
    presentProtected = {T}
    offer plain T at the same geometry -> no fresh plain membership
    offer protected U                -> add only protected U

Do not set a plain bit when a protected bit arrives. Do not infer that one
class covers the other. An unaffected mark or geometry must not be decoded
and restored merely to admit U.

### Proofs and checks

Model the current canonical rules and fresh support in Lean. Prove:

- Read-only absorption leaves the owner and delivered support unchanged.
- Every newly applicable rule has a changed endpoint or a changed immediate
  MUST parent/child witness; a frontier worklist reaches the same closure.
- MUST filling requires the complete immediate child. A deeper child or
  nonempty child exclusion cannot fill the hole.
- E/mx intersection, same-head overlap, parent/descendant pruning and typed
  cross-tail laws are unchanged.
- Both H memberships survive, and delivery remains fresh and arrival-order
  independent.
- Index removal, final publication filtering and frozen records use the
  actual retained basis.

Use the current generic path as a native differential oracle. Check complete
packets and child-first/parent-first sequences, multiple exclusions, both
layers, both H classes and late FLOW backing. Do not restore the old OR-upgrade
or retain discarded leaves as hidden history.

Let R be retained projection nodes/memberships, H the header count and d the
changed frontier. Current duplicate offers can pay whole-R work and old/old
header comparisons. The target is a bounded lookup for duplicates and work
proportional to d plus affected neighbors for updates. The exact dynamic
R/H/duplicate distributions are not yet measured. The 89% hotspot makes this
a high-impact target; it is not a promised wall-time speedup.

## 3. Factor joined static guidance

### Current versus proposed

Current binding is repeated per owned writer row. Candidate selection and
matching depend on owner and complete premise, but are repeated for different
output columns. Detached local inputs are scanned. Root input selection is
indexed. Successful pairs invoke guidance insertion and may enqueue another
parent-owned writer.

This is not static-pool supply. It preserves caller origins for backward
guidance, including a write removed by exit cleaning. Pool reachability cannot
replace it.

Proposed: schedule compatible writer columns by complete owner/premise.
Select and match actual inputs once for that group. Use a short-lived,
per-owner base/path selector for detached local inputs. Discard it after the
owner group; do not retain a second global input archive.

There is a second exact cell:

    mode = FULL
    formal I = nonstatic STAR / T, with legal empty run-1 E
    raw O    = named static ANY / U

After successful native matching, the thin exported guide has fixed O.path,
ANY, concrete U and DEMAND. The actual suffix is erased. Executable H can
differ, but the exported guide Pattern has no H. One supporting input per
complete parent owner/original and raw output suffices for this guide cell.

    bindOwner(owner):
        selector = buildTemporarySelector(owner.detachedInputs)

        for group in writersGroupedByCompletePremise(owner):
            matches = nativeMatchesInExistingOrder(selector, group.I)
            for output in group.outputs:
                if supportedConcreteAnyGuideCell(group.I, output):
                    for firstSupport in distinctParentOriginals(matches):
                        ensureExistingBoundary(firstSupport.parentScope)
                        emitAndQueueExistingGuide(firstSupport, output)
                else:
                    for match in matches:
                        applyExistingBinding(match, output)

The implementation must stream or bound per-group scratch. It must not keep
all raw matches for the whole project. Matching includes the existing mark,
scope, source/ZERO and compatibility tests. Reuse is not based on the output
field alone.

### Principal example and boundary

A write reached through an abstract field read can have this legal run-1
binding cell:

    void set(Box p) {
        C.f = p.value;
    }

    formal writer: p.* / T -> C.f.[any] / T, DEMAND
    parent original: q.* / T
    matching actual choices include p.a.$ / T and p.b.$ / T

For that ANY output, both matches export the same q/T-to-C.f/ANY/T thin
guide. Current handling applies both, inserts the same guide twice and offers
the same derived-parent writer twice. Proposed handling uses the first native
support once. This example specifies the binding cell after abstraction; it
does not claim that every set body creates that cell for every input.

The STAR-output control is different:

    formal writer: p.* / T -> C.f.* / T
    actual p.a.$ / T -> q/T-to-C.f.a.$/T guide
    actual p.b.$ / T -> q/T-to-C.f.b.$/T guide

Keep both. Do not apply the existential shortcut to a suffix-carrying cell.

Also keep distinct parent origins q and r. A callee write can survive as a
pool supply while exit cleaning removes the caller's executable static
result. Both caller-owned origin guides can still be required by run-2.
This proposal preserves them.

### Impact and proofs

Thingsboard has 33,099,986 bound callbacks, while the whole final catalog has
2,753,000 W attachments and 331,581 own B memberships. At least 30,015,405
callbacks cannot add a new final W/B membership. That is not a measured
duplicate count or eligible-ANY rate. Other seed sources contribute to the
catalog, and boundary/queue effects must be checked.

Prove the narrow ANY output independence constructively from native binding.
Prove first-support equivalence for the monotone BIND-W fixed point, including
B bridges, recursive/block parent routes, killed writes, genuine ZERO-to-Target
guidance and later source permissions. Prove output-column matching reuse
before changing schedule. Check native order where first support matters.

Measure unique owner/premise groups, output fanout, root/local candidates,
parent-origin support choices, output tails and actual fresh guide/queue
insertions. Then compare input visits, applications and allocation weights.
A lazy symbolic whole binding graph is a possible later design; it is not
required for this first optimization and must not be added silently.

## 4. Prepare the whole loop query across prefix trials

### Current versus proposed

Current growing DATA results are scalarized. Each scalar is observed raw.
Each trial prefix is observed again until the full signature matches. One
observation includes adjacent C2, saved replay plus enclosing C5, repeat C2
and scoped admission labels.

Conductor run-10 has 9,296,702 scalar baselines and 21,390,423 extra trials:
30,687,125 complete observations. ParametersUtils.replace alone makes two
C2 calls per observation. Most candidates are valid MAY/MAY cases. Making
impossible STAR matches faster will not remove this workload.

Use the real hot code pattern:

    for (Entry<String, Object> e : input.entrySet()) {
        Object value = e.getValue();
        Object newValue;
        if (value instanceof Map)
            newValue = replace((Map) value, documentContext, taskId);
        else if (value instanceof List)
            newValue = replaceList((List) value, taskId, documentContext);
        else
            newValue = value;
        result.put(e.getKey(), newValue);
    }

Proposed: prepare the frozen consumer program once for the raw path and its
cuts. Select relevant demand rows and saved records once. Retain their complete
C2 command families and paired C5 budgets. Evaluate semantic change points
across budgets with shared work, rather than run a fresh whole query per cut.

    restrictLoopResult(original, F, context):
        if existingBypassApplies():
            return F

        plan = prepareCompleteConsumerProgram(context, original, F)
        baseline = plan.observeRaw(F)
        if baseline.isEmpty:
            return DROP

        for budget in plan.candidateBudgetsInAscendingOrder():
            // Omit a budget only with a whole-family impossibility witness.
            cut = existingFieldLimit(F, budget)
            if plan.sameFinalComponents(cut, baseline):
                return cut
        return F

The first implementation can compare finalized independent components lazily:
if the complete canonical adjacent result differs, do not compute enclosing
and repeat results for that trial. Compare the finalized enclosing result next,
then repeat. Include the existing scoped admission labels and paired-row
support, either in those finalized components or as an explicit final component.
Equal admitted-initial sets alone are not the complete signature. Do not reject
on a raw tuple before union/canonicalization; a later contribution can cover
that tuple.

A narrower shared-C2 key is also possible for scalar ANY inputs: after the
first missing compatible demand-trie child, a later suffix cannot change
ancestor first-new-field initials or companions. Keep the complete static
anchor and the first new counted field. Keep view, policy, mark, layer,
exclusions, H/protection coordinate and class compatibility. Do not merge
plain and protected queries. Index all demand tails, not ANY alone.
Initially exclude run-2 virtual static completion and unsupported cells.

Identical C2 images do not imply identical saved-replay/enclosing-C5 images.
The complete observer remains the authority. Do not restore the old scalar
certificate or discard a companion to make a new certificate pass.

### Proof and impact gates

Prove equality of the finalized component comparator and the current complete
signature. Prove every omitted budget is impossible and the selected budget
is the same first valid budget. Include off-raw branches exposed by a shorter
ANY cut, physical ports, all original premises and both H classes.

For any shared C2 quotient, prove equality of the entire command family,
including the concrete-STAR NORMAL FLOW twin and raw exact FLOW prefix.
Then prove native correspondence. Retain current fallback for unsupported
tails, exclusions, control paths or special completion.

Removing all extra run-10 trials would remove 69.7% of that observer stream,
a 3.3-fold kernel reduction before preparation cost. This is an upper target,
not a guaranteed whole-run speedup. Count actual queries and allocated result
sets; do not claim a duplicate rate from outgoing demand totals.

## 5. Validation and experiments

Use a constructive Lean model, refinement counterexamples and native
differential tests before each optimized path. Keep existing hard cases:
independent H classes, MAY/MUST exclusions, C2 companions, paired C5,
Conductor recovery, cleaner repair and own-ZERO loop routing.

After implementation, commit and freeze the runtime. Repeat exactly the four
saved FULL/16 GiB configurations through Gradle runProjectAnalyzer. Reuse f945.
Keep report identities, current strict omissions and extra diagnostic failures
visible. Report reached, engine-complete, committed and accepted run labels.

Measure work removed, not only time:

- Canonical owners: offers, read-only rejections, fresh changes, affected
  headers/nodes, old projection decodes and full fallback visits.
- Static binding: unique input-premise groups, candidate/matched supports,
  eligible ANY columns, distinct parent supports and fresh W/B/queue effects.
- Loop queries: scalar baselines, prefix trials, skipped budgets, C2 calls/rows,
  complete observations, component short-circuits and reference fallbacks.
- Allocation, GC and memory: weighted allocation by exact pipeline, after-GC
  heap, RSS, OOM hooks and retained owners only when a real dump exists.

Also record complete semantic state hashes/diffs for Stirling's repeated
same-direction demand, NORMAL basis, seeds and relevant inputs. Record uncapped
maximum depths and one full applied-summary/C2/C5/freshness tuple for each hot
route. Include current versus opposite-record role. Saturated depth bins and
equal demand counts are insufficient.

Stirling's repeated bounded decoder work suggests future method-result reuse,
but exact dependency/state equality is unproved. Do not change stopping or
reuse a whole method from counts alone. OWASP first-use alias/form construction
is another separate question, not the dominant cause in these later windows.

The strict finding investigations also remain required: trace Thingsboard's
dynamic reflection input at instruction 1; preserve the current strict
receiver-reset failure; distinguish XSS coordinate fallback from witness
preservation. Select any source/reset/reporting semantics fix separately.
