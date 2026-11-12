# Analyzer work reduction

**Specification; production unchanged.** This document specifies handoff
compaction, C2 pruning, early loop-probe rejection, disabled diagnostic
removal and exact FULL caller-input storage.

[Implementation proposal](../docs/design/bidirectional-work-reduction-implementation-20261112.md)
gives the code boundaries, indices, tests and staged proof/activation gates.

## 1. Contract and notation

| Change | Before → after | Required result |
| --- | --- | --- |
| Handoff compaction | Exact normalized demand-row deduplication → cross-origin subsumption at handoff. | Preserve required refinement; NORMAL persistence is unchanged. |
| C2 pruning | Visit impossible descendants → skip their empty emissions. | Identical complete ordered initial families. |
| Loop probes | Complete every trial → reject on a real extra admission. | Identical selected prefix/drop/fallback. |
| Disabled diagnostics | Archive facts before a no-op callback → skip diagnostic work. | Identical semantic output; enabled observers unchanged. |
| FULL caller storage | Separate qualified inputs → shared geometry with exact mark relations. | Identical logical snapshots, fresh deltas and delivery. |

Residual MAY coverage (R3, §2.1) has the proof obligation in §2.4. It may
change intermediate runs and confirmation timing, but must preserve eventual
refined findings in both directions, with no iteration limit. The production run-11 cutoff
is unchanged and cannot justify that proof. The other changes preserve
semantic results at common completed runs under the same compaction setting;
work counters, allocation IDs and timing can differ.

Keep AP transfer, initial emission, paired summary restriction, field limits,
marks/groups, cleaners, aliases, protection, rule selection, source permissions,
Targets and reporting unchanged. Packing introduces no bulk rule execution.
Proof/storage metadata must not enter public equality or hashing.

```text
Γ = complete method/context, stored direction, block and physical ports
H = literal protection membership: plain or non-subsumable
P = complete original premise, unary or ND; C = conclusion packet
O = current outgoing guidance origins
G(X) = complete native next-demand projection; K ⊆ O = final retained origins
$ = EXACT; * = STAR; MAY = [any]; MUST = [any-taint]
E = field exclusions; mx = FLOW mark exclusions; T,U = full concrete marks
C2 = initial admission, including layers, companions and precision/owner support
C5 = paired entry admission/output restriction, including the relative field cut
```

Compare complete decoded keys. Keep plain and protected memberships separate
in both directions, including when identical geometry has both flags.

## 2. Proposed handoff compaction

The new rules remove redundant **outgoing guidance**, after current summary
storage has normalized it. They do not add a NORMAL-record compactor.
Compare equal Γ, H and full marks; retain legal static anchors. All
witnesses must be actual retained edges.

### 2.1 Compaction rules

**R1. Weaker premise, identical conclusion**

```text
X: a.f.MUST/T → C, DEMAND
Y: a.f.*/T   → C, DEMAND
Y subsumes X for outgoing guidance.
```

Require identical conclusion and empty E on compared projected premise
selectors. Existing projection gives the same entry and equivalent MAY/STAR
paired-output selectors. This comparison crosses distinct premise keys,
which current per-premise storage does not compare.

**R2. Equivalent concrete-point conclusions**

```text
X: P → a.p.$/T, DEMAND
Y: P → a.p.*/T, DEMAND
Y subsumes X for outgoing guidance.
```

Require identical complete P. At late FULL admission, legal same-head
concrete STAR/EXACT demand entries have identical C2/C5 images. EXACT E
must be empty; STAR E can be any legal E. This does not equate their raw
NORMAL transfer. Current summary storage can retain both outputs.

**R3. Less restrictive DEMAND conclusion: remaining storage cases**

```math
X: P → Cx, DEMAND; Y: P → Cy, DEMAND
Req(Cx) ⊆ Req(Cy)  ⇒  Y subsumes X as a refinement obligation

Req(a.p.$/T) = Req(a.p.*/T) = {a.p.$/T}
Req(a.p.MAY/T) = {a.p.s.$/T | s is a legal suffix}
```

Require identical complete P and empty E for this adapter. Each removed
leaf needs a retained covering leaf. Ancestor STAR is not an ancestor
wildcard: it cannot cover a deeper point. Both edges must already exist.

Same-premise MAY coverage is already implemented within `TaintGroup`.
The proposed difference is to cover residual edges which are split across
storage lanes and therefore survive current normalization. For example:

```text
X: p.*/T → ret.f.$/T, DEMAND       # scalar exact lane
Y: p.*/T → ret.MAY/T, DEMAND       # packed diagonal lane
Proposed: retain Y; omit X's guidance.
```

No unrelated C2-supplying edge is a condition of R3. Its remaining native
proof obligation is stated in §2.4, not an additional subsumption rule.

**R4. ND guidance covered by retained arms**

```text
X: {I1,...,In} → C
For every Ii and every conclusion leaf c:
    retain arm witnesses covering the projected obligation (g(c);g(Ii)).
Then omit X's outgoing guidance.
```

The same-conclusion case needs one retained unary arm per member:

```text
X: {p.$/T, q.$/U} → ret.$/V, DEMAND
Y:  p.$/T        → ret.$/V, DEMAND
Z:         q.$/U → ret.*/V, DEMAND
Y and Z cover X through R2; Y alone does not.
```

For broader arm conclusions Ck, require
`Req(C) ⊆ intersection_k Req(Ck)` and preserve each member's paired selector.
Any new MAY-coverage application inherits R3's proof obligation. Exact
service witnesses may be supplied by more than one retained origin.

This changes guidance selection, not executable AND semantics. Keep
complete caller originals, NORMAL contributors and reports. A NORMAL ND
origin can lose its redundant guidance; it does not become a persisted
unary record. The backward run remains unary; run-1 cannot retain ND.

### 2.2 Difference from current implementation

| Mechanism | Current implementation | Proposed difference |
| --- | --- | --- |
| Literal payload union, aligned NORMAL FLOW specialization and FLOW-backed T coverage | Implemented in `ConclusionGroup`/`FlowBackedSummaries`. `PersistentRecordStore` also uses that store across saved runs. | None. Reuse ordinary persistence; no new rule or pass for NORMAL records. |
| Same-premise MAY conclusion coverage | `TaintGroup` canonicalizes its own scalar lane; packed diagonal admission also canonicalizes its own rows. | R3 covers residual scalar/diagonal combinations at handoff. It does not reimplement the already normalized cases. |
| Equivalent demand services | C2/C5 already implement the matching behavior used by R1/R2. | Use it to remove redundant outgoing origins; the current demand builder deduplicates only identical normalized rows. |
| Projection and control routing | `HandOff`/`projectBlockHandOff` already project all members/leaves and reverse block ports. | Select a retained basis before feeding that unchanged projection to the demand builder. |

The current-store [inventory](lean/proposals/in-handoff-compaction-20261112/compaction-inventory-receipt.json)
checks both arrival orders. In particular, for distinct full U and T,
`b.*/U → a.MAY/T,D` already removes `b.*/U → a.f.$/T,D` in the scalar store.
An extra `c.*/U → a.f.$/T,D` is unnecessary. Its earlier use supplied a
stricter exact-C2 proof certificate; it is not a semantic requirement of
conclusion coverage and is removed from the proposal.

### 2.3 Handoff application and comparison

Apply after a COMPLETE run joins, before the next run. Support FULL local
handoffs whose next run is at least run-3, for methods and generated inner
blocks in either direction. Bypass run-1→run-2 and GROUP-mode handoffs.
Use only current demands/summaries/submitted initials, with no future-run,
JVM-type, CFG/rule, finding-count or iteration-limit eligibility test.

The projection is **existing machinery**, not a new transfer rule:

```text
G(P → C) = {(next owner/ports, entry=g(c), output=g(p))
             | c is a conclusion leaf; p is EVERY premise member}
```

Keep existing `g`, physical port reversal, outgoing-origin predicate,
ZERO/Target typing and normalization. NormalTarget supplies no refinement
demand. Preserve its IDs, all source permissions, contributors and reports.
Select origins from current summaries/Targets, not persisted NORMAL records.

For the new comparisons, use private keys without changing actual rows:

```text
entryKey: legal late FULL concrete STAR/T or EXACT/T → same-head EXACT
          (STAR has legal E; EXACT has empty E); otherwise literal entry
outputKey: empty-E DATA MAY → same-head STAR; otherwise literal output

C2Cover(q,z): same entry owner/port and equal entryKey
C5Cover(q,y): same owner/physical exit/outputKey, and
             (equal entryKey or existing point-to-MAY C5 image containment)
```

The point adapter supports This/Argument/Return/LocalVar/Exception and
legal ClassStatic anchors, not FLOW/GROUP, literals or cleaner temporaries.
The C5-only point-to-MAY adapter supports ordinary This/Argument/Return/
LocalVar at the same path or its first counted extension: zero or more
CLASS accessors then one FIELD/ELEMENT and nothing later. Retain native
shape/budget guards. These are comparison laws for existing services;
C2 emission and paired C5 restriction are unchanged.

For exact-service certificates, cover every q in complete nonempty G(X)
with retained C2 and C5 witnesses, which may differ. Preserve the complete
initial family, layers/companions/precision support and complete C5 original.
This certificate proves R1/R2 and exact R4 cases. It is not a requirement
that R3 reproduce the same intermediate C2 family.

```text
handoff(completeRun):
    require workers joined and status == COMPLETE
    use existing report/seed preparation and NORMAL persistence
    O = all current selected method/block/Target guidance origins
    if unsupported scope: use existing handoff
    rows = unchanged complete native G(O); K = O

    for X in stable order of complete decoded keys:
        trial = K minus {X}
        rebind/check EVERY removed origin against final providers in trial
        accept only rules whose native proof obligations are discharged
        if all certificates pass: K = trial

    demand = existingBuilder(union(rows[Y] for Y in K))
    count successful normalized insertions
    preserve other handoff state; use existing commit and stop/continue
```

Never mutate live summaries or use absent/self/circular witnesses. Rebind
transitive cover to final providers: A may cover C after B is removed.
Equivalent origins can each be redundant alone while a joint plan must
keep one. Stable full-key order makes selection independent of arrival
order; minimality is not required. Compare every ND member/output leaf
without premise products. Exact lookups use hashes plus full-key checks;
affected-certificate indexing can replace global plan rechecks.

### 2.4 Proof obligations

| Rule | Established | Remaining before activation |
| --- | --- | --- |
| R1/R2 | Existing C2/C5 service-key laws and retained-service proof. | Bind new handoff selection to complete native origins/final witnesses. |
| R3 residual MAY coverage | Request-language inclusion and transitivity. Existing scalar MAY coverage is already active. | Prove eventual native refinement for the newly covered cross-lane cases. |
| R4 | Complete-arm exact-service composition. | Broader MAY arm cases depend on R3's remaining proof. |

R3 may change intermediate initials and confirmation timing. The remaining
proof must preserve eventual valid refined findings in both directions,
with no iteration limit, including source/ND permissions, NORMAL replay,
cleaners, H, ports/statics and empty-demand stopping. For example:

```text
scalar X:   p.*/T → ret.f.g.$/T,D
diagonal Y: p.*/T → ret.MAY/T,D
submitted: ret.f.g.$/T,N
C2(X): ret.f.g.$/T,N
C2(Y): ret.f.*/T,D + FLOW companions
```

The first-field emitter makes request inclusion weaker than native progress.
Do not claim this proof is complete, require an unrelated exact witness as
part of R3, or change admission/field semantics to close it. Until discharged,
leave those new residual MAY removals disabled; R1/R2 and exact R4 remain
independent. This is a proof-status constraint on the rules above, not
another proposed compaction mechanism.

## 3. Prune impossible local C2 descendants

The emitter's rejection already exists. The new change is to avoid
enumerating candidates which can only take that rejecting branch.

`RestrictedInitialPolicy.emitAdmissions` emits nothing, including companions,
when the demand strictly extends a STAR/EXACT actual. Its descendant branch
requires actual MAY or MUST. Therefore:

```text
visitCandidates(actual, kind, visit):
    walk existing ancestor spine, visiting values in existing order
    if actual's node is absent: return
    if kind == INITIAL_C2 and actual.tail in {STAR, EXACT}:
        visit same-node values; return
    run existing same-node/subtree DFS
```

Use raw path-prefix order, including CLASS accessors. Preserve native child,
profile and terminal ordinal order. Apply to `offer` and run-2 `requireFamily`;
leave completion/carry, Reach/ZERO, OUTPUT_C5 and precision cursors unchanged.
Run-1 does not use restricted C2. The rule holds in both directions/layers;
other mark/E/budget guards can reject more, never enable this branch.

```text
actual x.*/FLOW,N; demands x.MAY, x.f.MAY, x.f.g.MAY:
    old visits all; new visits root; both emit only x.*/FLOW,N.
actual x.MAY/T,D or x.MUST/T,N; demand x.f.$/T:
    keep descent; emit x.f.$/T at its native layer if E admits f.
```

For an h-long path and d descendant nodes, remove those d node/profile visits
and rejected emitter calls; MAY/MUST work is unchanged. Add a stoppable
internal traversal for §4: callback CONTINUE/STOP, result COMPLETED/STOPPED.
Ordinary visitors always continue. Returning from today's Unit callback
cannot stop DFS. Preserve cancellation propagation and count finalization;
STOP is not cancellation. Use one native traversal, not an approximate walker.

## 4. Reject losing loop probes early

The complete observer, prefix search and query caches already exist.
Add only negative-witness streaming and reuse its completed C2 work.

Preserve all existing bypasses, scalarization and prefix order. Compute the
complete baseline before trying cuts. Observation equality includes exact
sets of adjacent initials, repeat initials, scope/family-labelled admissions
and enclosing results. Enclosing results retain saved composition, C5,
liveness, Targets, original, exit, layer and H. Observation remains a pure
query: no rules, subscriptions, requests, sources, statics or publication.

The negative witness is an actual emitted descriptor:

```text
(consumer scope/physical entry, ADJACENT or REPEAT,
 full emitted Pattern including mark/mx/E, emitted layer)
```

Decode baseline initials with `toPattern`; stream candidate descriptors from
every `emitAdmissions` result, including companions. Use the same routing
and liveness. The legal interner round trip `ap.initial(p).toPattern()==p`
justifies comparison before interning. Admission descriptors have no H;
packet H/original remain in query context and enclosing results.

```text
restrictLoopResult(raw, original, views):
    apply existing run-1, ZERO/Reach and non-growing-summary bypasses
    baseline = completeObserver(raw, original, views)
    if baseline.isEmpty: return DROP
    keys = complete labelled baseline admission descriptors
    for budget in existing proper-prefix order:
        candidate = existingLimit(raw,budget)
        completed = []; extra = false
        if run >= 3 and supported frozen local DATA views:
            for V in existing adjacent/repeat view order:
                if native liveness rejects candidate: record empty V; continue
                stream native C2 with §3 traversal and complete emission families:
                    if descriptor(V,emission) not in keys:
                        extra = true; STOP traversal and abort remaining probe views
                    retain emitted descriptors for V
                retain completed V
        if extra: discard trial scratch; continue with next budget
        observed = completeObserver(candidate, reusing completed C2 families)
        if observed == baseline: return candidate
    return raw
```

Exact observation sets only add memberships: an extra descriptor cannot
later disappear. It rejects **one budget**, not the fact or loop. No extra
does not imply acceptance: baseline `{a,b}` versus candidate `{a}` still
fails full equality. Different scope/family/layer or a late extra companion
also matters. Do not revive first-budget/range certificates.

Unsupported/generic unlabelled views and run-2 transitive/static queries
use the full observer. Reuse completed families in all LoopAdmissionBundle
projections without a second C2 traversal; existing complete cache answers
may be decoded. Never cache partial/aborted results or retain trial scratch
across owner turns. Materialize initials only if full comparison needs them.
This avoids remaining C2/saved-observer work on losing trials, not actual
saved replay outside the observer.

## 5. Remove disabled unresolved diagnostics

Currently the JVM observer is non-null when its tracker is null, so run-1
archives qualified TAINT inputs before a no-op callback. Make the capability
stable and default-enabled for existing generic observers:

```kotlin
fun interface UnresolvedCallObserver {
    val enabled: Boolean get() = true
    fun reached(call: CommonCallExpr, position: AccessPathBase, plan: CallPlan)
}
// JIRInterpreter:
override val enabled: Boolean get() = externalMethodTracker != null
// SharedObjects: keep the same enabled observer object.
val unresolvedObserver: UnresolvedCallObserver?
    get() = (interpreter as? UnresolvedCallObserver)?.takeIf { it.enabled }
```

Initialize the diagnostic archive to null. Under the existing run-1/ADDED
guard, first obtain the enabled observer and check the unresolved stage;
only the first eligible TAINT input creates the old AddedFactAccumulator.
Then keep existing CallerRef, delta deduplication and callback behavior.
Disabled tracking creates no archive, mark-tree delta or callback. The
unresolved call's AP transfer still runs normally; freeze releases any
enabled archive as before.

Do not remove the accumulator class/other owners, change enabled diagnostic
aggregation/counts, infer that a generic observer is disabled, or introduce
runtime toggling. Preserve Kotlin/Java SAM use and public equality.

## 6. Exact FULL caller-input storage

Diagonal masks already exist in other stores/neutral transport. The new
work is their use in the caller-input directory together with exact
changing-mark buckets; existing handles and scalar protocol are retained.

### 6.1 Representation and keys

Replace only the retained TAINT backend of CalleeSubscriptions inside its
existing per-callee SubscriptionManager directory. Preserve admission and
selected-call policy. Eligible inputs have a legal singleton nonzero FULL
original and legal FULL TAINT output memberships, in run-1/later FULL runs.
ND, ZERO/Reach, FLOW, GROUP and other unsupported shapes stay scalar.
Keep native protection-class/domain validation. LocalInputDirectory, summary
stores and other accumulator owners are unchanged.

```text
FamilyKey:
    exact callee and caller/context, call, stage, caller layer, scope/ports
    original P geometry: manager, base, full path, tail, E
    current GroupKey: kind, layer, base, E, mx, tail, protection class

family.currentGeometryTrie[Q.path].exact / .any = MarkRelation:
    diagonal: immutable MarkSet
    changingByTarget: Map<FullMark, MarkSet>  # target → exact input marks

contains(s,t) = (s==t and s in diagonal)
               or (s!=t and s in changingByTarget[t])
add(s,t): add s to diagonal if s==t; otherwise to changingByTarget[t]
sourcesFor(t) = changingByTarget[t] union ({t} if t in diagonal else {})
```

Use existing full runtime identities, not group IDs; different groups are
permitted when native relations permit them. Off-diagonal buckets exclude
self-pairs. Keep a thin logical handle/insertion ordinal per `(family,s)`
and derived handle-to-cell-ID postings, adding each cell once per source.
Share geometry without a second full qualified-input archive.

P and Q are private descriptors, never synthetic FLOW initials. Keep public
CallerRef/Subscription/Facts equality and hashing unchanged. Full checked
key equality must follow a hash match. Preserve tails, E/mx, primitive-mark
metadata, legal static anchors and independent H families.

```text
(P,T1)→(Q,T1), (P,T3)→(Q,T3), (P,T1)→(Q,T2), (P,T3)→(Q,T4)
 ↔ (P→Q)[diagonal={T1,T3}, byTarget={T2:{T1}, T4:{T3}}]

T1→T4 and T3→T2 remain absent. New T1→T4 extends byTarget[T4].
Repeated T1→T4 is a duplicate; a new source at T4 is another logical input.
```

### 6.2 Complete snapshots and fresh deltas

Factor each native packet into literal `(path, EXACT/any slot, outputMark)`
cells, attaching its original input mark. Do not widen, subsume or broadcast
marks across positions:

```text
P/T1 → {Q.f.$/T2, Q.g.$/T4}
 ↔ Q.f exact: T1→T2; Q.g exact: T1→T4       # no Q.f/T4 or Q.g/T2
```

```text
readNativeGroup(family,s):
    for Q in source s's complete cell-ID postings:
        restore exact/any leaf marks {t | Q.contains(s,t)}
    restore the complete native header/H and CallerRef(P/s, owner/stage/scope)
    return the same complete scalar snapshot

admit(subscription):
    keep existing validation/policy; use scalar backend when ineligible
    key = FamilyKey of ORIGINAL offered packet; s = original full mark
    old = readNativeGroup(key,s)               # transient; absent initially
    merged,fresh = existing native add/merge(old,offered)
    if no fresh: return NO_CHANGE
    add every (Q,slot,t) in fresh as relation (s,t) UNDER key
    maintain logical handle/order and cell/candidate postings
    queue the exact immutable native fresh packet with its complete original
    return Admission(fresh, current=readNativeGroup(key,s))
```

Required invariant: `readNativeGroup(packed,k)==scalarCurrentSnapshot(k)`
for every logical group k, after every offer. The reference uses native
mergeAddDelta; direct pair admission requires the same native delta law.
Its literal union is old cells plus fresh cells. An exact-only fresh packet
can simplify E/tail: keep the original admitted key for storage and the
actual fresh header for replay, as the old accumulator does.

A queued fresh delta never becomes the later standing union. Temporary
native snapshots and pending deltas are allowed; a second standing scalar
mirror is not. Both outputs of one input and inputs sharing one output are
retained independently. Arrival permutations preserve final membership;
each actual trace retains its existing delivery order.

### 6.3 Queries, execution and lifetime

Share geometry postings by family/cell. Keep native prefix/extension and
opposite-direction candidate policy. Exact FULL target buckets may narrow
mark candidates; unsupported selectors retain conservative selection and
all candidates still pass the existing full matcher.

Expand candidates to logical handles, deduplicate by handle and restore
old input/member order. Materialize complete immutable snapshots before
callbacks can grow the directory. Request batches also deduplicate logical
handles, not families. A selected mark/cell does not replace the complete
packet supplied to a join or source/request hook.

Decode before existing records/summaries, ND joins, rules, cleaners, aliases,
primitive filters, requests and joined static-writer binding. Keep current
NeutralRelationBatch execution guards; storage eligibility does not certify
new changing-mark bulk execution. In `P/T→Q/U` composed with `U→T`, the
scalar composer must see original T and make the same protection decision.

The table remains caller-runner owned. Publishers queue notifications.
Joined ownership moves/freezes the same directory. Clear relations, handles,
postings and fallback together at the existing release point; expose no
live mutable view to queued callbacks or summaries.

### 6.4 Consequences and cost

Native MarkSet is a sorted integer set. At common geometry, store d diagonal
IDs plus t changing target keys and c source memberships, with shared
geometry/header. Thin handles/postings still cost space. Existing AP nodes
may already be shared; logical compression is not a byte-saving estimate.

Source cell postings avoid unrelated geometry scans. Target-first buckets
can still cost a scan of changing targets when decoding one source; an
exact derived reverse index is allowed, never a second authority. Measure
its storage, transient native-merge allocations and decode CPU cost. This
is compact standing storage, not fewer scalar rule executions.

### 6.5 Why FLOW subsumption does not replace input storage

A FLOW summary describes transfer, not which concrete marks arrived:

```java
Object copyAndLabel(Object arg) {
    // Source rule: CM(arg,T2) assigns U to the returned value.
    return arg;
}
```

```text
stored inputs: P/T1→arg/T1; P/T2→arg/T2
NORMAL arg.*/FLOW→ret.*/FLOW can cover diagonal T→T summary results.
A later arg.*/T2→ret.$/U still needs the stored T2 input, not T1 or FLOW.
```

Packing preserves these witnesses in exact masks/pairs. It deletes no
input. Inputs already avoided by existing subsumption require no packing.

## 7. Proof and validation gates

[Proof package](lean/proposals/in-handoff-compaction-20261112/README.md):

| Model | Checked result | Native boundary |
| --- | --- | --- |
| HandoffCompaction, 17 claims | Exact-service composition, complete ND/retained witnesses, transitive request order. | Bind R1/R2/R4 selection to existing services; R3 cross-lane progress remains open. |
| WorkReduction, 23 claims | Empty-family pruning, descriptor round trip, negative witness, same selected budget, diagnostic noninterference. | Preserve real routing/liveness, exact set union and an inert disabled callback. |
| CallerMarkRelations, 26 claims | Exact encode/decode/union/freshness, pair buckets, packet factoring, source-cell postings and separation. | Reconstruct whole native snapshots/deltas, indexes, order and lifetime before scalar consumers. |

Models are constructive, with only `propext`/`Quot.sound` in successful
audits. They are local components, not a whole Kotlin analyzer proof.
Native controls pass 182 C2/interner assertions and 8,325 MarkSet prototype
assertions across 512 small relations. They do not test a future production
rewrite. Source audits/receipts and failed-attempt history remain in the
linked package; no runtime implementation or project scan was done here.

Before landing, bind decoded native keys to these models and run differential
controls:

| Area | Required cases |
| --- | --- |
| Compaction | All leaves/ND arms, ports/marks/H, ZERO/Target, both saved directions, E overlap, alias closure, final witness rebinding, both arrival orders and transitive chains. |
| C2 | Complete ordered families for all tails/marks/layers/directions/E; same/ancestor visits, run-2 requireFamily/completion, unchanged C5/cursors. |
| Loop | Full baseline, late-extra companions, scope/family/layer differences, missing-only/enclosing-only differences, unsupported fallback, bypasses and one C2 pass per completed view. |
| Diagnostics | No disabled archive/update/callback; enabled and generic observer parity, ignored methods, SAM use, unchanged semantic output. |
| Caller storage | Diagonal/changing/mixed cells, one-to-many/many-to-one, separate positions/slots/H/owners, primitive marks/statics, scalar fallback, native snapshot after every offer, exact-only deltas, late requests/publications, T→U→T, fresh/current timing, candidate order and joined release. |

Keep real finding assertions and known failures. Exact-service/technical
changes compare semantic results at common completed frontiers; enabling
compaction may intentionally change raw demand counts. New residual MAY activation
additionally requires uncapped natural-continuation/refined-finding proof
and tests; a missing intermediate initial alone is not a sink-loss example.

After each independently landed feature, use the same FULL rules/models,
limits, aliases and statics. Run heavy jobs sequentially. Measure removed
C2 visits, early witnesses/full observations avoided, reused families,
initial allocations and zero disabled archives. For storage, separate logical
groups, geometry cells, diagonal IDs, changing pairs/buckets, thin postings,
fallbacks, decoded snapshots, retained heap and allocation churn. Claim no
speed factor from sample shares or logical row counts. The loop probe does
not optimize actual saved replay outside the observer.

Report latest reached/completed/accepted-forward labels and final reason,
plus exact finding identities and confirmed/provisional status. Existing
baseline evidence (no new experiment):

| Project | Reached | Completed | Accepted forward |
| --- | --- | --- | --- |
| OWASP | run-11 | run-11 | run-11 |
| Conductor | run-8 | run-7 | run-7 |
| Stirling-PDF | run-11 | run-10 | run-9 |
| Thingsboard | run-1 | none (OOM) | none |
