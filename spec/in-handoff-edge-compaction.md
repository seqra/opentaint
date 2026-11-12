# Analyzer work reduction

**Specification; production unchanged.** This document specifies handoff
compaction, C2 pruning, early loop-probe rejection, disabled diagnostic
removal and exact FULL caller-input storage.

## 1. Contract and notation

| Change | Before → after | Required result |
| --- | --- | --- |
| Handoff compaction | Retain/project every eligible edge → retain a checked basis. | Preserve native NORMAL applications and complete demand services. |
| C2 pruning | Visit impossible descendants → skip their empty emissions. | Identical complete ordered initial families. |
| Loop probes | Complete every trial → reject on a real extra admission. | Identical selected prefix/drop/fallback. |
| Disabled diagnostics | Archive facts before a no-op callback → skip diagnostic work. | Identical semantic output; enabled observers unchanged. |
| FULL caller storage | Separate qualified inputs → shared geometry with exact mark relations. | Identical logical snapshots, fresh deltas and delivery. |

General MAY coarsening (§2.4) is **proof-gated**. It may change intermediate
runs and confirmation timing, but must preserve eventual refined findings
in both directions, with no iteration limit. The production run-11 cutoff
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
N = old and new eligible NORMAL records; O = current outgoing guidance origins
G(X) = complete native next-demand projection; K ⊆ O = final retained origins
$ = EXACT; * = STAR; MAY = [any]; MUST = [any-taint]
E = field exclusions; mx = FLOW mark exclusions; T,U = full concrete marks
C2 = initial admission, including layers, companions and precision/owner support
C5 = paired entry admission/output restriction, including the relative field cut
```

Compare complete decoded keys. Keep plain and protected memberships separate
in both directions, including when identical geometry has both flags.

## 2. Handoff compaction

Run after workers join a COMPLETE run-j, before run-(j+1). If repetition was
observed at i and i+2, the removal point is after j=i+2. Repetition is not an
algebraic eligibility requirement. The new compactor supports FULL local
handoffs whose next run is at least run-3, for methods and generated inner
blocks in either direction. Bypass run-1→run-2 and GROUP-mode handoffs.

Use only demands, summaries and submitted initials available at this barrier.
No future-run observations, JVM types, CFG/rule properties, finding counts
or iteration limit may decide a removal.

### 2.1 Saved NORMAL relations

Compact actual eligible native records at equal Γ and H. Preserve existing
persistence grammar: no DEMAND or ND records; keep legal nonempty initial E
on NORMAL FLOW; retain the backward ZERO/MUST restrictions.

**Literal inclusion:** with identical complete P, Y covers X when every
literal conclusion leaf of X occurs in Y with identical path/tail/mark/E/mx/H.
Per-leaf application then reproduces X in either read direction.

**Correlated NORMAL FLOW specialization:**

```text
S: a.u.* / EiS   → b.v.* / EoS
L: a.u.r.* / EiL → b.v.r.* / EoL
ES = EiS ∪ EoS; EL = EiL ∪ EoL

require same Γ, H and endpoint bases; same r at BOTH endpoints
require mxS ⊆ mxL
if r is empty: require ES ⊆ EL
else:          require ES admits r's first counted field
```

S covers L: L's suffix τ has witness r++τ in S. Preserve named-static
anchors. Check each output against a real retained output, without forming
input/output products. Use the existing overlap matcher and opposite-only
STAR-inside policy.

```text
p.* → ret.* covers p.f.* → ret.f.*              # NORMAL FLOW
p.* → q.* does NOT cover p.f.* → q.*           # different suffix correlation
p.* → q.* {f} does NOT cover p.f.* → q.f.*      # output excludes f
```

Reuse the existing FLOW-backed concrete cells under their current geometry,
mark, layer and H guards. NORMAL FLOW can cover its plain T specialization
when T is admitted; a protected-only provider cannot cover a plain row or
vice versa. Transitive cover can use a factored view of the final provider;
no intermediate fabricated record is published. This adds no broader native
law than [AP subsumption §3](edge-subsumption-initial-emission-demand-intersection.md#3-relation-subsumption).

### 2.2 Outgoing projection and exact service cover

Freeze O **before** compacting N. O uses the existing outgoing predicate,
including forward NORMAL ND and DemandTarget origins. A NORMAL singleton
which contributes no outgoing row is not a guidance provider. Backward
summaries remain unary; run-1 cannot retain an ND original.

```text
G(P → C) = {(next owner/ports, entry=g(c), output=g(p))
             | c is a conclusion leaf; p is EVERY premise member}
```

Reverse block ports as today. `g` maps MUST to MAY and clears its E, clears
FLOW mx and FLOW/STAR E, and preserves other legal coordinates. DemandTarget
uses the existing Target entry and ZERO/DATA output. NormalTarget supplies
no refinement demand. ZERO, Target and DATA remain distinct; preserve
NormalTarget IDs and all report/source/contributor state.

For a projected row q, compute comparison keys without changing the row:

```text
entryKey(q):
    legal late FULL concrete STAR/T with legal E, or EXACT/T with empty E
        → same base/path/full T, EXACT, empty E
    otherwise → complete literal typed entry
outputKey(q):
    empty-E DATA MAY → same-head STAR, keeping all other coordinates
    otherwise → complete literal typed output

C2Cover(q,z): same entry owner/port and entryKey(q) == entryKey(z)
C5Cover(q,y): same complete owner, physical exit and outputKey,
             and (entryKey(q) == entryKey(y) or pointToMayImageContains(y,q))
```

The point-entry adapter supports This, Argument, Return, LocalVar, Exception
and legal ClassStatic anchors; it excludes FLOW/GROUP entries, literal-backed
and cleaner-temporary bases. It preserves actual-derived layer and the full
C2 family/support profile, not just the primary fact.

`pointToMayImageContains` is C5-only: q has a full-concrete point entry; y
has empty-E MAY at the same ordinary base/full mark and either the same path
or the prefix before its first counted extension. That extension is zero
or more CLASS accessors followed by one FIELD/ELEMENT and nothing later.
Supported bases are This, Argument, Return and LocalVar; retain native
shape/budget guards. The output selector and exit must still be identical.

```text
coveredOrigin(X,K):
    require G(X) is complete and nonempty
    for q in G(X):
        require retained row z in G(K) with C2Cover(q,z)
        require retained row y in G(K) with C5Cover(q,y)
```

z and y may differ, but must belong to actual final-retained origins. C2
preserves all initials/companions/support; C5 preserves paired restriction
and the complete original, even when one ND member admits it. See the
[service proof](retained-demand-service-basis.md).

### 2.3 Subsumption examples, including ND

All rows below have compatible complete headers/H. These remove guidance,
not saved NORMAL transfers:

| Removed X | Retained witnesses | Reason |
| --- | --- | --- |
| `a.f.MUST/T → C,D` | `a.f.*/T → C,D` | Same entry; empty-E projected MAY/STAR outputs have equal C5 selectors. |
| `P → a.p.$/T,D` | `P → a.p.*/T,D` | Same complete P; legal late concrete-point entries have equal C2/C5 images. |
| `b.*/U → a.f.$/T,D` | `c.*/U → a.f.$/T,D` and `b.*/U → a.MAY/T,D` | First row supplies exact C2; second supplies paired C5. |

For the first row require empty E on compared projected selectors. For the
second, EXACT E is empty and STAR E follows the point-key guard. Neither
rule equates raw NORMAL STAR/EXACT or MUST/STAR transfer.

```text
X: {p.$/T, q.$/U} → ret.$/V,D
Y:  p.$/T        → ret.$/V,D
Z:         q.$/U → ret.*/V,D

G(X) has (ret.$/V; p.$/T) AND (ret.$/V; q.$/U).
Y and Z cover both; Y alone does not.
```

Require witnesses for every ND member and every conclusion leaf. This does
not replace executable AND by OR, split a complete caller original, or make
ND records persistable. A NORMAL ND origin may lose only its redundant
outgoing contribution. Different marks, H or ports are not interchangeable.

### 2.4 General MAY coverage: activation blocked

For equal Γ, H, full mark, legal static anchor and identical complete P,
with empty E, the proposed DEMAND order is:

```math
Req(a.p.$/T) = Req(a.p.*/T) = {a.p.$/T}
Req(a.p.MAY/T) = {a.p.s.$/T | s is a legal suffix}

Y covers X as an obligation if Req(Cx) ⊆ Req(Cy).
```

Both origins must exist; each removed packet leaf needs a real covering
leaf. For an ND arm family use `Req(C) ⊆ intersection_k Req(Ck)` plus its
complete paired-selector checks. Any arm using general MAY coverage has
the same proof gate. Ancestor STAR does not cover a deeper point.

Request inclusion is proved; native progress is not:

```text
X: P → a.f.g.$/T,D       Y: P → a.MAY/T,D
submitted: a.f.g.$/T,N
C2(X): a.f.g.$/T,N
C2(Y): a.f.*/T,D + FLOW companions
C5(Y) does not accept the literal deep initial in this step.
```

Before activation, construct finite simulations in both directions for
valid refined findings, under any retained surrounding edges. Account for
first-field C2, paired C5 cuts, source/ND permissions, NORMAL replay,
cleaners, H, ports/statics, and empty-demand stopping. No hard iteration
limit or mere request-set inclusion closes this gap. Until proved, require
the independent exact C2 witness in §2.2; change no AP semantics to force it.

### 2.5 Barrier algorithm and complexity

```text
handoff(j, completeRun, saved):
    require workers joined and status == COMPLETE
    observations = prepare existing reports/seeds/Targets/contributors
    O = freeze all selected method/block origins
    rows = complete native G(O)
    N = saved union eligible new NORMAL records
    if unsupported compaction scope: return existing handoff

    Nfinal = compact N with §2.1, using actual final providers
    K = O
    for X in stable order of complete decoded keys:
        trial = K minus {X}
        rebind/check certificates for EVERY origin in O minus trial
        if all exact-service checks pass against trial: K = trial
    require all removed origins have witnesses in final K

    prepare persistence(Nfinal)
    demand = nativeBuilder(union(rows[Y] for Y in K))
    counts = successful normalized demand insertions
    preserve observations; commit with existing cancellation/report protocol
    apply ordinary stop/continue to actual compacted demand
```

Do not mutate live summaries, project only compacted NORMAL records, or
use absent/self/circular witnesses. Rebind transitive cover to final leaves:
A may cover C after B is removed. Equal-projection origins can each be
individually redundant while a joint cut must keep one. Stable full-key
ordering makes selection independent of arrival order; minimality is not
required. Keep saved applications and guidance cover as separate contracts.

Index by complete Γ/H/mark and premise/selector keys. Exact lookup is hash
lookup plus full-key comparison; checking an ND origin needs one C2/C5 pair
per projected row, without origin products or premise subsets. Reference
plan rechecks may be quadratic or worse; optimize affected-certificate
lookup without changing final-witness checks.

## 3. Prune impossible local C2 descendants

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
| HandoffCompaction, 17 claims | Exact-service composition, complete ND/retained witnesses, transitive request order. | Reuse native AP relation laws and C2/C5 service-key proofs; MAY eventual progress remains open. |
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
compaction may intentionally change raw demand counts. General MAY activation
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
