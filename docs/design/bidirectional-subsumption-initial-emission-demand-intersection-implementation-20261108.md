# Implementation proposal: subsumption, initial emission and demand intersection

8 November 2026. Status: ready for implementation review. No production code
change or new project measurement is part of this proposal.

Implement the finalized
[specification](../../spec/edge-subsumption-initial-emission-demand-intersection.md).
Follow the [implementation guide](../../spec/impl-proposal-guide.md) and
[proof guide](../../spec/proof-guide.md). Code below is Kotlin-like pseudocode.
Names marked `proposed` are implementation helpers, not existing APIs.

**No further unresolved FN-producing counterexample is currently known in
the reviewed FULL-mode cases under the finalized specification.** This is
the current evidence status. It is not a universal no-FN proof. Native
correspondence, full-project recovery, general DATA-premise loop progress
and natural convergence remain acceptance checks. GROUP keeps its known
issues and is outside this FULL-mode acceptance contract.

## 1. Baseline and scope

Use `52829d5890ec3b3145cc996a1d8162d85cb8ceda`. Its `core` tree equals the
reviewed `52f32dd437d438aec4a700a02c18d94c31d58093` tree:
`6a3e587954faf5a5f9bcaf34f47e919edf69b95b`. The
[baseline contract](../../spec/subsumption-redesign-baseline-20261107.md)
pins the original source and proposals.

Checkout ownership update, 9 November 2026: the user requires the complete
implementation in the primary repository checkout, on saloed/bidirectional.
Use that checkout for implementation and commits. Do not create another
implementation worktree unless the user requests it.

The initial measurement used an isolated checkout from the selected revision.
Its tested implementation is now integrated into the primary checkout.
The earlier dirty prototype is preserved in a verified external backup.
Do not copy that withdrawn STAR_OR_ANY prototype into the implementation.
Apply the finalized contract to the pinned baseline. A source change outside
this contract needs a separate proposal with a counterexample and the
intended behavior.

This document replaces the withdrawn
[special-tail implementation proposal](bidirectional-star-or-any-initials-implementation-20261107.md)
for this work. That document and its measurements remain historical evidence.
The finalized spec takes precedence over older task and proposal wording.

### 1.1 Major semantic changes

These are analysis changes. Do not describe the whole patch as a technical
optimization.

| Part | Pinned baseline | Selected implementation | Proof obligations |
| --- | --- | --- | --- |
| MAY/MUST facts | Covered descendants can survive in a packet or after a later broader offer | Canonicalize the current union; fill only a complete immediate MUST child | P01, P13 |
| Protection | Exact flag upgrades and several temporary unions can expose one OR-upgraded membership | Keep plain and protected memberships independently, including identical geometry | P02, P04, P27, P32 |
| NORMAL FLOW relations | Equal-initial FLOW backing; no general aligned relation antichain | Use admitted aligned prefix relations, both endpoint E and admitted-mark inclusion; include legal statics | P03, P04, P24 |
| Summary matching | Some incomparable E reject; STAR inside use is not limited to the selected record role | Match same-head STAR/MUST overlap; permit strict-ancestor STAR inside only for opposite saved records | P05, P24 |
| C2 primary | Restricted runs can emit ANY; same-head ANY demand rejects STAR actuals | Use the table in section 5; emit no ANY initial; reject an ordinary STAR above a deeper demand | P06-P08 |
| Conditional FLOW analyses | No complete primary-plus-companions stream | Add the concrete-STAR FLOW companion and the successful ANY-descendant exact FLOW prefix | P25, P30 |
| C5 | Normalized C2-image entry, paired output selection and FL+1 restriction already exist | Reuse them with the new complete image and authorized FLOW companion; preserve every matching pair | P08-P12, P28 |
| Selected cleaner | A selected PART STAR/T survivor stays STAR/T on DEMAND | Replace that survivor by ANY/T, DEMAND, Empty E; keep P and H | P31, P36 |
| Extra loop gate | An own-ZERO result can enter the growth gate | Bypass only this gate for an effective local ZERO premise | P14, P15, P33-P35 |

Keep ordinary field reads/writes and their exclusion rules, selected FLOW
cleaning, full kills, aliases, source permissions, rule compilation,
complete ND execution, run-1 origin splitting, static supply, typed Targets,
physical block ports, boundary liveness and the stopping rule. A pass carries
H; it never creates H. Keep `trackFactsReachAnalysisEnd` empty.

Run-1 keeps its existing abstraction and static layers. C2 changes apply to
restricted runs, from run-2. The cleaner change also applies to run-1. The
extra loop gate already has a run-1 bypass. FULL remains the default, with
limits `1,1,2,3,4,...` and alternating forward/backward direction.

Do not add a tail kind, grounding state, a companion FLOW analysis for a
rejected primary, endpoint demand completion, a discarded-fact archive,
unrestricted summary storage, a new alias policy or a new stop condition.

## 2. Values and owner boundaries

```kotlin
EXACT = Tail.EXACT       // $: one position
STAR  = Tail.STAR        // *: one suffix shared by both edge endpoints
MAY   = Tail.ANY         // [any]: an independent unknown suffix
MUST  = Tail.ANY_TAINT   // [any-taint]: uniform taint outside field E

// E excludes immediate fields. mx excludes concrete marks from FLOW.
// N = NORMAL; D = DEMAND. H = existing non-subsumable flag.
// P is the complete original premise, including every ND member.

Interface = (method, context, direction, blockScope, entryPort, exitPort)
Membership = (Interface, P, conclusionBase, path, tail, mark, E, mx, layer, H)
```

An actual can have MAY. A conclusion or demand selector can have MAY.
An owned initial and its premise cannot have MAY. Keep the existing four-tail
enum. ZERO and typed Targets are controls, not field paths.

A static class anchor counts as zero fields. Its named field counts as one.
Do not detach that field from its class when a path is factored or cut.
Concrete static fields stay named. Keep the existing EXACT class markers;
do not introduce broad root/class concrete taint.

| Owner | Authoritative state | Derived state |
| --- | --- | --- |
| Statement/block actor | Canonical post-statement edges, split by H | Work items and CFG delivery cache |
| Summary owner | C5-admitted canonical relations, split by H | Publication and relation-prefix indexes |
| Frozen run records | Final retained NORMAL records under the existing persistence selection | Direct, opposite and position indexes |
| Demand owner | Immutable complete paired rows | Entry trie and prepared C5 programs |
| Loop context | Existing completion store and consumer observations, split by H | Prepared routes and query scratch |

Keep the existing single writer for each owner. No index becomes a second
authority. Do not compare or merge different interfaces, complete premises
or support layers merely because their paths agree.

## 3. Keep both protection classes

### 3.1 Selected packet representation

Use class-homogeneous packets. Keep native geometry tries. A retained TAINT
packet has either no H mask or an H mask equal to its root. Mixed producer
results are split before generic union or admission.

```kotlin
// proposed: labels for the existing flag, not a new analysis property.
enum class ProtectionClass { PLAIN, PROTECTED }
typealias MembershipBatch = List<Facts>

fun splitFreshProducerResult(f: TaintTree): MembershipBatch {
    val selected = intersectExactCoordinates(f.nonSubsumable, f.root)
    val plain = subtractExactCoordinates(f.root, selected)
    return listOfNotNull(
        plain?.let { packet(f, root=it, nonSubsumable=null) },
        selected?.let { packet(f, root=it, nonSubsumable=it) })
}

fun classOf(f: TaintTree): ProtectionClass {
    require(f.nonSubsumable == null || f.nonSubsumable == f.root)
    return if (f.nonSubsumable == null) PLAIN else PROTECTED
}

fun offer(batch: MembershipBatch): MembershipBatch =
    batch.flatMap { packet ->
        if (packet is TaintTree)
            canonicalInsert(lanes[classOf(packet)], packet)
        else existingUnflaggedInsert(packet)
    }
```

The split applies to a fresh producer result whose mask assigns a class to
each output. It does not recover plain membership from an owner. An owner
can retain the same coordinate in both classes. Its plain lane must never
be computed as `all minus protected`.

For FLOW and REACH, keep the existing unflagged representation. A geometry
interner can ignore H. TAINT packet equality, group keys, retained-edge keys
and freshness must include the class. A class-aware batch can contain both
packets with the same root. This is also required in temporary results.

Keep `ConclusionGroup.add(Facts): Facts?` for a homogeneous packet if useful.
A wrapper must offer each batch member. An API which can produce two classes
must return a batch or use a visitor; it cannot promise one merged `Facts`.
`mergeAddDelta(a,b)` must require equal class keys. Remove its cross-class OR
upgrade. A transfer acts on one input class at a time and sends its outputs
through the existing protection producer and the fresh-result split.

### 3.2 Scalar, packed and temporary storage

| Baseline seam | Required implementation |
| --- | --- |
| `ap/Conclusions.kt`: `TaintTree.equals/hashCode`, `GroupKey` | Include homogeneous H class in membership equality and grouping |
| `ap/Groups.kt`: `TaintGroup`, `ConclusionGroup` | Independent class lanes; canonicalize and return fresh support in that class |
| `ap/TrieOps.kt`: `mergeAddDelta` | Merge equal-class packets only |
| `store/MethodEdges.kt`: scalar identity bits | Store `present(layer,H)` independently; protected insertion does not set plain presence |
| Same file: promotion, restore and `edgesAt` | Decode both class bits, including after scalar-to-full promotion |
| `store/DiagonalRelations.kt` | Use independent `plainMarks` and `protectedMarks`; overlap is legal |
| `store/DemandResultCoverage.kt` | Keep exact C5 result unions in separate classes |
| `store/PreparedOutputPrograms.kt` | Pack and return separate class streams |
| `engine/PersistedSummaryReplay.kt` | Deduplicate `(recordView,H)`; do not use a Boolean OR-upgrade map |
| `engine/LoopOutputRestriction.kt`, `LoopQueryScratch.kt` | Include H in DATA observations, results and query keys |
| `engine/RunMethodCallServices.kt` and conjunction stores | Retain both class choices within the existing complete binding scope |

Keep existing scalar fallback when a packed adapter cannot represent the
complete class result. Do not erase H to enter a packed fast path.

For an already compatible complete ND binding, plain transport is possible
when every part has a plain choice. Protected transport is possible when
every part has a choice and at least one selected part is protected. Keep
both results when both are possible. Then apply the existing action-specific
protection producer. Do not weaken the condition, merge incompatible binding
scopes or enumerate new origin products. Run-1 still publishes no ND edge.
Keep its existing per-origin completeness and layer test: a split incomplete
arm stays DEMAND; a complete NORMAL unary or all-ZERO witness stays NORMAL.
Later ND application still needs all arms.

```text
offer A/plain; offer A/protected -> retain and deliver both
offer A/protected; offer A/plain -> retain and deliver both
repeat A/plain                 -> no fresh plain output
protected parent; plain child  -> retain both
plain parent; plain child      -> child is covered
pass A/plain                   -> plain output only
pass both classes              -> both output classes
```

ZERO and Target have no H class. Keep their current deduplication and report
identities. Do not multiply NormalTarget IDs to represent DATA classes.

## 4. Canonical facts and admitted relations

### 4.1 Canonical MAY/MUST facts

For one compatible owner/P/base/mark/layer/class cell, insert the offered
packet into the current union. Apply these rules to a fixed point:

```text
MAY at u covers MAY at u+r.

MUST at u/E1 covers MUST at u/E2 if E1 subset E2.
MUST at u/E1 union MUST at u/E2 = MUST at u/(E1 intersect E2).

MUST at u/E covers MUST at u+f+r/E2 if f is not excluded by E.
The descendant E2 can differ.

MUST at u/(E+{f}) plus MUST at u+f/{} fills the f hole.
A deeper child, or a child with a remaining hole, cannot fill it.
```

Apply the rules per mark and class. Preserve existing supported cross-tail
laws; do not add a new MUST-to-STAR or MUST-to-EXACT law. A FLOW fill must
cover the parent's admitted marks under native mx compatibility. Do not
enumerate all concrete marks or invent a positive-only FLOW payload.

Prune covered old descendants as well as covered offers. A broader header
created by exclusion intersection is fresh support and must be delivered.
Use only the canonical actual packet for C2. Do not retain discarded leaves
as hidden admission history or preserve old guide coordinates outside this
contract. Test one packet, child-first and parent-first insertion.

### 4.2 Aligned NORMAL relation coverage

Add a relation-prefix index to the admitted summary owner. Partition by
interface, input/output bases and compatible relation kind. Compare:

```kotlin
fun alignedNormalFlowCovers(s: Relation, l: Relation): Boolean {
    if (!sameInterface(s,l) || !bothUnaryNormalFlowStar(s,l)) return false
    if (s.input.base != l.input.base || s.output.base != l.output.base) return false
    if (s.H != l.H || !legalStaticAnchors(s,l)) return false
    val r = stripPrefix(l.input.path, s.input.path) ?: return false
    if (l.output.path != s.output.path + r) return false
    if (!s.output.mx.isSubsetOf(l.output.mx)) return false
    val es = s.input.E union s.output.E
    val el = l.input.E union l.output.E
    return if (r.isEmpty()) es.isSubsetOf(el) else r.first() !in es
}
```

FLOW initials have empty mx. For packed output trees, test each candidate
output path against a retained path with this same shift. Do not form an
input/output Cartesian product. Nonempty E and legal named statics are
allowed. Preserve both endpoint exclusions.

`store/FlowBackedSummaries.kt` currently selects backing by equal initial.
Extend that selection to compatible prefix providers. For a plain diagonal
T-to-T row, compute the private correlated specialization of an admitted
FLOW provider at the candidate initial. Run the existing FLOW-backed test:
T is not excluded; support is sufficient; STAR outputs have the same
correlated coordinate; ANY outputs can use prefix coverage. EXACT, MUST and
mark-changing rows keep their separate rules. All backing requires equal H.

```text
A NORMAL: p.* -> q.* / FLOW
C DEMAND: p.f.* -> q.f.* / T, plain

private view of A at p.f: p.f.* -> q.f.* / FLOW
existing diagonal backing test removes C if T is admitted.
No intermediate B needs to exist, be published or be persisted.
```

Recheck affected old concrete groups when a FLOW provider arrives. Check
offered concrete rows against retained providers when they arrive later.
Cover A-then-C, C-then-A and one-packet insertion. A rejected raw candidate
cannot be a provider. FLOW-first processing remains enabled. Local concrete
facts still reach CM, source and cleaner handlers before summary compaction.

### 4.3 Match the retained provider correctly

```kotlin
enum class SummaryReadRole { CURRENT, SAVED_DIRECT, SAVED_OPPOSITE }

fun matchEndpoint(actual, endpoint, role): Match? {
    if (sameHead(actual, endpoint) && endpoint.tail == STAR &&
        actual.tail in setOf(STAR, MUST)) {
        val slice = actual.copy(E = actual.E union endpoint.E)
        return existingMatchOnAdmittedSlice(slice, endpoint)
    }
    if (actual.tail == STAR && actual.path.strictAncestorOf(endpoint.path) &&
        role != SAVED_OPPOSITE) return null
    return existingOtherMatch(actual, endpoint, role)
}
```

The slice is an immutable operand. Keep the actual tail, mark, mx, H and
support. Apply output E and the normal layer join after matching. Keep
ordinary field micro-edge matching separate from this summary-record role.
Keep MAY/MUST matching and the trusted reverse-MUST lane. That lane needs
the original MUST-conclusion capability; a MUST premise alone is insufficient.
Generic STAR/STAR inversion keeps its current read-side E clearing and
combined result E. Do not change that inverse constructor a second time.

For example, `p.* {f} -> q.*` can replace `p.g.* -> q.g.*` when f differs
from g. On actual `p.MUST/T {z},N`, use overlap `{f,z}`. Rejecting the short
relation merely because `{f}` and `{z}` are incomparable would lose the g
route after the long relation is removed.

### 4.4 Publication and persistence

Only normalized C5-admitted candidates enter `RunSummaryStore.addAdmitted`.
Update the canonical authority before its indexes. A detached publication
batch must be filtered against the final retained class basis before it is
queryable or delivered. A removed long relation cannot remain a provider
through an old publication index entry. Already completed work is not
retracted.

At the joined run barrier, canonicalize the complete retained NORMAL record
authority under the existing persistence selection. Rebuild direct-entry,
opposite-exit and positional indexes from it. The baseline
`store/RecordStore.kt` appends delta records to indexes; that cannot be the
final query authority after relation pruning. Preserve both H classes and
NORMAL records with nonempty E. Keep existing backward-ZERO persistence and
handoff selection; do not replace it by a new all-NORMAL rule.

## 5. One C2 emitter

Implement the scalar selector in `ap/RestrictedInitialPolicy.kt`. Its inputs
are a legal demand entry, an original submitted scalar and its support.
First check base, bounded grammar and directed mark compatibility. A concrete
T demand accepts T only. FLOW accepts admitted full marks and compatible
FLOW exclusions. Use the existing catalog binding for optional GROUP.

Ignore selector E only for abstract FLOW/STAR demand. Keep real actual E,
mx, H and support. The existing query-only view can clear raw EXACT/FLOW E
for C2; it does not change the actual used by summary application.

Let p be the demand head and q the actual head. Every proper descent must
pass its ancestor's tail/E test. EXACT cannot descend; STAR/MUST cannot enter
an excluded first field. Incomparable paths reject. MUST initials remain
forward-only. Stored FLOW demand entries are STAR or ANY, not EXACT.

| Heads | Demand tail | Actual tail | Primary shape |
| --- | --- | --- | --- |
| p=q | ANY | EXACT | p.EXACT |
| p=q | ANY | STAR or ANY | p.STAR, Empty E |
| p=q | ANY | MUST | p.MUST, actual E |
| p=q | STAR or concrete EXACT | Any legal actual | p.EXACT |
| q below p | ANY | Any legal actual | First new counted field r.STAR; concrete T plus EXACT exactly at r uses r.EXACT |
| q below p | STAR, run-2 | Admitted descendant | Requested p.STAR |
| q below p | STAR, later; or EXACT | Any | Reject |
| p below q | ANY | ANY | p.STAR, Empty E |
| p below q | ANY | MUST | p.MUST, normalized selector E |
| p below q | ANY | Ordinary STAR or EXACT | Reject |
| p below q | STAR or concrete EXACT | ANY or MUST | p.EXACT |
| p below q | Any | Ordinary STAR or EXACT | Reject |

Each command starts as an identity. FLOW and ZERO start NORMAL. Concrete
STAR starts DEMAND. Concrete EXACT/MUST starts NORMAL only with NORMAL
actual support; an exact selected from ANY remains DEMAND. No concrete
DEMAND actual becomes NORMAL. A conditional FLOW start does not promote
the actual input.

Replace the single production result from `emitAdmission` with a small
list or visitor. Keep the primary helper private to the shared policy.

```kotlin
fun emitAdmissions(d, actual, support): List<InitialEmission> {
    val shape = emitPrimary(d, existingC2QueryView(actual)) ?: return emptyList()
    val result = linkedSetOf(
        InitialEmission(shape, admissionLayer(shape, actual, support)))

    if (shape.isConcreteStar()) {
        result += InitialEmission(shape.asFlow(mx=EMPTY), NORMAL)
    }
    if (d.tail == ANY && actual.path.strictlyExtends(d.path)) {
        result += InitialEmission(
            exactFlow(d.base, d.path, E=EMPTY, mx=EMPTY), NORMAL)
    }
    check(result.none { it.pattern.tail == ANY })
    return result.toList()
}
```

The STAR companion has the primary's exact path/E. The prefix companion has
the demand head, Empty E/mx and no new H. Both require a successful primary.
Wrong mark/base/shape, an excluded descent or a rejected STAR ancestor gives
no command. Same-head ANY admission gives no prefix companion. Controls
admit only canonical ZERO and create no DATA companion.

Keep raw EXACT/FLOW exact during execution. A direct return can later
normalize it to a STAR summary. It cannot read an arbitrary strict child.
An ordinary field write must update its E before that normalization. Keep
whole-position RemoveAll, selected mx cleaning and ANY/DEMAND residuals.

```text
demand p.ANY/T; actual p.f.g.$/T,N:
    p.f.*/T,D       -> same fact                 // primary
    p.f.*/FLOW,N    -> same fact                 // STAR companion
    p.$/FLOW,N      -> same fact                 // prefix companion

demand p.f.$/T; actual p.*/T,D:
    no initial; no companion

demand p.ANY/U; actual p.f.$/T,N; U != T:
    no initial; no companion
```

### 5.1 Use the complete command family everywhere

Update `ap/Demand.kt:emitInitials`,
`engine/RestrictedInitialEmission.kt`, and
`store/DemandResultCoverage.kt:InitialDemandResults` to consume this emitter.
Caller lookup is still performed once and passed to the callee. Preserve
the current call order: saved NORMAL replay, demand lookup, current summaries
and subscription. No relevant demand means no current subscription.

`InitialDemandResults.offer`, `has` and `requireFamily` must compare all
commands, including layers. Finding the primary alone is not complete
coverage. Run-2 static lookup must not stop before it has accounted for
companions. Intern only commands that are actually emitted; do not create
hypothetical APs during a family/image test.

Use the same emitter for block entry, repeat/adjacent loop C2 and enclosing
observations. Keep the real input binding so application still joins its
support and transports H. Do not create a second callee lookup.

Assert the no-ANY owned-initial invariant in `startInitials` and block
`addInitial`, and check owned premises at publication. Do not ban ANY in
the general Pattern or record-view API: a demand selector or an opposite
read view can still have ANY. Such a view is not an owned analysis initial.

## 6. C5 uses the same constructive image

### 6.1 Entry authorization

`canEmitInitial` describes the raw image of the selected primary.
`canStoreInitial` tests its public normalized image and the authorized
concrete-STAR FLOW companion. Keep the raw containment check.

```kotlin
fun canStoreInitial(dc, storedP): Boolean {
    if (primaryStoredImageWithRawContainment(dc, storedP)) return true
    if (!storedP.isFlowStar() || !dc.requiresConcreteMark()) return false
    val twin = storedP.withMark(dc.concreteMark)
    return primaryStoredImageWithRawContainment(dc, twin)
}
```

The twin is a query witness, not an emitted full mark. Do not run a second
`markSub(T,FLOW)` rejection after this authorization. The paired output
still rejects a FLOW result whose mx excludes T.

The exact prefix adds a raw preimage, but no new public entry key. A FLOW
ANY entry already permits its normalized root STAR/FLOW key. A concrete ANY
entry permits that key through its concrete STAR primary and FLOW companion.
Keep the existing whole-FLOW EXACT preimage for normalized STAR keys, also
at field-limit boundaries. Do not test image membership by
`emit(d,p)==p`: run-2 requested STAR is not an idempotent emission cell.

Use this one predicate in `EntryRestrictionTicket.prepare`, native
`DemandStore`, `StaticPairLookup` and prepared output programs. Do not add
caller-specific permission metadata or actual-input history to C5.

### 6.2 One complete paired intersection

A previous edge is `Dp -> Dc`; current candidate is `P -> C`. Dp and P
have one chain in the scalar kernel. Dc and C can have trees. Split their
chains in the reference only. Each selected chain keeps the original full
row, headers, owner and paired Dp budget.

```text
intersectEdge(previous=(dp -> Dc), candidate=(p -> C), policy):
    require same owner/context/direction/scope/physical ports
    (p,C) = normalizeWholeFlowPair(p,C)
    result = empty class-aware exact union
    for dc in scalarChains(Dc):
        if not canStoreInitial(dc,p): continue   // includes FLOW companion
        for c in scalarChains(C):
            selected = intersectChain(c,dp)
            if selected is absent: continue
            cap = min(policy.fieldLimit, countedDepth(dp)+1)
            if countedDepth(selected) > cap:
                selected = cutKeepingStaticAnchor(selected,cap)
                selected.tail = ANY
                selected.E = empty
                selected.layer = DEMAND
            if selected is EXACT/FLOW: selected.tail = STAR
            result.add(p -> selected)            // keep P and supplied H
    return packPerClass(result)

intersectChain(c,d):
    d = clearEOnlyForAbstractFlowStarSelector(d)
    if differentBases(c,d) or noMarkOverlap(c,d): return absent
    if c.path == d.path:
        if c.tail in {EXACT,STAR}: return c
        if c.tail == ANY:
            return c with tail=(EXACT if d.tail==EXACT else ANY), E=empty
        if c.tail == MUST:
            if d.tail == EXACT:
                return c with tail=EXACT, E=(c.E if c is FLOW else empty)
            if d.tail == STAR: return c with E=c.E union d.E
            return c
    if c.path strictly extends d.path:
        return c if d.tail/E admits that suffix else absent
    if d.path strictly extends c.path:
        if c.tail==EXACT or c.tail/E excludes that suffix: return absent
        if c.tail==STAR: return c                // preserve correlation
        if d.tail==EXACT: return c with path=d.path, tail=EXACT, E=empty
        return c with path=d.path,
            E=(d.E if c.tail==MUST and d.tail==STAR else empty)
    return absent
```

Keep the mark/mx, support and H of c. This operation never synthesizes T
from FLOW. Normalization converts an entire eligible FLOW pair and preserves
each endpoint's own path/E. It does not normalize concrete EXACT to STAR.

| Current c | Paired dp | Selected result, before/with cap |
| --- | --- | --- |
| `x.$/T,N` | `x.ANY/T` | `x.$/T,N` |
| `x.ANY/T,D` | `x.$/T` | `x.$/T,D` |
| `x.*/T,D` | `x.f.$/T` | Keep `x.*/T,D`; this is C5, not C2 admission |
| `x.MUST/T {f},N` | `x.*/T {g}` | `x.MUST/T {f,g},N` |
| `x.ANY/T,D` | `x.f.ANY/T` | `x.f.ANY/T,D` |
| `x.f.g.h.$/T,N` | `x.f.ANY/T`, global limit at least 2 | `x.f.g.ANY/T,D`, paired cap 2 |
| `x.$/T,N` | `x.f.ANY/T` | Empty |
| `x.MUST/T {f},N` | `x.f.ANY/T` | Empty |
| `x.*/FLOW,N`, mx contains T | `x.ANY/T` | Empty |

Use the existing `Reference.restrictConclusionOnly` geometry. Do not replace
the retained correlated STAR cell by a C2-style ancestor rejection. Do not
stop after the first matching DATA pair. Two pairs can select the same
candidate and preserve NORMAL in one while cutting it to DEMAND in another.

The ND adapter checks existing entry witnesses while retaining complete P.
It must not turn an AND premise into a unary executable summary. Keep typed
control cases: ZERO/Target Dc admits canonical ZERO; DATA Dc rejects ZERO;
ZERO Dp accepts Reach or DemandTarget. Keep NormalTarget's forward NORMAL
composition and persisted deduplication; ignore it backward.

### 6.3 Prepared lookup and publication

Keep `PreparedLocalDataPlan` and `PreparedOutputPrograms` as optimized
implementations of this kernel. Prepare by exact original, run policy,
scope/physical port and immutable demand snapshot. Reuse the plan. Preserve
all paired output programs. If preparation is unsupported or exceeds its
existing limit, fall back to native C5 without publishing a partial result.

The native trie walk need not materialize the scalar Cartesian reference
loop. It selects relevant demand and output paths together. Its exact union
and packing must keep both H classes.

```text
boundary candidate
  -> existing boundary liveness
  -> whole-FLOW-pair normalization
  -> paired C5 and each row's FL+1 cut (all candidate layers)
  -> canonical admitted authority
  -> final-basis publication
  -> saved records / next demand at the joined barrier
```

No raw rejected relation is stored as a semantic provider. Run-1 has no
previous demand snapshot and keeps its ordinary global limit.

### 6.4 Handoff format closure

C5 can select an EXACT/FLOW result on DEMAND from a raw ANY/FLOW
candidate. Whole-pair normalization then publishes STAR/FLOW on DEMAND.
A correlated STAR candidate can also remain STAR on DEMAND. These are
legal selected results; the handoff must not require every FLOW demand to
have ANY tail.

Reuse the existing guidance projection. It preserves STAR correlation,
clears FLOW selector E/mx, converts MUST guidance by its existing rule, and
keeps the complete pair and physical block ports. Accept STAR or ANY FLOW
entries at every restricted run. Do not widen STAR to ANY, drop the pair,
or promote DEMAND to NORMAL.

Update the old validators in BlockRunState.retainSummary,
HandOff.forEachDemandPiece, block handoff, and
DemandStore.validateIncoming. Keep the typed constructors and all C2/C5
checks. Add a native raw-ANY-to-EXACT-to-STAR test through both method and
block handoff and the next RunConfig. The constructive format bridge is
in spec/lean/proposals/flow-star-demand-handoff-20261108/.

## 7. Cleaner and loop changes

### 7.1 Selected PART STAR survivor

Change both scalar `ap/Reference.kt:cleanResRaw/concPart` and tree
`ap/Clean.kt:TaintClean.cut`. Keep the old mark/base/spatial/E checks first.
The new branch follows the existing same-head BELOW-to-EXACT branch.

```kotlin
when {
    existingMustImmediateChildCase -> existingMustResult()
    existingSameHeadBelowCase -> put(oldLayer, at, EXACT, selectedMarks)
    tail == STAR && isSelectedMarkCleaner ->
        put(DEMAND, at, ANY, selectedMarks, E=EMPTY)
    else -> existingPartSurvivor()
}
```

Here `selectedMarks` is the existing `gone(marks)` result for the selected
scalar mark or FULL mask. RemoveAll has no selected mark and cannot enter
this branch. A cleaner under an excluded field is disjoint before this code.
Do not widen that result. Keep the existing GROUP no-kill behavior.

Emit only the replacement, not old STAR plus new ANY. Keep the complete P,
base, path, full mark, DEMAND support and existing protection. Keep separate
exact siblings, other marks, MUST/MAY/EXACT results, kills, FLOW mx and
requests. `ApOps.clean`, `cleanSelectedFullMask` and the existing protection
wrappers still decide H; split their fresh outputs into the class packets.
Add no survivor provenance field.

### 7.2 Applied loop summary

Change the two runtime callers in `engine/MethodBlockRuntime.kt`.

```kotlin
// Current rows and same-direction saved rows.
fun onData(..., row: PremiseKey, geometry: Pattern, original, value) {
    val needsGate = !row.isZero && loopSummaryGrows(row,geometry)
    onApplied(..., needsGate, original, value)
}

// view is the effective row after opposite-direction reversal.
fun applySavedView(..., view: RecordLeafView, protected) {
    val needsGate = !isCanonicalZero(view.premise) &&
        countedDepth(view.result) > countedDepth(view.premise)
    applyRecordView(..., view, protected, onData = { original,value ->
        onApplied(..., needsGate, original, value)
    })
}

fun onApplied(..., needsGate, parentOriginal, value) {
    val routes = existingPreparedExitAndLiveness(value.base)
    if (routes.isDeadData) return
    for (bounded in existingGlobalLimit(value)) {
        val outputs = if (isLoopBoundary && needsGate && !run1)
            existingFullLoopRestriction(bounded)
        else listOf(bounded)
        for (kept in outputs)
            existingFreshCompletionAndRouting(parentOriginal,kept,routes)
    }
}
```

Never use `parentOriginal` or the caller's ZERO to decide the bypass. A DATA
grower under a ZERO parent remains gated. A genuine ND premise is DATA and
keeps the existing arm-based growth test. FL(ZERO) remains zero. Rename the
runtime Boolean from `grows` to `needsGate` to make its role clear.

Mirror the test in the `LoopOutputRestriction` convenience overload, but
do not treat that overload as the only runtime change. Keep paired C5 before
current publication, global limiting before delivery, local liveness,
source permissions, physical ports, deduplication and Target handling.

### 7.3 Existing loop certificate

`LoopRestrictionSession.certifiedFirstBudget` currently checks one scalar
emission and requires ANY/DEMAND. That assumption no longer applies. Return
no certificate for unsupported expanded-emitter cases and use the existing
complete observer. Do not substitute a STAR comparison without a proof.

A later optimized certificate must compare the whole labeled command family
and all observation routes. This proposal selects correctness fallback,
not a new longest-demand pruning law or a different DATA growth test.

## 8. Principal implementation traces

Use real code and source/sink rules in native tests. Do not supply the needed
summary or demand as a fixture in a test that claims full-driver recovery.
Component tests may supply a row, but must state that precondition.

### 8.1 Selected root cleaning: required finding at run-3

```java
// Source rule: T at p.g.$. Sink rule: CM(r.g.$, T).
// Run-1: initial p.*/T,D; independent FLOW analysis stays NORMAL.
Box m(Box p) {
    cleanRootT(p); // selected T only at p.$
    return p;
}
// Run-1 summary: p.*/T -> ret.ANY/T,D,H=true.
// FLOW excludes T and cannot back this marked survivor.

// Run-2: demand ret.ANY/T -> p.*/T.
// Submitted ret.g.$/T,N.
// Initials ret.g.$/T,N and ret.$/FLOW,N.
// The backward exact g fact is disjoint from cleanRootT(p).
// Retained NORMAL: ret.g.$/T -> p.g.$/T,H=true.

// Run-3: saved opposite replay on actual p.g.$/T,N.
// Result ret.g.$/T,N,H=true; ordinary sink -> NormalTarget(id).
```

The prefix companion must remain exact while m executes. Test a child write
and RemoveAll negative control. Do not infer a NORMAL T identity through the
selected root cleaner.

### 8.2 Own-ZERO loop output: required finding at run-5

```java
while (true) {
    sourceAtFFFF(x); // rule assigns T at x.f.f.f.f
    x = x.f;
    sinkT(x);       // rule checks x.$/T
}
// Run-5 local published row: ZERO -> x.f.f.f.$/T,N.
// Its effective own premise is ZERO: bypass only the extra loop gate.
// Repeat receives x.f.f.f.$/T,N after the global bound.
// Saved NORMAL x.f.*/FLOW -> x.*/FLOW gives x.f.f.$/T,N,
// then x.f.$/T,N. Existing exact admission and the actual read/sink
// produce ZERO -> NormalTarget(id),NORMAL at the enclosing owner.
```

Test the actual `onData` and `applySavedView` routes. Also test a DATA-owned
grower under parent ZERO: it must still invoke the full restriction. No new
DATA demand, ZERO seed or FLOW endpoint completion is needed for this case.

### 8.3 Conductor-shaped uniform input: run-4/run-5 recovery

```java
// Source rule: uniform T at p.f; sink rule: exact T at mapped.e.h.
void root() {
    Object p = initializedRoot();
    sourceUniformT(p.f);
    Object mapped = mapper(p);
    sinkExactT(mapped.e.h);
}

Object mapper(Object p) {
    Object out = initializedResult();
    if (flag()) out.e.h.extra = p;
    else out.e.h = p.f.g;
    return out;
}
```

At run-3, root ANY/FLOW demand and actual `p.f.MUST/T,N` emit the field
STAR/FLOW primary and raw `p.$/FLOW,N` prefix. They do not invent a MUST
initial. Both mapper return branches can still be DEMAND. Continue the
driver; do not treat that run-3 delay as proof of permanent loss.

```text
Run-4, backward, global limit 3:
  complete demand pairs at mapper:
    dc=ret.e.h.ANY/FLOW, dp=p.f.*/FLOW
    dc=ret.e.h.ANY/FLOW, dp=p.*/FLOW
  submitted: ret.e.h.$/T,N
  raw initial: ret.e.h.$/FLOW,N       // ONE exact live initial
  good branch raw result: p.f.g.$/FLOW,N
  whole-FLOW normalization: ret.e.h.* -> p.f.g.*,N
  paired C5 results:
    ret.e.h.* -> p.f.g.*/FLOW,N      // cap 2
    ret.e.h.* -> p.f.ANY/FLOW,D      // cap 1

Run-5, forward, global limit 4:
  saved opposite NORMAL: p.f.g.* -> ret.e.h.*/FLOW
  actual: p.f.MUST/T,N
  saved application: ret.e.h.MUST/T,N -> exact sink NormalTarget
  current child demand: p.f.ANY/FLOW -> ret.e.h.*/FLOW
  current initial: p.f.MUST/FLOW,N
  good branch: ret.e.h.MUST/FLOW,N
  deep-copy branch raw: ret.e.h.extra.f.MUST/FLOW,N
  paired cap 3: ret.e.h.extra.ANY/FLOW,D
```

Keep both run-4 outputs. The precise NORMAL row does not cover the ancestor
ANY/DEMAND output. The latter derives the finer run-5 guide. Run-5 has a
NORMAL finding route and can also have outgoing demand. Do not require
natural termination at run-5. The
[full trace](../../spec/conductor-must-admission-fact-trace-20261108.md)
pins the captured real query and both historical Conductor sink identities.
Their full-project recovery remains a separate mandatory test.

## 9. Constructive proofs and correspondence checks

Use the existing
[proof package](../../spec/lean/proposals/subsumption-initial-demand-20261107/README.md)
and [obligation map](../../spec/subsumption-initial-demand-proof-obligations.md).
The latest complete
[receipt](../../spec/lean/proposals/subsumption-initial-demand-20261107/component-checks-1245.json)
checks 1,245 declarations with `PASS_LOCAL_COMPONENTS_ONLY`.
`nativeAnalyzerProved=false` and `allPrincipalProgramsProved=false` remain
true statements about its scope. The count includes historical and negative
results. Do not use the withdrawn OR, completion or special-tail model as
proof of the selected operator.

### 9.1 Executable proof arguments

**Class representation and delivery.** Decode a homogeneous packet as its
root coordinates paired with its class. Splitting a fresh mixed producer
partitions those coordinates by its selected mask. Packing merges only equal
classes. Thus decode after packing is the same per-class membership union.
Overlapping U/H roots decode to two distinct memberships. For each offer,
insert only into its class and publish that fresh class. Induction over the
offer list gives the same class authority at the subscriber. A later parent
removes a covered child through the same insertion at both owners. A pass
maps each membership with the same H. It cannot create H from a plain input.
The offer list is a proof witness, not retained runtime history.

**Spatial canonicalization.** A descendant MAY witness maps to its retained
prefix. A descendant MUST witness remains admitted exactly when its first
suffix field is outside ancestor E. Same-head union excludes only fields
excluded by both inputs. A complete immediate child supplies every location
in one missing branch; a partial/deeper child has a concrete missing witness
and cannot fill it. Apply these constructions independently per class/mark.

**Relations and transitivity.** For a long correlated row suffix tau, use
`r+tau` in the short row. At r empty, combined endpoint E inclusion preserves
admission. At r nonempty, its first field outside both short exclusions
admits the entire long region. Mark-set inclusion preserves the chosen mark.
Compose these witnesses for A/B/C; B need not be stored. The matching slice
with union E preserves an actual witness needed after the long row is
removed. This is why overlap matching must land before relation pruning.

**C2 and C5 entry.** Split heads into equal, actual-below, demand-below or
incomparable. The table constructs the root EXACT/STAR/MUST or first-field
EXACT/STAR witness. None has ANY tail. Its depth is at most demand depth+1.
Build the structural image witness from the same templates, including a
legal fresh counted field for run-2 requested STAR. At the field cap that
witness does not exist. Add the concrete-STAR FLOW branch only after its
concrete twin has a raw witness. The exact prefix has a new raw witness but
an already legal public STAR/FLOW key. These witnesses establish the shared
entry predicate; they do not assert that an unknown actual carries T.

**Paired C5.** Select one complete row and one candidate output chain. The
scalar meet keeps its mark, H and support. A dropped suffix has an explicit
witness in the ANY/DEMAND cut at that row's cap. Union all matching rows.
No row borrows another row's paired exit or budget. Exact FLOW publication
normalizes the complete eligible pair after real field writes have supplied
the required E. The saved record therefore cannot restore an overwritten
field. A concrete DEMAND output never becomes NORMAL by this restriction.

**Cleaner.** Keep the old selected PART survivor's input and output witness.
ANY accepts that pair without STAR suffix correlation; clearing E broadens
only this already DEMAND result. This is conservative inclusion, not equality.
The exact branch guard proves that NORMAL, other-tail, disjoint, excluded,
other-mark, full-kill and RemoveAll results are unchanged. E31 separately
checks the later precise NORMAL route; inclusion alone is not progress.

**Own-ZERO loop.** A fixed own-ZERO row has no incoming suffix to append.
Repeated application yields the same globally bounded geometry, which the
existing completion store deduplicates. DATA rows can append a prefix and
retain the old growth gate. Testing the effective local premise preserves
that distinction under reversal and under a ZERO parent. The E21 witness
then reaches the saved shrinking NORMAL reader and the actual sink.
This argument gives no general workload or whole-program convergence bound.

### 9.2 Proof-to-code map

| Obligations | Checked model / evidence | Native acceptance work |
| --- | --- | --- |
| P01-P04, P27, P32 | Canonical, Relations, SelectedTransitiveSubsumption, CombinedExclusionCoverage, CurrentCoverageInvariant, PlainCoverageDelivery | Two-class packet codec, all E/mx headers, both orders, mixed marks, delivery and restore |
| P05, P24 | Matching, StarHeadOverlap, CombinedOverlapBridge | Explicit read roles; actual overlap; trusted reverse-MUST capability |
| P06-P08, P25 | RelativeAdmission with selected overlays; RejectAncestorStarAdmission; ConcreteStarFlowCompanion; ExactFlowPrefixCompanion | Complete production emitter, constructive stored image, static anchors and native catalogs |
| P09-P12, P28 | AnnotatedC5Exit, ScalarChainIntersectionExamples, GetFFC5Policy | Scalar/native/prepared equality, full ND P, both paired outputs, field E before FLOW normalization |
| P13-P20, P23, P29-P30, P33-P35 | WrapperRecovery, concrete/static/loop phase models, E21 closure models, GetFFExactFlowPrefix, ZeroPremiseLoopBypassCandidate | Real root driver, source callbacks, all physical ports, loop runtime seams and natural stop controls |
| P31, P36 | SelectedCleanerStarSurvivor; E31 phase model | Scalar/tree/bulk FULL equality; exact guards; source-to-NormalTarget through run-3 |
| P19, P26 | ConductorLateIterations and the three native late-iteration component checks | Full small program through run-5 and both real Conductor identities |
| P21-P22 | Historical completion comparisons and actual disjoint-write controls | No completion code; retain same-field kill/disjoint-field tests |

The 44 selected-cleaner, 33 separate-delivery, 11 ZERO-bypass and 36
Conductor-late declarations have their stated component scopes. The native
[ZERO component receipt](../../spec/lean/proposals/subsumption-initial-demand-20261107/native-zero-loop-bypass-candidate-20261108/receipt.json)
has eight tests with a test-only policy adapter. The native
[Conductor receipt](../../spec/lean/proposals/subsumption-initial-demand-20261107/native-conductor-late-iterations-20261108/receipt.json)
has three tests from an explicit run-3 boundary snapshot. Neither receipt
is an end-to-end implementation result.

Before native implementation, check the pinned constructive sources. During
implementation, add the packet-codec and native adapter differential checks
before enabling each optimized path. Use no `sorry`, custom axiom, classical
choice or assumed native-equivalence theorem. A new counterexample must
refine the model or lead to an explicit behavior decision; do not weaken the
test silently.

## 10. Lookup and storage cost

Let h be path depth; v the visited trie nodes; c the tested headers/records;
e the E/mx and mark comparison cost; q the selected C5 programs; and o the
emitted output size. These are per query, not project-size constants.

| Operation | Expected work bound | Avoided work / limit |
| --- | --- | --- |
| Fresh producer class split | O(v) in selected mask/root | At most two class streams per compatible packet header; no offer archive |
| Canonical insertion | Visited trie/header work to the local fill/prune fixed point | No path-product enumeration; a linear worst-case claim is not made |
| C2 selected cell | O(h+e), at most 3 commands | No concrete mark enumeration or hypothetical AP interning |
| C2 trie lookup | O(h + v + c*e + commands), plus terminal-order sorting | Reuse caller lookup; completion checks the entire command family |
| Relation provider lookup | O(h + c*(h+e)), plus visited output nodes | Index by compatible interface and input prefixes; do not scan all owners |
| Native/prepared C5 | Selected trie/program work plus O(o); reference worst case is Dc-chains times C-chains | Keep complete pairs; prepare once and reuse |
| ZERO bypass decision | O(1) after effective premise is known | Skip only extra loop observation; global bound and dedup remain |
| Persistence | One final authority freeze and index rebuild per joined barrier | Removed long records cannot remain in a historical delta index |

Two H lanes and up to three initial commands can increase work. The purpose
is correct admission plus removal of redundant paths and relations. Do not
promise a speedup or unchanged callback counts before measurement.

The current `FrozenDemandTrie.visitCountedNativeOrder` can visit the whole
subtree below an actual head. Count all visited profiles, including rejected
ones. Sorting costs the sum of O(s*log(s)) for selected terminals at each
visited node. The proposal does not replace that traversal by an unproved
constant-time or selected-only lookup. Retain its node/profile/candidate
counters in the experiments.

## 11. Implementation sequence and required tests

1. Preserve the prototype. Create and pin the baseline checkout. Repeat the
   constructive component check and retain its receipt.
2. Write failing tests for separate H identity, temporary unions, scalar
   promotion, packed storage, publication and saved replay. Implement the
   homogeneous packet boundary and independent lanes first.
3. Add scalar reference canonicalization and relation tests. Implement
   same-head overlap and explicit read roles before enabling broader relation
   pruning. Test transitive FLOW/T coverage without an intermediate row.
4. Write the complete C2 table and image tests. Implement one multi-command
   emitter. Update caller, block, loop and static family consumers together.
5. Differential-check scalar/native/prepared C5 with the shared entry
   predicate. Keep the existing output kernel and per-row cap. Audit all
   exact unions for class preservation. Disable an unsupported certificate
   through its existing full-observer fallback.
6. Add selected PART-cleaner tests and the two loop runtime-seam tests.
   Implement only their guarded changes. Run the full principal programs.
7. Run the core and JVM integration checks. Freeze the actual built runtime
   and its configuration. Then run the unchanged four-project campaign.
8. Review exact finding differences and workload evidence before accepting
   the implementation. A failed gate needs an explained first divergence,
   not a lower assertion count or an extra unselected semantic mechanism.

Use existing suites where they fit:

| Area | Existing test seams to extend | Required checks |
| --- | --- | --- |
| Spatial and class storage | `GroupMergeTest`, `GroupNormalizationReferenceTest`, `ProtectionStoreTest`, `DiagonalRelationsTest`, `ScopedBlockStorageTest` | Packet + both orders; independent flags; full immediate fill versus partial/deeper child; class-aware promotion and scalar fallback |
| Summary providers | `FlowBackedOwnersTest`, `FlowBackedSummaryStoreTest`, `RecordReplayTest`, `RecordOutputPositionTest` | A/C without B; legal statics; both E endpoints; mx subsets; final-basis publication/direct/opposite/restore |
| C2 and layers | `RestrictedInitialPolicyTest`, `InitialEmissionContractTest`, `EmissionTest`, `InitialLayerDeliveryTest` | Every table cell, no ANY owned premise, all command families, wrong mark/field, support and field cap |
| C5 | `DemandRelativeRestrictionTest`, `DemandStorageDifferentialTest`, `PreparedDemandPlanTest` | Native/prepared/reference equality, nonempty E, concrete twin permission, rejecting excluded T, both per-row outputs |
| Loops and statics | `LoopConsumerObservationTest`, `LoopRestrictionSessionTest`, `ScopedStaticCompletionTest` | Complete command families, full-observer fallback, exact physical ports, own-ZERO versus parent-ZERO, global cut and duplicate output |
| Cleaner/pass | `CleanerTest`, `ReturnFullCleanupTest`, `FlowBackedProtectionTest`, `Run1OriginProtectionTest` | Selected PART only, bulk mask equality, disjoint/excluded/other tails/RemoveAll unchanged; plain pass never adds H |

Run E01-E31 with their positive and negative controls. For each changed
shape assertion, cite the selected spec clause. Keep strict source-to-sink
assertions. In particular, require the original nested getter/wrapper route,
E30's actual two-read route, E31's run-3 NORMAL finding, E21's run-5 NORMAL
finding and the current-spec E29 small route through run-5. Do not assert a
run-5 stop for E29. Run natural convergence controls with the existing empty
outgoing refinement demand criterion. Never stop because counts are stable.

Useful commands from the implementation checkout are:

```bash
python3 spec/lean/proposals/subsumption-initial-demand-20261107/check.py \
  --output-directory /tmp/subsumption-implementation-proof-check-UNIQUE

cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --no-daemon --max-workers=2
```

Use a fresh proof output directory. Run the applicable JVM/integration gates
from the repository workflow after the focused tests pass. No test result
is claimed by listing these commands.

## 12. Removed and retained mechanisms

| Mechanism | Action |
| --- | --- |
| STAR_OR_ANY enum branches, marker propagation, marker image/normalization adapters and prototype-only tests | Do not import from the withdrawn prototype |
| ANY owned initial emission | Replace by the C2 table; retain ANY actuals, selectors and conclusions |
| OR-upgraded exact H identity, replay Boolean upgrades, cross-class result unions | Replace by independent memberships and class-aware batches |
| Nonstatic-only / Empty-E-only / equal-mx-only relation guards | Replace only inside the proved aligned relation domain |
| Append-only historical normal-delta query basis | Replace final query authority with retained records and rebuilt indexes |
| Primary-only production C2 call sites | Replace by the complete stream; keep a private scalar primary helper |
| Old ANY/DEMAND loop fast-certificate assumption | Reject unsupported certificate and use full observer |
| FLOW endpoint completion, paired-head erasure and stored raw histories | Do not implement; they are unselected historical candidates |
| Original E/mx field transfer, full ND execution, source/Target protocol, global bound, DATA loop test and stop rule | Reuse under the stated narrow changes |

## 13. Post-implementation experiments

Run OWASP as in `.github/workflows/ci-analyzer-owasp.yaml`. Run Conductor,
Thingsboard and Stirling-PDF with the saved project configurations in
`../opentaint-test`, through `runProjectAnalyzer` directly. Keep FULL,
16 GiB analyzer heap, enabled aliases/statics, limits `1,1,2,...`, and the
saved IFDS/outer budgets. The recorded campaign uses IFDS 1,000 seconds for
OWASP, 1,080 for the other projects and outer 1,200. Read the actual config
before launch; if it differs, report the difference and do not silently
select another experiment. Reuse f945 quality evidence; do not rerun it.

Record the runtime revision, core tree, runtime artifact hashes, rules,
project model and command. Build/package all selected artifacts before the
classpath is frozen. Keep prescan, run-1 engine and transition timing separate.
The run-1 target remains 60 seconds of engine time.

Every runtime report must give the latest reached run, latest engine-complete
run, latest fully committed run and latest accepted forward report, with
labels such as run-1/run-5. A cleanup barrier or timeout snapshot is not a
completed iteration. No new project run has been made for this proposal.

### 13.1 Quality and convergence

Compare exact report identities against saved f945 and the pinned baseline.
List missing and added identities. Explain timeout/OOM censoring separately
from a demonstrated missing path. Verify the two real Conductor Graal
identities in E29. Do not treat the small mapper result as full-project proof.
Keep historical Stirling quality gaps visible; do not label them fixed by
this patch without tracing the relevant source-to-sink route.

Record every iteration's direction, field limit, engine/transition time,
NORMAL/DEMAND summaries, Targets, demand method keys and stop reason. Test
the natural stop behavior. Do not replace the existing rule by an iteration
cap or stable demand count.

### 13.2 Repeat the fact-path explosion investigation

At run-1 and each expensive restricted run, collect these shapes:

```text
actuals and raw initials: base class, path depth, tail, mark/FLOW, E/mx, N/D, H
initial commands: primary / STAR companion / exact prefix companion
raw boundary candidates -> normalized pairs -> C5 admitted pairs
per-row cap: in-budget NORMAL / existing DEMAND / new field cut / rejected
retained summaries: plain / protected / both exact classes
coverage: direct FLOW / aligned FLOW / transitive FLOW-to-T / MUST / MAY
not covered: no provider / shift / tail / base / interface / E / mx /
             mark-changing / support / opposite H / separate exact-MUST rule
loop: own-ZERO bypass / DATA non-growing / DATA growing observed /
      observer cut or rejection / certificate fallback / completion duplicate
delivery: subscriptions / matches / applications / fresh outputs / duplicates
```

For class statistics, report both memberships and unique geometries. A plain
and protected overlap counts as two memberships. For “shape covered but H
blocks removal,” show the exact candidate and all relevant FLOW providers.
Do not infer a root cause from a flag total alone.

Select representative dominant facts in Conductor and Stirling, in both
directions. Trace the same concrete relation through C2, post-statement
storage, loop completion, call subscription, summary application, C5 and
handoff. Include all relevant shorter NORMAL providers. Distinguish a long
candidate cut by C5 from a retained relation that can continue to grow.
Determine whether remaining growth is intra-procedural path generation,
inter-procedural summary application, or repeated lookup/delivery of already
covered data. Analyze Thingsboard statics separately under the same config.

Count work avoided and work added by the patch: deleted covered paths and
relations, eliminated future subscriptions, extra companion commands, two-class
deliveries, exact prefix results, and observer fallback work. Report operation
counts with their owner/fact shapes. A faster lookup alone is not evidence
that the redundant workload has been removed.

Capture CPU/allocation samples during active workload and near the configured
time limit, using the established profiling setup. Take heap snapshots on
the existing MemoryManager/JVM OOM event. Analyze retained owners separately
from allocation churn. Clean old owned snapshots/profiles before the campaign
after their required evidence has been retained. Do not delete the pinned
proof or native component receipts.

### 13.3 Acceptance boundary

Accept only after the native correspondence tests and configured quality
checks support the result. Record any unfinished project or proof check
explicitly. The current lack of another known FULL-mode FN counterexample
does not remove these gates. If measurements expose a new design issue,
show the code and inline fact trace and obtain the intended behavior before
adding a major semantic change.

## 14. Proposal preparation checks

The baseline source map and proposed adapters received three independent
reviews: storage/delivery, C2/C5, and cleaner/loop handling. No new undecided
behavior gap was found. The reviews corrected the demand-trie cost bound
and preserved the existing per-origin run-1 layer test.

The pinned constructive package was checked again during proposal
preparation: `PASS_LOCAL_COMPONENTS_ONLY`, 1,245 checked declarations,
`allPrincipalProgramsProved=false`. Local document links and patch whitespace
checks passed. No production source was changed and no project benchmark
was run for this proposal.
