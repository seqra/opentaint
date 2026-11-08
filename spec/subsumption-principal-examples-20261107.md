# Principal examples for subsumption and initial/demand redesign

Date: 7 November 2026. Finalization status updated 8 November 2026.
These are the principal examples for the finalized combined specification.
Language: ASD-STE100 Simplified Technical English.

The implementation baseline is **52829d5890ec3b3145cc996a1d8162d85cb8ceda**.
Its core is identical to the reviewed **52f32dd437d438aec4a700a02c18d94c31d58093**
core. Read the [baseline definition](subsumption-redesign-baseline-20261107.md)
and the [byte-pinned original documents](baselines/subsumption-20261105/README.md).
Do not read later edits of the original proposal as the baseline contract.

This catalog separates three things:

- **B0:** behavior before implementation of the original subsumption proposal.
- **S1:** changes selected in the original 5 November proposal. Its frozen
  examples are contracts, not proof that an implementation passed them.
- **R2:** the new initial/demand redesign. The selected cells below prohibit
  ANY initials/premises, use ordinary STAR instead, and admit a same-head STAR
  input under an ANY demand. The selected STAR initial starts with an
  identity edge: its start conclusion is STAR too. There is no SOA or other
  new tail. The [combined specification](edge-subsumption-initial-emission-demand-intersection.md)
  defines the C2/C5 tables. FLOW demand completion is not selected. The ZERO-premise loop bypass
  and partial selected-cleaner STAR-to-ANY survivor are selected. Native
  correspondence and complete-policy convergence remain open.

Later native captures use their stated revisions. They are not B0 results.
The current protection decision permits subsumption only within the same
flag class. Exact plain and protected memberships both remain stored
and published. This supersedes OR-upgrade and the earlier rule which retained
every literal protected coordinate. Pass rules cannot add
protection. Do not silently attribute these later decisions to B0 or S1.

**Current known-gap status:** no further unresolved FN-producing
counterexample is known in the reviewed FULL-mode cases. E21 and E31 use
the selected loop/cleaner repairs; the Conductor-shaped uniform example
has a NORMAL route at run-5. Historical failures remain regression cases,
not new results for this final design. Full native/project validation
and universal proof obligations are separate.

## Notation and evidence rules

`F` is FLOW; T and U are full marks. `N` and `D` are NORMAL and DEMAND.
`$`, `*`, `MAY` and `MUST` mean EXACT, STAR, ANY and ANY_TAINT field tails.
`E` excludes fields immediately after a known prefix; `mx` excludes marks.
`H` is the non-subsumable flag. A STAR conclusion shares the original's suffix;
MAY has an independent unknown suffix. STAR does not mean uniform taint.

An **initial key** I and its **start conclusion** C are different values. The
command starts an edge `I -> C, layer`. R2 now requires a STAR identity start:
`a.STAR/T -> a.STAR/T,D` for both accepted same-head STAR and ANY inputs.
E25 keeps the historical independent start as a rejected alternative. Do not
call a MAY start conclusion an ANY premise.

A demand pair is `(Dc,Dp)`: entry permission and paired output permission.
An ANY demand selector or submitted fact is legal even when an ANY **initial
or summary premise** is forbidden. A MAY conclusion caused by a real field
cut is still legal. ZERO, Target, scope and physical ports are separate data.

For algebra examples, “if both rows are admitted” is an explicit assumption.
It does not claim that the listed program starts both hypotheses in one run.
For native cases, **captured**, **source-derived**, and **new prediction** have
different meanings. No new-design recovery is claimed without a native result.
An omitted normal/demand row means “not established here,” not an invented
empty method result.

## Coverage index

| Case | Required subject | Original or later source |
| --- | --- | --- |
| E01 | Aligned NORMAL relation and native extra MAY output | Original proposal §§4.1, 4.5; original relation audit §§2–3 |
| E02 | Unaligned paths, E, mx, scope and absent provider | Original proposal §§4.1–4.2 |
| E03 | Transitive FLOW/concrete coverage; all arrival orders | Original proposal §4.3; later user clarification |
| E04 | MAY/MUST prefix coverage and exclusions | Original proposal §3.1 |
| E05 | Complete-child fill, partial marks and mx | Original proposal §§3.1–3.2 |
| E06 | Cold packet, warm stores, delta freshness and stale delivery | Original proposal §§3.2, 4.4 |
| E07 | Canonical input changes C2's literal initial set | Original proposal §3.3 |
| E08 | Opposite MUST overlap, typed outputs and read metadata | Original proposal §3.4 |
| E09 | Directional strict-ancestor STAR matching | Original proposal §5; original relation audit §§4–5 |
| E10 | Correlated concrete STAR and protection | Original correlated/concrete and FLOW-backed specs |
| E11 | Same-flag coverage, separate exact classes and pass-role correction | Later selected decisions; not silently B0 |
| E12 | Initial table, marks, field limit and static grammar | Original AP policy; R2 selected output cells |
| E13 | Requested run-2 STAR and sibling overwrite | `OwaspDemandCycleTest`, sibling-overwrite control |
| E14 | Paired C5, normalization and cap | Original demand-relative restriction contract |
| E15 | EXACT FLOW, strong overwrite and RemoveAll | Original correlated spec; exact-normalization controls |
| E16 | Original four-method loop/getter finding | Later native loop-boundary reports; latest run-5 |
| E17 | Direct getter and nested FLOW wrappers | Later native nested-call report; latest run-3 |
| E18 | Concrete guarded converter wrapper | Same report; latest run-3 |
| E19 | Static no-loop positive and exact negative | Later native FULL static probe; latest run-3 |
| E20 | Two static loops, missing provider and actual ZERO replay | Later native 59-record control trace; latest run-3 |
| E21 | Deep no-leave loop and EXACT DemandTarget | Prior later native trace; latest run-5 |
| E22 | OWASP recurring demand and natural stop | `OwaspDemandCycleTest`; original demand-cycle investigation |
| E23 | ZERO/Targets, normal context and ND guards | Original AP/Target contracts and later exact-DEMAND decisions |
| E24 | Saved-first replay, aliases, liveness and owner boundaries | Original proposal unchanged contracts; actual loop/call pipeline |
| E25 | Initial key versus start conclusion; selected STAR identity and rejected independent start | Historical AP §6.5 versus the correlated extension and R2 decision |
| E26 | Static setter/getter/consumer, marked demand and typed ZERO closure | Static erasure/completion contracts and native regression destinations |
| E27 | Unprotected DEMAND STAR identity is not a NORMAL transfer proof | Abstract guarded-pass control only; native compiler removes a residual mark guard |
| E28 | Run-1 NORMAL identity and saved-first replay | Correction of the artificial missing-provider premise |
| E29 | Two missed Conductor Graal findings; lost child demand and weaker C2 admission | Real frozen Current/B snapshot run-4/3/3; main run-15/14/13; later recovery run-4/3/3 |
| E30 | Two reads need a correlated STAR return under a deeper output selector, or another refinement bridge | Constructive FULL policy comparison; modeled through run-5, no new native run |
| E31 | Direct exact-root selected cleaning blocks a precise marked child | Latest-emitter source/helper/sink catalog through run-3, completion off/on; native adapter open |

“Original proposal” means the frozen
[implementation proposal](baselines/subsumption-20261105/original-implementation-proposal.md).
Its companion [field-path design](baselines/subsumption-20261105/original-field-path-design.md),
[relation audit](baselines/subsumption-20261105/original-relation-and-matching-audit.md),
[FLOW-backed spec](baselines/subsumption-20261105/original-flow-backed-spec.md), and
[correlated concrete spec](baselines/subsumption-20261105/original-correlated-concrete-spec.md)
are also pinned at the baseline. Current tests linked below are regression
destinations, not evidence that their current bytes existed at B0.

## E01. An aligned longer relation adds no concrete pair

This is the original relation example. The code justifies the relations;
the displayed admission set is a condition of the algebra check.

```java
// Forward run-i, if one owner actually admitted both hypotheses:
//   S initial p.*/F; L initial p.f.*/F.
Box copy(Box p) {
    return p;
}
// S: p.*/F   -> ret.*/F,   N
// L: p.f.*/F -> ret.f.*/F, N
```

For each L suffix `tau`, choose S suffix `f ++ tau`. This is the same pair.
B0 can retain S and L. S1 keeps the actually admitted S and removes L.
R2 must preserve this original relation law; it must not invent S from L.

```java
// Backward run-(i+1), saved opposite records:
//   offered ret.*/F, N.
Box copy(Box p) { return p; }
// B0 native reads: S gives p.*/F,N; L can give p.f.MAY/F,D.
// S1 basis: S only, so p.*/F,N remains and the extra approximation is absent.
// Offered ret.f.g.$/T,N: S and L both transport p.f.g.$/T,N.
```

The extra native MAY is not an uncovered concrete pair. Removing a producer
is different from claiming that isolated `p.*` fact-subsumes `p.f.MAY`.

Keep the rest of the same application family. These are transfer predictions,
not new executions of the proposed redesign:

| Opposite input to S/L | S result | Additional L result before relation subsumption |
| --- | --- | --- |
| ret.MAY/T,D | p.MAY/T,D | p.f.MAY/T,D |
| ret.MUST/T,N | p.MUST/T,N | p.f.MUST/T,N |
| ret.$/T,N | p.$/T,N | None: exact root does not contain f |

The MAY/MUST prefix laws act on those output facts separately. R2 must also
check their effects on C2 and loop observations. Keep same-head and precise
descendant controls as well as the strict-ancestor STAR example.

## E02. Cases which the aligned law must reject

```java
Box removeF(Box p) { return p.f; }
// Valid relation: p.f.*/F -> ret.*/F,N.
// It is not covered by an identity p.* -> ret.*.

Box addF(Box p) {
    Box q = new Box(); q.f = p; return q;
}
// Valid relation: p.*/F -> ret.f.*/F,N.
// It is not covered by an identity either.
```

Keep these negative comparisons in B0, S1 and R2:

```text
short p.* -> q.* / E{f}; long p.f.* -> q.f.* / E{f}
    not covered merely because E is equal: p.f.g is excluded by short.
short output excludes T; long output admits T
    not covered.
different context, block entry, output port or direction
    not the same current relation owner.
only L exists, or candidate S failed paired C5
    no available S provider; keep L.
S exists only in saved records; L is current
    do not import S into a current owner silently.
```

The original S1 aligned-law domain has nonstatic, nonzero singleton FLOW STAR
endpoints, empty E and equal canonical mx. The review explicitly extends
that domain to legal statics, admitted nonempty E and mx subset coverage.
This extension includes the selected overlap-matching bridge; it is not
silently attributed to S1. See the unified spec §3 for its counterexamples.

## E03. Transitivity includes FLOW-backed concrete rows

```java
// One exact interface; assume these rows were admitted, T is not excluded.
Box copy(Box p) { return p; }
// A: p.*/F   -> ret.*/F,   N
// B: p.f.*/F -> ret.f.*/F, N
// C: p.f.*/T -> ret.f.*/T, D, H=false
```

A covers B. The existing diagonal FLOW law lets B cover C. S1 must therefore
let A cover C even after B is removed. Its transient specialized cover is
`p.f.* -> ret.f.*`; that view is not a new stored or published summary.

```text
offer C; offer A      -> C is removed from the final plain authority.
offer A; offer C      -> no retained C.
offer {A,B,C}         -> the same final plain basis.
offer C with H=true  -> plain A cannot cover C; a protected provider can do so
                       only through the same-flag coverage rule.
only C exists        -> do not synthesize A or B.
```

For partial marks, let both A and B have the same mx excluding U. They may
cover an unprotected T diagonal when T is admitted; they cannot cover a U
diagonal. If only the T part is covered, keep the other actual marks and
their flags. The implementation-time extension from equal mx to a subset
test is not part of the original S1 proof domain. It is now an explicit
reviewed extension, with a separate proof obligation.

Already queued work can finish once. The original design does not add
downstream retraction. Current publication, saved direct/reverse indexes and
handoff must use the final admitted basis. R2 must prove that basis plus its
new C2/C5 rules keeps the required next-run effects.

## E04. MAY/MUST coverage is not STAR coverage

```java
Box fork(Box p) {
    Box q = new Box();
    if (choose()) q = p;
    else q.f = p;
    return q;
}
// At one complete premise and owner, possible output families include:
//   {ret.MAY/T, ret.f.MAY/T},D       when p is an independent MAY value;
//   {ret.MUST/T, ret.f.MUST/T},N     when p is uniformly tainted.
```

These are typed state examples, not a claim that R2 emits a MAY premise.
MAY facts can still arise from cuts after R2 starts a STAR initial.

S1 canonicalizes each compatible same-tail family to its prefix. For MUST,
`q.MUST/E{f}` covers `q.g.MUST/E{h}` when g differs from f. It does not cover
a fact under excluded f. Equal-head E values union by E intersection.

Do not extend this to MUST-to-STAR, MUST-to-EXACT, different original premises,
different layers or a missing mark. R2 must distinguish ordinary DATA coverage
from positions used to select later initial facts.

## E05. Fill only a complete immediate child

```java
void fill(Box x) {
    taintAllT(x);       // Source rule: T at the position and all descendants.
    removeAll(x.f);    // Full-position cleaner at field f.
    taintAllT(x.f);
}
// At the shared ZERO origin:
// {x.MUST/T,E{f}; x.f.MUST/T,E{}} -> x.MUST/T,E{}.
```

Replacing the last source with a source at `x.f.g` is not a complete fill.
Neither is `x.f.MUST/E{h}`. A parent carrying T and U plus a complete T child
fills T only; U keeps E{f}. A FLOW child must supply the parent's whole allowed
mark complement. Do not enumerate all marks or weaken mx to force a fill.
The original S1 domain uses equal compatible mx for its simple FLOW fill.

## E06. Cold, warm, repeated and protected arrivals

Use the E04/E05 programs and one fixed complete coordinate cell.

```text
one packet {root, child}; child then root; root then child
    -> the selected canonical ordinary basis.
root/E{f}, then complete child f/E{}
    -> strengthen the parent and remove only proved redundant ordinary data.
same final packet again
    -> no fresh ordinary work.
plain coordinate, then same coordinate with H
    -> retain both; publish the fresh protected membership.
protected coordinate, then same coordinate without H
    -> retain both; publish the fresh plain membership.
repeat the same geometry and class
    -> no fresh work.
```

Apply canonicalization independently to plain and protected coverage. A
protected parent can remove a covered protected child; it cannot remove a
plain child. Exact plain/protected duplicates remain two memberships. No
discarded-fact archive or hidden plain certificate is used.

Let A be a MAY root and B its MAY child, with all other headers fixed:

```text
A plain; B plain; A protected -> retain A/plain and A/protected
A protected; A plain; B plain -> retain A/plain and A/protected
A protected; B plain          -> retain A/protected and B/plain
```

Each fresh class is published even when the other class already exists.
A pass carries both classes independently. Both producer and subscriber
therefore retain the same plain coverage in either arrival order. Queue
keys, caches and restore must preserve that distinction too.

## E07. Canonical input can remove a literal C2 initial

```java
// Forward restricted run-i, demand x.MAY/F.
// Submitted normal packet before canonicalization:
//   {x.MUST/F, x.f.MUST/F}.
Box use(Box x) { return x; }
// Raw-input C2 could select x.MUST/F plus x.f.STAR/F.
// S1 canonical-input C2 selects only x.MUST/F.
```

This is an explicit S1 change. Equal represented locations alone do not prove
that the discarded field-specific initial has no required observation or
handoff effect. R2 must show that required effects survive through the retained
uniform input and native summary application. It must not retain a hidden
discarded-leaf history to make the old literal sets equal.

R2's checked `GeneralLoopAdmissionBound` model constructs the retained root
MUST initial and identity in either arrival order. Application to a definite
uniform full-mark actual retains an arbitrary marked descendant and its sink
observation. An ordinary STAR actual is not accepted as a definite MUST input.
The result proves this identity program, not all programs from inclusion alone.

## E08. Reverse MUST overlap and typed native results

```java
// Forward run-i initial p.MUST/F,N.
Box cleanH(Box p) {
    removeAll(p.h);
    return p;
}
// Saved normal row: p.MUST/F -> ret.MUST/F,E{h},N.

// Backward run-(i+1): actual ret.STAR/F,E{g},N, g != h.
// Root ret is an overlap witness. Existing inverse result is p.MAY/F,D.
```

B0 can reject incomparable E. S1 admits that overlap while keeping the native
inverse result and layer. Excluded descendant paths remain excluded.

Keep the related cases separate: old concrete EXACT premise with a MUST
conclusion retains its native EXACT inverse result; old MUST premise retains
its existing MAY/DEMAND inverse. Only an old MUST **conclusion** grants the
new same-head overlap lane. A mixed packet can have both an old match and a
new overlap match. A plain view followed by the same protected view must
deliver the protection upgrade. Raw record identity is not an AP key.

R2's ban concerns emitted initials/premises. It must not relabel this legitimate
MAY inverse result as STAR without a separate correlation proof.

## E09. Direction is a match role, not an instruction direction

```java
// Hypothesis relation justified by the body:
Object readF(Box p) { return p.f; }
// Consider an incoming p.STAR/F,N above a deeper summary premise p.f.*.
```

S1 allows this strict-ancestor STAR contribution only for an opposite-direction
record. A current backward summary is still CURRENT. A saved record produced
in the active direction is SAVED_DIRECT. The selected scope includes concrete
STAR/T on DEMAND, not only FLOW. Same-head, actual-below-premise, MAY/MUST
matching and instruction field reads retain their separate rules.

The original complete-driver controls also include:

```java
void main() {
    Box early = sourceFG();       // Exact T at ret.f.g.
    Box late = sourceABCFG();     // Exact T at ret.a.b.c.f.g.
    sinkT(helper(early));
    sinkT(wrapper(late));
}
Object wrapper(Box w) { return helper(w.a.b.c); }
Object helper(Box p) { return p.f.g; }
// Variant: helper returns convert(p.f.g), CM(arg.$,T) assigns U to ret.$;
// both sinks then check U.
```

The original audit reports both findings through run-7 in its bounded native
controls. Those results do not prove the new joint C2/C5 contract universally.

## E10. Concrete STAR, rule assignment, cleaner and cycle protection

```java
// Already selected before the original proposal:
// initial p.STAR/T starts p.STAR/T,D, with its suffix correlation.
Object id(Object p) { return p; }
// It does not start an independent p.MAY/T result.
```

The frozen correlated spec preserves this in all runs. Keep these protection
cases from the FLOW-backed contract:

```java
Object dependent(Object p) { return new Object(); }
// Source rule: CM(p,T) assigns T to ret. The triggering conclusion has T.
// The assigned ret/T dependency is protected, regardless of original mark K.

Object cycle(Object p) { return convertBack(convertToU(p)); }
// CM(T) -> assign U, then CM(U) -> assign T.
// Restoring original T protects the result, locally and through summaries.

Object survivor(Object p) { removeSelectedT(p.f); return p; }
// A surviving selected-T result is an assign-back T dependency: protect it.
```

A complete cleaner kill emits no survivor. Ordinary field/call transport
preserves existing H. A protected summary conclusion protects its application.
Equal edges with the same flag deduplicate. Equal plain/protected edges
remain two memberships. Do not protect U because a packed leaf contains
protected T. Caller H must not contaminate a shared callee
initial or global static mark availability.

## E11. Later pass and exact-coordinate protection decisions

```java
Object pass(Object p) { return p; }
// PASS_THROUGH / CopyMark / CopyAllMarks: transport H; introduce no H.
```

The later selected rule requires both action role and rule kind to prevent
assignment classification for a pass. The new proposal must audit this on
the reset baseline. It must not silently assume the later fix is present.

At one premise and mark, an unprotected `q.MAY/T` and protected
`q.f.MAY/T` keep the protected child. If a protected parent is also present,
the protected coverage view can remove the covered protected child. Neither
flag class removes a member of the other. Keep and publish both exact
plain/protected duplicates. Apply the rule to NORMAL and
DEMAND and all effective tails. Mixed packet EXACT
leaves have Empty E even if their span wrapper has a different E.

## E12. The new C2 boundary cells and their negative controls

Use `Object id(Object p) { return p; }` as the transfer body. This table is
an admission specification, not an injected native demand snapshot.

| Demand Dc | Submitted fact | Required or existing initial |
| --- | --- | --- |
| p.MAY/M | p.MAY/M | R2 selected: p.STAR/M |
| p.MAY/M | p.STAR/M | R2 selected: p.STAR/M |
| p.MAY/T | p.$/T | Existing: p.$/T |
| p.MAY/F | p.MUST/T | Existing: p.MUST/F, forward only |
| p.MAY/M | p.f.g.$/T, eligible mark | Existing: stop at first field, p.f.STAR/M |
| p.MAY/T | p.f.$/T | Existing concrete exact exception: p.f.$/T |
| p.f.MAY/M | p.MAY/T, eligible mark | Old ANY output becomes p.f.STAR/M |
| p.f.MAY/M | p.STAR/T | Reject the ordinary STAR strict ancestor; no companion |
| p.f.EXACT/T | p.STAR/T,D | Reject; wait for a matching-head/deeper fact or an ANY/MUST actual |
| p.STAR/T, run-3+ | p.f.$/T | Keep the selected strict-descendant rejection |
| p.$/T | p.MAY/T,D | Existing provisional p.$/T,D; see E21/E23 |
| p.MAY/U | any fact with only T, U != T | Nothing |
| any compatible demand | wrong base or excluded required first step | Nothing |

On B0's correlated start policy, FLOW STAR starts NORMAL as a symbolic
relation. Concrete STAR starts STAR on DEMAND. R2 keeps this identity start
for the selected same-head STAR and ANY admission cells; see E25.
Concrete EXACT retains supplied DEMAND support; it does not become NORMAL
because its tail is exact. MUST admission remains forward-only. Keep static
named-field anchors and exact global class markers; no broad concrete class
or static-root taint is introduced. Do not add a companion FLOW initial for T.

The C5 image predicate must match these exact C2 outputs, including the
requested run-2 STAR and normalized EXACT/FLOW preimages. Self-emission alone
is not a complete image test.

## E13. Run-2 requested STAR keeps a sibling source

```java
void main() {
    sourceT(q.g);              // Exact T; f != g.
    Box r = m(q);
    sinkT(r.g);
}
// Run-1 initial p.STAR/F; raw source-backed caller input q.g.$/T.
Box m(Box p) {
    p.f = new Leaf();
    return p;
}
// Run-1 return: p.STAR/F -> ret.STAR/F,D; no NORMAL return cover.
// Run-2 demand: (ret.STAR/F,p.STAR/F).
// Submitted ret.g.$/T -> requested ret.STAR/F initial, NORMAL.
// Strong backward result: ret.STAR/F -> p.STAR/F,E{f},N.
// Run-3 saved opposite replay transports the actual g suffix and source T.
```

This existing native control completes run-3. A new emission policy must not
drop the special run-2 STAR merely because emitting the demand head from
itself gives a different exact initial. Keep the normal record's exclusion;
do not generalize it to an unconditional identity through the overwritten f.

## E14. Every summary uses a complete demand pair

```java
Object choose(Object p) { return p; }
// Restricted run-i, condition on an actually admitted p.f.$/T initial.
// Raw result ret.f.$/T,N must pass BOTH the same row's Dc and Dp.
```

Keep these C5 tests in the new proposal:

```text
Dc admits P, Dp absent                  -> no publication.
Dc admits P, Dp has wrong base/mark     -> no publication.
row1 admits P, only row2 admits C       -> do not form a mixed pair.
raw NORMAL C exceeds min(L,FL(Dp)+1)   -> cut the actual result to MAY/D.
unrestricted candidate S fails C5      -> S cannot subsume admitted L.
```

Two rows with the same Dc can have different Dp depths. For example,
`(p.MAY/T,ret.MAY/T)` gives output budget 1, while
`(p.MAY/T,ret.f.MAY/T)` can give budget 2 at a sufficient global limit.
Do not discard the second pair merely because its entry is identical.
An actual normal result `ret.f.g.$/T` can have different retained cuts under
these rows. ZERO/Target output checks use their typed endpoints, not an
invented field depth. No unrestricted raw-summary cache is required to
publish or persist a rejected candidate.

Store and publish only the restricted result. Keep actual NORMAL summaries
and saved-record application; do not bypass C5 for a new NORMAL candidate.
An ANY demand endpoint is not an ANY emitted premise. Preserve complete ND
premises and exact method/scope/port ownership during restriction.

## E15. EXACT FLOW normalization requires write and cleaner precision

```java
// Restricted raw initial p.$/F,N.
Box overwriteF(Box p) {
    p.f = new Leaf();
    return p;
}
// Raw NORMAL FLOW needs the f exclusion before public $ -> * normalization.
// A stored unconditional p.* -> ret.* would wrongly restore old p.f taint.
```

For a neutral `id`, the complete exact FLOW pair can normalize to STAR at
both endpoints. Preserve each endpoint's own field path; do not copy the
premise path to the return. Strong writes still update the required exclusion.

```java
Box cleanField(Box p) { removeAll(p.f); return p; }
// Legal full-position RemoveAll at p.f; preserve its real residual/exclusion.
```

A below-only RemoveAll which leaves just the root must not be normalized
into a NORMAL root-plus-descendants identity. The existing cleaner restriction
and its proof are not removed by the C2 redesign.

## E16. The original four-method loop finding

This later native example is not a measured B0 result. Its observed failure
before the SOA attempt reaches run-5. Its exact source/trace is in the
[loop-boundary report](../docs/reports/bidirectional-loop-boundary-normality-loss-20261106.md)
and [guidance-repair report](../docs/reports/bidirectional-concrete-guidance-repair-reproducer-20261106.md).

```java
void root() {
    Object s = sourceExactT();
    do { temp.g = s; next.f = temp; s = next; } while (again());
    Object mapped = mapper(s);
    sinkExactT(mapped.Element.h);
}
Object mapper(Object q) {
    if (choose()) out.Element.h = getG(getF(q));
    else { root1 = q; root2 = root1; out.Element.h = root2; }
    return out;
}
Object getF(Object q) { return q.f; }
Object getG(Object q) { return q.g; }
```

All objects and the Element slot are initialized. After one loop body,
`s.f.g` is the source object. No ND, static field or explicit alias path is
needed for this feasible finding.

The captured run-3 raw `ZERO -> s.f.g.$/T,N` is initially collapsed to
`s.f.MAY/T,D` in one historical trace. Later storage repair retains the fine
guide but still reaches a source-derived `arg.g.MAY/F` demand versus
`arg.g.STAR/F,N` input at getG, with no getter actor. Both historical cases
end run-5 without the required NORMAL report.

R2's `LoopMapperRecovery` derives the fine `s.f.g.EXACT/T,N` result from the
g/f writes and the adjacent `s.f.ANY/FLOW` demand from the real B2 getter.
The fine result has a depth2 initial command; no proper cut through ANY
additional query family with B2-bounded heads≤1 can reproduce it. The loop
gate therefore retains the fine observation. The checked wrapper pipeline
then derives source permission and the NORMAL mapper/sink result. This is a
scoped feasible-path proof. The unchanged one-finding native gate remains a
required implementation check; no new runtime completion is claimed.

## E17. Nested FLOW wrappers expose the output/input distinction

Captured later policies use FULL and limits `1,1,2,...`. Their latest run is
run-3. The [native report](../docs/reports/bidirectional-star-initial-nested-calls-20261107.md)
contains all four direct/wrapper cases and portable traces.

```java
void main() {
    Object s = sourceExactT(); temp.g = s; next.f = temp;
    Object x = getF(next);
    Object y = wrapG(x);             // Direct control calls getG(x).
    out.Element.h = y;
    sinkExactT(out.Element.h);
}
Object getF(Object p) { return p.f; }

// Run-2 old submitted/initial ret.MAY/F,D.
// Plain-output-only candidate initial ret.STAR/F,N.
Object wrapG(Object p) {
    Object tmp = getG(p);
    // Captured at the inner reverse call: tmp.MAY/F,D versus tmp.STAR/F,N.
    return tmp;
}
// Old backward DATA exit: ret.MAY/F -> arg.g.MAY/F,D.

// Run-2 Dc=ret.MAY/F, Dp=arg.STAR/F (pair derived from the captured R1 row).
// Bound input is ret.MAY/F,D versus ret.STAR/F,N, derived from ordinary bind.
Object getG(Object p) { return p.g; }
// Old policy enters. The output-only candidate has no getG processed rows.
```

The old policy reports all four programs. The plain-output-only candidate
reports the direct case and misses all three wrapped cases. Merely updating
the C2 output image does not admit the new STAR input. R2 selects that input
cell explicitly. A complete new-design result has not been measured here.

## E18. A concrete converter has the same wrapper gap

```java
Object convert(Object p) { return new InitializedContainer(); }
// Source rule: CM(p.MAY,T) assigns U exactly at ret.f.g.
Object wrap(Object p) { return convert(p); }
void main() {
    Object t = sourceExactT();
    Object r = wrap(t);             // Direct control calls convert(t).
    sinkExactU(r.f.g);
}
```

The rule is an actual native source transfer, not a predefined summary.
There is no ordinary p-to-ret FLOW route. Its run-1 target is cut at limit 1.
At the run-2 wrapped call, old processing has `tmp.f.MAY/U,D`; the output-only
candidate has `tmp.f.STAR/U,D`. The ordinary bind preserves that difference.
Only the latter misses convert and the finding. Both end run-3.

The selected new input cell must cover concrete STAR/DEMAND too. A FLOW-only
or NORMAL-only extension does not cover this example. Do not add a companion
FLOW source/converter or change CM's mark requirements to make it pass.

R2's checked `ConcreteConverterWrapper` uses the actual source/application
kernels. B2 starts `ret.f.STAR/U,D`, reverses the original T→U source action
and reaches the actual T source occurrence. F3's exact T input starts NORMAL;
the guard is satisfied, and the real source emits exact U at ret.f.g. The
complete paired C5 budget is 2, so this result stays NORMAL. Every finite
ordinary wrapper preserves that relation and the U sink witness. Wrong input
T/U marks reject. Source occurrence IDs/permission-store correspondence still
require the existing native callback adapter test. No FLOW provider is used.

## E19. Static carry needs its actual C2 family, without loops

```java
// Exact static source rule at C.g.h; f != g.
void main() { sourceT(C.g.h); clearF(); sinkT(C.g.h); }
void clearF() { C.f = null; }
```

Later native FULL traces reach run-3 and keep the expected-one-report gate
red. They establish two successive issues, not a B0 or new-design result:

```text
Run-1: ZERO -> C.g.MAY/T,D.
Run-2 actual call: C.g.MAY/T,D.
Original SOA attempt: raw C.g.S?/T -> C.g.S?/T,D reaches callee boundary.
Public C5 candidate: C.g.STAR/T -> C.g.STAR/T,D (source-derived then).
Old carry lookup rebuilt STAR/STAR guidance at the field cap and lost it.

After the separate C5 carry adapter:
Run-2 captured: STAR/T identity is admitted; physical source hit exists.
Run-3 captured: source emits C.g.h.$/T,N and offers it to clearF.
Current demand remains the precise C.g.STAR/T identity; no current callee
traversal or final finding follows. Do not reinterpret the identity as MAY.
```

The shallow same-field control reports once. An exact T source on `C.g`
must not taint child `C.g.h`; that negative control reports zero. Preserve
all three programs, the real source action and actual field write. The
static-carry adapter is not evidence that the later path has been repaired.

The completion candidate adds a complete named-field ANY/FLOW permission. The review also adds
an explicit FLOW companion when a primary concrete STAR/DEMAND is emitted. C2 starts its NORMAL
FLOW identity. The disjoint write preserves g, paired C5 admits the inferred
NORMAL g frame, and its later saved application transports the actual precise
T descendant. `StaticFlowCompletion` checks this route and the strong-same-field
and exact-parent negatives. It does not synthesize a frame or promote the T
identity. This is a conditional provider derivation, not a proof that the
complete new handoff needs or supplies that permission. No native rerun is claimed.

## E20. Two static loops: no FLOW cover, and ZERO does replay

```java
void main() {
    while (again1()) { a = sourceAtG(); Box.shared = a; }
    while (again2()) { b = get(); sinkExactT(b.g); }
}
Object get() { return Box.shared; }
// Source rule: exact T on sourceAtG's a.g result.
```

The [current evidence report](../docs/reports/bidirectional-concrete-static-flow-provider-20261107.md)
pins the 59-record native trace. Latest completion is run-3, no finding;
the unchanged one-finding assertion fails. No plain-STAR redesign was run.

```text
Run-2 L1 entry10/exit4 and repeat entry4/exit4:
    C.shared.STAR/T -> C.shared.STAR/T,D,H=false.
    No same-interface NORMAL FLOW provider exists.
Run-3 saved ZERO records actually replay prefix -> L1 -> AL1 -> root exit.
Run-3 C5 admits ZERO -> C.shared.g.$/T,N at L1 repeat exit4.
Growth restriction keeps it; the exact NORMAL value is offered at entry4.
The adjacent observer has one admission; its repeat observer has zero.
The later delivery C2 return list is not directly captured.
```

L1 is write-only with respect to statics. It has no activated static FLOW
read seed. In that captured version, run-2 concrete-only admission did not
invent FLOW. The review now adds an explicit companion for concrete STAR
primaries; that does not relabel the old capture. The getter's
FLOW row has another owner and relation. Implicit static carry is demand,
not an available executable NORMAL S-to-S summary. A universal normal static
identity is invalid through arbitrary strong writes.

The user explicitly says the precise T identity must not be refined. A
concrete selector must still admit only T. The latest decision requires
changes to initial/demand emission to infer the missing FLOW summaries.
The proposed repair is a separate explicit FLOW demand permission, followed
by real analysis. It does not assert a NORMAL provider or widen the T
identity. Actual saved ZERO replay is not the missing operation here.

R2's `TwoLoopHeaderFlow` model derives the NORMAL FLOW header at backward
10→4 from the query-local FLOW carry permission and actual no-write header.
Its saved opposite application is 4→10, not repeat4→4. The fixture's existing
weak static transfer also permits a separate repeat frame; the strong-write
negative kills that frame. The actual marked source/write/getter route reaches
the sink under that supplied permission. This is a scoped conditional model,
not a complete new-design handoff proof or a new native run.

## E21. Deep no-leave loop creates an exact Target obligation

**Latest diagnosis:** the
[saved-repeat report](subsumption-loop-saved-replay-root-cause-20261108.md)
isolates the run-5 loop gate. It omits saved repeat effects and can drop
the actual source before the saved-first repeat input handler. The existing
NORMAL `x.f.* -> x.*` reader can reach the exact-f demand and a NORMAL sink
Target without completion. The selected ZERO-premise bypass delivers that source result. Eight native
component tests check the old failure and the new test-only policy, ordinary
source/read/C5, saved replay, real sink evaluation and Target joins. They
are not a full native multi-iteration run of the redesign.

```java
// Source rule: exact T at x.f.f.f.f. All runs use the same physical source.
void deep(Node x) {
    while (true) {
        sourceFFFF(x);
        x = x.f;
        sinkExactT(x);
    }
}
```

The prior later native trace completes **run-5** without its required finding.
It is separate from the current run-3 two-loop trace. The captured guide chain
is below. `L` is the same loop block; its repeat entry is physical port 5.
The arrows in the handoff rows show the actual paired control selector, not
a newly executed transfer.

```text
Run-3 incoming scoped control: Data(x.f.$/T) -> ZERO.
Actual source/caller contribution: ZERO -> x.f.MAY/T,D.
Provisional raw initial/start: x.f.$/T,D.
Body read: x.$/T,D; the sink emits DemandTarget with exact original x.f.$/T.

Run-3 published Target: x.f.$/T -> DemandTarget.
Run-4 incoming handoff: Target -> Data(x.f.$/T).
    Captured: trace lines 63 and 15.

Run-4 published Target: x.f.f.*/T -> DemandTarget.
Run-5 incoming handoff: Target -> Data(x.f.f.*/T).
    Captured: trace lines 70 and 20.
Run-4 DATA: x.f.f.*/T -> ZERO,D, including repeat-to-repeat port 5.
Run-5 incoming handoff: ZERO -> Data(x.f.f.*/T).
    Captured: trace lines 68-69 and 18-19.

Run-5 repeat entry also has Data(x.f.$/T) -> ZERO.
Actual run-5 source-backed repeat result: ZERO -> x.f.f.f.$/T,N.
Saved NORMAL relation in this same repeat scope:
    x.f.*/F -> x.*/F.
    Captured: trace lines 18, 74-75 and 77.
Run-5 loop gate: observations=2, drops=2, trials=0, C2 rows=0.
    Captured: trace line 73.
```

Thus B4 did publish the growing `x.f.f.*` Target. Do not explain this failure
as rejection of all B4 growth by an exact paired output. F5 has both the
inherited exact DATA-entry selector and the newer STAR Target/output
selectors. It also has the saved shrinking NORMAL relation. The gate drops
both observed growing results before it obtains a local C2 row. A separate
read-only query after the run returns no initial for the exact actual
(trace line 76). That query is not a captured callback from the gate.

An isolated comparison between `x.f.$/T` and `x.f.f.f.$/T` predicts rejection
under the exact-entry rule. It is a source-derived hypothesis about one
lookup, not proof that this lookup alone causes the whole failure. R2 must
trace how all three paired guide routes and saved NORMAL replay interact.
Replacing ANY initials with STAR does not automatically alter the captured
EXACT original. Do not refine a precise STAR identity to MAY to force progress.
Changing provisional EXACT admission, Target projection or loop delivery is
a separate semantic choice. The Target-to-MAY counterfactual was cancelled
before execution; it proves no fix.

The [worked fact trace](../docs/reports/bidirectional-star-or-any-worked-fact-traces-20261107.md)
records the complete handoff explanation. The
[portable evidence package](../docs/reports/data/bidirectional-concrete-static-flow-provider-20261107.json)
embeds the prior Deep trace, its source and its receipt separately from the
current 59-record two-loop probe. Neither is a run of the proposed R2 design.

The [per-run BL/L/AL ledger](subsumption-e21-block-ledger-20261107.md) puts
demands and submitted facts above each block and emitted families below it.
It includes the FLOW rows omitted from the earlier three-row argument.
In particular, B2's FLOW DATA family can infer F3's NORMAL shrinker without
completion. A companion under a ZERO exit still publishes no DATA.

The [corrected run-4 trace](subsumption-loop-and-gap-audit-20261108.md#24-run-4-backward-field-limit-3-close-saved-replay-first)
includes saved-repeat delivery, which the older one-body catalogs did not
execute. It reaches `x.f.f.[any]/T,D` in the parent's completion store and
deduplicates the next identical result. That value is not automatically a
local summary. The corrected packet yields three local families and only
the precise NORMAL source image in run-5. The older five-family catalog
and shorter DEMAND image are transaction upper-bound cases, not proved
reached results. Their off/on gate theorems keep that conditional scope.
Entry/discovery/leave ports, enclosing publication and whole-program
stopping remain open.

The [run-2/run-3 fixed-point review](subsumption-loop-and-gap-audit-20261108.md#22-run-2-backward-field-limit-1-publication-replay-to-fixed-point)
also closes new publications against standing inputs and saved replay.
It reaches the coarse T input organically in run-2 and the shorter parent
point facts in run-3. The local publication families remain eight and five;
the paired handoffs remain seven and three. The old extra exact/T/DEMAND
run-2 initial is not produced by the reached MAY input.

## E22. Do not restore the OWASP demand cycle

```java
void main() { sinkT(helper(sourceAllT())); }
Object helper(Object p) {
    Object bytes = getBytes(p);
    return newString(bytes);
}
// sourceAllT: uniform T.
// getBytes has ordinary p -> bytes and storage-field p.H -> bytes flows.
// newString maps bytes back through the same storage routes.
```

The [native regression](../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/OwaspDemandCycleTest.kt)
models these field operations. An old cycle reopens coarse FLOW hypotheses
instead of using the actual uniform input to discharge the stored demand.
The existing regression requires a natural stop and the NORMAL sink, with no
policy iteration cap. It also includes E13's sibling-write positive.

R2's same-head ANY/STAR admission adds no new field in that one cell. In the
checked uniform producer family, every reversed B2 DATA entry
has depth≤1. C2, canonical getBytes/newString transfer and paired C5 produce
only in-budget NORMAL DATA at F3; real NORMAL FLOW removes the eligible plain
T/D arms before completion. The scoped family therefore has no next DATA
refinement demand. Native canonical-packet/driver correspondence must still be
checked. Finite per-run keys alone do not prove stopping, and no stable-count
stop rule is introduced.

## E23. EXACT DEMAND is provisional; Targets preserve the layer

```java
Object factory() { return sourceU(); }
void main(Box out) {
    Object x = factory();
    Box tmp = new Box(); tmp.b = x; out.a = tmp;
    sinkU(out.a.b);
}
// A saved NORMAL ZERO -> ret.$/U must replay in backward handling.
// Reverse source completion changes ZERO to Target as specified.
```

Also retain the conditional producer:

```java
Object make(Object p, Object q) { return new Object(); }
// CM(p,T1) AND CM(q,T2) assigns U to ret.$.
// A good call supplies both; a bad call supplies only p/T1.
```

A multi-origin run-1 approximation can require an exact DEMAND result. Do
not force it to NORMAL merely because U is a full mark. A concrete exact
demand may be answered provisionally from submitted MAY, but its initial
and derived sink witness remain DEMAND. Emit DemandTarget, not NormalTarget.
Complete later ND joins must still require all premises. ZERO is an origin
only when one complete cube has all-ZERO support.

NormalTarget is composed with NORMAL inputs only, ignored backward, and not
re-emitted when the corresponding normal terminal is already persisted.
DemandTarget has no report ID and still counts as refinement demand. Every
typed DATA/Target/ZERO intersection must remain paired; admitting one control
endpoint does not authorize arbitrary DATA at the other endpoint.

E21 shows why local provisional-exact soundness does not by itself prove
that later source/refinement guidance is complete. This remains a required
joint C2/C5/Target proof obligation.

## E24. Availability, liveness, aliases and owner boundaries

```java
Object id(Object p) { return p; }
void main() {
    Object t = sourceExactT();
    sinkT(id(t));
}
// When id has a persisted NORMAL FLOW provider, replay it before checking
// whether id has current demand. An empty current demand does not erase it.
```

The same policy applies to local blocks. E20 captures its ZERO lane executing.
A native source or sink cannot be skipped merely because a raw fact set was
canonicalized; show the surviving normal-record or demand-guided route.

```java
while (again()) {
    Object tmp = x;       // Overwritten before any use on the next iteration.
    use(tmp);
}
use(x);
```

Drop the dead `tmp` conclusion at the appropriate block boundary before
summary publication or demand checking. Do not drop a truly loop-carried
local which is read before redefinition on the repeat edge. Keep physical
ports and all method registers; no generated method or new alias scope is
implied. Identity-only alias candidates use the established input-alias
closure rule, not a new identity guard on FLOW subsumption.

## E25. The selected initial starts with a STAR identity

The original AP start operation and the later correlated extension must not
be combined silently. The pinned correlated spec explicitly changed the
older concrete start; B0 at 528 already has that extension. The user now
requires R2 to retain a STAR identity start. An independent MAY start is not
an open implementation choice.

| Policy | Initial key | Start conclusion and layer |
| --- | --- | --- |
| Historical unextended AP §6.5 | a.STAR/T | a.MAY/T,D |
| B0 correlated extension, all runs | a.STAR/T | a.STAR/T,D |
| B0 abstract FLOW | a.STAR/F | a.STAR/F,N |
| Selected R2, accepted same-head STAR or ANY input | a.STAR/T | a.STAR/T,D |
| Rejected R2 independent-start alternative | a.STAR/T | a.MAY/T,D |

The rejected alternative would satisfy the ban on ANY emitted keys/premises
without a new tail, but it would change the start transfer. It is kept here
to make the semantic distinction clear. Do not implement it in restricted
runs or use it to claim recovery of a failed case.

```java
// Restricted run-i, concrete Dc=a.MAY/T; submitted a.MAY/T,D.
// Selected key and start: a.STAR/T -> a.STAR/T,D.
Object id(Object a) {
    return a;
}
// Selected R2 transfer prediction, before paired C5:
//   a.STAR/T -> ret.STAR/T,D.
// Rejected counterfactual, not an R2 result:
//   a.STAR/T -> ret.MAY/T,D.
```

The selected initial is also an identity when the accepted submitted input
is `a.STAR/T`. A genuinely precise STAR-to-STAR identity stays precise; it
does not acquire a MAY handoff selector merely to allow a deeper fact. This
decision alone does not prove that every missed path recovers.

FLOW, EXACT and MUST start cases, request answers in run-1, and the concrete
layer/support tests are not silently changed. FLOW STAR keeps its symbolic
NORMAL identity start. E21's provisional EXACT key is not a concrete STAR
key, so the selected STAR start does not settle its Target gap.

The combined proposal must trace the selected identity through E16–E23,
paired C5, source permissions, normal-record reuse and natural stopping. The
old AP seed rule is context for the rejected alternative, not a proof or a
repair for the current loop and Target machinery.

## E26. Static setter, getter and consumer need marked guidance

```java
void main() { set(); wrap(); }
void set() { C.f = sourceExactT(); }
void wrap() { wrapDeep(); }
void wrapDeep() {
    Object t = get();
    sinkExactT(t);                  // t is dead at return.
}
Object get() { return C.f; }
```

This is a contract example and a native regression family, not a new B0
execution. See the
[static erasure spec](run1-static-summary-erasure.md),
[static completion contract](restricted-demand-static-closure.md), and
[StaticTargetRefinementTraceTest](../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/StaticTargetRefinementTraceTest.kt).
The test source is a regression destination; its presence is not a fresh
result for the new proposal.

```text
Run-1: set and its ordinary caller route retain ZERO -> C.f/T,D.
       The getter has the C.f -> return reader relation.
       A canonical concrete C.f.STAR/T hypothesis is DEMAND, not a source.
       wrapDeep can retain C.f/T -> DemandTarget although local t is dead.
       It need not have a DATA return summary with C.f premise.
Handoff: compose the genuine ZERO writer with the static reader/terminal.
         The root needs the complete pair (Target,ZERO).
Run-2: backward ZERO/Target routing must retain the T requirement through
       getter and setter and reach the actual source occurrence.
Later forward: the same source permission and real static DATA flow must
               reach the sink; only a NORMAL ZERO -> NormalTarget reports.
```

Keep the marked requirement. A FLOW-only guide is not permission to emit an
arbitrary T edge in run-2. A nonzero writer `arg -> C.f` is not a ZERO writer
and cannot manufacture `(Target,ZERO)`. A caller with no relevant current
demand still replays an actually persisted NORMAL summary first.

Run-1 does not propagate static-to-static summaries through all callers.
Its completed static composition is a handoff concern. Later runs require
actual matching static premises; ZERO does not satisfy them. Keep the
normal-exit rule path and immediate write-point pool supply separate.

## E27. Do not promote a DEMAND row to NORMAL from its shape

**8 November correction:** this program is an abstract rule-language control,
not a native guarded-pass counterexample. At the selected baseline,
`JIRCallPlanBuilder.passRules()` diagnoses a remaining mark condition and
applies the pass without it. `JIRRuleForms.pass()` emits an unconditional
copy. The serialized type alone does not prove the shown runtime semantics.
The [gap audit](subsumption-loop-and-gap-audit-20261108.md#42-e27-is-not-a-native-guarded-pass-counterexample)
records this correction. No compiler behavior is changed.

The absence of protection is not proof that a transfer is NORMAL. The
serialized rule type permits a condition on a pass rule; see
[SerializedRule.PassThrough](../core/opentaint-configuration-rules/configuration-rules-jvm/src/main/kotlin/org/opentaint/dataflow/configuration/jvm/serialized/SerializedRule.kt).
A pass rule cannot create H, even when its guard is approximate.

```java
// Rules for guardedCopy:
//   CM(arg0.f, T) -> Pass(arg0, ret).
//   Copy T and its correlated field path only when the guard holds.
// The returned object is otherwise clean; f != g.
Box guardedCopy(Box p) { return new Box(); }

void main() {
    Box p = new Box();
    sourceExactT(p.g);
    Box r = guardedCopy(p);
    sinkExactT(r.g);
}
// Concrete rule semantics: CM(p.f,T) is false. There is no T at r.g.
```

The required operational trace has these separate parts:

```text
Hypothetical coarse analysis input: p.STAR/T -> p.STAR/T,D.
If that approximation satisfies CM(p.f,T), the pass result can have:
    p.STAR/T -> ret.STAR/T,D,H=false.
    Pass has not made the row NORMAL and has not added H.

Actual caller input: p.g.$/T,N. The concrete guard still fails.
Incorrect repair: promote the unprotected STAR/STAR row to NORMAL.
That NORMAL identity transports p.g.$/T,N to ret.g.$/T,N.
The sink then gets a false NORMAL witness and a false NormalTarget.
```

This is a rule-semantics counterexample to blanket promotion. It is **not a
captured native execution** of that coarse guard. The native compiler does
not implement this guarded pass, so this fixture cannot supply native
evidence against a repair. The independent abstract
concrete fact remains: an unconditional NORMAL identity is not justified by
a conditional pass whose guard can be false.

Thus neither `H=false` nor equal STAR endpoints establishes a NORMAL FLOW
or concrete provider. Do not invent a NORMAL default or upgrade a DEMAND
identity to repair E19–E21. Such a change needs its own actual-input and
reporting proof, including the actual source/cleaner kernels. E31 supplies a
legal selected-cleaner continuation counterexample without a guarded pass.

## E28. Run-1 identity already handles the cross-base transfer

```java
// Run-1 submitted: actual p.g.EXACT/T; ordinary abstraction starts p.*/FLOW.
Object id(Object p) {
    return p;
}
// Produced and saved: p.*/FLOW -> ret.*/FLOW, NORMAL.

// Later run-i: submitted p.g.EXACT/T,N.
// Saved-first application: ret.g.EXACT/T,N.
// A current precise p.STAR/T demand can reject the deeper input;
// that rejection does not suppress the earlier saved result.
```

The earlier example assumed this ordinary `id` had no saved DATA provider.
That artificial interface assumption is not a trace of the program. Run-1
already supplies the provider. E28 therefore does not justify completion.

Keep the paired C5 rule separately: `(p.ANY/FLOW,p.ANY/FLOW)` and
`(ret.ANY/FLOW,ret.ANY/FLOW)` cannot be mixed to publish p-to-ret. The archived
local model checks that algebraic limit; it does not prove a reachable
missing-provider state for `id`. A method which clears p and returns a clean
object must still infer no p-to-ret provider.

## E29. Conductor: a covered location set can lose a refinement head

Read-only evidence review, 7 November 2026. No new run was launched. This is
a required real-project example for the unified redesign. The exact local
guidance/admission defect is observed; its complete necessity for the two
missing findings is not proved.

The [small code example and inline fact trace](conductor-must-admission-fact-trace-20261108.md)
show how root ANY demand removes a MUST-selecting child head. They include
run-1/run-2 demand generation and run-3 admission, with latest-spec versus
historical-runtime evidence kept separate.

The small trace continues through run-4/run-5. It derives the NORMAL
read and regenerated child demand rather than assuming either. Both routes
can give the small example its NORMAL witness in run-5. A separate DEMAND
return remains possible; no latest whole-driver stop or Conductor recovery
claim follows from this local result.

### Required identities and saved routes

Both identities use rule `java.security.graaljs-polyglot-code-injection`.

| Sink method | Exact saved sink | Fingerprint |
| --- | --- | --- |
| `com.netflix.conductor.core.execution.evaluators.PythonEvaluator#evaluate(java.lang.String, java.lang.Object)` | IR58, `context.eval("python", wrappedExpression.toString())`; `PythonEvaluator.java:63` | `8rLVjoe1V3DqzuJubn3Pc1RsFnegW1yHtQ/fuKX0gXQ=` |
| `com.netflix.conductor.core.events.ScriptEvaluator#getSource(java.lang.String)` | IR12, `Source.newBuilder("js", script, "inline")`; `ScriptEvaluator.java:253` | `EzmrpG1FD3CwGwVTQXyOH0FmoHson/4xsYBeDYPJbF8=` |

The saved Python witness starts at `WorkflowResource.testWorkflow` line 444,
through `WorkflowTestService` and `WorkflowServiceImpl.startWorkflow`. The
saved Script witness starts at `WorkflowResource.rerun` line 311, through
rerun task input and `tasks.StartWorkflow`. Both reach
`WorkflowExecutorOps.startWorkflow(StartWorkflowInput)` and the workflow
definition/model path. These are historical saved witness routes, not a new
executed first-loss trace.

```java
// Abbreviated source path, with separate expression and task-input fields.
workflow = createWorkflowModel(input, workflowDefinition, id);
createAndEvaluate(workflow);                  // actual diagnostic call 9
  createAndEvaluateWithLock(workflow);
    decide(workflow);
      decider.startWorkflow(workflow);
        task = workflow.workflowDefinition.tasks.get(0);
        getTasksToBeScheduled(workflow, task, 0);
          mapper.getMappedTasks(context);
            evaluator.evaluate(task.expression, context.taskInput);
```

Python also appends task-input map keys into its code text. The Script route
uses GraalJSEvaluator and forwards expression to ScriptEvaluator. A
taskDefinition field is a sibling, not an expression value. The pinned source
audit has 37 exact snippets and 20 matched historical source pins.

### Historical report and control ledger

R/C/A means latest **reached/completed/accepted** iteration. It is not a claim
of natural convergence or a measurement of the proposed redesign.

| Runtime or diagnostic | R/C/A | Result and qualification |
| --- | --- | --- |
| Main 8331 canonical implementation | 15/14/13 | Accepted strict report has five rather than seven identities; both exact keys above absent. |
| Same-point-only rollback A over 8331 | 6/5/5 | Both missing native R5 sink-signature report projections still absent. |
| Proper-prefix-only rollback B over 8331 | 6/5/5 | Both native R5 report projections recover. This changes one `canonicalSpans` expression; not a strict new SARIF acceptance or performance result. |
| Exact Current/B demand snapshot over production 8331 | 4/3/3 each | One complete event per side; 77 versus 175 paired local rows, 2 versus 3 initials, no drop/cap/error. |
| Later selected storage runtime 7069 | 4/3/3 | Accepted strict report has all seven exact reference identities. Backward run 4 times out; convergence is not established. |

Proper-prefix-off is a sufficient isolated intervention for the historical
native report projection recovery. It also changes NORMAL actual packet
normalization, so it is broader than a guidance-only repair. Later 7069
recovers the strict identities but contains the selected storage changes;
that campaign does not prove which individual transition is necessary for
either finding. These facts must not be relabelled as a full native causal
lineage for the particular query below.

### Exact local missing coordinate and initializer

Let `T` be the full atom
`java/security/graaljs-polyglot-code-injection.yaml:graaljs-polyglot-code-injection#spring-source;0;$UNTRUSTED;2`.
Let `wfDef` be the full typed field
`WorkflowModel.workflowDefinition:WorkflowDef`.

The equal F3 query is Ops `startWorkflow` to Ops `createAndEvaluate`, Empty
context, physical call 9, stage 3, ROOT scope `(0,-1)`, global limit 2:

```text
Actual in BOTH: arg0.wfDef.MUST/T, NORMAL, E={}, H=null.
Native DAG: empty root -> typed wfDef field -> uniform T leaf; no exact T.

Current row15: arg0.ANY/FLOW -> this.taskStatusListener.ANY/FLOW.
B row0:       the same root pair.
B row16:      arg0.wfDef.ANY/FLOW -> the SAME taskStatusListener exit.
Current complete local list has no wfDef.ANY/FLOW entry.

Current initials: wfDef.STAR/FLOW,N + wfDef.STAR/T,D.
B initials:       those same two + wfDef.MUST/FLOW,N.
```

This snapshot is the complete explicit local DATA/ZERO projection. Static
completion/shared carry are absent; Target-entry rows are omitted by the API
and cannot match this nonzero DATA query. It is not a global callee census.

The query digest is
`2d4642a06869395d21b1a14a86f54d47f4eeede366566207f111787138675a6e`.
The unchanged emitter's root ANY rule advances one field and emits STAR;
the child ANY rule is at the actual MUST head and can preserve MUST. The
snapshot observes the complete demand lists and actual returned lists, but
does not log which individual row produced each initializer.

B later uses initializer ID 4784 as the original ROOT premise in an actual
call to `createAndEvaluateWithLock` (sequence 1403, raw JSONL line 1414).
This is a same-JVM positive identity association, not unique event lineage.

The raw snapshot records are at JSONL line 2 in the two
`conductor-must-demand-snapshot-*-20261106T110322460795Z` attempts. Exact
records, typed catalogs, unchanged C2 code and controls are already embedded
in the repository's snapshot JSON. The companion evidence index records
their exact byte hashes, JSON pointers and all source package hashes.

### What the redesign must prove

Completion starts from final retained endpoint heads. Applied only to the
displayed Current root-to-listener pair, it adds root and listener-prefix
FLOW self-pairs and a paired root-to-listener erasure. It does **not** recreate
the missing `arg0.wfDef.ANY` coordinate. The proposed root ANY C2 rule still
returns wfDef.STAR/FLOW,N for this deeper MUST actual; that initializer was
already present in Current. Merely adding a FLOW duplicate is not this
example's recovery proof.

A possible different route is to infer a genuine NORMAL root/field transport
under a new explicit FLOW self-permission and the new STAR/NORMAL identity
start in B2. Its actual saved-first application might preserve the source
MUST packet before F3 current admission. That is an obligation, not an
installed provider: show the real ordinary body transfer, C5 pair, aliases,
owner/ports, publication and application. The full original P and actual
T/E/H/support must remain. No discarded child coordinate may be reused as
an endpoint, and no unconditional NORMAL frame may be invented.

Acceptance requires both exact Graal identities and their negative controls,
plus a real route through the selected canonical basis. Existing local
MUST-versus-STAR repros show a refinement delay, not necessity for these final
Conductor findings. No new performance, complete-program proof or redesign
runtime result is claimed by E29.

Required validation sources: [exact frozen snapshot](../docs/reports/bidirectional-conductor-must-demand-snapshot-20261106.md), [upstream admission](../docs/reports/bidirectional-conductor-upstream-admission-20261106.md), [quality/control investigation](../docs/reports/bidirectional-conductor-canonical-quality-regression-20261105.md), and [uniform small reproducer](../docs/reports/bidirectional-uniform-prefix-refinement-reproducer-20261106.md).
The snapshot [portable JSON](../docs/reports/data/bidirectional-conductor-must-demand-snapshot-20261106.json) embeds the complete paired rows and actuals. The [E29 evidence index](lean/proposals/subsumption-initial-demand-20261107/conductor-e29-evidence-index.json) pins the existing artifacts; it is not another analyzer run.

## E30. Rejecting an ancestor STAR conclusion can remove a needed return route

The [descendant-intersection review](descendant-intersection-and-flow-completion-review-20261107.md)
gives the full source/sink rules and run-1 through run-5 trace:

```java
void main() {
    Node b = new Node();
    b.f = new Node(); b.f.f = new Node(); b.f.f.f = new Node();
    sourceFFF(b);             // Assign exact T at b.f.f.f.
    Node r = getFF(b);
    sinkT(r.f);
}
Node getFF(Node p) { return p.f.f; }
```

Run-1 has a NORMAL unchanged-argument summary, but no NORMAL return
provider. In run-3 the real Flow start `p.f.f.*` gives `ret.*`, NORMAL.
Its paired output demand is `ret.f.*`. Rejecting the ancestor STAR removes
that return; preserving the argument p does not supply ret. An extra
completion-derived analysis can instead infer a DEMAND return bridge.

`GetFFC5Policy` checks all argument/return candidates in this finite helper
model, real source/sink actions and the three policy comparisons. Caller
ZERO/Target scheduling and dead-local projection are native adapters. The
latest modeled report is run-5; no native result or natural-stop claim for
completion is inferred from it.

The follow-up `GetFFCoarseFlowRun2` confirms that current run-2 starts only
`ret.f.*`, never `ret.*`. An additional coarse FLOW start would infer
`ret.* -> p.f.ANY,D`; its reversed root-ret demand admits the NORMAL run-3
return even under STAR rejection. This is a counterfactual admission change,
not a current command. E30 therefore does not force the STAR output rule if
initial admission is redesigned at the same time.

The selected version emits raw `ret.$/FLOW,N` as an additional prefix
identity after successful ANY-demand descendant admission. Its run-2 result
normalizes to that coarse STAR summary at the complete FLOW boundary.
`GetFFExactFlowPrefix` checks this actual emitter, preserves the fine primary
and recovers the modeled run-5 NORMAL finding without completion. The raw
EXACT prefix remains a read barrier; this does not change field processing.

## E31. A direct exact-root selected cleaner blocks a precise child

The complete [code and per-run trace](subsumption-loop-and-gap-audit-20261108.md#3-a-separate-counterexample-direct-exact-root-selected-cleaning)
uses a source at `p.g.$/T`, `m(p){ RemoveMark(p,T,Exact); return p; }`, and
an exact sink at `ret.g`. The source is already in budget in run-1.
The root-only cleaner does not clean the concrete child g.

Run-1 answers its T request with root STAR/T,D. Its surviving concrete rows
are protected; its NORMAL FLOW argument/return rows all exclude T. Run-2
starts requested STAR and preserves a protected STAR/T demand. In run-3
that STAR selector rejects the real exact g input. Saved NORMAL replay has
no T transport. Optional completion starts extra FLOW probes, including
the latest exact prefix, but the same cleaner makes all of them exclude T.

`RootExactCleanerGap` computes this finite phase catalog with the actual
cleaner/AP operators, paired C5, source permission and saved replay. It
establishes the missing run-3 continuation with completion off/on. Native
root, Target, storage and stopping correspondence remain open. The selected repair below changes only the partial selected STAR survivor;
initial admission stays unchanged.

The selected [STAR-to-ANY cleaner rule](subsumption-loop-and-gap-audit-20261108.md#34-selected-change-a-partial-start-survivor-to-anyt)
keeps the STAR premise, DEMAND layer and H. Its finer run-2 NORMAL result
restores this example in run-3 through saved replay. The original candidate
model checks that local route. The selected generic rule also checks PART
provenance, the selected mark, Empty E, unchanged other results and retained H.
The native integration and whole-driver stopping checks remain required.

## Closing ledger: design and validation

| Area | Selected route | Proof or validation boundary |
| --- | --- | --- |
| C2 and C5 entry | One relative-input image; no ANY initial; ordinary STAR identity; same-head ANY/STAR accepted | 47-law image plus 30-law legal FLOW EXACT/E bridge; static/group adapters require native checks |
| Precise STAR | Keep mark-specific primary admission, explicit STAR/FLOW companions and later strict-descendant rejection | E19/E20 provider routes are conditional on the supplied FLOW view; full handoff validation remains required |
| Deep Target | Keep exact Target geometry; ZERO-premise summaries bypass only the extra loop gate | Checked run-5 source/read/sink route and native component tests; full ports/root and stopping remain open |
| Ordinary wrappers | Admit both FLOW and concrete STAR under same-head ANY | Loop-free wrapper derivation and concrete source/action route; no implicit FLOW converter |
| Canonicalization | Canonical input only; same-flag coverage; retain both exact plain/protected memberships | Separate-class publication and pass checks; native packed-store integration remains required |
| Transitivity | A directly covers C through a computed B view | Equal-mx aligned domain, both arrival orders, no stored/published B; H is retained |
| FLOW demand completion | Not selected | Historical comparison only; no new selectors are added by this revision |
| Layers and sources | Conditional hypotheses do not upgrade actual support; selected PART STAR/T becomes ANY/T,DEMAND,H | E31 recovers the local run-3 NORMAL result through precise saved replay; no NORMAL promotion |
| Stopping | Stop when inferred outgoing refinement demand is empty | Scoped E22 no-D family; arbitrary Java and whole-driver convergence are not claimed |

E29 is a mandatory real-project implementation acceptance check. The new companion alone
returns a FLOW STAR command which Current already had; root-prefix completion
alone does not reconstruct the missing wfDef head. The small example now derives a saved NORMAL route and regenerated child
demand in run-4, with NORMAL transport in run-5. The actual project must
still pass its exact report checks. Do not label the full project fixed by
the smaller example, or label its local delay a new permanent-FN proof.

The combined spec defines each selected change and its unchanged mechanisms.
The proof package states the exact domains of its theorems. Implement from
528, not the withdrawn SOA prototype. Before implementation acceptance, run
all strict principal assertions and negative controls in the native engine,
including cold/warm/one-packet and both arrival orders. The historical run-3
and run-5 failures remain in this catalog; a scoped Lean route is not a new
runtime measurement or project quality result.
