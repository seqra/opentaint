# Consolidated demand-termination counterexamples

Updated 17 November 2026. Synthetic data-flow reachability investigation, 13–17 November.
[Consolidated design history](../design/bidirectional-demand-termination-approach-20261115.md).
[Reference verification and natural stops](bidirectional-termination-fix-validation-20261117.md).
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.

The [active spec](../../spec/demand-refinement-and-termination.md) defines
the selected rules. Results that use R37–R40 belong to the
[candidate Target-retirement spec](../../spec/demand-target-retirement.md).

**Current search result.** A reader that reads before and after recursion
admits a recurrent clean return cone while R39 cannot certify the entire
slice. R40 **[REC]** proves its complete nested language disjoint from
the regular writer language. The baseline diagnostic reaches
**run-9/POLICY** and the adapter reaches **natural run-5**.
The positive that requires the nested arm retains its NORMAL relation at
**natural run-5**. No further example was established in **882** certificate
comparisons and **72** cold programs, with natural completion through
**run-11**. The two-sided writer pilot has a reference/native alignment
difference and is not classified as a native repeat. [Traces and checked scope](bidirectional-two-sided-field-search-20261117.md).

**Earlier field-pattern result:** the recursive writer/read case has a scoped
uncapped ZERO/DT recurrence. All writer paths end in f; all complete reader
paths end in g. Cuts and independent MAY results hide the mismatch.
**R39 [REC] [LOOP]** adds a complete regular field-path NoRoute certificate
without changing AP propagation. Native ordinary-code diagnostics reach
**run-9/POLICY**; the repaired reference/adapter stop naturally at **run-5**.
Positive controls keep their NORMAL observation and natural run-7.
Two-loop and mutual controls preserve earlier natural run-5/run-3 stops.
**170 native tests pass; 65 new constructive claims, 7,468 cumulative in
445 hash-pinned modules.** Fresh scope: 9,704 grammar pairs, 32 cold paired
programs and the long shared-word reference (natural **run-13**).
No further termination/comparative loss is found in those explicit families.
A separate existing native long-word miss is recorded: baseline and adapter
both naturally stop at run-5 without it; no R39 rewrite occurs. The reference
retains it at run-13. G1–G4 and unsupported cases remain open; no universal
termination/soundness claim is made. Production is unchanged.
[Code, all principal run traces, proof scope and limits](bidirectional-branching-field-termination-20261117.md).

**Earlier source-specific four-phase result:** the new source-specific audit finds and repairs
an R37 loss. One report ID can hide a second marking point. Report-only
retirement naturally stops the flat case at **run-3** without the relation
that the baseline reaches at **run-5**. **R38 [REC] [LOOP]** requires complete
possible-origin accounting and a valid NORMAL route for every possible
marking point. The repair keeps natural **run-5**, preserves the actual
hierarchical loop routes at **run-13** and **run-17** (nested), and serves
two recursive marking origins before natural **run-9**. The earlier single-origin recursive case
keeps natural **run-7**. [Full counterexample, per-run traces and repair](bidirectional-mark-origin-service-soundness-20261117.md).
**143 targeted native tests pass; 43 new constructive claims, 7,403
cumulative in 436 hash-pinned modules.** A fresh 7,686-case search has no
further termination or source-specific mismatch in its stated scope;
reference natural completion reaches **run-9**. The native recursive
diagnostic remains **run-15/POLICY**. No known open case remains in these
explicitly checked families. Unsupported upper/lower adapters and G1–G4
remain open; universal termination/soundness is not claimed.
The older summaries below are historical scoped results. R38 supersedes
R37's report-ID-only service predicate.

**Historical recursion campaign (K superseded by R38):** a recursive wrapper has a proved recurring
root Target even after its NORMAL observation at run-3. R37 **[REC]** uses
one terminal-only unconfirmed-origin bit and omits only a certified covered
forward root ZERO/DT handoff row. The repaired reference/native handoff
adapter stop naturally at **run-7**. The unchanged diagnostic reaches
**run-15/POLICY**; mutual native controls retain an earlier natural run-5.
The fresh 11,340-case direct/mutual search finds no further example, with
natural completion through **run-13**. **123 native tests pass; 52 new
constructive claims, 7,360 cumulative in 431 checked modules.**
[Trace, rule, proofs, costs and scope](bidirectional-recursive-target-termination-20261117.md).
No known open termination counterexample remains in the explicitly checked
scopes. General whole-analyzer soundness and termination remain unproved.

**Earlier cleaner campaign:** two new Target recurrences have constructive
uncapped proofs. The selected EXACT cleaner below a uniform mark is repaired
by R35 (natural **run-1**); nested ALL/BELOW cleaning is repaired by R36
(natural **run-3**). Their unchanged native diagnostics reach
**run-15/POLICY**. A fresh 2,551,500-case search has no further example;
natural completion reaches **run-5**. **111 targeted native tests pass;
7,308 cumulative constructive claims in 427 checked modules.**
No known open termination counterexample remains in the stated checked
scopes. This is not a universal termination or whole-analyzer soundness proof.
[Full traces, repairs and limitations](bidirectional-cleaner-termination-campaign-20261117.md).

**Soundness status:** the earlier case 165 and its reduced one-call prefix
example are repaired in the proposal by
[possible DIRECT saved replay](../design/bidirectional-saved-direct-possible-replay-20261117.md).
The reference retains its NORMAL observation and empties demand at **run-5**.
Six native components check the repair; the unchanged production driver
still loses the broad observation at run-5. The updated 884 control is
unchanged. These are soundness controls, not termination refutations.
General whole-analyzer proof obligations remain open.

**Further investigation:** no additional soundness counterexample was
found in the [13,604-configuration post-DIRECT check](bidirectional-post-direct-soundness-audit-20261117.md).
The new reference scope completes naturally through **run-11**. Nine new
native cold controls complete through **run-9**; the combined suite passes
92 tests. These finite checks add no analyzer rule and do not close G1–G4.

**Termination status: no known open termination counterexample in the checked scope.**
The [nested overwrite soundness counterexample](bidirectional-nested-star-soundness-gap-20261117.md)
is repaired in the proposal by the
[run-2 same-head STAR relay](../design/bidirectional-run2-star-relay-20261117.md).
The reference and cold native adapter retain the NORMAL observation and
stop naturally at **run-3**. The old rejection control still loses it at
run-3. It is a soundness regression control, not a termination counterexample.
General audit obligations remain open.

The [next handoff-mask audit](bidirectional-post-run2-soundness-audit-20261117.md)
rules out another candidate by applying the existing F72 Empty-mx demand
projection. Its native controls preserve U and reject the exact cleaned T
at **run-3**. The latest 1,536-case conditional-marking sweep finds no new
counterexample in its scope: natural completion through **run-13**,
diagnostic scan through run-25. Earlier alignment issues below remain open.

The later soundness audit found a cleaner/getter admission loss outside the
no-cleaner search scope. The [disjoint-FLOW repair](../design/bidirectional-disjoint-cleaner-flow-20261117.md)
closes it in the proposal: NORMAL observation and natural completion at
**run-3**. Its original native cold diagnostic still loses the observation
at run-3 because production is unchanged. This is a soundness regression
control, not a new termination counterexample.

The [native-bound service repair](../design/bidirectional-native-bound-reply-service-20261117.md)
closes the protected caller-input cycle. The reference naturally stops at
**run-7**, with its NORMAL observation retained from **run-5**. The
uniform-input control naturally stops at **run-9**, retaining its observation
from **run-7**. Five earlier service references keep their **run-5** stops.
[Complete updated traces](bidirectional-native-bound-reply-service-trace-20261117.md).

The next search checked 252 explicit reference configurations, including
216 ordinary source-program variants and 36 packet/exclusion controls.
All reach an empty forward frontier by **run-9**; their observations match
the unbounded concrete reference. This finite family does not prove
termination for every acyclic program. The table below retains all earlier
examples and their proof scopes, including excluded special-pass models.

Production stays unchanged. The historical native diagnostic remains
**run-31/POLICY**, with its documented NORMAL-observation alignment difference.
Native component checks do not establish integration of the whole proposal.

The [pre-refinement run-101 baseline](bidirectional-termination-baseline-run101-20261118.md)
records the extended native outcomes, including the actual OWASP helper.
The earlier finite captures in this catalogue document the named
versions and reference models.

## Notation and reading rules

```text
$ = EXACT; * = correlated STAR; M = MAY; NE = non-empty MAY
MUST = uniform taint; F = FLOW; T = one full mark
N/D = NORMAL/DEMAND; H = literal protection; E = real field exclusion
[Dc | Dp] = entry selector and its original paired output selector
Z = ZERO; DT = anonymous DemandTarget
```

Every fact starts at a named base such as x, p or ret. `x.f^k` means k f
accessors after x. Unless stated otherwise, use FULL marks, limits
`1,1,2,3,...`, empty E/mx, plain membership and the ordinary call/Target policy.
Configured producers assign the stated mark; observations check it. Fresh
allocation adds no mark. Branches use the selected path-insensitive union.

The catalogue's small code blocks omit trivial allocation/control hosts;
the linked reports state their bodies, configured actions and analysis scope.
No reported NORMAL result is relabelled as a concrete JVM execution proof.

## Status map

| Example | Failure under the named earlier policy | Status under the current approach |
|---|---|---|
| [Recursive wrappers](bidirectional-recursive-target-termination-20261117.md) | Finite per-run recursive closure keeps making a cut; backward inside replay renews root MAY and the same ZERO/DT; NORMAL observation does not retire it | R37 **[REC]** certified covered root terminal service: natural run-7, retained NORMAL report from run-3; current diagnostic run-15/POLICY; mutual native control naturally run-5 without repair |
| [Descendant selected EXACT cleaner](bidirectional-cleaner-termination-campaign-20261117.md#2-first-counterexample-selected-descendant-point) | x.MUST/N becomes x.MUST/D; root Target repeats at every field limit | R35 projection-closed selected MUST policy: natural run-1; deliberate point-cleaner coarsening; unchanged native run-15/POLICY |
| [Nested ALL/BELOW cleaner](bidirectional-cleaner-termination-campaign-20261117.md#3-second-counterexample-nested-whole-subtree-cleaning) | The precise one-field rule misses x.f.g; the same root Target repeats forever | R36 precise NORMAL MUST residual after run-1: natural run-3 for selected ALL/BELOW and RemoveAll/ALL; unchanged native run-15/POLICY |
| [Protected caller input](bidirectional-protected-original-nontermination-20261117.md) | Exact NORMAL input inherits H=1; plain-original and premise-shape guards block its native NORMAL answer | [Native-bound service](../design/bidirectional-native-bound-reply-service-20261117.md): natural run-7 stop, NORMAL observation run-5, uncapped quiet suffix; historical native run-31/POLICY |
| [Uniform-input control](../design/bidirectional-native-bound-reply-service-20261117.md) | Exact-only completion cannot use the already owned NORMAL MUST query | Natural run-9 stop; NORMAL observation run-7; finite prior repetition only, not a new uncapped counterexample |
| [Protected relevant returns](bidirectional-relevant-protected-return-nontermination-20261117.md) | Every new current return has H=1; plain-reply pruning rejects it despite ready full NORMAL-layer closure | [Same-flag NORMAL service](../design/bidirectional-flag-aware-reply-service-20261117.md): natural run-5 stop with retained NORMAL observation and uncapped quiet suffix; old native run-31/POLICY |
| [Protected unrelated NORMAL return](bidirectional-protected-return-nontermination-20261116.md) | NORMAL k/H=1 fails both full-raw plain checks despite complete h service | [Layer-aware completion](../design/bidirectional-layer-aware-point-service-20261116.md): natural run-5 stop and uncapped quiet suffix; NORMAL observation retained; old native run-31/POLICY |
| [Same-mark disjoint return](bidirectional-unadmitted-field-nontermination-20261116.md) | k/U is unadmitted at h outputs; same-mark completion fails; ordinary h read renews root MAY | [Reply-scoped NORMAL service](../design/bidirectional-reply-scoped-point-service-20261116.md): natural run-5 stop and uncapped quiet suffix; NORMAL observation retained; old native run-31/POLICY |
| [Unadmitted NORMAL V return](bidirectional-unadmitted-return-nontermination-20261116.md) | Complete exact T service loses V at paired C5; coarse MAY cycle survives | [Per-full-mark terminal service](bidirectional-mark-scoped-point-service-20261116.md): natural run-5 stop, delayed receipt run-7; NORMAL observation retained; old native run-31 |
| [Exact input, no overwrite](bidirectional-exact-input-guard-nontermination-20261116.md) | First-field STAR loses the exact endpoint; coarse GEN renews root MAY | [Complete point service](bidirectional-complete-point-service-20261116.md): natural run-5 stop, delayed-readiness run-7; NORMAL observation run-3; no new cap exception; old native run-31 |
| [Deeper real exclusion](bidirectional-deeper-excluded-guard-nontermination-20261116.md) | Same-head E retention cannot move a p.f.g hole onto a p.f query; root MAY renews | [Enumerated NORMAL MUST head retention](bidirectional-excluded-head-admission-20261116.md): natural run-5 stop; NORMAL observation retained; historical native run-31 |
| [Real exclusion and unrelated output child](bidirectional-excluded-guard-nontermination-20261116.md) | Coarse STAR loses a real hole; precise h results cannot cover root MAY | [Carried real E](bidirectional-concrete-query-exclusions-20261116.md): natural run-5 stop; NORMAL observation run-3; old native diagnostic run-31 |
| [Alternating conditional generators](#alternating-conditional-generators) | Concrete STAR queries regenerate intrinsic MAY across alternating T/U assignments | Actual uniform coverage: selected reference stops run-5; historical native run-31 |
| [Root MAY renewal](#root-may-renewal) | Root question repeats without a field cut | Current complete method reference stops at run-5 |
| [BB and enclosing-method renewal](#bb-and-enclosing-method-renewal) | Precise BBs still feed an enclosing relative cut | Current complete BB reference stops at run-5 |
| [Global-cut growth](#global-cut-growth) | Deeper helper demand keeps root Target alive | OrdinaryTwo cold reference stops at run-3 |
| [Uniform root cleaner](#uniform-root-cleaner) | Root Target repeats with no DATA refinement | Historical policy withdrawn; selected cleaner stops at run-1 |
| [Protected global-cut growth](#protected-global-cut-growth) | Concrete/protected cuts bypass neutral coverage | Checked protected closure stops at run-3 |
| [Nested saved replay](#nested-saved-replay) | Empty current callee demand does not stop saved reader MAY | Current Nested cold reference stops at run-9 |
| [Saved replay with real exclusions](#saved-replay-with-real-exclusions) | Empty-E eligibility disables needed child routing | Current Overwrite cold reference stops at run-9 |
| [EXACT-origin nested write](#exact-origin-nested-write) | A point probe invents a deeper MAY | Current negative reference stops at run-3 |
| [Intrinsic MAY rule target](#intrinsic-may-rule-target) | Irreducible model uncertainty renews Target | Excluded special-pass model; not solved by the current scope |
| [Direct concrete MUST replay](#direct-concrete-must-replay) | A provisional saved read renews exact U/DEMAND after the helper demand empties | Definite native MUST replay: latest cold reference stops run-5; native regression run-31 |
| [Uniform saved reply](#uniform-saved-reply) | The provisional concrete MUST reply is not an exact point and survives the exact-only filter | Definite native MUST replay: latest cold reference stops run-5; native regression run-31 |
| [Different-path uniform replies](#different-path-uniform-replies) | A provisional root MUST reply differs from every actual NORMAL child reply | Definite native MUST replay: latest cold reference stops run-5; historical support-only recurrence from run-6; native diagnostic run-31 |

Run-3 results in older simplified method/BB closure packages and run-5 in
later complete cold traces are different reference scopes. The table uses
the latest complete cold results where available, rather than silently
replacing one measurement with the other.

## Protected relevant returns

```java
// Entry marking: T only at a.f.g.$.
void root(Box a) {
    Box x=make(a).h;
    Box y=make(x).h;
    Box z=make(y).h;
    // Observe CM(z.M,T).
}
Box make(Box p) {
    Box r=new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
```

Precise p.f.g.$/T returns protected NORMAL ret.h.h.MUST/T. The shorter
p.f.*/T query also publishes protected DEMAND ret.h.M/T. Its ordinary h
read gives root MAY. The fine result does not cover that whole MAY region.
NORMAL-layer closure succeeds; the latest fix is not disabled. However,
protected current replies are outside all three pruning paths, and the
relevant protected fine return remains a terminal-service veto.

The full reference state repeats run-9/run-10 forever, including all
completion metadata, saved records and control permissions. There is a
NORMAL observation from run-5 and a separate live DemandTarget. Every
within-run worklist is quiescent. No field-cap exception is used.
[Full report and constructive proof](bidirectional-relevant-protected-return-nontermination-20261117.md),
[all per-block annotations](bidirectional-relevant-protected-return-trace-20261117.md).
The same-flag repair now stops this case at run-5 without changing stored flags or field caps. See the updated trace linked in the repair.

## Protected unrelated NORMAL return

```java
// Entry marking: T only at a.f.g.$.
void root(Box a) {
    Box x=make(a).h;
    Box y=make(x).h;
    Box z=make(y).h;
    // Observe CM(z.M,U).
}
Box make(Box p) {
    Box r=new Box();
    // For (m,n) = (T,U), (U,T):
    // CM(p.f.g.g.M,m) => assign n to r.h.MUST.
    // CM(p.M,m) => assign n to r.h.h.MUST.
    // CM(p.M,m) => assign m to r.k.MUST.  // NORMAL+H=1 on a NORMAL input
    return r;
}
```

The exact p.f.g.$/T query returns plain NORMAL h.h/U and protected NORMAL
k/T. Every real h-region return has admitted/applied NORMAL service. k is
irrelevant to that region, but the earlier adapter scanned all raw returns
with `!demand && !protected` before projection. Neither current closure nor
reply completion succeeds, at any later field limit. Coarse p.f.* -> ret.h.M
was still delivered; the caller's h read renewed root MAY. Complete states
repeated run-11/run-12 forever. The same-mark source action is not a pass or
an identity assignment: its target is the fresh k position.

[Full counterexample and constructive proof](bidirectional-protected-return-nontermination-20261116.md),
[all per-block annotations](bidirectional-protected-return-trace-20261116.md).
The selected repair checks NORMAL-layer full closure with H preserved, then
plain service for every overlapping terminal return. k remains protected
and disjoint. h has whole plain NORMAL service and a native receipt, so the
coarse h reply is omitted. An overlapping protected return still prevents
selection. No raw k summary is archived. The new reference naturally stops
at run-5, retains its NORMAL observation and has an uncapped quiet suffix
from run-6. Earlier three reply-service histories are semantically identical.
[Repair, controls and proofs](../design/bidirectional-layer-aware-point-service-20261116.md),
[updated per-block annotations](bidirectional-layer-aware-point-service-trace-20261116.md).

## Same-mark disjoint return and ordinary reads

```java
// Entry marking: T only at a.f.g.$.
void root(Box a) {
    Box x = make(a).h;
    Box y = make(x).h;
    Box z = make(y).h;
    // Observe CM(z.M,U).
}
Box make(Box p) {
    Box r = new Box();
    // For (m,n) = (T,U) and (U,T):
    // CM(p.f.g.g.M,m) => assign n to r.h.MUST.
    // CM(p.M,m) => assign n to r.h.h.MUST.
    // CM(p.M,m) => assign n to r.k.MUST.
    return r;
}
```

The fine query p.f.g.$/T has two NORMAL U returns: ret.h.h and ret.k.
Paired h output selectors keep h.h and discard k. Per-full-mark completion
therefore cannot certify U. Coarse p.f.*/T still produces ret.h.M/U;
the ordinary caller h read makes x.M/U, which the next call submits to the
same owner. Its NORMAL x.h.MUST/U does not cover root MAY. Both marks are
assigned and checked. All H/E/mx remain plain/empty.

The full state repeats from run-11/run-12 at arbitrary later field limits,
not just until the temporary hard limit. The 70/82 handoff frontiers already
repeat from run-9. NORMAL observation run-5 does not cancel DemandTarget.
[Detailed proof](bidirectional-unadmitted-field-nontermination-20261116.md)
and [complete per-block fact trace](bidirectional-unadmitted-field-trace-20261116.md).

That is the checked before-change result. The reply-scoped repair keeps the
full NORMAL analysis but checks only true returns overlapping ret.h.M/U for
that one coarse delivery. h.h/U has applied NORMAL service; k/U is disjoint.
The updated reference stops at run-5 and retains its NORMAL observation;
its earlier run-3 DemandTarget remains recorded. No per-region cache or
extra propagated edge is added. [Updated contract and proof](../design/bidirectional-reply-scoped-point-service-20261116.md).

## Unadmitted NORMAL return

Keep the three ordinary calls and the original four marking rules from
the exact-input example below. Add two ordinary rules in the same make body:

```java
// CM(p.M,T)   => assign V to r.k.MUST.
// CM(p.s.M,V) => assign U to r.h.MUST.
```

The exact p.f.g.$/T query now computes a second raw NORMAL return, k/V.
It is rejected by the current T/U paired outputs. V is also checked by
an executable rule, so mark-set specialization does not remove it. Its
s input region is disjoint from k. The exact query has an incomplete
admitted return service and the newest pruning law correctly declines to
omit the coarse root-MAY reply. The selected reference has an uncapped
run-9/run-10 recurrence, with completion active for a separate U query.

[Full code and proof](bidirectional-unadmitted-return-nontermination-20261116.md),
[complete per-block trace](bidirectional-unadmitted-return-trace-20261116.md).
**Current resolution:** require complete terminal service only for the
current concrete output mark, while preserving the full internal closure.
The exact T query has complete U service even though C5 rejects V. A native
U receipt permits omitting only its coarse U reply. The updated reference
stops at run-5, or run-7 with delayed receipts. No V summary is restored.
[Updated trace and proof](bidirectional-mark-scoped-point-service-20261116.md).

## Exact input without exclusions

```java
// Entry marking: T only at a.f.g.$.
void root(Box a) {
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observe CM(z.M,U).
}
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // Also the symmetric U-to-T actions.
    return r;
}
```

The actual p.f.g.$/T,N starts coarse p.f.*/T,D for the broad p.M/T row.
The coarse deep guard can emit ret.M/U,D. The fine point rejects the same
guard and emits only the valid NORMAL h result. Those results coexist;
the child cannot cover the whole root-MAY question. Reverse broad result
queries renew the broad input demand and root source permission.

The [complete report](bidirectional-exact-input-guard-nontermination-20261116.md)
and [per-block trace](bidirectional-exact-input-guard-trace-20261116.md)
show the uncapped **run-9/run-10** cycle with 70/82 qualified rows and ten
NORMAL records. All field exclusions remain empty. The current NORMAL-MUST
head-retention exception is enabled but ineligible; ordinary global and
Dc+1 initial limits hold. Every run is quiescent. No cap relaxation, field
write, cleaner, special pass or Target cancellation is used.

**Current resolution.** The already owned p.f.g.$/T query has a complete
NORMAL service with only the h result. After this service actually applies,
the new section 6 delivery rule omits the coarse CURRENT return reply to
this exact actual. It keeps the coarse summary and all unrelated work.
The [new trace](bidirectional-complete-point-service-trace-20261116.md)
stops at run-5, or run-7 with handoff-only readiness, with the valid NORMAL
observation retained. No input-cap relaxation is needed.

## Deeper real exclusion

```java
// Entry marking: a.f.g.MUST/T.
void root(Box a) {
    a.f.g.g = new Box();
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observe CM(z.M,U).
}
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // Also the symmetric U-to-T actions.
    return r;
}
```

After the real write, actual p.f.g.MUST/T {g},N starts a coarse p.f.*/T,D
with Empty E. The latest same-head map is enabled but cannot shift E to
the shorter head: that would exclude the actual's own root p.f.g. The
coarse query can still satisfy the deep guard and generate root MAY/U,D.
Fine p.f.g queries keep `{g}` and produce only NORMAL h output. Such output
does not cover a whole-root MAY question. Reverse broad result queries
renew the same input questions and root source permission.

The historical reference reached an exact **run-9/run-10** cycle with 73/83
qualified rows and 12 retained NORMAL records. Its valid NORMAL observation
does not cancel the independent DemandTarget. Every later budget and
within-run fixed point is constructively checked. The [report](bidirectional-deeper-excluded-guard-nontermination-20261116.md)
contains the code, rule-by-rule explanation and proof; the [full trace](bidirectional-deeper-excluded-guard-trace-20261116.md)
embeds every demand, submission, initial and summary through run-10 for root
and make. The finite unchanged-native capture reaches **run-31**.

The current repair retains the already submitted p.f.g head and its E in
that concrete forward MAY/NE family, only because the actual is NORMAL
MUST. The new p.f.g STAR start and FLOW companion remain globally bounded;
this is the single enumerated Dc+1 exception. Output Dp+1 is unchanged.
Run-4 supplies p.f.g.M/T, and run-5 answers it with a NORMAL MUST query.
The frontier empties with the valid observation retained. The [new trace](bidirectional-excluded-head-admission-trace-20261116.md)
and [uncapped stop proof](bidirectional-excluded-head-admission-20261116.md)
include all old-case checks, the exact exception guard and its cost. No
Target is canceled and no exclusion is shifted to a parent.

## Real exclusion and unrelated output child

```java
// Entry marking: a.f.MUST/T.
void root(Box a) {
    a.f.g = new Box();
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observe CM(z.M,U).
}
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)     => assign U to r.h.MUST.
    // Also the symmetric U-to-T actions.
    return r;
}
```

The real run-3 input is `p.f.MUST/T {g},N`. Old coarse admission started
`p.f.*/T {},D`, so it could meet the excluded f.g guard and produce a root
MAY. The fine query produced only a valid NORMAL h result; h cannot cover
root MAY. This caused the checked historical run-7/run-8 recurrence.

Now the coarse initial and its FLOW companion keep `{g}` at p.f. The f.g
guard cannot run. The h action remains and produces six retained NORMAL
records across the alternating T/U calls. Ready NORMAL child images cover
the child DEMAND images under the existing actual-DATA law. Run-3 retains
the NORMAL observation and six local method demand rows but emits no root
DemandTarget. Existing backward control gating clears the frontier at
run-4; the next forward run, **run-5**, stops. No Target is canceled.

This changes C2 and the raw C5 entry image only for restricted FULL concrete
families at an unchanged head. A shortened head cannot inherit the child's
E. Different arrived E values can produce more conditional keys; family
size per offer is unchanged. The [full repair report](bidirectional-concrete-query-exclusions-20261116.md)
contains all run counts, complete six-record trace, old-case validation and
the constructive no-revival proof. The [old recurrence](bidirectional-excluded-guard-nontermination-20261116.md)
remains historical evidence for the policy without this repair.

## Alternating conditional generators

**Historical counterexample before NORMAL uniform actual coverage**, even
with definite native MUST matching and identical EXACT/MUST support. The
latest actual DATA coverage law resolves it at **run-5**. It keeps the
previous matching and Target semantics.

```java
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.MAY,T) => GEN(r.MUST,U)
    // CM(p.MAY,T)     => GEN(r.f.MUST,U)
    // CM(p.f.g.MAY,U) => GEN(r.MUST,T)
    // CM(p.MAY,U)     => GEN(r.f.MUST,T)
    return r;
}
void root(Box a) { // Entry producer: a.f.MUST/T,N.
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observe CM(z.MAY,U).
}
```

All targets are fresh uniform assignments. None is a pass or intrinsic-MAY
model. Both bodies and the call graph are acyclic; no cleaner is used.

```text
Forward witnesses:  p.*/m -> ret.MAY/flip(m),D
Backward witnesses: ret.*/flip(m) -> p.MAY/m,D
flip(T)=U; flip(U)=T
```

The coarse forward witness uses the field-qualified condition. The coarse
reverse witness uses the other action's field target. Both root MAY outputs
fit every positive field limit without a cut. Fine NE demand and NORMAL
uniform outputs may coexist, but the selected rules do not cancel the
coarse MAY/D witness or its root DemandTarget. These mark-changing relations
are outside diagonal FLOW coverage and correlated-FLOW child delegation.

The historical non-termination proof is a witness-projected simulation
closed under the old coverage law, not full-state equality. Native tests
check the GEN cells and diagonal/cross-mark distinction in both arrival
orders. **42 new claims; 2,437 audited claims across 122 modules**. Latest
native completed iteration: **run-31**, finite policy stop, root demand in
all runs. That historical capture does not include integrated NE or the
new actual-coverage repair.

[Historical trace and uncapped counterexample proof](bidirectional-alternating-conditional-nontermination-20261116.md).
[Resolved cold trace, accumulating-Target check and uncapped no revival](bidirectional-normal-uniform-actual-coverage-20261116.md).

## Different-path uniform replies

**Counterexample to:** the earlier support-only NE/progress policy, including
its definite EXACT/MUST support filter. **Resolved by the latest definite
native MUST matching rule**, not by cross-path output subsumption.

```java
Box make(Box p) {
    Box r = new Box();
    // CM(p.g.MAY,T) => assign U at r.MUST.
    // CM(p.MAY,T)   => assign U at r.f.MUST.
    return r;
}
void root() {
    Box a = new Box(); // Entry marking: a.f.MUST/T,N.
    Box b = new Box(); // Entry marking: b.MUST/T,N.
    Box x = make(b);
    Box y = make(a);
    // Observe U anywhere under x and under y.
}
```

Both owners are straight-line. The rules generate a new full mark U; there
is no pass, cleaner, alias or intrinsic MAY target. Every relevant path fits
one field. Qualified f demand and extra g guards are included in the model.

```text
saved NORMAL B: p.MUST/T   -> ret.MUST/U
saved NORMAL F: p.f.MUST/T -> ret.f.MUST/U
actual:         p.f.MUST/T,N
saved replies:  ret.MUST/U,D + ret.f.MUST/U,N

root D witness -> ZERO -> DemandTarget
reverse B      -> a.MAY/T,D
entry marking at a.f renews the same input
```

The NORMAL child does not prove the broad root output. The actual NORMAL
root reply at the other call cannot supply this caller's support. The helper
demand is empty after run-5. Saved-first replay still renews the root Target
forever. Both observation ids are already NORMAL by run-5.

The cold Lean trace retains seven NORMAL records, including the extra exact
and g-guard members. Thirty-one new constructive claims prove all cold states,
the latest filter's surviving packet and uncapped recurrence from run-6.
Three native tests validate matching/reversal/filter cells and capture
run-31 under the unchanged production policy. The finite capture and the
latest-policy uncapped proof are separate evidence.
[Full annotated trace and limitations](bidirectional-different-uniform-reply-nontermination-20261116.md),
[proof package](../../spec/lean/proposals/different-uniform-reply-cycle-20261116/README.md).

**Current resolution:** reject the unsupported broad MUST lane before saved
summary application. The current demand lookup still runs. The precise f
provider remains NORMAL; no report or Target is canceled. All seven NORMAL
records remain. The complete cold prefix is unchanged through run-4 and
naturally stops at **run-5**. Uncapped induction proves no revival. The same
matching repair closes the earlier exact and uniform cases at run-5.
[Current complete proof and trace](bidirectional-definite-must-replay-20261116.md).


## Root MAY renewal

**Counterexample to:** NE by itself, with the original shallow C2/C5 policy.
No loop, recursion, cleaner or special transfer rule is needed.

```java
Box choose(Box p, boolean b) {
    if (b) return p.f.g;
    Box q = new Box(); q.f = p;
    return q;
}
void entry(boolean a, boolean b) {
    Box x = produceAtF(); // x.f.MUST/T,N
    Box y = choose(x,a);
    Box z = choose(y,b);  // Same choose owner as the first call.
    observe(z);          // CM(z.M,T)
}
```

The first call starts p.f.STAR/F. Reading f then unknown g produces ret.M/F,D
without a cut. Its result supplies the second call's root MAY actual:

```text
C2(p.M/F, p.M/T,D) = {I(p.$/F), I(p.*/F)}
forward:  p.*   -> ret.M/F,D
backward: ret.* -> p.M/F,D
entry:    Z -> DT,D
```

The STAR start keeps asking the same unknown-suffix question. A larger global
limit changes none of these heads. The second-call input is derived from
the first call; it is not an assumed recurring input.

**Proof:** constructive witness recurrence for arbitrary later F/B pairs,
including both call applications and producer/Target guidance. Explicit
annotations cover run-1 through run-4, followed by symbolic later runs.
[Code, full trace and proof](bidirectional-non-empty-may-acyclic-nontermination-20261113.md).

**Current resolution:** qualified deeper demand heads, bounded child routing,
NORMAL reuse and later uniform coverage. Latest complete OldMethod reference
stops at **run-5** with its NORMAL observation.

## BB and enclosing-method renewal

**Counterexample to:** assuming BB summarization alone solves the first case.
Use the same code, but make the read and write branch separate summary owners:

```java
Box choose(Box p, boolean b) {
    if (b) readBB: { return p.f.g; }
    else writeBB: {
        Box q = new Box(); q.f = p;
        return q;
    }
}
```

The read BB becomes precise at **run-4**. Saved NORMAL BB summaries still pass
through the enclosing method's paired restriction:

```text
saved writer + p.f.MUST/F,N -> ret.f.f.MUST/F,N
method C5, Dp=ret.*:       -> ret.f.NE/F,D       // budget remains 1
next call: p.f.NE/T,D -> I(p.f.*/F)
saved opposite reader: p.f.* + (p.f.g.* -> ret.*) -> ret.M/F,D

run-5,7,9,...: p.f.* -> ret.M/F,D
run-6,8,10,...: ret.* -> p.f.M/F,D
```

Both inner owners can use NORMAL replay while the method still renews demand.
Moving repeated work to another summarizable block is not convergence.

**Proof:** 25 constructive BB witness declarations, explicit run-1 through
run-6, then uncapped method recurrence. This is a witness projection, not a
production BB-decomposition implementation.
[Full BB annotations](bidirectional-non-empty-may-basic-block-retrace-20261113.md).

**Current resolution:** preserve qualified method and block rows; omit a
proved duplicate NORMAL relation before re-cutting it, while retaining real
actual cuts. Latest complete OldBB reference stops at **run-5**.

## Global-cut growth

**Counterexample to:** bounded first-field refinement plus NORMAL precoverage
of uncut relations. NE does not stop genuine cuts from recurring.

```java
Node choose(Node x, boolean b) {
    if (b) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
void entry(boolean a, boolean b) {
    Node x = produceTree(); // x.MUST/T,N
    Node y = choose(x,a);
    Node z = choose(y,b);
    observe(z);            // CM(z.M,T)
}
```

At forward field limit L, a near-limit query grows by two fields:

```text
P = x.f^(L-1).MUST/F
P -> ret.f^(L+1).MUST/F,N
global cut -> P -> ret.f^L.NE/F,D
```

The boundary candidate is already D, so NORMAL precoverage cannot remove it.
It feeds the second call's STAR query and the next deeper frontier. Helper
heads grow; the **root edge** `Z -> DT,D` repeats forever. Equal-coordinate
helper repetition is not necessary for non-termination.

**Proof:** uncapped induction over arbitrary forward L, both calls, backward
producer permission and the root Target. Finite exploration reached **run-31**.
[Full trace and proof](bidirectional-bounded-refinement-ordinary-cycle-20261114.md).

**Current resolution:** same-complete-MUST-initial NORMAL uniform coverage
of NE, legal saved uniform providers, and canonical reply packets. The
latest OrdinaryTwo cold reference stops at **run-3**.

## Uniform root cleaner

**Historical counterexample to:** the policy which demoted a same-head MUST
at a selected root-only cleaner.

```java
void entry() {
    Node x = produceTree(); // x.MUST/T,N
    removeTAtRoot(x);       // Selected EXACT-reach cleaner.
    observe(x);             // CM(x.M,T)
}
```

Under that old policy:

```text
forward:  x.MUST/T,N -> partial MUST/T,D,H -> observation on D
backward: x.M/T,D survives and reaches the producer
both handoffs: Z -> DT,D
```

There is no field cut, growing path or DATA method initial to refine. The
native old-policy test completed **run-21**; an uncapped induction proves
the recurrence, independently of that test horizon.

**Current resolution is a semantic decision:** the selected exact-root T
cleaner cannot clean a same-head MUST/T. Preserve its layer and survivor
protection. The revised reference naturally stops at **run-1**.

This also permits a NORMAL exact-root observation which the old concrete
cleaner would have removed. That accepted consequence is explicit; do not
present the new rule as preserving the old cleaner precision.
[Historical proof, native evidence and selected revision](bidirectional-uniform-root-cleaner-nontermination-20261114.md).

## Protected global-cut growth

**Counterexample to:** solving the preceding cases with only neutral,
unprotected FLOW uniform coverage. The selected MUST-preserving cleaner
rule is already active in this example.

```java
Node choose(Node x, boolean b) {
    removeTAtRoot(x);
    if (b) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// entry: x=produceTree(); y=choose(x,a); z=choose(y,b); observe(z);
```

The recurring facts have nonempty known heads. The cleaner is disjoint
from those locations, preserves their layers, and adds existing protection:

```text
P = x.f.MUST/T
N: P -> ret.f.MUST/T,N,H=1
X: P -> ret.f.f.NE/T,D,H=1
```

N contains X's whole output region under the same complete original. The
neutral rule cannot use it because the rows are concrete and protected.
Same-layer MUST canonicalization cannot cross from N to D either. A NORMAL
observation can already exist at run-3 while another `Z -> DT,D` keeps
refinement alive.

**Proof:** uncapped recurrence, including FLOW companions, concrete T,
protection, both calls and backward producer permission. Witness replay
reaches **run-31**; native component/bootstrap checks reach **run-3**.
[Full protected trace](bidirectional-protected-cleaner-growth-nontermination-20261114.md).

**Current resolution:** the final same-mark/mx/H uniform extension, plus
complete reply folding. The checked protected closure stops at **run-3**.
A protected row is never replaced by a plain row.

## Nested saved replay

**Counterexample to:** NE, bounded primitive routing, same-lane uniform
coverage and reply folding, with saved replay still outside child routing.

```java
Node choose(Node x, boolean b) {
    if (b) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
Node wrapper(Node x, boolean b) { return choose(x,b); }
void entry(boolean a, boolean b, boolean c) {
    Node x = produceAtFG(); // x.f.g.MUST/T,N
    Node y = wrapper(x,a);
    Node z = wrapper(y,b);
    Node w = wrapper(z,c);
    observe(w);
}
```

Ordinary analysis derives, rather than assumes:

```text
W: x.*     -> ret.f.f.*,N
R: x.f.f.* -> ret.*,N             // backward-produced NORMAL view
```

The real actual x.f.g.MUST does not match R. The wrapper's coarse query can:

```text
I(x.f.*/F) -> choose input x.f.*/F
saved opposite R -> ret.M/F,D
```

This still occurs when choose has no current demand. Saved replay must run
before current admission; removing the call subscription would not remove
this contribution. The two scalar head positions reproduce four paired MAY
rows after the stationary basis is learned.

**Proof:** complete cold states through **run-9**, stationary run-9/run-10
packets and uncapped induction. Finite exploration reaches **run-31**.
[Code, annotations and proof](bidirectional-nested-saved-replay-nontermination-20261115.md).

**Current resolution:** route the supported saved reader contribution through
already prepared children, with a complete frozen qualified cover. Do not
remove wrapper ownership or add deeper raw starts. The current Nested cold
reference stops at **run-9**. Nontransparent prefix/postfix/two-call variants
also remain in the acceptance set.

## Saved replay with real exclusions

**Counterexample to:** requiring empty real E on the matched operand and
saved record endpoints before the preceding child route can run.

```java
Node choose(Node x, boolean b) {
    x.g = new Node();
    Node y;
    if (b) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
Node wrapper(Node x, boolean b) { return choose(x,b); }
// entry: T at x.f.g and descendants; call wrapper three times; observe final result.
```

The code-derived records are:

```text
Wg: x.*     -> ret.f.f.* {g},N
Rg: x.f.f.* -> ret.*     {g},N
```

The old empty-E routing guard falls back to native replay. Conditional
x.f.STAR still produces root MAY through Rg, although the actual next g
cannot use that reader. Four wrapper MAY rows repeat; choose's current
demand can already be empty.

**Proof:** cold run-1 through **run-13**, stationary packets, original marked
caller delivery, producer permission and uncapped recurrence. Latest finite
capture: **run-61**. Four native operator tests validate the E behavior.
[Full overwrite trace](bidirectional-overwrite-saved-replay-nontermination-20261115.md).

**Current resolution:** allow real operand/record E in the existing qualified
child proof. Keep each E at its original scope. Excluding g at x does not
exclude g at x.f. The Overwrite reference stops at **run-9**.

## EXACT-origin nested write

**Counterexample to:** all preceding fixes while keeping the EXACT/FLOW
write-keep exception. This is a supported **synthetic atomic core form**;
no end-to-end JVM lowering result is claimed.

```java
Node choose(Node x, boolean b) {
    x.f.g = new Node();
    Node y;
    if (b) y = x.f;
    else { y = new Node(); y.f = x; }
    y.f.g = new Node();
    return y;
}
void entry(boolean b) {
    Node x = produceAtG(); // x.g.MUST/T,N
    Node y = choose(x,b);
    observe(y);
}
```

The parallel keeps of the first write act on the same operand:

```text
x.$/F,N + keep(x.* {f})   -> x.$/F {f},N
x.$/F,N + keep(x.f.* {g}) -> x.f.M/F,D     // historical exception
then y=x.f               -> y.M/F,D
```

The raw prefix probe normalizes its public premise to STAR. The same root
MAY obligation is renewed after run-3; its paired output budget stays 1.
The existing child route only handles eligible STAR contributions, not this
EXACT-origin promotion.

The supplied g point/region cannot return: the read branch asks for f; the
writer branch puts it at y.f.g and then overwrites that location. Thus the
repeated D observation has no actual marked return in the modeled program.

**Proof:** complete cold states through **run-11**, arbitrary later two-phase
recurrence, caller/Target continuation and concrete negative reachability.
Latest finite capture: **run-61**. Four native core-operator checks pass.
[Full counterexample](bidirectional-nested-write-nontermination-20261115.md).

**Current resolution:** an EXACT/FLOW point cannot match a keep strictly
below it. Retain the normal same-head/ancestor exclusion and ordinary value
writes. The negative case stops at **run-3**. T exactly/uniformly at x.f
still reaches the observation and stops at **run-3**; deeper real f inputs
stop at **run-5**, the larger three-call variant at **run-11**.
[Complete repaired trace](bidirectional-exact-point-write-progress-20261115.md).

## Intrinsic MAY rule target

**Excluded-language counterexample.** This established counterexample is
kept in the catalogue, but special pass rules are outside the current
ordinary-code termination target.

```java
void entry() {
    Object x = produceExactT();
    Object y = copyToUnknownField(x); // Configured pass, no analyzed transfer body.
    observeExact(y);
}
```

The old permitted rule language gives:

```text
producer:        Z -> x.$/T,N
pass action:     x.$/T -> y.M/T,D
exact check:     y.M/T,D can match y.$/T on D
reverse pass:    y.$/T,D -> x.$/T,D
reverse marking: producer permission and Z -> DT,D
```

MAY is intrinsic to the configured target. No field cut, loop, recursion or
unbounded concrete path exists. Every handoff renews `[Target | Z]`.

**Proof:** complete scalar action/control recurrence for arbitrary runs.
Explicit traces run through **run-6**, then a symbolic later-run induction;
no finite latest scan is claimed. The model includes and exceeds run-11.
[Rule contract, full trace and proof](bidirectional-bounded-refinement-acyclic-nontermination-20261114.md).

**Status:** unresolved outside scope. More field precision or the EXACT keep
correction does not make this rule target precise. Changing the rule contract
or adding a retirement/completion rule needs a separate decision.

## Direct concrete MUST replay

**New required counterexample to the complete consolidated approach.**
No loop, recursion, cleaner, special pass, alias or static is needed.

```java
Box make(Box p) {
    Box r = new Box();
    // Producer rule: CM(p.M,T) => assign U at r.$.
    return r;
}
void root() {
    Box a = new Box(); a.f = new Box(); // Producer: a.f.MUST/T,N
    Box b = new Box();                 // Producer: b.MUST/T,N
    Box x = make(b);
    Box y = make(a);
    // Observe U exactly at x and y.
}
```

The source action generates an exact U point. It is not an intrinsic MAY
producer or a pass. The two real calls establish:

```text
M0: p.MUST/T   -> ret.$/U,N     // run-3
Mf: p.f.MUST/T -> ret.$/U,N     // run-5
```

On every later forward offer of a, direct saved M0 replay uses its native
provisional lane and returns `ret.$/U,D`. Mf returns `ret.$/U,N`. The complete
packet retains both support layers. The root therefore keeps
`Z -> DemandTarget,D`, even though both reports are NORMAL by run-5.

From run-6 onward make has no fresh demand or analyzer. Backward saved reads
still renew the field producer's permission and the same root Target. There is no
field cut or field growth: all chains have length at most 1. The NE and
STAR-child fixes do not change direct concrete MUST replay.

**Proof:** computed cold producer/observation-cone states through run-6,
then constructive induction for every later completed run. **30 theorems**
are checked. Three native case/component tests and three one-input controls
pass. Latest native capture: **run-31**, policy ceiling rather than natural
completion. [Full annotated trace and proof](bidirectional-provisional-must-nontermination-20261115.md).

**Earlier support-only resolution:** the consolidated proposal retains exact FULL reply
support absorption. An actually NORMAL exact point removes its identical
DEMAND reply under the same complete original, continuation and H. It removes
neither native record nor Target. The cold reference retains runs 1–6,
including the late provisional effect, and naturally stops at **run-7**.
That is the historical support-only result. The latest definite native MUST
gate instead preserves runs 1–4 and stops this example at **run-5**, with
both findings and records. [Latest proof](bidirectional-definite-must-replay-20261116.md).
The [new proof package](../../spec/lean/proposals/exact-support-absorption-20261115/README.md)
also checks every old cold reply packet unchanged. Production remains
unchanged; the run-31 capture and original uncapped proof remain regressions
for omitting this repair.

## Uniform saved reply

**Counterexample to the exact-only support policy.** No loop, recursion, cleaner, pass,
alias, static or unresolved body is used.

```java
Box make(Box p) {
    Box r = new Box();
    // Producer: CM(p.M,T) => assign U uniformly at r.
    return r;
}
void root() {
    Box a = new Box(); a.f = new Box(); // Producer: a.f.MUST/T,N
    Box b = new Box();                 // Producer: b.MUST/T,N
    Box x = make(b);
    Box y = make(a);
    // Observe CM(x.M,U) and CM(y.M,U).
}
```

The two calls infer NORMAL uniform records. The selected new C2/C5 policy
also infers exact members; they do not solve this cycle:

```text
p.MUST/T   -> ret.MUST/U,N       // run-3
p.f.MUST/T -> ret.MUST/U,N       // run-5

actual p.f.MUST/T,N:
    first saved record  -> ret.MUST/U,D
    second saved record -> ret.MUST/U,N
```

Exact absorption runs on the complete batch and removes the weak exact
image using the extra exact provider. It does not remove MUST. Same-layer
canonicalization keeps both uniform support layers. The surviving D witness
therefore renews `Z -> DemandTarget,D` indefinitely. Both findings are NORMAL
by run-5; the helper has no current demand or analyzer from run-6. Only the
a.f producer permission is renewed in the steady state.

**Proof:** 30 constructive claims compute the cold prefix and prove
`history(n+6)=stateAfterRun6` for every n. The exact repair is enabled; the
surviving uniform witness also withstands arbitrary additional ready exact
providers and either record order. Native latest capture: **run-31**, policy
ceiling. Three new native tests check the driver, matching/reversal cells,
complete packet and latest exact filter, alongside eleven prior controls.
[Full annotated trace and proof](bidirectional-provisional-uniform-nontermination-20261116.md).

**Earlier support-only resolution:** definite FULL reply support absorbs the identical
MUST/D member using its actually NORMAL counterpart, with the same literal
E/H and complete caller context. Both exact and uniform cold references
naturally stop at **run-7**, without changing their cold states through
run-6 or deleting an existing Target. The new proof also keeps every old
captured reply packet unchanged. [Proof and validation](bidirectional-definite-reply-support-20261116.md).
Production and the earlier uncapped counterexample are unchanged.

Latest status: definite native MUST replay stops this case at **run-5**.
The support-only run-7 proof remains valid for its named earlier policy.
[Latest proof and all three replay results](bidirectional-definite-must-replay-20261116.md).

## Safety counterexamples: fixes which must not return

These refute proposed pruning rules or generalizations. They are not all
claims of non-termination of the current approach.

### A child NE does not cover its boundary point

```text
previous: ret.* -> p.M,D  and  ret.* -> p.f.NE,D
actual:   p.f.$/T,N

exclude f from broad p.M: rejects
retained p.f.NE:          rejects its own empty suffix
result: no initial; required p.f.$ is lost
```

Latest failed-route trace reaches **run-2**; original policy obtains its
NORMAL observation at **run-3**. Retain complete boundary-point service.
[Code and checked trace](bidirectional-handoff-may-exclusion-20261113.md).

### A NORMAL writer does not cover every reader dependence

```java
Box choose(Box p, boolean b) {
    if (b) return p.g;
    Box q = new Box(); q.f = p;
    return q;
}
// T at p.g and descendants; observe exactly ret.f.
```

NORMAL `p.* -> ret.f.*` maps that producer to ret.f.g, not ret.f's root.
Banning f from the broad return demand blocks discovery of the different
`p.g.f -> ret.f` read dependence. Successful saved replay covers only its
own correlation. Failed admission is seen at **run-2**, the original route
at **run-3**.
[NORMAL-only exclusion counterexample](bidirectional-handoff-normal-summary-exclusions-20261113.md).

### Exported E can clip a needed NORMAL reader

A wrapper around that helper can submit only STAR at the coarse demand head.
Putting an artificial `{f}` only on that unrefined STAR still exports the
negative information in a NORMAL reader. A real `p.g.f -> ret.k.f` route can
be lost. The later separate-promotion-ban candidate avoids this particular
E error, but not the next problem.
[STAR-only exclusion trace](bidirectional-handoff-star-only-exclusions-20261113.md).

### A field-only promotion ban does not prove full child service

```java
Box choose(Box p, boolean a, boolean b) {
    if (a) return p.g;
    Box q = new Box();
    if (b) q.f = p.h;
    else q.f = p;
    return q;
}
Box wrap(Box p, boolean a, boolean b) {
    Box x = choose(p,a,b);
    Box q = new Box(); q.k = x;
    return q;
}
// T at p.h and descendants; observe ret.k.f.
```

Keep **both** broad and child demand rows. A coarse STAR arriving through
wrap can still fail the old child admission, while a ban removes its only
promotion. The direct writer's NORMAL correlation does not cover p.h's
other writer correlation. The trace is evaluated through **run-3**.
[Separate-ban counterexample](bidirectional-handoff-promotion-ban-20261113.md).
The current approach uses complete bounded child admission and readiness,
not a field-only ban.

### EXACT-only MAY admission loses a surviving marked descendant

```java
Box clean(Box p) { removeTAtRoot(p); return p; }
// T exactly at input p.f; observe result at or below its root.
```

Backward MAY must keep its nonempty alternative. An exact root query is
killed, while the nonempty protected survivor reaches the marking at p.f and
enables the **run-3** route. FLOW excludes T and cannot substitute for it.
Do not repair root MAY repetition by deleting its STAR branch or seeding
backward MUST.
[Admission counterexample](bidirectional-may-may-progress-investigation-20261114.md#2-a-failed-local-fix-answer-maymay-with-exact-only).

### Final-store uniform coverage is too late for an already delivered child

For one NORMAL reply packet:

```text
ret.MUST/T,H=1; ret.f.MUST/T,H=1; ret.f.f.MUST/T,H=1; ret.$/T,H=1
```

If the deepest child is offered to the second call first, C2 can already
start a STAR/D query. Later root coverage does not undo that work. The checked
**run-3** closure needs packet canonicalization before enqueueing, while
keeping root EXACT alongside root MUST.
[Delivery-prefix counterexample](../design/bidirectional-same-lane-uniform-termination-20261114.md#5-why-batching-is-part-of-this-approach).

## Scope and workload counterexamples

| Rejected or superseded direction | Counterexample or limitation | Retained replacement |
|---|---|---|
| Full discarded evidence composition across calls | Reconstructs unbounded field-sensitive relations outside the intended abstraction | Bounded C2/C5, local existing-child proofs; no full suffix archive |
| Full NORMAL guard expansion | May exceed FL(Dc)+1; a longer reader also exposes bootstrap limits | One observed field per original row; deeper qualified demand survives |
| Transparent wrapper owner sharing | Small ordinary operations break the syntactic eligibility; it does not solve the general problem | Keep owners; route eligible saved contributions inside them |
| Persistent whole-body partitions | Growth reference has 18 executable rows instead of 2 at run-8, both finishing run-11 | Reuse already prepared child queries; no persistent partition |

These are not all infinite-run proofs. The workload example refutes the
claimed practical advantage of that partition strategy. Its full ordinary
code and same-prefix counts are in the
[partition review](bidirectional-progressive-input-partition-20261115.md).
The full evidence and owner-sharing proposals are explicitly withdrawn in
their documents; the consolidated approach does not reintroduce them.

## Known model-alignment gaps, not termination proofs

The two older diagnostic cases had an independently accepted region route
but no reference observation in either historical mode. They were not silently
counted as successful preservation tests. The 17 November revisit now
confirms the historical 165 loss (now repaired by R34 in the proposal) and
884 as a passing current control.

| Case | Latest result | What is known |
|---|---|---|
| Earlier exclusion-aware screen, case 165 | R34 reference keeps NORMAL observation at run-5; unchanged native still loses it | Repaired by additional possible DIRECT service; minimal one-call case, exact control and field caps checked |
| Latest nested-write screen, case 884 | Updated reference and native controls retain NORMAL observation at run-5 | Old diagnostic is stale for this current scope; both broad and named native observations pass |

[Case 165 code](bidirectional-exclusion-aware-child-replay-20261115.md#existing-reference-alignment-gap)
and [case 884 code/route](bidirectional-exact-point-write-progress-20261115.md#6-wider-diagnostic-and-one-unchanged-alignment-issue)
retain the historical receipts. The
[new audit](bidirectional-prefix-return-soundness-gap-20261117.md) supersedes
their old alignment-only status. R34 repairs case 165 in the reference;
884 passes in the updated checked scope. Neither is a termination refutation.

## Current acceptance evidence

Latest recursion investigation: **52 new constructive claims; 7,360
cumulative in 431 source-hash-checked modules; 123 native tests pass**.
The new uncapped recursive counterexample has a validated proposal repair
at natural **run-7**. Current native diagnostic: **run-15/POLICY**. Fresh
reference search: 11,340 direct/mutual configurations, no further example
or observation mismatch, natural completion through **run-13**. The native
mutual run-5 control is not claimed to require the repair. Earlier cleaner
and acyclic examples retain their scopes. G1–G4 remain open.
[Detailed results and limitations](bidirectional-recursive-target-termination-20261117.md).

Previous cleaner investigation: **63 new constructive claims; 7,308 cumulative
in 427 source-hash-checked modules; 111 targeted native tests pass**.
The two new uncapped counterexamples have validated proposal repairs at
natural **run-1/run-3**. Current-engine diagnostics reach **run-15/POLICY**.
The new finite cleaner search checks 56,700 pipelines and 2,551,500
observation cases, with natural completion through **run-5** and no further
counterexample. General G1–G4 remain open.
[Campaign, exact scopes and major semantic effects](bidirectional-cleaner-termination-campaign-20261117.md).

Previous investigation: **8 new constructive claims; 7,245 cumulative in
422 checked modules; 92 targeted native tests pass**. All 13,604 new
reference configurations reach within-run fixed points and natural
completion, through **run-11**, with no observation mismatch. Native cold
controls reach **run-9**. No new concrete gap was found in this scope;
whole-analyzer soundness remains open.
[Report and remaining obligations](bidirectional-post-direct-soundness-audit-20261117.md).

Latest repair: 25 new constructive claims, **7,237 cumulative across 420
checked modules; 83 targeted native tests pass**. The repaired prefix
reference retains its NORMAL observation and empties demand at **run-5**;
the updated 884 full reference state is unchanged. All 18 old ordinary
cases complete naturally (two now need run-17/run-13); 256 new prefix
cases have no mismatch, with natural completion through **run-9**.
Native evidence includes six repair components and the historical expected-
broken controls, not an integrated production repair.
[Latest repair and bounds](../design/bidirectional-saved-direct-possible-replay-20261117.md).
The earlier service receipts below retain their historical scopes.

**246 new constructive claims; 7,009 cumulative audited claims in 399
source-hash-checked modules; 19 native component tests pass**.

[Native-bound repair and search](bidirectional-native-bound-reply-service-20261117.md)
records the latest results. The protected-input reference naturally stops at
run-7 and keeps its run-5 NORMAL observation. The uniform control naturally
stops at run-9 and keeps its run-7 observation. Five earlier complete service
references still stop at run-5. The linked proof package has exact cold
transitions, within-run fixed points, whole native witness proofs and
uncapped quiet suffixes. Earlier packages retain their proof scopes and
observations; the largest prior ordinary natural stop is run-15.

The next search checked 252 configurations through diagnostic run-25 and
found no further counterexample. All have an empty frontier by run-9 and
observations equal to their concrete reference. The finite-family theorem
is not a universal termination theorem. Unknown ND, alias, boundary or
other effects cannot be left out of a completeness certificate.

Nineteen native component tests pass. The unchanged production diagnostic
remains run-31/POLICY with the alignment gap above. The proposal is not
integrated into production, and no new project measurement is claimed.

[Proof source and reproduction](../../spec/lean/proposals/native-bound-reply-service-20261117/README.md).
Bulk captures and compiled data stay external. Keep all resolved historical
examples in this catalogue; do not use them as open counterexamples to the
current rules.


## Source-specific phase-3 regression and phase-4 repair (17 November)

| Required relation | Losing step | Status | Latest run |
| --- | --- | --- | --- |
| Deep marking point B/full T/observer o; A has the same report ID | R37 removes the sole root ZERO/DT permission after A's NORMAL report | Repaired by R38 complete possible-origin/NORMAL-route service; source labels stay out of DATA | Baseline/repair natural run-5; old proposal natural run-3 without B |
| NORMAL B generation followed by four ordinary field writes and three reads | A source activation alone is incorrectly treated as a complete observed route | Same R38 certificate; no N path crosses a D cut | Baseline/repair natural run-5; report-only control stops run-3 |
| Actual loop block/port pipeline with two marking points | Same report-only retirement, after the shallow path confirms | R38 keeps B's required Target; native hierarchical control separate from simple repeat components | Baseline/repair natural run-13 or nested run-17; report-only control run-5 |
| Two-source recursive wrapper | Disabling service for every multi-source goal restores the known root cycle | R38 can prove service for multiple actual NORMAL origins | Diagnostic run-15/POLICY; repaired native natural run-9 |

[Proof package](../../spec/lean/proposals/mark-origin-soundness-20261117/README.md).
Fresh phase-3 and phase-1 checks cover 6,615 flat programs, 735 bounded
repeat-closure components and 336 shared direct/mutual recursive programs.
All complete in the stated reference bounds and preserve each required
marking-point relation. This is not a complete model of arbitrary native
loop ports, ND, GROUP, alias or static handling. The actual native loop
control reaches run-13; earlier checked acyclic references still reach
run-17. General activation still needs the documented witness adapters.


## Branching field-word recurrence and R39 (17 November)

| Case | Cause/classification | Resolution | Latest reached run |
| --- | --- | --- | --- |
| Prefix-only recursive writer followed by prefix-only recursive reader | W={g,h}* f and R={g,h}* g are disjoint; cuts hide final f and root ZERO/DT repeats | R39 [REC] [LOOP] validates complete word grammars and an empty product; only certified root Target guidance is omitted | Native diagnostic run-9/POLICY; repaired reference/native natural run-5 |
| Same code with a matching reader terminal or another exact observer coordinate | A real shared word forbids NoRoute pruning | Original demand retained; R38 NORMAL service still applies after the witness | Native/reference positive natural run-7 |
| Equal last fields or even/odd word parity | Last-field/suffix-only heuristics are insufficient | General word-product proof; native controls retain their earlier natural completion | Natural run-3/run-5 |
| Two actual write/read loops, or mutual recursive copies | These particular native controls already converge | Preserve all block ports and DATA handoff; no new recurrence claim | Natural run-5/run-3 |
| Long shared word g.g.g.g.g.g.f | Existing native baseline misses the valid relation; certificate declines pruning and performs zero rewrites | Not a new comparative phase-3 loss; keep as explicit implementation-alignment diagnostic | Baseline/adapter natural run-5 with no NORMAL; selected-policy reference natural run-13 with NORMAL |

The recurrence proof uses actual C2/body/C5/application witnesses and a
calculated operational pair. A constant Target Boolean alone is not its
proof. Word-automaton safety is generic in every accepted word and recursion
depth. Complete source aliases and all routes/ports are required. Unknown
or an omitted branch cannot be treated as an empty language. The proof
package and all checked controls are linked in the report above.


## Nested recursive reader and R40 (17 November)

| Case | Result and resolution | Latest run |
| --- | --- | --- |
| Writer `g*·f`, reader `g \| g·R \| h·R·h` | Field cuts hide the final mismatch. R40 **[REC]** proves no shared word and retires only the certified root Target. | Baseline diagnostic run-9/POLICY, adapter natural run-5 |
| Writer gives `h.g.h`, reader requires the nested arm | A complete shared word forbids absence certification. Both native runs retain its NORMAL observation. | Natural run-5 in both |
| Writer adds fields on both sides of its recursive call | Scalar pilot repeats through run-9. Native baseline finishes before that. This is a model alignment diagnostic. | Scalar run-9, native natural run-5 |

[Per-run traces, evidence and proof scope](bidirectional-two-sided-field-search-20261117.md).
