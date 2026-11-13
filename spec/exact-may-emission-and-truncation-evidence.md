# EXACT/MAY emission and truncation evidence

13 November 2026. Specification draft. No production implementation changes.
Baseline: `374fa3c6f5f73b24ccca00fc829da8c83a322d3f`.
Follow [proof-guide.md](proof-guide.md). The
[proof dossier](lean/proposals/exact-may-evidence-policy-20261113/README.md)
states the checked scope and outstanding adapter obligations.

The remaining decision is the replacement of unresolved MAY guidance;
section 8 records the native counterexample and uses conservative retention
until that decision is resolved. The selected emission, admitted-view and
local-priority rules below do not depend on deleting that guidance.

## 1. Changes and retained behavior

This specification changes restricted runs, starting at run-2:

| Part | Current baseline | New contract |
| --- | --- | --- |
| Uncertain C2 query | STAR initial and STAR live identity | MAY identity plus a conditional EXACT/FLOW probe |
| First-field refinement | Stop at the first new counted field, often with STAR | Keep that stopping point; use EXACT when complete, otherwise the two-start family |
| MAY summary application | No MAY owned premise | Apply a MAY-owned premise through the view admitted by this original offer |
| C5 entry | Image of the old STAR-based emitter | Image of the new complete family, including its probes |
| Boundary field cut | Discard the removed suffix | Record local suffix evidence for the admitted MAY membership |
| Next entry lookup | Empty-suffix admission has no cut evidence | Reject an exact empty binding when the selected row proves it impossible |
| Owner scheduling | ZERO/FLOW preference; summary batching can wait for all facts | Drain ready EXACT work and its publications before MAY work in each method/block |

These are semantic changes to admission, matching and refinement. Priority
changes execution order. Evidence metadata must not change fact equality,
hashing, protection classes or source/sink identities.

Keep run-1 abstraction and static handling, full concrete marks, positive
field limits, the `1,1,2,3,...` schedule, ordinary field transfers and strong
later-run writes, cleaners, aliases, complete ND joins, typed ZERO/Targets,
source permissions, physical block ports, liveness and stopping rules.
Keep the existing forward MUST lane; it is not converted to MAY. Backward
MUST remains invalid. Optional GROUP mode keeps its documented limitations.

Keep saved NORMAL replay on the original precise offer before current
demand lookup. Do not add a raw-summary archive, a grounding label, a new
tail kind, a new alias policy or a special static transfer.

## 2. Terms and domains

```text
$ = EXACT                  [any] = MAY
* = correlated STAR        [any-taint] = uniform MUST
F = abstract FLOW mark     T,U = full concrete marks
N = NORMAL                 D = DEMAND
E = field exclusion       mx = FLOW mark exclusion
H = literal protection class

previous selected edge Dp -> Dc
next-run demand pair: (entry=Dc; exit=Dp)
```

The new restricted refinement starts have EXACT or MAY tails. Legal
forward MUST starts keep their separate existing contract. There is no
restricted live STAR start. STAR remains legal in demand selectors and
normalized summary/record templates. Run-1 retains its old STAR domain.

A live initial starts an identity with its own path, tail, mark and layer.
Keep EXACT during instructions. Only the existing complete FLOW summary
normalization turns EXACT endpoints into STAR. Concrete T EXACT endpoints
do not normalize. Applying a normalized template must preserve the actual
EXACT/MAY/MUST shape, or produce MAY for an existing approximation; it must
not install the stored STAR template as a live fact.

All old base, mark, counted-depth and static-anchor guards remain. T never
matches U or manufactures T from FLOW. Keep indivisible static class/field
anchors, exact class markers and named concrete static fields. No broad
root/class concrete mark is introduced. E/mx on supplied facts remain real
constraints. Normalize selector E only in the existing abstract-demand role.
MAY has Empty E. EXACT/FLOW can retain the exclusions required by writes.
An EXACT/FLOW initial is legal; this does not make an EXACT/FLOW frozen
demand entry legal. Keep those two roles separate.

## 3. Initial families

Let the demand head be p and the offered head be q. A proper extension must
pass the existing tail/E reachability test. Unrelated heads give no result.
Reject a restricted live STAR offer; it signals an unconverted producer or
delivery route. Do not silently reinterpret it as MAY.

For an admitted uncertain head r and required mark M:

```text
dual(r,M) = {
    r.$/F     -> r.$/F,     N,   // conditional structural probe
    r.[any]/M -> r.[any]/M, D    // uncertain payload query
}
```

The FLOW probe does not assert that the actual caller has an exact root
mark. Its summary is conditional; application must still use the actual
offer and its support. A concrete exact query derived from uncertain
support stays D. Only FLOW probes get the symbolic NORMAL start.

### 3.1 Complete spatial table

| Geometry | Demand | Offered tail | Primary family |
| --- | --- | --- | --- |
| p=q | MAY | EXACT | EXACT at p, unless section 5 excludes the empty binding |
| p=q | MAY | MAY | `dual(p,M)` |
| p=q | MAY | MUST | Existing forward MUST result at p, with actual E |
| p=q | STAR or concrete EXACT | Any legal offered tail | Existing EXACT result at p |
| p=q | EXACT/FLOW | MAY | Reject; an abstract exact demand is not a generic MAY permission |
| q properly extends p | MAY | EXACT ending at the first new field r | EXACT at r |
| q properly extends p | MAY | Longer EXACT, MAY, or deeper MUST | `dual(r,M)`, where r stops after the first new counted field |
| q properly extends p | STAR, run-2 | Legal descendant | `dual(p,M)`, replacing the old requested STAR start |
| q properly extends p | STAR, later runs; or EXACT | Any | Reject |
| p properly extends q | MAY | MAY | `dual(p,M)` |
| p properly extends q | MAY | MUST | Existing forward MUST result at p, with its existing rebased E |
| p properly extends q | STAR or concrete EXACT | MAY or MUST | Existing EXACT result at p |
| p properly extends q | EXACT/FLOW | MAY | Reject |
| p properly extends q | Any | EXACT | Reject |

For every successful proper-descendant admission under a MAY demand, keep
the **existing** EXACT/FLOW/NORMAL probe at the demand prefix p too. This
does not replace the new pair at r. Deduplicate equal probe keys.

Examples, with compatible marks and sufficient global depth:

```text
Dc=x.[any]/F, A=x.[any]/T:
    x.$/F,N; x.[any]/F,D

Dc=x.[any]/F, A=x.f.g.h.[any]/T:
    x.f.$/F,N; x.f.[any]/F,D
    x.$/F,N                         // retained existing prefix probe

Dc=x.[any]/T, A=x.f.g.$/T,N:
    x.f.$/F,N; x.f.[any]/T,D
    x.$/F,N

Dc=x.[any]/T, A=x.f.$/T,N:
    x.f.$/T,N; x.$/F,N              // the known exact point stays exact

Dc=x.f.[any]/F, A=x.[any]/T:
    x.f.$/F,N; x.f.[any]/F,D        // preserves uncertainty through wrappers
```

MAY starts are always D. FLOW EXACT probes are N. Concrete EXACT/MUST
starts retain the existing offered-layer rules; a provisional concrete
EXACT from MAY is D. A rejected primary creates no companion.

## 4. Call and block application views

One admitted key is not a replacement for the original offered packet.
The caller retains both logical roles:

```text
original offer A: used by ordinary saved NORMAL replay
admitted query I: used by current query subscription and application
```

A MAY initial I uses a MAY application view with I's base/path, the
compatible actual mark payload, Empty E and D support. The view is allowed
only by the actual C2 result for this offer and demand snapshot. It cannot
be invented from an unrelated summary or another caller's admission.
Preserve actual FLOW mark exclusions mx and the literal protection class H;
admission does not create an excluded mark or erase protection.

For example, original `p.f.g.$/T,N` admitted as `p.f.[any]/T,D` uses
`p.f.[any]/T,D` for that MAY query's current-summary application. The
original precise input still reaches saved NORMAL records first. A broad
MAY at an ancestor similarly gets a view at the selected deeper demand head.

A MAY-owned summary applies only through such an admitted MAY view. Merely
overlapping an EXACT or MUST original does not authorize it. Reuse the
existing admission result; do not perform an independent second demand
lookup or keep a rejected-input history. Exact-origin normalized summaries
keep the ordinary precise-offer matching rules. Keep the original caller
premise, link support and physical ports on every returned fact.

ND summaries still require a complete same-context binding for all members.
A MAY member uses its authorized view and contributes D support. Never
weaken an ND premise or combine views from independent caller contexts.

## 5. Truncation evidence

Capture evidence only at an admitted method/block summary field cut:
after complete paired C5 selection, immediately before its FL+1 limit.
The global in-body limit, rule effects and loop instruction processing
remain unchanged. Evidence from these earlier operations is not inferred.

Conceptually, evidence at an output prefix a is a union of removed suffix
patterns. An unknown contribution denotes every suffix:

```text
cut a.g.h.[any] to a.[any] -> evidence { g.h.[any] }
also cut a.n.m.*          -> union { n.m.* }
uncut a.[any]             -> unknown
MAY transported from a callee without a new local cut -> unknown
```

The selected evidence query is **whether the suffix can be empty**. It
does not introduce general first-field exclusion or alias filtering:

```text
mayEmpty(known suffix set) = some suffix pattern admits epsilon
mayEmpty(unknown)          = true
merge bit                 = OR
real cut removing a known field contributes false
uncut/unknown contribution contributes true
```

An exact one-bit representation is sufficient for this query. Full suffix
sets may be diagnostic data; do not require an unbounded raw-path archive.
The proof model checks that bit merge is equivalent to union followed by
the empty-suffix test. Missing evidence is true, never false.

Evidence belongs to a complete admitted membership: owner, direction,
scope, ports, complete original, output coordinate, marks, layer and H.
Merge every contributor, including duplicate offers which add no fresh
fact. Rebase evidence when output compaction rebases its coordinate:

```text
rebase(bit, shift) = shift.isEmpty AND bit
```

Thus an unknown same-head contributor widens the bit to true. An unknown
child under a nonempty shift cannot supply the ancestor's empty binding.
Initialize a newly created membership from its actual first contribution;
do not OR a first known cut with an invented prior unknown. A genuinely
missing or legacy certificate still means unknown. Never transfer evidence
between independent rows or protection classes.

During handoff, old output evidence becomes the next demand entry's evidence.
Freeze it only after the ordinary run barrier. Do not propagate evidence
with live facts, call results or source marks.

### 5.1 The admission filter

For one MAY demand row, reject a same-head **EXACT** payload offer when its
entry evidence says `mayEmpty=false`. It represents only the forbidden
empty binding. A same-head MAY offer is not an exact empty binding: it can
contain nonempty suffixes and still uses `dual`. A MUST offer can also
contain the required nonempty region; keep its existing guard.

An accepted strictly deeper offer has a known nonempty extension and is
not rejected by this empty-only test. Existing geometry/mark/E checks still
apply. Evidence does not add source permission, a NORMAL concrete mark,
or an exact initial for a rejected payload.

The EXACT/FLOW probe of an accepted MAY family remains legal even when the
row excludes an empty payload binding. It is a conditional relation probe,
not an assertion that the payload marks the root. Keep this distinction in
the C5 image; otherwise the normal-provider probe would be rejected later.

Example, for demand `x.f.[any]/T` whose complete local evidence is
`{g.h.[any], n.m.*}`:

| Submitted fact | Result |
| --- | --- |
| `x.f.$/T,N` | No initial: only the empty binding is offered |
| `x.f.g.h.$/T,N` | `x.f.g.$/F,N`, `x.f.g.[any]/T,D`, and the existing `x.f.$/F,N` prefix probe |
| `x.f.[any]/T,D` | `x.f.$/F,N` and `x.f.[any]/T,D`: MAY still contains nonempty bindings |

If a wrapper contributes an uncut same-head MAY, its unknown evidence
widens the bit to true. The first row is then admitted again. This loss of
filtering is deliberate: local evidence must not act as an unrecorded
constraint on another method's transfer.

## 6. C5 and handoff

Every new AP summary uses the same paired pipeline:

```text
offerSummary(owner, original, raw):
    (P,C) = existing complete FLOW normalization(original, raw)
    for complete demand row d:
        require P is in the normalized image of the NEW C2 family for d
        for selected output c in existing paired output intersection(C,d.exit):
            k = min(globalLimit, FL(d.exit)+1)
            (bounded,evidence) = cutAndCapture(c,k)
            merge evidence into this admitted membership, even if duplicate
            store and publish only admitted fresh memberships
```

The normalized image includes MAY owned keys, the EXACT probes, their
normalized STAR/FLOW public keys, and the retained forward MUST cases.
It must include the requested run-2 replacement only when a legal bounded
descendant witness exists. It must not admit a concrete exact empty key
under a nonempty-only MAY row without an actual new-family witness.

Reuse paired output intersection, layer joins, protection, the FL+1 bound
and admitted-only persistence. A cut is D and has MAY output with Empty E.
Keep original mark payload and H. No raw candidate or uncut NORMAL fallback
is retained. Do not mix one row's entry with another row's output or budget.

Keep the existing demand selector and typed control rules. A MAY original
has D support, so it cannot generate a NORMAL sink witness or NormalTarget.
DemandTarget may have MAY members in its complete premise. ZERO/Target
admission and backward ZERO-to-Target conversion stay typed; suffix evidence
does not filter control facts.

Prepared C2/C5 plans, owner eligibility, loop consumer probes, handoff
compaction and native-record adapters must use the new family/image. An
old optimization proved against the old emitter is not automatically valid.
Keep its literal reference result until its new coverage proof is checked.

Entry-only lookup may union admission permissions of identical normalized
entries: its empty-binding permission is the OR over those rows. It must
not replace the separate paired C5 certificates by that OR. A deepest row
which rejects an exact empty binding does not prove that every shorter
MAY row rejects the offer; visit the remaining relevant rows until the
complete new family is covered. A static-completion row without its own
valid cut certificate uses unknown evidence. Do not infer a certificate
from a component of its transitive composition.

## 7. Local EXACT-first scheduling

The user selected priority **within each method/block**, not a global
cross-method phase barrier. Define these local lanes:

```text
high: ZERO/control enabling work; EXACT data (N or D); legal MUST data;
      EXACT summary candidates/publications; pending NORMAL-provider
      summaries and their local delivery work
low:  MAY data, MAY query starts and MAY-conclusion D publications
```

Preserve FLOW-before-concrete as a tie-breaker within a lane. Split a packed
mixed EXACT/MAY value into correctly annotated work pieces; do not demote
its exact members or promote its MAY members to change priority.

```text
workOwner(owner):
    while quantum remains:
        if ready high work exists in this owner or its ready child block:
            process high work
            secure all resulting local sends/enqueues
            continue
        flush pending high summaries through ordinary C5/storage/publication
        deliver their ready local continuations
        if high work appeared: continue
        if no low work: finish the ordinary owner barrier
        process one low work step
        // restart at high; low can itself create a new EXACT result
```

Flush high summaries before taking MAY work even if MAY remains queued.
Waiting for the entire old fact queue to empty is insufficient. Keep the
run-1 request-commit barrier and run-1 schedule unchanged.

Do not block a method awaiting remote callees or impose a global exact
fixed point. An exact result can arrive after MAY work from another owner,
or be generated by MAY work itself. At the next local dispatch it takes
priority. The guarantee concerns ready local work, not unknown future work.

Priority therefore reduces late-provider work but does not replace
arrival-order-independent subsumption, deduplication, final retained-basis
filtering or late publication handling. Preserve existing effect ownership;
do not replay rule/report side effects merely to reorder queues.

## 8. Subsumption boundary: unresolved MAY guidance

Keep all existing proved NORMAL-relation and FLOW-backed concrete laws,
with their complete owner/ports/marks/E/H checks. A provider must actually
be admitted and retained. Priority is not a provider-existence proof.

Do not erase a MAY-owned summary merely from this shape pair:

```text
S: x.f.*/F     -> ret.*/F,     N
W: x.f.[any]/F -> ret.[any]/F, D
```

The initial local same-head-MAY application check is insufficient after
admitted views are used. The ordinary-code counterexample is:

```java
// Demand x.[any]/F, offered x.f.g.$/T,N.
// First-field starts include x.f.$/F,N and x.f.[any]/F,D.
Object choose(Object x) {
    if (b) return x.f;
    return x.f.g;
}
// Exact probe produces S from the first branch only.
// MAY query produces W, including the second unresolved branch.

// Apply S to original x.f.g.$/T: ret.g.$/T,N.
// Apply W to admitted x.f.[any]/T,D: ret.[any]/T,D.
// The second code branch really produces ret.$/T.
```

For the user's longer MAY offer `x.f.g.h.[any]/T`, the same two first-field
starts are present. S on that original offer gives `ret.g.h.[any]/T,D`.
W on the admitted view gives `ret.[any]/T,D`. The second branch can really
return `ret.h.$/T` from the valid exact binding `x.f.g.h.$/T`. Thus adding
the exact probe at f does not itself prove the missing branch covered.

The [native projected-view test](../scripts/demand_experiments/dual-starts/ProjectedMayCoverTest.kt)
checks these results and the real exact transfer of the second branch.
It is an AP-level counterexample to the proposed shape/application proof,
not an uncapped complete-driver finding-loss measurement.

Until the remaining replacement decision is resolved, retain unresolved
MAY guidance unless both application and future-guidance coverage are
proved. Do not silently add a NORMAL-provider view service, a completion
edge or a support label to delete it. The new emission/evidence rules do
not require such deletion to be defined.

## 9. Principal examples and correctness obligations

The proof dossier includes executable component witnesses for:

- Same-head MAY/MAY: two identity starts; no live STAR and no NORMAL MAY.
- `x.[any]` with `x.f.g.h.[any]`: the first-field pair, plus the retained
  existing root-prefix probe.
- Getter backward: exact probe gives a NORMAL normalized read relation;
  forward exact root gives no field-read result and MAY remains necessary.
- Wrapper and nonempty evidence: broad MAY survives at the selected field
  head; an exact empty payload does not pass a nonempty-only entry.
- Duplicate/uncut evidence contributors: OR merge, unknown widening and
  complete-row ownership prevent a false negative certificate.
- Exact current work/publication before local MAY; a late exact arrival
  preempts future MAY dispatch, with no global wait.
- The projected-view example in section 8: retaining an unresolved route
  is necessary unless its replacement has a stronger proof.

Required native acceptance is a complete combined policy, not only AP
tests: same/ancestor/deeper C2 cells, layer/mark/E/H guards, static anchors,
MUST, complete ND, Targets, exact DEMAND, wrapper/getter programs, loop ports,
no-leave and successive-loop programs, and the historical Conductor routes.
Run finding-preservation regressions without an iteration cap. Do not use
run-11 as a redundancy or convergence proof.

After implementation, compare OWASP, Conductor, Stirling-PDF and Thingsboard
with the same configurations and findings. Record latest reached/completed/
accepted iteration, per-run engine times, memory, raw/admitted/demand rows,
exact/MAY starts, evidence rejections and unknown contributions, late-provider
retirements, and repeated post-handoff rows. Separate a true field cut from
intrinsic MAY. No universal convergence or workload-reduction factor follows
from the local rules alone.

No project was scanned for this specification. Historical positions remain
OWASP **run-11/run-11/run-11**, Conductor **run-8/run-7/run-7**, Stirling-PDF
**run-11/run-10/run-9** (reached/completed/accepted forward). The prior isolated
truncation wrapper baseline finishes at **run-7**; the rejected old STAR
filter finishes at **run-5** without its finding. Those are historical
controls, not executions of this complete new specification.
