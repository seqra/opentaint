# Non-empty MAY: emission, restriction and subsumption

13 November 2026. Design specification. Production code is unchanged.
Source baseline: `374fa3c6f`; reviewed repository HEAD: `2bed8939b`.
Follow [proof-guide.md](proof-guide.md). The
[proof dossier](lean/proposals/non-empty-may-20261113/README.md) identifies
the constructive results, model scope and implementation acceptance checks.

This document replaces the earlier EXACT/MAY-start and STAR/MAY-admission
candidates for these mechanisms. It does not restart the demand campaign.

## 1. Selected semantic changes

| Mechanism | Current implementation | Selected behavior |
| --- | --- | --- |
| Tail domain | EXACT, STAR, MAY, MUST | Add non-empty MAY, written NE below |
| Restricted MAY admission | Usually one STAR primary | Split empty and non-empty alternatives; emit EXACT and STAR when both are supplied |
| Submitted STAR at the same demand head | Can supply an exact query | Supplies only the non-empty alternative |
| Restricted NE admission | No such selector | Select only the non-empty alternative |
| MUST admission | Dedicated forward MUST query | Keep that query for MAY and NE demands; do not add EXACT/STAR duplicates |
| C5 entry | Test the normalized initial's image | Test the actual raw initial's image before normalization |
| Real field cut | MAY/DEMAND | NE/DEMAND, in every run |
| Uncut write of a MAY value | Keep the written field and MAY suffix | Keep this behavior |
| MAY coverage | No NE output | A retained MAY output also covers NE in the same region |

These change query selection, summary admission and the next demand frontier.
The raw C5 check is a semantic change: another raw initial with the same
normalized key is not its witness. No persistent origin flag is added.

Keep ordinary mark identities, full-mark matching, exclusion meaning,
field overwrites, alias rules, complete ND execution, typed ZERO/Targets,
source permissions, static write effects, CFG/block ports, liveness, saved
NORMAL replay, stopping rules and the `1,1,2,3,...` field-limit schedule.
Run-1 initial abstraction stays unchanged. The new cut tail applies in
run-1 too. FULL is the acceptance mode; GROUP keeps its known limitations.
No grounding support, StrongQueries extension, rejected-input history,
raw-summary archive or extra static propagation service is introduced.
Currently rejected AnyField pass inputs remain rejected. The observation
contract preserves supported eventual refined findings under an uncapped
run schedule; it does not require identical intermediate frontiers,
confirmation timing or batch-dependent diagnostic callback counts.

## 2. Facts, tails and legal roles

```text
DATA = (base, path, tail, mark, E, mx, layer, H)
$    = EXACT                 * = correlated STAR
MAY  = [any]                 NE = [non-empty-may]
MUST = [any-taint]           N = NORMAL; D = DEMAND
E    = field exclusions immediately after path
mx   = concrete marks excluded from a FLOW slot
H    = the existing per-concrete-membership protection flag
```

For a field alphabet Sigma and empty suffix epsilon:

```text
path.$   admits {epsilon}
path.MAY admits Sigma*
path.NE  admits Sigma+

MAY = $ UNION NE;       $ INTERSECT NE = empty
```

NE does not name a first field. It is existential uncertainty, not uniform
MUST taint. All loss-created MAY and NE values have D support and Empty E.
They retain their mark, mx and H. Neither tail creates a NORMAL witness.

STAR remains a correlated symbolic suffix during transfer and summary
application: STAR-to-STAR transports the same suffix. **C2 classifies a
submitted STAR as non-empty for query selection.** This does not redefine
STAR as MUST or change ordinary STAR rule/record matching. NE, in contrast,
excludes epsilon in every spatial operation. A MAY conclusion can choose a
suffix independently of its premise; NE can independently choose a nonempty
one. Neither independent relation is subsumed merely by a STAR relation.

| Role | Allowed tails |
| --- | --- |
| Raw DATA initial / owned premise member | EXACT, STAR; forward MUST in its existing lane |
| DATA conclusion or submitted DATA fact | EXACT, STAR, MAY, NE; forward MUST |
| Frozen demand entry Dc | STAR, MAY, NE; concrete EXACT |
| Ordinary demand exit Dp | EXACT, STAR; forward-origin MUST; existing virtual MAY selectors |

MAY and NE never become owned initials or premise members, including ND
and Target premises. Consequently an ordinary Dp cannot have NE. A virtual
row cannot invent an NE exit permission. EXACT/FLOW is a legal raw initial,
but is not a legal frozen FLOW demand entry. Backward MUST remains invalid.
ZERO and Targets are typed control endpoints with no DATA tail.

NE is part of semantic equality and hashing. Preserve tail, layer and H in
logical memberships, freshness, delivery, persistence and handoff. H=false
and H=true memberships remain separate, even for identical geometry.
Pass rules carry H and never create it. Initial keys retain their existing
identity; no demand-row ID, seed layer or evidence field is added to them.

Static class anchors count as zero fields. Named static fields and array
elements count as fields. Never split a class/field anchor or create broad
root/class concrete marks. Exact class markers keep their existing role.

## 3. Initial emission: C2

Let a complete previous edge be `Dp -> Dc`. The next run uses Dc as its
entry selector and Dp as its output selector. This section defines DATA
admission in restricted runs, starting at run-2.

First require equal bases, legal bounded shapes and directed mark matching.
Concrete T accepts T, not U or unknown FLOW. FLOW accepts only marks not in
its mx; an emitted FLOW initial has Empty mx. Keep the existing catalog
operation for GROUP, outside FULL acceptance. Normalize E only for an
abstract FLOW/STAR demand. Keep real supplied E, mx, H and support.
Every descent must pass the ancestor's field-exclusion guard. An excluded
field does not become reachable through an uncertain-tail view.

### 3.1 Same head

Here demand and submitted paths are both p. Cells list raw initial tails.
Every result starts as an identity at p with the accepted required mark.

| Demand | Submitted `$` | Submitted `*` | Submitted MAY | Submitted NE | Submitted MUST |
| --- | --- | --- | --- | --- | --- |
| Concrete `$`, or precise STAR selector | `$` | none | `$` | none | `$` |
| MAY | `$` | `*` | `$` and `*` | `*` | MUST |
| NE | none | `*` | `*` | `*` | MUST |

The dedicated MUST query is the selected exception to splitting uniform
input into separate queries. Its actual proves root and descendant taint;
keep its existing forward lane, E and support. It is not a MAY value.

```text
demand p.MAY/T; submitted p.MAY/T,D:
    p.$/T -> p.$/T,D
    p.*/T -> p.*/T,D
    plus the existing p.*/FLOW -> p.*/FLOW,N companion

demand p.NE/T; submitted p.MAY/T,D:
    p.*/T -> p.*/T,D
    plus p.*/FLOW -> p.*/FLOW,N

demand p.NE/T; submitted p.$/T,N:
    no initial
```

An EXACT tail selected from MAY is provisional: concrete support stays D.
It does not assert that the actual packet definitely marks the root.

### 3.2 Different heads

Let p be the demand path and q the submitted path. Unrelated paths reject.

**Submitted q strictly extends p:**

1. Demand EXACT rejects. Demand STAR keeps only the existing run-2
   requested-STAR exception: emit p.STAR for an admitted actual descendant.
   Later STAR selectors reject descendants. Do not broaden this exception.
2. For MAY or NE demand, let r stop after the first new counted field from
   p toward q. Keep an indivisible static anchor. Emit no further known
   fields in this admission.
3. If q strictly extends r, emit r.STAR. The known removed suffix is
   nonempty. If q=r, use this table:

| Submitted tail at r | Raw initial(s) at r |
| --- | --- |
| EXACT | EXACT |
| MAY | EXACT and STAR |
| STAR or NE | STAR |
| MUST | STAR, retaining the existing first-field query policy |

The known extension p→r already satisfies an NE requirement at p; an
EXACT at r is therefore legal. EXACT first-field starts are available for
FLOW too. Keep raw EXACT during instructions, until summary normalization.

**Demand p strictly extends submitted q:**

- EXACT rejects. Ordinary STAR rejects, as before; do not add a CURRENT
  inside-query policy. Wait for an explicit matching/deeper offer or a
  suitable loss/MUST offer.
- MAY and NE can descend through the requested nonempty path. Rebase at
  p and use MAY as the residual offered tail, then apply the same-head
  table. A nonempty suffix can be exhausted by this descent.
- MUST retains the existing admitted uniform region at p. Use its
  same-head MUST cells and rebase E as before; E at q has already served
  its first-accessor guard.

Every emitted initial satisfies both bounds:

```text
FL(initial) <= run.limit
FL(initial) <= FL(Dc) + 1
```

The complete family includes the companions below, not just a scalar
primary. A failed base/mark/shape/spatial admission emits no companion.
Equivalently, construct an NE selector's family from the same-head/path
MAY selector's complete family, then remove every raw EXACT command at
the original demand head. Keep EXACT commands at a known proper descendant,
STAR commands, authorized STAR/FLOW companions and the MUST lane. This
reference filter also removes MAY's exact prefix probe for an NE selector.
It proves that an NE selector never adds a query absent from MAY.

### 3.3 Layers, companions and local priority

FLOW queries start N. Concrete STAR queries start D. Concrete EXACT/MUST
queries start N only with actual N support; a concrete point projected from
MAY/NE remains D. These are query seed layers. Applying a summary must
still join the real caller support; a symbolic FLOW query never confirms T.

For every admitted concrete STAR initial, keep the same-geometry STAR/FLOW
identity companion, N, with Empty mx. Keep legal field E. Do not manufacture
a full mark from a FLOW companion.

Keep the **conditional EXACT/FLOW prefix probe**: if Dc is MAY and the
original submitted head strictly extends its head, successful admission
also emits `Dc.head.$/FLOW -> Dc.head.$/FLOW,N`, with Empty E/mx. This is an
explicit structural exception, selected by the user. It is not evidence
for an empty concrete binding. It applies to MAY, not NE, demand.

Deduplicate raw commands by initial identity and starting-support membership.
Caller H remains on the binding/resume path; local H remains on produced
facts. Do not add H to the initial key or introduce a per-caller query key.
Retain both protection classes when storing or delivering facts.
Within each method/block, process ready EXACT work and its
publications before uncertain STAR/MAY/NE work. Keep control enabling work,
legal MUST work and ready NORMAL-provider publication in the high lane;
use FLOW-first order inside a lane. Flush high publications before the
old full-queue barrier would hide them. New high work preempts the next low
dispatch. This is local priority, not a cross-method exact fixed point.
Do not delete work or replay side effects to enforce ordering.

## 4. Calls, blocks and raw summary admission

Use the selected common call/block pipeline:

```text
offer(original actual):
    apply saved NORMAL summaries to this actual
    family = C2(current demand, original actual)
    if family is empty: stop current-analysis admission
    pass this result to the callee/block; do not repeat the lookup
    start each fresh raw query; apply/subscribe to current summaries
```

The raw query is not a replacement for the original actual packet. Do not
apply a summary to an invented coarser MAY/STAR packet merely because C2
coarsened its initial. Keep original caller premise, mark, E/mx, layer, H
and physical ports. There are no MAY-owned queries in this proposal and no
new admitted-MAY-view service. Ordinary STAR record matching, opposite-only
STAR inside matching and trusted reverse-MUST views keep their roles.
New NE actuals use their nonempty spatial region: an exact endpoint at the
same head has no overlap; a strict descendant can overlap.

An ND summary executes only after all members have complete same-context
bindings. C2 admission of one member never weakens the AND premise.
Run-1 keeps its existing singleton-origin approximation; backward remains
unary. Do not combine data from independent callers or block ports.

### 4.1 The raw C2 image is the C5 entry authority

For one entry selector d and raw initial I:

```text
RawImage(d,I) := exists legal bounded submitted A and supported layer s:
                   I is an output of the COMPLETE C2(d,A,s) family
```

This includes actual EXACT/STAR/MUST results and authorized FLOW companions.
It is not symmetric overlap, self-emission, a depth test or the image of
another normalized initial. The witness must use the same run, owner,
direction, budget, mark and static grammar. A requested run-2 STAR needs a
legal descendant witness within the budget. Do not assume a fresh legal
accessor exists when none is available.

For a concrete entry T, a raw FLOW initial is permitted only through its
actual authorized companion/probe case. Do not subsequently reject that
case with `markSub(T,FLOW)`, or use it to invent T in the output.

For a complete ND original P, the existing contributing-member C5 test
can obtain a raw entry witness for a member. Preserve **all of P** on every
admitted result. No ND member, raw initial or complete P is replaced by a
different key to pass this test.

The implementation may use a proved structural image predicate. Its
reference witness is a legal hypothetical actual, not sampled input
history. Keep no hypothetical-fact interner or rejected-input archive.

## 5. Paired C5, normalization and truncation

Dc and a current conclusion can each contain a field tree. Split them
into scalar chains for the reference operation. Keep each Dc leaf paired
with its original Dp, support, marks, H, scope and physical ports. Do not
mix entry permission from one row with output permission/budget from another.

```text
intersectSummary(rawP, rawC, previousRows, run):
    result = empty exact membership union
    for each complete scalar pair (dp -> dc) in previousRows:
        require matching owner/context/direction/block/physical ports
        require RawImage(dc, actual rawP)             // before normalization
        // For ND, use the existing member admission test; retain full rawP.
        (p,c) = normalizeCompleteFlowPair(rawP, rawC)
        for each selected leaf b in intersectExit(c,dp):
            k = min(run.limit, FL(dp)+1)
            b = fieldCut(b,k)                       // real cut -> NE,D
            (storedP,storedB) = normalizeCompleteFlowPair(p,b)
            result.add(storedP -> storedB)          // preserve layer/H
    canonicalize result with the rules in section 7
    store/publish/persist only admitted fresh memberships
```

The first normalization occurs **after raw entry acceptance and before
output selection**. This keeps the existing correlated FLOW output behavior.
The final normalization handles an EXACT/FLOW result selected by C5. No raw
candidate collection is stored. A transient boundary candidate already has
its real raw original; checking it requires no persistent provenance label.

### 5.1 Complete FLOW normalization

For a singleton FLOW original and FLOW conclusion, replace EXACT endpoints
with STAR. Preserve paths, base, E, mx, layer, scope/ports and H. Normalize
neither a concrete-mark EXACT nor any MAY, NE or MUST endpoint. Do not use
the initial's mark alone: normalization is a property of the complete pair.
ND/control pairs retain their existing normalization rules.

```text
raw p.$/FLOW -> q.$/FLOW,N     becomes p.*/FLOW -> q.*/FLOW,N
raw p.$/FLOW -> q.NE/FLOW,D    becomes p.*/FLOW -> q.NE/FLOW,D
raw p.$/T    -> q.$/T,D        stays unchanged
```

Raw EXACT still matters for field reads and field-write exclusions before
this boundary. Strong writes update E as in the current core. Do not erase
E from a NORMAL summary. Whole-position RemoveAll and the existing allowed
field-position RemoveAll shapes retain their semantics; below-only RemoveAll
and other currently rejected rule shapes are not enabled here.

Two raw FLOW initials p.$ and p.* can normalize to one public p.* key.
They are **not interchangeable before C5**. With entry p.NE/FLOW, raw p.$
rejects while raw p.* can pass. A STAR witness must not admit an unrelated
EXACT-origin result. The later public-key merge is allowed only after each
raw candidate has passed its own paired restriction.

### 5.2 Scalar exit selection

First require equal DATA bases and intersecting marks. Full T and U meet
only if equal. T does not meet FLOW excluding T. Keep the candidate's mark,
mx, H and support; an exit selector does not synthesize a full mark.
Normalize only the existing abstract FLOW/STAR selector E.

For the **same head**, this is the complete tail table. MUST denotes the
existing uniform lane, not a new NE/MUST combination:

| Current conclusion | Dp EXACT | Dp STAR | Dp MAY | Dp MUST |
| --- | --- | --- | --- | --- |
| EXACT | Keep | Keep | Keep | Keep |
| STAR | Keep whole correlation | Keep whole | Keep whole | Keep whole |
| MAY | EXACT, same D | MAY | MAY | MAY |
| NE | empty | NE | NE | NE |
| MUST | EXACT, same support | MUST with E union | MUST | MUST |

The STAR row is the existing representability rule; this operation is not
plain set intersection. It must not break suffix correlation to manufacture
an exact NORMAL result. NE cannot supply an exact root at its own head.

For **different heads**, let q be the candidate head and p the Dp head:

```text
q strictly extends p:
    keep candidate if Dp tail/E admits q-p; otherwise reject

p strictly extends q:
    EXACT candidate: reject
    STAR candidate: if E admits descent, keep it whole
    MAY or NE candidate:
        require descent is admitted
        rebase at p
        use EXACT if Dp is EXACT; otherwise use MAY
        keep D support and Empty E
    MUST candidate:
        require its E admits descent
        rebase at p; use EXACT if Dp is EXACT
        otherwise keep MUST and the existing rebased E rule

incomparable heads: reject
```

Rebasing NE through a nonempty unknown suffix resets it to MAY: that suffix
may have been exhausted. For MUST rebasing, the old E at q has served its
descent guard; use Dp's E for a STAR selector and Empty E otherwise. At a
same-head MUST→EXACT selection, retain required E for abstract FLOW and use
Empty E for a concrete exact point. No selection upgrades D to N.

### 5.3 Real field cuts, all runs

```text
fieldCut(c,k):
    if FL(c.path) <= k: return c unchanged
    keep prefix through k counted fields, with the static anchor attached
    replace the removed suffix AND old tail by NE
    set layer=D; set E=empty
    retain mark, mx and H
```

At least one known field was removed. Every binding of the old tail thus
has a nonempty suffix at the retained prefix, including an old exact point.
An uncut MAY has no such certificate and remains MAY.

Apply this cut at all existing actual field-limit operations: instruction
results, call/alias result limits, block/loop outputs and summary admission,
including run-1. Do not invent earlier cut points. Run-1 has only its global
limit. A restricted summary also uses its own Dp-relative budget above.
Do not classify demand before the final cut. A new cut of a NORMAL result
creates a DEMAND membership.

```text
x.f.g.h.$/T,N --cut to FL=1--> x.f.NE/T,D
x.f.MAY/T,D --limit >=1-----> x.f.MAY/T,D
```

Keep within-budget pieces of a packed tree unchanged; cut overflow pieces
separately and union their memberships. Existing deliberately broad protocol
supplies, such as a run-1 global static-pool MAY answer, remain broad MAY.
Do not infer a negative empty-binding fact from their canonical region key.

## 6. Transfer, rules, controls and handoff

NE is preserved by a move and by transport of a known field prefix. Reading
from its **unknown suffix** consumes one or more fields and yields MAY/D.
This is the same distinction used by the current STAR read operation:

```text
y = x.f, input x.NE       -> y.MAY,D     // unknown suffix consumed
y = x.f, input x.f.NE     -> y.NE,D      // only known prefix transported
y = x.f, input x.$        -> no y fact
```

A write prepends its known target chain and preserves the input's residual
tail. It does not assert another field after that chain:

```text
x.f = y, input y.MAY      -> x.f.MAY,D
x.f = y, input y.NE       -> x.f.NE,D
```

If f is later removed by a real cut, the first result becomes x.NE/D.
It must not become x.f.NE: y's possible root was written exactly at x.f.
Strong overwrite kills/keeps and field exclusions keep their current rules.
This proposal adds no weak-write policy. Static fields obey the same tail
algebra, in addition to their existing run-1 ownership/DEMAND protocol.

Literal checks and cleaners use NE's spatial region. An exact literal at
the same head has no NE binding; a strict descendant can have one. A partial
survivor of NE remains within its nonempty region; if the residual cannot
be represented precisely, retain NE/D rather than invent an empty binding.
Keep existing cleaner protection producers. Full kills, mark exclusions,
mark-changing actions and complete source/ND conditions remain unchanged.
NE never becomes MUST and never bypasses a mark gate or source permission.
The existing selected partial STAR cleaner survivor remains MAY/D with
its existing protection; this proposal adds no further STAR-cleaner-to-NE
optimization. Do not relabel an old MAY survivor without the selected
field-cut certificate.

ZERO and Target matching remains typed. Tail splitting cannot create a
control seed from DATA. Preserve NormalTarget's normal-only composition,
backward exclusion, IDs and persisted duplicate rules. DemandTarget and
backward ZERO conversion keep their paired gates. The existing own-ZERO
loop-summary exception bypasses only its extra loop growth gate, not C5 or
the field limit. Use the new C2/C5 tables in all loop consumer probes.

At handoff, derive the next rows from final admitted memberships, after
compaction. A DATA NE conclusion becomes a DATA NE entry selector. Do not
normalize it to STAR or MAY. Preserve original premise members, directions,
marks, source permissions and reversed physical ports. Persist eligible
NORMAL summaries as before, including legal field exclusions. NE/D itself
does not become a NORMAL native record. Existing native reverse-MUST views
remain the only MUST exception; add no general MUST/NE reversal rule.

## 7. Subsumption and canonicalization

All rules require the same complete interface: owner/context, run direction,
block scope and physical ports. Scalar output rules also require the same
complete P, compatible base/mark/mx, layer and literal H. Protect each flag
class independently. A protected membership neither removes nor is removed
by an unprotected membership. Only a real admitted retained row is a provider.

### 7.1 Independent MAY/NE conclusions

Keep the existing same-layer MAY-prefix law. MAY covers every compatible
output at or below its head, now including NE. The selected same-head case is:

```text
P -> a.MAY/T,D  subsumes  P -> a.NE/T,D
```

The retained MAY demand supplies the non-empty query too; it can additionally
supply an empty query. The raw C2 image and paired Dp stay with that retained
row. Do not apply this output-only rule to another P or silently weaken ND.

Keep equal-geometry deduplication for NE. This spec adds **no separate rule**
letting an NE parent remove a descendant STAR/MUST/EXACT relation. Such a
rule would need its own application and guidance proof, beyond positivity.
Keep both tails if no rule here proves coverage.

### 7.2 Correlated NORMAL FLOW and backed concrete rows

Keep the existing aligned NORMAL FLOW law:

```text
S: a.u.* -> b.v.*, NORMAL
L: a.u.r.* -> b.v.r.*, NORMAL
```

The same r extends both endpoints. Bases and legal static anchors must
match. Every mark admitted by L must be admitted by S (`mxS subset mxL`).
Let ES/EL union the relevant input/output field exclusions. For empty r,
require ES subset EL. For nonempty r, its first field must be admitted by
ES. The constructive S witness is r plus L's suffix. Use the current
overlap matcher with unioned exclusions before deleting L.

Keep FLOW-backed diagonal T coverage after that specialization: T must not
be excluded; output tail/geometry and the appropriate E relation must agree.
NORMAL FLOW can cover N or D T. DEMAND FLOW cannot cover NORMAL T. Keep the
existing same-tail backing rule; extend its literal same-tail case to NE,
without adding STAR-to-NE backing. Mark-changing, EXACT/MUST and protected
rows retain their existing separate rules. Local T facts still reach rules
and observations before summary replacement.

In particular, **neither** of these is a new subsumption:

```text
P -> a.*   does not cover P -> a.MAY merely from matching heads
P -> a.*   does not cover P -> a.NE  merely from matching heads
```

The independent output may use a different suffix from the correlated one.

### 7.3 MUST and handoff-only rules

Keep existing same-mark/layer/H MUST canonicalization: equal-head E uses
the represented union, admitted ancestor regions cover MUST descendants,
and only a complete immediate child with Empty E fills its parent's field
hole. Do not use a longer child or a partially excluded child as a fill.
No new MUST-to-EXACT/STAR/NE deletion is selected.

Keep existing late-FULL handoff service compaction only where its service
proof remains valid under this C2/C5:

- Same-head concrete STAR and EXACT entry selectors have the same empty
  request service outside the run-2 exception. This does not equate their
  NORMAL executable relations or erase the raw C5 distinction.
- A weaker premise/identical-conclusion outgoing service can replace a
  stronger service only with complete per-row entry/output service cover.
- An ND origin's guidance can be omitted only if retained arm witnesses
  cover **every** projected premise member and conclusion leaf, with the
  same ports and paired selector. Executable ND remains AND.

Recheck old private comparison keys: an NE selector is not equivalent to a
STAR point selector or MAY. An old `isAny` predicate is not sufficient.
Do not use repetition, future-run observations, JVM types or the temporary
run-11 limit to justify compaction. Keep a joint retained basis; two edges
redundant individually are not both removable without retained witnesses.

### 7.4 Arrival order and transitivity

Evaluate coverage against the final retained basis. MAY then NE, NE then
MAY and one combined packet must all retain the same MAY membership. If
A covers B and B covers C, use A's computed valid coverage of C even if B
was never stored. Do not publish a fabricated B. Preserve the matching
correlated shift, marks, E, layer and H through this composition.
Invalidate dependent prepared plans when their basis changes. Filter queued
publications and handoff against final membership; a removed row is not a
provider. Deduplication must retain distinct protection classes and layers.

## 8. Principal traces and required validation

The new tail adds a constant-size semantic header. A scalar MAY admission
has at most two primary starts, plus its existing companions: at most four
commands in the deeper concrete-MAY case. NE selection filters that family;
it does not enumerate lost suffixes or marks. The reference raw-image
definition can enumerate a finite legal domain for checking. Production
must use a structurally equivalent path/table predicate, not that enumerator.
Its work is proportional to path/exclusion checks and selected outputs;
indexed C5 must visit relevant complete rows and preserve their individual
budgets. No measured workload-reduction factor is claimed.

```java
// Demand entry p.MAY/T; submitted p.MAY/T,D.
// Concrete starts: p.$/T -> p.$/T,D; p.*/T -> p.*/T,D.
void copy(Box x, Box p) {
    Object y = p.g;
    // p.$ branch: no y result.
    // p.* branch: y.MAY/T,D, including y.$ when the suffix was exactly g.
    x.f = y;
    // p.*/T -> x.f.MAY/T,D; keep f while it fits.
}
// With exact Dp=x.f.$/T, admitted concrete summary:
// p.*/T -> x.f.$/T,D. The exact tail does not confirm it.
```

```text
Raw-entry separation:
    Dc=p.NE/FLOW; raw original p.$/FLOW: reject
    Dc=p.NE/FLOW; raw original p.*/FLOW: can admit
    later public normalization may give both the same STAR key

Exit and cut:
    x.NE/T,D intersect x.$/T       = empty
    x.NE/T,D intersect x.f.$/T     = x.f.$/T,D
    x.NE/T,D intersect x.f.*/T     = x.f.MAY/T,D
    x.f.g.h.$/T,N cut after f      = x.f.NE/T,D

Subsumption:
    same P/H/layer, a.MAY + a.NE   -> retain a.MAY in either order
    a.* plus a.NE                 -> retain both absent another proof
```

The checked language/selector components do not prove full-driver finding
preservation or universal termination. In particular, same-head STAR/NE/MAY
can admit another STAR non-empty query without naming a new field. The
proved progress distinction excludes an empty query from a non-empty-only
offer; it is not a theorem that each admission increases concrete FL.
Unknown reads and protocol over-approximations can produce MAY again.
The proof dossier contains 79 audited constructive declarations across
four modules; it separates these results from native adapter obligations.

Before implementation acceptance, compare native C2, its structural raw
image, C5, trie/packed storage, loops and both arrival orders with the
reference. Include marks/mx/E/H, static anchors, arrays, MUST, ND, Targets,
source permissions, the two-loop/no-leave cases, and the historical two
Conductor findings. Re-trace those programs with this emitter and NE cuts;
old-policy traces are not new-policy counterexamples or acceptance results.
Run the finding-preservation regressions without an iteration cap.

Measure repeated post-handoff rows, exact/STAR/MUST starts, NE/MAY cuts,
summary delivery, fixed-point work, time and peak memory. State the latest
reached/completed/accepted forward iteration. No project was scanned for
this specification. Historical positions remain OWASP **run-11/11/11**,
Conductor **run-8/7/7**, Stirling-PDF **run-11/10/9**. Neither those capped
positions nor the tail laws prove a speedup or natural convergence.
