# Demand refinement and termination

This specification defines bounded refinement and demand retirement in
FULL mark mode of the bidirectional access-path analyzer. Run forward at
limit 1 in run-1, backward at limit 1 in run-2, then alternate direction
with limits 2, 3, …. A policy cutoff is separate from natural termination.

## 1. Domain and processing order

`p.f.K/m,L` means base `p`, field chain `f`, tail `K`, mark `m` and layer
`L`. The tails are exact point `$`, correlated suffix `*`, possible suffix
`M`, nonempty possible suffix `NE`, and uniform region `MUST`. FLOW is
`F`, a full concrete mark is `T`, and the layers are NORMAL and DEMAND
(`N/D`). `E` excludes fields at its own head, `mx` excludes marks from FLOW,
and `H` is the literal protection flag. Examples use empty exclusions and
plain H unless shown. A field chain counts field and array accessors.
Static class anchors count as zero fields and remain indivisible.

For a field alphabet Σ, a head denotes the suffix sets `$={ε}`,
`M=Σ*` and `NE=Σ+`. A NORMAL STAR relation carries **the same** admitted
suffix from its premise to its conclusion. MAY and NE conclusions can
choose an independent suffix. MUST asserts support at every represented
point, subject to E. The STAR binding used by C2 queries the nonempty
case. This choice does not change ordinary STAR application.

A query owns EXACT or STAR initials, with the existing forward MUST
exception. A result or offer can also have M or NE. A frozen entry
selector can have STAR, M, NE or concrete EXACT. A paired exit selector
can have STAR or EXACT, with the existing uniform and virtual MAY cases.
An executable DATA premise, including an ND member, and an ordinary
paired exit selector cannot have NE or M. The virtual MAY exit comes
from the native projection. Backward MUST initials are invalid. ZERO, DemandTarget (DT)
and NormalTarget (NT) are typed controls outside DATA.

An owner is a method or generated block. The comparison frame contains
owner and revision, direction, complete original premise, physical ports,
stage and resolved continuation. Equality also checks base/path/tail,
mark, E, mx, layer and H where applicable. Keep `H=0` and `H=1` as
separate memberships. A pass carries H and does not create it. An ND
application needs every arm in one binding. Handoff may project arms into
guidance, while the executable premise stays AND. Run-1 retains its selected
singleton-origin approximation and produces ZERO only from an all-ZERO
witness. For example, equivalent plain/protected `p.f.$/T` remain separate,
and one arm of `CM(p,T) AND CM(q,U)` cannot produce the later-run result.
These constraints apply at storage, application and handoff (R29/R30).

```text
on offer: apply saved NORMAL to the original actual
          prepare the complete current C2 plan
          if nonempty, install starts and apply/subscribe in that binding
          resolve effects and fold ready replies before their continuation
in owner: schedule ready exact/control/NORMAL work before uncertain work
          execute rules and transfers, including the usual global cuts
at exit:  run boundary effects, test NORMAL precoverage, then paired C5
          retire proved covered rows and capture qualified DEMAND heads
          publish the canonical executable packet
at seal:  finish each owner's closure and recheck the final provider basis
          persist admitted NORMAL records
          project native-selected qualified DATA and typed Targets
          omit only certified unused guidance, then test the native frontier
```

Keep existing strong overwrites, field and mark guards, aliases,
condition evaluation, ports, block liveness and source permissions.
For run-2, run-1 static completion and shared carry supply virtual
pairs to C2 and C5. Include static Target lookups, lost-write guides,
scoped static shortcuts, preflight and the frontier test in the same view.
Keep each pair's physical owner route, anchor, selected mark label and
output budget. Keep the native positive `NO_DEMAND_EDGE` behavior. For
example, `ZERO→C.f/T` and `C.f/T→DT` can supply a virtual `ZERO→DT`
guide. Check equivalence with the native static view before activating
an NE-aware adapter. Use transitive lookup for these pairs without
materializing the closure.

An already reached backward exceptional ZERO also tests the normal
control view. Return a borrowed `ZERO→DT` to the genuine normal
invocation address. This view supplies no standalone seeds and changes
no DATA ports. Loop consumer probes use the same C2/C5. The own-ZERO
loop exception applies only to the additional growth gate.

Use restricted C2 and C5 from run-2 onward. Run-1 uses unrestricted
admission and its ordinary publication. Apply rules that explicitly cover
run-1 to those transfers. The selected changes cover tail and cut
semantics, restricted admission and publication, proven reply suppression,
cleaner transfer, and sealed demand retirement. They can change demand,
report timing and delivery counts. Selected EXACT cleaning of concrete
MUST has the explicit precision tradeoff in §5.

## 2. Field transfer and C2

| Rule and affected part | Required behavior and principal example | Proof |
| --- | --- | --- |
| R01–R03 · DATA grammar, cut, transfer, handoff | A real cut emits NE. A cut of `x.f.g.h.$/T` at limit 1 gives `x.f.NE/T,D`, with empty E and the same mark, mx and H. Apply at every existing real field cut, including run-1. Uncut M stays M. For `y=x.f`, `x.NE` gives `y.M,D`, `x.f.NE` gives `y.NE,D`, and `x.$` gives no y. For `x.f=y`, keep `x.f.M` from `y.M` and `x.f.NE` from `y.NE` while f fits. If f is cut, both give `x.NE,D`. An intrinsic MAY supply can include the root. | The removed suffix has a first field, and its old point lies in the retained head's NE region. An unknown read can consume the entire suffix. An uncut write can put the former root at the newly named field. |
| R04–R06 · C2, call binding, raw C5 | For same-head `p.M/T ← p.M/T`, start `p.$/T,D` and `p.*/T,D`, plus the conditional FLOW companion. NE keeps the nonempty case. A frozen `p.f.M` row can use a compatible ancestor `p.*` as a **possible** offer, within its prepared budget. Keep the real caller binding. | Empty and nonempty suffixes exhaust M. Each primary authorizes only its stated companions. Guessed binding support joins as D, so neither a FLOW hypothesis nor possible admission confirms NT. |
| R07 · C2, raw C5 | `p.M/T ← p.f.MUST/T {g},N` starts `p.f.*/T,D` and its FLOW companion. Carry `{g}` on both STAR starts at the unchanged actual head. Apply only in restricted FULL for a concrete demand and a STAR or MUST actual. | At the same head the copied mask denotes the same forbidden subtrees. E cannot move to another head. The map adds no seed and changes no start layer. |
| R08 · C2, raw C5, field limits | For `p.M/T ← p.f.g.MUST/T {g},N`, replace the two eligible shorter STAR starts by `p.f.g.*/T,D` and `p.f.g.*/F,N`, both with `{g}`. Keep the conditional `p.$/F` probe. | The actual head and holes stay together. Every overrun of Dc+1 comes from the certified map below. The global and paired output caps still hold. |
| R13 · raw transfer | For `x.f.g=new Node()`, reject the strict-descendant keep at `x.f.*` per leaf when the actual is `x.$/F`. The keep at `x.* {f}` still yields the exact root with `{f}`. | No strict descendant lies in the exact point. The same-head keep records the real overwrite exclusion before normalization. |
| R32 · run-2 C2 and raw C5 | Start the requested STAR identity in backward run-2 for a same-head precise STAR demand and STAR actual. `set(p){ p.f=new Node(); return p; }` through wrappers can then produce the NORMAL relation with `{f}` and preserve `p.g/T` at run-3. Retain the existing admitted deeper-actual run-2 STAR case. | Same base/head requires no extra field. C5 uses the same raw family. The wrapper proof relays NORMAL service through any finite number of wrappers. |

C2 first checks legal geometry, direction, base, mark and global limit.
A concrete demand T matches T. A FLOW demand uses empty mx at handoff.
Actual and saved-record masks retain their own meaning. Normalize selector E
only in the existing abstract FLOW/STAR case. For the **same head**, emit
the following raw identities. MUST entries in the last column require a
legal forward uniform actual.

| Dc | Actual $ | Actual * | Actual M | Actual NE | Actual MUST |
| --- | --- | --- | --- | --- | --- |
| Concrete $ | $ | ∅ | $ | ∅ | $ |
| Precise STAR | $ | STAR in run-2 only | $ | ∅ | $ |
| M | $ | * | $ and * | * | MUST |
| NE | ∅ | * | * | * | MUST |

If the actual extends Dc, reject under precise $ and under precise STAR
after run-2. Under M/NE, stop at the first new counted field `r`. A
longer head starts `r.*`. An actual at r starts `r.$` for EXACT,
both for M, and `r.*` for STAR/NE/MUST. For an ancestor actual, check
its own E at the first field of descent. EXACT cannot descend. M/NE
can descend and use residual M at Dc. MUST uses its native uniform
descent. An ancestor STAR is possible only for an eligible M/NE selector
or its prepared child in the frozen plan, within that row's budget.
Incomparable heads reject.

Every successful concrete STAR start gets the same-shape N FLOW
companion. A successful deeper actual under MAY also gets a conditional
EXACT/FLOW probe at Dc. Build NE from the complete MAY family and remove
all EXACT starts at NE's original head, including that prefix probe.
FLOW starts have empty mx and structural N support. Concrete STAR starts
D. Concrete EXACT/MUST starts N only with definite actual N support.
Keep the real layer and H on resume, including possible admission.
Deduplicate by raw initial and starting support. A failed primary emits
no companion.

An ordinary entry obeys `FL(I) ≤ min(global, FL(Dc)+1)`. The sole
exception is an eligible Empty-E STAR command in a **restricted forward
FULL** concrete M/NE family whose actual is the same T, NORMAL MUST with
nonempty actual E, and whose actual head strictly extends that command at
the same base and fits global. Replace the head and E together, including
its FLOW companion. Apply all ordinary member and output caps.

Preserve the required service of each command that these rules replace.
R07/R08 can affect other bindings as well as the triggering actual. For
example, replacing hole-free `p.f.*/F` with `p.f.*/F {g}` can remove a
guide for another offer. Check that consumer against the retained binding
and its paired C5 row before replacing the family.

## 3. Prepared children, replay and paired C5

| Rule and affected part | Required behavior and principal example | Proof |
| --- | --- | --- |
| R09/R10/R23 · demand preparation, publication, handoff | For `P→p.M,D` and `P→p.f.NE,D`, executable union can hide f. Capture the bounded post-C5 child before executable union. Use f from a deeper row with the same paired Dp or an eligible saved NORMAL guard; `p.f.g.*` contributes f only. Prepare `p.f.$` and `p.f.*` when compatible. | M contains NE for execution. At the same head the NE query family is contained in MAY's under identical qualifiers and budget. A deeper head can admit an extra concrete field that the parent cannot. A child NE alone also misses its exact boundary point. |
| R11/R12 · primitive transfer, saved replay inside queries | In `y=x.f`, route the `x.*→y.M,D` contribution for f through an already ready complete child only with the service proof in §6. Apply the same rule to supported saved NORMAL reads inside the query, even if current callee demand is empty. | A matching unknown suffix begins with f. Its residual belongs to the child point or child suffix. The child's qualified proof must supply all real effects and every consumer's paired output service. |
| R14 · call/block coordination | Reuse saved-first replay. If `id` has saved `p.*→ret.*` and no current demand, `p.f.$/T` still gives `ret.f.$/T`. Reuse the caller's C2 plan at the owner. | Original actual and resolved effects preserve the saved route. An empty plan only disables current-query service. |
| R15 · saved matching, actual delivery | A saved `p.MUST/T→ret.MUST/U` can supply a provisional reply from `p.f.MUST/T`. Suppress that reply only after the continuation check below. Apply definite MUST matching and prepare current C2 as usual. | The child does not prove support at p. At equal heads definite matching needs `actual.E ⊆ required.E`. An actual ancestor must admit the first descent. Definite replies preserve NORMAL support. The continuation check preserves required service from provisional replies. |
| R34 · saved matching, ordinary caller caps | For a same-direction saved NORMAL FLOW `p.f.*→ret.*` and a shorter `p.*` offer in a restricted run, use a possible read if the ordinary scalar match fails and yield `ret.M,D` at the saved result head, Empty E, with native mark/H/binding and guards. | A compatible suffix beginning in f can satisfy the guard, but a shorter STAR supplies no definite choice. Existing hits are unchanged. The possible reply can guide a later NORMAL return. |
| R18 · summary emission before relative C5 | A learned NORMAL `p.*→ret.*` already returns the whole `p.f.g.*→ret.f.g.*` specialization. Skip the redundant publication only with retained NORMAL unary FLOW STAR service whose exact native image equals the whole candidate and fits global. | Native whole-image equality gives the same suffix, masks, tail, ports and layer. Run rule/exit effects first. Genuine global cuts and a candidate that depends on a different binding remain. |
| R20–R22 · summary restriction and normalization | Under `Dc=p.NE/F`, C5 rejects raw `p.$/F` even though it shares public `p.*/F` with an allowed raw STAR. Select with the row's own Dp, cut to its own limit, then publish admitted pairs. | Raw membership constructs an actual legal C2 command for that row. The scalar selection preserves each point in the paired intersection. Conditional FLOW EXACT-to-STAR needs a suffix-lifting witness, including real write E. |

Choose first fields without recursive expansion in the same preparation.
For one legal base family, preparation adds at most two probes per observed
field. Preserve each child's owning row, flags, ports and budget. Freeze
readiness for a shared raw query only when all its possible issuing
consumers, including later arrivals, have complete child service. Route supported primitive reads with the complete child proof. For a saved
inside read, require an Empty-E/mx STAR/FLOW query, a still NORMAL correlated
STAR/FLOW operand with empty mx, and a unary unprotected NORMAL FLOW
STAR-to-STAR record with empty mx. Operand and saved endpoint E stay at
their original heads. The saved view is opposite-direction or uses R34. Keep independent effects, unsupported aliases,
concrete, protected, MUST, DEMAND and ND outside that routing. Outer saved
replay uses the original actual. R34 may omit only its new contribution
when an already prepared child fully covers it. The R34 lane does not
create a new query and must participate in any later closure check.

Use the definite MUST matcher for saved calls, blocks, loops and service
probes. Under R15, omit a nondefinite saved reply only if every required
use of that reply is served, including later guidance from a DEMAND
result and a caller with empty current C2. Otherwise retain the native
reply. Preserve full ND binding and native port and alias behavior.

For R18 the retained saved provider's input prefixes P and admits the
whole P region. Its image keeps P's tail and exact native guards. Check the
skipped row's uses in publication, current delivery and handoff. Using a
current-only provider requires complete committed service to every
affected subscriber.

```text
C5(rawP, rawC):
    for each compatible scalar pair (Dp -> Dc) at this owner and port:
        if rawP is outside the complete prepared raw C2 image of Dc: skip
        (p,c) = normalizeFLOWPair(rawP,rawC)
        b = selectExit(c,Dp)
        if b exists:
            emit normalizeFLOWPair(p, cut(b, min(global,FL(Dp)+1)))
```

Split packed chains before pairing. Preserve the owning row on each leaf.
The raw image uses legal hypothetical offers and the exact C2 rules
above, including companions and head retention. It does not depend on an
input history. ND uses its existing member entry test and keeps the complete
premise. Normalize EXACT endpoints to STAR only for a complete singleton
FLOW-to-FLOW pair, preserving each path, E, mx, layer and H. Keep the native
ND/control rules. The two normalizations occur after the raw entry check.
All fresh restricted-run DATA summaries, including NORMAL, use the
paired output cap. Include the qualified virtual pairs in run-2.

Activate raw checking and the C2 plan together. For a native admitted
summary or start that the new plan rejects, prove that a legal retained
route serves every needed use of it. A normalized STAR key alone cannot
justify a raw EXACT command under NE. A proof uses one complete paired
row for each new admission/publication, including its companions and
output cap. If the bridge is missing, use native admission and publication
for the affected scope under §6.

`selectExit` first checks equal bases and intersecting marks. It retains
the candidate mark, mx, layer and H. At the same head keep EXACT or correlated
STAR whole. M becomes EXACT for exact Dp and stays M otherwise. NE rejects
exact Dp and stays NE otherwise. MUST becomes EXACT for exact Dp, joins E
for STAR Dp and stays MUST otherwise. Concrete EXACT has empty E. The
same-head abstract EXACT selected from MUST retains its required E.

If the candidate is below Dp, keep it only when Dp's tail and E permit
descent. If Dp lies below the candidate, require the candidate to permit
descent. EXACT rejects; STAR stays whole; M/NE rebase at Dp as M or as
EXACT for exact Dp; MUST rebases uniformly or as EXACT for exact Dp.
Use Dp's E at a uniform rebased STAR selector and Empty E otherwise.
Incomparable heads reject. A selector never produces a new concrete mark
or upgrades support. Ordinary Dp cannot be NE.

## 4. Reply and summary coverage

| Rule and affected part | Required behavior and principal example | Proof |
| --- | --- | --- |
| R16 · applied ready reply packets | A definite `ret.MUST/T {f}` can be delivered twice with N and D. Fold D into identical N before continuation, as for definite EXACT. Compare the whole key, including H and resolved alias/identity continuation. | N proves the same points at the same location, with the same continuation. Resolve real effects first or keep separate continuations. A raw NORMAL record or a D actual is not a provider. |
| R17 · post-statement actual DATA, ready delivery | A ready `x.h.MUST/U,N` can cover `x.h.M/U,D` from an alternating T/U generator. In forward FULL omit the D actual only after the continuation check below. | Every candidate point has the same-mark, same-H witness already bound in the continuation. Positive derivation induction keeps every whole AND premise. Raw C2 image equality is not required or claimed. |
| R19 · current reply delivery only | Omit the current `p.f.*→ret.h.M/U,D` delivery only if the owned query serves every relevant h return and the continuation check passes. A disjoint k/V or k/U return can fail C5; it remains in internal closure but adds no h obligation. An H=1 actual may use its own bound H=1 service. A NORMAL MUST actual can use its existing uniform query. | Induct on the complete owned graph to include every true return. Each selected return has a whole committed NORMAL image in the same native binding. A missing, partial, wrong-port or wrong-H receipt blocks omission. |
| R24 · post-C5 summary, execution and handoff | Same `P=MUST`: `P→a.u.MUST/T,N,H=1` covers `P→a.u.f.NE/T,D,H=1` with the guards below. Check next-run guidance before removing the NE row. | Every NE point is within the uniform region of the same original. Equality of qualifiers and H preserves its application witness. A cut provider cannot serve it. |
| R25/R27 · publication, ready queues, compaction | If `A` covers `B` and `B` covers `C`, retain a final service witness for C even when C arrived first. Process ready exact work and its summaries before uncertain work per owner, with control-enabling work, legal MUST and ready NORMAL providers in the high lane. Use FLOW first within a lane. When a ready exact reply and its uncertain counterpart share a consumer, publish the exact service first. | Witness substitution is transitive. Requiring a final retained basis prevents joint deletion cycles. Fair sound stores closed under the same positive rules have the same least result; callback counts may differ. |

For actual coverage in R16, use FULL concrete EXACT with empty E or MUST
with equal E, empty mx, and equal continuation, original, flags and geometry.
Run ordinary same-layer MUST folding first. For R17 the provider must be
a ready NORMAL MUST actual. The candidate is concrete EXACT/MUST/M/NE on D.
With the same head, the provider covers the exact root, MUST when its E is
a subset of the candidate's E, and M/NE only with empty E. A descendant
must start outside the provider's E. Other heads reject. Keep exact and MUST
membership where existing admission needs both. Store results after the
processed statement. A late provider can remove a pending membership
once its complete continuation is covered. Independent effects and
emitted Targets stay accumulated.

For R16, R17 and R19, and for R24 at publication or handoff, check
continuation service as well as point coverage. Include dependent C2/C5,
rule effects, typed Targets, source permissions and later guides. For
example, ready NORMAL coverage from source A can share the ZERO original,
mark and observer with B's only DEMAND route. Keep B's member until
every needed use has committed service or a verified retained route.
Check before the first affected delivery or publication. Use the
qualified service views in §6 without adding origin labels to DATA.

R19 requires forward FULL after run-2 and an **already owned** NORMAL
concrete EXACT (Empty E/mx) or MUST (actual E, Empty mx) query. Establish
closure over its complete uncut strong transfer graph, including internal
other marks, all H values, children and unpublished boundary states.
Unknown effects, pending dependencies, internal cuts or unresolved D
prevent closure. A child's mark/region certificate cannot prove its full
transfer. For each applicable unary non-ZERO current concrete D return,
check every possible overlapping return in its native bound H class
against whole, already applied N service. Partial overlap requires whole
coverage. Unknown FLOW that can contain the mark is relevant. Use only
supported transfer adapters. Omit just that delivery. Owner records and
handoff demand stay. The proved positive-unary leaf adapter supports fresh
returned objects, marking rules, allocation/return and caller field reads.
Reuse the guarded whole-query, per-mark and plain-region fast paths on
their existing scopes; sparse positive mark flags reference existing
return classes. Keep no per-region cache, and do not wait for future replies.

R24 requires forward singleton MUST original, nonstatic common output
base, empty E on original and both outputs, diagonal FLOW or same-T
concrete marks, equal output mark/mx and literal H, and equal qualified
frame. If R18 replaces the provider, use a temporary definite native
image through the same C5 and require that it remains NORMAL MUST.
Do not store this image. R17 and R24 serve different consumers.

Reuse aligned NORMAL FLOW specialization with identical suffix extension
at both endpoints and real mask/overlap checks. Reuse diagonal FLOW-backed
same-tail marked coverage for eligible plain edges. No STAR coverage of
independent M/NE follows from this. Same-layer MUST union fills an excluded
field only with its complete immediate child with empty E. For instance,
`x.*→y.*` can cover `x.f.*→y.f.*` with the same admitted suffix, but cannot
cover `x.f.*→y.g.*`. At handoff keep existing weaker-premise/same-result
and concrete STAR/EXACT service compaction only if the full updated C2/C5
service agrees, including all ND projections; the latter equivalence is
outside run-2. Recheck against the final basis. Individual redundancy
alone gives no joint deletion permission.

## 5. Cleaners, controls and handoff

| Rule and affected part | Required behavior and principal example | Proof |
| --- | --- | --- |
| R26/R35 · concrete cleaner transfer [selected coarsening] | For selected EXACT cleaning of T at `x` or `x.f.g`, a matching same-base `x.MUST/T` keeps its region, original support, E and cleaner-survivor H. Nonuniform exact T still dies at the selected point. | Split along the cleaner path and use the selected same-head policy at the final child. Union with its siblings reconstructs the original region. This explicitly retains a possible observation at the selected point. D stays D. |
| R36 · concrete cleaner transfer after run-1 | For NORMAL `x.MUST/T` cleaned ALL at `x.f.g`, emit `x.MUST/T {f}` and `x.f.MUST/T {g}`, normally. Selected BELOW also retains `x.f.g.$/T`. Apply the usual caps. | Partition into one residual sibling region per field plus the optional point. The union is exactly the input minus the selected subtree. There are at most depth+1 pieces. |
| R31 · FULL nonstatic FLOW cleaner, all runs and directions | For `clearExactT(p); return p.g;`, keep the original headers of every path whose whole suffix cone is disjoint from the cleaner. Mask the remaining leaves as before. Cleaner at `p.f` still masks an abstract point probe at p because its normalized suffix can include f. | For EXACT, the cleaner head lies in the cone iff the input head prefixes it. For BELOW/ALL use prefix incomparability. This guard covers normalized suffixes too. The getter relays `p.g.h/T` with its original mark support. |
| R28/R33 · typed controls, handoff and stopping | Reuse the existing paired DATA/Target projection. FLOW masks are cleared on both demand endpoints only. For `p→ret/F, mx={T}`, demand can guide FLOW admission, while saved replay still excludes T. DT still counts when DATA is empty. | Mask projection is idempotent and preserves all other coordinates. Controls carry their own witness and accumulate independently of DATA compaction. Stopping requires the full frontier to be empty. |
| R37/R38 [REC] [LOOP] · terminal receipt, handoff | Omit a root ZERO→DT only with frozen service for every source/full-mark/observer relation and a proof of all other uses of that control key. One ID can report from a shallow source at run-3 while its deeper source first reaches the same observer at run-5. Keep guidance for the deeper source. | Induct over terminal derivations through relays. OR of unresolved leaves is false only if each leaf's complete source catalogue is served. A valid origin cannot use another origin's witness. |
| R39 [REC] [LOOP] · origin certificate at seal | Certify an empty product for validated regular word languages, including eligible loops. Recursive writer words `{g,h}*f` and reader words `{g,h}*g` have an empty product. | A common word induces a simultaneous automaton path to an accepting pair. A closed reached set with none rules out that word at every depth. |
| R40 [REC] · origin certificate at seal | Admit one nested clause side against a regular other side. Writer `g*f` and reader `R=g or g·R or h·R·h` are disjoint. With writer word `h.g.h` the nested arm supplies a real observation, so keep guidance. | Induct on a nested word derivation. Split its regular run at prefix/child/suffix. A closed owner/state-pair relation contains its endpoints. A real matching outer suffix would reach an accepting state. |

R36 applies to the partially intersecting NORMAL concrete MUST region in
FULL after run-1. At each selected field retain the current head with that
field excluded, then recurse into the field with empty E. Stop if that field
was already excluded. Kill a wholly cleaned subtree as before. At the last
head keep an exact point only for selected BELOW; ALL removes it. Use
existing H, original, mark and layer. Whole-position RemoveAll and legal
field-position ALL use this spatial rule. Below-only RemoveAll remains
invalid. For R31 leave existing mark requests and cleaner ownership in
place. Partition packed paths by the stated prefix test and add the
selected marks to mx only on the remaining leaves. At most two packets.

For R28/R33, select admitted DATA whose layer is D, whose original is
ND, or whose original is singleton ZERO in backward. Apply the native
selection to methods and scoped blocks. Backward executable ND is
invalid. For example, backward `ZERO→x.f.$/T,N` in a loop's after block
provides the next forward C2 guide at that block. Project each selected
pair with its physical ports and original pairing. NE remains NE in Dc. Use only existing forward MUST
guidance projection and reverse views. Persist admitted NORMAL records,
including real E/mx. Target entries admit ZERO, and a paired ZERO exit
permits ZERO or Target. Use existing backward ZERO-to-Target relations and
source permission rules. NT composes only with NORMAL and is ignored
backward. Keep NT IDs, existing duplicate rules and observations. These
rules do not change the conditions under which a run emits a Target.

For R37/R38, freeze the set of proved closed goals at forward start.
A goal includes observer identity, its full-mark/position predicate, and
the graph and rule version. Each predicate sharing an ID needs its own
proof. A local Target origin contributes `goal ∉ frozenClosed`, or true
for an unknown origin. Relays pass this bit and alternatives OR it.
Publish a late false-to-true upgrade even when the terminal key is already
stored. Join all upgrades. At completed FULL forward handoff, omit only
the configured method-root ZERO→DT when accounting is complete and the
bit is false. Also prove that every required use of that root key for
admission, seed activation and future guidance is already served or has
another retained route. Terminal origin accounting alone cannot certify
an unrelated or latent consumer. Each key needs at most its first
notification and one upgrade. Use a closed-goal proof at the next forward
start. One unserved origin keeps the whole anonymous row.

A complete catalogue includes every possible marking point and its bindings.
For each point require a retained actual root NORMAL path to the same
observer or a validated NoRoute result. Complete upper graphs may prove
absence with fields forgotten. Bounded summaries alone cannot prove absence.
Conditional NORMAL rows, an early NORMAL GEN before a cut and another
source's report do not establish service. Retain only the frozen result and
terminal bit, with temporary views of existing states and records.

For R39/R40 require complete pure FLOW route extraction, including every
branch, resolved target, all source aliases, bindings and actual observer
ports. A normal return does not represent an internal observation by itself.
For source field word `a` and exact observation word `q`, solve
`writerWord·a = readerWord·q`. Regular clauses are base words or
`prefix·B`. A nested clause can use `prefix·B·suffix` on one side only.
Reverse writer loop instruction order for prefix writes; preserve reader
order. In a two-sided writer, fields prepended after the call come first.
Append a/q at regular base clauses. For the nested side append the outer
suffix **after the whole word**. For example, a nested `g·B·f` with B
empty and source h gives `g.f.h`; appending h to B incorrectly gives
`g.h.f`.

For regular sides validate every clause and traverse the synchronized
same-field product. Return Unknown on a cross-owner empty-word transition
unless its epsilon elimination is proved. For one nested side, use the
regular automaton's word transition `step`. Seed `(A,p,q)` where base(A)
can move p to q.
For `A→u·B·v`, an existing `(B,m,n)` adds `(A,p,q)` when
`m∈step(p,u)` and `q∈step(n,v)`. Check closure and absence of an accepting
start-owner cell after consuming the outer suffix. The product has at most
`Qw·Qr` pairs. The nested check has at most `M·Q²` cells for M owners and
Q regular states. Index clauses by child and solve the finite closure.
A possible word, incomplete code extraction, unsupported
effects or two nested languages leaves guidance in place. NoRoute creates
no NORMAL report or source permission.

## 6. Proof and activation

A service obligation identifies its run and stage, owner and revision,
physical ports, original, mark, exclusions, protection and exact effect.
Include required queries, publications, Targets, source permissions,
aliases, rule effects and source-specific observations. These coordinates
identify proof witnesses in native events.

For each changed branch, validate all affected seeds and native actions
in its complete scope. Check a finite replacement derivation for each
needed service. Each step must use an available permitted native transfer
with all of its inputs in the same valid binding. Respect run and stage
order. End every recipe in the final retained basis after all simultaneous
deletions. At a stop, require materialized witnesses and discharge every
remaining native continuation that could supply a required track.

The preservation proof substitutes the checked recipes into each finite
native derivation by induction. An AND derivation requires witnesses for
all members. At a natural stop, closure of the sealed result supplies
the materialized tracks. For termination of an example, show within-run
closure and an empty full frontier, or prove an inductively quiet suffix.
A bounded execution cannot prove natural termination without that
certificate.

Before activation, establish native correspondence for the complete scope.
The proof must cover the following parts.

1. **Future admission.** Preserve each later needed C2 route or provide a
   complete alternative service.
2. **Native service.** Match real ports, packed leaves, aliases, full ND,
   rule effects, readiness and caps.
3. **FLOW normalization.** Transport the same suffix under the actual
   guards for every normalized NORMAL form.
4. **Delivery and stop.** Preserve paired publication, static views, block
   exits, loop gates, source permissions and the full frontier test.

Select native processing for an uncertified connected analysis at its
start. Use local native fallback only with a checked adapter for incoming
boundaries and earlier history. A failed optional suppression retains its
original reply or guide. Unknown terminal scope keeps its ZERO→DT row.

[Constructive rule proofs](lean/proposals/demand-refinement-spec-20261117/README.md) ·
[Joint service proof](lean/proposals/demand-no-loss-audit-20261117/README.md) ·
[Termination examples](../docs/reports/bidirectional-demand-termination-counterexamples-20261115.md) ·
[Validation](../docs/reports/bidirectional-termination-fix-validation-20261117.md)
