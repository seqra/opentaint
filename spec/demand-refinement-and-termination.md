# Demand refinement and termination

This specification defines bounded refinement and fact handling in
FULL mark mode of the bidirectional access-path analyzer. Run forward at
limit 1 in run-1, backward at limit 1 in run-2, then alternate direction
with limits 2, 3, …. A policy cutoff is separate from natural termination.
In the examples, **current** means the native FULL rules at `8da26aa13`.
**Proposed** means the analyzer operations defined below.
For a proposed-only tail, the current column gives the corresponding
native case and names the substitution.

**COMPLEX** marks additional cross-row preparation or closure work.
Local tail cases and existing native lookups keep their ordinary
classification. For each COMPLEX candidate, compare its recorded fixture with the
candidate withheld. A bounded run supplies diagnostic evidence.
An uncapped claim needs a repeated frontier and inductive proof in the
stated model. A simpler rule that discharges the same fixture is
sufficient reason to withhold the heavier computation.

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
choose an independent suffix. NE excludes the empty suffix and carries
DEMAND support. M and NE have empty E. MUST asserts support at every
represented point, subject to E. C2 classifies a same-head STAR offer
under M/NE as supplying the nonempty branch only. In ordinary application,
STAR still admits the empty suffix. A strict descent through STAR/MUST
checks the first accessor against E at its head. EXACT admits only empty.
M admits any suffix and NE admits any suffix with at least one field or
array accessor. Compose support as D if any participant is D or the
binding is only possible.

| Role | Allowed tails |
| --- | --- |
| Raw initial or executable DATA premise member | EXACT, STAR, and the forward MUST lane |
| DATA conclusion or incoming actual | EXACT, STAR, M, NE, and MUST where the native direction permits it |
| Frozen demand entry Dc | STAR, M, NE, or concrete EXACT |
| Paired demand exit Dp | EXACT, STAR, forward-origin MUST, or M in a native virtual view |
| Saved NORMAL record | Only eligible native NORMAL shapes, with no NE endpoint |

NE and M never serve as owned initials, executable premise members or
record read premises. An ordinary reversed demand pair can have NE at
its entry Dc only. Backward MUST initials and actuals are invalid.
ZERO, DemandTarget (DT) and NormalTarget (NT) are typed controls outside
DATA. A concrete static AP has a named JVM class/field anchor, or an
EXACT class marker. Validate restricted run-2 concrete static actuals
at the usual handoff after the global cut. A named field can now supply
NE/D with empty E, as well as the existing EXACT, M and correlated STAR
shapes. An EXACT class marker still has empty E. No cut or rebase of
a concrete static AP can invent a broad root or class mark.

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
Tail, layer and H distinguish logical fact and summary memberships,
including packed leaves. Starting support distinguishes query processing
memberships but does not change the interned AP key. Row ownership,
possible-binding annotations and proof receipts are control data outside
fact equality and hashing.

```text
on offer: apply saved NORMAL to the original actual
          prepare the complete current C2 plan
          if nonempty, install starts and apply/subscribe in that binding
          resume saved/current replies with their native effects
in owner: schedule ready exact/control/NORMAL work before uncertain work
          execute rules and transfers, including the usual global cuts
at exit:  run boundary effects and paired C5
          retain distinct admitted MAY and NE rows
          publish the canonical executable packet
at seal:  finish the native worklist and publications
          persist admitted NORMAL records
          project native-selected qualified DATA and typed Targets
          compact qualified DATA rows and test the native frontier
```

Keep existing strong overwrites, field and mark guards, aliases,
condition evaluation, ports, block liveness and source permissions.
For run-2, run-1 static completion and shared carry supply virtual
pairs to C2 and C5. Include static Target lookups, lost-write guides,
scoped static shortcuts, preflight and the frontier test in the same view.
Keep each pair's physical owner route, anchor, selected mark label and
output budget. A completed forward run has reason `NO_DEMAND_EDGE`
when its full outgoing guidance is empty. For
example, `ZERO→C.f/T` and `C.f/T→DT` can supply a virtual `ZERO→DT`
guide. Check equivalence with the native static view before activating
an NE-aware adapter. Use transitive lookup for these pairs without
materializing the closure.

An already reached backward exceptional ZERO also tests the normal
control view. Return a borrowed `ZERO→DT` to the genuine normal
invocation address. This view supplies no standalone seeds and changes
no DATA ports. Loop consumer probes use the same C2/C5. The own-ZERO
loop exception applies only to the additional growth gate. That gate
checks a growing DATA relation at a loop boundary against the repeat or
leave consumer and the enclosing continuation. Its result uses the same
paired selector and cap as other block results.

Use restricted C2 and C5 from run-2 onward. Run-1 uses unrestricted
admission and its ordinary publication. Apply rules that explicitly cover
run-1 to those transfers. The selected changes cover tail and cut
semantics, restricted admission and publication, and cleaner transfer.
They can change demand, report timing and delivery counts. Selected EXACT cleaning of concrete
MUST has the explicit precision tradeoff in §5.

### COMPLEX

The scheduler and block layout reuse the native engine. They add no
separate termination search in this section.

### Examples diff

| Rule and input | Current | Proposed |
| --- | --- | --- |
| R29. Pass `p.*/F→ret.*/F,N` on memberships `{p.f.M/T,D,H=0; p.f.M/T,D,H=1}`. The proposal has the corresponding NE actuals. | `{ret.f.M/T,D,H=0; ret.f.M/T,D,H=1}` | `{ret.f.NE/T,D,H=0; ret.f.NE/T,D,H=1}`. Each input keeps its flag. |
| R30. Later-run summary `{p.$/T,q.$/U}→ret.$/V,N` with only `p.$/T,N` supplied to its binding. | Replies `∅`. | Replies `∅`, even if p has its own projected guide. |
| R30. Same summary with both `p.$/T,N` and `q.$/U,D` in one binding. | `{ret.$/V,D}` | `{ret.$/V,D}` |
| Static completion. Run-1 rows `{ZERO→S.C.f/T,D; S.C.f/T→DT,D}` in a qualified scope. | Run-2 virtual guide `{ZERO→DT,D}`. | Run-2 virtual guide `{ZERO→DT,D}` with the same owner and port. |
| Control port. Backward actual `ZERO,N` reached at a block's exceptional entry, with a normal `ZERO→DT,D` guide. | Borrow normal entry service and publish `{ZERO→DT,D}` at the normal invocation. | Publish `{ZERO→DT,D}` at the same normal invocation. An actual `p.f.NE/T,D` gets `∅` from that control-only guide. |

## 2. Field transfer and C2

| Rule and affected part | Required behavior | Proof |
| --- | --- | --- |
| R01–R03 · DATA grammar, cut, transfer, handoff | A real cut emits NE. A cut of `x.f.g.h.$/T` at limit 1 gives `x.f.NE/T,D`, with empty E and the same mark, mx and H. Apply at every existing real field cut, including run-1. Uncut M stays M. For `y=x.f`, `x.NE` gives `y.M,D`, `x.f.NE` gives `y.NE,D`, and `x.$` gives no y. For `x.f=y`, keep `x.f.M` from `y.M` and `x.f.NE` from `y.NE` while f fits. If f is cut, both give `x.NE,D`. An intrinsic MAY supply can include the root. | The removed suffix has a first field, and its old point lies in the retained head's NE region. An unknown read can consume the entire suffix. An uncut write can put the former root at the newly named field. |
| R04–R06 · C2, call binding, raw C5 | For same-head `p.M/T ← p.M/T`, start `p.$/T,D` and `p.*/T,D`, plus the conditional FLOW companion. NE keeps the nonempty case. A frozen `p.f.M` row can use a compatible ancestor `p.*` as a **possible** offer, within its prepared budget. Keep the real caller binding. | Empty and nonempty suffixes exhaust M. Each primary authorizes only its stated companions. Possible field binding joins as D. A FLOW hypothesis alone supplies no concrete-mark witness. |
| R07 · C2, raw C5 | `p.M/T ← p.f.MUST/T {g},N` starts `p.f.*/T,D` and its FLOW companion. Carry `{g}` on both STAR starts at the unchanged actual head. Apply only in restricted FULL for a concrete demand and a STAR or MUST actual. | At the same head the copied mask denotes the same forbidden subtrees. E cannot move to another head. The map adds no seed and changes no start layer. |
| R08 · C2, raw C5, field limits | Preserve the already bounded, deeper actual head and its nonempty E on the eligible concrete STAR start and its FLOW companion. Keep the conditional EXACT/FLOW prefix probe for M demand. | The actual head and holes stay together. Every overrun of Dc+1 comes from the certified map below. The global and paired output caps still hold. |
| R13 · raw transfer | For `x.f.g=new Node()`, reject the strict-descendant keep at `x.f.*` per leaf when the actual is `x.$/F`. The keep at `x.* {f}` still yields the exact root with `{f}`. | No strict descendant lies in the exact point. The same-head keep records the real overwrite exclusion before normalization. |
| R32 · run-2 C2 and raw C5 | Start the requested STAR identity in backward run-2 for a same-head precise STAR demand and STAR actual. `set(p){ p.f=new Node(); return p; }` through wrappers can then produce the NORMAL relation with `{f}` and preserve `p.g/T` at run-3. Retain the existing admitted deeper-actual run-2 STAR case. | Same base/head requires no extra field. C5 uses the same raw family. The wrapper proof relays NORMAL service through any finite number of wrappers. |

### 2.1 Legal starts and marks

C2 uses a scalar actual and the entry selector Dc of a qualified pair
`Dp→Dc`. The pair retains Dp for C5. C2 first checks owner, direction, physical entry, base, mark, legal static shape
and the global bound on both heads. A T selector accepts only actual T.
FLOW with mask X accepts T if T is outside X, and FLOW with mask Y if
`X ⊆ Y`. Handoff normally clears the FLOW selector mask. The initial
uses the demand mark with empty mx. Normalize selector E to empty only
for an abstract FLOW/STAR selector. An exact concrete selector has
empty E. Each descent checks E at the ancestor's head. An initial is a
raw identity. In the table, the cell names the tail of that identity
before its companions.

| Dc at p | Actual p.$ | Actual p.* | Actual p.M | Actual p.NE | Actual p.MUST |
| --- | --- | --- | --- | --- | --- |
| Concrete $ | $ | ∅ | $ on D | ∅ | $ |
| Precise STAR | $ | * in backward run-2, ∅ otherwise | $ on D | ∅ | $ |
| M | $ | * | $ and * | * | MUST |
| NE | ∅ | * | * | * | MUST |

MUST actuals use the forward lane. A same-head MUST initial keeps actual
E. A precise STAR identity in backward run-2 keeps selector E. Every
other primary has empty E except the stated MUST case and R07/R08.

- **Actual strictly below Dc.** EXACT demand rejects. STAR demand emits
  the requested STAR identity in backward run-2 if the selector admits
  the extension. STAR rejects deeper actuals in later runs. For M/NE,
  let r be the prefix of the actual through the first new counted field
  after Dc. If the actual is deeper than r, emit `r.*`. At r, actual EXACT
  emits `r.$`, actual M emits both `r.$` and `r.*`, and STAR/NE/MUST emit
  `r.*`. An EXACT at r already satisfies a nonempty requirement at Dc.
- **Dc strictly below the actual.** EXACT actual rejects. M/NE actual
  can supply a *possible* residual M at Dc after the descent. It can be
  empty if the chosen path ends there. Use the same-head table. A forward
  MUST actual descends uniformly with empty E at the new head, after
  checking E at the old head. STAR uses the limited possible-binding
  rule below. Incomparable heads reject.
- **Companions and starting support.** Each successful concrete STAR
  adds the same-geometry FLOW STAR companion with N support. A successful
  deeper actual under M also adds `Dc.head.$/F,N` with empty E/mx as a
  structural probe. For NE, take the complete M family and remove every
  EXACT command at Dc's own head, including that probe. A failed primary
  adds no companion. FLOW starts have N support. Concrete STAR starts
  D. Concrete EXACT/MUST starts N only when the actual provides definite
  N support for it. Concrete support projected from M, NE or a possible
  STAR descent is D. Always carry actual layer and H on resumption.
- **Real exclusions.** For restricted FULL concrete demand, R07 copies
  nonempty actual E from STAR or MUST onto each eligible empty-E STAR
  command at the exact same base and head, including its FLOW companion.
  Existing nonempty command E takes precedence. R08 can replace an
  eligible shorter empty-E STAR head and E together as specified below.
  Use these maps with the raw C5 check in §3.3.

Apply R07 to the ordinary C2 family first. It copies E only when the
STAR command already has the actual's full head. R08 then checks the
shorter STAR commands that still have empty E. For a single command and
actual, the two tests are disjoint. A command moved by R08 already has
the actual's E. It does not receive a second R07 update or leave a second
shorter STAR command behind. MUST alone does not qualify for R08.

### 2.2 Possible field bindings

A possible field binding comes from selecting a named field path inside
an unresolved suffix. It does not assert that the actual has that
specific path. For the R06 STAR exception, use a strict descendant head
already named by a frozen M/NE row or by an allowed one-field child
in §3. Use the entire known path from the actual head to that selected
head. The actual's E must admit the first accessor. Check the same
base, mark, scope and port gates as for a direct offer. Apply the table
as if the selected head had a possible M residual. For an NE selector
the residual must supply its nonempty branch. The child's exact point,
when selected by an NE **parent**, is already nonempty relative to
that parent. An unrelated precise STAR or EXACT demand grants no such
permission.

Retain the original actual. Attach the possible flag to its binding
with the chosen row and raw query. Match only a current summary of
that admitted query in the same caller context, owner and port. When
FLOW normalization changes an EXACT endpoint's public key, use the
normalization witness for that raw query. The flag grants no saved-record
match and no other current query. Run ordinary matches first and use
this possible lane for the extra binding. Join the possible flag,
original actual's layer and summary layer when applying the result.
A correlated STAR result with unknown residual becomes M/D. An explicit
result follows §3.2 with D support. A possible binding cannot compose NT.
No artificial actual fact, field exclusion or new AP key records this
choice.

### 2.3 Field limits

`FL` is the number of concrete fields and array accessors. Count a JVM
static class anchor as zero and keep its named field together with it.
For example, `FL(x)=0`, `FL(x.f.g)=2` and `FL(S.C.f)=1`. Typed control
endpoints have no AP cap. A mixed control/DATA relation still caps the
DATA side. The loop growth test alone can use depth zero for ZERO.
Let K be the positive global limit of the current run.

| Boundary | Limit | Scope and exceptions |
| --- | --- | --- |
| Instruction results, caller replay results, and incoming actuals at admission | K at the bounded interface | Intermediate concatenation may be longer until the normal global cut. Real cuts produce NE/D in every run. |
| Ordinary C2 starts, including FLOW companions, prepared children and run-2 STAR relay | `min(K,FL(Dc)+1)` | Use the originating row's depth. A prepared child supplies no second +1. For ND the matched member is checked against its own row. |
| R08 C2 starts | K | **Only C2 exception to `FL(Dc)+1`**. In restricted forward FULL, a concrete M/NE row and same-mark NORMAL MUST actual with nonempty real E may extend an already eligible empty-E primary STAR command to its own strictly deeper head. Move actual head and E together. Map the matching FLOW companion identically. The old family must already exist. No extra starts and no extension for a prepared child, an EXACT probe, a backward run, a DEMAND actual or an empty-E actual. |
| Fresh C5 DATA output, including NORMAL, static virtual pairs and block/loop exits | `min(K,FL(Dp)+1)` for its own pair | **No relative output exception**. R08 changes only the initial head. For an ND result, keep all original members and apply the matched row's output cap to each selected leaf. A typed ZERO exit cannot carry DATA. |
| Run-1 summaries | K and native run-1 shape/static rules | There is no previous pair and thus no relative limit. |
| Saved NORMAL replay and predefined summaries | K on delivered DATA | Replay/model input is outside fresh C2/C5 publication. Any newly inferred caller summary still passes its own C5. |
| Loop own-ZERO exception | Ordinary K and C5 cap if DATA is emitted | Bypass the extra loop growth gate only. |

The output limit uses the previous pair's **Dp**, even when it is longer
or shorter than the current raw premise P. There is no general
`FL(C) ≤ FL(P)+1` rule. In a multi-row packet, cut each selected leaf
before union. A covered uncut leaf does not justify skipping another
row that would emit a cut D variant. An early exit needs coverage of
every remaining row's **capped** membership, including layer and H.

### 2.4 C2 at an offer

```text
prepareC2(offer, owner, entryPort):
    bounded = nativeGlobalCut(offer)
    commands = empty exact set
    for row in indexedEntryCandidates(owner, entryPort, bounded):
        if native scope, geometry and mark gates fail: continue
        family = primaryCommandsFromSection2_1(row.Dc, bounded)
        add only the authorized companions and point probe
        apply R07 then R08 to their eligible commands
        add the prepared children from §3.1
        keep each command's own qualified row and bound offer
        enforce the entry and global limits from §2.3
        commands.addAll(family)
    return commands
```

Use this for DATA once per real restricted offer after saved replay.
Use §6.1 for ZERO. The caller
hands the result to the owner for current application and subscriptions.
The C5 raw-image predicate uses the same cases as a structural query.
For `P` candidate rows, `G` guard hits for child preparation and `B`
command memberships examined or produced, work is a candidate/guard
scan plus `O((P+G+B)·(K+Emax))` scalar field and exclusion work.
`Emax` bounds the mask comparisons per scalar operation. This
excludes the existing index traversal and run-2 static query. The
family uses at most `4+3·|fields|` commands per scalar row before
deduplication. Scratch space follows the prepared plan, with no
unbounded actual-offer history.

### COMPLEX

R04–R08 and R32 use the scalar table, prefix tests and a bounded
rewrite. The additional cross-row child lookup is audited with
R09/R10 in §3.4. The R08 example with
`p.f.g.h.MUST/T{k},N` needs the right head for correctness, but its
replacement is one local operation on the actual.

### Examples diff

#### Raw field transfer

`{f}` after a fact is its field exclusion at that fact's head. Results
below are before C5 and summary normalization. R13 is shown in a
restricted forward run with K≥2.

| Input fact and operation | Current output facts | Proposed output facts |
| --- | --- | --- |
| R01. Cut `x.f.g.$/T,N` at K=1 | `{x.f.M/T,D}` | `{x.f.NE/T,D}` |
| R02. `y=x.f`. Offer `x.M/T,D` in the current core and `x.NE/T,D` in the proposal. | `{y.M/T,D}` | `{y.M/T,D}`. Reading f can exhaust the nonempty suffix. |
| R02. `y=x.f`. Offer `x.f.M/T,D` or `x.f.NE/T,D`. | `{y.M/T,D}` | `{y.NE/T,D}`. Reading f consumes a known field only. |
| R03. `x.f=y` with `y.M/T,D` and room for f. | `{x.f.M/T,D}` | `{x.f.M/T,D}` |
| R03. `x.g.f=y` with `y.M/T,D` and K=1. The write first forms `x.g.f.M/T,D`. | `{x.g.M/T,D}` | `{x.g.NE/T,D}` |
| R13. `x.f.g=new Node()` with `x.$/F,N`. Apply the parallel root keep `x.*/F→x.*/F{f}`. | `{x.$/F{f},N}` | `{x.$/F{f},N}` |
| R13. Same write and actual `x.$/F,N`. Apply the strict child keep `x.f.*/F→x.f.*/F{g}`. | `{x.f.M/F,D}` | `∅` |
| R13. Next instruction `y=x.f`. Use the union of both keep results above. | From `{x.$/F{f},N; x.f.M/F,D}` emit `{y.M/F,D}`. | From `{x.$/F{f},N}` emit `∅` for y. |

#### C2 initial emission

Each member `i,L` in a result set denotes the raw identity edge
`i→i,L`. Use one frozen row and no
other eligible deeper row or saved guard in these examples. The R07 and
R08 rows use restricted forward **run-5**, K=4. The letters f, g, h and k
are distinct fields. The comparison operates on Dc and the actual.
Dp is carried with the row for the later C5 step.

| Rule | Entry demand Dc | Actual | Current initial set | Proposed initial set |
| --- | --- | --- | --- | --- |
| R04 | `p.M/T` | `p.M/T,D` | `{p.*/T,D; p.*/F,N}` | `{p.$/T,D; p.*/T,D; p.*/F,N}` |
| R05 | `p.M/T` from a current cut, `p.NE/T` from the proposed cut | `p.$/T,N` | `{p.$/T,N}` | `∅` |
| R05 | `p.M/T` from a current cut, `p.NE/T` from the proposed cut | `p.f.$/T,N` | `{p.f.$/T,N; p.$/F,N}` | `{p.f.$/T,N}` |
| R06 | `p.f.M/T` | `p.*/T,D` | `∅` | `{p.f.$/T,D; p.f.*/T,D; p.f.*/F,N}`. The caller binding is possible. |
| R06 | `p.f.M/T` | `p.*/T{f},D` | `∅` | `∅` |
| R07 | `p.M/T` | `p.f.MUST/T{k},N` | `{p.f.*/T,D; p.f.*/F,N; p.$/F,N}` | `{p.f.*/T{k},D; p.f.*/F{k},N; p.$/F,N}`. R07 adds E at the same head. R08 does not move the head. |
| R08 | `p.M/T` | `p.f.g.h.MUST/T{k},N` | `{p.f.*/T,D; p.f.*/F,N; p.$/F,N}` | `{p.f.g.h.*/T{k},D; p.f.g.h.*/F{k},N; p.$/F,N}`. R07 leaves the initial `p.f.*` commands alone. R08 replaces both with depth-3 commands with `E={k}` at the full actual head. |
| R08, empty E control | `p.M/T` | `p.f.g.h.MUST/T,N` | `{p.f.*/T,D; p.f.*/F,N; p.$/F,N}` | `{p.f.*/T,D; p.f.*/F,N; p.$/F,N}` |
| R08, D actual control | `p.M/T` | `p.f.g.h.MUST/T{k},D` | `{p.f.*/T,D; p.f.*/F,N; p.$/F,N}` | `{p.f.*/T,D; p.f.*/F,N; p.$/F,N}` |
| R08, same-head MUST control | `p.M/T` | `p.MUST/T{k},N` | `{p.MUST/T{k},N}` | `{p.MUST/T{k},N}`. This family has no STAR command to replace. |
| R08, FLOW selector control | `p.M/F` | `p.f.g.h.MUST/T{k},N` | `{p.f.*/F,N; p.$/F,N}` | `{p.f.*/F,N; p.$/F,N}`. The selector is FLOW, so neither R07 nor R08 copies E. |
| R08, NE selector | `p.M/T` from a current cut, `p.NE/T` from the proposed cut | `p.f.g.h.MUST/T{k},N` | `{p.f.*/T,D; p.f.*/F,N; p.$/F,N}` | `{p.f.g.h.*/T{k},D; p.f.g.h.*/F{k},N}`. NE omits `p.$/F,N`. |
| R32, backward run-2 | `p.*/F` | `p.*/F,N` | `{p.$/F,N}` | `{p.*/F,N}` |

For the positive R08 row, the ordinary `FL(Dc)+1` is 1. The two
replacements have FL=3 and fit K=4. The EXACT/FLOW probe has FL=0.
No MUST identity or extra shorter STAR identity is in this family.
Reducing K below 3 would require a global cut **before** C2. The raw
three-field MUST actual would no longer be the submitted fact.

## 3. Prepared children, replay and paired C5

| Rule and affected part | Required behavior | Proof |
| --- | --- | --- |
| R09/R10/R23 · demand preparation, publication, handoff | Keep distinct admitted `P→p.M,D` and `P→p.f.NE,D` rows. Use f from a deeper guide with the same Dp or an eligible saved NORMAL guard. `p.f.g.*` contributes f only. Prepare `p.f.$` and `p.f.*` when compatible. | A deeper head can admit an extra concrete field that the parent cannot. The prepared suffix alone misses the child's exact boundary point. |
| R11/R12 · primitive transfer and saved replay | Run the coarse read and the prepared child through their ordinary transfers. Deduplicate equal bound results after application. | The child splits the suffix into a point and a nonempty suffix. The resulting N children do not replace a different D continuation. |
| R14 · call/block coordination | Reuse saved-first replay. If `id` has saved `p.*→ret.*` and no current demand, `p.f.$/T` still gives `ret.f.$/T`. Reuse the caller's C2 plan at the owner. | Original actual and resolved effects preserve the saved route. An empty plan only disables current-query service. |
| R15 · saved matching | Use the definite MUST lane when the actual proves uniform coverage. Keep an applicable provisional D response. | An actual child does not prove the parent uniform premise. The provisional response can still be the only backward guide. |
| R34 · saved matching, ordinary caller caps | For a same-direction saved NORMAL FLOW `p.f.*→ret.*` and a shorter `p.*` offer in a restricted run, use a possible read if the ordinary scalar match fails and yield `ret.M,D` at the saved result head, Empty E, with native mark/H/binding and guards. | A compatible suffix beginning in f can satisfy the guard, but a shorter STAR supplies no definite choice. Existing hits are unchanged. The possible reply can guide a later NORMAL return. |
| R18 · summary emission | Run C5 for a specialized candidate even if a saved NORMAL FLOW relation covers its uncut image. Use existing storage deduplication on admitted rows. | The candidate can become a distinct D guide due to its own paired cap. A saved NORMAL image does not supply that guide. |
| R20–R22 · summary restriction and normalization | Under `Dc=p.NE/F`, C5 rejects raw `p.$/F` even though it shares public `p.*/F` with an allowed raw STAR. Select with the row's own Dp, cut to its own limit, then publish admitted pairs. | Raw membership constructs an actual legal C2 command for that row. The scalar selection preserves each point in the paired intersection. Conditional FLOW EXACT-to-STAR needs a suffix-lifting witness, including real write E. |

### 3.1 Prepare one level of children

For an M/NE family with a STAR command at the row's own head p, collect
first fields from compatible deeper frozen rows with the same complete
Dp, or from retained NORMAL record guards in the active read view. A
guard `p.f.g.*` contributes f. A field must be legal for the row's mark,
scope, ports and actual, and admitted by real E. Use only bounded frozen
demand/record inputs. A prepared command cannot contribute a field to
this preparation.

For each retained f, select the residual at `p.f` from the **original**
actual. An exact actual at `p.f` offers the point. A known longer head
offers the suffix. An unknown compatible suffix that can start with f
can offer both a possible point and a possible nonempty residual. An
actual whose known prefix is disjoint offers neither. The point uses
EXACT, the nonempty branch uses STAR. A same-head STAR at the child
supplies only the suffix branch. A definite admitted MUST query remains
available for its own region. Carry the usual companion and support rules
from §2. For a concrete child family, STAR's FLOW companion is the
existing same-geometry hypothesis. The count of *primary* child starts
is at most two per observed field. No new parent prefix probe is added
by child preparation. Including companions, a scalar row and actual
produce at most `4 + 3·|fields|` commands before deduplication. Keep the
parent's Dp and cap even if a deeper
row helped select f. The deeper row can also supply an independent
plan with its own cap.

```text
prepareChildren(row, originalActual):
    collect distinct allowed first fields from compatible rows and saved guards
    for f in those fields:
        select the empty and nonempty residuals at row.Dc.head + f
        emit the eligible EXACT and STAR child and its authorized companion
        bind the child to the original actual and the parent's complete row
```

Apply the field limit once against that parent row. This loop does not
recursively prepare grandchildren. Its work is included in §2.4.

Apply the prepared children and the ordinary coarse transfer through
native application. A child query has its own original. It cannot
supply a different original's publication just because both fact
regions contain a field. For a supported primitive read or saved
inside read, use the ordinary exact result deduplication only after
both contributions have been applied in the same binding and have
reached the same destination. Equality includes original, layer, E, mx
and H. R34 likewise uses ordinary delivery for its possible result.

### 3.2 Match and apply scalar summaries

```text
onRestrictedCallOrBlockOffer(originalActual):
    apply saved NORMAL summaries to the original actual
    plan = prepareC2(originalActual)
    if plan is empty: return
    submit the plan's admitted initials to the owner
    apply admitted current rows in this binding
    subscribe for later matching current rows in the same binding
```

This is the normal offer path. Saved replay and current application
cost one indexed candidate scan each plus native matching, cuts and
effects for the selected rows. This reuses the one C2 plan and adds no
second actual traversal. An ND application still uses its native join.

Use the original actual for saved and ordinary current application.
Evaluate the caller's current C2 plan once. An empty plan ends current
application and subscription for that offer. Saved replay has already
run. In a nonempty plan, ordinary current matches still use the usual
premise matcher. An additional possible match must use the bound query
from §2.2. R34 extends only a failed direct saved read of a unary NORMAL
FLOW STAR-to-STAR record on a strict ancestor STAR actual. It checks
actual E at the descent, the ordinary mark/effect guards and the global
cut. It can return the record's output head as M/D with empty E.
Ordinary saved STAR-inside matches use opposite-direction records.

**NE actual.** For each scalar actual `a.u.NE`, select compatible leaves
at the summary premise head `a.v`. Use the normal base, mark, owner,
port and record-role filter, with the following NE geometry. Here
`s ≠ ε` is a known path component.

| Head relation | Premise EXACT | Premise STAR | Premise MUST |
| --- | --- | --- | --- |
| `u=v` | Reject, no empty suffix | Nonempty residual NE at v | No definite match |
| `u=v·s` | Reject | Admit if premise E allows s. Residual is the known s followed by NE. | No definite match |
| `v=u·s` | A possible point at v where the ordinary inside lane permits this premise | A possible residual M at v where the ordinary inside lane permits this premise | No definite match |
| Incomparable | Reject | Reject | Reject |

The inside lane in this table is the one available for an incoming M
leaf, with the same base, direction, mark, role and selected-record
checks. It does not require the R06 STAR exception. The strict descendant
s consumes at least one field, so the residual of NE there can be empty.
MUST still needs its definite basis for a definite match. A native
provisional MUST lane, when retained under R15, must pass its own
overlap and support checks and stays D. It gets no uniform support from NE.

**NE result.** After a successful actual binding, apply the leaf by the
following rules. They apply to a call or generated block, including a
repeat or leave edge.

1. An explicit NE conclusion is an independent result at the written
   output head. Use the ordinary endpoint mark substitution and mapped
   result base. Its tail remains NE and its layer D. Do not append the
   actual's unmatched suffix. A complete ND application or ZERO premise
   applies the same output constructor after its own match. A same-head
   NE result still uses the ordinary DEMAND alias and effect lane.
2. A correlated STAR-to-STAR relation with an NE actual copies the
   residual to its output. At equal heads it preserves NE. If a known s
   follows the premise, append s before the NE tail. Check the shared E
   of the STAR endpoints at the first field of s. With an unresolved
   suffix at equal heads, keep its NE region with empty E, which
   conservatively covers any admitted nonempty suffix. If matching
   consumed a strict prefix *from* an unknown suffix, the remaining
   output is M/D, with empty E. Do not restore NE there from the layer.
3. For other result tails use the ordinary constructor on the selected
   support, including ordinary MAY demotion when correlation is lost.
   An explicit point, where supported by the native constructor, is
   D under a possible or NE actual. No case turns an NE actual into
   definite MUST or a NORMAL observation. Apply the ordinary result
   cuts, alias/effect processing and H transport. An NE output carries
   its literal H membership, independent of the field-depth decision.

NE summaries are current-run DATA summaries. Store and deliver NE on D,
with empty E. At handoff turn the NE conclusion into Dc, keeping its
head and pairing with Dp. Do not reverse it into an executable premise or
persist it as a NORMAL record. For a packed result apply these rules
leaf by leaf, then union equal logical memberships; an EXACT leaf at
the same head retains its own support and membership.

At a rule test, NE cannot satisfy an exact condition at its own head.
A strict descendant can match with D support. A selected cleaner can
kill the whole NE region or remove a covered piece. If a partial
survivor cannot be represented, keep its NE/D cover. The survivor
cannot regain an empty suffix. Existing mark masks and cleaner H still
apply.

Use definite MUST matching for saved calls, blocks and loops. If that
match fails and ordinary provisional replay can apply, deliver its D
result through the native continuation. Preserve C2, ND and the port
and alias behavior.

### 3.3 Raw entry witness and paired output

Run boundary rules and C5 before admitting a newly inferred summary.
An existing saved summary's native image can equal the uncut raw
candidate while the latter produces a distinct D row after its paired
cap. R18 keeps that row. Use ordinary exact deduplication at admission.

```text
C5(rawP, rawC):
    for each qualified pair (Dp -> Dc), including virtual pairs:
        if either endpoint or the result is control:
            apply the typed C5 cases in §6.1 for this pair
            continue
        if no eligible raw premise member is in RawImage(row): continue
        for each candidate leaf c0:
            (p,c) = normalizeFLOWPair(whole rawP,c0)
            b = selectExit(c,Dp)
            if b exists:
                emit normalizeFLOWPair(p, cut(b, min(K,FL(Dp)+1)))
```

Split packed chains before pairing. Preserve the owning row on each leaf.
For the reference entry test, let A be the legal bounded scalar actuals
of this row's resolved base, port, direction and FULL mark mode.
`RawImage(row) = ⋃{ rawAPs(prepareC2(row,a)) | a ∈ A }`.
Preparation uses the same frozen row and saved-guard view as §3.1.
Compare the raw command's AP before normalization. A positive result
supplies the actual and the command which C2 emits for it. A negative
result must exclude all the C2
cases in §§2–3.1. The reference domain has finite legal accessors,
marks, masks and depth K. An implementation solves the finite cases
symbolically from the relative heads, tails, mark/E gates, fixed guard
fields and support lanes. Validate both directions against the reference
test. A missing accessor must be witnessed by a real legal accessor.
Do not enumerate path products or scan historical offers at runtime.
The hypothetical witness grants no caller application. A concrete
T selector can authorize a raw FLOW start via its own companion/probe.
The later mark restriction is on the output and must not reject that
entry witness just because it is FLOW. ND uses one contributing member
for entry permission but keeps the complete original on the output.
Normalize EXACT endpoints to STAR only for a complete singleton
FLOW-to-FLOW pair, preserving each path, E, mx, layer and H. Keep the native
ND/control rules. The two normalizations occur after the raw entry check.
All fresh restricted-run DATA summaries, including NORMAL, use the
paired output cap. Include the qualified virtual pairs in run-2.

Select the C2 plan and raw C5 check together before analysis starts.
Enable the pair in scopes where the comparative proof supplies a
retained route for every required use of a native start or summary it
rejects. Use the native pair in other scopes. Validate each proposed
admission and publication against one complete demand row with its
companions and cap. A normalized STAR key alone cannot witness a raw
EXACT command under NE. Use the reference raw image to validate the
updated `RestrictedInitialPolicy.canStoreInitial`.

`selectExit` first checks equal bases and intersecting marks. Equal
concrete marks meet. A concrete mark meets FLOW only if FLOW admits it.
Two FLOW slots meet. Preserve candidate mark, mx, layer and H. On the
selector only, normalize abstract FLOW/STAR E to empty.

| Candidate tail at Dp's head | Dp EXACT | Dp STAR | Dp M or MUST |
| --- | --- | --- | --- |
| EXACT | Keep | Keep | Keep |
| STAR | Keep whole relation | Keep whole relation | Keep whole relation |
| M | EXACT | M | M |
| NE | Reject | NE | NE |
| MUST | EXACT | MUST with E union | MUST |

If the candidate is below Dp, keep it only when Dp admits that suffix.
If Dp is below the candidate and the candidate admits descent, use
this table. Incomparable heads reject.

| Ancestor candidate | Dp EXACT | Other Dp |
| --- | --- | --- |
| EXACT | Reject | Reject |
| STAR | Keep whole relation | Keep whole relation |
| M or NE | EXACT at Dp | M at Dp with empty E |
| MUST | EXACT at Dp | MUST at Dp, using selector E for STAR and empty E otherwise |

Any selected concrete EXACT has empty E. An abstract EXACT selected
from MUST at the same head keeps its required E. An abstract EXACT
after descent has empty E. Keep correlated STAR whole for the native
representability case. Selection never upgrades support or creates a
concrete mark. Cut after this step and normalize again. The cut keeps the
prefix through the effective budget's last counted field, changes the
tail to NE/D, clears E, and preserves mark, mx and H.

**Work.** Run C5 once per fresh summary at its publishing boundary.
For `P` indexed pairs, at most `M` eligible original members and
`L` candidate output leaves, there are at most `P·M` raw admission
tests and `P·L` scalar output tests after a matching member is found.
The reference loop can share the same row's member test across its
leaves and the same output test across its matched arms. Bound work
per test by its geometry and exclusion scans and the lookups needed
for the row's prepared C2 cases. Never enumerate hypothetical offers
on the publishing path. The cut processes at most the selected
leaf's field chain. Store the deduplicated admitted results and emit
no unrestricted candidate record.

### 3.4 COMPLEX — prepared children

R09/R10 read deeper rows and saved guards before creating additional
bounded C2 queries. The R11/R12 proof model can then delegate a
coarse transfer to those children. The active path keeps the coarse
transfer, as in §3.1. No further query closure or delegation is
performed on the worklist.

| Candidate and fixture | Rule-disabled check | Necessity for current proposal |
| --- | --- | --- |
| Prepared children with delegation. `wrapper(x){ return choose(x); }`, where `choose` reads `x.f.f` on one branch and writes two fields on the other. Saved `x.f.f.*→ret.*,N` on `x.f.*/F` keeps `x.f.*/F→ret.M/F,D` even when current C2 is empty. | The historical branch without saved delegation has four stationary MAY pairs from run-9/run-10 and an uncapped recurrence. The child-routing reference stops at run-9. | This isolates the missing **saved-replay delegation** in that reference. Prepared C2 children alone do not remove the saved result. No independent stop caused by the currently enabled preparation has been established with the other guards retained. |
| Generic pre-C5 or live-reply coverage. The enclosing-method example can pass `ret.f.f.MUST/F,N` through a `ret.*` guide and publish `ret.f.NE/F,D`. | The historical BB reference needs an additional whole-summary proof. A longer initial and the inner BB's NORMAL record do not change the enclosing cap. | There is no production proof check for this candidate. R18 uses ordinary C5. A historical stop with precoverage is not evidence for enabling general cross-context analysis. |

The remaining C5 selection is one raw membership test and one
bounded output selection per qualified pair. Restrict the raw-image
implementation to the C2 cases in §§2–3.1. A general search over
hypothetical inputs would be an additional COMPLEX algorithm without
a termination witness here. Keep that search out of publication.
[Nested replay fixture](../docs/reports/bidirectional-nested-saved-replay-nontermination-20261115.md) ·
[BB fixture](../docs/reports/bidirectional-non-empty-may-basic-block-retrace-20261113.md)

### Examples diff

#### Preparation and application

| Rule and input | Current output | Proposed output |
| --- | --- | --- |
| R09. Qualified candidates `ret.*/F→p.M/F,D` and `ret.*/F→p.f.M/F,D`. In the proposal the latter comes from a real cut and ends in `p.f.NE/F,D`. | The broad result can leave only `{ret.*/F→p.M/F}` in the frozen guidance. | Keep guides `{ret.*/F→p.M/F; ret.*/F→p.f.NE/F}`. Apply ordinary executable admission to both candidates. |
| R10. `Dc=p.M/F`, actual `p.*/F,N`, eligible saved guard `p.f.g.*/F→ret.*/F,N`. | Initials `{p.*/F,N}`. | Initials `{p.*/F,N; p.f.$/F,N; p.f.*/F,N}`. The child bindings are possible. |
| R11. `y=x.f` under original `x.*/F`. Prepared child outputs are `{x.f.$/F→y.$/F,N; x.f.*/F→y.*/F,N}`. | Coarse output `{x.*/F→y.M/F,D}`. | Coarse output `{x.*/F→y.M/F,D}` and the prepared child outputs. The originals and layers differ. |
| R12. Apply saved opposite `p.f.*/F→ret.*/F,N` to `p.*/F,N`. Current callee C2 is empty. A child supplies `p.f.*/F→ret.*/F,N`. | Saved output `{p.*/F→ret.M/F,D}`. | Saved output `{p.*/F→ret.M/F,D}`. The separate child output does not remove it. |
| R14. Saved `p.*/F→ret.*/F,N`, actual `p.f.$/T,N`, current C2 set `∅`. | Caller reply `{ret.f.$/T,N}`. | Caller reply `{ret.f.$/T,N}`; current subscriptions `∅`. |
| R15. Saved `p.MUST/T→ret.MUST/U,N`, actual `p.f.MUST/T,N`. | Possible saved reply `{ret.MUST/U,D}`. | Possible saved reply `{ret.MUST/U,D}`. |
| R15, definite control. Same saved edge, actual `p.MUST/T,N`. | `{ret.MUST/U,N}` | `{ret.MUST/U,N}` |
| R34. Direct saved `p.f.*/F→ret.*/F,N`, actual `p.*/F,N`, f allowed. | `∅` | `{ret.M/F,D}` |
| R34, excluded descent. Same saved edge, actual `p.*/F{f},N`. | `∅` | `∅` |
| Independent result. `p.*/F→ret.M/F,D` currently, `p.*/F→ret.NE/F,D` in the proposal. Actual `p.f.$/T,N`. | `{ret.M/T,D}` | `{ret.NE/T,D}`. No appended f. |
| Correlated result. Saved `p.*/F→ret.*/F,N`, actual `p.f.M/T,D` currently or `p.f.NE/T,D` in the proposal. | `{ret.f.M/T,D}` | `{ret.f.NE/T,D}` |

#### C5 publication and delivery

Demand is the complete previous edge `Dp→Dc`. Raw summary is the
current edge `P→C`. Each output cell lists the **published current
summary set** for that candidate and row. Those edges are available to
matching caller subscriptions. `∅` means the candidate publishes
nothing and sends no current reply. Retained saved edges use the
separate replay path. The examples use no other demand row unless
shown.

| Rule | Previous demand edge `Dp→Dc` | Raw current summary `P→C` | Current published set | Proposed published set |
| --- | --- | --- | --- | --- |
| R18. Saved `p.*/F→ret.*/F,N` can reproduce the uncut candidate. K≥2. | `ret.*/F→p.f.M/F,D` | `p.f.g.*/F→ret.f.g.*/F,N` | `{p.f.g.*/F→ret.f.M/F,D}` | `{p.f.g.*/F→ret.f.NE/F,D}`. The saved reply can still use `p.*/F→ret.*/F,N`. |
| R20. Same public STAR key, different raw starts. | Current `ret.*/F→p.M/F,D`; proposed `ret.*/F→p.NE/F,D` | `p.$/F→ret.$/F,N` | `{p.*/F→ret.*/F,N}` | `∅`. The raw point fails before normalization. |
| R20, STAR control. | Current `ret.*/F→p.M/F,D`; proposed `ret.*/F→p.NE/F,D` | `p.*/F→ret.*/F,N` | `{p.*/F→ret.*/F,N}` | `{p.*/F→ret.*/F,N}` |
| R21. Authorized FLOW companion under concrete T demand. | `ret.$/T→p.M/T,D` | Current `p.*/F→ret.M/F,D`; proposed `p.*/F→ret.NE/F,D` | `{p.*/F→ret.*/F,D}`. Select `ret.$/F,D`, then normalize the output. | `∅`. Entry still accepts `p.*/F`. The exact exit cannot select the root from `ret.NE/F,D`. |
| R21, strict descendant exit. | `ret.f.$/T→p.M/T,D` | Current `p.$/T→ret.M/T,D`; proposed `p.$/T→ret.NE/T,D` | `{p.$/T→ret.f.$/T,D}` | `{p.$/T→ret.f.$/T,D}`. The selected f itself consumes the nonempty suffix. |
| R22. FLOW normalization, real exclusion. | `ret.*/F→p.M/F,D` | `p.$/F→ret.$/F{f},N` | `{p.*/F→ret.*/F{f},N}` | `{p.*/F→ret.*/F{f},N}` after raw admission. |
| Output cap, K=4. | `ret.*/T→p.M/T,D` | `p.$/T→ret.f.g.$/T,N` | `{p.$/T→ret.f.M/T,D}` | `{p.$/T→ret.f.NE/T,D}`. The two-field NORMAL candidate is never published. |
| R08 with output cap, run-5 and K=4. | `ret.*/T→p.M/T,D` | Current `p.f.*/T→ret.f.g.h.$/T,D`; proposed `p.f.g.h.*/T{k}→ret.f.g.h.$/T,D` | `{p.f.*/T→ret.f.M/T,D}` | `{p.f.g.h.*/T{k}→ret.f.NE/T,D}`. The three-field premise fits R08. The conclusion still has a one-field budget. |
| Output budget from Dp, K=4. | `ret.f.g.*/T→p.M/T,D` | `p.$/T→ret.f.g.h.$/T,N` | `{p.$/T→ret.f.g.h.$/T,N}` | `{p.$/T→ret.f.g.h.$/T,N}`. `FL(Dp)+1=3`, regardless of `FL(P)=0`. |

In the first output-cap example, a caller that offers `p.$/T,N` gets
`{ret.f.M/T,D}` from the current published edge and `{ret.f.NE/T,D}`
from the proposed published edge. The raw `p.$/T→ret.f.g.$/T,N`
is absent from both publications, so this application delivers no
`ret.f.g.$/T,N`.

## 4. Reply and summary coverage

### Rule definitions

| Rule and stage | Required behavior |
| --- | --- |
| **R16 · ready reply delivery** | Deliver each applicable NORMAL and DEMAND reply through native matching, layer joins, complete AND bindings, aliases and post-call stages. Submit the results to ordinary post-statement admission. Equal geometry keeps separate NORMAL and DEMAND memberships. |
| **R19 · current reply delivery** | Apply every current summary that matches the caller's native binding. A ready NORMAL result for the same region leaves the applicable DEMAND reply eligible. In restricted runs, current replies come from C5-admitted results. A raw exit rejected by C5 performs no caller delivery. |
| **R23 · admitted summaries and handoff** | Keep distinct MAY and NE summary rows after C5, including when the MAY region contains the NE region. Deduplicate identical NE memberships. Project each retained row with its own premise, field head and ports. |
| **R24 · admitted layers** | Keep an admitted DEMAND row when a NORMAL MUST conclusion covers its region. Retain the NORMAL row for replay and the qualified DEMAND row for the next handoff. Continue using native same-layer MUST folding. |
| **R25 · executable subsumption and guide compaction** | Reuse native aligned NORMAL FLOW subsumption, with the same suffix on both endpoints and the native mask and protection checks. At handoff, identical complete pairs can share one entry. For other compaction, verify the existing C2 key relation in the same entry scope and the C5 key relation at the same paired ports under the updated tails. Check every projection of an ND origin. Before sealing, verify every removed row's providers against the final retained basis. |
| **R27 · per-owner work priority** | Visit ready EXACT, NORMAL and control work before remaining uncertain work. Use FLOW first within each lane. Apply this order to an owner's ready work and publications. |

A DEMAND reply can still produce a Target or open a source permission
even when a NORMAL reply covers its points. C2 uses the preserved NE
head and C5 uses its own paired output selector. Transitive compaction
keeps a final valid provider regardless of arrival order.

### COMPLEX

The ordinary-delivery control reaches natural run-9 with the deferred
Target-retirement certificate.
[Bound-reply ablation](../docs/reports/bidirectional-termination-fix-validation-20261117.md)

### Examples diff

| Rule and input | Current | Proposed |
| --- | --- | --- |
| R16. Completed call gives `{x.MUST/T{f},N; x.MUST/T{f},D}`. | Submit `{x.MUST/T{f},N; x.MUST/T{f},D}` to admission. | Submit the same two memberships `{x.MUST/T{f},N; x.MUST/T{f},D}`. |
| R19. The owned query `p.f.g.$/T,N` returns `{ret.k.$/V,N; ret.h.$/U,N}`. C5 selects h/U. A coarse current reply also binds at x. | Deliver `{x.h.$/U,N; x.h.M/U,D}`. | Deliver `{x.h.$/U,N; x.h.M/U,D}`. The raw k/V return publishes `∅` under its C5 row. |
| R23. Same original `p.$/T`, outputs `ret.M/T,D` and `ret.f.M/T,D` currently. The latter becomes `ret.f.NE/T,D`. | The broad row can leave `{p.$/T→ret.M/T,D}`. | Keep both `{p.$/T→ret.M/T,D; p.$/T→ret.f.NE/T,D}`. |
| R24. `A=p.MUST/T→ret.MUST/T,N,H=1` and `B=p.MUST/T→ret.f.M/T,D,H=1` currently. B ends in `ret.f.NE/T,D,H=1` in the proposal. | Keep `{A; B}` where both are admitted. | Keep `{A; B}`. The D guide remains `{p.MUST/T→ret.f.NE/T}`. |
| R25. `A=p.*/F→q.*/F,N`, `B=p.f.*/F→q.f.*/F,N`, `C=p.f.g.*/F→q.f.g.*/F,N`. | Aligned native subsumption yields executable basis `{A}`. | Executable basis `{A}` and final service witness `A covers C` in either arrival order. |
| R27. Ready starts `p.*/F,N` and `p.$/T,N` at one owner. Their summaries are `A=p.*/F→ret.M/F,D` and `B=p.$/T→ret.$/T,N`. | A FLOW-first queue can publish `A then B`. | Publish ready `B then A`. The resulting set is still `{A; B}`. |

## 5. Cleaners

| Rule and affected part | Required behavior | Proof |
| --- | --- | --- |
| R26/R35 · concrete cleaner transfer [selected coarsening] | For selected EXACT cleaning of T at `x` or `x.f.g`, a matching same-base `x.MUST/T` keeps its region, original support, E and cleaner-survivor H. Nonuniform exact T still dies at the selected point. | Split along the cleaner path and use the selected same-head policy at the final child. Union with its siblings reconstructs the original region. This explicitly retains a possible observation at the selected point. D stays D. |
| R36 · concrete cleaner transfer after run-1 | For NORMAL `x.MUST/T` cleaned ALL at `x.f.g`, emit `x.MUST/T {f}` and `x.f.MUST/T {g}`, normally. Selected BELOW also retains `x.f.g.$/T`. Apply the usual caps. | Partition into one residual sibling region per field plus the optional point. The union is exactly the input minus the selected subtree. There are at most depth+1 pieces. |
| R31 · FULL nonstatic FLOW cleaner, all runs and directions | For `clearExactT(p); return p.g;`, keep the original headers of every path whose whole suffix cone is disjoint from the cleaner. Mask the remaining leaves as before. Cleaner at `p.f` still masks an abstract point probe at p because its normalized suffix can include f. | For EXACT, the cleaner head lies in the cone iff the input head prefixes it. For BELOW/ALL use prefix incomparability. This guard covers normalized suffixes too. The getter relays `p.g.h/T` with its original mark support. |

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

```text
cleanConcreteMust(c, cleaner):
    if the regions are disjoint: return {c}
    if cleaner is selected EXACT and its point is in c:
        return {c with native cleaner-survivor H}
    if not the R36 restricted NORMAL case: return nativeClean(c, cleaner)
    if the entire region is cleaned: return empty
    residuals = []
    for next field f on the cleaner's path relative to c:
        if f is excluded at this head: return ordinaryCut(residuals + [c])
        residuals.add(c with E union {f})
        c = child MUST at f with empty E
    if cleaner is BELOW: residuals.add(the surviving exact point)
    return ordinaryCut(residuals)

cleanFlowPacket(packet, cleaner):
    partition its leaves by the R31 suffix-cone disjointness test
    emit disjoint leaves with their original headers
    emit remaining leaves with the native selected-mark mask update
```

Run at ordinary cleaner transfer, before the next delivery or
publication. R36 emits at most one residual per traversed cleaner
field plus the possible exact point. The work is linear in those
steps, the mask inspections and the sizes of the emitted paths.
R31 does one prefix comparison per leaf and uses at most two packets.
Neither rule creates a C2 start or expands arbitrary field suffixes.

### COMPLEX

R26/R35 classify an exact point locally. R36 traverses only the
cleaner's declared field chain, and R31 visits only the packet
already being cleaned. This section adds no search across statements,
methods or iterations.

### Examples diff

| Rule and input | Current output facts | Proposed output facts |
| --- | --- | --- |
| R26. Selected EXACT cleanup of T at x with `x.MUST/T,N`. | `{x.MUST/T,D,H=1}` | `{x.MUST/T,N,H=1}` |
| R35. Selected EXACT cleanup of T at `x.f.g` with `x.MUST/T,N`. | `{x.MUST/T,D,H=1}` | `{x.MUST/T,N,H=1}` |
| R35, exact input control. Same cleanup with `x.f.g.$/T,N`. | `∅` | `∅` |
| R36. Selected ALL below and at `x.f.g`, with `x.MUST/T,N` and room for both fields. | `{x.MUST/T,D,H=1}` | `{x.MUST/T{f},N,H=1; x.f.MUST/T{g},N,H=1}` |
| R36. Selected BELOW `x.f.g`, same actual and budget. | `{x.MUST/T,D,H=1}` | `{x.MUST/T{f},N,H=1; x.f.MUST/T{g},N,H=1; x.f.g.$/T,N,H=1}` |
| R31. Selected EXACT cleanup of T at p with the disjoint leaf `p.g.*/F,N`. | `{p.g.*/F(mx={T}),N}` | `{p.g.*/F,N}` |
| R31, intersecting control. Same cleanup with `p.*/F,N`. | `{p.*/F(mx={T}),N}` | `{p.*/F(mx={T}),N}` |

## 6. Controls and handoff

| Rule and affected part | Required behavior | Proof |
| --- | --- | --- |
| R28/R33 · typed controls, handoff and stopping | Reuse paired projection, demand mask clearing and the forward stop test. Carry NE through DATA projection. | Projection is idempotent. Typed controls keep their paired witnesses. Stopping requires an empty effective frontier. |

### 6.1 Typed matching, publication and seeds

**Current implementation.** Reuse the existing ZERO, Target and seed
handlers.

- **C2 and C5 controls.** A reached ZERO starts the ZERO identity when
  `Dc` is ZERO or DT. C5 tests both endpoints on one qualified row. A
  ZERO or DT entry requires a ZERO original. A ZERO exit accepts ZERO
  and also admits DT publication without creating a ZERO result.
  [DemandStore](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/DemandStore.kt#L157)
- **Target publication.** A forward NORMAL witness yields NT with its
  report ID. A DEMAND witness yields DT. NT composes only on NORMAL
  links, deduplicates against saved NT and confirms a report at a
  configured root with ZERO premise. Backward ignores NT. DT uses paired
  C5 after run-1. A reversed source completion from DATA to ZERO emits
  DT with the caller original. `ZERO→ZERO` stays ordinary control flow.
  Keep concrete or ZERO Target origins and full ND application joins.
  [BlockRunState](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/BlockRunState.kt#L132)
- **Seeds and ports.** Reuse statement-scoped sink seeds and source-hit
  permissions keyed by method, statement, forward micro-edge and action.
  The seed index supplies permissions at reached statements.
  A reached backward exceptional ZERO can also use the normal control
  view. If that view admits ZERO, hand off `ZERO→DT` at the normal
  invocation. Use §6.3 for the run-2 static routes.
  [SeedIndex](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/Seeds.kt#L59) ·
  [BlockBoundaryDemandView](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/BlockBoundaryDemandView.kt#L35)

**Proposed change.** In scopes that enable revised C2/C5, use §2 and
§3.3 for the DATA endpoint of a mixed DATA/control row. For a DATA
entry, including a DT probe, replace the current `canStoreInitial`
check with the raw C2-image test. One contributing member can satisfy
the restriction, and the full ND original stays on the result. For a
DATA exit, use the revised selection and NE truncation at the existing
row cap in §3.3.

### 6.2 Barrier projection and stop

**Current implementation.** At a completed barrier, persist eligible
NORMAL summaries with their masks and use the existing report and seed
stores. Build the next demand index from admitted DEMAND summaries, ND
summaries, backward singleton-ZERO summaries and outgoing DT. DATA
projection forms one `(Dc,Dp)` pair per result leaf and original member.
Reverse block ports. Keep the original ND premise for application.
[IterationDriver](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/IterationDriver.kt#L213) ·
[HandOff](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/HandOff.kt#L31)

R33 already clears FLOW mx on both projected endpoints and E on FLOW
STAR. MUST projects to M with empty E. ZERO and DT stay typed. These
projections are idempotent. FULL handoffs after run-1 use exact C2/C5
service compaction. The forward stop test is `HandOff.demandEdges.isEmpty()`
after insertion and compaction. A retained DT counts. Report rows and
seed definitions stay in their own stores.
[Projection](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/StaticGuidance.kt#L50) ·
[Compaction](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/driver/HandoffCompactor.kt#L21) ·
[Mask proof](lean/proposals/handoff-mask-audit-20261117/MaskHandoff.lean)

**Proposed change.** Project each distinct admitted NE result as an NE
entry at its own head, paired with its own original and ports
(R09/R23). A MAY row leaves that NE row eligible. Revalidate existing
DATA compaction keys against the new C2/C5 rules under R25 in §4.
Remove an origin only when every projection has its required service in the
final retained basis. Keep typed Target compaction and the stop test.
Projection still offers at most `k·m` pairs for k result leaves and m
original members. The stop test still reads the completed index count.

### 6.3 Run-1 static views

**Current implementation.** Reuse the frozen run-1 direct, write,
lost-write, boundary and terminal rows for run-2. Keep method and block
attachments scoped to their ports. The native lookup uses explicit
rows and same-slot carry, then local composition and eligible inherited
static-to-static bridges. It joins shared anchors with compatible
geometry and mark labels. A static anchor is a class/field pair or an
EXACT class marker. FLOW acts as identity. In FULL mode,
two concrete middle labels must agree. Keep the C2 entry-only lookup,
complete C5 pairs with their own budgets and the existing Target
probe. Later runs use local demand. The barrier attaches the index
without expanding the transitive closure.
[FrozenStaticCompletion](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/StaticGuidance.kt#L212) ·
[StaticPairLookup](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/StaticPairLookup.kt#L5)

The backward run-2 block Target shortcut uses the `STATIC_SHORTCUT`
entry scope, the matching output port and a writer path back to real
ZERO. Keep this route separate from ordinary DATA entry.
[Shortcut](../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/DemandStore.kt#L328)

**Proposed change.** Keep NE at its named static field anchor. For a
join involving NE, require an overlapping location with a nonempty
suffix relative to every NE endpoint, respecting both endpoints'
geometry and E. Thus same-head EXACT and NE cannot join. Use §§2–3
for the qualified C2/C5 tests. Check the adapter against native C2,
C5, Target, preflight and frontier results on existing shapes and
validate NE joins before enabling it. Keep this check outside the
worklist. Runtime lookup still visits only indexed postings and states
reached by the native query.

### Examples diff

Guide rows are shown in the previous edge's orientation.

| Rule and input | Current | Proposed |
| --- | --- | --- |
| R28. Backward after-loop block emits `ZERO→x.f.$/T,N`. | Guide `{ZERO→x.f.$/T,N}` at reversed ports. | Guide `{ZERO→x.f.$/T,N}` at reversed ports. |
| R28, paired C5. Guides `{p.$/T→DT,D; ZERO→q.$/T,D}`, raw `ZERO→DT,D`. | Published `∅`. | Published `∅`. Adding guide `ZERO→DT,D` admits the candidate. |
| R28. No DATA guides, live root `ZERO→DT,D`. | Guide `{ZERO→DT,D}`. Continue. | Guide `{ZERO→DT,D}`. Continue. |
| R33. Admitted `p.*/F{f}(mx={U})→ret.*/F{g}(mx={T}),D`. | Guide `{p.*/F→ret.*/F}`. | Guide `{p.*/F→ret.*/F}`. NORMAL replay keeps `E` and `mx`. |
| R09/R23. A field cut gives `p.$/T→ret.f.M/T,D` today and `p.$/T→ret.f.NE/T,D` under the proposal. | Guide `{p.$/T→ret.f.M/T}`. | Guide `{p.$/T→ret.f.NE/T}`. A broader MAY guide does not replace this NE row. |
| Run-2 static join. Matching ports and `ZERO→S.C.f.M/T,D` writer with `S.C.f.$/T→DT,D` reader. In the proposal the same field cut gives `S.C.f.NE/T,D`. | This pair can produce virtual `{ZERO→DT,D}`. | This pair yields `∅`. The NE writer excludes the reader's exact head. |

Candidate Target retirement and its termination evidence are in the
[possible next-iteration spec](demand-target-retirement.md).

---

[Constructive rule proofs](lean/proposals/demand-refinement-spec-20261117/README.md) ·
[Joint service proof](lean/proposals/demand-no-loss-audit-20261117/README.md) ·
[Scalar, continuation and handoff checks](lean/proposals/demand-spec-clarification-20261118/README.md) ·
[Termination examples](../docs/reports/bidirectional-demand-termination-counterexamples-20261115.md) ·
[Validation](../docs/reports/bidirectional-termination-fix-validation-20261117.md)
