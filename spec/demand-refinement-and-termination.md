# Demand refinement and termination

This specification defines bounded refinement and fact handling in
FULL mark mode of the bidirectional access-path analyzer. Run forward at
limit 1 in run-1, backward at limit 1 in run-2, then alternate direction
with limits 2, 3, …. A policy cutoff is separate from natural termination.
In the examples, **current** means the native FULL rules at `8da26aa13`.
**Proposed** means the analyzer operations defined below.
For a proposed-only tail, the current column gives the corresponding
native case and names the substitution. The analyzer uses existing
statement forms, AP stores and handoff indexes. Sections 4 and 7 state
the implemented scope of suppression. In particular, the mathematical
live-reply and terminal-retirement proofs stay in the model.

**COMPLEX** marks additional cross-row preparation, graph extraction
or closure work. A local tail case, a scan of first CFG destinations
or reuse of a native lookup keeps its ordinary classification. For
each COMPLEX candidate, compare its recorded fixture with the
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
semantics, restricted admission and publication, completed-output filtering,
and cleaner transfer. They can change demand,
report timing and delivery counts. Selected EXACT cleaning of concrete
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
  Apply the C2/C5 policy selection in §7 as one unit.

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
reached the same destination. R34 likewise uses ordinary delivery for
its possible result. There is no delegation check on the worklist.

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
and alias behavior. The eventual local result can use §4.1.

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

Activate raw checking and the C2 plan together. For a native admitted
summary or start that the new plan rejects, prove that a legal retained
route serves every needed use of it. A normalized STAR key alone cannot
justify a raw EXACT command under NE. A proof uses one complete paired
row for each new admission/publication, including its companions and
output cap. If the bridge is missing, use native admission and publication
for the affected scope under §7.

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
| Prepared children with delegation. `wrapper(x){ return choose(x); }`, where `choose` reads `x.f.f` on one branch and writes two fields on the other. Saved `x.f.f.*→ret.*,N` on `x.f.*/F` keeps `x.f.*/F→ret.M/F,D` even when current C2 is empty. | The historical branch without saved delegation has four stationary MAY pairs from run-9/run-10 and an uncapped recurrence. The child-routing reference stops at run-9. R17 sees live caller/return consumers and cannot remove them. | This isolates the missing **saved-replay delegation** in that reference. Prepared C2 children alone do not remove the saved result. No independent stop caused by the currently enabled preparation has been established with the other guards retained. |
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

| Rule and affected part | Required behavior | Proof |
| --- | --- | --- |
| R16 · completed statement output | Use §4.1 for an identical definite N/D pair. | An eligible D delivery has no effects at any first destination. |
| R17 · completed statement output | Omit a covered concrete local D offer before insertion when every native next destination discards the old local. | Native delivery cannot pass the first relevant instruction without executing it. The accepted statements have no action for the fact. |
| R19 · current reply | Apply the current reply and its call stages normally. At completed statement output use §4.1 for the eligible local result. | C5, other subscribers and call effects see the same inputs. Only a local result with no consuming instruction is skipped. |
| R24 · post-C5 summary and handoff | Retain the distinct DEMAND membership even when the NORMAL MUST conclusion contains its points. | NORMAL support cannot replace the paired demand row. The paired comparison in §6 preserves the outgoing uses. |
| R25/R27 · publication, ready queues and compaction | Reuse native aligned NORMAL subsumption and qualified handoff compaction. Process ready exact and control work before uncertain work per owner. Use FLOW first within a lane. | Native membership is checked on the final retained rows. Scheduling changes callbacks and processing order. |

### 4.1 R17 at completed statement output

Apply R17 in forward FULL after run-1, in `BlockRunState.completeOutput`
before `admitOutputs` writes to `ScopedEdgeStore`. Calls use this same
point after their last stage, ordinary alias handling and the field cut.
Statement and identity results use the same check. Limit this path to
single scalar concrete local facts on D with tail EXACT, MUST, M or NE.
Use ordinary admission for a packed offer unless it already comes
through this scalar path. Skip the filter at method exits, exceptional
exits and other output paths that do not call `completeOutput`.

Take the exact ordinary first destinations for `(S, d.base)`. For a
flat method use `context.forEachSuccessor` and `forEachDeliveryTarget`.
For a physical block use the same `BlockCfgDeliveryCache.after` result
as `Binding.successors`. A block boundary, repeat edge, method endpoint
or synthetic route fails the deletion test. Keep the native path for
root routing without that exact destination view. The cache already
skips statements proved irrelevant to this base. Never continue past a
first relevant statement for this test.

At a first destination J, an input with base x has no effect only in
this supported case:

- J is an ordinary non-call instruction, outside entry/exit handling.
- Its `DirectedForms.withStatement` value touches x, and
  `StatementSummary.edgesOf(x)` is empty. The ordinary `FormApplier`
  therefore takes the touched-base branch and emits no plain result.
- The form has no conjunctions, source predicates or static operations.
  This excludes the other callbacks that could use x. No after-call or
  boundary rule runs at J.

For example, the form of `x = null` touches x and has no edge from x.
A field overwrite such as `x.f = y` normally has a keep edge from x and
fails the test. A call fails even if its declared return overwrites x.
It can read x or run a rule before the overwrite.

```text
completeOutput(S, P, d):
    if forward FULL after run-1 and scalar concrete local D(d)
       and hasOnlyDiscardingDestinations(S, d.base)
       and edges.edgesAt(S, P).hasNormalCover(d):
        return                       // skip insertion and all enqueues
    admitOutputsAndDispatchAsUsual(S, P, d)

hasOnlyDiscardingDestinations(S, x):
    for J in borrowCachedFirstDestinations(S, x):
        if J is a boundary, endpoint, call or synthetic route: return false
        form = borrowCachedForwardFullStatement(J)
        if form is missing: return false
        if x not in form.touched or form.edgesOf(x) is nonempty: return false
        if form has conjunctions, sources or static operations: return false
    return every ordinary successor had a complete cached destination list
```

Read existing cache entries without building or pinning new forms for
this check. A missing or reclaimed row uses ordinary output admission
and delivery. An empty cached row is a completed result. A provider
already delivered from S normally has warmed the same routing rows.
Where a form provider has no cache-only read, leave that destination
ineligible until the provider exposes a read of its existing cached
value. A cache-only read holds the existing value during the predicate.
It needs no new cache or retention policy. Stream each successor's
cached destinations. Repeated destinations can be checked twice without
allocating a union. Stop at the first failing destination.

An empty, completed destination list passes the destination test. Use
the existing store lookup for the same block entry scope, original P
and producing statement S. Compare a NORMAL leaf with the same local
base, full mark and literal H. For R17 the provider is MUST. At the same
head it covers EXACT, MUST when its E is a subset of the candidate's E,
and M or NE when the provider has empty E. For descendant heads the
first extra field must be outside its E. Other heads fail. R16 can use
this same output filter with a NORMAL EXACT or MUST of identical
geometry, E and mark. Use the existing same-layer folding independently.

The deletion skips insertion of this offer and every enqueue from S.
The provider has already taken its native path. A later NORMAL arrival
does not remove any stored D, pending work or emitted effects. At least
one live or unavailable destination keeps the whole D offer. The
filter requires only the current output, cached destinations, statement
forms and the existing edge store. It introduces no origin key, proof
record, speculative rule execution, waiting or scan across future runs.

**Work.** Let `s` be the immediate successor count, `d` the number
of destination references read, and `b` the number of provider leaves
inspected in the one `(S,P)` cell. The added work is
`O(s + d + b·(K + Emax))`, plus decoding the borrowed cell's existing
packets. `Emax` is the largest exclusion-set scan during comparison.
Read only providers at the same base/mark/H and use the existing prefix
lookup where available. A failed destination check never reads the
edge store. Extra retained space is zero. The check causes no new CFG
walk, form build, call application, C2 start or C5 lookup. A hot check
can still cost more than one ordinary overwrite delivery. Measure
offers checked, drops and processing time before claiming a speedup.

**Preservation.** Native delivery skips only irrelevant statements. At
all first destinations accepted here, this input only touches a base
with no transfer, join or rule callback. It emits no later fact, call,
Target or summary. Induction over the worklist therefore leaves all
subsequent semantic outputs identical. C5 and the next permission
index have the same inputs. In particular, a ready NORMAL cover does
not authorize dropping D on the way to an observer. Both D and N reach
that observer and native Target handling decides what to publish.

### 4.2 R19 and the call output path

Apply saved NORMAL and current summaries through the existing
`RunMethodCallServices` application and resume paths. In particular,
finish the premise match, ND join if any, bound H, ordinary alias and
identity handling, and all post-call stages. The caller then reaches
`completeOutput` and tests its local result under §4.1, regardless of
which summary produced it. R19 adds no filter inside call application.
Keep all owner summaries, existing C2 admissions, subscriptions,
permissions and admitted Targets.

There is no separate owned-query closure scan in this implementation.
The local `r.k.$/V,N` below can trigger a V-dependent rule in the
callee. Its return transfer yields raw `ret.k.$/V,N`, which C5 rejects.
A closed h/U query with
committed `x.h.$/U,N` does not by itself show which future caller action
or source permission depends on `x.h.M/U,D`. In that live case send
both. The stronger R19 model that inspects every raw exit is an
analysis proof model, not an input to call delivery. It shows how an
h/U test may ignore a disjoint k/V exit only after completing the
callee transfers. It does not supply the missing caller test.

### 4.3 Summary coverage and retained basis

Store both a distinct MAY or NE DEMAND summary and its covering
NORMAL MUST summary. Existing same-layer MUST folding and aligned NORMAL
FLOW specialization stay in force. For example, `x.*→y.*` can cover
`x.f.*→y.f.*` with the same admitted suffix, while the misaligned
`x.f.*→y.g.*` remains eligible. Keep literal NE deduplication. At
handoff `DemandStore.Builder` can share identical complete projected
pairs. The existing `HandoffCompactor` can use its implemented key
matches only for cases whose C2/C5 semantics still agree, including
all ND projections. Compare every retained provider at the end of
compaction as in the existing method and scoped handoff. Keep both
rows for other shape comparisons, including MAY versus NE. Do not
introduce cross-layer summary folding or pre-C5 suppression.

### COMPLEX

R17 and its use after call application require only the immediate
native continuation in §4.1. R19's former complete owned-query and
caller-use closure would be COMPLEX. The live `x.h.M/U,D` fixture
illustrates the extra computation but does not require it for
termination: the guarded run-9 reference stops using R38 while
forwarding every applicable reply. The other bound-reply controls
also stop with the same root rule and no live-reply omission.
Keep the stronger R19 test out of the analyzer. [Bound-reply ablation](../docs/reports/bidirectional-termination-fix-validation-20261117.md)

### Examples diff

| Rule and input | Current | Proposed |
| --- | --- | --- |
| R16. Completed call S gives `{x.MUST/T{f},N; x.MUST/T{f},D}`. NORMAL already stored. Every first destination executes `x = null`. | Store and send `{x.MUST/T{f},N; x.MUST/T{f},D}`. | Store and send `{x.MUST/T{f},N}`. Both versions produce `∅` for these inputs at the overwrite. |
| R17. Output of S under ZERO is `{x.h.MUST/U,N; x.h.M/U,D}`. The NORMAL leaf is already stored. The sole first destination is `x = null`. | Store `{x.h.MUST/U,N; x.h.M/U,D}` at S and queue both. The overwrite emits `∅` for them. | Store `{x.h.MUST/U,N}` at S. Skip the insertion and enqueue of `x.h.M/U,D`. The overwrite emits `∅` for the remaining input. |
| R17, live destination. Same output at S, but one branch reads `x.h.f` for `observeU`; the other overwrites x. | Deliver `{x.h.MUST/U,N; x.h.M/U,D}`. The observation can produce `{ZERO→NT(o),N; ZERO→DT,D}`. | Deliver both `{x.h.MUST/U,N; x.h.M/U,D}`. A live first destination keeps D. Its DT can authorize the backward route to a different marking site. |
| R19. Actual `p.f.g.$/T,N` owns q below. The bound caller outputs are `{x.h.$/U,N; x.h.M/U,D}` and use `x.h`. | Deliver `{x.h.$/U,N; x.h.M/U,D}`. | Deliver `{x.h.$/U,N; x.h.M/U,D}`. The owned h exit proves one point. The caller can read the D reply. |
| R19, overwritten caller output. Current return gives `x.h.M/U,D` and an earlier completed result at S is `x.h.MUST/U,N`. The next instruction is `x = null`. | Complete the call and deliver `{x.h.MUST/U,N; x.h.M/U,D}`. | Complete the call and deliver `{x.h.MUST/U,N}` under §4.1. The callee summary and the subscription remain. |
| R23. Same original `p.$/T`, outputs `ret.M/T,D` and `ret.f.M/T,D` currently. The latter becomes `ret.f.NE/T,D`. | The broad row can leave `{p.$/T→ret.M/T,D}`. | Keep both `{p.$/T→ret.M/T,D; p.$/T→ret.f.NE/T,D}`. |
| R24. `A=p.MUST/T→ret.MUST/T,N,H=1` and `B=p.MUST/T→ret.f.M/T,D,H=1` currently. B ends in `ret.f.NE/T,D,H=1` in the proposal. | Keep `{A; B}` where both are admitted. | Keep `{A; B}`. The D guide remains `{p.MUST/T→ret.f.NE/T}`. |
| R25. `A=p.*/F→q.*/F,N`, `B=p.f.*/F→q.f.*/F,N`, `C=p.f.g.*/F→q.f.g.*/F,N`. | Aligned native subsumption yields executable basis `{A}`. | Executable basis `{A}` and final service witness `A covers C` in either arrival order. |
| R27. Ready starts `p.*/F,N` and `p.$/T,N` at one owner. Their summaries are `A=p.*/F→ret.M/F,D` and `B=p.$/T→ret.$/T,N`. | A FLOW-first queue can publish `A then B`. | Publish ready `B then A`. With the same retained service, the resulting set is still `{A; B}`. |

R19 example for an already owned point query at run-5. The point
query q uses `ret.h.$/U→p.f.M/T,D`. A separate coarse query can use
`ret.h.*/U→p.M/T,D` and publish `p.f.*/T→ret.h.M/U,D`.

```java
// Actual and raw initial for q: p.f.g.$/T,N.
Box make(Box p) {
    Box r = new Box();
    labelV(p, r);   // CM(p.f.g, T) gives r.k.$/V,N.
    labelU(r);      // CM(r.k, V)   gives r.h.$/U,N.
    return r;      // Raw exits {ret.k.$/V,N; ret.h.$/U,N}.
}
// C5 publishes {p.f.g.$/T → ret.h.$/U,N}. It rejects the k exit.
// Caller: x = make(p). A qualified coarse query separately supplies x.h.M/U,D.
// Ready NORMAL binding is {x.h.$/U,N}.
```

`r.k.$/V,N` enters the compiled `labelU` predicate during ordinary
analysis and can produce `r.h.$/U,N`. The return later emits raw
`ret.k.$/V,N`, which C5 rejects. In the caller the next uses of x decide
§4.1. A field read keeps the coarse h/U fact. If every first destination
is `x = null` and the caller already stores a NORMAL MUST cover for
the D fact at the producing statement, the coarse local can be skipped under §4.1. No callee state
needs to be retained for that decision.

#### R17 across calls and blocks

All examples start in forward run-3 or later. Let
`N = ZERO→x.h.MUST/U,N` and `D = ZERO→x.h.M/U,D`. Use the same
caller scope, original and H. N is already stored at S unless noted.
An overwrite example assumes the destination and statement form are
already cached.

```java
void caller(Box p, Box replacement, boolean branch) {
    Box x = wrapper(p);      // S. Applied caller results include {N, D}.
    if (branch) x = null;
    else x = replacement;   // Both arms discard the old x in their forms.
    observe(x);              // Cannot take the old x from S.
}
Box wrapper(Box p) {
    return dispatch(p);      // Multiple resolved callees can supply N and D.
}
```

| Native result and first destinations | Current output from S | Output with R17 |
| --- | --- | --- |
| The two cached overwrites above. `wrapper` returns `{p.f.g.$/T→ret.h.MUST/U,N; p.f.*/T→ret.h.M/U,D}` in compatible bindings. | Caller forwards `{N; D}`. Both overwrites give `∅` from old x. | Caller forwards `{N}`. The same two callee summaries remain. |
| Replace the else arm with `x = wrapper2(x)`. One resolved target reads h first and emits `{ZERO→DT,D}`. | `{N; D}` reach the call. | Keep `{N; D}`. The first relevant instruction is a call, even though the result rebinds x. |
| The original caller now saves `Box a = x` before the overwrite, and `anotherWrapper(a)` can read h. | The copy emits `{ZERO→a.h.MUST/U,N; ZERO→a.h.M/U,D}`. | Same two facts. The first form has an edge from x to a. No callee lookup is required to reject removal. |
| A completed call also emits `Q→p.f.$/V,D` to a caller alias and an admitted `ZERO→DT,D`. Old x has only the two overwrites. | `{N; D; Q→p.f.$/V,D; ZERO→DT,D}`. | `{N; Q→p.f.$/V,D; ZERO→DT,D}`. The local gate applies only to x after these effects. |
| After a call inside a loop, x reaches a repeat/leave port, with `ZERO→x.h.M/U,D` in a candidate block summary. | `{N; D}` enter ordinary block exit handling. | `{N; D}`. R17 cannot look through a block port to an outer overwrite. |
| A cached empty destination row for x. Alternatively one row is missing, or N is from a different original or was delivered after D. | Store `{N; D}` when both facts arrive. | Empty row and ready cover: store `{N}`. Missing row, wrong original or late N: retain D. |

#### R17 and the termination cases

Every R17 deletion removes deliveries whose first transfers have empty
results and effects. Applying the check to any catalogue program
preserves the baseline semantic frontier, including its active DT,
source permissions, next C2 admissions and published summaries. The
test can save local propagation. It cannot close a cycle that requires
an observable D delivery to disappear.

| Checked case and decisive fact | R17 decision | Termination evidence |
| --- | --- | --- |
| Alternating generators. After the first two `make` calls, `x.M/U,D` and `y.M/T,D` feed another call. After the third, `z.M/U,D` feeds the observer. | Keep all three. The first two destinations are calls and the third is an observation, or its boundary. | The historical run-5 model used live uniform folding. With it withheld, the checked retained-reply model still has root `ZERO→DT,D` through run-11. The run-7 natural stop with R38 requires a separate root retirement. |
| Two marking sites with one report. `r.M/T,D` from B and `r.MUST/T,N` from A reach the same observer. | Keep D, so `ZERO→DT,D` can still authorize B. | The guarded native fixture reaches B's precise track at run-5. The value-only gate lost it at run-3. |
| Protected and uniform bound replies, disjoint or unadmitted returns, exact-input control, and saved MUST replay controls. Bound coarse return facts feed reads, calls or observers. | Keep the live D replies regardless of their coverage. | The recorded guarded stops at run-7 through run-11 rely on the fixture's complete root Target proof. The run at which the NORMAL track already exists is not a stopping proof. |
| Exclusion-carry and deeper-head controls. The useful NORMAL reply must still reach its observer. | Preserve the observer delivery. R17 does not decide E or the initial head. | The checked exclusion references stop at run-5 with uniform value folding withheld. |
| Root MAY renewal, BB and enclosing-method renewal, global-cut growth (including protected), both cleaner cases, uniform root cleaner and EXACT-origin write. The relevant C2/C5 or field-transfer paths reach an operation or boundary. | Keep the live path. Any deleted local offer has no following output. | The catalogue tests distinct admission, cap or transfer repairs for these cases. R17 neither replaces those repairs nor changes their frontiers. |
| Nested saved replay with and without exclusions. The regenerated D result has a live input or publication use. | Keep it at the call/block. | The recorded run-9 certificates use child routing, outside the local overwrite check. |
| Recursive wrappers and regular/nested writer–reader examples. The coarse D route reaches a return, call or observer. | Keep the route and its admitted root DT. | Wrapper stops at run-7/run-9 and field-route stops at run-5 require terminal retirement. The field-route native diagnostics with DT retained reach run-9/POLICY. |

The compared runs are reference or native fixture results with their
stated policies. They do not give a new natural stop for the whole
current pipeline. [Catalogue verification](../docs/reports/bidirectional-termination-fix-validation-20261117.md) ·
[Two-source audit](demand-refinement-no-loss-audit.md)

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
| R28/R33 · typed controls, handoff and stopping | Retain paired DATA/Target projection. Clear FLOW mx from both demand endpoints. Keep real masks in NORMAL replay. DT still counts when DATA is empty. | Projection is idempotent. Typed controls keep their paired witnesses. Stopping requires an empty effective frontier. |
| R37/R38 [REC] [LOOP] · terminal proof | Keep the root DT. The proof model explains when all marking-site routes and uses could be discharged. | A saved `ZERO→NT(id-1),N` neither serves id-2 nor proves that all seeds using the root guide are redundant. |
| R39 [REC] [LOOP] · NoRoute proof | The regular-language model can prove absence of a marking-to-observer path. The native handoff retains its DT row. | A common word would induce a reachable accepting product pair. |
| R40 [REC] · NoRoute proof | The nested/regular model can prove disjointness. The native handoff retains its DT row. | A common word would supply a checked owner/state-pair derivation. |

### 6.1 Typed matching, publication and seeds

Each eligible pair is `(Dc, Dp)` for the next execution, written
`Dp→Dc` in the previous direction. The entry port and exit port come
from the same row. C2 matches a reached ZERO against Dc=ZERO or DT
and starts the native ZERO identity. This grants entry only. An
offer with DATA uses DATA selectors under §2.

For C5, evaluate the following two tests on **one** qualified pair.

| Test | Selector | Accepted result |
| --- | --- | --- |
| Raw entry | Dc is DATA | A DATA premise member belongs to the row's raw C2 image. For ND this tests a contributing arm and keeps the full original. |
| Raw entry | Dc is ZERO or DT | The matched original is ZERO. A DATA member cannot match. |
| Output | Dp is DATA | Only DATA can pass. Apply scalar selection and the row's cap in §3.3, including for a legal ZERO original. |
| Output | Dp is ZERO | Only a ZERO result or a DT candidate passes. The DT probe accepts on the same exit slots as ZERO and emits only a DT. |

```text
emitTarget(boundOriginal P, target, physicalPort):
    if target is NT:
        if forward and all required witnesses and links are NORMAL:
            publish via the existing NT deduplication
        return
    if unrestricted run-1 or acceptsTarget(P, physicalPort):
        publish DT with the admitted original and port

acceptsTarget(P, port):
    for row in ordinary qualified paired rows at this port:
        if row.Dp == ZERO and row.Dc accepts a complete P member:
            return true
    return false
```

The paired probe implements the table above and includes the existing
run-2 virtual and borrowed-normal routes where eligible. The ND member
test above applies only to restriction. The ND call join still requires
all arms before it can emit a Target. Use this at the existing Target
publication point, after ordinary rule handling or native call/block
composition. Work for the typed part is linear in indexed candidate
pairs and their inspected original members, with early exit at a
complete match. DATA entry checks and static lookup keep their own
costs. No AP path product is created by the typed ZERO/DT check.

For example, with guides `{p.$/T→DT,D; ZERO→q.$/T,D}`,
`ZERO→DT,D` matches the entry of the first row and the exit of the
second. It publishes `∅`. A complete `{ZERO→DT,D}` guide admits it.
NT uses the separate forward NORMAL report protocol. It is neither
an entry selector nor an exit selector.

At a forward observation, a complete NORMAL witness emits `P→NT(id),N`.
ID is the native key for location and rule. A DEMAND witness emits
`P→DT,D`. Preserve the run-1 origin selection and later-run full AND
joins. Dispatch a DT to its callers only if run-1 is unrestricted at
this boundary or paired C5 admits it. At a call or block link use the
native premise match in the actual binding, including all ND members
when applicable. The composed NT requires NORMAL inputs and links and
has the original ID. Ignore NT in backward. Keep native deduplication
against already persisted NT and collect confirmed reports from
configured root `ZERO→NT(id),N` edges. Section 6.4 models an optional DT bit. Native publication does not use it.

In backward saved replay, a reversed forward source is a matching
non-ZERO premise whose application produces ZERO. Preserve the caller
original, emit DT through its paired restriction and finish that
application. A `ZERO→ZERO` completion stays ordinary control flow.
Only the native source-hit paths record source permissions. The
conversion grants no independent source permission.

The seed index stays separate from the pair index. Forward demand
observations contribute the existing literal FULL requirements or
predicate occurrence handles at their native method and statement.
Backward source hits contribute the exact method, statement, forward
micro-edge and action identity. The next forward source hook compares
that complete key. At both ends, a seed becomes active only if the
native entry and CFG/rule binding reach it. A retained seed definition
does not replace a missing entry guide.

For an already reached backward exceptional block ZERO, C2 unions the
physical ZERO admission with admission from the normal invocation's
ZERO/DT view. Record whether that second test admitted ZERO. A ZERO
original's DT probe can use either whole paired control row. If the
borrowed admission was recorded, project the admitted ZERO→DT at the
normal invocation address. Resolve that address through the existing
normal block exit map. Keep exact DATA ports, the physical ZERO→ZERO
paths and the independent run-2 static-shortcut rule below. The
borrowed view creates no new block offer.

### 6.2 Barrier projection and stop

```text
handoff(sealedRun):
    persist eligible admitted NORMAL DATA and existing NORMAL Targets
    selected = admitted DATA where layer is D
                              or original is ND
                              or (backward and original is singleton ZERO)
    selected += admitted DT at method and block boundaries
    seeds = forward ? native sink seeds : native source hits
    for each selected origin with its physical owner and ports:
        for each scalar result and each original member:
            Dc = guideEndpoint(result)      // DT handled as typed entry
            Dp = guideEndpoint(member)
            emit row(Dc, Dp) at the reversed ports
    attach the run-1 static view only for run-2, as in §6.3
    apply existing qualified C2/C5 compaction to eligible DATA rows
    insert admitted DT and the retained DATA rows in DemandStore.Builder
    freeze the demand index and use the native forward stop test

guideEndpoint(x):
    if x is ZERO or DT: return the same typed endpoint
    if x.tail == MUST: x = x with M tail and empty E       // native view
    if x.mark == FLOW:
        clear mx
        if x.tail == STAR: clear E
    return x
```

The selector applies to admitted method and block results, including
the existing backward singleton-ZERO NORMAL case. Backward executable
ND is invalid. An ND projection adds one row per arm and scalar
result. The saved/current summary still requires the whole ND
original. Keep the source origin in the proof frame until compaction
checks finish. Identical projected pairs can then share one index entry
at the same owner and ports. Reverse block ports by exchanging the
producer entry and exit. A block's logical normal Target port must
resolve to the existing forward or reverse normal invocation, including
the borrowed route above.

`guideEndpoint` copies concrete heads, tails and masks except for
the existing forward MUST projection to M with empty E. It drops mx
on FLOW endpoints and clears E on FLOW STAR selectors. Keep NE and
its nonempty meaning. ZERO and DT stay typed. NORMAL replay retains
its original E/mx and real support. Confirmed NT and the seed index
do not become guide rows. Never apply DATA subsumption to DT.

For R09/R23, keep the distinct admitted summaries in their existing
summary store. Project these rows at handoff. This keeps the deeper
NE head available to C2 without a separate list of removed outputs.
Equal entry selectors can select different paired outputs or budgets.
The compactor compares complete projected pairs under §4.3.

At a completed forward barrier use `HandOff.demandEdges.isEmpty()`
after insertion and compaction, as in `IterationDriver.barrier`.
A retained typed DT counts. NT, saved replay, raw candidates rejected
by C5 and seed definitions do not count. Run-1 preserves the existing
frozen static views, their attached rows and preflight. Do not run a
second search for virtual consumers at the stop test. A changed static
view must pass the native comparison for C2, C5, Target and preflight
before activation. A policy cutoff stays separate.

**Work.** At the sealed barrier, a selected origin with `k` scalar
outputs and `m` original members offers `k·m` pairs. A DT has one
typed output. Projection and index construction charge the decoded
paths of those pairs and the native seed count. The existing
`HandoffCompactor` also sorts eligible origins by owner group and
looks up matching rows for each projection. Its comparison keys
and provider rechecks stay native. The final positive-count test is
constant time. It launches no lookup or transitive walk.

### 6.3 Run-1 static views

Build the run-2 static view from the frozen run-1 direct, captured write
and lost-write rows, attached boundary rows and terminal readers. Index
by complete scope and port as well as the static anchor. A write or
read attachment, including a terminal reader, belongs to the
selected method or exact block port pair. Only static-to-static
bridges can be inherited. The local lookup accepts a bridge owned by
this method. An inherited lookup accepts it if an owning method is
reachable from the querying method along zero or more resolved
caller-to-callee edges. The native outside-graph case accepts only
exact ownership. Apply this projection to C2, C5, Target and the
stop proof. Static shortcuts use their own physical attachment.

The reference view includes the direct rows and compositions of
visible rows at a shared static anchor. The anchor is the pair
(class, field), or the exact class marker for that class considered on
its own. From `A→S` and `S'→B`, extend only if S and S' have the same
anchor, their represented locations can overlap and the marks
compose. For native non-NE tails, overlap compares the two heads.
The shorter tail must admit the remaining known path and its E
must admit the first descent. For NE also require a possible nonempty
suffix in its region, so same-head EXACT and NE cannot overlap.
FLOW composes as identity. Two concrete labels must agree on the
middle full mark.
Carry the composed endpoint labels on A and B. A ZERO origin remains
typed and a DT endpoint has no output mark. The search keeps the
complete endpoint pair and scope and stops extending at a nonstatic
input. Revisit a search key only for new qualified endpoint/mark
service. Expose each reached pair on demand. A `ZERO→S/T` writer
and a `S/T→DT` reader can expose `ZERO→DT` through their common S.
Short-circuit only after the probe has all
its required results, including different C5 budgets. Shared carry
offers just the projected identity for the same actual static slot.

```text
queryRun2Static(owner, ports, operation, input):
    try the native explicit and eligible shared-carry rows
    for view in [local, inherited if the native preflight allows it]:
        pending = indexed endpoints matching this operation in view
        seen = empty set
        while pending is not empty:
            row = pending.pop()
            if row already in seen: continue
            seen.add(row)
            offer the complete row to C2, paired C5 or Target
            if the operation has all its required results: return
            if row.input has a static anchor:
                for predecessor in indexedIncoming(view, row.input):
                    if anchors, geometry and mark composition match:
                        pending.push(compose(predecessor, row))
```

For C2, the indexed traversal can use the native entry-only
optimization. For paired C5 it keeps both endpoints and its port until
the row is consumed. For a Target the output is typed DT and there is
no AP label on that endpoint. The latter two queries follow matching
predecessors as shown. This is the reference lookup order. Use the
existing native static view, including its entry-only specialization,
and compare any new implementation against its operation-specific
results. A boolean Target probe can stop at one accepted pair. DATA
C5 must account for all selected output leaves and their budgets.

**Work.** A native run-2 lookup examines the indexed seed postings
and then the reachable qualified states and their incoming candidate
postings. Its extra memory is the worklist and visited keys of this
probe. A posting check costs the mark and geometry comparison only
after the native filters allow it. Each query may examine a large
closure in the worst case. No such expansion runs in later iterations,
and the barrier does not materialize a static relation closure.

For a reached backward run-2 concrete static original at a block, the
static-write shortcut may serve a DT candidate through a completed
writer origin at `STATIC_SHORTCUT` with the matching output port.
The writer or preceding static bridge chain must end at real ZERO
when followed backwards. A carry identity, other-port writer or
terminal reader alone cannot serve this probe. It grants no DATA
entry alias. After run-2 use local demand only. Validate equivalence
to the native qualified static view before enabling NE in it.

### 6.4 R37/R38 terminal service proof

The implementation hands off every admitted DT with the ordinary
`projectTargetGuidance`. `NormalTargetStore` records report IDs and
conditional target rows. The seed index records permissions. Neither
provides a source-to-observer witness for each branch of an anonymous
DT. The theorem below is the condition for a stronger retirement rule.
It adds no runtime terminal bit, source catalogue or graph scan to this
implementation.

A goal is `(observer ID, full-mark/position predicate, revision)`.
Revision includes the applicable graph and rule versions. Freeze the
set of proved closed goals at forward start. Each local admitted DT
derivation contributes true for an unknown goal or a goal outside the
snapshot, and false otherwise. Each admitted relay copies its input
bit. If a relay has several required terminal inputs, OR their bits
under its complete binding. Alternative derivations of the same
qualified Target key also combine by OR. Retain a false-to-true
upgrade even when the Target edge was already delivered. Process
upgrades through the same valid Target links until stable before
handoff. A key publishes at most its first notification and one upgrade.

Compute closure of a goal before adding it to a later snapshot.
Use the complete catalogue S of possible marking sites, actions and
bindings for this predicate. In a temporary upper view U, every
possible source-to-goal transfer must map to a path, including sources
beyond current cuts or without current permission. In a temporary
NORMAL witness view N, every path used by the check must lift to a
retained actual root NORMAL path from that same source and mark to
the goal. Use ordinary matching, ports, binding and caps. Build both
views by supported adapters. With fields forgotten U can be
conservative. Bounded summaries alone cannot establish U. A local
conditional NT, a different source's report and NORMAL GEN before a
later cut do not establish N.

```text
proveClosedGoal(g):
    if catalogue or transfer correspondence is unproved: return Unknown
    possible = reverseReachable(U, g)
    witnessed = reverseReachable(N, g)
    for s in S:
        if s in possible and s not in witnessed and no validated NoRoute(s,g):
            return Open
    return Closed

onAdmittedTargetInModel(key, originBits):
    incoming = OR(originBits)    // a local origin contributes goal not in frozenClosed
    if key has no bit: publish and store incoming
    else if incoming and currentBit(key) == false: publish upgrade to true
```

For the proof model, run `proveClosedGoal` at a completed forward seal
for a goal with an available complete catalogue and both validated
graphs. A Closed result enters the next forward snapshot. With
adjacency lists, two reverse searches cost `O(V+E+|S|)` time and
`O(V+|S|)` scratch space after the views are built. Construction and
validation of the two views are separate costs and are not constant
time. The modeled bit uses OR on every admitted alternative. It can
publish once and upgrade once per key. A missing graph or catalogue is
Unknown. A possible route without a retained witness is Open.
Production runs neither search nor
the bit propagation.

This condition alone is insufficient for removing a row. The same
`PairedDemand(Target, Zero)` authorizes a ZERO initial in `DemandStore`
and lets a ZERO-original DT pass `acceptsTarget`. Those operations can
activate a seed in another rule or block. A root DT must stay as long as
the implementation cannot prove that every such use will survive or has
no required effect. Native stores have no reverse consumer index for
that key. Knowing that both report IDs are confirmed gives no decision
about such a seed. The implementation preserves the explicit control
row, seed index and exact scope/ports.

Induction over finite terminal derivations puts every goal of a
stable false key in the frozen set. The catalogue and path checks
give service for every possible source of each such goal. A
separate proof for all other control uses would be required before
retiring the row.

### 6.5 R39/R40 NoRoute proof models

**When.** Run this checker in a reference fixture or a read-only query
at a completed forward seal. It checks one exact marking-action to
observer relation. The native handoff currently keeps the DT. Even a
valid NoRoute could discharge only this relation under §6.4.

**Inputs.** One FULL mark T, the native marking action and exact source
position with word `a`, the exact observer occurrence and position
with word `q`, and the writer/reader interfaces. Each interface fixes
the actual root object, resolved entry and exit bindings and ports.
The writer and reader must meet at the same bound base. A field or
array label is the actual accessor ID. Do not use field names without
their resolved identity. The writer prepends its derived word to a.
The reader consumes its derived word before checking q. Thus a route
requires `writeWord · a = readWord · q`.

#### Extract the two languages

Use a finite value-flow graph for this fragment. Its vertices are
`(physical scope, instruction or port, base)` in the writer or reader.
Use the resolved CFG, the ordinary statement forms and resolved call
binding/return maps. The following table specifies labels on the value
being tracked. Include identity edges on every CFG branch that can
preserve it. A fresh result starts with no incoming value edge.

| Native transfer on the tracked value | Writer | Reader |
| --- | --- | --- |
| Identity or local copy | ε | ε |
| Ordinary `b.f = v`, with verified fresh, non-aliased result b | Edge `v→b` with label f | Unknown |
| Ordinary `b = v.f` | Unknown | Edge `v→b` with label f |
| Resolved call with an exact input/return mapping in the fragment | Invocation edge for the matching interface | Same |
| Branch or type guard on control only | Include every possible successor | Same |

Select the cone between the chosen input and output ports. Use the
version of the writer graph with these value edges read backwards
from output to input. Prepending f last puts f first in the final
word. Use the reader graph from input to output. For example, if a
writer prepends g before B and f after B, the rule is `f·B·g`. A
reader with the same instruction order uses `g·B·f`.

```text
extract(graph, interface, role):
    if exact endpoints, actual binding or other incoming routes are unproved:
        return Unknown
    scan all control-reachable CFG points at the resolved interfaces
    add the supported edges from their statement forms
    if any relevant operation can carry T outside these edges:
        return Unknown                     // includes unknown alias or call
    keep the value-flow cone between the selected ports
    orient value edges in word order for role
    for each matched interface:
        create a nonterminal for its start and each local vertex
        at the chosen output vertex add A → ε
        for each ordinary edge A --word--> B add A → word · B
        for each invocation edge A --callee--> C:
            v = uniqueRemainingWord(C, selected output)
            if v is NoPath: continue
            if v is unknown: return Unknown
            for each resolved alternative B with the matched ports:
                add A → ε · start(B) · v
    return the reachable clauses from the selected start

uniqueRemainingWord(C, exit):
    cone = vertices reachable from C that can reach exit
    if C not in cone: return NoPath
    if cone contains a call or cycle: return Unknown
    word(exit) = ε
    for node in reverseTopologicalOrder(cone), excluding exit:
        candidates = {edge.label · word(edge.to) | edge in this cone}
        if candidates do not all agree: return Unknown
        word(node) = the common word
    return word(C)
```

`uniqueRemainingWord` considers every continuation from C that can
reach the selected output. For the checked fragment, this subgraph
contains no call and is acyclic. Scan in reverse topological order:
the exit maps to ε and each other vertex maps to `edgeWord · word(next)`
when all reaching successors give the same word. No route gives no
clause. A cycle, second call or different suffix words gives Unknown.
This is a sufficient test for the recorded nested fixtures. Loops in
the regular part use ordinary labelled graph cycles outside this
suffix test. A branch before a call or in a regular loop adds edges,
not one clause per complete path. Mutual recursion names the resolved
callee interface, without unfolding it.

Check all resolved callees and relevant CFG edges, including exceptional
routes to this observer. Exclude a transfer only when its configured
base/alias information rules it out for the tracked carrier. A cleaner,
mark-changing rule, relevant overwrite, missing binding, hidden heap
route or unsupported effect in the cone yields Unknown. Carry no
facts through this extractor. An unobserved summary, the current
field limit or current seed permissions cannot justify omitting an
edge. A different internal observer or caller binding is a separate
query. A NORMAL return alone gives no edge to an internal observer.

**Extraction invariant.** Each real segment in the binding takes one
of the checked edges or invocation alternatives. Induct on the local
path and the nested return tree. Ordinary labels compose in word
order and each invocation substitutes the child's word before the
checked suffix. Thus the extracted language includes every real
word. Extra CFG branches can give Possible, while an omitted route
would invalidate NoRoute. The verifier rejects incomplete extraction.
For a supplied fixture grammar, validate this invariant against its
fully analyzed code separately from testing product emptiness.

#### R39 [REC] [LOOP] with two regular sides

A regular grammar has only `A→w` and `A→u·B`. Compile the first to a
word-labelled path to an accepting state and the second to a path to
B. Split each nonempty label into one transition per accessor. Attach
`a` on the writer and `q` on the reader after a base path to a final.
For ε arcs, compute ordinary ε closure: a state is final if its
closure reaches a final and a labelled transition may follow any
state of that closure. Its endpoint uses the same rule for the next
label. If the implementation cannot verify this expansion, return
Unknown. Finite ε closure preserves each labelled path by factoring
it at its labelled transitions.

```text
compileRegular(grammar, outer):
    add a word-labelled path A --w · outer--> final for each A → w
    add a word-labelled path A --u--> B for each A → u · B
    split each nonempty path into single-labelled arcs
    for state p:
        closure = reachableByEpsilon(p)
        mark p final if closure meets an original final
        copy labelled arcs from closure to p, leaving their destinations intact
    return the new labelled arcs with the updated finals and no ε arcs

regularNoRoute(writer, reader):
    if either validated grammar is unavailable or nonregular: return Unknown
    W, R = compileRegularWithOuterSuffixes(writer, a, reader, q)
    seen, pending = {(W.start, R.start)}, queue of that pair
    while pending is not empty:
        (p, r) = pending.pop()
        if p in W.finals and r in R.finals: return Possible
        for label in the common outgoing labels of p and r:
            for (pNext, rNext) in W.next(p,label) × R.next(r,label):
                if new to seen: pending.push((pNext, rNext))
    return NoRoute
```

The exhausted set includes the start and all equal-label successors.
Every shared word induces a path to a pair of accepting states by
induction on the word. The empty product test is independent of K
and the iteration budget. With ε removed, product space is at most
`Qw·Qr` pairs. Time is linear in those reached pairs, label probes and
matching successor pairs actually examined. The product is visited
lazily. For Q compiler states and E arcs before ε elimination,
the direct compiler takes at most `O(Q·(Q+E))` time and
`O(Q·E)` expanded labelled-arc space. It uses the original ε
graph and labelled arcs for each state, so copied arcs do not
feed the expansion scan.

#### R40 [REC] with one nested side

One side may also have `A→u·B·v`. Compile only the other, regular
side into automaton A with its outer suffix. Write `end(p,w)` for the
set of states reached from p by w. For each distinct fixed clause word
or outer suffix, compute `end` by an ordinary word transition DP.
Let `outer` be a or q on the nested side. Apply `outer` after the
whole derived word.

```text
nestedNoRoute(nested, regular, outer):
    if either model is incomplete or both are nested: return Unknown
    A = compileRegularWithItsOuterSuffix(regular)
    acceptingEnd = {q | end(q, outer) intersects A.finals}
    cells, pending = empty set, empty queue
    for each base rule B → w and each state p in A:
        for q in end(p,w): insertNew((B,p,q), cells, pending)
    while pending is not empty:
        (B,m,n) = pending.pop()
        if B == nested.start and m == A.start and n in acceptingEnd:
            return Possible
        for each rule C → u · B · v indexed by child B:
            for p with m in end(p,u):
                for q in end(n,v): insertNew((C,p,q), cells, pending)
    return NoRoute
```

A cell means a derived word can take the regular automaton from its
start state to its end state in that cell. Every inserted cell has
such a witness by construction. Conversely any word derivation
splits the automaton path at the prefix and suffix of its last rule.
By induction, the child cell enters the queue and adds the parent
cell. A source at h and a writer deriving `g.f` yield `g.f.h`.
Appending h inside the base of `g·B·f` would yield `g.h.f` and could
falsely prove disjointness. The last test therefore consumes the
outer suffix after the accepting candidate cell.

**Work.** Let M be the finite number of nested nonterminals including
local CFG vertices, Q the compiled regular state count, and C the
clause count. The worklist stores at most `M·Q²` cells. After computing
word relations, seeding takes at most `O(C·Q²)` and advancing takes
`O(C·Q⁴)` in the dense case. Use indexes by child and by start/end state.
The fixed word tables occupy at most `O(W·Q²)` for W distinct words.
For total word length L and E labelled arcs, computing them by a scan
per start and letter takes `O(L·Q·(Q+E))`. Extraction costs one scan
of the finite CFG, resolved bindings and tracked bases. Each invocation
can add a linear scan of its suffix cone plus the costs of building
and comparing its fixed words. There is no read/write word
enumeration. Unknown or an
interrupted search leaves the candidate open. Production incurs zero
work from these proof-only searches.

**Principal results.** R39 accepts disjointness for `{g,h}*f` versus
`{g,h}*g`. Changing the reader base to f gives Possible, with shared
word f. R40 returns NoRoute for `g*f` versus `R = g | g·R | h·R·h`.
Adding a writer base word `h.g.h` yields Possible through the nested
arm. Possible means a shared word in the model, which can contain
extra control branches. A proof result creates no DATA row, NORMAL
report or permission.
[Regular proof](lean/proposals/branching-field-cycle-20261117/RegularCertificate.lean) ·
[Nested proof](lean/proposals/two-sided-field-cycle-20261117/PairedContext.lean)

### 6.6 COMPLEX — terminal retirement and field languages

Typed projection, compaction and static lookup in §§6.1–6.3 reuse
native work. The added proof algorithms in §§6.4–6.5 have the
following independent termination evidence.

```java
Node wrap(Node p, int depth) {
    if (depth == 0) return p;
    Node y = new Node();
    y.f = wrap(p, depth - 1);
    return y;
}
// Mark x.f.g.$/T. Let r = wrap(x, depth). Observe CM(r.M, T).
```

| Candidate | Witness with the candidate withheld | What the other rules cover |
| --- | --- | --- |
| **R37/R38, source-specific terminal retirement.** In the wrapper above, `ZERO→NT(id),N` is available by run-3 while the next recursive cut again supplies `ZERO→DT,D`. | Without retirement, the bounded closure and the reverse MAY offer renew the live root DT in every later pair of the reference. The native diagnostic reaches run-15/POLICY. The single-source closure reference stops at run-7 after complete service is frozen. | The observer reads the D result, so R17 must keep it. NoRoute cannot discharge a real shared route. Two marking sites can share id while only A is served. The separate two-source wrapper stops at run-9 only after both are served. R38 is a correctness requirement on this retirement, not a second independent stopping rule. |
| **R39, regular intersection.** A fresh wrapper writer prepends g or h recursively and ends in f. A prefix reader consumes g or h recursively and ends in g. The coarse `z.M/T,D` yields `ZERO→DT,D`. | The signed regular reference has the repeated DT and backwards permission in every later pair. The disabled native control reaches run-9/POLICY. Its certificate adapter stops at run-5. | R17 keeps the live observation and R38 has no NORMAL witness. But the field-membership test below already proves this route impossible. R40's cell algorithm can also handle empty right chunks. The product is a cheaper regular implementation of the general language decision, with no independent necessity shown in this fixture. |
| **R40, nested state-pair closure.** Use `g*f` for the writer. Reader base `return p.g`, recursive arms `read(p.g)` and `read(p.h).h`. The coarse `z.M/T,D` yields the same DT. | With no NoRoute certificate, the clean return cone repeatedly carries the DT and the backward permission. The disabled native control reaches run-9/POLICY. The nested certificate adapter stops at run-5. | The R39 compiler rejects the nonempty right chunk in `h·R·h`. R17 and the NORMAL-only R38 proof cannot close the route. The field-membership test still proves this fixture disjoint. The native same-terminal and parity controls already stop naturally, so they do not supply an independent termination witness for the general closure. |

**Smaller-certificate control.** For the checked linear grammars, a
finite derivation reaches a base rule. Compute a field required by
every base on one side and absent from the other side. Include the
fixed outer positions. Test both directions.

```text
absentRequiredField(L, R, outerL, outerR):
    if either extraction is incomplete or L has no base clause: return Unknown
    must = fields(outerL) ∪ intersection(fields(w) for each L base word w)
    may = fields(outerR) ∪ union(fields of all R base, left and right chunks)
    if must minus may is nonempty: return NoRoute
    return Unknown
```

Compute the intersection and union with sets of accessor IDs. Work
is linear in the total clause fields and the outer words with
ordinary set operations. Every L word contains every element of
`must` by induction on its final base and outer position. Every R
word uses only `may`. Both negative fixtures have f in the difference.
This check can replace the language solver in the proof model and
supplies the same NoRoute premise. It does not replace validation
of the extraction or the other root control uses.

The wrapper isolates the need for source-specific terminal retirement
in its reference. The field-route fixtures isolate the need for an
absence proof. They do not justify adding the general product or
nested closure to production. None of these claims assumes a
run-11 cutoff or a combined production experiment. [Wrapper recurrence](../docs/reports/bidirectional-recursive-target-termination-20261117.md) ·
[Regular controls](../docs/reports/bidirectional-branching-field-termination-20261117.md) ·
[Nested controls](../docs/reports/bidirectional-two-sided-field-search-20261117.md)

### Examples diff

Each set below lists outgoing guidance in the previous edge's orientation.
For instance, `ZERO→DT` will select actual ZERO in the next run at the
matching typed entry.

| Rule and input | Current handoff | Proposed handoff |
| --- | --- | --- |
| R28. Backward after-loop block publishes `ZERO→x.f.$/T,N`. | `{ZERO→x.f.$/T,N}` in the block's reversed scope. | `{ZERO→x.f.$/T,N}` in the same reversed scope. |
| R28, paired C5. Guides `{p.$/T→DT,D; ZERO→q.$/T,D}`, raw `ZERO→DT,D`. | Publish `∅`. | Publish `∅`. Adding `ZERO→DT,D` to the guides allows publication `{ZERO→DT,D}`. |
| R28. EMPTY DATA set, with a live forward root `ZERO→DT,D`. | `{ZERO→DT,D}`. Continue. | `{ZERO→DT,D}`. Continue. |
| R33. Admitted `p.*/F{f}(mx={U})→ret.*/F{g}(mx={T}),D`. | Guide `{p.*/F→ret.*/F}`. | Guide `{p.*/F→ret.*/F}`. For a NORMAL replay record with those masks, retain `{p.*/F{f}(mx={U})→ret.*/F{g}(mx={T}),N}`. |
| R37. Run-3 root has saved `{ZERO→NT(id-1),N}` and admitted `{ZERO→DT,D}` from open goal id-2. | Guide `{ZERO→DT,D}`. | Guide `{ZERO→DT,D}`. |
| R37, two saved reports. Retained `{ZERO→NT(id-1),N; ZERO→NT(id-2),N}` and admitted `{ZERO→DT,D}`. | Guide `{ZERO→DT,D}`. | Guide `{ZERO→DT,D}`. The reports do not identify which seed consumers still use the row. |
| R37, separate control use. Same two reports, but this row also provides the only reached ZERO for `permission(B, x.f.$/T)` outside both goals. | Guide `{ZERO→DT,D}`. | Guide `{ZERO→DT,D}`. Neither NT authorizes the missing permission. |
| R38. A and B can reach the same observer. Only A contributes `ZERO→NT(id),N`; B uses `ZERO→DT,D`. | `{ZERO→DT,D}` | `{ZERO→DT,D}`. A's NT does not close B's track. |
| R39. Root has `{ZERO→DT,D}` with writer words `{g,h}*f` and reader words `{g,h}*g`. | Guide `{ZERO→DT,D}`. | Guide `{ZERO→DT,D}`. The proof model gives an empty intersection; the native handoff does not consume it. |
| R40. Root has `{ZERO→DT,D}` with writer words `g*f` and reader `g or g·R or h·R·h`. | Guide `{ZERO→DT,D}`. | Guide `{ZERO→DT,D}`. The proof model gives an empty intersection, but gives `{h.g.h}` as a possible witness if the writer supplies that word. |

#### R37 trace with two observer IDs

Only root is analyzed in this slice. The two marking actions and two
observers are local rules at the shown positions. The deep action marks
only the four-field path.

```java
void root() {
    Node a = new Node();    // A assigns T at a.g.$.
    observe1(a.g);          // Exact T observation, id-1.
    Node x = new Node();    // B assigns T at x.f.f.f.f.$.
    Node r = x.f.f.f;
    observe2(r);            // CM(r.MAY, T), id-2.
}
```

Each forward DATA fact below has ZERO as its original. Ignore ordinary
ZERO→ZERO completion in the Target columns. DT has no report ID on the
edge. The id-2 annotation identifies its proof goal, not a stored label.

| Run and guide input | Decisive facts and control | Current handoff | Proposed handoff |
| --- | --- | --- | --- |
| run-1, forward K=1. Unrestricted root ZERO. | `a.g.$/T,N→NT(id-1)`. B cuts to `x.f.M/T,D` currently and `x.f.NE/T,D` under the proposal. The reads yield `r.M/T,D→DT` at id-2. | Guide `{ZERO→DT,D}`. Report `{ZERO→NT(id-1),N}`. | Guide `{ZERO→DT,D}`. Report `{ZERO→NT(id-1),N}`. |
| run-2, backward K=1. Guide `{ZERO→DT,D}`, actual ZERO. | Root starts `ZERO→ZERO,N`. Observer id-2 emits reverse `r.M/T,D`. The reverse reads yield `x.f.M/T,D` currently and `x.f.NE/T,D` in the proposal, both matching B's declared position. | `{ZERO→DT,D; permission(B)}`. | `{ZERO→DT,D; permission(B)}`. |
| run-3, forward K=2. Guide `{ZERO→DT,D}`, actual ZERO with `permission(B)`. | Retained report `{ZERO→NT(id-1),N}`. B cuts to `x.f.f.M/T,D` currently or `x.f.f.NE/T,D` in the proposal. The reads yield `r.M/T,D→DT`. | Guide `{ZERO→DT,D}`. | Guide `{ZERO→DT,D}`. The retained `{ZERO→NT(id-1),N}` grants no reason to delete it. |
| run-4, backward K=3. Guide `{ZERO→DT,D}`, actual ZERO. | Reverse id-2 yields `r.M/T,D`, then `x.f.f.f.M/T,D`. This includes the last f at B. | `{ZERO→DT,D; permission(B)}`. | `{ZERO→DT,D; permission(B)}`. |
| run-5, forward K=4. Guide `{ZERO→DT,D}`, actual ZERO with `permission(B)`. | B produces `x.f.f.f.f.$/T,N`. The reads produce `r.f.$/T,N`. Observer 2 emits `ZERO→NT(id-2),N`. | Guide `∅`. Reports `{ZERO→NT(id-1),N; ZERO→NT(id-2),N}`. | Guide `∅`. Reports `{ZERO→NT(id-1),N; ZERO→NT(id-2),N}`. |

Deleting the run-3 DT just because the root already has NT(id-1)
would leave `∅` at that handoff. The root has no DATA summary or
alternative activation for id-2. It would stop before run-4 supplies
B's permission. In the R37 proof model, an id-1 DT derivation can set the bit to
false first. The id-2 derivation then upgrades the same anonymous
row to true. Native handoff keeps the row without consulting a bit.

## 7. Proof and activation

### 7.1 Checks performed by the analyzer

Use the existing AP operation and compare its actual output at the
stage where the implementation would skip work. The table states the
permitted checks. A missed check keeps the ordinary result. The
implementation does not construct a graph of uses or run a proof recipe.

| Operation | Native decision |
| --- | --- |
| R07/R08 query map and R20–R22 raw C5 | Use the C2 and C5 operators and qualified rows in §§2–3. Enable together for the scopes covered by the comparative proof. Outside those scopes use the native C2/C5 pair from the start of analysis. The reference raw image specifies `RestrictedInitialPolicy.canStoreInitial`; it is not a lookup into actual call-offer history. |
| R11/R12 child and saved contribution | Keep the ordinary coarse contribution when the available child result differs in original, applied result, layer, E, mx, H or destination. Only ordinary exact-result deduplication can remove equal already applied results. It happens after the distinct native effects have run. A child hypothesis or an uncombined child result cannot replace the contribution. |
| R15 provisional saved MUST reply | Use the ordinary possible replay when the definite matcher does not apply and the native possible lane succeeds. The resulting D local may use the completed-output rule in §4.1. No special drop at the record match. |
| R16/R17/R19 actual DATA | Filter at completed statement output as in §4.1. Preserve calls, live local paths and boundary outputs, including ones with a ready NORMAL cover. |
| R18/R23/R24 executable summaries | Run exit effects and C5. Use native exact membership and existing same-layer subsumption. Keep a distinct D membership if its provider is only NORMAL, even with the same geometry. There is no new pre-C5 skip based on a saved record. |
| R09/R23/R25 outgoing guidance | Compare the complete normalized next-run rows, including the matched owner and physical ports. Keep distinct origins unless the existing C2/C5 compactor relation is proved for the updated tail/mark cells. Equality of the entire projected row suffices at insertion. Preserve all of an ND origin's projections. |
| R37–R40 root DT | Keep the admitted DT and its native seeds. The abstract closure proofs in §§6.4–6.5 do not authorize a drop using the current stores. |

The root and block handoff use the typed lookup and projection in §6.
Use the existing forward stop test on the built demand index. The
run-1 static view retains its own native preflight. Enable a changed
static view only after verifying that its qualified C2, C5, Target and
empty-frontier results agree with the specified reference for that view.
This check is part of verification, outside the analysis worklist.

### 7.2 Proof boundary

Point containment proves spatial support. It does not prove preservation
of the next source permission, paired publication or Target. The Lean
models can compare complete sets of effects or show that a proof would
suffice if all uses were available. Their use lists and derivations are
proof inputs. Inspecting an already observed prefix of forward or backward
runs cannot construct those inputs for a live fact. The analyzer uses the
native gates above.

For the completed-output filter, the native statement dispatch or
block router yields the complete first destination list. The form test
shows that every skipped delivery has an empty effect. Induct over
subsequent worklist processing and then the run handoffs. The same
semantic inputs reach every rule, publication and source-permission
query. Iteration timing and processing counters may change. In
particular, this proof does not imply termination of the earlier
examples that needed a live coarse reply or anonymous DT to be removed.

### COMPLEX

The proof inputs are checked outside the worklist. The active
analyzer has no general proof search or validation over future runs.
Sections 3.4 and 6.6 give the additional candidates and their
rule-disabled controls.

### Examples diff

| Proof input | Current route or basis | Proposed route or basis |
| --- | --- | --- |
| A run-3 reply `x.f.M/T,D` is needed to emit `ZERO→DT,D`. A replacement claims a permission first available in run-5. | Keep `x.f.M/T,D` and the resulting `ZERO→DT,D`. | Keep `x.f.M/T,D` and `ZERO→DT,D`. The call destination fails §4.1. |
| At the normal port, a reached backward ZERO needs `ZERO→DT,D`. The proposed child supplies only `p.f.$/T→ret.$/T,N`. | Keep `{ZERO→DT,D}` for the reached ZERO. | Keep `{ZERO→DT,D}`. The DATA edge does not serve it. |
| A and B are qualified guides, `A=ret.*/T→p.NE/T,D` and `B=ret.*/T→p.M/T,D`. | The corresponding same-head MAY rows deduplicate to `{ret.*/T→p.M/T,D}`. | Keep `{A; B}`. Different NE and MAY keys do not use exact-row compaction. |

[Constructive rule proofs](lean/proposals/demand-refinement-spec-20261117/README.md) ·
[Joint service proof](lean/proposals/demand-no-loss-audit-20261117/README.md) ·
[Scalar, continuation and handoff checks](lean/proposals/demand-spec-clarification-20261118/README.md) ·
[Termination examples](../docs/reports/bidirectional-demand-termination-counterexamples-20261115.md) ·
[Validation](../docs/reports/bidirectional-termination-fix-validation-20261117.md)
