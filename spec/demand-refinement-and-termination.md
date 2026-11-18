# Demand refinement and termination

This specification defines bounded refinement and demand retirement in
FULL mark mode of the bidirectional access-path analyzer. Run forward at
limit 1 in run-1, backward at limit 1 in run-2, then alternate direction
with limits 2, 3, …. A policy cutoff is separate from natural termination.
In the examples, **current** means the native FULL rules at `8da26aa13`.
**Proposed** means the qualified rules below with their proof guards satisfied.
For a proposed-only tail or certificate, the current column gives the
corresponding native case and names the substitution.

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
semantics, restricted admission and publication, proven reply suppression,
cleaner transfer, and sealed demand retirement. They can change demand,
report timing and delivery counts. Selected EXACT cleaning of concrete
MUST has the explicit precision tradeoff in §5.

### Examples diff

| Rule and input | Current | Proposed |
| --- | --- | --- |
| R29. Equal geometry with H=0 and H=1 | Keep both memberships. A pass carries the input flag. | Same. An NE result also keeps both flags distinct and a pass creates neither flag. |
| R30. Later `{p.$/T,q.$/U}→ret.$/V`, only p supplied | No reply. | Same. A guide for p alone does not satisfy the q arm. With both arms in one binding, application joins both support layers. |
| Static completion. `ZERO→C.f/T` and `C.f/T→DT` at run-1 handoff | The run-2 virtual lookup supplies `ZERO→DT` in the eligible owner. | Same lookup and typed output. Any NE DATA entry uses its nonempty region in that same virtual row. |
| Backward exceptional ZERO at a block with a normal `ZERO→DT` guide | Borrow the normal control entry for the reached ZERO, at the real normal invocation. | Same. A DATA NE input still uses its own physical port. |

## 2. Field transfer and C2

| Rule and affected part | Required behavior and principal example | Proof |
| --- | --- | --- |
| R01–R03 · DATA grammar, cut, transfer, handoff | A real cut emits NE. A cut of `x.f.g.h.$/T` at limit 1 gives `x.f.NE/T,D`, with empty E and the same mark, mx and H. Apply at every existing real field cut, including run-1. Uncut M stays M. For `y=x.f`, `x.NE` gives `y.M,D`, `x.f.NE` gives `y.NE,D`, and `x.$` gives no y. For `x.f=y`, keep `x.f.M` from `y.M` and `x.f.NE` from `y.NE` while f fits. If f is cut, both give `x.NE,D`. An intrinsic MAY supply can include the root. | The removed suffix has a first field, and its old point lies in the retained head's NE region. An unknown read can consume the entire suffix. An uncut write can put the former root at the newly named field. |
| R04–R06 · C2, call binding, raw C5 | For same-head `p.M/T ← p.M/T`, start `p.$/T,D` and `p.*/T,D`, plus the conditional FLOW companion. NE keeps the nonempty case. A frozen `p.f.M` row can use a compatible ancestor `p.*` as a **possible** offer, within its prepared budget. Keep the real caller binding. | Empty and nonempty suffixes exhaust M. Each primary authorizes only its stated companions. Possible field binding joins as D. A FLOW hypothesis alone supplies no concrete-mark witness. |
| R07 · C2, raw C5 | `p.M/T ← p.f.MUST/T {g},N` starts `p.f.*/T,D` and its FLOW companion. Carry `{g}` on both STAR starts at the unchanged actual head. Apply only in restricted FULL for a concrete demand and a STAR or MUST actual. | At the same head the copied mask denotes the same forbidden subtrees. E cannot move to another head. The map adds no seed and changes no start layer. |
| R08 · C2, raw C5, field limits | For `p.M/T ← p.f.g.MUST/T {g},N`, replace the two eligible shorter STAR starts by `p.f.g.*/T,D` and `p.f.g.*/F,N`, both with `{g}`. Keep the conditional `p.$/F` probe. | The actual head and holes stay together. Every overrun of Dc+1 comes from the certified map below. The global and paired output caps still hold. |
| R13 · raw transfer | For `x.f.g=new Node()`, reject the strict-descendant keep at `x.f.*` per leaf when the actual is `x.$/F`. The keep at `x.* {f}` still yields the exact root with `{f}`. | No strict descendant lies in the exact point. The same-head keep records the real overwrite exclusion before normalization. |
| R32 · run-2 C2 and raw C5 | Start the requested STAR identity in backward run-2 for a same-head precise STAR demand and STAR actual. `set(p){ p.f=new Node(); return p; }` through wrappers can then produce the NORMAL relation with `{f}` and preserve `p.g/T` at run-3. Retain the existing admitted deeper-actual run-2 STAR case. | Same base/head requires no extra field. C5 uses the same raw family. The wrapper proof relays NORMAL service through any finite number of wrappers. |

### 2.1 Legal starts and marks

C2 runs on a scalar actual and one qualified pair `Dp→Dc`. It first
checks owner, direction, physical entry, base, mark, legal static shape
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
  Check that other required callers and guides keep their service before
  applying either replacement.

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
| Saved NORMAL replay, predefined summaries and R18 precoverage | K on delivered DATA | Replay/model input is outside fresh C2/C5 publication. R18 skips a redundant candidate only if the existing whole image fits K and all services are retained. Any newly inferred caller summary still passes its own C5. |
| Loop own-ZERO exception | Ordinary K and C5 cap if DATA is emitted | Bypass the extra loop growth gate only. |

The output limit uses the previous pair's **Dp**, even when it is longer
or shorter than the current raw premise P. There is no general
`FL(C) ≤ FL(P)+1` rule. In a multi-row packet, cut each selected leaf
before union. A covered uncut leaf does not justify skipping another
row that would emit a cut D variant. An early exit needs coverage of
every remaining row's **capped** membership, including layer and H.

### Examples diff

Each listed initial is an identity. F means FLOW, and the unqualified
examples fit the global budget.

| Rule and input | Current emitted result or initial set | Proposed emitted result or initial set |
| --- | --- | --- |
| R01. Cut `x.f.g.$/T,N` at K=1 | `x.f.M/T,D` | `x.f.NE/T,D` |
| R02. `y=x.f` on the result of a cut at x, then on a known `x.f` prefix | `x.M/T,D→y.M/T,D`; `x.f.M/T,D→y.M/T,D` | `x.NE/T,D→y.M/T,D`; `x.f.NE/T,D→y.NE/T,D` |
| R03. `x.f=y` with `y.M/T,D` and room for f | `x.f.M/T,D` | Same while f fits. A subsequent cut at x gives `x.NE/T,D` instead of `x.M/T,D`. |
| R04. `Dc=p.M/T`, actual `p.M/T,D` | `{p.*/T,D; p.*/F,N}` | `{p.$/T,D; p.*/T,D; p.*/F,N}` |
| R05. Previous cut produced `Dc=p.M/T` currently, `p.NE/T` in the proposal. Actual `p.$/T,N` | `{p.$/T,N}` | `∅`. With actual `p.f.$/T,N` both admit the field point, and only the current M family adds the prefix FLOW probe. |
| R06. `Dc=p.f.M/T`, actual `p.*/T,D`, after run-2 | `∅` | `{p.f.$/T,D; p.f.*/T,D; p.f.*/F,N}`, with possible binding. Add `E={f}` to the actual and both sets are empty. |
| R07. `Dc=p.M/T`, actual `p.f.MUST/T {g},N` | `{p.f.*/T,D; p.f.*/F,N; p.$/F,N}` | Same set, with `{g}` on both `p.f.*` starts. |
| R08. `Dc=p.M/T`, actual `p.f.g.MUST/T {g},N`, K=2 | `{p.f.*/T,D; p.f.*/F,N; p.$/F,N}` | `{p.f.g.*/T{g},D; p.f.g.*/F{g},N; p.$/F,N}`. The first two have FL=2, one above Dc+1. At K=1 a raw depth-2 actual is invalid. |
| R13. `x.f.g=new Node()`, raw actual `x.$/F` and strict child keep `x.f.* {g}` | The strict keep can produce an uncertain survivor. | The strict keep has no result. The same-head keep still gives `x.$/F{f}`. |
| R32. Backward run-2, `Dc=p.*/F`, actual `p.*/F,N` | `{p.$/F,N}` | `{p.*/F,N}`, including at the cap. In later restricted runs this same STAR offer emits nothing. |
| C5 cap. `Dp=ret.*/T`, raw `C=ret.f.g.$/T,N`, K=3, legal raw entry | `ret.f.M/T,D` after the row cut | `ret.f.NE/T,D`. Neither side can publish the depth-2 result under this pair. |
| Independent output budget. `Dp=ret.f.g.*/T`, current `P=p.$/T`, `C=ret.f.g.h.$/T,N`, K=3, legal raw entry | The paired cap is 3. The exact result fits. | Same. The three-field result is legal even though FL(P)=0. |

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

A child is ready for delegation only after its exact-point and suffix
service for that contribution are both proved or discharged. Freeze
routing for a shared raw query only when all its issuing consumers,
including later arrivals, have that proof. Otherwise process the
coarse contribution. Route supported primitive reads with the complete child proof. For a saved
inside read, require an Empty-E/mx STAR/FLOW query, a still NORMAL correlated
STAR/FLOW operand with empty mx, and a unary unprotected NORMAL FLOW
STAR-to-STAR record with empty mx. Operand and saved endpoint E stay at
their original heads. The saved view is opposite-direction or uses R34. Keep independent effects, unsupported aliases,
concrete, protected, MUST, DEMAND and ND outside that routing. Outer saved
replay uses the original actual. R34 may omit only its new contribution
when an already prepared child fully covers it. The R34 lane does not
create a new query and must participate in any later closure check.

### 3.2 Match and apply scalar summaries

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

Use the definite MUST matcher for saved calls, blocks, loops and service
probes. Under R15, omit a nondefinite saved reply only if every required
use of that reply is served, including later guidance from a DEMAND
result and a caller with empty current C2. Otherwise retain the native
reply. Preserve full ND binding and native port and alias behavior.

### 3.3 Raw entry witness and paired output

For R18 the retained saved provider's input prefixes P and admits the
whole P region. Its image keeps P's tail and exact native guards. Check the
skipped row's uses in publication, current delivery and handoff. Using a
current-only provider requires complete committed service to every
affected subscriber.

```text
C5(rawP, rawC):
    for each qualified pair (Dp -> Dc), including virtual pairs:
        for each candidate leaf c0 and eligible raw premise member i:
            if typed control: apply the typed pair rule in §5 and continue
            if no legal actual with i in the prepared raw C2 family of Dc: skip
            (p,c) = normalizeFLOWPair(whole rawP,c0)
            b = selectExit(c,Dp)
            if b exists:
                emit normalizeFLOWPair(p, cut(b, min(K,FL(Dp)+1)))
```

Split packed chains before pairing. Preserve the owning row on each leaf.
The raw image uses legal hypothetical offers and the complete C2 rules
above, including possible binding, prepared children, companions and
head retention. A C5 witness can be a hypothetical legal actual; it does
not grant a caller application without a real binding. A structural
implementation must construct the same witness, including a real legal
accessor if it needs one, rather than scan historical offers. A concrete
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
for the affected scope under §6.

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

### Examples diff

| Rule and input | Current | Proposed |
| --- | --- | --- |
| R09. Same Dp, `Dc=p.M` and a deeper guide after cut at `p.f` | Executable MAY coverage can hide the deeper guide. | Keep `p.f.NE` in the bounded refinement view until its own service is covered. |
| R10. `Dc=p.M/F`, actual `p.*/F`, eligible saved guard `p.f.g.*` | `{p.*/F,N}` | `{p.*/F,N; p.f.$/F,N; p.f.*/F,N}`. Both child bindings are possible at the caller. The child has FL=1. |
| R11. `y=x.f`, actual `x.*/F`, ready exact and suffix child | The coarse read emits `y.M/F,D`. | Use the proved child contribution. Omit that coarse reply only once the complete consumer check passes. A different field g still uses ordinary transfer. |
| R12. Inside an owned query, an opposite saved `p.f.*→ret.*` reads `p.*` | Emit its possible `ret.M,D` even with empty current callee demand. | Keep saved-first replay. Delegate only this contribution if the f child supplies its whole service. |
| R14. Saved `p.*→ret.*`, actual `p.f.$/T,N`, current C2 empty | `ret.f.$/T,N` | Same. No current subscription or extra admission. |
| R15. Saved `p.MUST/T→ret.MUST/U`, actual `p.f.MUST/T,N` | Provisional `ret.MUST/U,D` from the overlap lane. | Omit only with continuation service. Otherwise retain that D reply. A definite `p.MUST/T` still gets the NORMAL reply. |
| R18. NORMAL candidate `p.f.g.*→ret.f.g.*` under a short Dp | C5 can cut it and publish a D variant. | Skip that candidate when retained `p.*→ret.*` gives its complete uncut service. |
| R20. Raw `p.$/F→ret.$/F`, same head with a nonempty entry | The analogous native MAY entry checks the normalized `p.*` key. | An NE entry rejects this raw point. An admitted `p.*` witness alone cannot license it. |
| R21. Entry `p.M/T`, paired exit `ret.$/T`, admitted FLOW STAR companion, raw conclusion a cut `ret.M/F,D` currently or `ret.NE/F,D` in the proposal | Native normalized admission can accept the FLOW companion. The exit selects a provisional point, with the output mark still FLOW. | Keep the legal companion as the entry witness. The exact exit rejects NE at the same head. No other row can lend its exit or synthesize T. |
| R22. Admitted raw `p.$/F→ret.$/F,N` | Publish `p.*/F→ret.*/F,N` with legal E. | Same public relation after raw checking and the suffix-lifting proof. A result `ret.NE` survives either normalization. |
| R34. Direct saved `p.f.*→ret.*`, actual `p.*/F,N`, f allowed | No reply via direct STAR inside. | `ret.M/F,D`. If the actual excludes f the result is empty on both sides. |
| NE result. `p.*→ret.NE,D`, actual `p.f.$/T,N` | The native cut form gives `ret.M/T,D`, regardless of f. | `ret.NE/T,D`, with no f appended. Resolve a normal read of `ret.g` to M/D because g can consume the unknown suffix. |
| NE actual. Saved `p.*→ret.*`, actual `p.f.NE/T,D` | The native M actual gives `ret.f.M/T,D`. | `ret.f.NE/T,D`. An EXACT premise at the same head as an NE offer has no match. |
| NE C5. Current result `ret.NE/T,D`, paired Dp `ret.$/T` | With native M at the same head, select `ret.$/T,D`. | Empty. With Dp `ret.f.$/T`, select `ret.f.$/T,D` assuming the global and pair budgets admit it. |

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
same-tail marked coverage for eligible plain edges, including equal-tail NE
where the ordinary mask, layer and geometry checks pass. A MAY output at
p can cover an NE output at or below p with the same complete original,
scope, base, mark, mx, layer and H. Its captured NE guide remains until
the retained basis supplies its own raw C2 and paired C5 service. NE has
literal deduplication. No STAR coverage of independent M/NE or blanket
NE-prefix coverage follows from this. Same-layer MUST union fills an excluded
field only with its complete immediate child with empty E. For instance,
`x.*→y.*` can cover `x.f.*→y.f.*` with the same admitted suffix, but cannot
cover `x.f.*→y.g.*`. At handoff keep existing weaker-premise/same-result
and concrete STAR/EXACT service compaction only if the full updated C2/C5
service agrees, including all ND projections; the latter equivalence is
outside run-2. Recheck against the final basis. Individual redundancy
alone gives no joint deletion permission.

### Examples diff

| Rule and input | Current | Proposed |
| --- | --- | --- |
| R16. Ready replies `ret.MUST/T{f},N` and `ret.MUST/T{f},D` in one binding | The two support memberships can both resume. | Keep N only if the complete continuation is covered. Different H or a unique D seed use keeps both. |
| R17. Post-statement `x.h.MUST/U,N` and `x.h.M/U,D` | Both can reach the next use of x. | Keep N and omit the covered D when all required uses are served. If D is the sole route to a second marking point, keep D even with the same report ID. |
| R19. Owned exact query publishes NORMAL `ret.h.$/U`. Coarse query also yields `ret.h.M/U,D`. A disjoint `ret.k.$/V` is unadmitted. | The applicable coarse reply reaches the caller. | Omit that delivery only after the bound h proof and continuation check. Keep the k work in the owned closure and keep the bounded handoff rules. |
| R23. Same P, two outputs `a.M/T,D` and `a.f.NE/T,D` | Native MAY coverage can retain only the broad result and its handoff. | It can retain only the broad executable output, but retains the qualified child guide unless the broad basis supplies its complete C2/C5 service. Same-head `a.NE` can be removed if the M row covers that service. |
| R24. Same forward MUST P and H=1. NORMAL `P→a.MUST/T` plus cut `P→a.f.NE/T,D` | The existing protected cut result can remain even with the NORMAL uniform relation. | Omit the D relation only with whole same-lane coverage and proof of its future guide service. |
| R25. `A:p.*→q.*`, `B:p.f.*→q.f.*`, `C:p.f.g.*→q.f.g.*` have the same qualified NORMAL FLOW suffix law | Existing aligned coverage may drop specializations. | The final basis must also prove the service of any omitted guidance. If B is removed, use A for C in either arrival order. |
| R27. At one owner a point command and an uncertain STAR command are both ready | Ordinary FLOW priority and batching can defer the point's publication. | Drain ready point and high-lane provider work before dispatching the next low-lane command. Use FLOW-first inside each lane. Already delivered effects remain. |

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

### 5.1 Typed matching and next-run rows

For R28/R33, select admitted DATA whose layer is D, whose original is
ND, or whose original is singleton ZERO in backward. Apply the native
selection to methods and scoped blocks. Backward executable ND is
invalid. For example, backward `ZERO→x.f.$/T,N` in a loop's after block
provides the next forward C2 guide at that block. Project each selected
pair with its physical ports and original pairing. NE remains NE in Dc. Use only existing forward MUST
guidance projection and reverse views. Persist admitted NORMAL records,
including real E/mx. For the frozen guide, clear mx from FLOW endpoints
only. The saved record continues to use its own mask.

| Pair component | Match and result |
| --- | --- |
| Dc is DATA | Use C2 and the raw C5 image, or the contributing-member test for ND. |
| Dc is ZERO or DT | Only an actual ZERO at the permitted entry starts/serves this control binding. |
| Dp is DATA | Use scalar selection and its own cap, including from a control entry with a legal ZERO original. |
| Dp is ZERO | Accept only a ZERO result or a DT publication under that same paired entry. |

A DT publication uses the ordinary paired control restriction. A backward
saved source relation that returns ZERO uses the native ZERO-to-DT
conversion and source permission route. NT composes only with NORMAL.
It remains forward-only, keeps its report ID and existing deduplication,
and uses its separate NORMAL report protocol rather than DATA C5. Do not
satisfy a DATA selector with ZERO or a Target. At a sealed forward barrier
stop only when the full outgoing frontier is empty, including applicable
virtual DATA and DT guidance. On a reached exceptional backward ZERO
the borrowed normal rule in §1 applies only to the control match.

### 5.2 Terminal service

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

### Examples diff

| Rule and input | Current | Proposed |
| --- | --- | --- |
| R26. Selected EXACT cleanup of T at x with incoming `x.MUST/T,N` | A partial survivor can be D and renew a Target. | Keep `x.MUST/T,N` with its survivor H. An exact observer at x can now report on this retained uniform result. |
| R35. Selected EXACT cleanup at `x.f.g` in `x.MUST/T,N` | The descendant point can demote a broad survivor. | Keep the original NORMAL uniform region. A nonuniform EXACT fact at the cleaned point still dies. |
| R36. Restricted ALL at `x.f.g` with `x.MUST/T,N` | A partially cleaned region can remain only as a broad D result. | Emit `x.MUST/T{f},N` and `x.f.MUST/T{g},N` if both fit. BELOW also keeps `x.f.g.$/T,N` if it fits. |
| R31. `clearExactT(p); return p.g` | The FLOW cleaner can attach mx={T} to the getter's flow. | Keep T eligible on the disjoint `p.g` cone. Keep the mask where the cone contains the cleaned point. |
| R28. Backward `ZERO→x.f.$/T,N` in an after-loop block | Retain the native ZERO-origin guidance. A remaining DT keeps the analysis active even with no DATA demand. | Same. Also preserve a cut NE entry and its real paired scope. |
| R33. FLOW summary with mx={T} used to derive a guide | The guide has empty mx. Saved replay still excludes T. | Same, including both endpoints of the paired projection. |
| R37. A recursive relay continues to publish root `ZERO→DT` with only closed terminal origins | The anonymous row can keep renewing. | At a sealed forward handoff with a frozen complete proof, omit that row. Other scoped DATA and terminal rows keep their own handling. |
| R38. Two marking sites A and B share one observer ID. Only A has a NORMAL track. | The root `ZERO→DT` remains. | It still remains until B and every other root use are served. Later retirement uses both tracks, not the one report ID. |
| R39. Writer words `{g,h}*f`, reader words `{g,h}*g` | Cuts can hide the final mismatch and repeat the root Target. | A closed empty product discharges the route. If it is the last root use, the frozen proof lets the frontier drain. |
| R40. Writer `g*f`, reader `g or g·R or h·R·h` | The opposite sides of the recursive call can keep creating possible matches. | A closed nested state-pair relation proves disjointness. With a real `h.g.h` writer route the certificate fails and keeps guidance. |

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

### Examples diff

| Case | Current | Proposed |
| --- | --- | --- |
| Planned deletion relies on a source permission only obtained in a later run | Native processing retains the original path. | The replacement fails its run-order check. Keep the original path under the fallback rule. |
| A proposed child route meets a DATA value but loses the only scoped ZERO guide | The native paired scope can still start that consumer. | The DATA witness is insufficient. Activation needs the matching ZERO route or a complete retained alternative. |
| Both A and B are individually removable using each other | Ordinary processing retains a basis. | The joint proof cannot use a deleted provider. Keep a basis that supplies each needed continuation. |

[Constructive rule proofs](lean/proposals/demand-refinement-spec-20261117/README.md) ·
[Joint service proof](lean/proposals/demand-no-loss-audit-20261117/README.md) ·
[NE application and limit checks](lean/proposals/demand-spec-clarification-20261118/README.md) ·
[Termination examples](../docs/reports/bidirectional-demand-termination-counterexamples-20261115.md) ·
[Validation](../docs/reports/bidirectional-termination-fix-validation-20261117.md)
