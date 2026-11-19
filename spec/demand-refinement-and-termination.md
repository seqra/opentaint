# Demand refinement and termination

This specification defines bounded refinement and fact handling in
FULL mark mode of the bidirectional access-path analyzer. Run forward at
limit 1 in run-1, backward at limit 1 in run-2, then alternate direction
with limits 2, 3, …. A policy cutoff is separate from natural termination.
In the examples, **current** means the native FULL rules at `0438facd2a09e44a386b829cb2f1f4fe3d3954a8`.
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

## Scope and adoption

Start with work removal in the native pipeline. The cost-repair profile
uses the following implementations. The other transfer, qualification
and live-reply variants below remain candidates. Each variant requires
its own work, reachability and project checks (§8).

| Rule | Profile |
| --- | --- |
| R13 | Reject the invalid strict-descendant keep at an EXACT FULL nonstatic head. Collect the first result directly and use the read-only loop C5 shortcuts in §8.1. |
| R26, R35 | Reuse the structural observer guard at the selected cleaner site. Check the uncleaned witness for each leaf (§5). |
| R36 | Pack the residual partition in one trie where exclusions permit. Use the native fast path for the simple cases (§5). |
| R41 | Bypass unused compaction indexes and build the joined saved-record index once. Use the applicable closed proof at the completed forward seal (§7.1). |
| Field limit | Deliver an already fitting packet directly when its protection permits it (§8.1). |

Select at most one R41 proof mode for a scan. The measured profile
uses the closed observer check for one configured root and the
closed run-pair check for two to four configured roots. It uses
their ordinary fallback on a failed check. Keep local retirement
available as a separate profile.

| Change | Current | Proposed | Affected stages |
| --- | --- | --- | --- |
| Retire acyclic copy demand | A previously learned transfer can regenerate a broad DATA obligation after every C5 cut or inside read. | R41 removes that obligation at the seal when independently retained replay supplies every required use. | Handoff, saved replay verification |
| Retire an acyclic root obligation | An anonymous DT can recur after all its source-to-observer relations have NORMAL witnesses. | R37/R38 retire the root row only after every use has a frozen receipt or an acyclic NoRoute proof. | Forward handoff, next-run control |
| Retire served uniform cut guides | A definite uniform reply and a covered cut can trigger independent continuation work. | R42 at handoff requires complete same-lane application and continuation service. Live reply folding is a separate candidate. | Handoff first, reply admission separately |
| Refine genuine unresolved suffixes | Real cuts and reads with unknown suffix use the same MAY category. | Candidate NE and local rules in §§1–5 for validated nonstatic, noncyclic scopes. The first implementation keeps native transfer, C2 and publication semantics. | Transfer, C2, C5, delivery |
| Stop at a certified forward seal | A nonempty frontier can continue after every report has a retained NORMAL receipt, or after two native transfers have shown that the whole state will repeat. | The two run-level R41 candidates in §7.1 use a complete receipt or repeated-state proof. Select either stopping policy separately from local demand retirement. | Completed forward seal, driver stopping |

The driver, run schedule, typing of ZERO/Targets, ND application join,
physical ports, report identities and saved-first policy use the native
contract. Recursion and loop-specific retirement, including R39/R40, are
postponed. A cyclic endpoint or unresolved boundary gives Unknown to a
local certificate. Method-local eligibility gives no proof for a caller
loop's Target. A run-level certificate can use a completed native run
that contains a loop because it proves the whole transition. Run-1
static shortcuts and lazy static completion use their native behavior.
Keep the production run-11 policy and use run-101 in the termination suite.

A selected rule cannot be enabled using only a reference model stop.
Section 8 specifies how to validate the native correspondence and reject
a rollout with higher work or changed required reachability.

The isolated rule experiments identified five useful rules. R13 removes
an invalid field-transfer result. R26 and R35 change the layer for a
selected cleaner survivor in a closed observation scope. R36 preserves
the NORMAL layer of the exact residual region after a deep cleaner. R41
discharges a FLOW demand using independently retained service. The
cost controls below apply to these variants individually. See the
[rule experiments](../docs/reports/bidirectional-demand-refinement-rule-prototypes-20261118.md)
and the [cost-fix checks](../docs/reports/bidirectional-useful-rule-cost-fixes-20261119.md).

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
run-1 to those transfers only in the corresponding candidate variant.
The candidate changes to tail and cut semantics, restricted admission,
publication and cleaners can change demand, report timing and delivery
counts. Selected EXACT cleaning of concrete MUST has the precision
tradeoff in §5.

### COMPLEX

The first implementation uses the native scheduler and block layout.
R27 is a separate scheduling candidate under §8.3.

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
| R01–R03 · DATA grammar, cut, transfer, handoff | A real cut in a validated scope emits NE. A cut of `x.f.g.h.$/T` at limit 1 gives `x.f.NE/T,D`, with empty E and the same mark, mx and H. Apply at every existing real field cut in that scope, including run-1. Uncut M stays M. For `y=x.f`, `x.NE` gives `y.M,D`, `x.f.NE` gives `y.NE,D`, and `x.$` gives no y. For `x.f=y`, keep `x.f.M` from `y.M` and `x.f.NE` from `y.NE` while f fits. If f is cut, both give `x.NE,D`. An intrinsic MAY supply can include the root. | The removed suffix has a first field, and its old point lies in the retained head's NE region. An unknown read can consume the entire suffix. An uncut write can put the former root at the newly named field. |
| R04–R06 · C2, call binding, raw C5 | For same-head `p.M/T ← p.M/T`, start `p.$/T,D` and `p.*/T,D`, plus the conditional FLOW companion. NE keeps the nonempty case. A frozen `p.f.M` row can use a compatible ancestor `p.*` as a **possible** offer, within its prepared budget. Keep the real caller binding. | Empty and nonempty suffixes exhaust M. Each primary authorizes only its stated companions. Possible field binding joins as D. A FLOW hypothesis alone supplies no concrete-mark witness. |
| R07 · C2, raw C5 | `p.M/T ← p.f.MUST/T {g},N` starts `p.f.*/T,D` and its FLOW companion. Carry `{g}` on both STAR starts at the unchanged actual head. Apply only in restricted FULL for a concrete demand and a STAR or MUST actual. | At the same head the copied mask denotes the same forbidden subtrees. E cannot move to another head. The map adds no seed and changes no start layer. |
| R08 · C2, raw C5, field limits | Preserve the already bounded, deeper actual head and its nonempty E on the eligible concrete STAR start and its FLOW companion. Keep the conditional EXACT/FLOW prefix probe for M demand. | The actual head and holes stay together. Every overrun of Dc+1 comes from the certified map below. The global and paired output caps still hold. |
| R13 · raw transfer | For `x.f.g=new Node()`, reject the strict-descendant keep at `x.f.*` per leaf when the actual is `x.$/F`. The keep at `x.* {f}` still yields the exact root with `{f}`. | No strict descendant lies in the exact point. The same-head keep records the real overwrite exclusion before normalization. |
| R32 · run-2 C2 and raw C5 | Start the requested STAR identity in backward run-2 for a same-head precise STAR demand and STAR actual in an enabled nonstatic scope. Use §6.3 for statics. `set(p){ p.f=new Node(); return p; }` through wrappers can then produce the NORMAL relation with `{f}` and preserve `p.g/T` at run-3. Retain the existing admitted deeper-actual run-2 STAR case. | Same base/head requires no extra field. C5 uses the same raw family. The wrapper proof relays NORMAL service through any finite number of wrappers. |

**R13 cost control.** Select the ancestor rule once per application.
For a non-EXACT packet use the ordinary ancestor result. For an EXACT
packet in nonstatic FULL, the strict-ancestor result is empty. The
legacy EXACT cases need the existing write-keep check only for a
nonempty input head. Check the nonempty exclusion and the endpoint
bases and tails before comparing paths. Compare the immutable path
cells with the existing input array. Reuse the result at each ancestor.
The same-head branch performs the exclusion update. Use the same
FULL nonstatic check in the scalar reference transfer. GROUP and
static facts use the existing write-keep exception.

**Output allocation.** Record the two REACH
layers in bit flags.
Keep the first canonical key and root for each of FLOW and TAINT
directly in the operation result. Merge another result for that
key in place. Allocate the ordered map on the first different
key. At flush, emit the direct slot, then the remaining keys in
insertion order. Keep the native REACH, FLOW and TAINT order.
The merge uses the same algebra and operands as the native map.
Mark requests retain their native callbacks. The collector also serves
other transfers. Measure it separately from the R13 guard and enable
it only after the same project checks pass.

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
E. A precise STAR identity in the enabled backward run-2 relay keeps selector E. Every
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
| Instruction results, caller replay results, and incoming actuals at admission | K at the bounded interface | Intermediate concatenation may be longer until the normal global cut. Real cuts in an enabled scope produce NE/D in every run. At a legacy interface project NE to MAY/D with the same head, mark and H. |
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
coarse transfer to those children. The candidate path keeps the coarse
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
| **R16 · ready reply delivery** | Deliver each applicable NORMAL and DEMAND reply through native matching, layer joins, complete AND bindings, aliases and post-call stages. Submit the results to ordinary post-statement admission. Equal geometry keeps separate NORMAL and DEMAND memberships. Section 7.3 defines the certified complete-packet exception. |
| **R19 · current reply delivery** | Apply every current summary that matches the caller's native binding. A ready NORMAL result for the same region leaves the applicable DEMAND reply eligible. In restricted runs, current replies come from C5-admitted results. A raw exit rejected by C5 performs no caller delivery. |
| **R23 · admitted summaries and handoff** | Keep distinct MAY and NE summary rows after C5, including when the MAY region contains the NE region. Deduplicate identical NE memberships. Project each retained row with its own premise, field head and ports. |
| **R24 · admitted layers** | Keep both by default when a NORMAL MUST conclusion covers an admitted DEMAND region. R42 adds a certified service exception for guides and complete reply packets. Retain the NORMAL row for replay and the qualified DEMAND row for the next handoff. Continue using native same-layer MUST folding. |
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
| R24. `A=p.MUST/T→ret.MUST/T,N,H=1` and `B=p.MUST/T→ret.f.M/T,D,H=1` currently. B ends in `ret.f.NE/T,D,H=1` in the proposal. | Keep `{A; B}` where both are admitted. | Keep `{A; B}`. The D guide remains `{p.MUST/T→ret.f.NE/T}` unless R42 proves the paired service. |
| R25. `A=p.*/F→q.*/F,N`, `B=p.f.*/F→q.f.*/F,N`, `C=p.f.g.*/F→q.f.g.*/F,N`. | Aligned native subsumption yields executable basis `{A}`. | Executable basis `{A}` and final service witness `A covers C` in either arrival order. |
| R27. Ready starts `p.*/F,N` and `p.$/T,N` at one owner. Their summaries are `A=p.*/F→ret.M/F,D` and `B=p.$/T→ret.$/T,N`. | A FLOW-first queue can publish `A then B`. | Publish ready `B then A`. The resulting set is still `{A; B}`. |

## 5. Cleaners

| Rule and affected part | Required behavior | Proof |
| --- | --- | --- |
| R26/R35 · concrete cleaner transfer [selected coarsening] | For selected EXACT cleaning of T at `x` or `x.f.g`, a matching same-base `x.MUST/T` can keep its region, E and cleaner-survivor H. Preserve NORMAL only under the observer guard below. Nonuniform exact T still dies at the selected point. | Split along the cleaner path and use the selected same-head policy at the final child. Union with its siblings reconstructs the original region. The erased point is a possible extra member. The observer guard prevents using that point as a new confirmed witness. D stays D. |
| R36 · concrete cleaner transfer after run-1 | For NORMAL `x.MUST/T` cleaned ALL at `x.f.g`, emit `x.MUST/T {f}` and `x.f.MUST/T {g}`, normally. Selected BELOW also retains `x.f.g.$/T`. Apply the usual caps. | Partition into one residual sibling region per field plus the optional point. The union is exactly the input minus the selected subtree. There are at most depth+1 pieces. |
| R31 · FULL nonstatic FLOW cleaner, all runs and directions | For `clearExactT(p); return p.g;`, keep the original headers of every path whose whole suffix cone is disjoint from the cleaner. Mask the remaining leaves as before. Cleaner at `p.f` still masks an abstract point probe at p because its normalized suffix can include f. | For EXACT, the cleaner head lies in the cone iff the input head prefixes it. For BELOW/ALL use prefix incomparability. This guard covers normalized suffixes too. The getter relays `p.g.h/T` with its original mark support. |

R36 applies to the partially intersecting NORMAL concrete MUST region in
nonstatic FULL after run-1. Use the native cleaner when the selected
point is at the current head or one field below it. The native one-field
branch already emits exactly the selected residual and, for BELOW, the
surviving exact point. Enter the partition only if two or more fields
remain and the full cleaner chain fits the current run's field limit.
Check this before constructing a fallback path. At each selected field
retain the current head with that
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
        if c is D or frozenObserverGuard(c, cleaner) is valid:
            return {c with native cleaner-survivor H}
        return nativeClean(c, cleaner)
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
When adjacent residuals have the same field exclusion, build one
MUST packet for those residuals. Set its leaf flag at each residual
head on the cleaner spine. Build each shared prefix once. For
`x.f.f.f` with an empty input mask this gives one packet with
heads `x`, `x.f` and `x.f.f`, all with `{f}`. A different
input mask at the first head keeps that residual in its own packet.
The packed spine has the same leaves, layer, H and marks as the
individual results. All residual heads lie on the cleaner path and
fit the global field limit. A residual can exceed the paired summary
exit budget. Ordinary C5 applies the relative cut at that boundary.
The scalar reference emits the individual residuals under the same
bounded FULL guard. Tests compare their annotated leaves with the
packed result, including the last surviving exact point for BELOW.
R31 does one prefix comparison per leaf and uses at most two packets.
Neither rule creates a C2 start or expands arbitrary field suffixes.

### COMPLEX — point cleaner observer guard

Construct the guard with the finite use check in §7.2, before enabling
a cleaner scope. Keep the removed point and the survivor region separate.
For every observation or exported continuation that the removed point
can reach on NORMAL, require an actual uncleaned witness for the same
complete origin/mark/observer or independent native service. Reject the
guard if a point-dependent branch, future consumer or binding is unknown.
A terminal local `CM(x.M,T)` can use a known uncleaned point in the same
region. `CM(x.f.g.$,T)` after removing exactly `x.f.g` has no such
point. The former can keep the broad NORMAL region for that closed
use. The latter keeps the native transfer. Account for the same origin
on every consumer of a scoped summary.

**R26/R35 cost control.** Test forward FULL and closed-root eligibility
once for the owner. The selected prototype requires the only scan root,
the method boundary and a ZERO premise. R26 handles an EXACT cleaner
on a local root. R35 also handles a descendant EXACT cleaner on a
single carrier copied through an otherwise empty resolved callee.
The call must have only the normal exit as its successor. The exit must
have one local MAY observer for the same mark and no other effect.
Refer to the immutable call plan to verify the carrier and the absence
of other consumers or rule effects. Retain at most the last verified
site result, including a rejection, in the owning run. Key it by the
instruction, immutable plan, stage and cleaner. This cache requires no
allocation until an eligible concrete NORMAL MUST packet reaches the
site. Check the uncleaned witness against each selected leaf's path,
mark, exclusion and field limit on each use. The structural result does
not authorize a new packet on its own. Release it with the owner.

The separation is valid since all paths and rule bindings in the
verified suffix are fixed for that key. Packet evidence is evaluated
under its current mark and mask. A cache hit has the same guard result
as a complete new check. A miss performs at most the old structural
check. A disallowed owner performs neither a form lookup nor a witness
walk. Consume a successful check in the existing partial-cleaner
fallback. Ordinary disjoint, kill, one-field and below-at-head paths
finish before this check in the cleaner kernel. Include guard
construction, lookup and retention in the §8.3 comparison.
R36 remains a declared field-path partition. R31 visits only the
packet already being cleaned.
[Constructive checks for R13 and the cleaner paths](lean/proposals/termination-rollback-20261118/UsefulRuleCosts.lean)

### Examples diff

| Rule and input | Current output facts | Proposed output facts |
| --- | --- | --- |
| R26. Selected EXACT cleanup of T at x with `x.MUST/T,N`. The closed MAY observer has an uncleaned witness below x. | `{x.MUST/T,D,H=1}` | `{x.MUST/T,N,H=1}` |
| R35. Selected EXACT cleanup of T at `x.f.g` with `x.MUST/T,N`. The closed MAY observer can witness `x.$/T`. | `{x.MUST/T,D,H=1}` | `{x.MUST/T,N,H=1}` |
| R35, negative observer guard. Same MUST input and cleaner, with `CM(x.f.g.$,T)` as the only consumer. | `{x.MUST/T,D,H=1}` | Native transfer gives `{x.MUST/T,D,H=1}`. No NORMAL hit is allowed for the erased point. |
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
final retained basis. Use native typed Target compaction and the
empty-frontier stop. A selected run-level proof adds the independent
stop case in §7.1.
Projection still offers at most `k·m` pairs for k result leaves and m
original members. The empty-frontier test reads the completed index count.

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

**Admission boundary.** Use the native policy for all static C2 work
and pairs obtained through run-2 static completion. An NE leaf at an
interface served by that view is passed as MAY/D with the same known head
and mark. Keep the same projection for C5 and for the typed Target path.
An explicit or virtual row remains eligible through the native query, with
its own ports and its own cap. Do not route it through the shared-carry
fast path by endpoint equality. The shared default uses exactly the
pre-rule C2/C5 variant, including the EXACT entry when that variant
emits one. There are no static child probes or possible qualifiers.

The native static query seeds coverage with explicit and carry service,
then uses the indexed reachability search only for missing service.
Keep label selection ahead of owner checks. Compare full run-2 starts and
projected pairs against the baseline when both receive the same H1 static
index and input. Reusing its matcher on the same inputs gives identical
outputs, including when an explicit row and a shared-carry row have
the same fields. The handoff must not materialize transitive pairs.

### Examples diff

Guide rows are shown in the previous edge's orientation.

| Rule and input | Current | Proposed |
| --- | --- | --- |
| R28. Backward after-loop block emits `ZERO→x.f.$/T,N`. | Guide `{ZERO→x.f.$/T,N}` at reversed ports. | Guide `{ZERO→x.f.$/T,N}` at reversed ports. |
| R28, paired C5. Guides `{p.$/T→DT,D; ZERO→q.$/T,D}`, raw `ZERO→DT,D`. | Published `∅`. | Published `∅`. Adding guide `ZERO→DT,D` admits the candidate. |
| R28. No DATA guides, live root `ZERO→DT,D`. | Guide `{ZERO→DT,D}`. Continue. | Guide `{ZERO→DT,D}`. Continue. |
| R33. Admitted `p.*/F{f}(mx={U})→ret.*/F{g}(mx={T}),D`. | Guide `{p.*/F→ret.*/F}`. | Guide `{p.*/F→ret.*/F}`. NORMAL replay keeps `E` and `mx`. |
| R09/R23. A field cut gives `p.$/T→ret.f.M/T,D` today and `p.$/T→ret.f.NE/T,D` under the proposal. | Guide `{p.$/T→ret.f.M/T}`. | Guide `{p.$/T→ret.f.NE/T}`. A broader MAY guide does not replace this NE row. |
| Run-2 static join. Matching ports and `ZERO→S.C.f.M/T,D` writer with `S.C.f.$/T→DT,D` reader. | This pair can produce virtual `{ZERO→DT,D}`. | Same result. A cut arriving as `S.C.f.NE/T,D` projects to `S.C.f.M/T,D` at this interface. |
| Run-2 implicit static carry offers `S.C.f.*/T` to a same-head selector generated by that carry. | The native family, for example `{S.C.f.$/T}` under the precise singleton selector. | The same native family. It adds no START at `S.C.f.*/T,D` or FLOW companion through R32. |

The stopping condition reads the frontier **after** §7. Remaining
DT counts as demand. The empty test and provisional reporting policy
keep their current definitions.

## 7. Discharge demand at the completed handoff

Apply these rules to the frozen result after NORMAL persistence and exact
compaction. Current-run applications and observations have already run.
Use committed NORMAL providers, a proof of no required effect, or
native guidance ineligible for every enabled retirement rule at this seal.
This gives each omitted row independent service. The first
implementation retires a projected origin only after all its pairs
have passed their checks. Keep the whole origin after a partial success.
The next demand store receives the remaining rows with their original ports.
Run the selected R41, R37/R38 or R42 check in the existing handoff walk
using the allowance in §8.2. The native fallback installs the original
pairs without starting a new analysis query.

```text
finishHandoff(joinedRun):
    normal = commitNativeNormal(joinedRun)
    origins = compactAdmittedOrigins(joinedRun)
    for origin in nativeInstallOrder(origins):
        if enabled proofs with reserved work discharge every pair's uses (§8.2):
            omit the origin
        else:
            install its native pairs
    commit native reports and seed catalogue
    if forward and the installed demand is empty: finish
    if forward and a selected run-level proof closes the seal (§7.1): finish
    apply the native continuation policy
```

### 7.1 R41 — Retire an independently replayable FLOW obligation

**Affected stages** are DATA handoff and saved-record applicability.
Start with a unary method summary `X = p.u.*/F→q.v.M/F,D` or its NE
counterpart, in restricted FULL, with empty masks and ordinary nonstatic
ports. Use a finite, acyclic prefix-copy region with stable, fully described
calls and native effects. The region includes both directions of each call
stage. Unsupported actions, cleaners, unmodeled alias effects, typed
controls and ND use native guidance. Rule checks stay in the compiled
form. An owner with a mark check is eligible when a restricted FLOW
initial cannot contribute a concrete witness or start an action used by
that check. Inspect the native rule entry points for this property.
`markCheckFacts` rejects restricted FLOW. Unconditional marking and
observation follow ZERO. Keep each concrete demand and its companions
and all live rules, seeds and Targets. Refuse a row if an unsupported
action can consume its FLOW service.

Derive a complete may-transfer relation from the compiled form. An arc
`p.u→q.v` copies an arbitrary remaining suffix. To compose `a→b` and
`c→d`, require equal middle bases. If `b=c·s`, produce `a→d·s`.
If `c=b·s`, produce `a·s→d`. Disjoint middle heads give no row.
Compose touched bases using their actual transfers. Include untouched
identity, all branch arcs and all bound call-stage copies. Include a
potential alias copy or deletion-filter path in the may relation, then
verify the actual provider has the required binding, filter and alias
effect. A form the checker cannot interpret gives Unknown.

Clip each paired relation to both endpoints of X. Preserve the nonempty
output constraint of NE. An origin is a pair of finite prefixes with
residual constraints and exact ports. Construct it without enumerating
the residual suffixes. A lack of observed rows gives no completeness
evidence.

```text
checkCopy(X):
    graph = completePrefixCopyRegion(scope(X))
    if graph is Unknown or X has an unproved non-copy use: return live
    for origin in clipPairedRelations(graph, X):
        for role in [FORWARD, BACKWARD]:
            require a retained NORMAL provider in this native replay view
            prove aligned suffix, input applicability, marks, masks and effects
            prove delivery at the removed service point through native cuts
    return discharged
```

For a same-direction STAR provider, the broad offer must begin within
the provider's premise. The opposite-direction role can use the native
inside matcher on a STAR ancestor. Split applicability by the two
finite heads and supported tail/layer cases. Keep a pair when a caller
use lacks replay service after its own cap. If an abstract provisional
output is needed by a caller, require the same saved provisional service
or a precise route with independently retained source permission. This
includes compound and reversed consumers. Use an acyclic region check
as in §7.2 if exact service is used in place of a provisional consumer.
A cover of one raw C5 result supplies no evidence about the other
paired rows. R18 applies during current-run publication.

**Closed-root continuation.** Check the one-root case before building
copy geometry. The affected owner must be a proper callee of the root.
Walk the reachable compiled forms with the same work bound as the
certificate. Reject a cycle, an unknown stage, a second observation, a
second producer or a guard with a data effect. The closed form has one
unconditional marking action at root entry and one same-mark observer
at the root exit. The root is the only external entry. Require a
retained ZERO-to-NormalTarget with that observer's exact identity.
This receipt supplies the observable track from the only producer.
The remaining pure copies cannot create another observable effect.
The local replay check still applies to every paired row.

For a wider caller scope, check the complete affected continuation
from the result binding in the compiled form. A root reply can
replace a lost MAY reply for a same-mark root use. It cannot authorize
deleting an unresolved descendant read or a coarse-only C2 route.
Check forwarded carriers, later boundaries and reverse permissions as
part of that proof. Keep the origin if any such use is unresolved.
For example, an append can write the incoming point to both `ret`
and `ret.content`. The next call can read `this.content`. A proof
for the return root must cover that named-field use through the
explicit write. It must also cover any different aliases, rule
activation or call admission caused by the broader reply.

**Proof.** A shared middle location gives one of the two prefix
composition cases, with a constructive suffix witness. Induction over
the finite graph covers each concrete origin behind X. An aligned
provider with extra prefix s executes the same transfer by applying it
to suffix `s·t` for the origin's suffix t. The role, guards, ports and cap
checks make the route executable before current demand admission can
skip the callee. Forward and reverse service are checked independently.
Replace each use with its saved route. Simultaneous replacement is
sound because no omitted row is a provider. A deeper direct row with
the right output but a rejected broad STAR actual fails this check.
[Prefix and native replay proofs](lean/proposals/normal-backed-demand-20261110/README.md)

**Principal trace.** In the OWASP helper, b is one of the two modeled
byte fields and `[]` is one array element.

| Path | Current handoff | Proposed |
| --- | --- | --- |
| Raw `p.b.[].*/F→ret.b.[].*/F,N`, cap 1 | `p.b.[].*/F→ret.b.M/F,D` | Saved `p.*/F→ret.*/F,N` serves the precise correlated transfer. Retire the pair when every other origin and use passes the check. |
| Read of known b then unresolved element | `p.b.*/F→ret.M/F,D` | Saved opposite `ret.*/F→p.b.[].*/F,N` gives a possible reply on `p.b.*/F` and an exact reply on `p.b.[].$/T`. A direct-only deeper provider keeps the pair live. |
| Reversed write | `ret.*/F→p.b.M/F,D` | Opposite `p.b.*/F→ret.b.*/F,N` serves the reversed route. Check the caller's binding and cap. |

The baseline has six forward and eight backward helper rows through
run-101. The audit checks 2,374 clipped origin instances from the 12-row prefix
relation in both native record roles. Activation requires checking current
compiled-form completeness and the caller and reverse permission checks. A native diagnostic omitted only the six helper pairs after run-7.
It reached natural run-11 with both confirmed identities. The caller
and block control pairs drained under the ordinary policy. A different
live DT still needs its own proof under §7.2.
[Baseline trace and audit](../docs/reports/bidirectional-termination-baseline-run101-20261118.md)

#### Candidate for a complete set of retained reports

For a bounded closed-root scope, the proof in R41 already establishes
that the root's exit observer is the only observer in the reachable
compiled forms. An alternative is to use that fact at a completed
forward seal and stop as soon as the root's NORMAL receipt exists.
This changes the driver stopping condition. The analyzer publishes
the current summaries and accepts the current reports as usual.

```text
if the frozen call closure is complete:
    sites = possible native observer identities in the closure
    require every site has a retained root NORMAL receipt
    commit the native report and stop at this seal
otherwise keep the native continuation
```

Use the exact physical identity of method, instruction and rule.
Include the configured entry, call and exit observer sites, every
compiled call alternative and any observer identity from a retained
Target that can reach a configured root. An open call-graph boundary
or uncertain observer identity gives Unknown. Use the compiled FULL
forward forms already cached by the native run. A missing context,
graph or form gives Unknown and does not start lowering. Stream
each observer test while walking the closure. Read exit positions
from the borrowed forward graph. Use the cached rule slots at those
positions. Reject at the first missing receipt or at a call to a
context still being visited. Use depth-first order, with one visit
state per context. A completed visit has finished all children.
Thus every edge in an accepted scope goes to an earlier completion
and the call graph has no cycle. This retains the native recursion
controls outside the measured proof scope. Charge the
retained Target and receipt enumeration before entering the closure.

Every future observation must have an identity in this complete set.
Its committed report is retained across later runs. Since all possible
latest reached identities also have a NORMAL receipt, the cutoff
would add no provisional report. This proof neither waits for a
specific field limit nor requires that future DATA states repeat.
The report consumes the retained descriptor of the first NORMAL
receipt. The proof covers that descriptor and confirmed status. An
observer can also be reached through a second marking action that
would give the same report identity. If separate tracks are required,
establish complete track coverage or use the ordered run-pair or
local retirement proof. Reserve the closure walk and its scratch
before attempting the check.
[Observer receipt proof](lean/proposals/termination-rollback-20261118/ObserverCensus.lean)

#### Candidate for a closed pair of native runs

The local R41 check needs a proof for each continuation that can
distinguish a saved precise reply from a removed MAY reply. A second
candidate proves that the entire remaining frontier can do no new
observable work. This is a new stopping condition. It changes the
driver at the completed forward seal. C2, C5, the native report
commit and ordinary publication use their existing operations.

Let `S` be the complete state sealed two runs ago, and `B` the
successor after the backward run. Include ordered demand with its
ports, source and observer seeds, the saved record and Target views,
condition contributors and the report state. Roots, compiled forms
and runtime configuration must remain stable. Compare actual
semantic values. A demand count, hash alone or matching method keys
cannot close the pair.

```text
after completing a restricted forward run:
    require prior two transitions both completed
    require exact sealed state == S
    require complete witness of native transitions S -> B -> S
    require each witnessed limit read gives the same result at every higher limit
    require all reached report identities already have a root NORMAL receipt
    commit the native report and stop at this seal
on any failed or incomplete check:
    use the native continuation
```

The native witness must include root admission and routing. Start
with one effective runner and one admitted root in each of the two
runs. A rejected start can be discarded only when its admission is
also independent of the higher limit. Require that the other runners
cannot deliver work to the effective runner. Count actual accepted
starts at the native admission. Actor creation at a configured root
can also happen through a call, so the number of root actors is a
diagnostic only. During an eligible pair witness, record the first
accepted non-start post to each runner under the existing admission
lock. This includes direct delivery posts as well as posts through
the router. Later posts to that runner need no new audit entry.
Intra-unit work owned by an actor belongs to that actor's unit.
Check this set with the joined actor units. A different unit with an
accepted data post makes the certificate ineligible. The ordinary
router and dequeue loop need no trace or audit lookup.
With one semantic producer, the event queue orders
active work by its immutable rank, step and sequence keys. A rejected
start is removable only when it has no semantic effect and erasing it
preserves the active event order. Account for any other source of
work or ordering that can affect the run. If this correspondence
cannot be established, keep the native path.
[Accepted-post proof](lean/proposals/termination-rollback-20261118/JoinedRouting.lean)

Observe global cuts where the runtime already tests a raw packet
depth. Observe depth rejection in C2 and the global clamp in C5
at their existing comparisons. The cost-fixed build has two more
global limit reads. The deep selected cleaner uses
`cleanerDepth <= limit` to select the MUST residual. The point
cleaner witness uses `headLength + 1 <= limit` to select NORMAL.
A failed test in either operation invalidates the witness. A relative
C5 cap remains in effect. Require a complete audit of the configured
native path and reject on any dependent or unknown global read.
Keep the failure bit set through the completed seal. Saturate optional
diagnostic counts so count overflow cannot clear that bit.
Gate the audit before allocating a comparison snapshot and charge
its bounded retained data and verification to §8.2. An audit is
never required for the ordinary native path. Put audit state in the
owning scan and pass it through the existing execution context.
Concurrent scans have independent audit state. It takes no part in
fact, key or mode equality.

Use only post-run-2 transitions for this certificate. The run-2
static input checks and its special STAR admission depend on the
iteration number. The later phase may compare a forward seal to an
earlier forward seal only after the backward and forward witness
runs both used the regular restricted rules. In the first profile,
check the configured root count before enabling any runtime proof
work. Bound the joined actor count before preparing any proof view.
The prototype uses at most four roots and 64 joined actors for
these two checks. The pair verifier accepts at most eight joined
actors, 512 saved record references, 64 explicit demand rows, 64 predicate
seeds and 64 identities in each report view. It rejects other seed
kinds and nonempty demand masks in this first profile. Use the
reserved field-word count for the exact key comparisons. These are
work bounds on the proof. All out-of-scope cases continue with
native analysis.

Keep one previous forward snapshot and the intervening backward
witness. Hold only bounded demand and seed keys and the report
identities in that snapshot. Use the following checks for retained
state instead of copying it into the witness.

| Native state | Equality check |
| --- | --- |
| Saved records | Compare the current ordered record references to the last sealed order during index construction. Increase the generation on any change, invalid or incomplete comparison. The old order refers only to records already retained before this rebuild. The previous forward witness holds the generation alone. |
| Rule contributors | Increase a generation when the existing publish operation changes the persistent contributor root. Keep that generation in the forward snapshot. |
| Retained NORMAL Targets and reports | Compare counts from the sealed ordered rows. The native seal inserts all previous rows first and adds only new keys. An unchanged count proves the ordered prefix is the whole view. |
| Latest reached | Compare bounded identity sets and check all the identities have retained root receipts. |

Reject comparisons that exceed the reserved key or primitive word
count. A generation must never wrap. A missing or replaced key can
invalidate the snapshot immediately. Additional work includes the
generation construction, bounded state capture and final comparison,
both successful and failed. All witness state belongs to one scan.
Release it when that scan stops, fails or leaves the bound.
[Ordered seal proofs](lean/proposals/termination-rollback-20261118/RecordIndexSeal.lean)

For a deterministic witness, induction over the run actions gives
the same successor at each higher limit. Induction over future
backward/forward pairs then repeats exactly `S -> B -> S`.
Every future report already has its retained root receipt. The
current native frontier test would continue. The candidate stops
using this proof with no hard iteration cutoff.
[Closed run-pair proof](lean/proposals/termination-rollback-20261118/ClosedRunPair.lean)

### 7.2 R37/R38 — Retire a fully served acyclic root Target

**Affected stages** are forward handoff, next-run ZERO/source guidance
and stopping. A root DT is anonymous. Its proof unit is the full set of
terminal origins and other uses of the typed row. A witness includes
observer identity, rule occurrence/cube, marking action, full mark
and bound carrier.

```text
checkRoot(row):
    require row == root ZERO→DT after a complete restricted forward run
    U = complete acyclic use graph for the control row
    if U is Unknown or exceeds its work budget: return live
    for (action, mark, binding, observer) in possibleOrigins(U):
        if committedNormalTrack(action, mark, binding, observer): continue
        if noPathInCompleteAcyclicGraph(U, action, mark, binding, observer): continue
        return live
    if another ZERO, DATA or seed use lacks independent service: return live
    return discharged
```

Enumerate candidate actions and bindings before restricting to reachable
ones, so the NoRoute test also accounts for origins beyond the current
field cut. Build the use graph by following directed ports, native
bindings and compiled actions from the row's entry, publication and
permission use sites. Include every resolved branch, observer and marking
action, including sites with no current permission. Track full AND
operands at joined transfers. A copy segment uses §7.1's paired prefix
rule. A graph edge for a rule is applicable only for the rule's complete
condition and binding, or represents an explicitly overapproximated
possible use. Overapproximation can conservatively keep a row live.
An unsupported port, guard, alias effect, call or cyclic dependency
returns Unknown. This acyclic check uses no recursive language solver.
Loop and recursion handling, including R39/R40, remains postponed.

For a NORMAL witness trace, check the same coordinates at each step.
Use a saved application or an admitted NORMAL row produced under the scope's
validated C2/C5 policy, with the complete condition of any rule. Port and action
identity, marks, masks and H are part of the witness. Read the committed
root report. For NoRoute, require the complete may-use graph and an empty
search for the exact origin. If the search reaches its cap, keep the row.
Every other use of the affected root row must be covered by an independent
retained row, saved-first replay or the complete origin proof. Keep native
NT and DT propagation. Attach no receipt bits or path evidence to
individual facts. Use the decision in the current seal and release
its temporary proof data with the handoff scratch.

**Proof.** Each affected origin has a corresponding path in the complete
may-use graph, by induction over its directed operations. A NoRoute
certificate rules out that path. A committed NORMAL witness serves the
same origin and retains its existing report. Check every independent
ZERO or seed use before deletion. Thus every affected use has a provider
available without the deleted row, or is outside all feasible paths.
With no live origins, the root row can disappear and the native
empty-frontier test can stop the driver. An iteration limit plays no
part in the proof.
[Origin proof](lean/proposals/mark-origin-soundness-20261117/OriginService.lean) ·
[Terminal traces](lean/proposals/termination-catalogue-verification-20261117/README.md)

| Frozen state | Current | Proposed |
| --- | --- | --- |
| `ZERO→DT,D`, committed `s1/T→o1` via `ZERO→NT(id1),N`; feasible `s2/T→o2` has no NORMAL witness | Retain DT | Retain DT. The first witness serves only its own origin. |
| Both origin tracks committed and all other uses supplied | Retain DT | Retire DT. Keep both NORMAL reports. |
| `p.$/T→ret.h.$/U,N` serves the observer; `ret.k.$/V,N` goes to another result | A coarse reply can renew `ZERO→DT,D` | Keep the replies. Retire DT only after checking the k/V route and the other uses. C5 cannot publish a raw k/V result against an h/U-only selector. |

### 7.3 R42 — Uniform service for the same bound origin

**Affected stages** are reply admission and DATA handoff. The protected
global-cut case needs this rule. A single caller input can yield a
definite uniform reply and a cut descendant on DEMAND. The latter
opens a new coarse query even though the definite reply can serve the
same bound transfer. R42 also covers the neutral ordinary cut case.

Use a definite NORMAL MUST provider in the same complete admission and
application lane. Require the same full mark or the same FLOW mx,
literal H, owner, original, ports, call binding and scope. At an outer
boundary check the native application on the original actual. At a
call site compare already bound output facts. Preserve the native
layer of each delivered result. The original must be a definite,
already served uniform query where owner-side replacement is used.
A submitted STAR, MAY, NE or DEMAND initial cannot prove definite
uniform service.

```text
uniformReplacement(candidate, providers, nextUses):
    require candidate is a concrete/diagonal-FLOW MAY or NE result on DEMAND
    provider = lookupDefiniteMustProvider(candidate.fullLane)
    require provider stays NORMAL after native binding
    require its unexcluded uniform cone contains candidate's whole region
    for use in complete nextUses of this candidate:
        require native replay or a covered admitted C2/C5 command for use
        require paired exit service after the use's cap, including H and layer
        require all rule, Target and seed uses served or discharged by §7.2
    return provider and the covered use keys
```

At a completed handoff, apply the certificate to paired DATA guides.
Live folding is a separate variant under §8.3. For a complete reply
packet in that variant, use the certificate **before its next C2 offer**, so an obsolete descendant cannot enqueue work first.
Use the existing complete packet only. Incremental or incomplete
reply streams may contain a still-open obligation. Deliver them
through ordinary R16/R19 unless the exact certificate was already
frozen and the provider is independently present. Do not hold the
caller queue open to build a whole closure. A failed or missing
certificate falls back to keeping both layers. Keep admitted records
and the independent NORMAL provider. Store no alternative raw result
to make this lookup succeed.

Use existing provider keys for the complete lane and prefix. An
extra index needs an independently measured implementation design. The coverage test
compares one concrete chain and its first-field E, including a
same-head exclusion comparison when needed. The use check is subject
to the same bounded certificate quota as R41. Its proof can reuse the
one scope-local finite continuation as an independent checker.
A root DT with a still-active origin cannot be discharged by fact
geometry. A broader provider that admits different next initials
needs a constructive paired replay witness for the unmatched commands.

| Bound inputs | Current | Proposed |
| --- | --- | --- |
| Definite same-mark `x.f.MUST/T,N,H=1`, and `x.f.g.NE/T,D,H=1` after the cut, in the same original and call | Both actuals can start the next C2 family. | Use the MUST alone when complete native application and paired service for the descendant is already covered. |
| Same heads but the MUST excludes g, or H differs | Both are eligible. | Keep both. The provider cannot cover that lane. |
| Provider has the same value region, but its native reply misses a paired exit or a live seed | Both are eligible. | Keep the candidate until that use is independently covered. |

**Proof.** Uniform taint witnesses every concrete point beyond its
head except the excluded first-field regions. A prefix inclusion with
the right E therefore gives a point witness for every member of the
candidate. Equal mark, mx and H preserve the lane. This step alone
proves neither admission nor caller behavior. The complete-use
check supplies the executable replacement, with both directions'
typed controls and each consumer's cap. Each independent provider
survives the omission. Substitution in a finite derivation preserves
the same bound observation. An earlier ordinary delivery of the
descendant may already have scheduled work. Restrict pre-C2 folding
to complete packets or an applicable frozen certificate, and test
membership and delivery order separately.
[Marked global-cut proof](lean/proposals/same-lane-uniform-termination-20261114/README.md) ·
[Uniform actual coverage](lean/proposals/normal-must-actual-coverage-20261116/README.md)

## 8. Work bounds and release gates

The [isolated prototype measurements](../docs/reports/bidirectional-demand-refinement-rule-prototypes-20261118.md)
record native termination tests and project comparisons for these candidates.

### 8.1 Replace current work before enabling new work

Test equivalent work removal with native fact generation, admission,
publication and scheduling first. Evaluate R41, acyclic R37/R38 and
handoff R42 as independent changes. Their proof checks operate on the
completed handoff. The selected transfer changes R13, R26, R35 and R36
require their own checks before joining that build. The other transfer
and admission rules in §§1–6 and live R42 reply folding also need
separate evidence of no regression.
Compile or select the native path before entering the run for variants
that use it. They incur no alternate plan, qualification table or
candidate lookup per offer or publication.

Use these substitutions at existing integration points.

| Stage | Native work to remove | Conditions and resource bounds |
| --- | --- | --- |
| Exact handoff compaction | Skip order-key construction, C2/C5 witness indexes and proof attempts for a group containing a single native origin. | The existing group key includes exact entry owner and port. Reuse the projected origin and rows. Every native proof excludes the origin itself, so there is no alternative provider in this group. The same origin is kept with no certificate. For multi-origin groups retain the native ordering and provider checks. |
| C5 | Within an indexed candidate stream, evaluate an equal complete entry test once and an equal paired exit test and cap once. | Reuse the existing plan or index. Include raw EXACT/STAR, companion and guard lanes, direction, scope, port, original member, selectors and cap in test identity. Reuse a contiguous group the producer can identify in the existing traversal or group at the existing plan build step in place of its scalar entries. Preserve every pair association. Singleton or already-unique streams use the native plan. No parallel scalar index, full-view preparation pass or extra C5 application on publication. |
| Current application | Share the payload and apply once where multiple authorized postings yield exactly the same application. | Group as part of existing posting construction or admission. Compare recipient, ports, original, premise arm, actual operand, effect, layer, E, mx and H. Preserve the full ND join and every distinct authorization. A later posting must still deliver if it authorizes a new operand. Preserve observable effects and order where observable. Use the ordinary path for native one-posting or first-seen keys. No cross-offer result history or second payload store. |
| Run-2 static and loop boundaries | Preserve existing fast paths in the first implementation. | Reuse static early completion and label indexes, exact carry admission, loop scratch and native plans. Do not build another worklist, enumerate virtual static pairs or traverse the static closure to find certificate candidates. Keep run-1 production and the H1 format native. |

**Loop observation candidates for the R13 workload.** Reuse the
existing `skipEmptyDataReplay` guards for same-direction DATA with a
non-ZERO original and record premise, matching fact kinds and no
MUST premise. At the method boundary, skip the read-only replay if
the record output base is private or absent from the prepared C5
output programs. Application preserves the original premise and the
output base. The exit metadata for that original permits only
unchanged data or subtraction. Neither preparation nor the replay
can produce an observable output on a rejected base. Actual
deliveries and Target observation use their native calls.

Within the same read-only C5 query, a one-program nonstatic FLOW
plan may reuse the result of a field cut. Require a selector head
strictly before the cap and every raw leaf strictly after the
same counted prefix at the cap. The measured profile uses caps
from 1 to 16. Verify that the next fields at
the cut are counted. The deeper-output selector reads only its
head and first remaining field, which are both in that prefix.
The cap erases the other fields and E, and promotes to MAY on
DEMAND. Use the complete original, prefix and mx as the key within
the prepared plan. Keep one result in that plan's owner quantum.
Compare the trie against the cached prefix before allocating a key
for a new result. Use the ordinary paired C5 procedure for other
inputs. Count the work removed by each shortcut and check the
combined R13 path on the configured projects before adoption.
The shortcuts add no field-budget exception.
[Constructive observation checks](lean/proposals/termination-rollback-20261118/UsefulRuleCosts.lean)

**Independent trie-traversal candidate.** Compare the complete node header before creating
comparison scratch. When both headers match and there is one child,
continue with that child pair. A terminal or identical subtree can
finish directly. Start the existing memoized traversal at the first
branch. For a childless postorder walk, call the native operation
once with an empty memo. In graft, a childless node either supplies
the replacement root or produces no result. It needs no child arrays.
Both paths keep the same node, leaf and accessor tests. They preserve
the value of the trie and the order of visits on a branch. Keep this
candidate outside the selected profile. In the OWASP trial it reduced
run-9 engine time and increased measured end-to-end cost.
[Traversal proof](lean/proposals/termination-rollback-20261118/TrieScratch.lean)

**Bounded-cut fast path.** At the existing global or relative
field-limit operation, use the stored counted depth of the fact trie.
If the whole packet fits, deliver it once when it is REACH, FLOW or
TAINT with no protection or whole protection. Whole protection uses
the packet root as the mask. Check the positive limit and cancellation
as usual. The native operation would cut neither the ordinary facts
nor the protected facts. For whole protection it would split and
reattach the same protected coordinates. The result has the same base,
layer, head, exclusion, marks and protection. No audit failure or
mark request occurs. Use the ordinary operation for an over-limit
packet or a TAINT packet with a separate mask.
[Bounded-cut proof](lean/proposals/termination-rollback-20261118/BoundedFactLimit.lean)

**Independent whole-protection replay candidate.** In FULL, verify
that an ordinary micro-edge's TAINT input or a summary's TAINT
conclusion is canonical and uses its own root as the mask. For these
operations the private protection pass uses the same geometry, marks,
exclusions and layers as the ordinary pass. The raw micro-edge ignores
protection in its transfer. Summary selection and grafting use the same
ordinary coordinates when caller protection is stripped. In either
case the private pass would supply protection for every ordinary
TAINT output coordinate. Execute the ordinary pass once and attach
each result's own root as its mask. Keep ordinary requests in their
callback order. The private pass publishes no requests. Use the
ordinary path for partial or noncanonical masks and other transfers.
Keep this candidate outside the selected profile. The ThingsBoard
trial did not establish time parity.
[Whole-protection proof](lean/proposals/termination-rollback-20261118/WholeProtection.lean)

| Operation input | Current work | Candidate work |
| --- | --- | --- |
| Saved `x.*/F→tmp.*/F,N`, actual `x.f.$/T,N`; `tmp` is private at the method exit | Apply the relation to obtain `tmp.f.$/T,N`. Discard it at the public-base test. | Return no enclosing DATA observation for this saved relation without applying it. |
| One paired output selector `ret.f.M/T`, cap 2; successive FLOW outputs `ret.f.g.h.*/F` and `ret.f.g.k.*/F` with the same mx and original | Select and cut each output to `ret.f.g.M/F,D`. | Compute the same result for the first cut. Reuse it on the second query within the prepared plan. |
| Two independently built tries for `x.f.$/T` with the same leaf | Allocate a pair stack and identity maps for structural comparison. | Compare the headers and the sole child. Return the same equality result without allocating traversal scratch. |
| Graft a replacement `ret.g.$/T` at a childless FLOW node | Walk the root using an identity memo and build empty child arrays. | Test the root once and return the same `ret.g.$/T` subtree. |
| Fully protected `{x.$/T, x.f.MUST/U},N` at limit 1 | Run the bounded check on both the ordinary and protected tries and reattach the mask. Emit the original memberships. | The stored depth fits. Emit the same packet once without rebuilding the protection mask. |
| Actual `p.$/T,N`; summary `p.$/T → {ret.f.$/U, ret.g.MUST/V},N`, with whole conclusion protection | Apply twice and recover the mask `{ret.f.$/U, ret.g.MUST/V}` for the ordinary results. | Apply once. Both emitted memberships have whole-result protection. |

For C5, equal entry tests admit the same raw original members. Equal exit
tests select the same leaves at the same cap. Taking their union once gives
the same publication set. For e distinct entry tests and s eligible
(entry, exit, cap) tests in the existing plan, do at most e tests per
original member and s tests per leaf. This count excludes the existing
index traversal. Key construction, grouping and scratch count as work
for acceptance. Sharing applies to replies only when repeated application
would have the same externally visible result and no independent effect.
A change in delivery timing, log or diagnostic count alone does not
establish that effect equality.

### 8.2 Spend only work already saved on certificates

A repeated row is evidence to investigate in a trace. In production,
discover candidates in the existing projected-row walk using the row
shape and retained provider index. A failed match on the propagation
path schedules no proof work. Keep the existing frontier lifetime.
At the seal, a check can use a complete derivation already available in
native state. Any new validation, prefix extraction or enumeration,
including a failed check, needs a reservation **before** it begins.

Maintain a short-lived work allowance for the completed handoff. It
starts at zero. Increase it only for audited native work already replaced
in that handoff, for example the singleton-compaction shortcut. For
each counted class, use a conservative lower bound on the units saved
after paying for the replacement, candidate identification, reservation
and accounting. Count the same units on the two paths, including item
visits, index operations and field/key words processed. An operation
without a comparable accounted bound supplies no allowance. In
particular, a potential later C2 offer or a future run that might
disappear supplies no allowance. Never pool allowances across scans
or infer any from a benchmark average.

```text
for eligible origin encountered by the existing handoff walk:
    recipe = boundedRecipeFromCurrentNativeEvidence(origin)
    if no recipe: keep origin
    else if allowance covers its full work bound and existing scratch fits:
        reserve the full bound in each counted class
        result = check within the reserved work and scratch
        if complete independent replacement of every pair: omit origin
        else: keep origin
    else: keep origin
```

The initial cheap recipe check itself must fit in the replacement's
accounted work. A handoff with no audited savings never enters the
optional proof path. Charge all work in the recipe, including provider
lookup, temporary keys, comparisons, an unsuccessful verification and
row installation. Consume the reservation even on failure. Give each
candidate at most one attempt in a handoff. Retry in a later handoff
only if a changed native provider or binding can be identified from
existing state and a new reservation is available. A missing proof or
limit gives Unknown. Reuse space relinquished in the same handoff for
temporary proof data, stay within its existing scratch footprint and
release it before publication. A new persistent proof or failed-attempt
cache needs its own resource design and acceptance evidence.
When several pairs of the same owner need the same prefix relation or
use slice, verify that prerequisite once per frozen basis in the
reserved scratch. Charge its construction once and charge each pair's
own port, cap and continuation checks. Release the slice at the end
of the handoff. For R41, the geometry key includes the owner and the
exact set of basis input bases from the paired rows. Cache a complete
geometry result or a completed structural rejection within the seal.
The prototype retains only the last geometry. It allocates no proof
cache for a handoff which cannot use the selected certificate.
Cancellation and a work limit supply no cache value. A geometry hit
still requires current replay and continuation checks for that origin.

For each clipped copy, borrow the existing saved-record indexes.
The direct witness premise must prefix the broad entry head. Visit
only that prefix chain. The input shift determines a unique output
leaf. Compare the shift with the output suffix and read that one
leaf from the FLOW trie. The opposite witness premise comes from a
saved output position. Visit only positions that prefix the clipped
input head, then use the existing reversal on the selected position.
Stop each lookup at its first valid witness. The existing indexes
supply the same candidate set that can satisfy the old alignment check.
Transfer a copy set to an empty, sole successor in the acyclic proof
graph. At a fork, give each successor its own set. At a join, merge into
the successor's set. Retain the exit set until it is returned. A moved
set can be reused because the source has already finished its last
read. The copies and paired clips are the same as with a fresh set at
each successor.

An additional native saving is available in exact-service compaction.
Keep a singleton group without building either index. For other
groups, build the C2 provider index first. If no key has two distinct origins,
each proposed removal fails its first C2 requirement. Return the
original sorted group without building the C5 index or trying deletions.
If a key has two origins, run the existing check. Two leaves of one
origin never establish that test. The shortcut preserves both the
selected origins and their order. Materialize the native string order
key only when the comparator needs to break an exit-port and protection
tie. Compute the key from the original premise and output packet.
Projected guidance can erase annotations that distinguish order keys.
A singleton has no comparison and needs no string key. The deferred
comparison returns exactly the previous result on every tie.
The deferred keys borrow the packets from the completed run during
this handoff. Release the origins and any materialized keys when
the rows are installed. Count the C5 index work saved on unique
groups. Charge detection of shared C2 keys, the second row walk on
shared groups and any added live scratch before crediting savings.
[Constructive compaction and cache checks](lean/proposals/termination-rollback-20261118/UsefulRuleCosts.lean)

**Publish saved-record indexes once per seal.** After the workers join,
merge the public NORMAL rows and then the scoped NORMAL rows. Rebuild
the public and scoped entry and exit indexes together. The driver
currently rebuilds all four indexes after each merge. No query reads
the intermediate indexes. Keep the native individual persist operations
for callers that publish only one partition.

The joined rebuild can also serve scans outside the certificate scope.
In that mode merge the two partitions and build the native indexes
once, with no record-order snapshot or proof accounting. Measure this
path separately because it changes handoff allocation even when the
terminating proof is ineligible.

The merge keys separate public and scoped rows. The two merges read and
write the same authoritative relations in the same order. Index
construction reads those relations without modifying them. The final
rebuild sees the same ordered input and output positions, ports, record
directions and retained keys. Reuse the prior sealed record for each
surviving key. A newly introduced key had no visible record before the
seal. If either merge fails, the driver abandons the seal and starts no
new run. The report commit still requires a complete seal.

The omitted rebuild would have visited every current public record and
every previously committed scoped record. It would have inserted each
entry and each indexed output position in that intermediate population.
Use those actual counts as a starting point for the same-seal allowance.
Charge the cost of recording and using the counts. Count field and key
work separately if the verifier needs that allowance. A newly indexed
scoped record in the current seal earns no credit for the omitted pass.
[Sealed index proof](lean/proposals/termination-rollback-20261118/RecordIndexSeal.lean)

**Candidate for one-time proof work.** Some small scopes have too few
saved positions in one seal to pay for a complete observer closure.
A scan can instead keep only the unused work counts from earlier
completed seals of that same scan. Credit each actual removal once
and reserve the complete verifier bound before starting it. Failed
verification consumes the reservation. A reserved walk can return
Unknown when it exhausts its bound. No credit comes from a future
run or from earlier scans. The memory and scratch bounds still
apply at the current seal. Retain no earlier edge solely to keep
work credit.

At every completed prefix of the scan, the sum of reservations is
at most the sum of actual credited work, by induction on credit
and reservation operations. This is an aggregate work bound.
A handoff can spend work saved by an earlier one. Evaluate timing
and memory per iteration with the actual reservations enabled
before selecting this accounting policy.
[Reservation invariant](lean/proposals/termination-rollback-20261118/RecordIndexSeal.lean)

In the selected OWASP case, the run-7 ablation bypassed
the general proof. A local R41 retirement certificate, or a complete
run-level witness from §7.1, must fit the verified savings at an
eligible seal to pass the run-11-or-earlier acceptance check. A
run-level witness changes the stopping policy and needs its own
proof and project comparison. Keep the local retirement check
when work for other observations must continue.

Alignment of concrete suffixes alone is insufficient for native
continuations. In run-5 a consumer with `p.*/F` demand admits
`p.M/T,D` as `p.$/F`. It rejects `p.f.$/T,N` under that same demand.
Both offers cover the concrete point `p.f`. Therefore a saved result
that gives the latter offer needs a separate admission or replay proof
at this consumer. The geometry result authorizes neither removal of
source permission nor pruning of this coarse-only admission route.

If B is baseline work in one counted class, S is the audited net work
already saved, and A is the sum of reservations, the handoff performs
at most `B−S+A ≤ B` in that class. The identity requires upper bounds
that cover allocation and lookup work as well as the successful proof.
Apply the bound separately to each counted class. Peak live memory
uses the separate scratch constraint. Wall time can still vary with
allocation behavior and locality. A successful retirement can also
change subsequent frontiers. Both effects require project-level measurement.
[Constructive allowance checks](lean/proposals/termination-rollback-20261118/HandoffBudget.lean)

| Example at this seal | Result |
| --- | --- |
| Every candidate has a unique native key, and no work has been saved. | Use the native operations and install the native frontier without a certificate attempt. |
| Singleton groups saved two counted steps after accounting, and a candidate's complete check reserves two. The check finds an open use. | Keep the native origin. A second check cannot spend those two steps. |
| Two projected pairs belong to one origin. The first is covered and verification of the second reaches its bound. | Keep the full origin. There is no pending work or partial removal to carry into the next run. |

### 8.3 Keep workload expansions independent

| Candidate | How it can increase work | Constraint before adoption |
| --- | --- | --- |
| NE and changed C2 images (R01–R08, R20–R23) | Distinct M and NE can hold more keys at one head. Point and suffix branches can start two queries. Mask changes split otherwise equal commands. R08 can explore more body edges even when it replaces one command with one command. | Compare one rule family at a time against the native pipeline. Account for logical memberships, total visited body edges, C2/paired C5 work and caller resumes. Retain native scope outside the selected boundary. Stay within K and document every relative-cap exception. |
| Prepared children and possible matching (R06, R09–R12, R34) | A child or an extra saved replay reply can create a caller binding, cascade into work and renew an extra frontier. Reusing its payload still leaves the binding cost. | Require a concrete regression case and a design that replaces a proven redundant producer or replay for the same service. Keep native matching on the first release path. No additional child scan or possible-authorization publication until this gate passes. |
| R32 and changed cleaner or queue behavior | A different support layer can change the retained closure, queue order, concrete requests, and the number of paired outputs. R36 can emit one surviving region per field of a selected cleaner chain. | Assess each independently, across the whole analyzed binding and downstream callers. Maintain native static carry and loop behavior. A smaller initial count alone cannot pay for extra outputs, body propagation or retries. |
| Live R42 | A whole-packet proof or extra thread-local state can slow every call. A one-off omitted reply may shift work to another continuation. | Use evidence already available at delivery. Require effect equality and savings in the existing delivery step. Keep live folding out of the initial handoff implementation. |

Work estimates based solely on query counts, apparent set inclusion or
the width of a summary do not justify turning these candidates on.
A blocked candidate remains at the native operation while its isolated
case is investigated. The policy selects work from native state. The
benchmark fixtures exercise those same selection rules.

### 8.4 A separate acceptance decision for every project

- **Reachability and convergence.** Compare marking-action/full-mark/observer
  tracks, source permissions, and exact confirmed rule/location identities.
  Preserve negative controls, including the removed point of an EXACT
  cleaner. Require natural convergence for any ordinary termination case
  claimed by the change. For the selected OWASP entry compare to the
  run-101 baseline and reproduce the run-11-or-earlier natural stop of
  the helper-only ablation with both findings. Keep LOOP/REC as parity
  controls. A run-limit cutoff is a diagnostic outcome.
- **Comparison.** Use repeated interleaved native and candidate scans at
  `0438facd2a09e44a386b829cb2f1f4fe3d3954a8` for **each** of OWASP,
  Conductor, Stirling-PDF and ThingsBoard. Pin the model, rule set, FULL
  mode, entry set, heap, timeout, field schedule, instrumentation and
  production run limit. Time from cold setup, including any index or
  certificate preparation. Also compare engine and handoff at common
  completed checkpoints and peak live heap at the same resource budget.
  Record reached, completed and accepted runs with stop reasons as well
  as starts, caller memberships, deliveries, C5 work and proof work.
  An earlier stop preserves progress when it keeps the required
  observations and proves that the remaining guidance cannot change them.
- **Pass rule.** A project passes only with preserved observations and
  progress, and equal or better end-to-end time and peak memory within
  the resolution of the matched measurements. A reproducible increase
  on one project fails the variant regardless of savings elsewhere.
  Inconclusive results require more matched evidence or a revised
  design. For a native memory guard or timeout, compare progress and
  resources at the original configured budget. Record the latest common
  checkpoint and the accepted locations. If no run completes, compare
  CPU and wall time at common in-run progress samples as well as at
  the guard. Event counts can hide different body work, so use them
  with the operation counters and allocation samples. A missing
  measurement leaves the comparison open.
- **Release.** Require all four individual passes and at least one
  demonstrated strict improvement in the combined build. Require the
  four no-regression checks both for each change independently and for
  the combined build. Assess projects separately at the same workload
  and iteration limits. Preserve the native path for any
  variant that has yet to pass.

Compare peak process RSS and the Java heap measured at the same
iteration boundaries. A post-pause heap measurement characterizes
retained Java data. The process high-water mark also includes short
native-memory spikes and report generation. Use the same resource
sampling in both arms when a spike changes the acceptance decision.

The structural checks bound the operations they count and preserve the
specified service. Passing the per-project comparison establishes the
resource result for those inputs and resource budgets.
[Matched project baselines and attribution](../docs/reports/bidirectional-demand-refinement-performance-20261118.md#comparison-with-the-previous-bidirectional-core)

---

[Batching and retirement checks](lean/proposals/termination-rollback-20261118/Handoff.lean) ·
[Local rule proofs](lean/proposals/demand-refinement-spec-20261117/README.md) ·
[Joint service proof](lean/proposals/demand-no-loss-audit-20261117/README.md) ·
[Scalar, continuation and handoff checks](lean/proposals/demand-spec-clarification-20261118/README.md) ·
[Termination examples](../docs/reports/bidirectional-demand-termination-counterexamples-20261115.md) ·
[Validation](../docs/reports/bidirectional-termination-fix-validation-20261117.md)
