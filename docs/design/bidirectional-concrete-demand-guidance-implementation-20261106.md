# Concrete demand and protected memberships: implementation draft

Status: **selected storage laws implemented and locally checked; acceptance open**.
Keep STAR and repair demand guidance. Protected memberships cannot be
subsumed, and a pass cannot introduce protection. This document specifies
those laws and the current storage implementation. Section 5 records its bounded
native checks; program recovery and new project acceptance remain open.

The selected behavior is also stated in the
[storage specification](../../spec/concrete-demand-guidance-retention.md).

The audited control is `6e0178c25`, with the production storage bytes of
`4182adae6`. The pass-assignment guard is implemented and tested separately.
The wider acceptance gates below remain open. Runtime
concrete IDs include experimental GROUP atoms; no per-mark FULL/GROUP filter
is added. FULL remains the required project acceptance mode. The finite C2
examples are FULL-only; existing GROUP issues remain outside their claim.

The [current report](../reports/bidirectional-demand-guidance-retention-performance-20261106.md)
contains the actual point transaction and portable control data. Shared-loop
naturally finishes run-5 with zero findings; its expected-one assertion fails.
The trace proves a producer loss, not a final Conductor finding cause.

## 1. Selected behavior and unchanged behavior

| Part | Current storage/control behavior | Required behavior |
| --- | --- | --- |
| Concrete MAY/T DEMAND child | Ancestor MAY/T can reject it | Keep the explicit child coordinate |
| Parent after child; one root+child packet | Normalization can remove the child | Keep both explicit MAY positions |
| Protected position, any tail/layer | Prefix, MAY/EXACT or E coverage can remove/rewrite it | Keep its exact typed coordinate |
| Protected ancestor and child | Compaction can retain only the ancestor | Keep both supplied protected coordinates |
| Protected MUST/STAR E headers | Joins/fills can relocate flags | Keep each supplied protected E header |
| Exact protected duplicate | Same ordinary membership may already exist | Merge; flag wins; new flag is fresh |
| Plain pass output | Broad action classification could enable assignment protection | Transport input protection; create no new protection |
| Unprotected EXACT/MUST/STAR/NORMAL | Existing DATA normalization | Keep that DATA policy |
| Scalar C2/C5 and layers | Existing emitter, image and application rules | Unchanged |

The two storage laws are distinct. Concrete MAY guide retention applies to
`TaintTree(layer=DEMAND, anyTail=ANY)` leaf.any memberships. Protected retention
applies to every protected concrete membership, across NORMAL/DEMAND and
EXACT/ANY/MUST/STAR. It includes protected EXACT even inside a MAY packet.

Keep field transfer, mark identity, mark requests, source/sink rules, Target
support, growth, physical ports, stopping, ownership and work scheduling.
Keep Facts/Initial equality, hashing and group keys. Add no role flag, plain
origin metadata, history store, global cache, grounding support or new manager.
The selected pass guard is a protection-assignment change, not a field rewrite.

Keep typed FLOW replacement for unprotected concrete rows. Compatible FLOW
can still replace such a row; do not revive legally replaced publications.
Protected rows remain exempt. NORMAL FLOW/ANY is invalid by constructor.

## 2. Actual small-program loss and unchanged C2

The complete trace has 173 contiguous events, nine complete point transactions
and 12 whole snapshots, with zero drops/errors:

```text
Backward run-2 mapper:
  original ret.Element.[any]/FLOW
  conclusion arg0.{root,f,g}.[any]/FLOW DEMAND

Actual application and binding:
  arg0.f.[any]/FLOW D -> arg0.f.[any]/T D -> s.f.[any]/T D

Point transaction 11, scope (3,-2), point 5, full original ZERO:
  before: s.[any]/T D
  offer:  s.f.[any]/T D
  after:  identical whole bucket; freshCount=0

Forward run-3 handoff:
  AL scope (3,7), paired exit -2: s.[any]/T -> ZERO
```

The call adapter preserves the child. `TaintGroup.addAll` rejects it in
`subtractSubsumed`, before warm canonicalization; g is rejected earlier by
the same path. These captured facts have Empty E and no protection. No demand
or source permission was injected into the fixture.

| Guide | Actual input | Existing native C2 result |
| --- | --- | --- |
| s.[any]/T | s.f.g.$/T NORMAL | s.f.*/T DEMAND |
| s.[any]/T | s.f.[any]/T DEMAND | s.f.*/T DEMAND |
| s.f.[any]/T | s.f.g.$/T NORMAL | s.f.g.$/T NORMAL |
| s.f.[any]/T | s.f.[any]/T DEMAND | s.f.[any]/T DEMAND |

The child guide distinguishes raw from cut. Equal DATA coverage therefore
does not justify deleting that guide. Full-program recovery remains required.

## 3. Exact storage and protection contract

Fix method/context, complete original P, direction, method/block scope,
entry, actual exit, base and layer. Never join across those labels.

```text
May(X) = supplied (path, full mark) from TAINT/DEMAND/ANY leaf.any
H(X)   = supplied protected (path, full mark, effective tail, effective E)

EXACT: effective tail EXACT, Empty E; ignore its mixed wrapper tail/E.
ANY:   effective tail ANY, Empty E by constructor.
MUST:  effective tail ANY_TAINT, retain the full supplied E.
STAR:  effective tail STAR, retain the full supplied E.
```

For residual rows admitted by the unchanged relation law:

```text
May(after) = May(before) union May(offer)
H(after)   = H(before) union H(offer)
newMay = May(offer) - May(before)
newH   = H(offer) - H(before)
fresh payload includes newMay union carriers(newH)
fresh flags include newH
```

H is included at exact coordinates in payload. Neither ordinary nor protected
ancestor coverage, E subset, E intersection or hole filling may replace an H
coordinate. Different typed H coordinates remain distinct. Exact duplicates
merge and the flag wins. A pass/storage operation may not infer a new H.

This is a storage rule, not immortality across field operations or owner/run
lifetime boundaries. Existing transfer/reversal/run-1 operations keep their
rules; normalization preserves their already-produced protected outputs.
Facts.equals omits protection. Change detection and cache keys must include
masks where required; no equality/hash change is proposed.

## 4. Incremental DATA admission plus literal protection

Use the existing incremental DATA order. Do not turn current packets into a
new global normal form by re-admitting them from empty:

```text
erase(S) = current payload packets with protection annotations removed
H(S)     = exact typed union of S's protected coordinates
A(S,t)   = old DATA admission from that restored current state and new offer

(dataAfter, legacyDataDelta) = A(restoreCurrent(erase(S)), erase(t))
U(S,t) = embedRawProtection(dataAfter, sources=S + t)
H(U(S,t)) = H(S) union H(t)
```

Erase keeps the complete payload, including protected payload, and its
current header order. `restoreCurrent` restores without admission. Only the
new offer enters the old no-H admission path. That retains `addInto` STAR/T4,
the ordinary regional kernel, and the selected MAY-coordinate behavior.
The wrapper runs when current or offered H is present; no-H admission keeps
its existing direct path. No K/T view, origin metadata or history is added.

H is saved before destructive normalization. Its ANY/MUST/STAR masks remain
under their supplied tail/E; no protected prefix compaction, E intersection
or hole filling is allowed. `embedRawProtection` unions each raw carrier into
payload before attaching its exact mask. DATA-derived headers do not gain
flags through coverage.

Protected EXACT ignores a mixed wrapper's tail/E. Place it once at the first
matching existing DATA EXACT coordinate. If DATA pruned it, reuse an existing
original cohort where possible, then use a canonical exact-only carrier as
fallback. Do not move every EXACT flag out of its mixed cohort: whole-root
T4 geometry matters. Coalesce effective EXACT duplicates without relocating
protected MUST/STAR E headers.

Keep old DATA E-join carriers as plain. Protected p.MUST/T E={f} plus protected
p.MUST/T E={g} may yield plain p.MUST/T E={}; both original H headers remain.
E={} is not flagged. Forbidding the plain carrier would be another policy.
Independent plain-origin normalization is also unsuitable: flag-wins forgets
that origin at an exact duplicate and can change later E joins by arrival.

There is no assumed global DATA confluence, fold idempotence or absorption
law. For example, add ANY p.g, then STAR p.f, then ANY p. The existing warm
state can retain the old STAR row with ANY first. Re-admitting that current
list from empty drops STAR p.f under ANY p. U preserves the restored-state
incremental contract; H union does not prove all ordinary effects equivalent.

## 5. Current prototype: packet, group and delta paths

The local prototype follows U rather than a batch C operator. Its packet
normalizer computes the ordinary result from full payload and unions the raw
protection mask back unchanged. The inherited EXACT-removal and same-point
`exact - any` rules remain ordinary DATA rules; protected EXACT is restored
separately. For ordinary bits E=EXACT, N=MAY and A=inherited MAY,
`(E-A)-(N-A) = (E-A)-N`; the new MAY bit is N rather than N-A. This Boolean
bridge describes the DATA kernel, not the all-header H rule.

In `TaintGroup.addAll`, current/offered protection selects `addWithProtection`
before the STAR/exact-only shortcut. Its precheck combines ordinary DATA
freshness with literal H freshness. Protected difference is at-coordinate:
EXACT matches across wrappers; ANY/MUST/STAR require identical tail/E. It
uses no prefix subtraction, E-subset test or E-based traversal filter.

```kotlin
// Existing source structure, simplified; owner/layer checks remain.
if (subtractSubsumed(offer, before) == null) return emptyList()
val data = TaintGroup(m, interner)
before.forEach { data.restoreCurrent(it.withoutProtection()) }
val legacyDataDelta = data.addAll(offer.withoutProtection())
val after = m.embedRawProtection(data.all().toList(), before + offer)
// Build deltas below, then commit the complete after state.
```

The temporary has no masks and therefore follows the existing no-H path;
it does not recurse through the protection wrapper. This is an operation-local
calculation with existing storage types and interner, not a new retained store.

`canonicalTaintDataState` is only the existing regional DATA step. It is not
the complete old group/T4 law and must not replace A. STAR equal whole payload
with E={f} and E={g} joins to E={} in `addInto`, outside that regional helper.
Thus protected STAR Ef plus plain STAR Eg retains the legacy plain E={} DATA
carrier and raw protected Ef. Current headers are restored, not re-admitted.

The unannotated warm regional step preserves D/ANY heads, ordinary pruneExact,
exact cohort placement, T4 mixed-content handling and MUST fills. The saved
H stream bypasses its protected canonicalization. Batch helper use is not a
claim of a unique whole-engine DATA normal form.

### Delta contract, including legacy STAR/T4 content

Do not derive ordinary deltas solely by subtracting before from after. The
old admission can replay whole T4 mixed content, including unchanged EXACT
siblings. Preserve `legacyDataDelta` returned by the temporary group:

```text
1. Filter each legacy DATA delta against the complete current after state.
2. Attach only already-current H at matching typed coordinates:
   EXACT ignores wrapper; span flags require identical tail/E.
3. Add literal new H carriers: protectedDifference(after, before),
   minus protected memberships already included in the returned deltas.
4. Coalesce equal packet headers by raw node/mask union only.
   Do not prefix-canonicalize those returned carriers.
```

A prior EXACT flag may replay with legacy whole T4 content. That is an
already-supplied flag at its current effective coordinate. Protected Ef/Eg
must not flag a DATA-derived E={} MUST/STAR carrier. A new H membership is
fresh even when ordinary DATA support already existed. Packet/header checks
must include masks because Facts.equals omits them.

The group commits the complete embedded state after preparing current deltas.
Packed adapters restore current scalar headers and call the same list-returning
path, then stage `replaceAtom`; Section 6 describes that boundary. Repeats,
exact H union/no invention, same-restored-state DATA reference and delta
sufficiency need their stated native/model evidence. Global DATA order
independence is neither required by this wrapper nor proved by its H algebra.

### Current verification and remaining failure

Root reports 19 new native storage tests passing and 3,035 default native
tests passing at this local-prototype checkpoint. These checks do not establish
project quality or the required end-to-end finding. The natural shared-loop
reproducer still completes run-5 with zero reports; its required-report gate
remains unmet.

The [current native report](../reports/bidirectional-concrete-guidance-repair-reproducer-20261106.md)
embeds the actual repaired point transactions and remaining getter boundary.
The latest default command ran 2,573 core tests and reused 462 successful JVM
results. The 3,035 count is not a claim that all results were freshly rerun.

The [later DATA bridge and historical control](../reports/bidirectional-guidance-historical-control-and-data-bridge-20261106.md)
adds five passing restored-state DATA tests. The final default gate has 3,040
clean results: 2,578 fresh core and 462 reused JVM results. The complete 52f
runtime also misses the same small-program observation at run-5. The inherited
failure remains open. The [saved-record capture](../reports/bidirectional-getter-saved-record-gap-20261106.md)
finds no saved getG return relation before run-3: only ZERO and argument
identities. This closes that bypass question, not the first-loss or new-policy
proof for the entire program.

A distinct C2 cell is now under review: same-path ANY/FLOW demand rejects a
supplied NORMAL STAR/FLOW actual under the unchanged emitter. Any change to
that admission policy awaits the user's decision. The storage implementation does
not change C2/C5, field transfer or layers to make that case pass.

## 6. Packed scalar parity

Cold `DiagonalDelta` has one effective tail and uniform protection. Preserve
literal geometry for selected D/ANY guides and for protected packets. Other
unprotected geometry keeps its DATA canonicalization. Keep same-geometry
mask union and differing-geometry/header fallback before mutation.

```kotlin
// For guides or current/offered protection, use the scalar U reference.
val before = currentAtom(scope, mark)
val temporary = TaintGroup(m, interners.taint)
before.values.forEach(temporary::restoreCurrent)
val changes = temporary.addAll(canonicalTaintPacket(f))
val after = temporary.all().associateBy {
    Header(scope.initial, it.base, it.layer, it.anyTail, it.exclusion)
}
replaceAtom(scope, mark, after)
return changes
```

Bypass `addOne` region overlap on these operations. Its old overlap can flag
an offered plain child below an old protected parent, or flag an old plain
parent when a protected child arrives. Decode preserves such invented flags;
it does not correct them. All tails/layers with protection require U or a
proved equivalent fast path, not only D/ANY.

Restore current headers without re-admission. Keep sibling full-mark masks
and staged `replaceAtom`. Its plain/flag split uses exact coordinate
subtraction. Cross-header adapters may need `addAll`, since preserving old
protected headers plus a plain joined header can produce several deltas.
Keep compact's existing protected exemption and FLOW replacement law.

## 7. Pass protection assignment

A pass transports incoming protection through the existing AP operation.
It cannot introduce protection from a concrete identity edge, relabel or
broad action-ID presence. Enforce that contract with a computed property:

```kotlin
val isRuleAssignment: Boolean
    get() {
        val id = actionId
        if (id?.role == ActionRole.PASS_THROUGH ||
            id?.occurrence?.kind == RuleKind.PASS_THROUGH) return false
        return isSource || id != null
    }
```

Use `me.isRuleAssignment` in both EngineAlgebra application paths and in the
unary source transfer that currently passes literal true. Valid SOURCE forms
keep their existing result. Do not rewrite ND handling or invalid SOURCE/pass
hybrids. The typed role OR kind exclusion is intentional.

Actual native pass-builder action IDs remain null. Add no fake pass IDs or
new action registry. There is no evidence that those null-ID native passes
introduced protection through EngineAlgebra; this gate enforces the explicit
contract and is not claimed as the observed shared-loop root cause.

Keep transportProtection and the existing summary-cycle/restored-mark rule.
The pass gate does not remove independently valid summary protection or
change scalar summary matching, output layers or field application.

The pass-only patch has checked evidence:

- [24 constructive policy lemmas](../../spec/lean/proposals/concrete-demand-guidance-retention-20261106/pass-protection-checks.json).
- [Native RED/GREEN and full-suite evidence](../reports/data/bidirectional-pass-protection-validation-20261106.json):
  clean RED has one incorrect-protection failure and five passing controls;
  GREEN passes. All 2,554 dataflow and 462 JVM tests pass, with no skips.
- [Engine tests](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/PassRuleProtectionTest.kt)
  cover both directions, all application modes, EXACT/ANY targets, full/group
  runtime atoms, partial flags, source assignment and summary/record transport.
  JVM tests exercise actual CopyMark/CopyAllMarks forms and retain null IDs.

These results validate the pass guard. They do not validate the proposed
storage repair or establish a new project performance result.

## 8. Consumers, handoff and effect limits

The source audit found 24 canonicalPackets consumer sites. They must receive
the central packet/U behavior without owner-side history. Publication remains an
exact-current filter; it must retain flags present at their typed coordinates
and must not recreate legally removed plain rows. Persistent record signatures
and loop scratch keys already include masks; audit all changed paths.

Handoff keeps full P, method/context, block entry and paired exit. It must
not combine a child from another original or exit. Persistent records still
exclude DEMAND and backward-ZERO normal rows. No demand history is added.
Normal/ND shapes, static completion and complete loop AL/RPT/DATA/Target
families retain their contracts. Local H union is not a full C5 effect proof.

Two limits remain. First, an unprotected EXACT guide and MAY guide can have
different same-head C2 images; unprotected EXACT pruning remains in the DATA path:

```text
same original and paired exit; actual q.[any]/T DEMAND:
  guide q.[any]/T -> q.[any]/T DEMAND
  guide q.$/T     -> q.$/T DEMAND
```

Protected EXACT now survives under the selected H law. That does not prove
preservation of every unprotected guide or its required C5/normal-Target effect.

Second, unchanged typed FLOW replacement can remove an unprotected concrete
row with a different literal C2 image:

```text
one owner/scope/exit; Empty E; no protection:
  I_FLOW=arg0.[any]/FLOW -> ret.[any]/FLOW DEMAND
  I_T=arg0.[any]/T      -> ret.f.[any]/T DEMAND
on ret.f.g.$/T NORMAL:
  root FLOW guide -> ret.f.*/FLOW NORMAL
  child T guide   -> ret.f.g.$/T NORMAL
```

This structural cell does not prove that the retained FLOW route loses the
required final effect. Do not disable replacement to close the proof. The
observed point witness has P=ZERO and cannot use this diagonal replacement.

## 9. Proof and native gates

Follow [proof-guide.md](../../spec/proof-guide.md), with unchanged scalar
RestrictedInitialPolicy as C2 reference. Root's
[58 checked proposal lemmas](../../spec/lean/proposals/concrete-demand-guidance-retention-20261106/checks.json)
cover MAY coordinate algebra, finite unchanged C2 cells, exact port pairing,
the cold Boolean law and finite Empty-E warm examples. Their
[stated scope](../../spec/lean/proposals/concrete-demand-guidance-retention-20261106/README.md)
does not prove this new all-header H operator, pass gate, native adapters,
full spatial canonicalization, FLOW effects or program recovery. The old
39 FLOW lemmas are not concrete-protection proofs either.

For U, prove literal H preservation/no invention, coordinate inclusion,
exact duplicate flag-wins and delta freshness. Compare DATA behavior with
old admission from the same restored current state and incoming offer. Keep
legacy STAR/T4 deltas and current-mask attachment in that adapter proof.
The [35 local incremental protection laws](../../spec/lean/proposals/concrete-demand-guidance-retention-20261106/all-protection-checks.json)
parameterize DATA admission/restore/embedding; they do not prove the native
adapter, full DATA normal form or global order independence. Do not assume
`C(C(X) union Y)=C(X union Y)` to close those native obligations. Repeat/no-op
and required downstream C2/C5/loop effects still need their own evidence.

The separate [50 ordered-embedding laws](../../spec/lean/proposals/concrete-demand-guidance-retention-20261106/ordered-embed-checks.json)
check first DATA/source/fallback placement, literal H, payload carriers and
EXACT allocation count on arbitrary ordered bags. They leave native DAG
operations, deferred-write refinement and full downstream effects explicit.

| Gate | Required evidence |
| --- | --- |
| MAY producer | Cold, both orders, one packet, repeat, full mark and owner/P/ports |
| All-header H | NORMAL/DEMAND; EXACT/ANY/MUST/STAR; ancestor/child; mixed slots; no inferred flag |
| E/header handling | Equal/subset/incomparable E, joins/fills, exact wrapper equivalence, partial masks |
| Pass | Plain input stays plain; input H transports; role OR kind exclusion; null native pass IDs |
| Unchanged rules | Plain EXACT/MUST/STAR/NORMAL; field output; summary-cycle protection; C2/C5/image/layers |
| Backends | Scalar/packed/cold/fallback, shared T/U geometry, cross-header list deltas |
| Consumers | Publication, persistence/reversal, exact paired handoff and complete loop signatures |
| Required effect | Existing FLOW replacement qualification and open C5/Target effect proof |
| End-to-end | Shared-loop one NORMAL report after natural convergence; both prefix regressions remain passing |
| Project quality | New committed runtime, four fixed configurations and strict finding identities |

External source audits explain the storage prototype but are not proofs.
Section 5 records its current native checks and still-failing natural
reproducer; Section 7 links separate portable pass evidence. Native PASS is
not project acceptance or shared-loop recovery. Keep the failing end-to-end
gate and the distinct pending C2 decision explicit.

## 10. Measurement and rollout

Complete constructive local proofs and native red cases, then implement only
the reviewed scopes. Run default dataflow/JVM gates and exact regressions.
Tie changed expectations to the selected MAY, H or pass law; do not weaken
unrelated field, NORMAL, MUST, STAR, C2 or quality assertions to pass tests.
Commit the tested runtime before measuring projects.

Repeat OWASP, Conductor, Thingsboard and Stirling-PDF through direct
runProjectAnalyzer: FULL, 16 GiB, `1,1,2,...`, aliases/statics enabled and
saved budgets. Reuse f945, 52f and 8331 controls. Preserve owned evidence before
clearing old raw captures. Record reached/completed/accepted runs, exact
findings, phase coverage, CPU/allocation/GC, counters and OOM signals; capture
a heap if MemoryManager reports OOM. More positions can add work, and earlier
normal results can remove later demand; neither outcome is assumed.

The 4182 project report remains a control, not a measurement of this draft.
Quality acceptance and the overall task remain open. Lazy observations,
sparse C5 programs and frozen static inputs remain separate unselected work.
