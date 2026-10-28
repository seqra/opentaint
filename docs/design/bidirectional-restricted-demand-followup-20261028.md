# Restricted demand: exclusions, STAR inputs and killed static writes

Date: 28 October 2026. Reviewed checkout: `86eb2f043` plus the current
uncommitted implementation. The selected contract is
[restricted-demand-static-closure.md](../../spec/restricted-demand-static-closure.md).

The user selected the exclusion rule in section 1. Section 2 identifies a
stale validator. Sections 3 and 4 separate the killed-write guidance repair
from live writer-point handling. The user also selected immediate supply at the write point in section 4.
Summary processing is orthogonal. Do not add a live producer channel.

No project scan was made for this review. The last referenced Thingsboard
campaign reached **run-2**, completed **run-1**, and accepted **run-1**.
The five local killed-writer regressions reach and complete **run-3** and
then lose the finding. They are correctness tests, not project timings.

## 1. Selected: ignore abstract STAR demand field exclusions

Apply this rule to demand copies on both entry and exit:

```text
abstract demand: STAR/E/FLOW -> STAR/{}/FLOW
concrete demand: STAR/E/T    -> unchanged
actual input and native record E -> unchanged
```

Nonempty offered E is valid. It is not an admission error. Normalize before
demand deduplication, emission and C5 restriction. Keep the STAR tail. Do
not use the previous exclusion-union fallback.

```kotlin
fun normalizeDemandFieldExclusion(p: Pattern): Pattern =
    if (p.fact.mark is MarkSlot.Star && p.fact.tail == Tail.STAR)
        p.copy(exclusion = ExclusionSet.Empty)
    else p

fun normalizeDemand(d: DemandPattern) = DemandPattern(
    normalizeDemandFieldExclusion(d.entry),
    d.exit?.let(::normalizeDemandFieldExclusion),
)
```

For an abstract entry, the shared initial is independent of actual E and
actual marks. Actual E still affects overlap, summary satisfaction and
application. A blocked actual descent must remain blocked.

```text
offered Dc: x/STAR/{f}/FLOW
stored Dc:  x/STAR/{}/FLOW
actual:     x/STAR/{g}/T
initial:    x/STAR/{}/FLOW

actual x/STAR/{g}/T with Dc x.g/STAR/FLOW:
  no initial, because the actual exclusion blocks the descent
```

This changes demand permission. The whole-original containment check uses
normalized Dc. Normalizing abstract Dp can also permit an existing raw
result that its old E excluded. It adds no pair to that raw relation and
keeps the original, mark, layer and protection. Field transfer, cleaners,
actual exclusions, concrete demand exclusions and native records keep
their existing semantics.

[AbstractDemandEmptyExclusion.lean](../../spec/lean/proposals/restricted-demand/AbstractDemandEmptyExclusion.lean)
checks 19 local constructive results. These include normalization,
shared-start C2, retained C5 pairs, raw-pair containment and actual-E-aware
matching. They do not prove the complete JVM or iteration pipeline.
The selected runtime fix passes 95 focused tests, including nine new
boundary tests. TDD first recorded seven expected failures. Concrete,
actual and native-record exclusions retain dedicated checks.

## 2. Why the static input validator rejects STAR

The check depends on an old normal form. The field-limit schedule is not
the reason for the rejection.

| Change | Evidence | Consequence |
|---|---|---|
| Both first limits became 1 | `ff2966455`, 19 October | The equal limits predate the validator |
| Static-summary erasure | `b68b3a1c9`, 22 October | A concrete STAR descriptor started as ANY; the validator admitted named-field EXACT/ANY |
| Correlated concrete starts | `85dc2bbf8`, 26 October | Every run preserves concrete STAR, but the validator was left unchanged |
| Current restricted implementation | `StaticInputGrammar.kt` | The old validator moved from StrongQueries without a domain correction |

The class accessor C costs no field budget. Thus `S.C.f` has field depth 1:

```text
limit 1 (S.C.f / STAR / E / T)   = S.C.f / STAR / E / T
limit 2 (S.C.f / STAR / E / T)   = S.C.f / STAR / E / T
limit 1 (S.C.f.g / STAR / E / T) = S.C.f / ANY / {} / T
```

Raising the limit permits longer explicit paths. It does not expand a
STAR suffix or turn a bounded STAR into EXACT/ANY.

Demand is a separate operation. At the same path with an actual T:

| Actual | Concrete demand entry | Emitted initial |
|---|---|---|
| STAR/E/T | ANY/T | STAR/E/T |
| STAR/E/T | STAR/D/T | STAR/(E union D)/T |
| STAR/E/T | EXACT/T | EXACT/T |
| ANY/T | STAR/D/T | STAR/D/T |

These are concrete intersections; section 1 does not clear their E. An
EXACT guide can select an exact initial. It cannot be assumed for every
input. Validation currently runs before demand lookup, so a guide cannot
rescue a STAR input which that validator already rejects.

The consistent correction is to admit bounded named-field STAR/E inputs.
Keep fixed demand as the authority for starting work. Keep the ban on
broad concrete static roots and class-wide marks. Keep exact class
markers exact and backward MUST forbidden. Do not reintroduce STAR-to-ANY
widening to satisfy the stale validator.

The existing local
[static-domain model](../../spec/lean/proposals/restricted-demand/StaticInputGrammar.lean)
checks 15 declarations, including bounded STAR relay and the correlated AP
identity/limit operations. The validator correction now passes 44 focused tests. The existing STAR
literal/target rejection is tested separately and remains unchanged.

## 3. Separate guidance storage for static writes lost at exit

The proposed store has one purpose: preserve writer dependencies which
exit processing does not retain. It is not a pool, write-point directory,
normal summary or persistent record.

```java
Object get(Object p) {
    C.f = p;
    return C.f;
    // An exit rule removes the outgoing C.f value.
}
```

```text
body writer:       p -> C.f
post-exit writer:  absent
reader:            C.f -> ret

postprocessing uses the saved writer:
    p -> C.f ; C.f -> ret = p -> ret
run-2 guide:
    ret -> p
```

Store thin keys with the complete original, static output geometry and
complete mark relation. Include FLOW, colored relations, static copies
and genuine ZERO source effects. Run-1 has singleton originals only.
Keep colors distinct from FLOW. This does not add an ND edge, support
label or new field rule.

Capture input static dependencies at the executed exit pipeline. Also
observe static rule results before global-drop/entry-removal filtering.
Keep pending thin keys until final comparison with common retained
summaries and private static/static seeds. FLOW-backed storage can remove
a colored writer after an earlier observation; its exact survival is not
monotone. At the joined barrier, prune against the final available keys.
An earlier discard requires a proved stable-key or coverage contract.
Measure peak candidates; they are not all known kills during the run.
An unresolved or changed row may conservatively remain as guidance; do
not call it proof that a cleaner definitely killed that complete row.

```text
exit observation:
  pending += reached static input and each executed intermediate write key
  pending += final static result before common exit drops

complete barrier:
  retained = final available common-summary/private B guidance keys
  lost = pending without an equal retained key
  add lost to the guidance-only writer/bridge inventory
  bind required caller writers
  freeze the static closure
```

The store must survive long enough for static postprocessing. It cannot
be used to publish an outgoing relation that an exit rule removed.
An exit-rule write continues its existing exit pipeline; it must not
schedule NormalExit again.

Caller binding is still required for nonstatic and ZERO writer guidance:

```java
Object wrap(Object p) { return get(p); }
```

```text
killed writer in get: p_get -> C.f
actual call binding: p_wrap -> p_get
writer in wrap:      p_wrap -> C.f
reader in wrap:      C.f -> ret_wrap
guide in wrap:       p_wrap -> ret_wrap
```

The method call graph alone cannot translate formal arguments. It can
inherit static/static B rows. For nonstatic/ZERO writers, use the existing
actual caller subscriptions and full AP matching at the transition.
Use genuine reached ZERO controls, not prescan reachability as a source.

There is an important lifetime constraint: `RunManager.run` currently
joins workers, freezes actors and releases caller subscriptions before
`HandOff` starts. Therefore the transition must borrow those bindings
after join and before release, or freeze the required binding view there.
The preferred route is a joined read-only phase before release, with no
second caller-fact history and no live PW publication directory.

First bind only primitive and recursively caller-bound writer seeds.
Freeze that inventory before static composition; do not rebind a composed
guidance schema through callers. AP tail keys need not be equal under such
reassociation. Exact eager/factored equality applies to static closure of
the same frozen bound inventory. Required concrete witness coverage of
writer binding is a separate adapter contract.

The final acceptance proof must show required writer capture, caller
binding, mark-aware composition and finite closure. Test the existing
five failures, ZERO sources, returning wrappers, static copies and both
delivery orders. A local closure theorem with caller bindings as an
assumption does not establish that the production adapter supplies them.

## 4. Immediate write registration and the actual pool gate

Write registration already happens before exit handling:

```text
executed static-write micro-edge
  -> Run1PointResume.localWrite
  -> StaticFlowWriter registration
  -> req/processed groups wake WriterInterest
  -> ordinary Base(p)/T request
  -> actual marked input starts p/T
  -> the write executes with T
```

The missing step is not registration. Current `computedGroups` supplies
ZERO results directly and handles static-origin results. It ignores a
nonzero nonstatic relation such as `p/T -> C.f/T`. The older grouped-static
contract requires that relation to be applied outward through actual
caller bindings before it supplies the pool. If exit rules kill its
summary, that old route is gone.

The separate producer index added during this implementation preserves
that older gate independently of outgoing summaries. It was not needed
to register the write point. The earlier report did not make this
distinction clear.

The selected local rule is:

```text
executed local concrete write, after its existing complete guard:
  publish the bounded concrete static result to the pool immediately

FLOW write:
  register its existing request-producing writer point
```

Production nonstatic concrete initials are created from actual marked
inputs by request answering. Structural startup creates FLOW, not an
arbitrary `p/T` initial. Under the accepted run-1 field/context DEMAND
approximation, this actual-input-existence invariant can support the
simpler policy. The write-point path then owns registration and supply;
it needs no separate producer-summary replay channel.

This would explicitly replace the older requirement to rebind every
nonstatic colored writer through callers. It must not be called an
equivalent storage-only optimization. Later FULL field transfer,
complete rule guards, source eligibility and native summaries stay
unchanged. The user selected immediate supply at the write point and stated that
summary processing is orthogonal. The runtime removes the added producer
relay and passes 26 focused tests. Its local model has 14 constructive
audits. Killed-write postprocessing remains a separate implementation step.

A focused shadow-class probe preserves the earlier sink for a direct
caller and one wrapper when direct local supply replaces the producer
channel. It also fails an old test which manually injects a hypothetical
concrete initial and requires ZERO-derived supply. This exposes the
contract difference; it is not evidence that the old policy is unchanged.
These probes are not a committed production build or project campaign.
