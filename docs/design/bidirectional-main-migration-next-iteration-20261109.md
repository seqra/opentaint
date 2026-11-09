# Next iteration after the main migration

Historical record for the earlier uncapped runtime. Use the latest
[run-11 validation report](../reports/bidirectional-run11-cutoff-validation-20261109.md)
and [replacement next-iteration proposal](../design/bidirectional-run11-next-iteration-20261109.md).
The newer measurements supersede this document for optimization selection.


9 November 2026. Status: proposal, not selected for implementation. Runtime
pin: `9b21b3716`; measured source HEAD: `03cf52fa9`. The
[validation report](../reports/bidirectional-main-migration-validation.md)
contains the data and limits. Current project limits remain unchanged.

Latest reached / completed / accepted forward runs:

- OWASP: **run-185 / run-184 / run-183**.
- Conductor: **run-8 / run-7 / run-7**.
- Thingsboard: **run-1 / none / none**, OOM.
- Stirling-PDF: **run-11 / run-10 / run-9**.

The full Java/Go rule gate is still running. Project heap/profile checks are
complete. The rank can change with the remaining rule results. These proposals do not change
the current core. IR storage is out of scope.

## Ranked work reduction

| Rank | Change | Current work | Proposed work | Expected scope and limit |
| --- | --- | --- | --- | --- |
| 1 | Avoid materializing and replaying losing loop probes | Each prefix trial can intern initials and repeat saved replay, C2 and C5 | Prune tail-incompatible C2 descendants; reject a losing prefix on one proved extra descriptor | Dominant late Conductor loop observer and a large Stirling share; preserve exact output signatures |
| 2 | Keep healthy forms across iterations | Every engine and barrier clears managed payloads; later calls rebuild identical forms | Keep payloads while healthy; use the existing pressure eviction and final owner cleanup | Repeated rule/form construction; no claim that this alone fixes a refinement cycle or Thingsboard OOM |
| 3 | Merge equal pending static images before answers | One mutable image wrapper per pending mark; eager per-mark image union | One immutable image bucket plus merged marks; merge geometry only for an answered mark | Measured 2.74 million memberships versus 251,351 point/root pairs; whole-heap saving is smaller than this ratio |
| 4 | Avoid full exit-sink objects during prescan discovery | Broad exit templates bind across many methods, and selected copies retain originals | Use exact lightweight eligibility for ID discovery; defer full objects until required | 129 templates become 4.10 million sink objects; provider owner is 7.09% of Thingsboard heap, so no 2x heap claim |

No speed factor is claimed before an experiment. The first two changes target
work that need not run at all. The third also changes representation. The
fourth must preserve the exact selected-rule set.

## Avoid materializing losing loop probes

Conductor run-8 spends 85.91% of Java execution samples in loop-observer
C2, versus about 2% in all C5. Stirling spends substantial time in actual
and virtual saved replay and canonicalization. This proposal avoids work
inside pure observation; it does not change loop admission or restriction.

### Select C2 demand nodes by the actual tail

`FrozenDemandTrie.visitCountedNativeOrder` currently visits every descendant
below the actual path. Yet `RestrictedInitialPolicy.emit` rejects a demand
strictly below a STAR or EXACT actual. No companion can be emitted without
a primary. Therefore those descendant visits cannot change the answer.

A captured Conductor scoped query at `ParametersUtils.replace` has 4,666
compatible terminals at or below a local-root STAR/FLOW input. Two are
same-path terminals and 4,664 are strict descendants which cannot emit.
A tail-aware visit keeps the root and removes 4,664 rejected calls. The other
context removes 3,820. These are exact per-query counts, not query frequencies
or a whole-run speed estimate.

```text
visitLocalC2(actual):
    visit all nodes on the path to actual.path, in existing order
    visit the node at actual.path
    if actual.tail is ANY or MUST:
        visit its descendants, in existing order
    // STAR and EXACT stop at the same-path node.
```

Keep OUTPUT_C5, precision cursors, control rows, static carry and run-2
transitive completion unchanged. ANY and MUST must keep descendant lookup:
`x.[any]/T` can supply demand `x.f.[any]/T`; MUST can supply a required
child too. Mark/exclusion and complete-family checks still use the existing
policy. Do not replace them with a geometric overlap approximation.

### Reject a prefix on the first extra observation

The current gate constructs full initial sets for trial prefixes, interns
those initials, replays saved summaries and compares complete signatures.
Most trial initials are never delivered. C2 already has a pure structural
emitter, `emitAdmissions`.

Keep the existing run-1, ZERO and non-growing-summary bypasses first.
Use structural descriptors for the raw signature. During a prefix trial,
an emitted admission which is absent from the matching baseline family
already proves inequality. Adjacent, repeat and labelled admission sets only
grow by exact union. Stop that failed trial before constructing its remaining
initials or replaying enclosing summaries. If no such witness is available,
use the complete existing observer.

```text
baseline = fullObservationDescriptors(raw)
if baseline is empty: drop

for budget from 1 to rawDepth - 1:
    candidate = limit(raw, budget)
    witness = findExtraLocalC2Descriptor(candidate, baseline)
    if witness exists:
        continue  // This candidate cannot equal the baseline.
    observed = fullObservationDescriptors(candidate)
    if observed == baseline:
        deliver candidate through ordinary admission
        return

deliver raw through ordinary admission
```

An absent witness is not permission to accept. Missing baseline members still
require the full equality test. Reuse completed pure query work when possible;
do not add a second full C2 pass on successful candidates. Intern the compared C2 starts only for real delivery, not for descriptor
comparison. Native enclosing normalization and full fallback can still need
owned APs; removing those allocations requires a separate proof. Unknown views
and run-2 transitive queries can retain the current complete fallback.

Preserve every companion, layer, protection membership, scope and physical
port. Keep ZERO bypass, growth classification, boundary liveness, saved
summary order, Targets and ND execution. The old range certificate stays
disabled in this candidate; no unproved ANY-primary assumption is restored.

The required constructive proofs are: tail-pruned C2 emits the same family;
descriptor materialization equals ordinary admission; an extra descriptor
survives the complete monotone observation union; and the optimized gate
selects exactly the same prefix or raw result as the reference. Add native
differential tests for every C2 cell, both directions, both protection classes,
companions, missing-only differences and fallback views. Measure selected
nodes, emitted descriptors, real interned initials, early witnesses, full
observations and saved replays. A failed trial can avoid thousands of calls;
no fixed wall-time factor is claimed before measurement.

The [source audit and nine local laws](../../spec/lean/proposals/main-migration-work-reduction-20261109/README.md)
cover the negative filters. The largest reconstructed trie probe changes
4,666 compatible terminal visits to two. A separate deeper raw probe has four
C2 starts, while its budget-one candidate has 466. The actual descendant
demand `local3.MapValue.MapValue.[any]/FLOW` emits
`local3.MapValue.MapValue.*/FLOW,NORMAL`, which is outside the four-member
baseline. It is a concrete rejection witness. These are reconstructed probes
against captured demands; their live frequency is not known.

## Keep healthy forms across iterations

`RunManager.run` uses `MemoryManager.runWithMemoryManager` for each engine.
The driver uses it again for each barrier; run-1 also has a joined-static
scope. The wrapper always calls `cleanup()` on all managed soft-reference
managers in `finally`. This clears references and disables registration even
without memory pressure. The method-entry/form owner survives these scopes.

Late OWASP runs repeatedly spend most Java samples in call processing and
allocate condition compilers/builders. The same FULL view is used long after
run-1. This is a deterministic invalidation path in addition to normal JVM
and pressure eviction.

Use the existing ownership and eviction machinery. Add an explicit guard
exit policy, rather than rewrite `SoftReferenceManager`:

```text
whole analysis:
    retained = explicit analysis-owned method-form manager
    try:
        for each engine, joined phase and barrier:
            with memory guard(keepOnExit = {retained}):
                run the existing operation
                // GC pressure still uses the existing cleanup policy.
    finally:
        clear managed references at the analysis-owner boundary

legacy caller:
    with memory guard(keepOnExit = {}):
        run as before
```

Keep other managed caches on their current exit policy until their owners
are audited. Do not retain the unrelated per-run interner caches as a hidden
side effect. Pass explicit owner references through the guard; do not put
JVM cache-name lookups in the common engine. Keep the legacy wrapper overload.

Keep per-engine OOM callbacks, deadlines, cancellation and joined release.
A cache hit must not return a different rule view or another method context.
Keep FULL and RUN1_GROUP slots separate. Check every cached payload for
run-specific closures before selection. A form-build counter test must show
reuse across healthy forward/backward iterations, then correct rebuild after
pressure eviction. A failed/cancelled analysis must still release all owned
resources.

This changes cache lifetime, not transfer semantics. A performance test must
compare builds/reversals and allocation, not only total wall time. A repeated
refinement cycle can still consume its whole timeout after this optimization.

## Merge equal pending static images

Thingsboard run-1 retains 99,692 point rows and 2,741,433 pending mark entries.
88,106 rows have one identical immutable FLOW root for all their pending
marks. Those rows hold 2,563,315 memberships (93.50%). There are 251,351
point/root pairs in total, versus 2,741,433 per-mark wrappers. Most pending
memberships originate at `TenantId.tenants` and `TenantId.SYS_TENANT_ID`.
Only 997 static writer rows exist.

Keep the exact point key: operation site, original initial, current base,
tail, exclusions, layer and call-resume state. Merge only image storage:

```text
current: point -> mark -> union(FLOW images)
new:     point -> immutable FLOW image -> merged pending marks

offer(point, image, marks):
    pending[point][image] |= marks

answer(point, T):
    images = detach T from every matching image bucket
    answer with union(images), using the existing resume operation
    erase empty buckets
```

The invariant is exact for each point and mark:

```text
oldImage(point, T) = union(image | T in pending[point][image])
```

Do not retain a history of answered requests. New images after an answer use
the existing processed-group path. Do not merge different contexts, sites,
layers or exclusions. Preserve late writes and the three global request sets.
This does not filter a static field or change which marks are eligible.

The snapshot proves duplicate image memberships, not a 10.9x process-memory
saving. FLOW roots are already shared. Count map entries, wrappers, union
operations and retained subgraphs separately. Avoid a new unbounded history
of successive roots: equal buckets merge, and a dominating bucket can absorb
another only with a mark-membership-preserving union proof. If that proof is
not available, retain the exact buckets and measure their bound first.

## Avoid full exit-sink binding during prescan discovery

There are 129 serialized exit-sink templates and 4,101,442 bound sink objects.
Only 2,051,225 sink metadata objects exist. Selected specialization can keep
an original sink through `RuleSpecializationIndices.originalRule`. The exact
per-epoch distribution still needs the owner query.

Prescan needs serialized IDs, not every complete exit-sink/action object.
However, name matching alone does not preserve the ID set. For example:

```text
CM(Result,T) on void method             -> false, drop
NOT CM(Result,T) on void method         -> true, retain
CM(This,T) on static method             -> false, drop
missing argument / AnyArgument contexts -> use the existing binder rules
```

Reuse the exact condition/context existence test in a lightweight collector:

```text
prescan:
    for template in matchingExitTemplates(method):
        if exactBoundConditionCanExist(template, method):
            record template.serializedId

actual exit processing:
    bind the required rule through the current resolver
    evaluate it through the current boundary join
```

Unconditional and negative guards must still run on ZERO. FLOW facts must
still create all required mark requests. Preserve original conditions,
ordinals, signed simplification and fixed-point mark reduction. Do not change
selection to all name-matched IDs. Do not add another strong cache. An old
prescan epoch can be released only after proving that it is obsolete and
actually retained; epoch replacement already exists.

## Investigate synthetic alias cycles before changing them

A Conductor point has a long path with repeated synthetic
`HttpHeaders.headerValues` and `HeaderIterator.headers`. The HeaderIterator
model has both `this -> result` and `this.headers -> result`. The alias adapter
converts CopyAllMarks rules to symmetric aliases, which can equate an iterator
with its synthetic contents and permit unbounded path variants. The fields
are model slots, not physical Java backreferences.

This is a candidate source of avoidable expansion. It is not yet the complete
native producer trace: the long point can involve reversed transfers, alias
expansion and virtual dispatch. Only 1,789 of the 41,898 sampled point rows
have adjacent `headerValues` repetitions, and the same method also has other
collection paths. Do not claim that deleting this one pattern halves work.

First create a small source/model reproduction with exact points and all
relevant shorter NORMAL relations. Then decide between a finite canonical
representation of the existing cyclic alias closure, and a changed distinction
between taint copy and true object alias. The former needs observation
equivalence at reads, writes, cleaners and rule checks. The latter is a **major
alias semantic change**, can affect field updates and findings, and requires
explicit selection and per-model completeness proofs. No string-based path
shortening or new alias filter is included in the four optimizations above.

## Target/refinement lifetime is an acceptance blocker

The current rule-suite upload sample has a retained root report but continues
through hundreds of thousands of runs. Its run-57799 input contains no paired
DATA rows, only 26 controls. Completed forward runs emit 27 raw Targets and
27 normalized patterns; those counters are not a proven partition. Frozen
paths are at most two accessors despite field limit57,798. The separate
[rule-cycle evidence](../reports/data/bidirectional-main-migration-upload-cycle.json)
contains the source and native operators.

One retained NORMAL producer supplies `iterator.Element.MUST/T2`. The root
ANY/T2 demand emits STAR/T2 DEMAND, while a same-path demand retains MUST/T2
NORMAL. Production C2 confirms both. Preserve the selected STAR policy in this
iteration; do not silently choose the previously rejected MUST-admission
strategy. A new admission decision needs an explicit specification and proofs.

A NORMAL sink witness has a stable report key. A DEMAND witness becomes an
anonymous Target. Thus its later obligations cannot be matched directly to an
already settled root report. More field depth does not remove this class of
continuation. The four performance optimizations can reduce its per-run cost;
they do not by themselves prove convergence.

The next design should decide how an obligation becomes answered. A candidate
is to retain or check its physical sink identity before anonymization, then
stop refinement whose only observable goal is already settled. This is a
**major refinement-policy change**, not a cache optimization. Do not use a
conditional `P -> NormalTarget(id)` as a settled report; require an accepted
entrypoint `ZERO -> NormalTarget(id)`. Prove preservation with multiple sinks,
shared source guards, late inputs and later source permissions. Normalized
DATA/control dependencies must remain live for other unresolved goals.

The current early heap cannot identify each final anonymous witness or prove
the full cycle. A small native reproduction and dependency/progress model
are required before selecting that candidate. Do not stop on equal counts,
report stability, the expected test result or an arbitrary iteration limit.

The later rule sample `fileToStringUnsafe` shows this problem without a loop:
`new File(BASE_DIR, input)` then `new FileInputStream(file.toString())`.
It reports in run-1 but was still active at **run-129444**. Forward runs
3/5/7 each have exactly one normalized Target control and no DATA pairs;
backward runs 2/4/6 have two patterns and one outgoing Target. The singleton
partition follows from the typed handoff builder, not equality between two
unrelated counters. Exact witness/state equality is not yet proved. This
straight-line case must be a regression case for the future lifetime design.
It shows why loop-probe work reduction alone cannot establish convergence.

A single native snapshot then confirms strongly rooted, consecutive
**run-129800/129801** configurations with zero paired DATA in both. Backward
has only `(Target,ZERO)` and three sink seeds. Forward has that control plus
`(ZERO,ZERO)` and 18 source permissions. All three sink ordinals use report0's
physical call; `ZERO -> NormalTarget(0)` is retained. No saved FLOW relation
exists. This narrows the required design to control/source/Target lifetime;
neither loop restriction nor reverse-FLOW matching can settle this case.
The snapshot has no current point store or anonymous witness, so its exact
MAY origin and a complete semantic fixed point are still unproved. Preserve
that distinction in the regression and future proof.

## Correctness work before acceptance

These are separate semantic/reporting decisions. They are not hidden inside
the four performance changes.

1. **Exact-root cleaner refinement.** The small native example reaches its
   source in run-2, then replays the same root MUST and demotes it again through
   run-9. Source query geometry, MUST canonicalization and partial cleaning
   need one proved design. Adding a child beside its root is insufficient.
2. **Scoped Spring ZERO guidance.** Method-level run-1 static completion works,
   but the wrapper's backward terminal does not lead to inner-body ZERO in
   run-3. Capture exact scoped W/Target/control port tuples before selecting
   a repair. Keep ordinary DATA ports and the run-1-only completion lifetime.
3. **Intrinsic reverse-MUST demand.** OWASP run-82 has only 103 DATA rows plus
   1,008 controls, with paths at most two accessors despite limit 81. A saved
   NORMAL FLOW MUST relation reverses to STAR input and ANY/DEMAND output.
   Increasing field limits cannot remove that specific uncertainty. Trace
   its demand lifetime and test possible provider-backed elimination against
   nonuniform input counterexamples. Do not delete it merely because counts
   or reports repeat, or because a short NORMAL STAR relation exists.
4. **Honest exit locations.** The current descriptor has no witnessed concrete
   return. Display a method boundary when no origin exists, or design bounded
   physical-origin evidence before the shared exit join. Preserve NormalTarget
   identity. Moving rule evaluation to each return changes join semantics and
   needs a separate decision. No added Stirling report is classified as false
   positive without its actual mark/guard/path evidence.

A repeated-state detector can be a diagnostic, but it must not mark an
unresolved analysis complete or waive a native false negative. Any stopping
change needs an explicit semantic contract and a proof about future field
budgets, full frontiers, seeds and retained NORMAL providers.

## Experiments after selection

Use the current project configuration and fresh source pins. Compare findings
by exact identity/location, plus honest method-boundary relocation separately.
Always report reached, completed and accepted-forward run labels. Retain the
native failures until their expected findings pass.

For each selected change, record current versus new work: form builds and
reversals; loop baseline/trial observations and descriptor/real admissions;
static point/image/mark counts and union operations; bound exit objects and
exact prescan IDs. Show allocation estimates and retained ownership separately.
Repeat the full Gradle-only Java/Go rule gate. No timeout, heap, alias or static
ablation is part of this proposal. Design and prove each selected change under
[the proof guide](../../spec/proof-guide.md) before changing the core.
