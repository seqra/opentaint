# Keep the known head of a NORMAL uniform fact with a real hole

16 November 2026. Synthetic data-flow reachability. FULL marks. Follow
[proof-guide.md](../../spec/proof-guide.md). This is a design and a checked
reference model. Production is unchanged.

The [deeper-hole counterexample](bidirectional-deeper-excluded-guard-nontermination-20261116.md)
now naturally stops at **run-5**, with its valid NORMAL observation. The
earlier hole example also stops at **run-5**. All earlier ordinary examples
retain their exact histories and findings, latest **run-15**. The proof
includes an uncapped quiet suffix and accumulating Targets.

## 1. Selected semantic change

The first-field query loses information when it shortens a NORMAL MUST
actual whose real exclusion is scoped below that first field. Keep the
actual's already known head together with that exclusion in this narrow
case. Replace an existing query; do not add a query or enumerate suffixes.

```text
Dc:           p.M/T              paired Dp: ret.*/U
actual:       p.f.g.MUST/T {g}, NORMAL

previous:     p.f.*/T {}, DEMAND
proposed:     p.f.g.*/T {g}, DEMAND

previous companion: p.f.*/FLOW {}, NORMAL
proposed companion: p.f.g.*/FLOW {g}, NORMAL
unchanged prefix:   p.$/FLOW {}, NORMAL
```

This is a **major C2/C5-entry semantic change**, including a narrow exception
to the external `FL(Dc)+1` entry cap. It is not just an exclusion copy or a
storage optimization. The global field cap and every paired output cap
stay unchanged. Concrete STAR never gains NORMAL support.

## 2. Exhaustive FL+1 contract

Ordinary new DATA initials still obey:

```text
FL(I) <= min(globalLimit, FL(Dc)+1)
```

There is **one additional exception class**. Every condition below is
mandatory; there is no fallback based on “seems useful” or iteration count.

| Coordinate | Required value |
|---|---|
| Run | Restricted forward run, starting at run-3; run-1 is unchanged |
| Mark mode | FULL |
| Dc | MAY or NE with a concrete full mark T |
| Actual mark | The same concrete T, accepted by ordinary admission |
| Actual support | NORMAL |
| Actual tail | MUST |
| Actual E | Nonempty **real field** exclusions; mx alone does not qualify |
| Old command | An already admitted STAR start with Empty E and the same base |
| Heads | The old head is a strict prefix of the actual head |
| Global bound | The actual head already fits the current global limit |
| New head/E | Exactly the actual head and its E, without a further field |

Within that class only these two existing command forms can exceed
`FL(Dc)+1`:

| Command | New raw identity | Starting support |
|---|---|---|
| Concrete STAR primary | actual.head.STAR/T with actual.E | DEMAND |
| Its existing FLOW companion | same head/STAR and E; FLOW with Empty mx | NORMAL, conditional |

The actual MUST command is **not** added or split. A separate same-head
MUST lane already allowed by the old demand remains unchanged. An EXACT
prefix probe is not moved. Independent FLOW demands are not eligible.

The new initial may retain more than one extra known field. There is no
hidden `Dc+2` rule: its maximum is the already submitted head, bounded by
the global limit. No access path beyond that actual is constructed. All
other cases keep `FL(Dc)+1`, including STAR actuals even when NORMAL,
DEMAND MUST actuals, EXACT/MAY/NE actuals, empty E, GROUP, backward runs,
precise STAR/EXACT demands and failed ordinary admission.

Use native counted FL, including indivisible static anchors and array
accessors. Do not substitute raw list length for that native measure. The
Lean scalar paths and new local-field tests use unit-weight ordinary fields;
the replacement reuses a complete valid actual head rather than splitting
an accessor or inventing a static/class shape.

**No output exception is added:** every fresh NORMAL or DEMAND summary
continues to obey its own paired restriction:

```text
FL(conclusion) <= min(globalLimit, FL(original Dp)+1)
```

Run-1 uses its existing global limit 1 and has no previous Dc. ZERO and
Targets have no DATA field chain. The existing ZERO-premise loop shortcut
bypasses only the extra loop growth gate; it does not bypass C5 or a field
limit. Saved/predefined NORMAL replay keeps its existing policy and does
not authorize a new initial outside this contract.

### Admission and C5

The previous family below already includes the selected same-head E copy.
The new operation maps its existing members:

```text
emit(run, direction, mode, Dc, actual):
    family = previousCompleteC2Family(Dc, actual)
    if run == 1 or direction != FORWARD or mode != FULL:
        return family
    if Dc is not concrete MAY/NE or actual is not NORMAL MUST:
        return family
    if actual.E is empty:
        return family

    return map family as q:
        if q.tail == STAR and q.E is empty
           and q.base == actual.base
           and q.path is a strict prefix of actual.path:
            return q with path=actual.path, E=actual.E
        return q

C5(previousRow, rawInitial, rawConclusion):
    require rawInitial in the complete constructive image of emit
            for this row, before FLOW normalization
    // This is a structural image over legal offers, not an input-history cache.
    (P, C) = existingFLOWNormalization(rawInitial, rawConclusion)
    C = existingPairedOutputIntersection(C, previousRow.Dp)
    if C is empty: return empty
    C = existingCut(C, min(globalLimit, FL(previousRow.Dp)+1))
    return existingFLOWNormalization(P, C)
```

Ordinary rejection runs first. An input deeper than the global limit still
emits nothing. The map cannot create a family when admission rejected it.
It preserves base, tail, mark, mx, starting layer and binding protection.
Existing initial equality, hashing and persistence retain the changed
path/E as real AP coordinates; no new metadata field is introduced.

The raw C5 image must change with C2. The old entry test correctly rejects
the longer initial under its old cap, so reusing it would discard the
repair. Conversely, the new test must not admit a longer Empty-E initial,
a DEMAND actual or a hypothetical FLOW offer through this exception.
Keep complete row pairing and qualified refinement heads.

## 3. Why the head and E must stay together

For the actual p.f.g.MUST/T {g}, copying `{g}` to p.f would exclude p.f.g
itself. That loses an allowed actual point. Leaving q at p.f with Empty E
permits the impossible p.f.g.g check. The proposed start instead has:

```text
pointRegion(p.f.g.STAR {g}) = pointRegion(p.f.g.MUST {g})
```

This is equality of geometric possibilities. STAR does not gain MUST's
uniform mark guarantee. Every real point represented by the actual remains
available to native transfer, while an excluded descendant stays excluded.
The proof is generic in the head length and excluded accessor; it is not a
special case for f, g or this program.

The rule follows an existing actual path. It does not read a whole guard
path from the program, append a discarded suffix, compose evidence through
calls, select new fields, create artificial E or build a partition trie.
Native summary matching remains responsible for applying the conditional
result to its actual input. A result confined to the excluded subtree
cannot satisfy the retained premise.

## 4. New example and progress trace

```java
class Box { Box f; Box g; Box h; }

// Entry marking: T at a.f.g.MUST.
void root(Box a) {
    a.f.g.g = new Box();
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observe CM(z.M,U).
}
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
```

All bodies are analyzed ordinary code. There is no loop, recursion, cleaner,
pass rule or unresolved operation. The actions assign literal full marks
to fresh results. H is plain in this example.

Run-1/run-2 are unchanged. The source is cut to a.f.NE at limit 1. Run-3
can represent a.f.g.MUST/T and its real hole. Its root-MAY question now
starts the identity `p.f.g.*/T {g} -> p.f.g.*/T {g},D`. The deep guard is
blocked; the independent h action remains.

The key paired rows are:

```text
run-3 forward:
    p.f.g.*/T {g} -> ret.h.M/U,D
    p.f.g.*/T {g} -> ret.h.$/U,D

run-4 backward, ordinary paired C5:
    ret.h.*/U -> p.f.g.M/T,D
    ret.h.$/U -> p.f.g.M/T,D

run-5 forward:
    demand p.f.g.M/T + actual p.f.g.MUST/T {g},N
    -> existing same-head MUST initial, NORMAL
    -> p.f.g.MUST/T {g} -> ret.h.MUST/U,N
    -> p.f.g.MUST/T {g} -> ret.h.$/U,N
```

The unchanged C5 in run-4 supplies demand at the retained actual head.
It no longer renews the old root p.M/T question on this route. The next
call inputs are the corresponding h results, alternating U/T/U. Existing
NORMAL actual DATA coverage and definite saved MUST matching remain active.

[Complete per-block annotations through run-10](bidirectional-excluded-head-admission-trace-20261116.md)
list demand, submitted facts, initials and NORMAL/DEMAND summaries. The
following counts are for the marked-return/control reference, not a project
scan or all engine facts:

| Run | Direction / limit | Qualified rows | Retained NORMAL return records | Fresh root DemandTarget | NORMAL observation retained |
|---|---|---:|---:|---|---|
| run-1 | F / 1 | 4 | 0 | yes | no |
| run-2 | B / 1 | 14 | 0 | source permission renewed | no |
| run-3 | F / 2 | 10 | 0 | yes | no |
| run-4 | B / 3 | 10 | 0 | source permission renewed | no |
| run-5 | F / 4 | 0 | 10 | no; natural stop | yes |
| Every forced later run | existing increasing schedule | 0 | 10 | no | yes |

Targets accumulate through every delivery within each run. No emitted
Target is canceled when NORMAL DATA later arrives. Run-5 has no fresh
DEMAND observation at all. All ten NORMAL records are retained. The old
cyclic model eventually retained twelve records, including unused variants;
equal unused record sets for the new program are not claimed.

The constructive proof checks cold run-1..run-6, within-run quiescence,
natural stop at run-5, and an absorbing quiet state for every later run
number. This is not a finite-limit convergence argument.

## 5. Earlier examples

The earlier 18 ordinary references have FLOW-only rows at each checked
prefix. Generic whole-pipeline equivalence leaves their exact states,
findings and stops unchanged, even if actual E is nonempty:

| Natural stop | Ordinary references |
|---|---|
| run-3 | NestedExact, NestedNegative, OrdinaryTwo |
| run-5 | LongReader, NestedDeep, NestedPositive, NestedSurvivor, OldBB, OldMethod |
| run-7 | Growth, Prefix |
| run-9 | Nested, Overwrite, RoundTrip |
| run-11 | NestedLarger, PrefixPostfix |
| run-13 | Postfix |
| run-15 | Double |

The shallow real-hole example keeps its **run-5** stop and six NORMAL return
records. The alternating-generator and three strict concrete-replay cases
keep their **run-5** stops and observations. Empty-E equivalence covers the
strict replay histories; the alternating cold states are checked again.
Protected and selected-cleaner controls retain their separately scoped
**run-3/run-1** results. The new proposal does not redesign their rules.

## 6. Work and the rarity requirement

The exception class must remain exceptional. Its frequency on projects has
**not** been established by these synthetic checks. It is not enabled for
the common correlated STAR/FLOW, uncertain or DEMAND input cases.

In the new deep example, Lean checks exactly **two distinct over-cap keys
at run-3**, both at FL=2 for Dc at FL=0: the concrete key and its FLOW
companion. Run-5 has no over-cap key; the same-head MUST lane answers the
refined demand. The earlier cases retain their old histories under the
guard's unchanged branches. These are scoped counts, not a project-frequency
estimate.

Per old family, the operation is one map, with the same number of members
before deduplication. Paths come only from the old key or actual. It creates
no new path products, mark sets, guard combinations, fields or suffixes.
The immutable actual path and E can be reused. For scalar paths the prefix
test costs O(path length); native interned/trie keys may share that work.
All existing output cuts remain mandatory.

There is a measurable cost: two NORMAL uniform actuals p.f.g and p.f.h,
each with a real hole, previously shared p.f STAR. They can now require
two distinct conditional keys. A native test pins that 1-to-2 split.
Family-size equality is therefore **not** a global workload bound. No
production speedup or absence of all future field-growth patterns is proved.

Before implementation acceptance, record for each run and for methods and
generated loop blocks separately:

```text
all admission offers; admitted old families
NORMAL MUST actuals with nonempty real E
exception offers; rewritten concrete and FLOW commands
old/new distinct keys; owners with key splits
overrun = max(0, FL(new initial) - (FL(Dc)+1)) histogram and maximum
new/persisted summary counts; delivery work; time; peak memory
```

Every over-cap initial must have the exact certificate from section 2.
The Lean witness theorem is exhaustive: an emitted initial over Dc+1 has
an old admitted command and that certificate. Assert the same contract in
native diagnostic builds. Any other case is a bug, not a second exception.
Also check that output overrun above FL(Dp)+1 is always zero.

If these cases are common or split too many keys, revisit this exception's
representation before activation. Do not silently widen its eligibility
or disable an output cut. Falling back to the old coarse start when a
counter is exceeded would restore the known recurrence; it is not a
termination-preserving memory policy. Diagnostics need counters and bounded
owner samples, not a new persistent archive of actuals.

## 7. Validation and proof scope

[Proof package](../../spec/lean/proposals/excluded-head-admission-20261116/README.md):
**492 new constructive claims; 4,994 audited claims across 251 modules**.
All dependency sources are hash checked. The audit permits only `propext`
and `Quot.sound`; there are no custom axioms, holes, classical choice or
external decision oracles. State values propose witnesses; kernel-checked
transitions establish them. Existence results provide executable witnesses.

**41 native component/control tests pass**, including eleven new adapter
tests. They pin the narrow eligibility, retained head/E, unchanged global
rejection, STAR and DEMAND exclusions from the exception, the new C5 key,
native rule/summary behavior and the key-split cost. NE is checked in Lean;
the unchanged native API has no NE tail.

Production is unchanged. The historical native diagnostics still complete
**run-31/POLICY**. They are not integrated executions of this proposal. The
reference proves the supplied examples; it does not prove universal
termination, full-program finding equivalence, generic negative/ND rule
coverage, Java-front-end equivalence or production performance. Existing
native matching, complete rule conditions, ND execution, aliases, real
overwrites, primitive policy, protection, reports, ports, liveness, statics,
source permissions and the stop criterion remain unchanged.

```bash
python3 spec/lean/proposals/excluded-head-admission-20261116/check.py \
  --out /tmp/excluded-head-admission-proofs

cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ExcludedHeadAdmissionTest \
  --tests org.opentaint.dataflow.bidi.ConcreteQueryExclusionsTest \
  --tests org.opentaint.dataflow.bidi.DeeperExcludedGuardCycleTest \
  --tests org.opentaint.dataflow.bidi.ExcludedGuardCycleTest \
  --tests org.opentaint.dataflow.bidi.NormalUniformActualCoverageTest \
  --tests org.opentaint.dataflow.bidi.DefiniteMustReplayNativeTest --console=plain
```

Compiled output, large exports and logs stay outside the repository. The
linked trace embeds all readable state data. The consolidated proposal
includes this exception and no longer treats the deeper-hole case as open.
