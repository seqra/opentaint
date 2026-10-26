# Correlated concrete initials and general FLOW subsumption

Date: 26 October 2026. Status: **proposed; analyzer code is unchanged**.
Language: ASD-STE100 Simplified Technical English. Technical terms are defined below.
The file name is retained for existing links. The contract applies to **all runs**.

Read this spec with its [proof dossier](run1-correlated-concrete-initials-proofs.md).
The runtime baseline is `f4954c26403bc7ecb8b64018f8aabdd479fd022d`, core tree
`e3ede1a36d3b04d79a23cc93285f385ecd968dbf`. The latest referenced Thingsboard
measurement has **run-1 COMPLETE; run-2 OOM**, including the 16 GiB experiment.
This revision has no new project measurement. See the
[run-1 census](../docs/reports/bidirectional-run1-protection-coverage-20261026.md)
and [16 GiB report](../docs/reports/bidirectional-run2-16g-memory-20261026.md).

## 1. Selected changes

A concrete STAR initial starts with the same STAR conclusion, in every run.
Preserve that tail through operations which preserve the initial suffix.
Apply FLOW subsumption in every run, forward or backward, at the existing
summary admission points. The operation has no run-number or mark-mode gate.

```text
Current: (x.*/E, T) -> (x.[any], T),   DEMAND
New:     (x.*/E, T) -> (x.*/E, T),     DEMAND
```

For run-1, E is Empty. Later runs can have nonempty E. FULL marks and GROUP
atoms use the same AP operation. This does not introduce GROUP into a run
which currently uses FULL.

**The seed change is semantic.** It removes an initial approximation and
changes the legal conclusion grammar. General summary replacement also changes
which marked demands remain. These are selected changes, not factory details.

| Mechanism | Current | New | Affected contract |
| --- | --- | --- | --- |
| Concrete initial result | Independent output suffix, ANY | Same input/output suffix, STAR; retain E | AP start, W2 |
| Same-suffix transport | Concrete STAR is erased or rejected | Retain derived STAR in any run and direction | Normalization, transfer, summaries |
| Summary replacement | Enabled for FULL run-1, ANY output | General mechanism in every run; ANY prefix and STAR equal-path cells | Coverage, application, handoff, persistence |
| Dependency protection | Selected producers enable it for FULL run-1 | Apply the same non-subsumable contract wherever replacement is enabled | Rule/cleaner/cycle flags, record views |
| Typed representation | No concrete STAR conclusion | Distinct concrete STAR header, with the ordinary phase-specific E | Constructors, keys, decode, readers |

The earlier `mode.run1 && mode.markMode == FULL` tests were scope limits in
this proposal. They were not semantic requirements. Remove them from STAR
legality, initial emission and the subsumption mechanism.

The following contracts stay unchanged:

- FULL is the default run-1 mode. Each run keeps its current mark domain.
  GROUP selected-mark cleaners still cannot kill the whole group.
- Run-1 uses field limit 1. Later direction and field-limit rules stay unchanged.
- Requests and demands select the same initials. A run-1 request is mark-only,
  has no E, and is not relayed by a concrete input.
- Initial field paths, marks and seed layers do not change. There is no run-1
  ANY initial. Later ANY/EXACT/must initials keep their current start rows.
  ZERO and exact global class markers keep their current seeds.
- Run-1 E is Empty. Full overwrite kills and disjoint preservation remain.
  An exclusion-needing run-1 residual demotes and keeps its tail and Empty E.
  Later runs retain the existing strong field operations and E rules.
- Rule conditions, fixed-target actions, sources, sinks, all contributing
  run-1 origins and later ND rules keep their current transfer contracts.
- The run-1 static pool, three request sets, activation, summary erasure and
  implicit static demand remain. Later calls require the actual static premise.
- Barriers, FLOW priority, alias-effect classification, normal record eligibility
  and original demand emission/restriction remain. This proposal does not
  extend the run-1 scheduling policy to other runs.

There is no new grounding support, actual-input validation, dependency graph,
mark token or rule specialization. StrongQueries is not part of the proof.

This spec replaces the concrete-STAR ban in [AP W2](ap.md#23-well-formedness-rules)
and the run-1/FULL admission limit in
[FLOW-backed relations](run1-flow-backed-concrete-relations.md).
The proved replacement shapes are stated in section 5. Availability in every
run does not authorize every possible shape. Historical W2 and backward
no-concrete-STAR theorems keep their old assumptions; they do not prove this
extended grammar. The backward ban on must-taint stays unchanged.

## 2. Meaning and legal shapes

`T` and `U` are selected runtime mark atoms. In FULL mode an atom is a full
mark. In GROUP mode it is a group. `F` is the abstract FLOW mark. `N` is NORMAL
and `D` is DEMAND. `p`, `q` and `s` are field paths. `$` is EXACT.
`[any]` is a may tail. `[any-taint]` is the existing must tail.
These tails and STAR are different values.

```text
I = (x.p.*/Ei, T)
I -> (y.q.*/Eo, T)   means x.p.s/T -> y.q.s/T, for s admitted by Ei and Eo
I -> (y.q.[any], T)  permits x.p.s/T -> y.q.r/T, for independent s and r
```

**A STAR conclusion uses the suffix bound by its original relation.** A seed
or a correlation-preserving transfer must establish that property. That is
the legality condition. It does not depend on run, direction, mark mode,
Empty E, or a mandatory DEMAND layer.

A concrete mark selects which mark the row carries. STAR selects how its
field suffix relates to the original. These are separate properties.
Same input/output mark is required for FLOW subsumption, not for the meaning
of a STAR tail. This spec does not add STAR targets to source/GEN rules.
Their existing fixed targets still control their outputs.

Do not invent a suffix binder for ZERO or an ND premise set. Keep their
current fixed-target results. Do not treat an independent ANY value or a
must-taint value as STAR. Ordinary constructors encode the supplied kind;
transfer owns the proof that a STAR kind is appropriate. No new support label
is needed. The original relation already identifies the binder.

An actual input must still supply T. A concrete STAR seed is not a source
and does not assert that every descendant has T. For a CM check, STAR is not
a must-taint observation. Keep the current overlap/mark test and layer rule.

Each run retains its existing initial grammar. In run-1 a non-static initial
has an empty concrete path; a nonexact static initial names `S.C.f.*`.
An exact global class marker stays `S.C.$/T`. Later runs can use their existing
deeper paths and exclusions. Do not add broad concrete root/class statics.

## 3. Initial emission

After the current request/input/demand match selects an initial, start its
identity relation. A STAR initial is not widened because its mark is concrete.

```kotlin
fun start(initial: InitialAp): Facts {
    if (initial.isZero) return Reach.NORMAL
    return when (initial.tail) {
        STAR -> when (val mark = initial.mark) {
            is AbstractMark -> flowTree(initial.base, NORMAL,
                leafAt(initial.path), initial.exclusion, mark.exclusion,
                tail = STAR)
            is ConcreteMark -> taintTree(initial.base, DEMAND,
                leafAt(initial.path, mark), initial.exclusion,
                nonExactTail = STAR, nonSubsumable = false)
        }
        else -> currentStart(initial) // ANY, EXACT and must rows are unchanged.
    }
}
```

This function needs no mode parameter. The caller already validates the
initial and selects its runtime atom. A wrapper can still accept a mode to
project the atom; it must not use that mode to widen the tail. Run-1 validation
still requires Empty E and its bounded grammar. Later validation permits its ordinary nonempty E.

The concrete STAR seed stays DEMAND, as before. An identity alone does not
change the current seed-layer policy. Subsequent transfers preserve their
computed layer; they do not infer a layer from the tail. Do not set the
non-subsumable flag on an identity seed.

Use the same start operation when a run-1 static point selects a concrete
STAR original. Keep its point and call stage. Do not replay the method from
entry. A raw pool reply has no bound writer/reader suffix; it remains an
independent value until the existing procedure selects the static original.

## 4. Transfer and deliberate loss of correlation

Use the current AP geometry and mark kernels in every direction. Remove the
mark-only W2 erasure after a legal STAR result. A layer change alone does not
change a field tail. Let `L` be the layer computed by the current operation.

| Operation on a concrete STAR row | Result |
| --- | --- |
| Identity or copy at the tracked prefix | STAR, same suffix, L |
| Input below a copy premise | Append the known remainder; keep STAR and L |
| Read premise strictly below the tracked prefix | ANY/D, unless the target is EXACT |
| Explicit may target | ANY/D |
| Field-limit overflow | ANY/D at the retained prefix |
| Ordinary call bindings and diagonal STAR summary | Compose the suffix; keep STAR if the actual input is STAR |
| Summary on an actual ANY or EXACT value | Keep the computed ANY or EXACT result; do not recover STAR |
| Full overwrite | Kill, as now |
| Disjoint write/cleaner/filter | Keep the original tail |
| Field transfer needs an exclusion | Use the current run's E/layer policy; preserve a representable STAR suffix |
| Source, fixed rule target, ND output | Use the existing EXACT, ANY or must target |

In run-1, an exclusion-needing residual uses Empty E and D. In later runs,
retain the ordinary exclusion when the current strong transfer produces it.
Do not apply the run-1 E-free cover to later runs. Do not change a selected
cleaner's spatial cases or the current partial-cleaning approximation.

A read below the tracked prefix consumes part of the unknown suffix:

```java
Object read(Object p) { return p.f; }
```

```text
Seed:         p.*/T -> p.*/T, D
Read witness: input p.f.s/T -> return.s/T
Result:       p.*/T -> return.[any]/T, D
Invalid:      p.*/T -> return.*/T   // This would return f.s, not s.
```

A known concrete output path can grow without loss:

```java
Box wrap(Object p) { Box b = new Box(); b.value = p; return b; }
```

```text
Before: p.*/T -> p.[any]/T -> b.value.[any]/T -> return.value.[any]/T, D
After:  p.*/T -> p.*/T     -> b.value.*/T     -> return.value.*/T, D
FLOW:   p.*/F -> return.value.*/F, N or D
```

Field-limit overflow can still change either result to ANY. This example
assumes a precise copy summary for any setter/library operation it uses.

### 4.1 Cleaners, rules and protection

FULL selected cleaners keep their current requests, exclusions and kills.
GROUP selected cleaners request the group and retain it, as now.
RemoveAllMarks can kill. A surviving selected-mark result keeps the existing
non-subsumable protection wherever summary replacement can consume it.

Handle STAR explicitly in the spatial cleaner. For a below-only cleaner at
the tracked root, retain the current root residual:

```text
Input:  I -> x.*/T
Action: remove T strictly below x
Output: I -> x.$/T, same surviving layer, non-subsumable
```

Do not retain the whole STAR row because `tail.isAny` excludes STAR.
For other partial cleaners keep the current spatial approximation and E rule.
A fixed-position assignment uses its existing target. It does not inherit
the trigger's suffix. This includes same-T/cross-mark assignments, sink end
facts and ND results. All-ZERO cube tests keep their current behavior.

The existing protection rules now apply in every run and selected mark domain:
assignment compares the assigned atom to the triggering conclusion atom;
local/call cycles protect a restored original atom; summary protection is
sticky; identical plain/protected rows merge into the protected row.
For ND, consider every contributing input and keep its current premise set.
Do not change ND into unary edges in later runs.

This extension needs no member enumeration. A GROUP atom is compared as one
atom. Protecting a same-group action can be conservative; it does not let the
cleaner kill the group or restore its full members.

### 4.2 Statics and suffix ownership

ZERO can activate a static premise only during run-1. It does not supply a
suffix. The existing procedure retains or selects a static original:

```text
I(S.C.f.*/T) -> local.*/T, D    // Legal for a same-suffix read.
I(S.C.f.*/T) -> return.*/T, D   // Legal through a conditional copy.
ZERO         -> return.*/T     // A pool reply does not authorize this.
```

Different writers have independent suffixes. Keep the current pool union.
A raw pool value uses ANY/EXACT. Installing the selected canonical STAR
initial uses the identity seed. A saved ANY image stays ANY.
No new S-S summaries are stored or sent in run-1. Later calls require the
actual static fact and use ordinary summary application and field behavior.

## 5. General FLOW replacement

Enable the mechanism in **all runs and directions**, for each current mark
domain. It compares relations in one current view, not a forward row against
an unreversed backward row, or unrelated native records from different runs.
Do not synthesize extra FLOW queries to make a counterpart exist. If there
is no matching FLOW row, keep the marked row.

A candidate has a singleton, non-ZERO initial. Its FLOW counterpart has the
same complete initial shape, including tail and E, with the mark replaced by
F. That counterpart must be well formed. STAR and ANY initial tails can use
this test. EXACT and must initials have no legal abstract-mark counterpart;
keep their marked rows. ND rows also stay outside this replacement cell.

```kotlin
fun covers(e: MarkedLeaf, f: FlowLeaf): Boolean =
    sameSummaryScopeAndInitialGeometry(e, f) &&
    e.inputMark == e.outputMark && !e.nonSubsumable &&
    e.outputMark !in f.markExclusion &&
    (f.layer == NORMAL || e.layer == DEMAND) &&
    sameAliasEffectClass(e, f) &&
    when {
        e.tail == STAR && f.tail == STAR ->
            e.finalBase == f.finalBase && e.finalPath == f.finalPath &&
            f.fieldExclusion.isSubsetOf(e.fieldExclusion)
        e.tail == ANY && f.tail == ANY ->
            e.finalBase == f.finalBase && f.finalPath.isPrefixOf(e.finalPath)
        else -> false
    }
```

There is no `run1`, `FULL`, forward-only or Empty-E admission test.
For a FLOW tree, one actual output leaf must satisfy all gates for each
marked output path/atom. A branch node without an output leaf is not enough.
Keep method/context, direction/view, endpoint, exit kind, call stage and the
existing alias-effect class in the comparison scope.

For STAR, equal output paths and sufficient suffix admission are required.
FLOW can exclude fewer first fields than TAINT, never more. Example:

```text
Same initial: x.p.*/{a}/T, or its FLOW counterpart
FLOW output:  y.q.*/{b}/F
TAINT output: y.q.*/{b,c}/T
Result: covered, if the other gates pass. Every TAINT suffix passes FLOW.
Reverse the two output exclusions: not covered.
```

A proper output path prefix is insufficient for STAR:

```text
FLOW:  p.*   -> return.f.*
TAINT: p.*/T -> return.f.g.*/T
Input suffix []: FLOW ends at return.f; TAINT ends at return.f.g.
Result: not covered.
```

Keep prefix containment for ANY/ANY. Keep the current same-base identity
exception in the ANY alias-effect classifier. Equal-path STAR identities
have the same FLOW and TAINT effect class. Do not add cross-tail, EXACT/must,
cross-mark or protected-result replacement here. Do not recover STAR from
ANY because a FLOW row arrives.

Apply semantic replacement at the current raw/selected/published summary
admission points. Typed local storage can share geometry, but it must still
process actual T checks and all producer hooks. FLOW alone does not fire CM,
source or sink observations. Removing an unprocessed marked seed is invalid.

The retained FLOW row replaces the eligible marked row. A DEMAND marked row
then needs no duplicate T demand. A NORMAL marked row can be replaced only
by NORMAL FLOW; retain the FLOW normal record under the existing persistence
rules. Do not upgrade a layer or demote a normal relation to justify deletion.

Carry the same protection through ordinary summaries and native/reversed
record views before they enter an enabled admission store. A view which
cannot preserve its mark/tail/flag cell must retain the marked residual.
Do not enable a bypass with missing protection. This is extension of the
existing Boolean metadata, not a new dependency or support mechanism.

## 6. Handoff between runs

Keep the existing direction-specific handoff. Forward-to-backward converts
a forward STAR conclusion into an ANY entry pattern; keep T:

```text
Forward marked demand: I(x.*/Ei/T) -> y.q.*/Eo/T, D
Backward guide:         entry y.q.[any]/T; exit x.*/Ei/T
```

For Empty Eo this has the same pattern location set. For nonempty Eo the
entry pattern is a conservative cover because handoff drops Eo. It still
retains each marked witness. The other endpoint keeps its ordinary shape.
Must-taint handoff and the existing mark-domain interpretation stay unchanged.

Backward-to-forward keeps its current demand endpoint construction. Do not
add the forward-to-backward erasure there. Both directions can now propagate
concrete STAR when an admitted initial and transfer preserve its suffix.
An unchanged ANY initial still starts ANY. This does not make all queries STAR.

If a row is replaced, the retained FLOW record or FLOW demand supplies the
same-mark transport. Original AP emission and whole-premise restriction still
apply. Protection keeps separate concrete guides at assignments, surviving
cleaners and cycles. Each run recomputes these flags on its own derivations;
ordinary cross-run demand patterns do not gain a new support label.
No actual-input-only query or StrongQueries permission is added.

A concrete STAR seed remains D. Its tail does not grant normal-record
eligibility. Other results use the existing layer rule and record check.
The proof claim is witness/demand coverage, not equality of the old coarse
candidates. The new seed is strictly smaller than the old one.

## 7. Inventory of ANY construction

This inventory covers production code for the bidirectional analyzer at the
pinned core tree. Legacy analyzers, tests and historical reference fixtures are
outside this source inventory. In the paths below, `B` means
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi`;
`J` means the adjacent `opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi`.
An ANY literal can construct a fact, an edge target, a read view or a pattern.
These are separate cases.

### 7.1 Operations which create an executable ANY result

| Source and operation | Why ANY exists now | Rule after this proposal |
| --- | --- | --- |
| `B/ap/Demand.kt: initialFacts`; `B/ap/Reference.kt: startFact` | Concrete STAR seed is projected to ANY | Every concrete STAR seed retains STAR and its E, in every run and mark mode |
| `B/ap/Reference.kt: normalize`; `B/ap/ApManager.kt: factsOf` | W2 erases concrete STAR; the typed factory calls this normalizer | Retain derived concrete STAR in every run. Remove the mark-only W2 erasure; do not infer a suffix binder from a raw region |
| `B/ap/EdgeApplication.kt: flow`, ancestor hit; `Reference.kt: above` | A read/binding/summary premise consumes an unknown suffix prefix | ANY/D unless target is EXACT; unchanged |
| `B/ap/EdgeApplication.kt: taint`, ancestor hit | Same loss for concrete may or new STAR input | Keep ANY/D for STAR/may; current must-specific result stays separate |
| `B/ap/EdgeApplication.kt: taint`, at a STAR target | A non-must concrete leaf is always emitted as ANY today | Keep STAR for legal same-suffix input; retain ANY for ANY input |
| `B/ap/EdgeApplication.kt: flow/taint`, explicit ANY target; `Reference.kt: below/above` | An explicitly independent target drops correlation | ANY/D; unchanged. An existing ANY value also stays ANY through a copy |
| `B/ap/Limit.kt: limitFacts/FieldLimitCut`; `Reference.kt: limit` | A concrete path exceeds the field budget; folded leaves use `LeafAlgebra.asAny` | Cut branch becomes ANY/D with Empty E. The kept branch retains its own tail |
| `J/interp/JIRRuleForms.kt: RulePos.star`, `CopyAllMarks`; `RulePos.fact`, `CopyMark` | A final AnyField pass target is may, not must | Keep the explicit ANY target. Do not reinterpret it as STAR |
| `B/engine/RunMethodLocalServices.kt: seedFact`; `B/ap/ApOps.kt: targetTree` | A backward sink seed with an AnyField requirement becomes an executable concrete ANY value | Keep ANY/D. The original sink pattern and the SEED field cut still apply |
| `B/ap/Reference.kt: reverse` and micro-edge reversal | Reversing a may/fixed edge can require an independent suffix | Keep the existing reversal table and demand bit; a resulting ANY stays ANY |

The ancestor-hit and explicit-target rows include local edges, call bindings,
alias micro-edges and applied method summaries. These use one AP transfer
kernel. They are not separate permission to widen all call results.

Source/GEN AnyField targets use `RulePos.sourceFact`, hence **ANY_TAINT**.
They are not direct ANY producers. Later transfer or a field cut can produce
ANY from them. Moving a must result to DEMAND alone must not do so.

### 7.2 Representation paths and static materialization

| Source | Current behavior | Required handling |
| --- | --- | --- |
| `B/ap/ApOut.kt: Results.flow/taint`; `Conclusions.kt`; `ApManager.kt` | Omitted tail arguments infer ANY from DEMAND; TAINT normal defaults to must | Pass STAR explicitly on the selected new paths. Layer is not a reason to erase a tail |
| `B/ap/Summary.kt: leafKinds` | A summary leaf becomes an edge with the stored ANY header | Compile the actual STAR/ANY/must header; do not erase STAR |
| `B/store/DiagonalRelations.kt: decode`; `B/engine/NeutralRelationBatch.kt: emit` | Current diagonal packets decode with an explicit ANY tail | Keep packets typed by tail, or use the scalar STAR fallback. An ANY packet cannot decode to STAR, or vice versa |
| `B/engine/Run1StaticService.kt: facts` | `factsOf` converts a canonical field STAR/concrete-atom reply to ANY | Keep raw membership independent. At an existing selected concrete STAR original, use the new start contract; keep raw ANY where no such binder exists |
| `B/engine/RunMethodAnalyzer.kt: knownStaticInput` | Rebuilds the canonical input through `factsOf`, which erases concrete STAR | Use the general seed under that known static original |
| `B/engine/Run1PointResume.kt: direct/packed answers`; `RunMethodCallServices.kt: applyStaticInput/applyStaticSummary` | Rebuilds scalar facts and applies a saved FLOW/summary image | Select the existing static original, then preserve only a same-suffix result. An ANY saved image stays ANY |

Generic reconstruction sites such as scalar summary extraction, return cleanup,
protection replay and diagnostic decode must preserve the supplied tail. They
do not have independent widening permission. `withLayer` must preserve it too.
A raw encoder preserves the supplied tail. A producer without a suffix binder
must select ANY explicitly before encoding. For example, a raw static pool
reply uses ANY/D; installing its selected canonical initial uses the STAR
identity seed. Factory normalization must not decide this from the run number.

### 7.3 ANY patterns, demands and transient read views

| Source | Object built | Meaning |
| --- | --- | --- |
| `B/driver/HandOff.kt: toBackward`, `located` | Backward entry/demand pattern | STAR -> ANY; must -> ANY; keep concrete marks |
| `B/store/DemandStore.kt: implicitStaticPair` | Universal static field/group query pattern | Existing static completion; not a propagated run-1 fact |
| `B/engine/StrongQueries.kt` | Later-run query/completion pattern | Current STAR/must -> ANY query conversion; unchanged and not used to justify this feature |
| `B/engine/RunMethodCallServices.kt: cleanChain` | Field-cleaner feedback pattern | BELOW/descendant reach uses ANY; exact reach uses EXACT |
| `B/engine/Run1StaticService.kt: intersect` | Region selector | Same-depth intersection uses ANY if a selector is ANY; it has no shared suffix |
| `J/interp/JIRRuleForms.kt: RulePos.fact`, condition literals | CM AnyField pattern | Match a descendant; this does not assign ANY to an initial |
| `B/ap/Reference.kt: mustRecordReadView` | Transient must-summary read view | Replaces must with ANY for a demand view; native stored record stays unchanged |
| `B/ap/Reference.kt: field-cleaner feedback helper` | Feedback pattern | A must observation uses concrete ANY; no executable STAR erasure |
| `B/ap/Reference.kt: emit` and `B/ap/Demand.kt: emitInitials` | Restricted-run initial selected by a demand meet | A concrete ANY demand may select an ANY initial later; run-1 grammar still rejects it |

The `Tail.ANY` tests in `Groups.kt`, `Facts.kt`, `Primitives.kt`,
`RuleStatement.kt`, `Summary.kt` selectors and `FlowBackedCoverage.kt` are
consumers/validators, not new semantic producers. Audit their handling of the
new legal STAR type. An arbitrary blanket replacement of `isAny` is unsafe.

## 8. Representation and implementation obligations

Replace the mark-only W2 ban with the bound-suffix invariant. A generic
constructor and normalizer must retain a legal STAR value in any run. Keep
ANY when a read, cut, explicit target or binder loss actually loses correlation.
Do not let the constructor decide this from mark kind, layer or run number.

The typed TAINT nonexact header distinguishes STAR, ANY and ANY_TAINT.
Include the tail and E in grouping, equality and hashing. Keep EXACT siblings
and protection masks exact. A STAR branch cannot inherit an ANY sibling's
header when roots merge. Protection remains metadata with explicit OR
admission; it is not part of ordinary edge equality.

Same-premise TAINT admission needs an explicit STAR case. Deduplicate equal
STAR paths/atoms and OR their flags. Do not apply a must-leaf descendant rule
to STAR because both use the current `any` payload channel. Existing ANY
coverage can cover a STAR pair under the same original and protection gate;
it does not reclassify the retained ANY as STAR.

Implementation must update the following current gates. This is a proposal,
not permission to apply them without their matching transfer/flag changes:

```kotlin
// All runs. Replacement retains the shape, scope, layer and flag gates above.
val summaries = RunSummaryStore(ap, flowBacked = true)
val publications = PublicationIndex(ap, flowBacked = true)

// No run/FULL gate inside the semantic matcher or protection transfer.
val counterpart = flowInitialForCoverage(ap, premise) // Check legal geometry.
val seed = start(initial)                           // Check the initial tail.
```

Audit `RunMethodAnalyzer` admission owners, `FlowBackedCoverage`,
`FlowBackedSummaries`, `DiagonalRelations`, local rule/ND producers,
`ApOps` cleaner/cycle protection, record views and publication admission.
Keep run-1-only queue, temporary static supply, cleanup and ND approximation
optimizations scoped as before. A run-1 packet format can remain an
optimization; the general scalar route must implement the same coverage law.

Audit constructors, canonicalization, groups, positive/negative CM readers,
selection, restriction, leaves, summary compilation, call adapters, flags
and decode in both directions. Preserve E in later runs. Do not introduce
unselected strong field validation, queries or new static pool routing.

## 9. Proof and validation gates

The [Lean module](lean/ApSpec/Run1CorrelatedConcreteInitials.lean) retains its
file name for links. Its general laws have no run or direction parameter.
They cover arbitrary paths, mark atoms, initial tails, STAR exclusions and
layers. They check the general seed identity, specialization, exclusion
coverage, ANY prefix coverage, application, reversal and handoff cover.
The [dossier](run1-correlated-concrete-initials-proofs.md) states their limits.

Before implementation is accepted, verify:

1. Start tables in both directions and every existing mark domain. Include
   STAR with Empty/nonempty E, later ANY/EXACT/must initials, ZERO and class marks.
2. Copies, reads above/below a prefix, aliases, cuts and mixed STAR/ANY/EXACT
   branches at field limits 1 and higher. Test suffixes [], [f], [g] and [f,g].
3. Run-1 full kill/disjoint/E-free residuals and later strong exclusion rows.
   Test every cleaner reach, GROUP no-kill, survival flags and flag union.
4. Sources, same/cross-atom assignments, local/call cycles, run-1 unary origins
   and later ND sets. Preserve every existing ZERO/condition/target contract.
5. Static late activation, raw independent pool values, selected static
   identity seeds and erased S-S rows in run-1. Later calls require actual statics.
6. STAR equal-path/E-subset and ANY prefix summary replacement. Cover flags,
   mark exclusions, scope, alias effects, layers and FLOW arriving first/last.
7. Raw/selected/published stores and native/reversed records. Test no counterpart,
   unsupported tails, new protected deltas and an all-runs scalar fallback.
8. Both handoff directions, original emission and whole-premise restriction,
   with marked witnesses and protected dependencies. Do not use StrongQueries
   as the test oracle.

Compare concrete witness retention and observations. Do not require equality
of deliberately removed coarse pairs. No whole-engine refinement or
performance result follows from the local Lean proofs alone.

Measure each reached run, not run-1 only: stored tails, covered plain rows,
flag-blocked rows, publications, demand pairs, engine time and retained bytes.
Include the latest reached iteration, such as run-2 OOM, in each report.
Keep the project commands fixed. There is no new measurement in this revision.

The expected saving remains fewer redundant same-mark rows, publications
and backward T demands. Above-prefix reads, cuts, fixed targets and protected
results remain. New headers and protection in later runs have a cost. Measure
the net effect; the previous run-1 census does not predict all-run savings.
