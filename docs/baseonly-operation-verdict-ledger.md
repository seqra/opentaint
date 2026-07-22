# BaseOnly operation verdict ledger

Status: release-mitigation evidence ledger.

Verdicts use the release-review scale:

1. **Perfect design and implementation**: normative contract, shared primitive,
   implementation, law tests, Tree differential tests, and regressions agree.
2. **Specification needs correction or generalization.**
3. **Specification is sufficient, but implementation/evidence is incomplete.**

Tree conformance means that every Tree-readable result remains readable after
BaseOnly projection. BaseOnly-only behavior must follow a named widening in
[`baseonly-access-domain-spec.md`](baseonly-access-domain-spec.md). Example pins
are regression evidence, not specifications.

## Evidence matrix

| Operation family | Normative contract | Shared production primitive | Implementation | Law/regression evidence | Tree differential evidence | Verdict and remaining gap |
|---|---|---|---|---|---|---|
| codec and validity | access spec §3.3–3.4 | validated codec (required) | `BaseOnlyAccess.kt` uses 16 static bits, 24 structural bits, and a 23-bit suffix value plus one value-accessor-state bit; invalid ranges and `Value` on a non-semantic suffix are rejected | packing/range/canonical tests | serialization differential scenario | **3**: encoded range and state are validated, but raw packed values remain constructible |
| projection and canonical construction | access spec §3, §5.1 | `build`/canonical projection | `BaseOnlyAccessOps.build` validates wrapper grammar and emits `Normal` for `M`/`T`, `Value` for `V M`/`G T`; unions retain two facts | malformed-order, two-state construction, canonical-boundary, and composite-suffix tests | value-accessor-state combined scenario required by Tree conformance §4.8 | **3**: implementation follows the compact state model; an independent bounded reference projector remains incomplete |
| abstraction construction | access spec §3.2, §5.2 | `abstractAt` | abstraction position is range-validated and canonically packed | abstraction enumeration in `BaseOnlyContainsTableTest` | abstraction/rebase scenario | **1** for the current encoded position API |
| prepend | access spec §5.3 | `prepend` + canonical construction | wrapper prepend validates the semantic category and sets `Value`; structural/static prepend preserves state | prepend/state cases in `BaseOnlyAccessTest`/`BaseOnlyFactOpsTest` | prepend/read and compact-state scenarios | **1** for represented accessor kinds and state |
| logical read/start | access spec §4.1 | shared logical head transition | `BaseOnlyAccessOps.read`/`startsWith` dispatch by state; wrapper read produces a `Normal` residual | normal/value operation cases and Any truth tables | merged-Tree compact-state scenario plus Any scenarios | **1** for the canonical logical domain |
| start-accessor view | access spec §4.2; Tree conformance §2 | shared logical view (required) | `BaseOnlyAccessView.startAccessors` exposes the root selected by the fact's state | compact terminal operation tests | merged-Tree compact-state and existing Tree accessor-view scenarios | **3**: behavior conforms, but terminal-path decisions are not yet delegated to one shared logical-graph view |
| all-accessor view | access spec §4.3 | shared logical view (required) | `BaseOnlyAccessView.allAccessors` excludes Any and includes the wrapper only for `Value` | compact terminal and Any operation tests | merged-Tree compact-state and existing Tree accessor-view scenarios | **3**: behavior conforms, but terminal-path decisions are not yet delegated to one shared logical-graph view |
| head, size, depth | access spec §4.4 | packed retention metric | size/depth count occupied concrete slots and remain at most three | size bounds and type-info cases | Tree metric is intentionally not the contract | **1** for the reviewed compact metric |
| clear | access spec §8 | `removeBranches`/least survivor cover | `BaseOnlyAccessOps.clear` retains a root compact terminal when its implicit Any branch survives | exhaustive clear/state tables and 39-case path-sampling A/B | Tree mutation traces remain reachable | **1**; the proposed whole-fact clear was proven underapproximating |
| exact equality | access spec §6.1, §11 | canonical equality under the single-manager invariant | equality includes value-accessor state but not manager identity | fact/delta/state tests | contains/equal and state scenarios | **1** |
| directional coverage | access spec §6.2 | `covers` | `BaseOnlyAccessOps.covers` requires equal value-accessor state for semantic suffixes | reflexivity/transitivity generator includes `Normal` and `Value` | merged-Tree compact-state and storage scenarios | **1** |
| projected final contains | access spec §6.2 | `containsProjected` | `BaseOnlyAccessOps.containsAccess`; base exact under the single-manager invariant, missing structural slot compatible, value-accessor state exact | contains pins and split-delta alignment tables | merged Tree union contains the separate `Normal` and `Value` projections; Stirling regressions | **1** |
| symmetric overlap | access spec §6.3 | `mayOverlap` | `BaseOnlyAccessOps.mayOverlap` requires equal value-accessor state for semantic suffixes | reflexivity/symmetry generator includes every state pair | storage differential scenarios | **1** |
| canonical join reference | access spec §3.1, §6.3 | test-only `canonicalJoin` | equal semantic suffixes with different states remain two facts; other differences widen at the earliest position | relation and differential evidence | Tree union of `Normal` and `Value` paths projects to two facts | **1** as an oracle; no production operation exists |
| final delta | access spec §7.1 | logical residual (required) | base check plus `matchPrefix`; `applyExclusions` retains a cover behind implicit Any | delta/state tests and Stirling regression | delta/concat plus value-accessor-state scenario §4.8 | **3**: state is preserved, but residual remains implemented by packed-prefix cases rather than one general primitive |
| final concat/graft | access spec §5.4, §7.3 | graft + canonicalize | graft/append carry the terminal-contributing operand's state; when two structural steps compete for one field slot, the outer step is retained and an incoming semantic terminal survives behind the implicit structural tail; joins retain different states as separate facts | append/checker tests | merged-Tree two-fact delta/concat, ordinary delta/concat, 101 reference-installation/mutation/transfer dataflow cases, and extra-structural graft scenarios | **1** for canonical single-state operands |
| initial split-delta | access spec §7.2 | logical residual (required) | split/drop-prefix preserve state | split alignment/state tables; Stirling regression | split/concat plus state scenario | **3**: state is preserved, but representation-shape branches remain instead of a general residual primitive |
| initial/delta concat | access spec §7.3 | graft + canonicalize | shared append/graft preserve state under the single-manager invariant | delta/concat/state tests and pins | split-delta/concat plus state scenario | **3**: sampled reconstruction passes; bounded exhaustive associativity/reference-language evidence remains incomplete |
| exclusions | access spec §8 | shared logical start-branch exclusion (required) | `applyExclusions` rejects Universe and retains the compact cover when a terminal survives behind implicit Any | compact mark/type/mode and Universe regressions | merged-Tree branch-subtraction plus delta/split/filter scenarios | **1** |
| fact filter | access spec §9 | logical branch filter | `filterAccess` evaluates the complete path selected by each fact's state | compact-state and fact operation tests | filter and state scenarios | **3**: compact terminal paths are handled exactly; unrelated projected antichain merging remains a limitation |
| compatibility filter and checked concat | access spec §9 | direct-abstract-edge compatibility check; checked graft | concrete facts and abstract ancestors bypass the checker; the direct predecessor of abstraction is checked; checked graft remains separate | checker rejection in `BaseOnlyDeltaTest`; concrete/direct/ancestor compatibility assertions in differential test | filter differential scenario; delta+concat scenario | **3**: fact filtering retains the merged-branch limitation, and checked concat still needs a shared Tree-equivalent compatibility primitive |
| `abstractOnly` | access spec §10 | slot-preserving abstraction | existing static/field AP stays in place; other facts become suffix-abstract | abstraction/rebase scenario | Tree root has no fully specified BaseOnly representation | **2**: restored behavior is pinned, but the general Tree-relative spec remains open |
| remove abstraction | access spec §10 | abstraction-state operation | `collapse` suppresses suffix acceptance as a transient final-fact state; unrepresentable terminating prefixes widen at the later abstraction position | abstraction lifecycle and collapsed-state tests | abstraction/rebase scenario | **1** for the single-state BaseOnly domain |
| rebase | access spec §10 | base substitution plus completion of the transient remove/rebase lifecycle | stable accesses are unchanged; transient collapsed suffix is restored | abstraction lifecycle and collapsed-state rejection regressions | abstraction/rebase scenario | **1** |
| factories and manager invariant | access spec §11 | validated fact construction | fact constructors reject noncanonical states; composition/equality assume one manager and do not hash manager identity | `BaseOnlyManagerTest`, canonical rejection and operation tests | construction/equality scenarios | **1** |
| rendering | access spec §12 | logical graph renderer | manager renderer | pins expose rendered operation matrices | indirectly exercised by failures only | **3**: `Normal`/`Value` state, static/field AP distinctions, and virtual branches are not yet guaranteed distinct and uniquely parseable |
| serialization | access spec §12 | compact logical payload | three tagged slots plus value-accessor state, with no magic/header/version; current 23-bit suffix range and collapsed-state rejection are enforced | both-state round trips, packed-range, and collapsed-state regressions | serialization/state scenarios | **1** |

## Combined-scenario coverage

The checked-in `BaseOnlyTreeDifferentialOperationsTest` covers:

- construction with two fields, then read through the discarded inner field;
- prepend + startsWith + read + start/all accessor views;
- Tree Any start-view versus all-view asymmetry;
- type-info logical views;
- a merged Tree containing `Normal` and `Value` semantic branches,
  projected to two facts, then read, viewed, cleared, excluded, contained, joined,
  formed into a delta, and concatenated;
- final delta + checked concat;
- initial split-delta + concat reconstruction;
- final containment, cross-kind equality, and exact initial containment;
- clear + surviving path language;
- fact and compatibility filters over a two-branch Tree and projected BaseOnly
  antichain;
- abstractOnly + rebase;
- final and initial serialization followed by path-language comparison.

## Current operation release gate

Verdict (1) is reached for abstraction construction, prepend, logical reads,
clear, equality, coverage/containment/overlap, the test-reference canonical join, final
graft/concat, remove/rebase, construction and ownership, and
serialization. Accessor views and exclusions are semantically conformant but
remain verdict (3) until their terminal-path decisions use the required shared
logical-graph/removal primitives. None of the remaining gaps requires weakening
or special-casing the normative specification.

The most important remaining operation work is:

1. a validated canonical codec API instead of public raw packed values;
2. one shared logical-path/value-accessor-state view used by accessor views,
   exclusions, filtering, metrics, and rendering;
3. one general residual implementation shared by final delta and initial
   split-delta;
4. branch-aware filtering/projection for merged logical branches;
5. a precise BaseOnly representation/specification for Tree's abstract root;
6. an unambiguous logical renderer backed by round-trip tests.
