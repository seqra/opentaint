# Retire source-safe FLOW demand with NORMAL replay

11 November 2026. This is a campaign predicate proposal. It changes no
production code. Reference: `14d7b63369d94f49d4c551be8405ed7719f267cc`.
Original reached / completed / accepted forward runs are OWASP 11/11/11,
Conductor 8/7/7, and Stirling-PDF 11/10/9.

## 1. Scope and selected change

`SourceSafeNormalReplay(X)` extends
[P](normal-backed-flow-demand-retirement.md). It uses P's required concrete
path contract. It does not require equal speculative MAY packets, work counts,
callback order, or provisional false positives.

The selected change removes a plain FLOW demand from the next-run frontier
after the later completed forward run. Run-i and its state stay unchanged.
The first application uses Conductor run-5/run-7 and removes after run-7.

Keep all retained NORMAL records, concrete-mark demand, protected demand,
ND demand, ZERO, Targets, source permissions, rule contributors and reports.
Keep current initial emission, C5, field cuts, layers, matching roles, aliases
and source/cleaner rules. Do not replace method semantics with its saved
NORMAL records. Do not install this predicate in the production analyzer.

Eligible X has one nonstatic DATA premise, STAR/FLOW input, ANY/FLOW output,
empty field exclusions and no protection. The run uses FULL marks and is
restricted, after run-1. Scope is one exact method/context/interface.
The source closure must be finite and acyclic, with every callee resolved.
Unknown scope returns OPEN.

The source adapter permits these operations only:

- Ordinary STAR/FLOW prefix copies, including aliases and bindings.
- Positive unary same-mark sources:
  `CM(this.$,T) OR CM(this.[any],T) -> assign ret.$/T`.
- Selected exact-root Return cleaners.
- Positive unary concrete EXACT sinks with no generated end facts.
- Empty boundary generators and no nonidentity static mutation.

Other rule forms, loops and unknown callees need a new proof. Rejection by
this guard does not show that an edge is necessary.

## 2. Predicate and witnesses

Build a complete paired prefix relation C from actual CFGs and call-stage
DAGs. Compose the actual resolved callee bodies. A row `a -> b` transfers
every common suffix: `a.s/T -> b.s/T`. Preserve bases, full typed field keys,
mark-exclusion masks, context and native direction.

C may be a conservative superset. For example, the sealed first adapter
passes an untouched base through some call stages. Native stage transfer
does not supply that implicit pass. This adds routes to C; it cannot justify
omitting a native route. Check coverage for every added route too. Type and
deleting filters can be omitted only under the same superset rule. Never
describe this relation as an exact native execution trace.

Clip C to X's paired input and output regions. For every row R in C(X),
require an independently retained NORMAL STAR/FLOW record N:

1. The exact owner, context, interface and endpoint bases match.
2. One suffix s gives `R.input = N.input.s` and
   `R.output = N.output.s` in N's native replay view.
3. N excludes no mark that R can transfer: `N.mx` is a subset of `R.mx`.
4. Same-direction replay accepts the offered region: N's input prefix is a
   prefix of X's input prefix. Preserve `SAVED_OPPOSITE` for reverse records.
5. N is persisted NORMAL at the removal barrier, not a raw candidate or a
   proposed future provider.

Also require equal complete C2 entry support before and after the joint
removal. Use actual projected rows and all raw origins. A projected row
disappears only when all its origins retire. Retain an explicit origin
witness for each affected entry. A witness cannot itself retire in this
application or any later application without proof replacement.

```text
sourceSafeReplay(removalSet, completedState, sourceClosure):
    require eligible(removalSet) and supported(sourceClosure)
    C = conservativePairedCopies(sourceClosure)
    for X in removalSet:
        for R in clip(C, X):
            require retainedNativeNormalWitness(R, X, completedState)
    before = projectAllLiveOrigins(completedState)
    after = projectAllLiveOrigins(completedState minus removalSet)
    require fullEntrySupport(before) == fullEntrySupport(after)
    require every entry witness remains outside all cumulative removals
    return certificates for each X, including its origins and dependencies
```

## 3. Why marked behavior stays available

FLOW cannot satisfy a concrete mark check in a restricted run. Empty boundary
GEN and the positive source guards prevent a new FLOW job from generating a
concrete source result or a marked sink witness in this closure.

A same-T source assignment survives as protected output. A surviving selected
cleaner result at the selected base is also protected. Copy transport keeps
the flag. An ordinary pass cannot set the flag. Thus a plain diagonal copy
result has no same-T rule assignment or selected-cleaner survivor in its local
derivation. Cross-mark, protected, EXACT, MUST and ND results are outside
plain FLOW-backed erasure and remain separate.

This provenance statement is local to the current initial. C2 starts a new
local derivation in a callee. Summary application restores caller protection;
do not assume a global ancestry tag inside the callee.

Removing a FLOW entry cannot change C5 results for an original concrete, ND,
ZERO or Target initial: that original cannot be admitted by the FLOW entry.
A concrete entry can admit its own FLOW companion. Keep that asymmetry and
all concrete entries. Equal full C2 support preserves the admitted initial
set for any fixed submitted packet.

The only removed output lane is ordinary copy debt. Complete C(X) coverage
replaces each required copy step with N before demand admission. The suffix,
mark, layer and protection of the represented point stay equal. Source and
sink events keep their action, leaf, rule and location. All premises of a
positive conjunction remain required; this proof never changes AND to OR.

The safety claim is the represented required source-to-sink path contract
of P. It is not a full Kotlin interpreter proof, equal arbitrary AP packets,
or equal driver termination time.

## 4. First principal case

Use e for `java.util.Optional.Element` and i for
`java.lang.Iterable.Element`. They are distinct typed fields.

```text
X:       this.e.i.*/FLOW -> ret.e.e.[any]/FLOW, DEMAND
origin:  this.e.i.s/T    -> ret.e.e.i.s/T
saved N: this.*/FLOW     -> ret.e.*/FLOW, NORMAL, SAVED_DIRECT
suffix:  e.i.s
```

N's input prefix is empty. It accepts the region behind X. Its native record
ID is `10b710bdcc701905b175353b9cfead01ec404024da98928033adac8dc57d858f`.
The source closure has three exact method keys and 30 physical instructions.
All 14 clipped origins for seven targets have NORMAL witnesses.

Five projected rows share the full entry `ret.e.e.[any]/FLOW`. Keep target
`21aded9dbe686cd10f4bb8e3a4a194e5187f4168c5a42fbcc27ba6a97c1231e2`
as their explicit entry witness. The first trial removes four other origins.
Seven local projected rows become three, with identical full entry support.
The other two rows and the witness stay OPEN under this guarded application.

The actual source DAG has a source branch `BOUND -> REWRITTEN` and a cleaner
branch `RETURNED -> REWRITTEN`. Source outputs bypass the cleaner and survive.
No proof here treats these source outputs as dead.

## 5. Proof and acceptance evidence

The generic constructive model has 26 audits. Its finite original-data binding
adds nine audits. The native bridge has eight tests, including 3,807 aligned
replay cells, 54 incoming-mask cells, 30 actual source-bypass cells, reverse
source rejection and protected copy/cut/C5/storage checks in both arrival
orders. These are scoped bridge tests, not an entire project deletion test.

Before acceptance, require independent review of the source adapter and the
native bridge, full per-target certificates, a result for every original
target, and the cumulative dependency audit. A guard failure remains OPEN.
Keep proof components and accepted packages immutable. Keep project replay
or source metadata separate from frozen original AP activity.

Evidence is under
[the Optional candidate](../docs/reports/data/redundant-demand-20261110/cases/optional-source-frame-candidate-v1/README.md)
and its source closure. Acceptance and counts belong to the campaign ledger;
this document alone classifies no target.
