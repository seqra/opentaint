# Proofs for exact DEMAND initials

Date: 31 October 2026. Read the
[design](demand-layer-exact-initials.md) first. This dossier describes the
constructive models and their limits. It does not certify a Kotlin patch.

The [proof package](lean/proposals/demand-layer-exact-initials-20261031/README.md)
contains executable definitions, theorems, audit commands, and an input-hash
receipt. Reproduce it from the repository root:

```sh
python3 spec/lean/proposals/demand-layer-exact-initials-20261031/check.py
```

## 1. Model boundary

The admission kernel uses concrete FULL data marks, equal bases, directed
prefixes, legal exclusions, and positive field budgets. Paths contain the
counted accessors of the scalar model. The runtime adapter must retain JVM
static-anchor validation and accessor counting. No constant-base ingress
or new class-wide concrete mark is permitted.

The models state the new exact cell. Other existing emission cells and
matching policies are not replaced by arbitrary overlap. FLOW normalization
is not selected by this proof set. Existing ZERO permission and starting
policy remain separate parameters.

Ordinary dependent operations join input and operation layers. Existing
independent ZERO GEN can have its own NORMAL proof. The layer theorem is
about a derivation that depends on the uncertain data, not a claim that
every result in a method with any DEMAND input must be DEMAND.

ND projection starts from a complete compatible abstract witness. The
factored proof assumes distinct canonical columns whose compatibility has
already been checked by the rule owner. It does not prove concrete path
feasibility or remove existing alias/control approximations.

## 2. Admission preserves the unchanged guards

In `ExactAdmission`, `ExactDemand.emitted_has_all_guards` and
`ExactDemand.emitted_has_matching_base_mark_and_budgets` prove that a returned seed
has matching base and mark, both paths within the positive budget, legal
exact demand geometry, and an actual location which admits the requested
point.

An actual at an ancestor can supply an exact requested descendant only
when its tail and exclusions admit that descent. A descendant actual does
not supply an exact parent. Different marks, bases, sibling paths, and
exceeded budgets return no seed. An invalid concrete exact demand with a
nonempty exclusion is rejected.

The proof unfolds the guarded emitter. A successful `some seed` branch
contains each Boolean guard. The returned key is the requested exact key,
with an empty exclusion. No existence or matching choice is assumed.

## 3. MAY admission is provisional and demand is not sticky

`may_exact_admission_is_demand` proves that every successful MAY-to-EXACT
admission has DEMAND layer. `demand_actual_starts_demand` covers an exact
actual already in DEMAND. `emitted_key_is_requested_exact` proves that the
geometry remains the requested point.

`guidance_layer_is_not_starting_layer` proves that changing the old demand
row's layer does not change admission. A later exact NORMAL actual emits
a NORMAL seed. Thus the design does not make an old DEMAND guide an
absorbing layer across iterations.

Starting an admitted exact DEMAND key retains DEMAND. Intrinsic STAR/MAY
loss is joined before entry deduplication. Canonical admission does not
invent a NORMAL lane for a key that necessarily starts in DEMAND.

## 4. C5 has a constructive C2 image witness

`ExactDemand.c5_image_iff_c2_emittable` states the exact entry-image invariant
in both directions. The reverse direction is constructive:
`c5ImageWitness` returns the canonical exact actual at the accepted key,
with the accepted layer, and a proof that C2 emits it.

The MAY cell supplies another DEMAND witness for that same key. It does
not enlarge the image to arbitrary overlapping keys. C5 keeps the raw
result layer; `c5_keeps_demand_layer` excludes a DEMAND-to-NORMAL upgrade.
An entry-image rejection cannot create an initial or a fallback query.

The kernel's exit acceptance is an explicit parameter. The unchanged
paired AP/Target intersection supplies it. This theorem does not authorize
mixing permissions from different rows.

## 5. Entry and result lanes do not erase required work

`AdmissionStore` models same-key N and D as distinct memberships. It proves
both arrival orders enqueue their required work, same-layer duplicates do
not enqueue again, and an offer never erases pending work or seen keys.
`AdmissionBounds` gives the finite-key work bound after canonicalization.

The NORMAL-first case is essential. A cached NormalTarget rejects a DEMAND
caller. Dropping the D admission merely because the key was previously
processed in N would remove its DemandTarget continuation. The Target
counterexample proves that the two lanes have different observations.

`ResultLanes` applies the same rule to source-rule output bookkeeping.
It also preserves a later protection upgrade within a lane. An old D arm
does not hide later complete N support for the same origin and output.

Layer is not added to InitialAp, ND member identity, or report identity.
Only the admission/result membership includes it.

## 6. Weakening a conjunction loses NORMAL support

`NDProjection.normal_arm_has_whole_support` proves that a projected NORMAL
arm retains every dependency of its complete witness. The companion
normal-cube theorem requires all contributing input layers to be NORMAL.

If two distinct nonzero origins are necessary, either singleton arm drops
a dependency and is DEMAND. The conclusion can still have exact geometry.
A same-origin witness, or one origin with ZERO support, can retain NORMAL.
An all-ZERO arm requires a complete all-ZERO witness. An incomplete binding
emits nothing.

The same projection applies to source data and sink terminals. A weakened
sink emits only DemandTarget. Its physical seed retains every required
condition; it is not replaced by one projected literal.

These theorems close both counterexamples: the source result cannot become
a reusable NORMAL unary record, and a joint sink cannot become independently
applicable unary NormalTargets for two incomplete callers.

## 7. Factored support equals the witness test

`FactoredOrigins` compares eager enumeration of complete origin bindings
with a direct column-membership test. For an existing origin P, every
column must offer P or ZERO. `choose` constructs a compatible full binding
from a successful test. Conversely, each accepted full binding proves all
column tests.

The theorem `eager_iff_factored` proves the Boolean results are equal.
Separate checks prevent inventing an absent origin and construct a genuine
all-ZERO binding. This preserves run-1's no-origin-product design.

For k binary columns, the eager product has `2^k` bindings. The membership
scan budget is `2*k` per tested origin. Both cost equalities are proved.
This is a bound within one compatible header/proof partition. It is not
a whole-analyzer speedup claim or a bound on all predicate proof shapes.

## 8. Target safety uses the existing protocol

`TargetLayers` proves:

- A dependent DEMAND chain remains DEMAND for any finite operation list.
- A DEMAND witness produces DemandTarget and cannot produce a report.
- NormalTarget rejects DEMAND support; it is not downgraded.
- NormalTarget is ignored backward.
- A final normal report requires the existing ZERO origin.
- DEMAND summaries do not enter the NORMAL native-record candidate set.
- Admission alone creates no source permission.
- A real reverse action retains its real action identity.
- Data admission does not construct ZERO or open a ZERO-only call.

Cached application keeps the actual offered facts and existing support
joins. Well-formed MAY facts already carry DEMAND. The caller safety proof
does not require a new callee seed before persisted replay, and does not
change the persisted-summary-before-C2 policy.

The unchanged stable-ID registry, paired Target C5, counted delivery,
retained NORMAL deduplication, and lazy static completion remain runtime
adapters. No new terminal service or Target-as-AP representation is used.

## 9. Required positive and negative pipeline

`Pipeline` models the source rule with two required marks, a good call,
an incomplete call, physical sink seeds, field-cut MAY input, layered C2,
actual reverse source actions, and later same-call ND binding.

Run-1's weakened source and sink arms are DEMAND. Run-2 admits the good
MAY return query as an exact DEMAND initial. The independent uncut bad
sink query can admit the same key in NORMAL. Both lanes remain available.
Reverse requirements are mapped through their caller bindings; source
permissions come from executed reverse actions. Run-3 materializes definite
source facts only with the required permissions, admits them in NORMAL,
and keeps the complete ND input relation.

The executable good-call control yields its normal report by run-3. The
incomplete and crossed-call controls do not. This is a finite semantic
model result. It is not a claim that a new Kotlin implementation ran, that
the driver stops at run-3, or that all concrete Java programs are covered.

## 10. Non-convergence is a proved limit

`IntrinsicMayCycle` constructs an intrinsic MAY pass which never gains
information from a larger field budget. Its exact admission stays DEMAND,
its target stays anonymous DEMAND, and it has no normal report.

The compressed forward/backward round retains the same explicit guidance.
The saved NORMAL source is replayed before C2; no nonexistent source guide
or source callback is fabricated. An induction over any positive growing
budget schedule repeats the frontier.

Every modeled local round has finite work. The driver can nevertheless
continue indefinitely without its existing budget/policy limit. Thus no
general cross-iteration termination theorem follows from the proposal.
Stopping on equal counts or promoting a provisional exact result would
require a separate selected rule.

## 11. Required runtime validation

The models are constructive: no classical choice, custom axiom, `sorry`,
`unsafe`, `partial`, or noncomputable definition is allowed. The checker
audits all public declarations, restricts kernel axioms, and binds the
specification, this dossier, models, and checker inputs by hash.

After implementation, runtime tests must validate the descriptor's full
delivery path, caller matching, mode/static policy, source/sink seeds,
origin-domain projection, ordinary transfer layer joins, and final report
barriers. The current runtime still has the recorded split-NORMAL false
positive; the new design has not been applied.

Do not treat a kernel PASS as runtime verification, project no-FN, or
convergence proof. The selected concrete-mark scope and unchanged FLOW
rules must remain visible in the implementation proposal.
