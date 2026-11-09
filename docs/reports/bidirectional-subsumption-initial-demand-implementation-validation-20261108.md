# Subsumption and restricted admission without ANY premises: validation

8 November 2026. State: **NATIVE_CHECKS_PASS / PROJECT_ACCEPTANCE_FAIL**.

The selected implementation uses the pinned `52829d5890ec3b3145cc996a1d8162d85cb8ceda`
core. It is in the isolated `task/subsumption-initial-demand-20261108` branch.
The original worktree and withdrawn STAR_OR_ANY prototype remain unchanged.
The final campaign measures runtime 334234c24. Latest reached / committed /
accepted: OWASP run-5 / run-5 / run-5; Conductor run-14 / run-13 / run-13;
Thingsboard run-2 / run-1 / run-1; Stirling run-52 / run-51 / run-51.
See the [final report](bidirectional-subsumption-initial-demand-performance-20261108.md).

## Selected changes

- Keep plain and protected memberships independently in scalar, packed and
  temporary owners, replay, loop completion and complete ND bindings.
- Canonicalize MAY/MUST facts. Use aligned NORMAL FLOW relations to remove
  covered relations, including transitive FLOW-to-concrete coverage.
- Match same-head STAR/MUST overlap. Limit ordinary ancestor STAR inside
  matching to opposite-direction saved records.
- Emit no ANY owned initial. Use one complete C2 command family, its STAR
  FLOW companion and its exact FLOW prefix. Use the same constructive image
  for paired C5 restriction. Keep each pair and its field budget.
- Replace the selected partial STAR cleaner survivor with ANY/DEMAND and
  empty field exclusions. Bypass only the extra loop gate for an effective
  own-ZERO summary.
- Publish and restore the final retained basis. Remove old index keys when
  their last admitted relation is removed.

These are the semantic changes selected by the finalized spec. Ordinary
field transfer, aliases, complete ND conditions, source permissions, Target
identities, static processing, field limits and stop rules keep their contracts.
No new tail, grounding state, StrongQueries route or endpoint completion was added.

## Verification

The constructive package passes **1,245 component declarations**. Its state
is `PASS_LOCAL_COMPONENTS_ONLY`; `allPrincipalProgramsProved=false`. It does
not prove the full Kotlin analyzer or universal convergence.

The final native command passes **2,510 common-core tests and 461 JVM tests**,
with zero failures, errors or skips:

```bash
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  :opentaint-dataflow-core:opentaint-jvm-dataflow:test \
  --offline --no-daemon --max-workers=2 --console=plain
```

The new checks cover both arrival orders, both protection classes, one-packet
canonicalization, FLOW-to-concrete transitivity without an intermediate row,
final publication/index authority, paired C5 outputs, prefix write exclusions,
the selected cleaner finding at run-3, the own-ZERO loop finding at run-5 and
the full Conductor-shaped mapper finding through run-5.

The scalar oracle now follows the selected full admission family. Its FLOW
comparison uses correlated input/output pairs across the relation family.
For explicitly pure FLOW reader methods, it models FLOW-first publication
and scalar FLOW backing. It does not use a production store as its oracle.
Protection delivery has separate finite class/region tests.

## Native trace clarification

In the Conductor-shaped run-5 example, a NORMAL MUST region at `ret.e.h` can
cover the deep-copy MUST descendant before C5. The native retained basis can
therefore omit that branch's demand. The two-pair C5 component test still
requires both per-row outputs when it supplies the candidate directly. The
full driver keeps the required finding; no forced run-5 stop is asserted.

## Limits and remaining work

Optional GROUP mode retains its documented constructive companion-image
limitation. FULL is the project acceptance mode. The GROUP F76 check keeps
its strict finding/exclusion assertions and checks raw admission provenance
with an independent bound FULL-mark witness.

Project measurement and profile review are complete. Three commands time out;
four strict baseline identities remain missing. No OOM occurs. The final
report and linked next proposal record the evidence and unresolved traces.
The campaign reused f945 and ran only OWASP, Conductor, Thingsboard and
Stirling-PDF with the saved FULL/16 GiB settings through `runProjectAnalyzer`.
