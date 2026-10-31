# Target, constant-filter, and concrete admission validation

Date: 31 October 2026. This report describes the implemented iteration.
The worktree base is `79775235e99583878c17f4fd88d2f7e09ea3c3ac`.
The implementation commit will include this report. Project measurements
must use that commit; no project campaign result is claimed here.

The [implementation proposal](../design/bidirectional-constant-filter-target-zero-implementation-v2-20261031.md)
includes the [concrete exact-DEMAND amendment](../../spec/demand-layer-exact-initials.md).
The earlier split-NORMAL false positive is fixed. The valid conditional
source reports by **run-3**; its incomplete caller stays negative.
DLINK now retains provisional guidance at run-3 and proves its finding
at **run-5**. The old stop at run-3 lost this real descendant flow.

## Checks

| Check | Result |
|---|---|
| Complete common-core suite | 2,207 tests; no failures, errors, or skips |
| Complete JVM dataflow suite | 452 tests; no failures, errors, or skips |
| Benchmark/report scripts | 39 tests pass |
| Retained and historical constructive models | 16 modules, 293 theorems, 543 audited declarations |
| Exact-DEMAND constructive models | 11 modules, 159 theorems, 280 audited declarations |
| Source review | No additional semantic change found in the reviewed amendment paths |
| Patch whitespace | Pass |

The final combined command runs from `core`:

```sh
JAVA_HOME=/usr/lib/jvm/temurin-17-jdk-amd64 ./gradlew \
  :opentaint-dataflow-core:opentaint-dataflow:test \
  :opentaint-dataflow-core:opentaint-jvm-dataflow:test \
  --continue --console=plain --max-workers=2
```

The command passes in 2 minutes 39 seconds. Its log is
`/tmp/bidi-exact-demand-final-validation.log`.
The script checks use `test_compare_bidi_projects.py` (33 tests) and
`test_benchmark_bidi_projects.py` (6 tests). No test was disabled to
obtain the results. Covered GROUP factory and conjunction controls pass;
FULL remains the selected project acceptance scope. These controls do
not establish general GROUP correctness.

## Implemented concrete admission rules

```text
exact demand p.$/T + actual p.[any]/T,D -> initial p.$/T,D
exact demand p.f.$/T + actual p.[any]/T,D -> initial p.f.$/T,D
exact demand p.$/T + actual p.$/T,D -> initial p.$/T,D
exact demand p.$/T + actual p.$/T,N -> initial p.$/T,N
```

The last rule can discharge guidance from an older DEMAND edge. The guide
layer is not a permanent lower bound. Wrong marks, bases, sibling paths,
descendant-to-parent offers, invalid exact demand exclusions, and excess
field budgets still fail. Actual exclusions still block descent.

`AdmittedInitial` carries the layer outside InitialAp identity. Caller
lookup, runner messages, run-1 request answers, and actor start retain it.
The actor applies the intrinsic and current run-1 policies before its
seen check. One key has independent NORMAL and DEMAND memberships.
Same-layer repeats start no work. Concrete STAR/N and STAR/D both
canonicalize to the same DEMAND start.

The caller retains actual Facts and replays saved summaries before C2.
The new exact hypothesis does not replace an actual MAY input. FLOW and
ZERO keep their existing emission and starting policies. Target stays
outside the AP domain.

## Complete rule support

```text
complete witness {P/T1,Q/T2}, NORMAL:
  run-1 source: P/T1 -> ret.$/U,D and Q/T2 -> ret.$/U,D
  run-1 sink: P/T1 -> DemandTarget and Q/T2 -> DemandTarget

complete witness from P plus optional ZERO, NORMAL:
  retained P arm can remain NORMAL

no complete witness:
  no arm, including no ZERO shortcut
```

Both factored source stores test whether each required column offers P
or ZERO. They do not enumerate origin products. A new nonzero membership
rechecks that origin. New ZERO membership, changed complete versions, or
protection growth can recheck earlier origins. Result deduplication keeps
separate layer and protection memberships.

The sink owner classifies each projected arm from its complete binding.
It captures the full physical predicate seed before anonymous terminal
deduplication. Later forward runs retain full ND premises and same-call
binding. NormalTarget still requires NORMAL actual, caller, and link
support, and is ignored backward.

## Principal runtime traces

| Control | Latest reached / complete | Result |
|---|---|---|
| FULL conditional source, good and incomplete calls | run-3 / run-3 | Good report present; incomplete call absent |
| Static writer, terminal reader, lazy paired handoff | run-3 / run-3 | Required report present |
| Exact NORMAL saved source through two field writes | run-3 / run-3 | Native replay retains the finding |
| Same source through one field write | run-1 / run-1 | Finding settles without refinement |
| DLINK root-only cleaner and descendant sink | run-5 / run-5 | Required descendant finding present |

DLINK's frontier provides a concrete continuation check:

| Run | AP demand count | Target demand count | Sink/source seed count |
|---|---:|---:|---:|
| run-1 | 3 | 3 | 1 |
| run-2 | 5 | 1 | 0 |
| run-3 | 3 | 3 | 1 |
| run-4 | 4 | 1 | 0 |
| run-5 | 0 | 0 | 0 |

The source taints all descendants. The cleaner removes only the exact
root. The sink checks `g.h` in a throwing helper. Its normal exit stays
unreachable and it has no AP return summary. At run-3 the coarse caller's
admitted point remains DEMAND, so the helper emits DemandTarget and keeps
its physical seed. At run-5 the field path fits; complete NORMAL support
reaches the sink and its NormalTarget reaches root ZERO. The driver then
stops with `NO_DEMAND_EDGE` and one report.

The static route uses the existing lazy composition and full paired C5.
The accepted backward source-summary ZERO result uses DemandTarget under
the original caller premise. Native replay does not create an actual
source callback. Constant packets remain rejected before runtime effects.
No new static service, grounding label, or field-transfer rule was added.

## Proof and measurement limits

Run both checked packages:

```sh
python3 spec/lean/proposals/constant-filter-target-zero-implementation-v2-20261031/check.py
python3 spec/lean/proposals/demand-layer-exact-initials-20261031/check.py
```

Only `propext` and `Quot.sound` are permitted. The maintained receipts bind
model and reviewed source bytes. Historical concrete MAY-rejection laws
are labeled as superseded; they do not certify the new admission rule.
The new kernel proves its concrete scope, constructive C2/C5 image,
layer preservation, separate lanes, factored support, Target safety,
finite pipeline, and incremental candidate selection.

These are model proofs and runtime controls, not whole-project no-FN or
performance proofs. An intrinsic MAY result can reproduce the same
DEMAND frontier at every field budget. No equal-count stop, artificial
NORMAL promotion, or fabricated source hit was added.

The remaining task is to commit this implementation, run the four selected
projects in the configured FULL/16 GB/1,1,2,... configuration, compare to
the saved f945 baseline, inspect profiles and OOM snapshots, and write the
next optimization proposal from those measurements. The earlier project
reports do not measure this implementation.
