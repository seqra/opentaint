# Nested-write termination counterexample

This dossier follows [proof-guide.md](../../../proof-guide.md).
Read the [self-contained report](../../../../docs/reports/bidirectional-nested-write-nontermination-20261115.md)
for the code, native-form scope, cold annotations and arbitrary later trace.

The only new formal transfer is the explicit existing native parallel
`strongKeep` for a nested ordinary write. Production is unchanged. C2/C5,
FLOW normalization, real exclusions, current/saved application, original
caller delivery and ZERO/Target rules keep their selected contracts.

Scope: fully analyzed synthetic nested-write **core forms**, unary FLOW
return cone and concrete marked outer packets. No loop, recursion, cleaner,
pass rule, unresolved transfer or intrinsic MAY producer. This is not a
Java-front-end or whole-production simulation result. The readable Java
notation compiles, but the JVM adapter's local-write lowering is not modeled
by the atomic nested write of this fixture.

Latest finite reference: **run-61**. Lean checks full cold states through
**run-11**, their independent fixed points and handoffs. It separately proves
a two-phase demand recurrence for arbitrary later runs with increasing field
limits, and guided ZERO/Target continuation. The proof uses no iteration cap.

Final audit: **90 new theorems, 1,487 audited declarations, 85 modules**.

| Module | Checked obligation |
|---|---|
| `NestedWriteReplay` | Ordinary write/read form execution, native exclusions, existing C2/C5 and outer saved-first service |
| `NestedWriteCold` | Empty start; every reference domain, publication, actual packet, quiescent state and handoff through run-11 |
| `NestedWriteBodies` | Every mature raw query/branch result remains the same at arbitrary later limits |
| `NestedWriteStable` | Complete mature C2 and C5 packet recurrence, arbitrary incoming-row advance, retained NORMAL provenance |
| `NestedWriteConcrete` | All concrete g paths are killed/rejected; EXACT-origin MAY survives any child mask and NORMAL precoverage |
| `NestedWriteControl` | Actual marked caller packets; producer permission; ZERO/Target C5 and handoff; uncapped continuation |

Run from the repository root:

```bash
python3 spec/lean/proposals/nested-write-cycle-20261115/check.py \
  --out /tmp/nested-write-proofs
```

The checker first rebuilds every dependency, then checks every declaration's
axioms. It rejects placeholders, classical choice, custom assumptions and
external decision oracles. Only `propext` and `Quot.sound` are permitted.
`--reuse-dependencies` is for a just-completed dependency rebuild; it verifies
all receipt hashes and compiled files before checking this package.

Freeze cold witness data with:

```bash
python3 scripts/demand_experiments/exclusion-counterexample/capture.py \
  --out /tmp/nested-write-data --lean-dir /tmp/nested-write-cold
```

Large data, `.olean` files and build logs stay outside the repository.
The native component test is `NestedWriteCycleComponentsTest` (4 checks).
