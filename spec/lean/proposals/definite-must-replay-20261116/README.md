# Definite native MUST replay

Follow [proof-guide.md](../../../proof-guide.md).
The [consolidated proposal](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md#definite-native-must-replay)
defines the selected contract. Production is unchanged.

**Major semantic change:** a saved native MUST premise uses the existing
definite input lane only, as a current MUST summary does. Omit the residual
overlap lane before any return continuation. Do this for concrete and FLOW
MUST records. Preserve non-MUST reads and native opposite-direction views.
Keep C2/C5, cuts, fields, E/mx/H, complete ND bindings, records and Targets.
Ordinary demand admission still runs after saved replay. Add no fallback
query or full suffix evidence.

```text
actual p.f.MUST/T,N + saved p.MUST/T -> ret.MUST/U,N:
    before: ret.MUST/U,D
    now:    no reply from this record

same actual + saved p.f.MUST/T -> ret.f.MUST/U,N:
    before and now: ret.f.MUST/U,N
```

The new rule does not use a replacement reply or a confirmed report as its
certificate. The required uniform premise itself lacks support. A child
reply is not turned into a NORMAL root reply, and no Target is canceled.

| Module | Checked result |
|---|---|
| `DefiniteMustReplay` | Literal definite-lane retention, no added lane/output, old NORMAL final DATA preservation, order/idempotence, constructive uniform-region coverage with real E, DEMAND support preservation |
| `StrictExact` | Earlier exact-output case: cold runs 1–4 unchanged, natural stop run-5 with both findings and both NORMAL records; uncapped no revival |
| `StrictUniform` | Earlier uniform-output case: stop run-5, all four scalar NORMAL records and findings retained; uncapped no revival |
| `StrictDifferent` | New different-path case: stop run-5 with all seven NORMAL records and both findings; no replacement required to reject broad guard; no invented root result; uncapped no revival |
| `PriorReplay` | Exact function equality with the earlier multi-owner MUST service, including E; all 18 final frontiers/report sets retained, latest run-15; protected closure already uses uniform support |

The earlier 18 cold certificates are source-hash-checked dependencies. Their
service was already strict, so the bridge establishes identical evaluation,
not only equal final counts. The standalone selected cleaner has no saved
MUST replay step and keeps its run-1 proof. The protected closure keeps its
existing definite read and run-3 result.

**64 new constructive claims; 2,395 audited claims across 121 modules.** Only
`propext` and `Quot.sound` are allowed. No custom assumptions, holes, classical
choice or external decision oracle is used.

Seven new native adapter tests pass, including 56 saved/current matching
cells, real E, literal protection, actual DEMAND, a genuine caller-side cut,
FLOW MUST and unchanged STAR service. With the existing support and three
raw cycle classes, **24 tests pass**. Raw driver captures still complete
**run-31**, as expected: the adapter does not patch production.

```bash
python3 spec/lean/proposals/definite-must-replay-20261116/check.py \
  --out /tmp/definite-must-replay-proofs
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.DefiniteMustReplayNativeTest
```

`--dependencies DIR` reuses the different-path counterexample proof build
after checking all source hashes. New modules are compiled and axiom-audited
again. Build output and bulk logs stay outside the repository.

The generic results concern the existing definite lane and uniform geometry.
The complete cold results concern the supplied synthetic cases. They do not
establish whole-engine completeness for arbitrary later actual offers,
nonlocal side effects, alias continuations, or global termination. A valid
definite branch retains its native effects; an unsupported branch is not
executed. This declared matching change needs native integration validation
before any stronger claim. No production patch is included.

[Current report, examples and limits](../../../../docs/reports/bidirectional-definite-must-replay-20261116.md).
