# Loop fragments and demand collapse: local models

Date: 2 November 2026. Selected design; no runtime implementation.

Read [the spec](../../../loop-fragments-and-demand-collapse.md),
[method-owned blocks](../../../method-owned-loop-blocks.md),
[the proof dossier](../../../loop-fragments-and-demand-collapse-proofs.md),
and [the proof guide](../../../proof-guide.md).

```sh
python3 spec/lean/proposals/loop-fragments-and-demand-collapse-20261102/check.py
```

The checker uses pinned Lean `leanprover/lean4:v4.33.1`, one worker and
one CPU. Its memory limit is 768 MiB for the structural modules and
2,048 MiB for Admission and the combined audit. It audits every explicit
public definition and theorem. It permits only `propext` and `Quot.sound`
and rejects classical choice, unproved declarations, unsafe/partial or
noncomputable source and native evaluation proofs.

| Module | Scope |
|---|---|
| Control | Exact labelled CFG routing, feedback ports, self loops and supplied acyclic-body certificates |
| Geometry | Bounded scalar prefix projection, coverage, metadata and finite-image/work witnesses |
| Admission | Stated finite concrete C2 cells and rejected forced-MAY counterexample |
| Guidance | Unary ND restriction metadata; unchanged complete AND execution |
| Shape | Strict summary growth, `FL(Zero)=0`, equal/shrinking bypass and exact-suffix bounds |
| Protocol | Whole original, port/context, producer effects and separate complete-row publication |
| Restriction | Fixed complete AL/B/L observer, finite shortest-safe-cut reference and image preservation |
| Feedback | Missing internal consumer under AL/B-only gate; selected L check preserves the example |
| Blocks | One method owner, shared registers, separate post-S stores, repeat/leave gates, parent dependencies and local frontier collection |
| Usefulness | Reference investigation only; no runtime NORMAL reachability service is selected |

The [native control record](controls.md) embeds the code and traces for the
next-body case. Its finite FULL driver control completes **run-3**, with
one report. Native controls are separate from the kernel proof receipt.

The [receipt](checks.json) hashes the exact inputs and records kernel and
audit results. A local-model PASS is not a proof of Kotlin block decomposition,
all AP application/projection adapters, whole-driver convergence or a
project speedup. The dossier lists the correspondence checks required
before implementation. No new runtime service or AP semantic exception
is implied by a local model.
