# Kernels for the next summary-work proposal

These models support [Reduce repeated summary work](../../../../docs/design/bidirectional-summary-work-next-iteration-20261030.md).
They do not change the runtime at `e090118e5f9603f1973c0578a3e04998035f4508`.
The current project labels are OWASP run-5/5/5, conductor run-4/3/3,
thingsboard run-2/1/1 and Stirling-PDF run-7/6/5 (reached/complete/accepted).

```sh
python3 spec/lean/proposals/summary-work-next-20261030/check.py
```

The checker pins Lean 4.33.1, one worker and CPU, 768 MiB, and 90 seconds per
command. It compiles every module and audits all public definitions and
named theorems. There are **47 named theorems and 99 audited declarations**.
Only `propext` and `Quot.sound` are allowed. There is no choice, custom axiom,
proof hole or noncomputable source. Logs use ignored spec/lean/.lake/verification.
The receipt binds model, checker, proposal and reviewed runtime source hashes.

| Model | Named theorems | Scope |
|---|---:|---|
| ReturnImageBatch | 18 | Complete context and ordinary-image signatures; exact protection-coordinate union; distinct keys; N images to K suffix calls |
| UniversalRootMatch | 12 | Canonical FULL universal-root selection; original header, ordinary and protection memberships; negative concrete-mark selection |
| JoinedWriterSelection | 6 | Selection independent of destination; writer-first/input-first output membership; late writer append; W*N versus N queries |
| InheritedCoverPrune | 11 | Folded coordinates covered by inherited payload have no residual; future cover only grows; separate protection pass; warm-fold node-visit saving |

ReturnScope contains full caller context, statement, stage, original and result
premises, caller layer, identity state and pending native demotion. FactsHeader
contains kind, layer, base, tail, E and mark exclusions. Token equality in these
models stands for complete canonical runtime identity, not AP prefix coverage.

The writer model uses a fixed joined input snapshot. It does not justify a
completed-query cache: late destinations must still run. Writer batching changes
output order from writer-first to selected-input-first. Prove that the mutable
queue and observation adapters preserve the completed closure. The matcher kernel
models only the selected universal FULL case; GROUP projection and arbitrary
AP selection remain outside that theorem. The pruning kernel uses concrete
finite marked coordinates and inherited-cover monotonicity. It does not verify
the generic Kotlin algebra, cached DAG traversal or its cancellation protocol.
The node-visit saving assumes a warm valid fold; a cold fold costs work itself.

Image compaction preserves ordinary/protection membership union. It assumes
no theorem about arbitrary stateful suffix callbacks. Kotlin source/ND/alias
adapters, complete rule observations and delivery/fixed-point behavior must be
checked before implementation. No whole-project speedup or finding-completeness
claim follows from these kernels. The proposal lists those remaining gates.

All seven supplemental production-AP controls passed after the project commands
closed: one return-image control, three universal-match controls and three
inherited-cover controls. A full rerun passed 2,133 core tests and 452 JVM tests.
These controls use the existing AP implementation; the proposed runtime
optimizations are not installed. They do not discharge the remaining queue,
suffix, observation, cache or DAG adapter obligations.

The [portable pruning control](controls/README.md) contains the same test-source
bytes as the passing external control. Its init script adds only that source
to the core test project. The portable init was not executed during packaging.
The proposal and control README give the exact scope and execution command.
