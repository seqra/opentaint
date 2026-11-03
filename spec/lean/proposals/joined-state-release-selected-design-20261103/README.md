# Selected joined-state release design model

Status: **SELECTED DESIGN; NOT IMPLEMENTED**.

The user selected point 1 of the next-iteration proposal. The detailed
contract is [the design document](../../../../docs/design/bidirectional-joined-state-release-design-20261103.md).
The model is [JoinedStateRelease.lean](JoinedStateRelease.lean).

Run `python3 check.py`. The checker uses Lean 4.33.1, one CPU, one worker,
and a 768 MiB compiler limit. It compiles the executable definitions, audits
every explicit public definition/theorem, checks immutable reference source
hashes, and authenticates the design, model, guides, and checker inputs.
Only `propext` and `Quot.sound` may appear in the audit. No classical choice,
admitted proof, unsafe command, or native proof shortcut is allowed.

The first namespace preserves the prior 35 conditional lifecycle laws.
The second namespace refines the selected design with finite state,
pending work, exact scoped local/physical input reads, ordered binding
enumeration, complete driver exports, ownership transfer, and cleanup.

The Kotlin AP matcher remains a parameter. Sealing must leave that matcher
and all input values unchanged. The model does not introduce a second
static binding algorithm. It does not model the JVM heap or prove that a
Kotlin closure is detached. The finite alias witnesses show why a separate
native read-footprint and retention test is required.

Native tests, implementation, project runs, and commits are outside this
design task. See [REPORT.md](REPORT.md) for the exact proof scope and
remaining adapter obligations.
