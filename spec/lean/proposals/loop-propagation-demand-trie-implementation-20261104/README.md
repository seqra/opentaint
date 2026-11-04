# Loop propagation implementation-proposal proof delta

Status: **IMPLEMENTATION PROPOSAL MODEL ONLY — no Kotlin implementation**.

```sh
python3 spec/lean/proposals/loop-propagation-demand-trie-implementation-20261104/check.py
```

Three small constructive models add obligations not covered by the earlier
20-theorem row/scalar batching and 46-theorem demand-prefix models. They import
only `Std`; those earlier receipts are pinned as related evidence and are
neither rewritten nor rerun.

`ProgramDedup.lean` models exact ordered output union: the first ordinary
payload occurrence owns its position and all finite protection bits are ORed.
It proves identical output streams idempotent and stable output-program
deduplication exact, even with intervening programs and protection upgrades.
Eligibility is applied to whole rows **before** deduplication. Program identity
must represent the entire remaining pure output operation in a fixed query
context. Distinct programs that emit the same ordinary payload can still add
different protection and must remain distinct.

`BoundaryFilter.lean` models typed endpoints and forward/reverse destination
selection. The primary theorem computes a route token before application,
**runs the native application**, and uses the token only in DATA callbacks.
Target, request and static effects retain exact order. A fixed DATA destination
capability proves equality with the existing post-application liveness filter.
Omitting an entire application requires the stronger pure DATA-only capability
and is limited to the already certified observer path. Actual mutable replay
with a dead prepared exit still runs its native callbacks.
The native adapter must preserve the interface's certified directed route list,
including represented repeat/leave routes. Dynamic `ActualStarts` intersection
is a native obligation and is not proved by this generic route model.

`CandidateJoin.lean` proves that an inverse selector preserves the exact
ordered row/input join if it omits only native `None` pairs. It provides no
native index completeness, mutable-state ownership or ND join proof.

See [REPORT.md](REPORT.md) for source/API correspondence obligations and
finite counterexamples. [checks.json](checks.json) records the kernel receipt;
[audit.txt](audit.txt) audits every public model definition and theorem.
