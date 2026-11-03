# Post-join execution-root release

Status: **DRAFT / UNSELECTED — constructive lifecycle model**.
Read the [proposal](PROPOSAL.md) and [proof guide](../../../proof-guide.md).

```sh
python3 spec/lean/proposals/post-join-execution-root-release-20261103/check.py
```

Opaque typed J contains the complete immutable read footprint of joined static
binding; X contains only candidate execution roots; S contains completed
snapshots. Under the explicit J-only binder prerequisite, old and detached paths
produce the same final state/output/publication. Work, local publication and
delivery are closed after join. Early detach requires completed snapshots;
failures export no new result; final cleanup is idempotent. Arbitrary projections
of retained J and S remain unchanged, including raw IDs, owners, ports and marks.

Kotlin read-footprint, concurrency, canonical identity, native-adapter and garbage
collector equivalence are not proved. The retained-alias witness prevents a false
freed-byte claim. No AP interner, IR or rewrite SoftManager clearing is proposed.
No runtime code, native test, analyzer, MAT or JFR execution is included.
