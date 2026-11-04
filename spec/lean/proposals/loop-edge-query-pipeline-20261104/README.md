# Output-side loop-query row/scalar factorization

Status: **PROPOSAL MODEL ONLY — no Kotlin implementation**.

```sh
python3 spec/lean/proposals/loop-edge-query-pipeline-20261104/check.py
```

The finite model proves an ordered row/scalar join reorganization. `select`
is an opaque native cell operation from one **whole paired row** and one
scalar to an optional part. `packCut` is an arbitrary function of that same
row and its complete input-ordered part list. It is called once per eligible
row. No property of AP transfer, normalization, merging, field cuts or mark
protection is assumed. In particular, no limit-distributes-over-leaves law
is used.

The reference runs row-major `filterMap`. The factorization builds scalar
columns, masks only provably empty cells, regroups their parts into positional
row buckets, and applies the same `packCut` in the original row order. The
resulting list is identical, before any downstream ordered union. Filtering
entry-rejected whole rows is also exact; rejected rows never call `packCut`,
even if `packCut row []` would produce a result. Equal payloads with distinct
raw/ND ordinals remain separate rows.

`leafMajor` is a simple dense reference transpose, **not a claimed sparse
Kotlin implementation**. Candidate completeness states exactly that a false
candidate cell has native selection `none`; it permits false positives.
The executable posting model filters owner postings by the entry mask and
proves `k ≤ N` for each lookup and their finite sum. It counts output postings,
not total time: index construction, path-node traversal, stable-order recovery,
native matching, packing/cutting and output width remain separate costs.
Both counts use the same row/member-ordinal occurrence universe. A plan can
contain several ND ordinals for one raw owner ID, so `k ≤ N` must not be read
as a bound against the number of distinct method-wide raw IDs.
All-eligible and strict-improvement examples make the absence of a universal
speedup explicit.

Read [REPORT.md](REPORT.md) for the proved scope, finite regression witnesses,
source pins and prerequisites for a native sparse adapter. The checked receipt
is [checks.json](checks.json); [audit.txt](audit.txt) contains the kernel axiom
audit for every explicit public definition and theorem.
