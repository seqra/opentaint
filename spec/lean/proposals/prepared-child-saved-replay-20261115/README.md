# Existing prepared children for owned saved replay

Constructive package for the
[proposal](../../../../docs/design/bidirectional-prepared-child-saved-replay-20261115.md)
and [report](../../../../docs/reports/bidirectional-prepared-child-saved-replay-20261115.md).
Production is unchanged.

This candidate adds no query, initial origin, field budget, persistent trie
or caller input. It routes one supported coarse saved-NORMAL result through
the complete child family already prepared by the old C2 plan. It reuses the
old C5, global/relative cuts, reply canonicalization and Target kernel.

| Source | Obligation |
| --- | --- |
| `RoutedCalls.lean` | Executable reference; unchanged old C2/C5 and original offer; routing changes no surviving result and adds no fixed-offer saved contribution |
| `ChildCover.lean` | Concrete positive prefix transport; every successful reader input belongs to its first child; exact endpoint plus nonempty remainder cover any reader length; same paired output selector retained |
| `Compatibility.lean` | Old entry families, MUST/concrete/protected/current-direction fallbacks, over-budget fallback, fixed-offer postprocessing bound and earlier selected cleaner/coverage results |
| `CertificateNested.lean` | Complete cold nested counterexample; natural run-9 completion |
| `CertificatePrefixPostfix.lean` | Ordinary read/call/write wrapper; natural run-11 completion |
| `CertificateRoundTrip.lean` | Write/read round trip before call; natural run-9 completion |
| `CertificatePostfix.lean` | Post-call write; natural run-13 completion |
| `CertificateDouble.lean` | Two inner calls; natural run-15 completion |
| `CertificatePrefix.lean` | Negative read-only-g case; no final observation; backward producer rejection is recorded where expected |
| `CertificateOldMethod.lean`, `CertificateOldBB.lean` | Old positive method and inner-block references; natural run-5 completion |
| `CertificateLongReader.lean` | Longer reader; natural run-5 completion |
| `CertificateOrdinaryTwo.lean` | Uniform-root two-field reference; natural run-3 completion |
| `CertificateGrowth.lean` | Old/new complete-state equality through run-11, not only a count comparison |

Each cold certificate checks whole method domains, current NORMAL/DEMAND
rows, all outer reply packets, another quiescent round, handoffs and retained
NORMAL records. Positive references check backward permission at the actual
uniform producer. The negative fixture records expected permission failure;
it does not claim a real path or a native termination iteration for it.
Final checks include DATA and Target demand plus the expected report identity.

The new reader-cover proof is for positive unary prefix relations. The
existing native child-service contract still needs an adapter for aliases,
ports, ND and configured rule processing. Such an adapter must preserve the
same complete original paired row. Unsupported contributions remain enabled.
No new native whole-core correspondence or universal termination is claimed.

Run against a **fresh external directory**:

```bash
python spec/lean/proposals/prepared-child-saved-replay-20261115/check.py \
  --out /absolute/external/fresh-proof-directory
```

Latest full result: **368 new theorems, 910 audited declarations, 46 modules**.

The checker rebuilds the earlier counterexample and old acceptance packages,
then audits every new theorem. Only `propext` and `Quot.sound` are permitted;
no custom axiom, classical choice, admitted claim or native proof shortcut.
The bulk receipt/log/compiled output is outside the repo, under external
`docs/reports/data/prepared-child-saved-replay-20261115/proofs-v3/`.

Python freezes executable witnesses but is not trusted by Lean:

```bash
python scripts/demand_experiments/operation-local-refinement/capture_prepared.py \
  --out /absolute/external/reference \
  --lean-dir spec/lean/proposals/prepared-child-saved-replay-20261115
```

Two 600-program screens and the growth regression are diagnostics, not
termination proofs. The largest total summary-membership ratio is 1.036 in
the post-read screen; the growth case itself exactly matches the old state.
Latest positive checked completion is run-15; screening reaches run-21.
No new project or integrated native experiment was run.
