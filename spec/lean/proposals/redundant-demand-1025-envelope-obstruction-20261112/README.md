# Current-target NORMAL envelope obstruction

This model concerns OWASP target `1025a197…`, native row `95b0a29e…`, at the run-11 handoff. The selected demand is:

```text
ret.[any]/FLOW -> arg(1).bytes.*/FLOW
```

The native source-pinned probe admits this hypothetical relation through C2 and paired C5:

```text
ret.f.*/FLOW -> arg(1).bytes.g.*/FLOW, NORMAL
```

The probe imports all 31 scalar NORMAL records (16 stored packets) at this owner. It uses their direct or opposite-direction read role. On `ret.f.*/FLOW, NORMAL`, 14 views match. Eleven produce NORMAL results, with these six distinct field paths:

```text
f, [].f, <string-bytes>.f, <string-bytes>.[].f,
bytes.f, bytes.[].f
```

The other three results are DEMAND. The root and `bytes` MAY results geometrically cover `bytes.g`, but neither is a NORMAL cover.

`no_normal_prefix_cover` proves that none of the six NORMAL paths is a prefix of `bytes.g ++ suffix`, for every suffix. Its hypotheses are five computed accessor inequalities. It does not assume a finite field or JVM type universe. The native mapping is `bytes=4`, `[]=11`, `<string-bytes>=0`, `f=12`, `g=16`. All four theorem axiom audits are empty.

This result only rejects a proposed proof that the fixed saved NORMAL basis covers every relation admitted by the demand. It does **not** show that this method can produce the hypothetical relation, establish sink loss, classify this target, or prove anything about all future body behavior.

Native input coordinates, all matching readouts, hashes, and the Lean execution receipt are external:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/
  redundant-demand-rows-20261112/cases/owasp-1025-normal-envelope-obstruction-v1/
```

Check the proof from `spec/lean`:

```bash
lake env lean proposals/redundant-demand-1025-envelope-obstruction-20261112/CurrentNormalEnvelopeObstruction.lean
```
