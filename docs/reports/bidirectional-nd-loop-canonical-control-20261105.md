# Finite ND loop canonicalization control — no reproduction

Both current production and the verified proper-prefix-off overlay find the expected NORMAL U sink. The feedback case and its acyclic control each reach, complete and accept run 5. This candidate does not reproduce the two missing Conductor findings.

| Native runtime | Feedback | Latest reached / completed / accepted | Result |
|---|---|---|---|
| Current production | Yes | run-5 / run-5 / run-5 | Expected sink found |
| Current production | No | run-5 / run-5 / run-5 | Expected sink found |
| Proper-prefix-off B | Yes | run-5 / run-5 / run-5 | Expected sink found |
| Proper-prefix-off B | No | run-5 / run-5 / run-5 | Expected sink found |

The [portable receipt](data/bidirectional-nd-loop-canonical-control-20261105.json) embeds all 2,290 semantic rows, source, Gradle init, frozen preparation manifests, 1,282 source pins, both resolved classpaths and the first failed build. It passes 33 result checks and a fresh 1,330-input source/class preflight. These are four external native cases; they add no repository regression tests or project benchmark results.

## Code and real rules

```java
s = sourceUniformT();
b0.box0 = s; b1.box1 = b0; b2.box2 = b1;
y = b2.box2.box1.box0;
do {
    if (flag) x = y;
    else { fresh.f = y; x = fresh; }
    u = conditional(x);
} while (again);
sinkU(u);

conditional(p) {
    marker = sourceV();
    // CM(p.f.f.f,T) AND CM(marker,V) assigns U to return.
}
```

All statements use native micro-edges. Both sources are tagged source actions. The U assignment is a real two-leaf source predicate. No summaries, demands, initial facts, source permissions or contributor rows are supplied. The acyclic control removes only the feedback edge. Both JVMs use FULL mode, field limits 1, 1, 2, 3, 4, …, a 20-second driver budget per case, 1 GiB heap and one active CPU. Root ran both commands; the preparing agent launched none.

## Observed lineage

For both runtimes and both CFGs, the conditional U producer is DEMAND in runs 1 and 3, then NORMAL in run 5. Its premises progress from `arg0.STAR/T` to `arg0.f.ANY/T` and then `arg0.f.f.MUST/T`. The first root ZERO-to-NormalTarget is in run 5. The expected source permissions are present in forward runs 3 and 5; the backward runs record hits for T, V and both conditional-source transfers.

A NORMAL `ZERO → marker.$/V` condition contributor is captured in run 1 and is available before runs 2–5. The NORMAL T condition leaf is captured in run 5. The U output proves that the complete native condition executes. The capture does not identify which fresh or restored V event completes that join.

There is no NORMAL saved `ret/U` DATA producer in the relevant pre-run record snapshots. This removes the specific pure-data saved replay bypass that made earlier getter probes weak. Other saved DATA/Target replays are still possible; no application callback trace was installed.

Current and B have equal recorded multisets of C2 queries, saved records, public/scoped summaries and public/scoped Targets. The receipt preserves encounter order separately and makes no order-equivalence claim.

## Limits

No rendered packet in either runtime contains a same-mark, same-tail proper-prefix MAY/MUST pair. This covers captured point, current and saved packets; it does not enumerate private `canonicalSpans` arguments. The candidate did not establish that the discarded-coordinate cell executes. Its PASS therefore does not prove that canonicalization preserves all driver findings.

All 20 callback projections in each runtime report zero whole-row and whole-packet drops. Each projection has an 8,192-row cap and each packet a 256-scalar cap. Saved records are rendered before each native run, while the previous barrier is fixed. Scope queries cover relevant finite bases and actual previously emitted block scopes plus reversed ports; unentered scopes are not claimed. Processed-point callbacks have no scope field, and the receipt leaves it unknown. Reconstructed C2 calls are diagnostic queries from the exact fixture BIND image, not application events, and are never fed back into analysis.

The first build failed before execution because `Map<String,Any?>=` lacked whitespace. The correction adds only that whitespace. The receipt preserves the failed source, manifest and log. No production or repository test file changed. This bounded candidate is complete; it supplies no new Conductor root-cause claim or accepted policy change.
