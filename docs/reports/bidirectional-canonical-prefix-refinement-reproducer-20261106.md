# Canonical prefix removal delays native refinement

The two-method reproducer has a Current-only failure at the run-3 checkpoint. The proper-prefix-off control passes that checkpoint. With increasing limits, Current first reports the exact T observation in run 5. The control first reports it in run 3. The delay is two iterations: one backward/forward cycle. Both traces complete run 5 with one report. This does not prove a permanent false negative or the cause of the missing Conductor findings.

| Runtime and mode | Reached / completed / accepted run | NORMAL reports | First NORMAL report | Process exit |
|---|---|---|---|---|
| Current `8331bf9e`, check | 3 / 3 / 3 | 0 | None | 1; expected assertion |
| Control B, check | 3 / 3 / 3 | 1 | 3 | 0 |
| Current `8331bf9e`, trace | 5 / 5 / 5 | 1 | 5 | 0 |
| Control B, trace | 5 / 5 / 5 | 1 | 3 | 0 |

The run-3 check compares this program with the control at the same fixed field-limit checkpoint. It is not a claim that every program must converge by run 3.

Both checks finish and accept `COMPLETE / POLICY` at run 3. This is a fixed checkpoint, not convergence. Both traces finish and accept `COMPLETE / NO_DEMAND_EDGE` at run 5. The sealed root receipt records all four terminal commands and log hashes.

The [source](../../core/opentaint-dataflow-core/opentaint-dataflow/src/reproducer/kotlin/org/opentaint/dataflow/bidi/CanonicalPrefixRefinementReproducer.kt) and [optional Gradle init](../../scripts/canonical-prefix-reproducer.init.gradle) are in the repository. The [portable evidence](data/bidirectional-canonical-prefix-refinement-reproducer-20261106.json) embeds both files, the frozen manifest, all four completed logs and the sealed root receipt. It also embeds the earlier positive pair and the verified control. All 20 embedded files have byte counts and SHA-256 hashes.

## Program and real rules

This code shows the analyzed behavior. All required objects and the Element slot are initialized. Allocation lines express that precondition; the native fixture models field effects. `Element` denotes the modeled element slot. Source and sink names denote rules, not additional analyzed methods. The Kotlin reproducer builds two methods and one tagged source action. The sink directly observes exact T at `mapped.Element.h`.

```java
root() {
    p = new Root();
    p.f = new Node();
    p.f.g = sourceT();
    mapped = mapper(p);
    sinkT(mapped.Element.h);
}

mapper(p) {
    out = new Result();
    out.Element = new Slot();
    out.Element.h = new Value();
    out.Element.h.extra = new Value();
    if (flag) out.Element.h.extra = p;
    else out.Element.h = p.f.g;
    return out;
}
```

Field operations use native micro-edges. The driver derives all summaries, demands, initial facts and source permissions. The reproducer supplies none of these. The minimized program has no ND rule, GROUP mode, STATIC operation or alias-specific operation. Both writes have empty alias-path lists. It has no conditional source rule or loop.

Each variant uses FULL mode, a 20-second engine budget, 1 GiB heap and one active CPU. Check mode uses field limits `1, 1, 2`. Trace mode uses `1, 1, 2, 3, 4, ...`. Root ran all four commands. The reporting agent launched none.

## Exact first lost retained fact

The first retained difference is the mapper's final public summary in backward run 2, at field limit 1. Both variants have this identical full premise:

```text
P = { ret.Element.ANY / FLOW(excluded=[]) / fieldExclusion=Empty }
```

The conclusion has layer `DEMAND`, empty field and mark exclusions, and no protected facts.

| Conclusion coordinate | Current | Control B |
|---|---|---|
| `arg0.root.ANY / FLOW` | Retained | Retained |
| `arg0.f.ANY / FLOW` | Lost | Retained |

`root` means the empty field path. The exact lost coordinate is `arg0.f.ANY/FLOW`. The premise and packet header are unchanged. All four minimized logs record the B2 summary at line 127. This is the first retained difference that the reproducer records. The trace does not expose private `canonicalSpans` input events.

The earlier detailed pair confirms actual child-before-root processing on its own program. Its mapper is the same. Both variants process child `arg0.f.ANY/FLOW` at mapper point 0 before the root, at log lines 229 and 235. Only Current's final B2 summary omits the child. Its extra conditional source uses T and V to assign U. Both variants retain the same final U finding.

## Effect in forward run 3

The source and call supply exact T at `arg0.f.g`. Current executes only the coarse mapper entry `arg0.f.STAR/FLOW`, layer `NORMAL`. The control also executes `arg0.f.g.STAR/FLOW`, layer `NORMAL`. Each minimized log prints these actual entries at line 130; control also prints the coarse entry at line 131. The control then records its NORMAL root target in run 3. Current first records that target in run 5.

The detailed pair gives a further lineage check. Both variants have the same concrete call input `arg0.f.g.EXACT/T`, layer `NORMAL`. Its reconstructed C2 query returns the coarse entry for Current and both entries for the control. These queries are diagnostics from the exact fixture BIND image. They are not call-application callbacks and do not prove whether saved replay succeeds.

In that detailed control, line 274 executes the finer mapper entry. This premise has 17 processed rows in run 3; Current has none. Control line 311 processes `mapped.Element.h.EXACT/T`, layer `NORMAL`. Current has no such run-3 caller fact. These rows are preserved separately from the minimized results.

The detailed pair also records the precision change at the second field, `g`, in the read `p.f.g`. Current's `arg0.f.STAR` entry produces `part.ANY/FLOW` in layer `DEMAND`. The control's `arg0.f.g.STAR` entry produces `part.STAR/FLOW` in layer `NORMAL`. Writing `part` to `out.Element.h`, then moving `out` to `ret`, preserves that difference:

| Point | Current coarse entry | Control finer entry |
|---|---|---|
| After read `p.f.g` | `part.ANY/FLOW`, DEMAND | `part.STAR/FLOW`, NORMAL |
| After write `out.Element.h = part` | `out.Element.h.ANY/FLOW`, DEMAND | `out.Element.h.STAR/FLOW`, NORMAL |
| At return | `ret.Element.h.ANY/FLOW`, DEMAND | `ret.Element.h.STAR/FLOW`, NORMAL |

`DEMAND` requests further refinement; it does not establish the exact NORMAL observation. The finer NORMAL transfer can bind the actual `T` input to exact `mapped.Element.h/T` in run 3. Current needs the next refinement cycle.

## Control and evidence checks

The manifest links capsule B by hash. Its sole executable change bypasses inherited parent-prefix subtraction in `canonicalSpans`:

```diff
- val leaf = samePoint(minus(key.node.leaf, key.above))
+ val leaf = samePoint(key.node.leaf)
```

Same-point removal, across-header removal, NORMAL indexing and directional policies remain active. The logs confirm the selected class origin in each JVM. A fresh read verified all 1,282 frozen source pins, all 16 overlay files and the linked capsule inputs. The minimized source and init match their frozen manifest. The sealed root receipt hash is `eb40a5133bfbe8d21f411ea36cdbb2107d0d22e08503b27ed9152362cb7675c7`. The embedded validator passes 269 checks using only portable evidence.

In the detailed pair, all ten projections per variant report zero dropped rows and packets. The caps are 8,192 rows per projection and 256 scalar leaves per packet. Saved snapshots are rendered before each run from the preceding fixed barrier. They cover relevant bases and observed prior scopes plus reversed ports. Processed-point callbacks have no scope field. The report assigns none.

Both frozen manifests still say `PREPARED_NOT_RUN`. The evidence preserves that preparation state. The completed native logs establish the execution results.

## Earlier controls

The four earlier pairs have equal first-report runs within each pair. All retain their expected final finding. Their result rows and log hashes are in the receipt.

| Candidate | First NORMAL report, both variants | Final complete run, both variants |
|---|---|---|
| Mapper | 5 | 5 |
| Extra field | 5 | 7 |
| Precision | 3 | 5 |
| Refinement | 5 | 5 |

These negative controls do not prove general correctness. The child-first pair changes the observed arrival order and exposes the delay.

## Run the optional regression

From `core/`, run:

```bash
./gradlew -I ../scripts/canonical-prefix-reproducer.init.gradle \
  :opentaint-dataflow-core:opentaint-dataflow:runCanonicalPrefixReproducer \
  --no-build-cache --max-workers=1 --console=plain
```

Current is expected to fail the finding-by-run-3 assertion after `COMPLETE / POLICY`, with zero reports. This is the observed regression assertion, not a compile or runtime setup failure. Use task `traceCanonicalPrefixReproducer` to verify recovery at run 5. The optional RED task preserves this counterexample. It does not change the default 2,992-test gate. That gate was not rerun for this reproducer. The receipt records the paired control results.

Production revision `8331bf9e` is unchanged. Main benchmark labels and metrics are unchanged. The diagnostic control is not an accepted production fix.
