# Loop boundary loses normality in a shared direct-observation case

Current and the proper-prefix-off control both miss the feasible exact T observation. Both analyses reach, complete and accept run 5 with `COMPLETE / NO_DEMAND_EDGE`. Neither reports a finding. This is a separate shared coverage problem. It does not isolate canonical prefix removal as its cause or explain the missing Conductor findings.

| Runtime and task | Reached / completed / accepted run | NORMAL reports | Process exit |
|---|---|---|---|
| Current `8331bf9e`, native probe | 5 / 5 / 5 | 0 | 0 |
| Control B, native probe | 5 / 5 / 5 | 0 | 0 |
| Current, native F3 trace | 5 / 5 / 5 | 0 | 0 |
| Current, optional regression | 5 / 5 / 5 | 0 | 1; expected assertion |
| Control B, optional regression | 5 / 5 / 5 | 0 | 1; expected assertion |

The [portable evidence](data/bidirectional-loop-boundary-normality-loss-20261106.json) embeds the direct source, init, paired logs, native run-3 trace and lineage audit. It also contains the optional regression source, init, both check logs and sealed root execution receipt. All 26 embedded files have byte counts and SHA-256 hashes. Its validator passes 217 checks. The plain and logging-enabled Current runs have equal run-end, frontier and final-result rows.

## Program and feasible observation

This program has four analyzed methods and one tagged T source. The source returns an initialized object. Required objects and the Element slot are initialized below. Allocation notation states the object-graph precondition; the native fixture models field effects. Source and observation names denote rules, not extra analyzed methods.

```java
root() {
    temp = new Box();
    next = new Box();
    s = sourceT();
    do {
        temp.g = s;
        next.f = temp;
        s = next;
    } while (again);
    mapped = mapper(s);
    observeExactT(mapped.Element.h);
}

mapper(q) {
    out = new Result();
    out.Element = new Slot();
    if (flag) out.Element.h = getG(getF(q));
    else out.Element.h = q;
    return out;
}
getF(q) { return q.f; }
getG(q) { return q.g; }
```

The loop executes at least once. If it exits after one iteration, `s.f.g` is the original source object. The getter branch places that object at `mapped.Element.h`. Thus, a feasible path satisfies the exact T observation.

The source uses a native tagged source action. Calls, reads, writes and moves use native micro-edges. There is no ND condition, GROUP mode, STATIC operation or explicit alias path. The driver derives all summaries, demands, records, initial facts and source permissions. The probe injects none of these.

Both variants use FULL mode, field limits `1, 1, 2, 3, 4, ...`, a 20-second engine budget, 1 GiB heap and one active CPU. Root ran the commands. The reporting agent launched none.

## First relevant executed downgrade

The direct native trace selects only the root method in forward run 3, at field limit 2. The source is actually replayed at sequence 6. Sequence 19 actually offers the resulting NORMAL `s.EXACT/T` to the loop.

The first executed downgrade of the source-backed `s.f.g` result is sequence 55. This packet has premise ZERO, empty field exclusions and no protection. The trace records:

| Native stage | Sequence / log line | Fact and layer |
|---|---|---|
| Raw loop result | 52 / 179 | `s.f.g.EXACT/T`, NORMAL |
| Kept loop result | 55 / 182 | `s.f.ANY/T`, DEMAND |
| Raw result on exit toward the adjacent block | 68 / 195 | `s.f.g.EXACT/T`, NORMAL |
| Kept result on that exit | 71 / 198 | `s.f.ANY/T`, DEMAND |
| Fresh completion | 72 / 199 | `s.f.ANY/T`, DEMAND |
| Actual offer to adjacent scope `(3, 7)` | 73 / 200 | `s.f.ANY/T`, DEMAND |

The restriction loses both the exact second field and the NORMAL layer. The raw packet header says `ANY_TAINT`, but its terminal node has `exact=[T]`, `any=[]` at path `[f,g]`. The kept packet has `exact=[]`, `any=[T]` at `[f]`. These are decoded leaf facts, not an inference from the packet header.

## Admission also limits the causal claim

The native diagnostic hook queries frozen admission for both raw and kept packets. These observations are read-only selections; they do not mean both packets were offered. The actual adjacent offer is sequence 73.

At both comparison points, the complete raw and kept observations are equal: sequences 53/54 and 69/70. Each selects:

| Family and scope | Initial | Layer |
|---|---|---|
| Adjacent `(3, 7)` | `#18: s.f.STAR/T` | DEMAND |
| Repeat `(2, 4)` | `#12: s.f.STAR/FLOW`, empty mark exclusions | NORMAL |

The enclosing selection is empty. The NORMAL repeat initial is abstract FLOW support; it is not a NORMAL concrete-T initial for the adjacent block. Even the raw NORMAL exact packet selects only DEMAND there. Thus, the executed restriction downgrade does not establish restriction as the unique cause of the miss. Control B also fails to restore the observation.

Sequence 79 records native scoped state with concrete initial `#18` in DEMAND. Sequence 104 records a `c5-normalized` candidate `mapped.Element.h.ANY/T`, also in DEMAND. That candidate is not evidence of an admitted C5 export. The root-only selector does not observe getter admission. Missing getter events cannot prove that no getter was admitted; saved replay can also answer calls.

## Evidence limits and optional regression

The direct trace emits all 104 attempted events. It reports zero oversized rows, limit drops, encoding errors and sink errors. Its cap is 4,096 events. A pinned logging provider exposes existing INFO hooks; this is not a performance measurement. No earlier ND trace row is used here.

The verified B capsule changes only inherited parent-prefix subtraction in `canonicalSpans`. Its native class origin is checked in the paired log. Both paired commands finish successfully because the discovery probe asserts completion, not finding presence. Their empty final demand and accepted reports are preserved in the receipt.

The [optional repository source](../../core/opentaint-dataflow-core/opentaint-dataflow/src/loopReproducer/kotlin/org/opentaint/dataflow/bidi/LoopBoundaryPrecisionReproducer.kt) checks natural convergence and then requires one NORMAL report. Both Current and B finish and accept run 5 with zero reports. Each process then exits 1 at exactly that missing-report assertion. The failures are not compilation or runtime setup failures. These optional RED checks preserve the shared counterexample.

From `core/`, run:

```bash
./gradlew -I ../scripts/loop-boundary-reproducer.init.gradle \
  :opentaint-dataflow-core:opentaint-dataflow:runLoopBoundaryPrecisionReproducer \
  --no-build-cache --max-workers=1 --console=plain
```

The [init script](../../scripts/loop-boundary-reproducer.init.gradle) keeps this source set separate from the default tests and the prefix reproducer. The default 2,992-test gate is unchanged and was not rerun for this case. The committed prefix reproducer inputs remain byte-identical.

Production revision `8331bf9e` and main benchmark labels and metrics are unchanged. This report establishes a shared native miss and an executed normality loss. It does not establish a unique production fix or a Conductor causal path.
