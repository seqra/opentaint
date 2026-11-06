# Uniform subtree source: prefix removal delays the NORMAL report

The uniform-source check fails its run-3 finding assertion on Current and passes on control B. Both traces reach, complete and accept run 5 with one finding and `COMPLETE / NO_DEMAND_EDGE`. Current first reports in run 5; B first reports in run 3. This proves a two-iteration report delay. It does not prove permanent finding loss or the cause of Conductor's final missing findings.

| Runtime and mode | Reached / completed / accepted run | First NORMAL report | Final reports | Process exit |
|---|---|---|---|---|
| External Current `8331bf9e` | 5 / 5 / 5 | 5 | 1 | 0 |
| External proper-prefix-off B | 5 / 5 / 5 | 3 | 1 | 0 |
| Repository Current, check | 3 / 3 / 3 | None | 0 | 1; expected assertion |
| Repository B, check | 3 / 3 / 3 | 3 | 1 | 0 |
| Repository Current, trace | 5 / 5 / 5 | 5 | 1 | 0 |
| Repository B, trace | 5 / 5 / 5 | 3 | 1 | 0 |

Both repository checks finish and accept `COMPLETE / POLICY` at the fixed run-3 checkpoint. This is not convergence. Current's process fails only the expected finding assertion after that result. The two trace processes complete naturally and exit 0. Root ran all six commands; the reporting agent launched none.

The [optional source](../../core/opentaint-dataflow-core/opentaint-dataflow/src/uniformPrefixReproducer/kotlin/org/opentaint/dataflow/bidi/UniformPrefixRefinementReproducer.kt) uses two methods and one native source action. Its analyzed program and call helper match the frozen external pair. Compared with the [exact-source case](bidirectional-canonical-prefix-refinement-reproducer-20261106.md), only the source fact changes:

```diff
- p.f.g.EXACT/T
+ p.f.ANY_TAINT/T
```

`ANY_TAINT`, called MUST below, marks the whole subtree. The source object and its `g` value are initialized. Allocation notation states that precondition; the fixture models native field effects.

```java
root() {
    p = new Root();
    p.f = sourceUniformT(); // initialized subtree, including g
    mapped = mapper(p);
    sinkExactT(mapped.Element.h);
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

Source and sink names denote rules, not extra analyzed methods. There is no ND condition, GROUP mode, STATIC operation or explicit alias path. The driver derives all demands, summaries, initial facts and permissions. No diagnostic query supplies analysis input.

## Exact mechanism

Here `p` is mapper `arg0`, bound from caller local 0. Fields `f` and `g` have logged IDs 0 and 4. `[any]` means ANY, `*` means STAR, and MUST means ANY_TAINT. All exclusions are empty; the listed facts are ordinary and have no protection.

```text
D0 = p.[any]/FLOW
D1 = p.f.[any]/FLOW
A  = p.f.MUST/T                 NORMAL

Current B2 retains {D0}         DEMAND
Control B2 retains {D0, D1}     DEMAND
C2({D0}, A)     = {p.f.*/FLOW}                 NORMAL
C2({D0, D1}, A) = {p.f.*/FLOW, p.f.MUST/FLOW}  NORMAL
```

Both B2 conclusions have the same full premise `ret.Element.[any]/FLOW`. Current's `canonicalSpans` subtracts the inherited parent span and removes `D1`. Set coverage is preserved, but the refinement image changes. For `D0`, C2 advances one field and emits STAR. For `D1`, the demand and actual have the same `p.f` prefix, so C2 preserves the actual MUST tail.

The external logs show the retained difference at line 162. The same NORMAL uniform T input remains at the caller in both variants. Actual processed F3 rows show the effect:

| Stage | Current | B's additional entry |
|---|---|---|
| Mapper entry | `p.f.STAR/FLOW`, NORMAL | `p.f.MUST/FLOW`, NORMAL |
| After reading second field `g` | `part.ANY/FLOW`, DEMAND | `part.MUST/FLOW`, NORMAL |
| Return after the good write | `ret.Element.h.ANY/FLOW`, DEMAND | `ret.Element.h.MUST/FLOW`, NORMAL |
| Caller output | `mapped.Element.h.ANY/T`, DEMAND | `mapped.Element.h.MUST/T`, NORMAL |

Current entry/read rows are lines 193/196; B's MUST entry/read rows are lines 197/200. B's NORMAL caller output is line 230 and its NORMAL root target is line 232. The probe records actual processed entries and results. Its C2 equations follow the native policy; it does not inject or reconstruct C2 queries. Current first reports in run 5. The capture does not assign a new run-5 entry as the recovery cause.

## Relation to the real Conductor query

The [upstream Conductor capture](bidirectional-conductor-upstream-admission-20261106.md) has pure query `2d4642a06869395d21b1a14a86f54d47f4eeede366566207f111787138675a6e`. Both variants submit the same NORMAL `WorkflowModel.workflowDefinition.MUST/Graal` packet to `createAndEvaluate`. Current returns `workflowDefinition.STAR/FLOW`, NORMAL. B also returns `workflowDefinition.MUST/FLOW`, NORMAL. Both return the concrete Graal STAR initial in DEMAND. B later uses its extra FLOW initial, local ID 4784, as the ROOT-scope premise of its call to `createAndEvaluateWithLock`.

This is the same MUST-versus-STAR admission distinction as the small uniform case. Equal pure query keys do not imply equal complete caller premises or a uniquely matched delivery. The capture does not prove that this initial is required for either final missing Conductor finding. The small case remains a report-delay proof.

## Optional check and trace

From `core/`, run:

```bash
./gradlew -I ../scripts/uniform-prefix-reproducer.init.gradle \
  :opentaint-dataflow-core:opentaint-dataflow:runUniformPrefixReproducer \
  --no-build-cache --max-workers=1 --console=plain
```

Check mode uses field limits `1, 1, 2` and requires one report by run 3. It compares this fixed checkpoint; it does not require every program to converge by run 3. Use task `traceUniformPrefixReproducer` to require natural completion, with limits capped through field 10/run 11. A POLICY stop does not establish convergence. Both modes use FULL, 1 GiB heap, one active CPU and a 20-second engine budget.

The frozen external preparation remains unchanged. The [portable evidence](data/bidirectional-uniform-prefix-refinement-reproducer-20261106.json) contains all six logs, both sealed root receipts, source, both checked and current init text, the one-source-change diff, and native/B pins. It also contains the selected real Conductor witness. All 24 embedded files have byte counts and hashes. Its validator passes 242 checks.

After all four repository commands ended, two init comment examples were corrected to name `uniform-prefix-reproducer.init.gradle`. The checked init is preserved in the evidence. The comments-only diff and current hash are recorded; executable text is unchanged and no rerun was required.

These tasks are optional. The default 2,992-test gate, production revision and main benchmark labels and metrics are unchanged. The default gate was not rerun for this case.
