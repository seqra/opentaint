# A NORMAL field read can create MAY without a field cut

12 November 2026. This is a small native AP regression cell for the current
demand-campaign target `1025a197…`. It does not execute the OWASP method or
classify its demand row.

The original OWASP reference reached/completed/accepted forward run is
run-11/run-11/run-11. This fixture runs no analyzer iteration or project
scan and makes no production change.

## Native cell

All marks are FLOW; all exclusions are empty. The direct compiled micro-edge
is NORMAL:

```text
x.f.*/FLOW -> y.*/FLOW
```

`x` is represented by `arg(0)` and `y` by `ret` in the isolated test. `f`
has the opaque native key `(owner=Opaque, name=f, type=Opaque)`. The labels
make the field-read transfer easy to read; no type property is used.

| Actual fact | Native output | Reason |
| --- | --- | --- |
| `x.*/FLOW`, NORMAL | `y.[any]/FLOW`, DEMAND | The fact is above the read. STAR does not establish which suffix reaches f. |
| `x.$/FLOW`, NORMAL | Nothing | The exact root does not include f. |
| `x.[any-taint]/FLOW`, NORMAL | `y.[any-taint]/FLOW`, NORMAL | Uniform taint includes f. |
| `x.f.*/FLOW`, NORMAL | `y.*/FLOW`, NORMAL | The read consumes f and keeps suffix correlation. |

The first result is a genuine NORMAL-to-MAY transition. It does not need a
field-limit cut, a DEMAND input, a DEMAND micro-edge or C5 restriction.

The pinned `EdgeApplication.flow` visits a fact above `fromPath`. For a
non-exact, non-MUST fact it adds a DEMAND result at the target. EXACT takes
no ancestor-read branch; MUST uses the definite-taint branch. A fact at the
complete `fromPath` instead keeps its tail and layer.

This is an **instruction micro-edge**. It does not bypass the separate
same-direction saved-summary STAR-inside guard. The fixture calls no
summary matcher, demand store, method actor, loop gate or alias analysis.

## Check and reproduction

The [Java fixture](../../scripts/demand_campaign/FirstMayNativeCell.java)
compares `ApOps.applyEdge` and the compiled AP entry point. It checks all four
cells in both directions at field limits 1, 3 and 11: **24 cells pass**.
It calls no field-cut function. The unchanged result at limit 11 establishes
that a small field budget is not needed for this MAY creator.

Use the frozen source-built 92-entry classpath, with source revision
`14d7b63369d94f49d4c551be8405ed7719f267cc`. The
[runner](../../scripts/demand_campaign/run_first_may_cell.py) verifies all
438 classpath files and runs one small Java process with a 256 MB heap:

```sh
python3 scripts/demand_campaign/run_first_may_cell.py \
  --runtime /path/to/redundant-demand-rows-20261112/cases/pinned-runtime-source-build-v3 \
  --out /new/external/first-may-cell-result
```

The final receipt and literal JSON fact outputs are in the external archive:

```text
docs/reports/data/redundant-demand-rows-20261112/cases/
  first-may-native-cell-v4/receipt.json
  first-may-native-cell-v4/run.txt
```

See the [external-data policy](EXTERNAL_DATA.md). The first compilation
attempt used a nonexistent diagnostic getter and remains an unsuccessful
attempt. v4 adds an explicit classpath-order check and bounded execution;
all 24 cells pass with the unchanged fixture.

## Existing coverage and limit of this result

The frozen micro-observer `MicroSmoke.java` already checks the STAR ancestor
and same-path STAR cases, including the ordered results with and without an
observer context. Its source hash is
`0a087341ed686427a6fc6dbbf0afbb23ac011105b4d0093c71ac1631e112d9d6`;
the frozen smoke trace hash is
`9b9615596198b3f87cee6d48edc5ec9dc7ca5293d50fca53714d5b5d54a5c5aa`.
The new fixture adds the missing EXACT/MUST comparison and makes the
field-limit independence explicit, without loading an observer or project.

This test shows how the native AP operation can create MAY. The separate
[project capture](bidirectional-demand-row-campaign-20261112.md#native-may-creation-in-the-constructor)
records the constructor input, compiled relation and instruction. The small
fixture itself proves no whole-method behavior, redundant row, closed
evolution or lost sink.
