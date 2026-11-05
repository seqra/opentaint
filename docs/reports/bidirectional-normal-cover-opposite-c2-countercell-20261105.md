# NORMAL relation cover changes native opposite replay and C2

**Status: native API countercell confirmed; no CFG or project finding loss proved.** On revision `8331bf9e326ddd1bd5083dbc50456963d6b26b52`, removing a covered NORMAL relation can remove an initial that native C2 would emit. The concrete relation-union law still holds. That law does not establish equivalence of the native replay and admission pipeline.

The [portable receipt](data/bidirectional-normal-cover-opposite-c2-countercell-20261105.json) contains all 24 results, full facts and original premises, source/init text, all three attempt logs and source versions, 1242 production Kotlin/fixture hashes, and 11 passing verification checks. Root ran the external control. There was no project analyzer run, core change, repository test addition or selected fix.

## The exact cell

Both stored rows are legal FORWARD NORMAL native FLOW records at the same interface:

```text
S: p.* / FLOW       -> q.* / FLOW       NORMAL
L: p.f.* / FLOW     -> q.f.* / FLOW     NORMAL

p = Argument(0), q = Return
f = fixture FieldAccessor(Box, f, Box), accessor ID 0
E = {}, mx = {}, protection = none
```

S covers L under the selected common-suffix relation law. The independent oracle retains both actual supplied records. The real `PersistentRecordStore` retains S only. This result holds for either arrival order.

Read the stored rows in the opposite, BACKWARD direction on `q.* / FLOW NORMAL`. The native inverse of S matches at its root and emits `p.* / FLOW NORMAL`. The inverse of L matches a strict ancestor STAR. That match is allowed for an opposite record. Native approximation emits `p.f.[any] / FLOW DEMAND`.

Both outputs pass through production `canonicalPackets` and `ConclusionGroup`. They have different tail/layer headers, so the extra MAY packet remains in the unpruned oracle. No hidden refinement history is used.

For an existing demand entry `p.[any] / FLOW`, native C2 then gives:

| Retained records | Native outputs before C2 | Emitted initial |
|---|---|---|
| S and L | `p.* NORMAL`; `p.f.[any] DEMAND` | `p.f.* / FLOW NORMAL` |
| S only | `p.* NORMAL` | none |

The reason is explicit in [RestrictedInitialPolicy.kt](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/RestrictedInitialPolicy.kt#L30): a STAR actual at the same prefix does not answer an ANY demand. A deeper MAY actual supplies the next field. FLOW initial admission uses its intrinsic NORMAL layer, even when this supplied MAY packet is DEMAND.

The complete parent original stays `Argument(2).f.* / FLOW`; each native data callback checks its identity. The record premise does not replace it.

## Native coverage and controls

The 24 cases cover run-2 and run-4 C2 policies with field budget 2, public and scoped records, and both arrival orders. Scoped native rows keep `(block 1, entry 11, exit 22)`; opposite reads use `(block 1, entry 22, exit 11)`. C2 uses a separate typed consumer interface. These are native store keys, not a claimed physical CFG.

| Actual at q | Countercells or controls | Unpruned C2 | Antichain C2 |
|---|---:|---|---|
| FLOW STAR NORMAL | 8 countercells | `p.f.* / FLOW NORMAL` | empty |
| concrete T STAR DEMAND | 8 countercells | `p.f.* / T DEMAND` | empty |
| concrete T EXACT NORMAL | 8 positive controls | `p.$ / T NORMAL` | same |

Every result records full headers, selected native read, output, original, E, mx and protection. All masks are empty in these cells. T is the fixture's declared concrete full atom, not a project Graal mark. Both inverse readers have `NativeReadKind.GENERIC`; the new reverse-MUST overlap branch is not used.

The primary FLOW check uses a legal DATA demand pair, `p.[any]/FLOW -> arg3.*/FLOW`. The probe also submits a builder-accepted FLOW-entry/ZERO control row to the C2 query interface. It does **not** prove that the analyzer can produce a FLOW-premise Target row. The concrete T control row has the producer-compatible shape `p.[any]/T -> ZERO`. Its C2 sets agree with the concrete DATA-pair sets. No Target is produced or removed by this control.

## What this means for a real flow

This proves a native admission difference, not a lost report. An added initial can run a block, produce a new precise NORMAL record, or reach a conditional source or Target obligation. The probe does not execute those steps.

A small candidate producer is a branch that returns p unchanged on one path and a fresh object's `f` field copied from `p.f` on another:

```java
Node relay(Node p, boolean b) {
    if (b) return p;
    Node q = new Node();
    q.f = p.f;
    return q;
}
```

A driver proof must first show that ordinary analysis admits both required native rows at one actual interface. It must then derive the coarse opposite STAR input and the `p.[any]` consumer demand through normal handoff. Finally, it must show a real source permission or Target available only after the extra initial. This code alone is not a finding reproducer: its identity-return path can already carry the same concrete DATA flow to a caller sink.

The actual Conductor guidance gap remains a separate investigation. This result does not identify its first lost producer and does not attribute its two missing findings to relation pruning.

## Execution record

Attempt 1 failed only during compilation because of two fixture API errors. Attempt 2 compiled, then failed a fixture assertion that compared a `PathNode` with a list. Attempt 3 corrected that representation check and passed all 24 cells: 16 countercells and 8 controls. All attempt source hashes and logs are retained. Main/test compile outputs stayed up to date. The one-second build is not analyzer performance evidence.

All attempts used the repository's `core` directory and its Gradle wrapper. The original preparation manifest had named the repository root; root corrected that working directory before execution. Runtime budget was 1 GiB and one active processor. No main-campaign iteration was added. The [main campaign report](bidirectional-canonical-facts-normal-relations-directional-inside-performance-20261105.md) retains the project reached/completed/accepted labels and unresolved quality status.

## Organic CFG follow-up

The [source, loop and getter control](bidirectional-normal-cover-cfg-progress-control-20261105.md) derives short and long NORMAL rows through ordinary analysis and reaches coarse STAR work. Both its feedback and acyclic cases report the sink and finish at run-5. It does not reproduce the required opposite STAR query or a lost source permission. The API countercell therefore remains a query-level result, not a proved finding loss.
