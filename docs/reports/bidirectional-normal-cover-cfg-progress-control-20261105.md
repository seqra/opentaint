# CFG follow-up to the NORMAL cover and C2 countercell

**Status: both native CFG controls pass. No finding loss is reproduced.** The feedback loop and its acyclic control both reach, complete and accept forward run-5. Each reports the expected exact sink and stops with `NO_DEMAND_EDGE`.

The [portable receipt](data/bidirectional-normal-cover-cfg-progress-control-20261105.json) contains all 820 structured events, the full log, source/init text, 1282 stable source hashes, and selected pipeline evidence. Root ran the external probe on revision `8331bf9e326ddd1bd5083dbc50456963d6b26b52`. Main and test outputs stayed up to date. No production code, repository test or analysis policy changed.

This is a follow-up to the [native API countercell](bidirectional-normal-cover-opposite-c2-countercell-20261105.md). It does not turn that admission difference into a proved loss of a source permission or report.

## Code under analysis

The common-IR program has a real tagged source action, field reads/writes, three resolved getter helpers and an exact sink:

```java
Box factory() { return sourceAt(f.g.h, T, MUST); }

Box relay(Box input) {
    Box x = input;
    while (again()) {
        if (choose()) {
            x = x;
        } else {
            Box q = new Box();
            q.f = x.f;
            x = q;
        }
    }
    return x;
}

root() {
    Box value = relay(factory());
    sinkT(getH(getG(getF(value))));
}
```

The fixture encodes these operations as explicit micro-edges. It does not load project bytecode, aliases, type filters or production rule metadata. The acyclic control sends the two feedback edges to the relay exit. It keeps the same source, field operations, getters and sink.

Both cases use FULL mode, field limits `1,1,2,3,4,…`, a 20-second driver budget, a 1 GiB heap and one active processor. No summary, initial, demand or source seed is supplied.

## What ordinary analysis produced

The feedback case exports these admitted NORMAL rows at the same public relay interface:

```text
run-1: arg0.* / FLOW       -> ret.* / FLOW       NORMAL
run-3: arg0.f.g.* / FLOW   -> ret.f.g.* / FLOW   NORMAL
```

Both rows have empty E and mx, with no protection mask. The loop also exports scoped NORMAL rows for the `f.g` input in run-3. Thus the short and long relation shapes arise from ordinary analysis. They are not only unit inputs constructed for the earlier API test.

Actual run-3 getter work also executes the coarse initial `arg0.f.g.* / FLOW NORMAL`. Reading `f` produces `ret.g.* / FLOW NORMAL`. This proves that a coarse STAR state is reachable in the CFG. It does not prove that the earlier opposite-replay/C2 countercell occurs at the required interface.

## The path still recovers

The backward run-4 caller point at the relay carries `ret.f.g.h.$ / T NORMAL` after the fixture's exact operand rebase. Its relay C2 query is empty. The input is EXACT, not the coarse STAR required by the API countercell.

Despite that empty query, backward run-4 records a real hit on the factory source. Forward run-5 has source permission and reports the sink. Backward run-2 also hits the source, and forward run-3 has permission. The same results hold for the acyclic control.

In forward run-3, the last getter's observed input is `arg0.h.[any] / T DEMAND`, and its C2 query is empty. That also does not prevent recovery. Saved replay occurs before C2. An empty current admission is not proof that the offered fact stopped.

These observations support the need to inspect the complete saved-first path. They do not identify an individual saved application callback: the probe records point facts and exact AP queries, not every runtime call stage.

## Evidence limits

The program has no reproduced missing finding or source permission. It has no observed coarse opposite STAR query followed by the specific lost admission from the API test. The identity branch can preserve the same concrete DATA path through saved summaries. No comparison against a modified or unpruned analyzer was run.

Two capture limits matter:

- `SAVED_PUBLIC_RECORD` events were printed after analysis. `RecordStore.view()` is a read-only live facade, not an immutable history across later barriers. Those events describe the final persistent store, even when their `run` field names an earlier configuration. They cannot prove which records were available before run-3.
- The run-3 bounded loop trace was requested, but the log contains no `BIDI_LOOP_PIPELINE_TRACE` events. The reason is not established. The requested settings do not prove a captured C5 or saved-application trace.

The frozen per-run summary exports, copied processed facts, demand queries, source hits and permissions are separate evidence and retain their stated meaning. Restricted call-binding observations contain subscriptions; they do not enumerate every denied offer.

The API admission difference remains verified. Whether it can remove a real obligation remains open. This probe does not explain the actual Conductor losses or change the main campaign's quality status.
