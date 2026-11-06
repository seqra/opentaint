# Saved NORMAL records at the getter boundary

The complete saved-record directory contains no NORMAL return relation for
`getG` before run-3. Saved-first replay therefore cannot supply its returned
value in this example. The two saved getG relations are ZERO identity and
argument identity. This closes the saved-record availability question left
open by the [earlier capture](bidirectional-concrete-guidance-repair-reproducer-20261106.md).
It does not select a new initial-admission policy.

Latest reached/completed/accepted: **run-5 / run-5 / run-5**. The unchanged
program naturally ends with `COMPLETE / NO_DEMAND_EDGE` and zero NORMAL
reports, then fails its expected-one-report assertion. The
[complete pre-canonical 52f control](bidirectional-guidance-historical-control-and-data-bridge-20261106.md)
has the same final miss.

The [portable evidence](data/bidirectional-getter-saved-record-gap-20261106.json)
embeds 16 artifacts, including the complete log, five frozen snapshots,
program identity, observer, source/runtime pins and root receipt. All five
snapshots are complete, with zero drops or observer errors. AP-manager
canonical tables remain unchanged across every observation.

## Program and backward result

The native fixture has one exact T source and one exact T observation:

```java
s = sourceT();
do { temp.g = s; next.f = temp; s = next; } while (again);
mapped = mapper(s);
observeExactT(mapped.Element.h);

mapper(q) {
    if (flag) out.Element.h = getG(getF(q));
    else      out.Element.h = q;
    return out;
}
getF(q) { return q.f; }
getG(q) { return q.g; }
```

Required objects and the Element slot are initialized; the finite IR models
these field effects directly. No demand, initial, summary or source permission
is injected. The new probe adds passive observations only. Its stripped
program is byte-identical to the original fixture.

The complete backward run-2 getG snapshot contains one summary and three
processed inputs. All three processed facts and the summary conclusion have
DEMAND layer. Their premise is `ret.[any]/FLOW`:

```text
initial:     ret.[any]/FLOW
at return:   ret.[any]/FLOW, DEMAND
after read:  arg0.g.[any]/FLOW, DEMAND
summary:     ret.[any]/FLOW -> arg0.g.[any]/FLOW, DEMAND
NORMAL summaries: none
scoped summaries: none
```

This is a native joined result, not a hypothetical transfer. The DEMAND row
can guide run-3 but does not become a persisted NORMAL return record.

## Complete saved directory before run-3

The probe reads the actual `PersistentRecordStore` backing state before the
forward run starts. It verifies that the run-3 read-only record view delegates
to this store. There are 12 current owners and 28 records. Every record joins
to one current row with the same owner, premise, facts and protection. There
are no packed rows in this directory.

Exactly two records belong to getG, both public and stored FORWARD:

```text
ZERO -> ZERO, NORMAL
arg0.*/FLOW -> arg0.*/FLOW, NORMAL
```

There is no getG BACKWARD record, scoped record or conclusion with return
base. The explicit call bind-back maps `ret` to `gotG`. Neither saved result
can supply that returned value. This conclusion does not depend on whether
the two identity records actually match. The probe does not call the record
matcher or replay API.

Native records do not store their creation run. The capture reports their
actual stored direction and owner; it does not invent creation-run metadata.

## Remaining forward boundary

The previous complete run-3 snapshots record the normal getF relation and
the following mapper input. The current source bytes are unchanged:

```text
getF: arg0.f.g.*/FLOW -> ret.g.*/FLOW, NORMAL
mapper at getG call: gotF.g.*/FLOW, NORMAL
bound getG input:    arg0.g.*/FLOW, NORMAL
getG demand:         arg0.g.[any]/FLOW -> ret.[any]/FLOW

call pipeline:
  replay saved NORMAL records        // no saved return relation
  apply existing C2 to demand + input // same-head ANY + STAR emits nothing
  current subscription/analysis       // no admitted initial
```

The bound input and C2 result are source-derived from the recorded caller
fact and call plan. A rejected-C2 callback was not logged. Separate native
tests verify that same cell against the unchanged policy. The new complete
directory proves that a saved return relation cannot bypass this boundary.

The capture uses the native main/test runtime with no production overlays,
Java 21, a 1 GiB/one-CPU diagnostic child and the original 20-second budget.
Root owns the execution. This is not a project performance measurement.
It identifies an inherited blocked getter route, not the first lost fact in
the entire analysis or a final Conductor cause. A new admission rule still
needs a separate semantic decision and progress proof. No C2, field, layer,
summary-restriction or stopping policy was changed.
