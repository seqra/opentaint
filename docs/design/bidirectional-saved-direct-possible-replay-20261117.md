# Possible replay of a blocked saved NORMAL FLOW relation

17 November 2026. Synthetic data-flow reachability. FULL mode.
Follow [proof-guide.md](../../spec/proof-guide.md).
This is a proposal repair. Production is unchanged.

The [prefix-return gap](../reports/bidirectional-prefix-return-soundness-gap-20261117.md)
is repaired in the reference: the NORMAL observation is present and demand
is empty at **run-5**. Native components check the repaired run-4/run-5
pipeline. The unchanged native driver still reproduces the old loss at run-5.

## 1. Semantic change

Add one **possible, DEMAND-only** read of an existing saved NORMAL record.
This is a matching change. It is not a storage optimization.

| Case | Before | After |
|---|---|---|
| Same-direction NORMAL `a.u.v.* / FLOW -> b.w.* / FLOW`, offered `a.u.*`, with nonempty v | Reject the STAR inside match; empty current demand gives no service | Keep the ordinary rejection as the definite result. Add the possible result `b.w.MAY`, DEMAND, if the real guards allow it |
| Existing successful saved read | Use the ordinary reply | Keep that exact reply; do not add a second reply for that scalar pair |
| Opposite-direction record | Existing native reverse view and matching | Unchanged |
| Current summary, ND record, marked record, MUST guard, non-STAR result or non-STAR offer | Existing policy | Unchanged |

Both restricted directions use the new lane. The saved record keeps its
real direction, premise, conclusion, scope and physical ports. Do not
reverse it to obtain this permission. Do not turn its possible match into
NORMAL. NormalTarget still accepts NORMAL composition only.

Keep C2, its raw C5 image, paired output selection, NE cuts, field exclusions,
mark exclusions, literal protection, aliases, source permissions, ZERO/Target
rules and the stopping rule. There is no new field-limit exception.
Run-1 has no previous-run replay and is unchanged.

## 2. Replay procedure

Use the existing saved-input index. `PersistentRecordStore.byEntry` already
returns comparable premise paths through `PathTrie.around`; it can return
the deeper guard in this example. The missing operation is matching, not
index expansion. Methods and local block boundaries use the same rule.

Apply this procedure to scalar record/result and offered leaves, before
current-demand admission. A successful match on one leaf of a packed row
must not hide an unmatched ancestor STAR leaf in that row.

```text
replaySavedScalar(record, offered, original, continuation):
    reply = ordinarySavedReplay(record, offered, original)
    if reply exists:
        return reply                         // exact old result and annotations

    if not restrictedRun: return empty
    if record.direction != currentDirection: return empty
    if record is not unary NORMAL DATA: return empty
    if record.premise.mark != FLOW or record.result.mark != FLOW: return empty
    if record.premise.tail != STAR or record.result.tail != STAR: return empty
    if offered.tail != STAR: return empty
    if not sameBaseAndRealPorts(record.premise, offered): return empty
    if record.premise.path != offered.path + nonemptySuffix: return empty
    if offered.E excludes first(nonemptySuffix): return empty

    // Keep all native mark, exclusion, original, H and application checks.
    // This permission does not change the record's direction or geometry.
    reply = nativePossibleInsideTransfer(record, offered, original)
    if reply is empty: return empty
    assert reply.layer == DEMAND
    assert reply.path == record.result.path
    assert reply.tail == MAY
    // MAY lost suffix correlation; use the existing loss-created Empty E.

    if existingReadyChildCertificateCoversThisContribution(reply): return empty
    return resumeExistingContinuation(reply)  // ordinary binding/actions/aliases
```

This does not restart the callee or subscribe without demand. It reads a
retained NORMAL relation and returns one possible answer. The caller uses
its usual field limiter and own paired C5. New DEMAND answers are not saved
as NORMAL records. There is no full suffix archive, child creation, guard
path product or new persistent key.

The ready-child test is the existing complete geometric proof, extended to
this extra possible read. Its first field is the first field of the saved
guard after the offered head. Use it only for an already prepared, ready
child with all required consumers and qualifiers covered. Otherwise keep
the reply. Never assume child coverage merely because that field is known.
Do not suppress an old successful replay under this new test.

The existing completion selectors must inspect the closure **with this
new lane enabled**. A new DEMAND state cannot be ignored to certify NORMAL
closure. Prior full-mark-only model histories are outside this lane; they
are not a proof that all combined completion histories remain equal.

## 3. Why the repair covers the missing route

The code is unchanged:

```java
Node wrap(Node x) {
    Node a = x.g.g;
    Node b = keepF(a);
    Node c = new Node(); c.g = b;
    Node y = new Node(); y.g = c;
    return y;
}
Node keepF(Node x) {
    Node y = new Node(); y.f = x.f;
    return y;
}
```

`main` assigns T uniformly below x.g and observes any returned T. F means
FLOW; N means NORMAL; D means DEMAND. All field and mark exclusions are
empty. The [original report](../reports/bidirectional-prefix-return-soundness-gap-20261117.md)
contains the complete cold run-1 through run-3 trace. Those runs are equal
before and after this repair. In particular, run-3 **still cuts** the raw
`ret.g.g.f.MUST/F,N` at limit 2 to `ret.g.g.NE/F,D`.

### Run-4: backward, global limit 3

Backward summaries are above the body. Demand, actuals and initials are
below it. The helper is served by a record; no helper query starts.

```java
// Published: ret.g.g.*/F -> x.g.g.NE/F,D
Node wrap(Node x) {
    Node a = x.g.g;                 // backward x.f.MAY -> x.g.g.f.MAY,D
    Node b = keepF(a);              // new possible reply: a.f.MAY/F,D
    Node c = new Node(); c.g = b;   // backward c.*/F -> b.*/F,N
    Node y = new Node(); y.g = c;   // backward y.g.g.*/F -> c.g.*/F,N
    return y;
}
// Demand (Dc; Dp): (ret.g.g.NE/F; x.g.MAY/F)
// Submitted: ret.MAY/T,D
// Raw initial: ret.g.g.*/F,N
// Raw output: x.g.g.f.MAY/F,D
// C5: min(global 3, FL(x.g)+1)=2 -> x.g.g.NE/F,D

// No current publication. Retained NORMAL backward record:
// ret.f.*/F -> x.f.*/F,N
Node keepF(Node x) {
    Node y = new Node(); y.f = x.f;
    return y;
}
// Current demand: empty
// Submitted from wrap: ret.*/F,N
// Emitted initials: none
// Ordinary DIRECT read: no reply
// New possible read: x.f.MAY/F,D
```

The raw result has three fields; C5 keeps only two. There is no special cap
bypass. The same helper record stays retained. Handoff gives wrap the paired
forward demand `(x.g.g.NE/F; ret.g.g.*/F)`.

### Run-5: forward, global limit 4

```java
// Demand (Dc; Dp): (x.g.g.NE/F; ret.g.g.*/F)
// Submitted: x.g.MUST/T,N
// Raw initial: x.g.g.MUST/F,N, using existing uniform coverage
Node wrap(Node x) {
    Node a = x.g.g;                 // a.MUST/F,N
    Node b = keepF(a);              // b.f.MUST/F,N, saved opposite record
    Node c = new Node(); c.g = b;   // c.g.f.MUST/F,N
    Node y = new Node(); y.g = c;   // y.g.g.f.MUST/F,N
    return y;
}
// Published: x.g.g.MUST/F -> ret.g.g.f.MUST/F,N
// Output cap: min(4, FL(ret.g.g)+1)=3; no cut.
// Original x.g.MUST/T satisfies the complete uniform premise.
// Caller receives r.g.g.f.MUST/T,N. NORMAL observation; empty demand.

// Current demand: empty; submitted: x.MUST/F,N; initials: none.
Node keepF(Node x) {
    Node y = new Node(); y.f = x.f;
    return y;
}
// No current publication. Ordinary saved opposite replay returns
// ret.f.MUST/F,N. The new possible DIRECT lane is inactive.
```

Thus the repair supplies guidance at run-4, and ordinary definite service
supplies the final NORMAL result at run-5. It does not confirm an uncertain
run-4 answer. Full case 165 also retains its NORMAL result at run-5. The
updated 884 control has exactly the same complete run-5 reference state.

## 4. Proofs and negative controls

The [constructive proof package](../../spec/lean/proposals/saved-direct-possible-replay-20261117/README.md)
checks these properties:

1. Every old successful saved reply remains literal, with its old layer.
   Every newly added scalar reply is DEMAND. A NORMAL reply from the new
   reader has an old NORMAL derivation.
2. A successful concrete relation `a.u.v.s -> b.w.s`, with nonempty v and
   real guards satisfied, has its result in `b.w.MAY`. The witness is s.
   Arbitrary additional fixed native qualifiers stay attached to that same
   witness. This proves conservative possible coverage, not uniform taint.
3. E blocking the first unknown field still rejects. EXACT, MAY, NE and
   MUST offers keep their old lanes. Marked and DEMAND records are ineligible.
   Native tests retain inherited H and reject a result excluded by mx.
4. Qualified ready-child suppression uses the existing constructive first-
   field cover with real E. It needs a complete actual service certificate.
5. All five cold runs are within-run fixed points. Run-4 retains the missing
   paired demand; run-5 retains the real NORMAL marked region and empties
   the frontier. Both caps and the mandatory run-3 cut remain active.

The formal model represents unary return-cone prefix transfers, including
real keeps, prepared children, C2, paired C5 and saved replay. It does not
model whole-driver Target/source-permission scheduling. Native components
check those AP operations, not an installed whole-engine repair. General
G1–G4 in the [soundness audit](bidirectional-demand-termination-soundness-audit-20261117.md)
remain open. This repair closes the concrete prefix-return case; it does
not prove universal termination or whole-analyzer soundness.

## 5. Work and validation scope

For L path length and N existing candidate scalar records, replay stays
O(N*L), plus the existing packet/binding cost. A record/offer pair produces
at most one reply. A new reply uses the stored result head; it appends no
unknown suffix or saved evidence. It creates no query or subscription at
that replay step. Later callers can receive more demands and start ordinary
demanded work. Do not describe this change as zero-cost.

All 18 earlier ordinary prefix/write cases reach within-run fixed points
and natural empty-demand completion. Sixteen keep their completion run.
Two need more refinement after the new possible service:

| Reference case | Old latest run | New latest run | Old/new maximum demand rows | Old/new maximum published rows |
|---|---:|---:|---:|---:|
| Double | run-13 | run-17 | 12 / 29 | 12 / 30 |
| Growth | run-11 | run-13 | 23 / 25 | 33 / 35 |
| Minimal prefix return | run-5, missed observation | run-5, NORMAL observation | 1+1 initial owner rows; repaired run-4 has 1+0 | repaired run-5 has 1+0 |

These are reference row counts, not project benchmarks. The old reference
has no integrated whole-driver reporting state. An added NORMAL value in
a returned packet need not be a new observation identity.

A separate 256-case check varies wrapper reads/writes of 0..3 g fields,
helper reads f or f.g, helper writes f or f.f, source uniform head g or g.g,
and one or two wrapper calls. All 95 positive and 161 negative cases agree
with ordinary concrete execution. All within-run fixed points pass;
natural completion reaches **run-9**, with at most 8 demand rows. The
run-33 diagnostic bound is not used as a termination or redundancy proof.

Six new native component tests join the previous targeted suite. The cold
unmodified-driver diagnostics remain expected-broken at run-5. Keep them as
historical controls until the complete proposal is implemented. Large logs,
XML and compiled artifacts remain outside Git.
