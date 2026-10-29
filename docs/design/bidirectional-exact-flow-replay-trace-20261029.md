# Closed trace for an uncovered exact FLOW replay

Date: 29 October 2026. Source reviewed: `7b0a3eed5`.
Latest modeled iteration: **run-3**, forward, field limit 2.
This is a trace of the proposed domain with the current exact-target
application cell left unchanged. It is not a measured JVM failure.
Current production still rejects the new typed abstract EXACT shape.

The trace checks the question raised during the
[implementation proposal](bidirectional-summary-demand-workload-implementation-20261029.md).
It includes initial admission, source seeding, live summaries, completed-run
records, caller bindings, C5 and raw persistence. It does not assume that a
standalone overlapping input appears without an emission path.

## 1. Program and complete modeled transfers

Use distinct Outer, Inner, Leaf, OpaqueOutput and Pair types. Only the stated
bindings and pass rules supply taint flow. No additional alias relation is
needed. Both methods are ordinary analyzed methods with one fixed MethodKey
each; reversing their call stages retains those keys.

```java
main() {
    q.f.h = sourceAllT();
    sinkAnyT(q.f.h);               // independent source-seed route
    sinkExactT(helper(q));         // independent exact helper probe
    pair = wrapper(q);
    sinkExactT(pair.a);
    sinkAnyT(pair.b);
}

wrapper(q) {
    a = helper(q);                 // whole q; do not substitute helper(q.f)
    b = opaqueMay(q);
    return makePair(a, b);
}

helper(p) {
    return p.f;
}
```

The source assigns T to every descendant of the Leaf at `q.f.h`. It does
not mark the Inner object at `q.f` itself. The exact sink checks only the
root at its given position. The ANY sink can check a descendant.

The complete nontrivial pass micro-edges are:

```text
helper read:   p.f.STAR/FLOW -> helperRet.STAR/FLOW
opaqueMay:     q.STAR/FLOW -> b.ANY/FLOW
makePair:      a.STAR/FLOW -> wrapperRet.a.STAR/FLOW
               b.STAR/FLOW -> wrapperRet.b.STAR/FLOW
call bind-in:  caller q.STAR/FLOW -> callee p.STAR/FLOW
call bind-out: callee ret.STAR/FLOW -> caller result.STAR/FLOW
```

Ordinary argument preservation and ZERO_KEEP also exist. `makePair` is a
declared pass model, not a pair of strong overwrite instructions. The MAY
target is a legal supplied pass rule. Its output is `b`, not `a`.
The source edge is `ZERO -> q.f.h.MUST/T`. E and mark exclusions are empty.
There are no statics, ND edges, conditional sources or cleaner operations.

N means NORMAL; D means DEMAND. Tail MUST means `[any-taint]`.

## 2. Run-1, limit 1

```text
source result before limiting: q.f.h.MUST/T, D
source result after limiting:  q.f.ANY/T, D
wrapper supplied argument:     q.f.ANY/T, D
wrapper abstraction:           initial q.STAR/FLOW; start q.STAR/FLOW, N
```

Main has ZERO premise. Run-1 moves the source's concrete output to DEMAND.
The path cut removes the second counted field and keeps a MAY fact at f.

The wrapper binds the whole argument into helper:

```text
wrapper initial:       q.STAR/FLOW
before helper:         q.STAR/FLOW, N
helper supplied fact:  p.STAR/FLOW, N
helper abstraction:    initial p.STAR/FLOW; start p.STAR/FLOW, N
helper read p.f:        helperRet.ANY/FLOW, D
```

The ancestor input at p loses the correlation at the read of f. There is
no `p.f.STAR/FLOW` helper initial in this run.

The relevant raw rows are:

| Method | Premise | Conclusion | Layer |
|---|---|---|---|
| helper | ZERO | ZERO | N |
| helper | p.STAR/FLOW | p.STAR/FLOW | N |
| helper | p.STAR/FLOW | helperRet.ANY/FLOW | D |
| wrapper | ZERO | ZERO | N |
| wrapper | q.STAR/FLOW | q.STAR/FLOW | N |
| wrapper | q.STAR/FLOW | wrapperRet.a.ANY/FLOW | D |
| wrapper | q.STAR/FLOW | wrapperRet.b.ANY/FLOW | D |

The argument identities and ZERO rows persist as NORMAL records. The return
rows become demand. No NORMAL helper return relation exists here.

The relevant incoming run-2 demand pairs are:

```text
helper:  entry helperRet.ANY/FLOW;    exit p.STAR/FLOW
wrapper: entry wrapperRet.a.ANY/FLOW; exit q.STAR/FLOW
wrapper: entry wrapperRet.b.ANY/FLOW; exit q.STAR/FLOW
```

The main-level sinks receive concrete T by applying these FLOW summaries
to the actual concrete source input. They do not require concrete helper
or wrapper initials. Run-1 emits concrete initials only for actual requests;
the trace does not assume those requests exist in these sink-free methods.

## 3. Run-2, limit 1: source and exact record bootstrap

### 3.1 The source is genuinely seeded

The independent `sinkAnyT(q.f.h)` starts a concrete T requirement in main.
Limiting gives `q.f.ANY/T, D`. It can reach the reversed source at f.h as a
partial requirement. The concrete mark gate passes; the source-hit event
records `sourceAllT`. This gives run-3 its source seed without depending on
an abstract wrapper/helper path crossing a concrete source gate.

### 3.2 The direct helper probe supplies a concrete exact input

```text
sinkExactT(helper(q)) seed:          result.EXACT/T
reverse return binding:             helperRet.EXACT/T
helper demand entry:                helperRet.ANY/FLOW
selected emitted helper initial:    helperRet.EXACT/FLOW
starting edge:                      helperRet.EXACT/FLOW -> itself, N
```

This uses the explicitly selected ANY-demand/exact-concrete-input rule.
It does not need an abstract actual to start helper analysis.

Reverse the ordinary field-read edge:

```text
helperRet.STAR/FLOW -> p.f.STAR/FLOW
```

Applying the exact requirement at the matching return prefix gives:

```text
raw helper summary:
    helperRet.EXACT/FLOW -> p.f.EXACT/FLOW, N
```

C5 accepts this pair. Its initial is an output of the helper ANY demand.
Its result lies under the demanded `p.STAR/FLOW` exit. The new EXACT FLOW
representation is needed, but no application to STAR has occurred here.

The live summary can answer wrapper's standing exact return input. It need
not wait for persistence and does not need another successful helper C2
admission for that abstract input. At the completed run-2 barrier, the same
raw normal row becomes a native backward record.

### 3.3 Wrapper A route becomes an exact record

```text
main exact A requirement:        wrapperRet.a.EXACT/T
wrapper entry demand:            wrapperRet.a.ANY/FLOW
selected wrapper initial:        wrapperRet.a.EXACT/FLOW, N
reverse makePair A binding:      a.EXACT/FLOW, N
helper return input:             helperRet.EXACT/FLOW, N
live helper summary answer:      p.f.EXACT/FLOW, N
reverse whole-q input binding:   q.f.EXACT/FLOW, N
raw wrapper summary:
    wrapperRet.a.EXACT/FLOW -> q.f.EXACT/FLOW, N
```

C5 accepts the row under the A pair. It becomes a native backward record.
It is NORMAL, so it supplies no next-run demand for this A route.

### 3.4 Wrapper B route keeps a coarse demand

```text
main B requirement:              wrapperRet.b.ANY/T
wrapper entry demand:            wrapperRet.b.ANY/FLOW
selected wrapper initial:        wrapperRet.b.ANY/FLOW, D
reverse makePair B binding:      b.ANY/FLOW, D
reverse opaqueMay:               q.ANY/FLOW, D
raw and published summary:
    wrapperRet.b.ANY/FLOW -> q.ANY/FLOW, D
```

The B requirement can pass the unrelated helper call through its argument
identity, retaining DEMAND. An argument-base packet does not match helper's
return-base demand. It does not start a `p.f.STAR/FLOW` analysis.

The forward handoff therefore contains this wrapper pair:

```text
entry q.ANY/FLOW; exit wrapperRet.b.ANY/FLOW
```

At the barrier, helper's backward exact record reverses to this forward
read view:

```text
premise p.f.EXACT/FLOW; result helperRet.EXACT/FLOW, N
```

Wrapper's proper A record reverses to:

```text
premise q.f.EXACT/FLOW; result wrapperRet.a.EXACT/FLOW, N
```

That wrapper record cannot match the real `q.f.h.MUST/T`: its exact premise
ends at f, while the supplied mark is below h. Thus it does not already
justify a root mark on A.

## 4. Run-3, limit 2: the broad FLOW input is emitted legally

The independent concrete source hit enables the source again:

```text
actual wrapper input:        q.f.h.MUST/T, N   // depth 2 fits
wrapper demand entry:        q.ANY/FLOW
selected wrapper initial:    q.f.STAR/FLOW
start edge:                  q.f.STAR/FLOW -> itself, N
```

The first new field f resolves the current ANY. The remaining h is not
consumed. This is an abstract FLOW STAR initial, not concrete STAR/T.
The concrete-STAR DEMAND start rule does not apply to it.

The call passes the whole q:

```text
before helper call:   q.f.STAR/FLOW, N
bind q.STAR -> p.STAR with suffix f
helper supplied fact: p.f.STAR/FLOW, N
```

No new helper nonzero initial is needed. Its completed run-2 record is
available for native replay at the caller, independently of new callee C2
emission. This is the same mechanism that keeps NORMAL records reusable.

## 5. The precise application cell under review

```text
existing helper read view:
    p.f.EXACT/FLOW -> helperRet.EXACT/FLOW, N

actual at this call:
    p.f.STAR/FLOW, N

same base and same prefix f
geometric inside matching accepts the exact premise
```

If the current Kotlin target-EXACT application cell is left unchanged when
the abstract EXACT guards are relaxed, it returns:

```text
helperRet.EXACT/FLOW, N
```

The cell drops the caller's bound suffix. The old formal STAR/Universe
cell is different and is not a runtime implementation here. This trace
does not silently introduce Universe or choose another repair.

Binding the return and the Pair A output gives this raw wrapper edge:

```text
q.f.STAR/FLOW -> wrapperRet.a.EXACT/FLOW, N
```

The subsequent B transfer has another base and cannot kill A. It creates
`wrapperRet.b.ANY/FLOW, D`, a separate result.

## 6. Why neither subsumption nor C5 removes the issue automatically

No stored NORMAL STAR return relation covers the new exact application:

| Available NORMAL relation | Why it is not a cover |
|---|---|
| helper p.STAR -> p.STAR | Argument result base, not helperRet |
| helper helperRet.EXACT -> p.f.EXACT, backward | Exact record, not the absent STAR return relation |
| wrapper q.STAR -> q.STAR | Argument result base, not wrapperRet.a |
| wrapper wrapperRet.a.EXACT -> q.f.EXACT, backward | Exact record with different native direction |
| ZERO identities | Different premise/result bases |

The broad return rows in run-1 are DEMAND. Wrapper B's result is at b,
not a. Optional concrete-T rows from requests also cannot provide an
all-mark NORMAL FLOW STAR return cover.

C5 sees the run-3 wrapper B pair:

```text
entry q.ANY/FLOW; exit wrapperRet.b.ANY/FLOW
```

It accepts the emitted initial `q.f.STAR/FLOW`, but rejects publication of
the `wrapperRet.a.EXACT/FLOW` result because a and b are apart. It retains
the B demand result.

However, current summary processing adds the raw summary before C5.
Completed-run persistence reads raw NORMAL summaries. Thus the false
NORMAL A relation is still eligible to become a native forward record.
This conclusion does not require a speculative later report trace.

## 7. Concrete false pair

The false raw summary claims this NORMAL pair:

```text
input:   q.f.h / T
output:  wrapperRet.a / T
```

The actual helper read preserves h:

```text
q.f.h / T -> helperRet.h / T -> wrapperRet.a.h / T
```

There is no T on A's root. The independent MAY branch supplies only B.
The selected C2 algorithm really emitted the first-field FLOW initial,
and the helper exact record was built from a real concrete probe. The
remaining issue is application of that record to a broad FLOW input.

## 8. Validation boundary

This is a proposed-domain scalar AP trace, not a current production bug
or new project measurement. It assumes only the selected abstract EXACT
domain admission and the unchanged application/matching path being tested.
It does not assume a repair, an unavailable normal cover, automatic T
requests, or an actual packet with no admission path.

The [embedded trace](../reports/data/bidirectional-closed-exact-replay-20261029.json)
contains all phase rows, source hashes, C2/C5 decisions, persistence checks,
and the exact false pair. The implementation proposal must keep this case
explicit until the application behavior is selected and proved.

The `ClosedExactReplay` namespace in
[RestrictedInitialPolicy.lean](../../spec/lean/proposals/initial-emission/RestrictedInitialPolicy.lean)
checks the complete finite operator trace. Its 11 theorems derive the
run-1 observations and demands, the independent source hit, the helper
record, the wrapper demands, and the run-3 replay. They check both the C5
rejection and raw persistence, and prove that the false pair is absent from
all declared wrapper routes. The executable check returns `true`.

The certificate uses the generic AP binding, limiting, restriction and
handoff operators. It models the current Kotlin target-EXACT replay cell
explicitly, because the older Lean STAR/Universe cell is different. MUST
certainty at admission is an explicit input flag; no new JVM payload is
assumed. This is a finite model of the stated transfers and schedule, not a
proof of the full driver, alias closure, or termination. All-theorem audits
use only `propext` and `Quot.sound`. The embedded trace includes the full
audit output and model hash.
