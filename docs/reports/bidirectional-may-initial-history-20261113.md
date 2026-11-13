# Why MAY initial premises were removed

13 November 2026. Historical investigation at
`374fa3c6f5f73b24ccca00fc829da8c83a322d3f`. No analyzer change or new
policy selection. The demand campaign remains paused.

**Finding:** removing MAY initial premises was selected to obtain correlated,
reusable NORMAL FLOW relations and repair a getter recovery failure. The
reviewed history does not contain a whole-program counterexample to the
new proposal “MAY demand plus MAY input starts a MAY premise, whose summary
can apply only to MAY inputs.” The old failure concerns a larger combination
of admission, layers and record availability. It does not prove that every
possible MAY-premise policy must fail.

No project scan was run. Historical reached/completed/accepted-forward
positions remain OWASP **run-11/run-11/run-11**, Conductor
**run-8/run-7/run-7**, and Stirling-PDF **run-11/run-10/run-9**.

## 1. The original policy allowed MAY initials

The [original AP emitter](../../spec/ap.md) and
[frozen baseline contract](../../spec/subsumption-redesign-baseline-20261107.md)
allowed MAY initial premises after run-1. The simple run-1 grammar excluded
them; there was no universal no-MAY-premise invariant.

Immediately before the final redesign, the native scalar policy contained:

```text
demand x.[any], actual x.[any]   -> initial x.[any]
demand x.f.[any], actual x.[any] -> initial x.f.[any]
demand x.[any], actual x.*       -> no initial

start x.[any]/FLOW -> x.[any]/FLOW, DEMAND
start x.[any]/T    -> x.[any]/T,    DEMAND
```

These are source-confirmed cells in `44065531e^` and the historical
`7069fe2d7` runtime. The ordinary data transfers then inherited this MAY
uncertainty. MUST was separate: it represented definite uniform input,
and its own matching guard required actual MUST support.

## 2. The concrete motivation: the getter route

The [6 November saved-record investigation](bidirectional-getter-saved-record-gap-20261106.md)
checked a complete native run, including the entire saved-record directory.
The relevant body was:

```java
// run-2 submitted and initial: ret.[any]/FLOW, DEMAND
Object getG(Object p) {
    return p.g;
}
// Produced: ret.[any]/FLOW -> p.g.[any]/FLOW, DEMAND.
// No NORMAL input-to-return record was saved.
```

The field `g` fit limit 1. MAY was inherited from the start, not created by
truncating an excessively long `g` path.

The next forward boundary was:

```text
run-3 demand:    (entry p.g.[any]/FLOW; exit ret.[any]/FLOW)
submitted:      p.g.*/FLOW, NORMAL
saved replay:   no return relation is available
old C2:         rejects same-head STAR under MAY demand
result:         no current getter analysis
```

The complete program naturally stopped at **run-5** with zero required
NORMAL findings. A pre-canonical control had the same miss. This was not
explained solely by the later packet-canonicalization change.

The [7 November audit](../design/bidirectional-star-initial-emission-audit-20261107.md)
tested replacement by STAR:

```java
// run-2 initial: ret.*/FLOW, NORMAL
Object getG(Object p) {
    return p.g;
}
// Produced: ret.*/FLOW -> p.g.*/FLOW, NORMAL.
// Saved forward view: p.g.*/FLOW -> ret.*/FLOW, NORMAL.
```

This relation has correlated suffixes. Applying it to a caller MAY fact
still produces a DEMAND result; the NORMAL conditional relation does not
confirm the caller's uncertainty.

Both tested conversion strategies recovered the original finding in
**run-3** and completed at **run-5**. One converted FLOW starts only; the
other converted both FLOW and concrete starts. The concrete STAR start
remained DEMAND. The universal ban was therefore broader than the
FLOW-only repair demonstrated necessary by this particular experiment.

The historical evidence establishes a need for a working NORMAL route or
another correct recovery route. It does not establish that banning every
MAY premise is the only way to provide one. In particular, the old failed
cell also rejected STAR admission; keeping MAY starts while admitting a
separate STAR start is a distinct policy, not that recorded old control.

## 3. How this became the current contract

| Stage | Decision or result |
| --- | --- |
| Original AP and pre-redesign runtime | Restricted MAY initials are legal. |
| 7 November conversion audit | FLOW-to-STAR creates reusable NORMAL relations. The user then selects conversion for concrete starts too. |
| Nested-call experiment | A conversion-only patch breaks wrappers because an outer STAR reaches an inner MAY demand whose old STAR cell rejects it. |
| STAR_OR_ANY proposal | Keep STAR data transfer with special MAY-like admission; erase the marker at summary boundaries. |
| STAR_OR_ANY full gate | Public erasure loses refinement guidance in two-loop and deep-loop cases. The successive-loop test stops at **run-3** without its finding; a separate deep-loop finding fails at **run-5**. |
| Combined 7–8 November redesign | Select ordinary STAR, no MAY initial premise, no new tail, and accept same-head STAR under MAY demand. Include the other selected C2/C5, companion, cleaner and loop repairs. |
| Implementation `44065531e` | Replace the two MAY emission cells, add the STAR cell and complete C2 families, update C5 image checks, and reject MAY in initial legality. |

The [nested-call report](bidirectional-star-initial-nested-calls-20261107.md)
is especially relevant: the old MAY-preserving policy passed all four
getter programs at **run-3**. The conversion-only copy lost three wrapped
cases, also ending at **run-3**. A separate concrete converter wrapper
likewise passed with MAY preservation and failed with conversion alone.
These results are evidence against an incomplete conversion, not evidence
that MAY preservation itself must be prohibited.

The [public-marker handoff report](bidirectional-star-or-any-handoff-gap-20261107.md)
explains the later marker failure. The
[final combined spec](../../spec/edge-subsumption-initial-emission-demand-intersection.md)
then explicitly selects the no-MAY-premise rule. The
[baseline summary](../../spec/subsumption-redesign-baseline-20261107.md)
identifies it as a new redesign decision, rather than an original AP rule.

## 4. Was the proposed MAY-only summary policy refuted?

The proposal under discussion is:

```text
C2(x.[any]/M, x.[any]/T) -> initial x.[any]/M

For an edge with that MAY premise:
    match only permitted MAY actuals
    do not use it as an ordinary STAR or MUST summary
```

No whole-program test or proof of a finding loss for exactly this combined
policy was found in the reviewed AP spec, getter captures, conversion audit,
nested-call tests, marker model, handoff report or final redesign dossier.
This is an audit result, not a soundness proof for the proposal.

Two distinctions matter:

1. **The old matcher was not this strict policy.** Historical
   `Summary.kt.satisfyingPart` combined `applicablePart` and `insidePart`.
   A MAY endpoint could select a same-head STAR with empty exclusions
   through `insidePart`; the shared any payload also included MUST.
   Restoring old C2 output alone therefore does not implement MAY-only
   applicability. MUST's definite-support guard cannot simply be renamed.
2. **The historical `mayOnly` theorem is a different experiment.**
   `StarOrAnyDesignProofFixed.lean` uses that name for interpreting a
   decorated STAR through a virtual MAY view, then emitting a decorated
   STAR. Its negative theorem compares an API-only abstract EXACT demand
   explicitly not proved reachable under the snapshot grammar. It does
   not test a real MAY initial premise with MAY-only summary application.

The original getter failure remains a required regression test. Its
recorded route fails through the combination of a DEMAND MAY start, no
saved NORMAL return relation and rejected subsequent STAR admission.
Those facts do not isolate the new MAY-only policy as the cause.

## 5. Consequences for the next investigation

Reconsidering the universal ban is a semantic design change. It can be
investigated without assuming that the historical experiments already
rejected it. Keep separate decisions for:

```text
MAY premise emission and start layer
MAY-premise matching and application
other C2 cells, including MAY-demand + STAR-input admission
C5 image, paired output restriction and persistence
handoff of MAY guidance through wrappers and loop blocks
```

The principal controls are the original four-method getter failure,
the wrapped getter/converter positives, the two-loop handoff failure, and
the [new truncation-evidence wrapper](bidirectional-truncation-evidence-20261113.md).
That last baseline reaches **run-7** with its finding; the tested direct
STAR filter stops at **run-5** without it. A new MAY-only policy has not
been run on these controls.

This history does not select a new tail, initial layer, matching rule,
FLOW companion, or production patch. It records why the earlier rule was
chosen and the limit of the evidence for keeping that rule.
