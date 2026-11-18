# Cleaner-free termination counterexample search: work in progress

14 November 2026. The active goal is to find a counterexample under
[the latest coverage and reply-packet proposal](../design/bidirectional-same-lane-uniform-termination-20261114.md).
Require no CFG loops, call recursion, special pass rules or cleaner rules.
Production is unchanged. The search completed on 15 November with the
[nested saved-replay counterexample](bidirectional-nested-saved-replay-nontermination-20261115.md).
This file retains the rejected candidates and bounded search history;
the linked report contains the accepted example, annotations and proof.

## Rejected candidates

A three-call helper with two branches looked stationary in an incomplete
model:

```java
Node choose(Node x, boolean b) {
    if (b) return x.f.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
```

Its source marks only an exact `x.g` point. The incomplete search retained
forward rows `x.f.* -> ret.f.MAY,D` and `x.f.f.* -> ret.f.MAY,D` through
run-23. It omitted delegation at unknown reads after earlier known-prefix
reads. The complete child family must also cover that first read from the
original symbolic suffix. Adding that selected routing removes this
candidate. The old run-23 trace must not be called nontermination evidence.

A second family added a temporary round trip: write k `f` prefixes and
then read k `f` fields, alongside a reader and writer. Initial exploration
also failed to compact caller-visible MAY/NE results. Keeping finer heads
in the local refinement ledger does **not** permit delivering all those
heads as independent caller facts. Correcting delivery makes the tested
k=2 through k=7 cases finish, respectively, at run-5, run-7, run-7,
run-9, run-9 and run-11. The tested source is root MUST; this is a scalar
reference experiment, not a native NE implementation.

## Bounded search evidence

[Exploratory scripts](../../scripts/demand_experiments/no-cleaner-counterexample/)
compose ordinary single-field reads and writes, apply per-operation global
cuts and paired relative C5, retain NORMAL records, run the one-level query
plan, compact executable MAY results separately from the retained demand
heads, and perform same-layer MUST reply compaction and uniform NE coverage.

| Search | Tested configurations | Observation |
| --- | ---: | --- |
| Single owner, root sink | 1,500 | No accepted survivor |
| Single owner, concrete source/sink prefixes | 4,000 | No accepted survivor |
| Two owners, varied call order and repeated calls | 10,000 | No accepted survivor through run-23 |

The single-owner searches used run-19 as their candidate screen. The
multi-owner search used run-23. Finite survival is only a prompt for a
separate proof; stopping before the screen is only this model's result.
These counts are not exhaustive over programs or even over the finite
prefix space. There is no claim that this proves termination.

The search model has no mark-changing or conjunctive rule semantics, real
field exclusions, aliases, statics, multiple output bases, or full native
service correspondence. Some C2 possible-binding and projection details
are represented only by the earlier scalar model. Any new survivor must
be retraced with the selected contract and proved constructively in Lean.
Do not promote this search model into a new semantic specification.

## Search direction used

The next checks investigated complete nested method/block ownership, multiple output
bases and ordinary source/sink predicates. Check every native/record
route, all paired rows and the actual complete handoff. No hypothetical
MAY producer, custom predefined summary or hidden AnyField-target pass
is an acceptable replacement for the requested code example.

A termination counterexample must contain the code, the per-run annotations
in the requested direction-sensitive layout and an uncapped induction of
fresh retained demand. It must survive the latest same-lane uniform law,
complete reply folding, child delegation, retained deeper heads, normal
precoverage and saved replay. The accepted nested-call package now meets these requirements under the
specified unchanged saved-replay policy.

## Other checked directions and cautions

- A field overwrite at a fixed shallow head is eventually disjoint from
  a deeper surviving fact, or kills that branch in both directions. It
  does not automatically recreate the earlier partial-cleaner cycle.
- A conditional source returning a fresh uniformly marked object does
  not preserve the input's arbitrary suffix. Its backward CM guard and
  fixed GEN target must be traced; substituting it for the ordinary
  reader in the old pumping proof is invalid.
- A delayed NORMAL reader can start stale work in a different publication
  batch, but that alone is not an infinite-run proof. Later retained
  NORMAL STAR reader records can make subsequent runs terminate.
- Possible wrapper bindings are in section 4 of bounded refinement. The
  original ancestor-STAR rejection is not the complete active contract.
- Ordinary JVM default getter models use named storage/element STAR
  edges, not a free intrinsic-MAY producer. Do not invent such a producer
  to force the search result.

The positive-prefix search results suggest investigating whether that
narrow subclass has a progress argument. They do not prove one and do
not close the requested broader counterexample search.

## Iteration positions

Latest rejected-candidate screen: **run-23**. The accepted reference reaches
**run-31**, with an uncapped constructive recurrence proof. Cold run-1 through
run-9 states are checked; stationary run-9/run-10 packets are proved for all
later limits. Three native operator tests pass at field limit 8 (run-9
geometry), not an integrated native NE run. No new project scan was run. Historical
project reached/completed/accepted-forward positions remain OWASP
**run-11/11/11**, Conductor **run-8/7/7**, Stirling-PDF **run-11/10/9**.
The cleaner-free counterexample goal is complete. The fresh checker passes
**69 new theorems; 542 audited declarations in 32 modules** including the
previous models and reused ZERO/Target kernel. Production remains unchanged.
