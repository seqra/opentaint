# FLOW-family control boundary

12 November 2026. Current campaign target: `1025a197…`, native demand row
`95b0a29e…`. Runtime source pin: `14d7b63369d94f49d4c551be8405ed7719f267cc`.
This is an operator audit. It does not classify the target or select a change.
The latest compatible OWASP project capture reached run-11, completed run-11
and accepted run-11. No new project scan was made. The tests below use small
native fixtures at run-3 and run-13. They do not provide a multi-run necessity
example or use the temporary iteration limit.

## 1. AP output coverage does not cover every control effect

Pinned `BlockRunState.emitTarget` has this rule:

```text
emitTarget(P, target):
    reject a FLOW origin
    reject NormalTarget in backward analysis
    ignore an already persisted identical NormalTarget
    retain the new raw Target row
    if target is NormalTarget OR run1 OR demand.acceptsTarget(P):
        publish target
```

Thus, a new forward NORMAL sink result bypasses Target C5. A DATA/Data demand
row can admit a concrete initial which discovers that result. It does not
need a separate DATA/Zero control row.

The native fixture uses this method and rule:

```java
// Entry sink rule: CM(p, T).
Object m(Object p) {
    return p;
}
```

The retained NORMAL provider is `p.$/T -> ret.$/T`. The only current demand is
`p.$/T -> ret.$/T`. The submitted fact is `p.$/T,NORMAL`.

```text
Saved replay:       ret.$/T,NORMAL
C2:                 p.$/T,NORMAL
Entry sink:         p.$/T -> NormalTarget(id)
Target permission:  acceptsTarget(p.$/T) = false
Published Target:   p.$/T -> NormalTarget(id)
AP summary:         p.$/T -> ret.$/T,NORMAL
```

After removal of the AP row, saved replay still gives the same `ret.$/T`.
C2 emits no initial. No new NormalTarget is produced. Every AP summary in
the retained-row case equals the saved NORMAL provider. Thus, coverage of
all AP output alone is insufficient for a concrete C2-family retirement.
This is a native control counterexample, not a sink-loss proof for the
current FLOW target.

## 2. A FLOW-only C2 family has a stronger local invariant

A FLOW demand retains FLOW in `RestrictedInitialPolicy.boundMark`.
Its companions are also FLOW. A concrete actual fact does not change this.
The fixture repeats section 1 with demand `p.*/FLOW -> ret.*/FLOW` and the
same submitted `p.$/T,NORMAL`. C2 emits `p.$/FLOW,NORMAL`; the sink does not
fire. FLOW summary normalization gives the retained NORMAL provider
`p.*/FLOW -> ret.*/FLOW`. The saved provider still returns `ret.$/T,NORMAL`.

The pinned operators support this local invariant after run-1:

| Operator | FLOW behavior |
| --- | --- |
| Primitive edge application | `EdgeApplication.flow` emits FLOW. A concrete mark premise has no FLOW result. |
| Current/saved summary match | `satisfyingPart` rejects a concrete premise for FLOW input. |
| Summary application | `applySummaryPart` requires a FLOW result for FLOW input. |
| Mark condition | `markCheckFacts` returns `None` for FLOW after run-1. |
| Cleaner, field cut and filter | They retain FLOW kind or discard the result. |
| Mark request | `BlockRunState.needGroups` returns after run-1. |
| Sink witness | No accepted concrete condition comes from this FLOW lineage. |
| Target publication | `emitTarget` rejects a FLOW origin. |
| Unconditional source/backward sink seed | It requires Reach/ZERO. A FLOW initial does not create that control input. |
| End-fact trigger | END_FACTS stages are ignored in the pinned runtime. |

An accepted backward source transfer also needs its selected concrete mark;
a FLOW packet cannot match it. Merely visiting that source does not create
a source hit or permission. This audit does not claim that AP output coverage
has already been proved for the current target.

## 3. Retained NORMAL ND contributors need a current accepted leaf

`NormalRuleContributors` construction takes a snapshot. It schedules no
initial, fact or rule action. Its only `restoreOnce` caller is
`RunMethodLocalServices.acceptedLeaf`. That caller runs after a current
`MarkCheck.Holds`. A location visit or a FLOW mark check is insufficient.
The facade is also disabled in backward analysis.

The native carrier test first checks both leaves of `CM(p,T) AND CM(q,U)` in
run-1 FULL. It freezes the actor and publishes the two actual retained
NORMAL contributor rows. It does not hand-build a cache certificate.

```text
New run-13 actor:                 restored rows = 0; no Target
FLOW visit at the exact ND site:  restored rows = 0; no Target
Concrete p/T visit at that site:  restored rows = 2; one NormalTarget
```

The last case can restore a complete old cube before it adds the new leaf.
It does not need a new `q/U` leaf. The current accepted `p/T` leaf is still
required to activate the cache. This preserves the selected ND reuse rule.
It does not create a local FLOW-to-concrete path.

## 4. Shared block routing is a separate proof boundary

Pinned `MethodBlockRuntime.offerChild` can register a new real target of a
canonical normal interface. When it does so, it starts every already
admitted initial of that block at that target. This includes concrete or
ZERO initials if another lineage admitted them.

For a complete method-root demand family with only FLOW entries and no
Zero/Target entry, every root initial is FLOW. The local type rules above
then keep its child offers FLOW. Its own target registry therefore has no
concrete or ZERO initial to replay.

A foreign callee can have other concrete or ZERO admissions. This audit has
not proved that its target-registration work is independent of the removed
FLOW call. Nor does it provide a counterexample where this registration
causes sink loss. The existing `LoopBlockEmptyReverseJoinTest` covers a late
real predecessor and already admitted ZERO, but does not prove the proposed
retirement invariant.

A uniform closed-family proof must account for this registration effect or
prove that independent retained arrivals always perform the same work.
Do not turn a missing counterexample into a claim that the effect is absent.
The eligibility guard must remain edge-only; source/CFG properties may be
used to prove a native invariant, but must not become project guards.

## 5. Static side channels after run-1

The global static write-pool hook in `emitOperationResult` requires
`config.run1`. Requests, static owner effects and static call interest use
the same run-1 service. The run-1-to-run-2 static completion is unavailable
after run-2. They do not give a new pool side channel at the H11 removal point.
Later static AP output still belongs in the complete AP service proof.

## 6. Evidence and remaining obligation

External case:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/
  redundant-demand-rows-20261112/cases/ap-family-control-boundary-v1/
```

`ApControlBoundary.java` checks all eight kept/removed, concrete/FLOW and
run-3/run-13 cells. `CarrierBoundary.java` checks actual ND carrier capture
and activation. `execute.txt` and `carrier-execute.txt` contain their terminal
PASS markers. Class-origin checks bind the operators to the source-built
pinned runtime and fixtures to their preserved source-pin build. Fourteen
production source snapshots are stored with hashes. Earlier failed preparation
attempts are preserved. No production file was changed.

There is no new redundancy certificate. A proposed whole FLOW-family rule
still needs a uniform AP service cover, persistence/delivery preservation,
and the shared routing proof. The local NormalTarget bypass and carrier
checks establish where that proof must differ from a concrete-family proof.
