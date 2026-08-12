# BaseOnly subscription and polymorphic-call mitigation

## 1. Delta-sound subscription routing

`MethodBaseOnlyAccessPathSubscription` is a candidate index. It may return a false-positive
subscription, but it must not reject a subscription that the canonical summary operation can
apply.

For a registered caller exit `F` and a newly published summary initial `I`, the authoritative
access-level predicate is:

```text
M = BaseOnlyAccessOps.matchPrefix(F, I)

ordinary summary event: M.emptyDelta || M.hasSuffix
empty-delta event:      M.emptyDelta
```

This is the same match used by `BaseOnlyFinalFactAp#delta`. Exclusions remain a downstream concern:
the index may retain a suffix candidate that a summary-initial exclusion later removes.

The packed three-slot `BaseOnlyInitialAccessIndex` supplies a conservative candidate set. F2F
subscriptions are inverted by caller exit so one index lookup selects all caller initials attached
to an applicable exit. ND subscriptions additionally map each exit to the initial-set storage
indices that contain it. Z2F uses the same exit index directly. Every emitted candidate is checked
with the predicate above.

The index and its leaf values follow the existing single-writer/multiple-reader contract:
three-slot maps and long sets are concurrent-read-safe; object sets and storage-index bitsets use
copy-on-write publication.

## 2. Polymorphic resolution

`JIRCallResolver` returns every contextual concrete and lambda alternative.
`JIRMethodCallResolver` processes those results directly; it does not insert a synthetic summary
method between the caller and the resolved targets.

A resolution-set proxy was evaluated and rejected. Its additional method-summary boundary merged
the results of broad generic dispatches such as `FutureCallback.onFailure` and
`DataValidator.validateDataImpl`. Contextual target sets also fragmented the proxy cache: one
source statement could produce dozens of synthetic methods, while most generated proxies were
used only once.

The ThingsBoard experiment measured the consequence:

- direct resolution: 104.6s prescan, 35.0s full scan, 14 findings, no high-memory events;
- resolution-set proxy: 109.5s prescan, 68.4s full scan, 13 findings, 32 high-memory events;
- compact one-statement proxy: 113.0s prescan, 95.1s full scan, 14 findings, 56 high-memory events.

Changing the proxy CFG did not remove the regression. The expensive operation was aggregating a
broad target set into another summary and then applying that merged summary to callers.
Direct resolution preserves each `MethodWithContext`, keeps lambda subscription in the original
caller context, and avoids that extra aggregation boundary.

## Verification

- Subscription tests compare F2F and ND results with a canonical-delta scan for ordinary and
  empty-delta events.
- Packed-shape index tests assert that routing contains every pair accepted by canonical delta.
- Tree/BaseOnly differential storage tests assert BaseOnly does not drop the corresponding Tree
  subscription.
- Dataflow samples cover direct resolution of two concrete implementations and a
  concrete-plus-lambda implementation in BaseOnly mode, in addition to the existing identity,
  transforming, captured, and passed-lambda cases.
