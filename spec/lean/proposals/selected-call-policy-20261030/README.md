# Selected restricted call policy: checked proposal kernels

The Lean checker in this package changes no production implementation. It supports the
[implementation proposal](../../../../docs/design/bidirectional-selected-call-policy-implementation-20261030.md)
for runtime `edb2e06cdb17eecafbe03415236bf56c57910239`.

```sh
python3 spec/lean/proposals/selected-call-policy-20261030/check.py
```

The checker uses the pinned `leanprover/lean4:v4.33.1`, one worker, one CPU,
768 MiB memory and a 90-second bound per command. Logs stay under ignored
`spec/lean/.lake/verification/selected-call-policy-20261030/`. The JSON receipt
binds the model, checker, proposal and reviewed runtime sources. Rerun it after
changing any model or the proposal.

There are **30 new named theorems** in SelectedCallPolicy.lean. The dependency
InputAdmission.lean has 28. The combined check audits **58 named theorems and
112 theorem/definition declarations**. Only `propext` and `Quot.sound` occur
in their axiom dependencies. There is no custom axiom, proof hole,
Classical.choice or noncomputable definition.

## Reference contract

For each original complete offered input F:

1. Apply persisted normal summaries to F, on every offer.
2. Evaluate the complete fixed-run initial-emission function E(F).
3. If E(F) is empty, retain no live input or initial packet for this offer.
4. Otherwise retain the complete original F in its exact caller route and
   deliver E(F) as canonical initial keys.

`Lookup` is an arbitrary deterministic function. The proof that moving its
result preserves the initial set does not require E to distribute over input
deltas. The first implementation queries whole offers and sends a packet even
when live subscription admission returns no fresh delta. It adds no caller
sent-initial history.

`Root` is a finite Boolean coordinate function. A route represents the full
callee/caller key, origin, call, stage, layer and typed header. Coordinates
preserve paths, tails, full marks and annotation memberships. This is literal
coordinate identity, not semantic AP prefix coverage.

## Checked claims

- Rejected offers leave live storage unchanged and create no packet.
- Accepted offers retain their full actual input and use fresh live deltas.
- An earlier rejected input is not activated by a later distinct accepted one.
- Moving complete admission from receiver to sender preserves emitted keys,
  live routes and saved semantic observation sets for the selected reference.
- The receiver admits exactly the fresh keys. Repeated packets cause no
  repeated initial starts and cannot erase an earlier start.
- Different caller routes remain distinct even when they emit the same key.
- Persisted replay does not depend on demand. Replaying an identical effect
  twice has the same observation set and still makes two replay calls.
- The selected phase order is persisted replay, demand lookup, registration,
  current replay, then initial send.
- A publication has a valid replay or notification channel when registration
  precedes replay. The model computes the channel as an executable witness.
- The callee performs no lookup. A naive caller gate plus receiver lookup
  costs two lookups on an eligible offer; the selected handoff costs one.

The lookup count is not a twofold saving against the current runtime: its one
query moves from callee to caller. Persisted replay can grow, and the model
does not predict the net project performance.

## Source and semantic limits

The finite state is a proof observation, not an extra runtime history. In
particular, `saved` collects semantic output memberships; runtime output and
observation stores remain the existing ones.

This model refines the user-selected demand authorization policy. It does not
prove equality with old current-summary callbacks outside demand. It does not
prove every whole-program finding remains present merely because some AP
summary is applicable. No hypothetical-summary compatibility guard is added.

The Kotlin adapters still need the implementation gates in the proposal:
exact query extraction, typed normalization, complete record replay, original
caller binding and suffix, native must demotion, ND origins, annotation-only
upgrades, observation identities, ZERO, run-2 static completion, immutable
packets and required delivery. The registration proof uses linearization
points; it does not verify locks, coroutines or cancellation in Kotlin.

Do not use these kernel proofs to change field transfer, conditions, marks,
layers, equality, record persistence or stopping. No production source was
modified or verified by this checker.

## Implementation adapter audit

The separate checker below binds the finite model to the implemented source
adapters and the completed test reports. It does not replace the model checker.

```sh
python3 spec/lean/proposals/selected-call-policy-20261030/check_implementation.py \
  --test-log /absolute/path/to/successful-implementation-tests.log
```

`implementation-checks.json` records these checks:

- The extracted persisted-record loop has the same Kotlin tokens as the base
  loop, after removal of aggregate diagnostic calls. Native and reversed
  record matching, temporary deduplication, and protection upgrades stay equal.
- AP, store, interpreter, key, and selected protocol sources retain the base
  bytes. Initial admission, boundary start, current summary application,
  native record application, return handling, and ZERO handling retain their
  base function bodies.
- The caller applies persisted records through its actor's SummaryApplier.
  This keeps existing call-service decorators in the dispatch path.
- The restricted caller queries the complete original offer once, stops on
  empty emission, subscribes before it delivers keys, and sends no raw LinkIn.
  The owner starts those keys without another demand query or field cut.
- Initial packets copy their key list. Owner routing retains cancellation and
  required-send checks. The selected tests cover immediate same-unit delivery,
  counted cross-unit delivery, duplicate starts, and cancelled or rejected sends.
- Passing test XML files and a successful suite command log are bound by hash.
  The complete-query differential test covers 432 submitted cases. Other
  tests cover repeated saved replay, reversed records, original caller paths,
  protection-only growth, empty gates, native must demotion, and ZERO calls.

The original `checks.json` remains a finite-model receipt. The implementation
receipt is a source and test audit. Token equality is not a proof of Kotlin
semantics. Tests do not prove all schedules or whole-project finding
completeness. Project measurements and baseline comparisons are separate
requirements. The implementation receipt must report FAILED while any
required source, model, or test gate is missing or has failed.
