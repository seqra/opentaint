# Use the existing child cover with real field exclusions

15 November 2026. Approach under [proof-guide.md](../../spec/proof-guide.md).
Production is unchanged. This extends
[prepared-child saved replay](bidirectional-prepared-child-saved-replay-20261115.md)
to the [ordinary-overwrite example](../reports/bidirectional-overwrite-saved-replay-nontermination-20261115.md).
It adds no new initial query, caller offer, partition or cross-call evidence.

**A real field exclusion narrows a reader's inputs. It does not invalidate
its existing first-field child cover.** Use native matching with all real
exclusions intact. For a supported matched contribution, use the already
prepared children even when the operand or NORMAL record has field exclusions.

The complete references naturally stop at run-3 through run-15. The new
overwrite case stops at **run-9**, with the NORMAL observation retained and
no DATA or Target demand. Broader diagnostic variants reach **run-19**.
See the [report](../reports/bidirectional-exclusion-aware-child-replay-20261115.md).
These results establish termination of the supplied reference examples;
they are not a universal native termination theorem.

## 1. Current and proposed behavior

The previous routing requires empty real field exclusions on the operand
and both ends of its saved NORMAL record. Ordinary writes can produce:

```text
Wg: x.*       -> ret.f.f.* {g}, N
Rg: x.f.f.*   -> ret.*     {g}, N
```

With a wrapper, a conditional `x.*` query can apply the opposite Rg and
renew `x.* -> ret.MAY,D`. The old empty-E gate keeps this contribution,
even though the query's first-field children are ready. Four MAY demand
rows then repeat. Increasing the global field limit does not resolve them.

Remove only those three empty-field-exclusion tests. Keep the existing
requirements on the raw owned query, suffix correlation, direction,
FLOW marks, mark exclusions, layer, protection and qualified child service.
In particular, the supported raw STAR query still has empty field E.
There is no C2 change to copy a parent exclusion into a deeper initial.

```text
owned query:         P.* -> a.*, NORMAL FLOW
operand:             a.* {g}
saved opposite R:    a.f.f.* -> b.* {g}, NORMAL FLOW
already ready:       P.f.$ and P.f.* under the same original demand row

before: parent produces P.* -> b.MAY,D; child produces P.f.* -> b.MAY,D
 after: omit only that parent reply; keep the child reply and all other work
```

This is a semantic change to intermediate refinement guidance. It can
change per-run counts and confirmation timing. The intended correctness
criterion is eventual refined observations, with no hard iteration limit.
It is not a new global summary subsumption rule.

Unchanged mechanisms are C2 and its companion queries, paired C5,
`FL(Dc)+1` and `FL(Dp)+1`, real field cuts, primitive transfers, NORMAL
precoverage, uniform/protected coverage, current-summary matching,
original input enrollment, rule handling and ZERO/Target handoff. Saved
records still apply to original actual caller inputs before current demand
lookup. No source, observation, cleaner or field-write handler is skipped.

## 2. The algorithm

Use the same frozen prepared plan that the existing primitive and saved
reader routing already use. Its child cover must be valid for every
qualified consumer of the deduplicated raw query, including later offers.
A child over the original budget, missing child, incompatible physical port,
or missing native service proof leaves the old contribution in place.

```text
callInsideOwnedQuery(rawInitial, originalOperand, preparedPlan):
    enrollOriginalCalleeInputAndBoundaryEffects(originalOperand)
    ready = preparedPlan.frozenChildCover(rawInitial)

    for record in savedNormalLookup(originalOperand):
        match = nativeMatch(record, originalOperand) // retain all real E and mx
        if match.empty:
            continue

        if rawInitial is supported FLOW/STAR with empty E and mx
           and originalOperand is correlated NORMAL FLOW/STAR with empty mx
           and record is opposite-direction, unary, unprotected NORMAL FLOW
           and record has STAR premise and STAR conclusion, with empty mx
           and match is an unknown-field inside match
           and ready.covers(match.firstUnknownField):
            continue   // children already own this reader contribution

        deliverUnmodifiedNativeResult(match)

    applyAndSubscribeCurrentUsingExistingDemandPlan(originalOperand)
```

`ready.covers` is the existing complete child-service check, not just the
presence of a field name. The frozen plan includes the original paired Dp
and physical ports. This proposal adds no second per-record lookup or new
coverage oracle. The proof broadens only its field-exclusion scope.

The change is that `originalOperand.E`, `record.premise.E`, and
`record.conclusion.E` may be nonempty. They remain inputs to native matching
and transfer. Do not clear them to force a match. Do not store an artificial
exclusion, ban a field, change the mark, or replace a reply's initial origin.

Apply the filter per supported native reply contribution. Do not discard
unsupported members of a mixed packet or the entire call.

The filter is inside an owned conditional query. The actual outer caller
still uses the original saved-summary service. It must not discard a real
marked input or its NORMAL result because it has no current demand.

The native hook may use matching's first-unknown-field descriptor before
allocating a reply. If that descriptor is unavailable, filter the native
contribution after matching; do not approximate its exclusion tests.

## 3. Why the exclusion does not break the cover

Write the correlated operand as `a.s`, where `s` is the initial query's
unknown suffix. A reader whose first unknown field is f can succeed only
when `s = f.t`. This remains true with arbitrary field exclusions.

Let `permit(E,s)` be true for an empty suffix, and otherwise test that the
first field of s is not in E. Let `u` be the remaining suffix after the
reader's complete guard. A concrete successful contribution satisfies:

```text
input = P.s
permit(operandE, s)
strip(readerPrefix, a.s) = u
permit(recordPremiseE, u)
permit(recordResultE, u)
output = readerResultPrefix.u
```

Success gives `s = f.t`. The child has exactly the same concrete input and
output, with the same filters at their original scopes:

```text
input = P.f.t
permit(operandE, f.t)
strip(readerPrefix, a.f.t) = u
permit(recordPremiseE, u)
permit(recordResultE, u)
output = readerResultPrefix.u
```

Split t into empty and nonempty. The existing `P.f.$` and `P.f.*` queries
cover both cases. The child need not solve the reader's full remaining
field chain in this iteration. Its next demand carries the deeper premise,
which advances the ordinary paired output budget.

If f is excluded in the operand, no concrete parent contribution exists.
If g is excluded at a and f differs from g, selecting f makes that particular
parent-scope restriction irrelevant to t. **Do not rebase `{g}` onto a.f.**
That would wrongly remove the valid input a.f.g. Native execution of the
child through the original instructions handles these scopes.

The record's exclusions remain on u at their original shared/own scope.
The proof is independent of the exclusion names, number of exclusions,
remaining guard length and fixed output selector. A later real cut still
uses NE and retains every concrete extension of the selected child.

This argument uses a correlated NORMAL prefix relation. It does not grant
coverage for arbitrary aliases, unsupported ports, ND joins, mark-changing
records or a lost-correlation DEMAND operand. Such services keep the old work
unless their complete child-service proof is already available.

## 4. Examples and consequences

**Ordinary overwrites.**

```java
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
Node wrapper(Node x, boolean down) { return choose(x, down); }
```

Use three wrapper calls with T initially at x.f.g and descendants, and
an observation of T at the final returned object or below. Rg and Wg above
are derived from this ordinary body. Previously the wrapper's coarse
reply survived solely because E was nonempty. With the cover, it moves to
the prepared f child, without moving the raw initial of any other result.
The backward row gets its deeper paired output, the required NORMAL reader
is retained, and the complete frontier is empty after run-9. The final
precise paths still include f.f.f.g and f.f.f.f.f.f.f.g.

**Excluded selected field.** An operand `a.* {f}` cannot use an inside
reader selecting a.f. Native matching already gives no reply. The algorithm
neither widens it nor creates a substitute child field.

**Exclusion scope.** After `x.g = new Node(); x.h = new Node();`, the parent
FLOW query at x carries `{g,h}`. The already prepared initial x.f.* survives
those writes with no exclusion at x.f. The path x.f.g remains valid.

**Other dependencies.** Concrete owned queries, MUST queries, protected
records, already-DEMAND operands and nonempty mark-exclusion cases retain
their previous path. The earlier cleaner/protection fixes remain required;
this approach does not replace them with plain FLOW coverage.

## 5. Storage and cost

Reuse the existing qualified prepared plan, frozen readiness mask and native
record lookup. There is no new persistent store, record family or lookup.
Readiness remains a once-per-raw-query computation. The per-record filter
uses the native match descriptor and a mask membership test.

For any fixed input, plan, saved-record list and native postprocessing:

```text
new raw initial keys        = old raw initial keys
new original callee offers = old original callee offers
new replies                 ⊆ old replies
new postprocessed work      ≤ old postprocessed work
```

Every retained reply is exactly the old native reply, including E, mark,
layer and protection. The complete growth regression is identical in both
modes at every run-1 through run-11.

There is no global whole-run cardinality bound. Removing broad MAY guidance
can expose narrower facts which it previously hid. This can increase some
later work even though the fixed-plan filter adds none. In the 400-case
E-heavy screen, the largest equal-prefix summary-membership ratio is 1.042;
queries, callee inputs and outer fact memberships do not increase in that
screen. These are diagnostics, not native performance guarantees.

## 6. Proof scope and acceptance

The [constructive package](../../spec/lean/proposals/exclusion-child-replay-20261115/README.md)
checks arbitrary E-aware concrete child coverage, the same qualified output
service, truncation coverage, fallback laws, and fixed-plan cost. It also
checks every cold state, quiescence, paired handoff, actual producer
permission and final DATA/Target frontier for all twelve references.
Earlier selected cleaner and protected-case proofs are rebuilt dependencies.

Seven native component tests validate the decisive old operators, including
both record exclusions, an excluded first field, and child-scope exclusions.
Production is unchanged. A native implementation must bind its frozen child
service to its actual alias, rule and port handling before enabling the
filter. No new permission to skip those effects is implied.

One diagnostic case disagrees with an independent concrete model in both
old and new modes, with identical observed work. It remains a baseline
reference-alignment issue, documented in the report. No new finding
regression was observed. Do not interpret the checked examples as a proof
of all native findings or of termination for every possible program.

Full fresh proof rebuild passed: **399 new theorems, 1,397 audited declarations,
79 modules**. Seven native component tests passed.
