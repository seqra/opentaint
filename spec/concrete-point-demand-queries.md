# Equivalent concrete point and control output queries

This is a campaign predicate for the pinned FULL analyzer. It removes only
outgoing guidance after the selected completed forward barrier, at run-5
or later. The runtime, raw summaries, NORMAL records, observations, source
permissions, seeds, targets and reports stay in the reference state.

## Query law

At run-3 and later, these two entries give the same C2 and C5 entry answers.

```text
entry A = x.p.*/T, with any legal field exclusion
entry B = x.p.$/T, with empty field exclusion

T is the same full mark in both entries.
The base, complete field path and physical owner are equal.
The entry is DATA with a nonzero base.
```

This is a query equivalence. Actual facts and summary endpoints keep their
own tails. No new fact grammar or transfer is selected.

For a same-path submitted fact, both entries emit the exact initial
`x.p.$/T`. Its layer is DEMAND when the actual is MAY or on DEMAND.
For a strict ancestor MAY or MUST actual, both entries emit that exact
initial if the actual field exclusion admits the suffix. For a strict
descendant, both entries emit nothing at run-3 and later. Other bases,
marks and disjoint paths emit nothing.

The emitted initial is concrete EXACT. It gives no FLOW companion.
The MAY-entry companion rule does not apply to either entry. Both entries
also have the same budget and static-initial grammar checks.

C5 admits only the same-path exact concrete initial for these entries.
FLOW normalization and the FLOW companion fallback do not add a different
stored initial. A complete ND original is accepted under either entry
exactly when one of its members has this image. The original ND premise
stays complete.

Both entries contribute no MAY precision cursor. Their entry-trie
base, path and full-mark profiles are equal. The indexes inspect both
entries on the same offers.

## Retained witness predicate

Use each raw origin's complete native handoff projections. Keep all
premise members and physical ports. A projection key includes the method
and context, block identity, entry and exit ports, typed endpoint kinds,
entry base/path/full mark, and the full output selector.

The entry key maps a concrete STAR or EXACT entry to the same point key
and clears its field exclusion. An EXACT input to this mapping must
already have empty exclusion. It leaves every other entry unchanged.
For a DATA exit with empty exclusion, the existing output-selector proof
allows MAY and STAR to use one output key. Every other exit coordinate
stays literal.

```python
def equivalentQueryKey(row):
    key = copy(row)
    if row.entry is DATA:
        if row.entry.mark is a full concrete mark:
            if row.entry.tail in {STAR, EXACT}:
                require row.entry.tail != EXACT or row.entry.E == EMPTY
                key.entry.tail = EXACT
                key.entry.E = EMPTY
    key.exit = equivalentOutputSelectorKey(key.exit)
    return key

def canRetire(origin, finalRetainedOrigins):
    projections = completeNativeProjection(origin)
    require projections is not empty
    for row in projections:
        witness = actualRetainedProjection(
            finalRetainedOrigins, sameKey=equivalentQueryKey(row))
        require witness exists
        save(row, witness.rawOrigin, witness.completeProjection)
    return certificate
```

The witness must remain after every accepted removal, including this
predicate's joint removal set. Preserve all previous accepted witnesses.
A witness can be inside the repeated universe if it remains retained.
Compare complete canonical values after a hash lookup. Save each witness
as an executable origin-to-projection certificate.

## Typed control output extension

The predicate also uses the empty-exclusion MAY/STAR output law for a
typed ZERO or Target entry with a DATA exit. This extends the scope of
the earlier output-selector predicate, which covered nonzero DATA pairs.
Keep the typed entry, complete exit path and mark, owner and ports equal.
Only an empty-exclusion MAY output selector can use its STAR equivalent.

C2 Reach admission checks the same typed entry on both sides. Neither
entry contributes a DATA entry or a precision cursor. C5 first checks the
same complete original against the typed entry. For an admitted ZERO
original and a DATA result, the runtime uses `ap.zero` as the entry of
the temporary data pair and calls the ordinary output restriction and
relative field cut. The scalar output law therefore gives equal results.
A Reach result cannot satisfy either DATA exit, so Target acceptance
also stays equal. Both control entry kinds and the wrong-port rejection
have native controls.

This extension keeps the target kind and identity rules. It changes no
Target publication, sink, source or ZERO routing behavior.

## Before and after

```text
Before, in the same block scope and at the same physical exit
    R = (entry x.p.*/T, exit y.q.[any]/U)
    S = (entry x.p.$/T, exit y.q.*/U)

Submitted
    x.p.[any]/T, DEMAND
Under both entries
    initial x.p.$/T, DEMAND

Current stored candidate
    x.p.$/T -> y.q.[any]/U, DEMAND, with its own protection
Under either complete row
    keep the same conclusion and apply the same relative field cut

After removing R's origin
    S supplies the same admission and paired output.
```

If the current conclusion has MUST with exclusions, the same old
empty-exclusion output law applies. Ordinary current field and mark
exclusions, layer and both protection memberships remain attached.
If the exit is typed ZERO, its complete control row stays paired with
the exact same DATA entry image. Reach input still cannot satisfy DATA.

## Boundaries and counterexamples

The proof uses local demand only. At run-2 a concrete STAR entry can emit a
STAR initial from a descendant, while an EXACT entry rejects it. Therefore
the predicate excludes run-2 and the special run-1 handoff.

The entry mark must be full and concrete. For FLOW demand at the same
path, STAR admits a submitted MAY but EXACT rejects it. A group mark
needs its separate mark-coverage semantics.

Keep output exclusions and physical ports. A STAR output excluding
`b` rejects a `y.q.b.$/U` result, while the empty-exclusion MAY
output accepts it. A witness at another physical exit cannot answer
the query. A row with a different full entry mark does not admit T.

## Proof and future use

`ConcretePointDemandQueries.lean` proves the primary initial, complete
family, stored entry image, full-original and paired-result laws for
all late runs. It gives an executable retained witness for each removed
row and proves equality of the whole query union. The existing
`EquivalentOutputSelectors.lean` supplies the output law and equal
relative budget for a canonical MAY/STAR exit.

The same C2 answers keep call admission and subscription equal. Complete
paired C5 and prepared output plans give the same results under every
offer, including ND originals and protected packets. Loop restriction
uses these same observations. Both point entries have no precision
cursor, and the pinned certificate shortcut returns no budget.

Each removed projection keeps a same-owner, same-port witness, so owner
support, typed control routes and empty-demand stopping are preserved.
The configured policy does not read row-count diagnostics.
With equal demand services and the same seeds and NORMAL records, the
next semantic fixed point has the same source permissions, Targets,
persisted summaries and report identities. The next handoff is built
from that state. Repeat this argument for later runs.

The finite binding must check all original projections and the final
retained witnesses. Native tests must exercise C2, direct and prepared
C5, complete ND originals, control exits, loop scope and port filtering,
layers, exclusions and the early-run and FLOW counterexamples.
