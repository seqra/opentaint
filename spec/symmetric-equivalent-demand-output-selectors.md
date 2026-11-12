# Symmetric demand output selector coverage

Status: checked extension of the
[output-selector law](equivalent-demand-output-selectors.md).
Production behavior is unchanged. The accepted certificates are under
`docs/reports/data/redundant-demand-20261110/q-equivalent-output-selectors-symmetric-v2`.

## 1. Change and unchanged behavior

The first matcher accepts a removed MAY output selector only when an actual
STAR selector remains. The proved query law is symmetric. This extension
also accepts a removed STAR selector when an actual MAY selector remains:

```text
same full owner, context, block and physical ports
same complete DATA entry A
R: entry A, exit x.p.STAR/M, E={}
S: entry A, exit x.p.ANY/M,  E={}
```

These are output selectors, not facts or demand entries. Keep both original
row payloads in the certificate. Do not replace S's real MAY selector with
an invented STAR row. Do not change C2, C5, matching, field limits, source
permissions, aliases, marks, protection, controls, reports or loop handling.
Keep raw current summaries and all NORMAL providers. Remove only the redundant
edge's contribution to the outgoing guidance after the later barrier.

The scope remains the pinned FULL runtime and built-in iteration policy,
after a completed forward run at least run-5. Later demand is local. A policy
that makes decisions from exact diagnostic counts is outside this proof.

## 2. Executable predicate

U is the entire fixed campaign universe, including already classified edges.
Use the complete native projection of X. Each row needs an actual selected
outgoing witness after the same later barrier, outside all of U.

```python
def canonical_output_query(row):
    result = copy(row)
    if row.kind == DATA and row.exit.tail == ANY and row.exit.E == {}:
        result.exit.tail = STAR
    return result

def symmetric_output_cover(X, outgoing, U):
    rows = complete_native_projection(X)
    if not rows or any(not nonzero_data_pair(r) for r in rows):
        return NO_CERTIFICATE
    certificate = []
    for r in rows:
        Y, s = find_actual_selected_projection(
            outgoing, origin_outside=U,
            query_key=canonical_output_query(r),
            key=canonical_output_query)
        if Y is absent:
            return NO_CERTIFICATE
        certificate += [(r, Y, s)]
    return certificate
```

Compare complete keys after lookup. Hashes are indexes only. Entries, bases,
paths, marks, exclusions, method/context identity and ports must all match.
The empty-E STAR/MAY output law is the only extra equivalence. Nonempty
concrete STAR exclusions and changed C2 entries do not qualify.

## 3. Proof

The existing constructive model proves
`restrictExit(c, STAR-empty) = restrictExit(c, MAY-empty)` for every raw
conclusion c and its metadata. Equality is symmetric. Both selectors have
the same path, so they have the same demand-relative budget. They have equal
entries and scope, so C2, paired C5, prepared output programs, output-base
eligibility and owner support remain equal.

For every removed emission, the certificate supplies a retained actual
emission with an equal canonical query. The existing `Anchored` theorem
replaces its reply in the union of all outgoing replies. It keeps unrelated
emissions arbitrary. No unknown origin is assumed to emit nothing. Each
anchor is outside U, so the prior P/Q filters and this filter preserve it.
There is no circular support between removals.

Equal demand-service replies preserve the next complete semantic fixed point,
source permissions, saved providers, Target observations and report identity.
The next handoff is therefore rebuilt from equal semantic state. The same
argument applies to later runs. Diagnostic callback and stored-row counts
can differ. A decrease in such counts is not a measured performance result.

The formal model is the unchanged
`EquivalentOutputSelectors.lean`. The new finite instantiation is
`ObservedSymmetricOutputSelectors.lean`. Its full dictionaries preserve the
actual MAY anchors. The kernel checks every target, anchor, scope and complete
projection. Native validation must also test keeping MAY alone in methods,
scoped blocks, prepared plans and loop observations. The first version's
STAR-only native store test does not by itself test this store orientation.

## 4. Corpus and acceptance gate

The checked extension adds 39 edges: 34 Conductor and five Stirling-PDF, with 14 FLOW
and 25 concrete-mark edges. There are 20 method and 19 inner-block edges;
23 are plain and 16 protected. All actual witnesses in this package have
STAR source selectors and MAY retained selectors. All origins are singleton
and have complete one-row projections. The generic law does not use these
counts as proof.

Conductor reached run-8, completed run-7 and accepted forward run-7. Its
removal point is after run-7. Stirling-PDF reached run-11, completed run-10
and accepted forward run-9. Its removal point is after run-9. OWASP reached,
completed and accepted forward run-11; this extension has no OWASP match.

Independent native-origin and encoding checks pass for all 78 complete
emissions. All 27 constructive theorem audits pass. Six fresh MAY-only
native tests pass, including method/block matrices, prepared programs,
loop observations and negative controls. The joint check with the prior
334 removals preserves every canonical query, owner/port support and control
row. Production sources match the reference. The original certificates stay
unchanged. The selected Conductor URI edge has a unique paired output query
and does not pass this predicate.
