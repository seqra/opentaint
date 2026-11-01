# Evaluation of a premise-relative field limit

Date: 1 November 2026. Base runtime:
`c4a71246519ee5432879ce82518823f1703f3aa4`.
This note evaluates a new abstraction policy. It does not select or
implement that policy.

The referenced campaign reached Stirling-PDF **run-8** (run-7 complete and
accepted) and conductor **run-4** (run-3 complete and accepted). Both timed
out. The [backward-work investigation](bidirectional-backward-work-amplification-20261101.md)
contains their source and profile evidence. No new project run is claimed.

## 1. Candidate rule

Let `L` be the existing run limit. Let `d(P)` be the maximum counted field
depth of an original premise member. The conservative interpretation is:

```text
budget(P, L) = L                         if P is ZERO
budget(P, L) = min(L, d(P) + 1)          otherwise
```

For an ND premise, use the maximum member depth, not the sum. Count normal
fields and array elements as the AP API does. A static class accessor does
not count: `p.f` and `S.C.f` both have depth 1. The exact marker `S.C.$`
has depth 0 and remains an exact marker.

The `min` is a design choice that retains the current global storage
invariant. A literal `d(P)+1` without that minimum allows an initial at
depth L to produce depth L+1, including changes to run-1 static shapes.
That interpretation requires a separate change to the global budget,
initial admission, storage validation, and handoff proofs.

Compute the budget from the edge's full original premise. Recomputing it
from the previous local conclusion allows the budget to grow at every
step. Recomputing it from a callee summary's premise gives the wrong
budget to the caller's instantiated edge.

Overflow must use the existing field abstraction:

```text
precise deeper result -> bounded prefix.[any], DEMAND
```

Do not drop the result or retain NORMAL after losing fields. Preserve
concrete marks and protection. Targets are typed control conclusions and
do not have a field depth.

## 2. Potential work reduction

The inverse binary-read loop has a nonzero root premise. Its depth is 0,
so the new cap is 1 at every later global limit. Its reduced control would
keep the existing limit-1 shape: three raw summary leaves and 21 processed
items. The old global limit 7 produces 255 leaves and 1,281 items.

This is a strong bound on that reduced case. It is not a new project
performance measurement. For a branching factor b, the path-depth term
changes from `b^L` to `b^min(L,d(P)+1)`. Deep premises can still retain the
full limit. Same-depth alias fanout, caller-origin multiplicity, and
separately resumed reverse record views also remain.

Apply the cut during propagation to avoid internal path construction.
Applying it only when storing a method summary leaves the preceding
internal expansion in place. Call-stage and cleaner-temporary cut points
need an explicit policy: an atomic cleaner's private temporary must not
accidentally receive a different original or lose its extracted-prefix
meaning.

## 3. The ZERO exception limits the expected project benefit

A backward sink seed is an ordinary AP fact under a ZERO premise:

```text
ZERO -> checked-position/T
```

`RunMethodLocalServices.seedFact` uses ZERO in `core.cut`. Call sink seeds
also enter the reversed call plan under ZERO. They retain that original
until a callee creates its own admitted initial. All this work keeps L
under the proposed exception, even when the checked fact has an empty
field chain.

The saved JFR recordings do not contain premise values. Before predicting
a project speedup, measure work under ZERO and under each nonzero premise
depth. Weight this by processed work or allocation, not only by initial
key count. The old "zero-only actors" diagnostic does not measure this:
one actor can process both ZERO-origin and nonzero-origin edges.

## 4. A permanent cap can block refinement

Consider ordinary object construction and reads:

```java
class Box { Box f; Object g; }

Box wrap(Object p) {
    Box inner = new Box();
    inner.g = p;
    Box outer = new Box();
    outer.f = inner;
    return outer;
}

Object unwrap(Box x) {
    Box inner = x.f;
    return inner.g;
}

void main() {
    Object p = sourceT();       // Source assigns T at the exact root.
    sinkT(unwrap(wrap(p)));     // Sink checks T at the exact root.
}
```

The relevant forward `wrap` premise has depth 0. The relevant backward
`unwrap` return premise also has depth 0:

```text
Forward wrap:
  p.$/T -> inner.g.$/T          fits depth 1
        -> outer.f.g.$/T        depth 2
        -> ret.f.[any]/T        cut to DEMAND, cap 1

Backward unwrap:
  ret.$/T -> inner.g.$/T        fits depth 1
          -> x.f.g.$/T          depth 2
          -> x.f.[any]/T        cut to DEMAND, cap 1
```

Both sides forget the same middle field `g`. The middle offers and guides
can remain `f.[any]/T`. C2 cannot invent the missing concrete child from
an equal-path ANY offer. It emits an ANY initial. That deeper initial
has a larger budget, but it has no information with which to reconstruct
the lost child. C5 can project a demanded shallow exact point while
retaining DEMAND; it cannot turn the lost witness into NORMAL.

The producer's root and the consumer's root remain depth 0. Increasing L
does not increase their cap. There is no initial NORMAL deep relation to
replay in the opposite direction: both were cut. ZERO's full budget in
`main` cannot recreate field information absent from the helper results.

An explicit ZERO source at `x.f.g/T` is a different case. It supplies the
missing path directly and can enable a deeper initial. It is not a
counterexample to this progress risk.

Two additional external checks execute the production AP, C2, and C5
operators for the paired construction/read case and the direct-deep-source
control. Both pass:

| Global limit | Paired helpers, existing global cap | Paired helpers, relative cap |
|---|---|---|
| 1 | Middle path is cut; crossing relations remain DEMAND | Same loss |
| 2 through 7 | Precise two-field middle facts and four NORMAL crossing relations | Same shallow exact endpoint keys; all four crossing relations remain DEMAND |

For the relative cap, both middle C2 initials remain depth-1 ANY on DEMAND.
C5 can select exact DEMAND endpoints, but the next outer endpoint initials
are the same root exact NORMAL keys. The local state therefore repeats.
The direct ZERO deep-source control succeeds at limits 2 through 7 because
it supplies a depth-2 exact initial.

This checks the local transfer/admission/restriction fixed point. It is
not a modified full-driver project test. The code, receipts, and exact
outputs are retained in the
[relative-limit controls](data/bidirectional-premise-relative-limit-controls-20261101.json).

## 5. Conditional generation gives another progress obligation

```java
// Rule on makeConditional:
// CM(arg0,T1) AND CM(arg1,T2) -> assign return.f.g/U.
// Its ordinary body constructs a fresh result with non-null result.f.g.
Box helper(Object p, Object q) {
    return makeConditional(p, q);
}

void main() {
    Box r = helper(sourceT1(), sourceT2());
    sinkU(r.f.g);
}
```

In a later forward run, the complete NORMAL ND premise is
`{p.$/T1, q.$/T2}`. Both members have depth 0. The new rule always cuts the
computed NORMAL `ret.f.g.$/U` to `ret.f.[any]/U` on DEMAND.

Here the unary opposite-native rescue cannot be assumed. The current
backward multi-condition source transfer emits conjunctive branches on
DEMAND. They cannot produce a NORMAL native record for the complete source
relation. NORMAL ND records are not stored as singleton native records
either. C5 preserves the DEMAND layer when refining geometry.

Thus proof of one unary case does not establish general progress. A fixed
cap needs to account for conditional generation and complete ND bindings,
as well as ordinary intermediate field paths.

## 6. Recommendation

Use the relative cap as an initial work allowance only if the design also
has a progress rule. For example, an unresolved required cut can cause a
larger allowance for that origin in a later analysis. The allowance must
eventually admit required intermediate paths, even when the boundary
premise stays shallow. Merely increasing L does not do that with a fixed
`d(P)+1` cap.

Restricting the new policy to backward runs is another candidate worth
checking while keeping forward construction at its existing limit. That
is not a proved complete solution. It still needs a cross-iteration
argument for source permissions, C2/C5 refinement, and native replay.

This is a major abstraction change: results previously NORMAL can become
DEMAND and require more refinement. It is not semantic-set-equivalent
deduplication. Before selection, prove local cut coverage and end-to-end
progress, including Targets, source permissions, ND rules, raw NORMAL
record persistence, and opposite-direction record application. Then
measure the ZERO/nonzero premise-depth distribution in the slow runs.
