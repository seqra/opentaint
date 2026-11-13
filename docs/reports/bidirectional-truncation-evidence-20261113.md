# Truncation evidence and empty-path refinement

13 November 2026. Investigation only. The demand-elimination campaign is
paused. No production source, campaign verdict, or iteration policy changes.
The tested analyzer is `d94702571859da976406973dc89d4bc5df7a5675`.

**Result:** evidence can distinguish an empty suffix from a nonempty suffix.
But a STAR offer with no *known* extra field can still bind a nonempty
suffix. Rejecting that offer from this evidence alone is unsound. A native
counterexample loses a finding: baseline completes at **run-7**; the filter
completes at **run-5**, with no finding. Neither control has an iteration cap.

No project scan was run. The latest historical project positions remain:

| Project | Reached | Completed | Accepted forward |
| --- | --- | --- | --- |
| OWASP | run-11 | run-11 | run-11 |
| Conductor | run-8 | run-7 | run-7 |
| Stirling-PDF | run-11 | run-10 | run-9 |

## 1. The property to record

Let a C5 cut replace `a ++ s / tail` with `a.[any]`. Keep suffix evidence
`E` at that complete demand row. Define:

```text
L(E)       = union of the suffix bindings represented by E
mayEmpty(E) = (epsilon belongs to L(E))

cut x.f.g.h.[any] to x.f.[any]: E = { g.h.[any] }; mayEmpty = false
also cut x.f.n.m.*:             E += { n.m.* };  mayEmpty = false
uncut/intrinsic x.f.[any]:      E = unknown;     mayEmpty = true

merge(E1, E2):
    unknown, if either input is unknown
    E1 union E2, otherwise

mayEmpty(merge(E1,E2)) = mayEmpty(E1) OR mayEmpty(E2)
```

Every actual field cut removes at least one known field. Its lost suffix
cannot be empty, even if the old tail was STAR or MAY. However, an existing
MAY at the retained prefix does not prove this property. Missing evidence
must mean unknown. It must not mean an empty set or `mayEmpty=false`.

Bind evidence to the complete row: owner, block, ports, premise, output,
marks, layers and literal protection membership. Merge all contributors
that become that row, including contributors removed by compaction. When
handoff reverses an edge, its conclusion evidence belongs to the next
demand's entry. Do not attach it to unrelated rows with the same base.
This is a requirement for a possible design, not a new runtime identity.

The bit needs constant space per row. Full suffix sets can cost as much
as the paths that C5 removed. They need a separate memory analysis.

## 2. Empty binding is different from an empty known chain

Use the prefix `x.f` as the anchor:

| Submitted fact | Possible binding relative to the anchor | Effect of evidence `{g.h.[any], n.m.*}` |
| --- | --- | --- |
| `x.f.$` | Empty only | No overlap with these suffixes. |
| `x.f.*` | A symbolic frame; it can bind `g.h` | Cannot reject solely because no extra field is written in the fact. |
| `x.f.[any]` | Empty or nonempty | Nonempty possibilities remain. |
| `x.f.[any-taint]` | Includes descendants, subject to exclusions | Nonempty possibilities remain. |
| `x.f.g.*` | Starts with `g`; can bind the remaining `h` | A relevant binding exists. |
| `x.f.k.*`, unrelated `k` | Starts with `k` | Disjoint in this finite, empty-exclusion example. |

The tested filter confused the first two rows. It rejected a same-prefix
STAR admission when `mayEmpty=false`. The native example below shows why
the STAR binding is still needed.

The local exact-empty result has a condition: evidence must cover **every
relevant binding**. A sample of observed facts is not that proof. A change
to C2 must also account for FLOW companions and the normalized C2 image
used by C5. The local result does not authorize a blanket exact-input filter.

## 3. Native counterexample

Rules: `sourceT()` assigns T at the exact returned object. It does not mark
all descendants. `sinkDeepT(y)` checks for T at `y.[any]`.

```java
void main() {
    Node x = sourceT();
    Node y = wrap(x);
    sinkDeepT(y);
}

Node wrap(Node p) {
    return make(p);
}

Node make(Node p) {
    if (choose()) return p.other;
    Node r = new Node();
    r.f = new Node();
    r.f.g = new Node();
    r.f.g.h = p;
    return r;
}
```

The native fixture uses the two ordinary FLOW transfers of the two return
paths, not predefined summaries:

```text
p.other.* -> ret.*       NORMAL
p.*       -> ret.f.g.h.* NORMAL
```

These are compiled statement transfers. The real engine performs calls,
C2, C5, storage, saved-record replay, source/sink handling and handoff.
There are no loops, statics, aliases, protected rows, ND rules, or type-based
conditions in this counterexample. FULL mode uses limits `1,1,2,3,...`.

All DATA rows in the trace below have FLOW marks and empty exclusions.
`N` means NORMAL; `D` means DEMAND. Write a demand as `(entry; exit)` in
the current direction. The source remains concrete T. C2 selects FLOW
initials from it under the FLOW guide; it does not change the source mark.

### Run-1 and run-2: establish the guides

Run-1 gives both helpers `p.*`. The `p.other` read creates a MAY result;
the write path is cut. The root MAY covers the deeper MAY for that origin:

```text
make and wrap run-1: p.* -> ret.[any], D
```

In run-2, both helpers start from `ret.*`. Their summaries include:

```text
ret.* -> p.other.*, N    // saved NORMAL read relation
ret.* -> p.[any], D      // inverse of the three-field write path
```

Thus run-3 has `(p.[any]; ret.*)` demand in both helpers. Saved NORMAL
records stay enabled in both controls.

### Run-3: a real C5 cut, with different local evidence

```java
// wrap demand: (p.[any]/FLOW; ret.*/FLOW)
// submitted: p.$/T,N. Initial: p.$/FLOW,N.
Node wrap(Node p) {
    return make(p);
}
// Stored: p.*/FLOW -> ret.f.[any]/FLOW,D.
// The received ret.f.[any] needs no further field cut here.
// No evidence is propagated through the call: wrap's evidence is unknown.

// make demand: (p.[any]/FLOW; ret.*/FLOW)
// submitted and initial: p.$/FLOW,N.
Node make(Node p) {
    if (choose()) return p.other; // Exact p.$ cannot supply p.other.
    Node r = new Node();
    r.f = new Node();
    r.f.g = new Node();
    r.f.g.h = p;
    return r;
}
// Before C5: p.*/FLOW -> ret.f.g.[any]/FLOW,D.
//            The global run limit 2 already removed h.
// C5 budget: FL(ret.*) + 1 = 1.
// Stored:    p.*/FLOW -> ret.f.[any]/FLOW,D.
// Local evidence at ret.f: {g.[any]}; mayEmpty=false.
```

The evidence is genuine: the selected native C5 input still has the
known field `g`, and C5 removes it. The example does not infer a nonempty
suffix from an already same-prefix MAY.

### Run-4: the required STAR passes through the wrapper

```java
// wrap demand: (ret.f.[any]/FLOW; p.*/FLOW)
// Submitted: ret.[any]/T,D from the deep sink.
// Initial:   ret.f.*/FLOW,N under current C2.
Node wrap(Node p) {
    return make(p); // Offers ret.f.*/FLOW,N to make in backward analysis.
}
// Baseline: ret.f.*/FLOW -> p.[any]/FLOW,D.

// make demand: (ret.f.[any]/FLOW; p.*/FLOW), mayEmpty=false.
// Submitted: ret.f.*/FLOW,N.
// Baseline initial: ret.f.*/FLOW,N. Filtered initial: NONE.
Node make(Node p) {
    if (choose()) return p.other;
    Node r = new Node();
    r.f = new Node();
    r.f.g = new Node();
    r.f.g.h = p;
    return r;
}
// Baseline: ret.f.*/FLOW -> p.[any]/FLOW,D.
// Filter: no current summary from this initial.
```

The wrapper has received no `g` evidence. It cannot offer `ret.f.g.*`.
Its STAR frame can still bind that suffix inside `make`. Rejecting it
removes the inverse write path.

The MAY demand **did** reach the caller. That does not ensure that the
caller names a field beyond the cut prefix. The exact run-4 pipeline is:

```text
wrap demand:       ret.f.[any]/FLOW
wrap submitted:    ret.[any]/T          // sink accepts any descendant
wrap C2 initial:   ret.f.*/FLOW         // current ancestor-MAY C2 cell
make submitted:    ret.f.*/FLOW         // wrapper's return binding is unchanged
make cut prefix:   ret.f
known extra chain beyond that prefix: empty
lost next field:   g
```

The caller's broad query does not name `g`. That field is introduced by
the write inside `make`. The `f` in the submitted fact is already part of
the cut prefix; it is not a new refinement of its MAY suffix. The next
more precise publication appears in run-5 only if run-4 analyzes this
symbolic query. Dropping it and waiting for a `g` offer is circular: the
dropped analysis supplies the guidance needed for that later refinement.
This counterexample refutes the direct filter in the current pipeline;
it does not refute a new design that preserves or constructs that route.

The old NORMAL read relation still replays. It gives the wrapper a route
through `p.other.f.*`, which C5 cuts to `p.other.[any]`. This is the only
remaining DATA guide in the filtered control. It cannot consume the exact
root source `p.$/T` in run-5.

### Completion without an iteration cap

| Run | Baseline | Filtered control |
| --- | --- | --- |
| run-3 | `p.* -> ret.f.[any],D` | Same. |
| run-4 | `ret.f.* -> p.[any],D` in make and wrap | Reject exactly one initial in make; wrap retains only the `p.other.[any]` route. |
| run-5 | `p.* -> ret.f.g.[any],D`; refinement continues | No matching root-source route; finishes with no finding. |
| run-6 | `ret.f.g.* -> p.[any],D` | Already stopped. |
| run-7 | `p.* -> ret.f.g.h.*,N`; reports `deep T` and finishes | Already stopped. |

Both end reasons are `NO_DEMAND_EDGE`, not a policy, time, or run-11 cutoff.
One rejected initial is enough to lose the valid source-to-sink finding.

## 4. What this says about the repetition hypothesis

The evidence distinguishes real field loss from intrinsic MAY. That is
useful diagnostic information. It can also support disjoint-binding
checks if capture and routing are proved complete. It does not prove
that all same-prefix STAR starts are redundant, nor that refinement terminates.

In the captured OWASP cycle, the selected run-10 and run-11 MAY results
already exist **before C5**. The constructor applies a deeper compiled
read to an ancestor STAR. C5 then rebases or preserves the MAY. It does
not remove a known extra field for those results. See the
[native cycle trace](bidirectional-demand-row-campaign-20261112.md).
Local C5-only evidence therefore remains unknown for those rows. It cannot
justify removing this established repetition pattern.

Do not conflate those operations with the 22 LIMIT callbacks in that
diagnostic capture. Some other rows do have boundary cuts. No corpus-wide
savings estimate follows from this finite counterexample or those counts.

## 5. Soundness boundary and possible next design

The safe *binding-level* condition is:

```text
irrelevant(E, offered) :=
    evidence is complete
    AND no allowed binding of offered overlaps L(E)

// Incorrect replacement:
irrelevant := !mayEmpty(E) AND offered has no known extra fields
```

The [Lean model](../../spec/lean/proposals/truncation-evidence-20261113/README.md)
proves the empty-suffix test, OR merge, nonempty-cut property, conditional
exact-empty rejection, and the explicit STAR binding that refutes the
incorrect replacement. It also gives a disjoint first-field example.
It uses no classical choice or assumed completeness of an observed sample.
It does not prove a complete new C2/C5 policy.

A future design could keep nonempty obligations while retaining symbolic
STAR delivery, or use suffix evidence to route a known next field. Routing
would need its own rules for wrappers, multiple rows and companions. It
would change admission semantics. It is not part of this experiment.

Any such design must preserve saved NORMAL replay, C2/C5 agreement, literal
protection memberships, complete ND origins and typed controls. Evidence
must remain complete after merging or subsumption. Unknown contributions
must widen it. It must not silently add a tail kind, a grounding service,
or a change to field transfers. No such change was made here.

## 6. Reproduction and evidence

The [native fixture](../../scripts/demand_experiments/truncation-evidence/TruncationEvidenceTest.kt)
uses a test-only admission filter. It leaves subscriptions and persisted
NORMAL replay in place. The filter unions support from all matching local
demand rows; it does not let one row veto an initial supported by another.
C5 evidence is reconstructed with the actual pure restriction and limit
operators from the captured normalized candidates. C5 itself stays unchanged.
The final admitted row must exist before evidence is retained.

The test compiles current production source with Gradle, offline, and an
external test-source overlay. No test class shadows a runtime class.
The passive raw-C5 observer reports 49 baseline attempts and 24 filtered
attempts, zero errors, zero missing contexts, and one instrumented method.

Data follows [the external-data policy](EXTERNAL_DATA.md):

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/
  docs/reports/data/truncation-evidence-20261113/native-v4/
```

This directory has the exact source, command, init script, source/classpath
pins, observer bytecode, complete text traces, JUnit result and receipt.
Earlier unsuccessful preparations remain separate. The compact checker is:

```sh
python3 scripts/demand_experiments/truncation-evidence/check.py \
  /drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/truncation-evidence-20261113/native-v4
lean spec/lean/proposals/truncation-evidence-20261113/Evidence.lean
```

No production implementation of truncation-evidence admission is selected.
