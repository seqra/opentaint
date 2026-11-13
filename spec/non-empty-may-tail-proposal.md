# Non-empty MAY: proposal and checked fragment

13 November 2026. Partial design; not an implementation contract.
Production source is unchanged. Follow [proof-guide.md](proof-guide.md).
This replaces the previous tail-renaming direction as the current proposal.

The new tail distinguishes a proved nonempty suffix from a suffix which
may be empty. It can represent the result of a real field cut without a
separate empty-binding evidence bit. It does not yet prove elimination of
the measured FL+1 recurrence.

## 1. Selected meaning and changes

Let epsilon be the empty field chain and Sigma the field alphabet:

```text
x.$                = x · {epsilon}
x.[any]            = x · Sigma*
x.[non-empty-may]  = x · Sigma+

[any] = $ UNION [non-empty-may]
$ INTERSECT [non-empty-may] = empty
```

Non-empty MAY is existential uncertainty, not uniform MUST taint. It says
neither which field comes first nor that every descendant carries the mark.

| Part | Current source | Proposed change |
| --- | --- | --- |
| Tail domain | EXACT, STAR, MAY and MUST | Add non-empty MAY as semantic state |
| MAY admission | Usually a STAR query and existing companions | Split empty and non-empty alternatives |
| Submitted STAR in admission | Can supply an exact initial in old cells | Has only the non-empty admission alternative |
| Submitted MAY in admission | Old scalar selector | Can supply both alternatives |
| Field cut | MAY/D, even when a concrete field was removed | Non-empty MAY/D for that real cut |
| Output coverage | No non-empty tail | MAY covers non-empty MAY at the same coordinate |

This changes admission and field transfer; it is more than storage packing.
Distinct tails must stay distinct in equality, hashing, fresh deltas and
published guidance until a proved coverage rule removes one. Do not erase
the new tail at handoff by default: doing so loses its empty-binding fact.
Mark identity, literal protection and layer support remain independent.

## 2. Same-head admission partition

Before existing base, mark, exclusion, direction, budget and static-anchor
checks, the proposed tail alternatives are:

| Submitted tail | Empty alternative | Non-empty alternative |
| --- | --- | --- |
| `$` | Yes | No |
| `*` | No | Yes |
| `[any]` | Yes | Yes |
| `[non-empty-may]` | No | Yes |

An EXACT demand selects only the empty alternative. A non-empty demand
selects only the non-empty alternative. A MAY demand selects both.
These are alternative conditional queries, not a claim that a MAY offer
definitely has an exact marked root. Joining the original caller's D
support must not produce a NORMAL concrete witness.

The user selected the emitted initial representation explicitly:

```text
empty alternative     -> p.$ -> p.$
non-empty alternative -> p.* -> p.*

demand p.[any], submitted p.[any]: emit BOTH initials
demand p.[non-empty-may], submitted p.[any]: emit only p.*
demand p.[any], submitted p.*: emit only p.*
```

The required mark is preserved in this spatial split. A concrete T start
from a submitted MAY/D offer retains D support in both branches; its
EXACT tail does not make that support NORMAL. Existing FLOW companions
are a separate mechanism. The old single-STAR trace below describes the
current source, not this newly selected admission family.

This tail partition and its EXACT/STAR initial representation are checked.
The complete spatial C2 rule, all seed-layer cases, its C5 normalized image and the migration
of old STAR producers still need a joint contract. In particular, an old
STAR-to-EXACT companion cannot be retained silently if it would defeat
the selected non-empty-only admission rule.

## 3. Transfer laws and the write decision

The proposed laws are:

```text
read below an unknown STAR suffix -> MAY, with the existing loss support
consume a field from a non-empty MAY suffix -> MAY
remove one or more known fields at a limit -> non-empty MAY, DEMAND
```

Reading a non-empty suffix can produce an empty result. For example, the
input's entire suffix may be f; reading f then reaches the marked root.

The position of the new tail on a write needs a decision. For `x.f = y`:

```text
y.[any] -> x.f.[any]      // retain known f; includes x.f.$
y.[any] -> x.[non-empty-may]
                          // safe abstraction at parent x; forgets f
y.[any] -> x.f.[non-empty-may]
                          // excludes x.f.$; not an over-approximation
```

The first two choices are sound positional representations. The third
loses the possible empty suffix at y. This is not about mark mismatch or
exclusion; it holds with one full mark and Empty E.

### Current implementation: exact native trace

N means NORMAL, D means DEMAND and F means FLOW. Both fields fit the limit.
The stated pair is a component-test input; this trace does not claim that
the three-statement body alone generated that pair in the previous run.

```java
// Given previous backward DEMAND edge:
//   x.f.$/T -> p.[any]/T
// Current demand pair:
//   entry p.[any]/T; exit x.f.$/T
// Submitted packet:
//   p.[any]/T, D
// Current emitted initial edges:
//   p.*/T -> p.*/T, D
//   p.*/F -> p.*/F, N       (FLOW companion)
void copy(Box x, Box p) {
    Object y = p.g;
    // Read micro-edge results:
    //   p.*/T -> y.[any]/T, D
    //   p.*/F -> y.[any]/F, D

    x.f = y;
    // Write micro-edge results:
    //   p.*/T -> x.f.[any]/T, D
    //   p.*/F -> x.f.[any]/F, D
    // f fits the budget: no field cut occurs here.
}
// Admitted summaries after restriction to the stated exact exit:
//   p.*/T -> x.f.$/T, D
//   p.*/F -> x.f.*/F, D
// The FLOW output uses existing EXACT-to-STAR summary normalization.
// Neither intersection nor normalization changes D into N.
```

The native test also supplies the precise binding `y.$/T,N` directly to
the write micro-edge. It emits `x.f.$/T,N`. This is the root binding which
must remain representable when the write receives MAY instead.

### Selected split: trace through the first read

For the same demand and submitted packet, the new concrete T query has
both starts. The non-empty part is relative to p; after a read it can
become the empty part relative to y:

```java
// Demand: entry p.[any]/T; exit x.f.$/T
// Submitted: p.[any]/T, D
// New concrete T initials:
//   p.$/T -> p.$/T, D
//   p.*/T -> p.*/T, D
void copy(Box x, Box p) {
    Object y = p.g;
    // p.$ branch: no y result; the exact root p is not p.g.
    // p.* branch: y.[any]/T, D.
    // Its possible suffix g has been consumed, so y.$/T is possible.

    x.f = y;
    // The position of non-empty MAY on this write remains the decision
    // described above. Splitting p does not make y's MAY suffix nonempty.
}
```

The split repairs the earlier omission of the empty initial in a new-policy
trace. It does not claim that a suffix stays nonempty after consuming a
field. Emitted summaries for the new write rule await that rule's decision.

For a real cut, non-empty MAY goes at the **retained** prefix:

```text
x.f.g.h.$/T --cut after f--> x.f.[non-empty-may]/T, D
```

At least g is removed, so every removed suffix is non-empty. An uncut
`x.f.[any]/T` has no such certificate and cannot be relabelled at that
same coordinate merely because an earlier write occurred.

## 4. Subsumption

With the same complete premise, output base/path/mark, layer, scope/ports
and literal protection class:

```text
X -> a.[any]  covers  X -> a.[non-empty-may]
```

The language union and same-head admission coverage are both checked.
The broad MAY row supplies every non-empty alternative and may also supply
the empty alternative. Retaining MAY therefore does not require keeping
its covered non-empty membership. Both arrival orders must yield that
same retained basis. Do not apply this output-only rule to different
premises or mix protected and unprotected memberships.

## 5. Progress: proved distinction, remaining obligation

The new rule prevents a submitted STAR from directly supplying the empty
alternative. That removes one specific non-refining admission.

It does not alone prove increasing concrete field length:

```text
demand x.[non-empty-may], submitted x.*:
    the non-empty alternative is compatible at the same head x

demand x.[non-empty-may], submitted x.[any]:
    the non-empty alternative is also compatible at x
```

A non-empty suffix has a first field in each concrete binding, but the
pattern does not name that field. The tail-only partition can therefore
admit another unknown non-empty query without extending the known chain.
Also, a read can reset the tail to MAY; abstracting a write at its parent
can restore non-empty MAY. That is a local tail reset, not a demonstrated
complete-driver cycle.

The complete proposal must show where a repeated query acquires a known
field or is eliminated, including call views, saved summaries, C5 cuts and
handoff. Do not infer global convergence from the suffix partition or the
temporary run-11 limit.

## 6. Validation and remaining work

[NonEmptyMay.lean](lean/proposals/non-empty-may-20261113/NonEmptyMay.lean)
checks 30 constructive declarations: partition, disjointness, first-field
witness, admission alternatives, read, write-position counterexample,
real cuts, output coverage, arrival order, the EXACT/STAR initial family,
the two-branch first-read trace and the progress limitation.
It models scalar field strings. Marks, exclusions, classes, arrays, MUST,
ND, aliases, Targets, raw summary image and physical ports are not proved
by this component.

[CurrentMayWriteTraceTest.kt](../scripts/demand_experiments/non-empty-may/CurrentMayWriteTraceTest.kt)
passes against the unmodified current C2, AP operations and C5. It verifies
the complete relevant trace above, including the FLOW companion and exact
binding. It does not implement the new tail or prove a new full-driver
policy. The write-position choice is still awaiting clarification.

Frozen evidence is under `non-empty-may-20261113/` in the
[external data root](../docs/reports/EXTERNAL_DATA.md).
No project scan was run. Historical reached/completed/accepted forward
positions remain OWASP **run-11/run-11/run-11**, Conductor
**run-8/run-7/run-7**, Stirling-PDF **run-11/run-10/run-9**.
