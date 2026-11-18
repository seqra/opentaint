# Recursion with field accesses on both sides of a call

Baseline commit `966a40c3647268cc006e5776591d6b68849379d0`, FULL marks,
field limits `1, 1, 2, 3, …`. This campaign follows [term-task.md](../../term-task.md).
It adds [R40 [REC]](../design/bidirectional-nested-field-goal-service-20261117.md)
to the proposal and uses a test adapter for the new handoff rule.

The new reader has one branch with a read on each side of its recursive
call. R39 treats that route slice as Unknown. The native diagnostic
renews the root Target in runs 1, 3, 5, 7 and 9. It reaches **run-9/POLICY**
with no NORMAL observation. The test adapter reaches **run-5/NO_DEMAND_EDGE**.
Changing the reader base from `p.g` to `p.f` gives a real route. The baseline
finds it and reaches run-9/POLICY. The adapter preserves the finding and
finishes naturally at run-7 through ordinary NORMAL origin service.

## Code and route

```java
class Node { Node f, g, h; }
class Choice { Choice next; boolean useH; }

void main(Choice w, Choice r) {
    Node x = new Node();            // Mark T at x.$.
    Node y = write(x, w);
    Node z = read(y, r);
                                   // Observe T at z.$.
}
Node write(Node p, Choice c) {
    Node b = new Node();
    if (c == null) b.f = p;
    else b.g = write(p, c.next);
    return b;
}
Node read(Node p, Choice c) {
    if (c == null) return p.g;
    if (!c.useH) return read(p.g, c.next);
    Node t = read(p.h, c.next);
    return t.h;
}
```

The writer produces paths `gⁿ.f` to the exact marking point. The reader
consumes a word from `R = g | g·R | h·R·h`. The words from its `h` arm contain
`h`, and the words from its `g` arm alone end at `g`. Thus the exact
marking point can never reach the observer. During analysis, truncation
forgets the trailing `f`. A deeper read can then produce a root MAY fact
on DEMAND and trigger the observer.

## Cold trace

Each annotation covers the method return cone. C2 raw initials are shown
before summary normalization. `$/*/M/NE` denote EXACT, STAR, MAY and
non-empty MAY. `F` is FLOW, and `N/D` name the layers. On backward runs the
input base is `ret`, and output uses `p`. The root's publication is
`Z → DT` unless otherwise indicated. The next trace uses the actual
scalar operators, including saved NORMAL replay and both field caps.

### Run-1, forward, limit 1

```java
// Demand = unrestricted
// Submitted = entry Z
// Initial = Z
void main(Choice w, Choice r) {
    Node x = new Node();  // Mark T at x.$.
    Node y = write(x, w);
    Node z = read(y, r);
    // Observe T at z.$.
}
// Published = Z → DT

// Demand (entry | exit) = ∅
// Submitted = p.$/T N; p.*/F N
// Raw initials = p.*/F N
Node write(Node p, Choice c) {
    Node b = new Node();
    if (c == null) b.f = p; else b.g = write(p, c.next);
    return b;
}
// Published = p.*/F → ret.f.*/F N; p.*/F → ret.g.NE/F D

// Demand (entry | exit) = ∅
// Submitted = p.M/F D; p.f.$/T N; p.g.NE/T D
// Raw initials = p.*/F N
Node read(Node p, Choice c) {
    if (c == null) return p.g;
    if (!c.useH) return read(p.g, c.next);
    Node t = read(p.h, c.next);
    return t.h;
}
// Published = p.*/F → ret.M/F D

```

### Run-2, backward, limit 1

```java
// Published = Z → DT and permission for mark T at x.$
void main(Choice w, Choice r) {
    Node x = new Node();  // Mark T at x.$.
    Node y = write(x, w);
    Node z = read(y, r);
    // Observe T at z.$.
}
// Demand = (Target | Z)
// Submitted = entry Z; observer z.$/T D
// Initial = Z

// Published = ret.g.*/F → p.M/F D
Node write(Node p, Choice c) {
    Node b = new Node();
    if (c == null) b.f = p; else b.g = write(p, c.next);
    return b;
}
// Demand (entry | exit) = ret.g.NE/F | p.*/F
// Submitted = ret.*/F N; ret.g.$/T D; ret.g.NE/T D; ret.h.NE/T D
// Raw initials = ret.g.*/F N

// Published = ret.*/F → p.g.*/F N; ret.*/F → p.g.NE/F D; ret.*/F → p.h.NE/F D; ret.h.*/F → p.g.NE/F D
//   ret.h.*/F → p.h.NE/F D
Node read(Node p, Choice c) {
    if (c == null) return p.g;
    if (!c.useH) return read(p.g, c.next);
    Node t = read(p.h, c.next);
    return t.h;
}
// Demand (entry | exit) = ret.M/F | p.*/F
// Submitted = ret.$/F N; ret.$/T D; ret.h.$/F N; ret.h.*/F N; ret.h.NE/F D
// Raw initials = ret.$/F N; ret.h.$/F N; ret.h.*/F N

```

### Run-3, forward, limit 2

```java
// Demand = (Z | Target)
// Submitted = entry Z
// Initial = Z
void main(Choice w, Choice r) {
    Node x = new Node();  // Mark T at x.$.
    Node y = write(x, w);
    Node z = read(y, r);
    // Observe T at z.$.
}
// Published = Z → DT

// Demand (entry | exit) = p.M/F | ret.g.*/F
// Submitted = p.$/F N; p.$/T N
// Raw initials = p.$/F N
Node write(Node p, Choice c) {
    Node b = new Node();
    if (c == null) b.f = p; else b.g = write(p, c.next);
    return b;
}
// Published = p.*/F → ret.gf.*/F N; p.*/F → ret.gg.NE/F D

// Demand (entry | exit) = p.g.NE/F | ret.*/F; p.h.NE/F | ret.*/F; p.g.NE/F | ret.h.*/F
//   p.h.NE/F | ret.h.*/F
// Submitted = p.*/F N; p.f.$/F N; p.f.$/T N; p.g.*/F N; p.gf.$/T N; p.gg.NE/T D
// Raw initials = p.g.*/F N; p.gf.$/F N; p.gg.*/F N; p.h.*/F N
Node read(Node p, Choice c) {
    if (c == null) return p.g;
    if (!c.useH) return read(p.g, c.next);
    Node t = read(p.h, c.next);
    return t.h;
}
// Published = p.g.*/F → ret.M/F D; p.h.*/F → ret.M/F D; p.g.*/F → ret.h.M/F D; p.h.*/F → ret.h.M/F D
//   p.gg.*/F → ret.*/F N; p.gg.*/F → ret.M/F D; p.gg.*/F → ret.h.M/F D

```

### Run-4, backward, limit 3

```java
// Published = Z → DT and permission for mark T at x.$
void main(Choice w, Choice r) {
    Node x = new Node();  // Mark T at x.$.
    Node y = write(x, w);
    Node z = read(y, r);
    // Observe T at z.$.
}
// Demand = (Target | Z)
// Submitted = entry Z; observer z.$/T D
// Initial = Z

// Published = ret.gg.*/F → p.M/F D; ret.ggg.*/F → p.M/F D
Node write(Node p, Choice c) {
    Node b = new Node();
    if (c == null) b.f = p; else b.g = write(p, c.next);
    return b;
}
// Demand (entry | exit) = ret.gg.NE/F | p.*/F
// Submitted = ret.g.$/T D; ret.g.*/F N; ret.gg.$/F N; ret.gg.$/T D; ret.gg.*/F N; ret.gg.NE/T D
//   ret.gh.*/F N; ret.gh.NE/T D; ret.hg.NE/T D; ret.hh.NE/T D; ret.ggg.$/T D; ret.ggg.NE/T D
//   ret.ggh.NE/T D
// Raw initials = ret.gg.*/F N; ret.ggg.$/F N; ret.ggg.*/F N; ret.ggh.*/F N

// Published = ret.*/F → p.gg.NE/F D; ret.*/F → p.gh.NE/F D; ret.*/F → p.hg.NE/F D; ret.*/F → p.hh.NE/F D
//   ret.h.*/F → p.gg.NE/F D; ret.h.*/F → p.gh.NE/F D; ret.h.*/F → p.hg.NE/F D; ret.h.*/F → p.hh.NE/F D
//   ret.hh.*/F → p.gg.NE/F D; ret.hh.*/F → p.gh.NE/F D; ret.hh.*/F → p.hg.NE/F D
//   ret.hh.*/F → p.hh.NE/F D; ret.*/F → p.ggg.*/F N; ret.*/F → p.ggg.NE/F D; ret.*/F → p.ggh.NE/F D
//   ret.h.*/F → p.ggg.NE/F D; ret.h.*/F → p.ggh.NE/F D; ret.hh.*/F → p.ggg.NE/F D
//   ret.hh.*/F → p.ggh.NE/F D
Node read(Node p, Choice c) {
    if (c == null) return p.g;
    if (!c.useH) return read(p.g, c.next);
    Node t = read(p.h, c.next);
    return t.h;
}
// Demand (entry | exit) = ret.M/F | p.g.*/F; ret.M/F | p.h.*/F; ret.h.M/F | p.g.*/F; ret.h.M/F | p.h.*/F
//   ret.M/F | p.gg.*/F; ret.h.M/F | p.gg.*/F
// Submitted = ret.$/F N; ret.$/T D; ret.h.$/F N; ret.h.*/F N; ret.hh.$/F N; ret.hh.*/F N; ret.hhh.$/F N
//   ret.hhh.*/F N
// Raw initials = ret.$/F N; ret.h.$/F N; ret.h.*/F N; ret.hh.$/F N; ret.hh.*/F N

```

### Run-5, forward, limit 4

```java
// Demand = (Z | Target)
// Submitted = entry Z
// Initial = Z
void main(Choice w, Choice r) {
    Node x = new Node();  // Mark T at x.$.
    Node y = write(x, w);
    Node z = read(y, r);
    // Observe T at z.$.
}
// Published = Z → DT

// Demand (entry | exit) = p.M/F | ret.gg.*/F; p.M/F | ret.ggg.*/F
// Submitted = p.$/F N; p.$/T N
// Raw initials = p.$/F N
Node write(Node p, Choice c) {
    Node b = new Node();
    if (c == null) b.f = p; else b.g = write(p, c.next);
    return b;
}
// Published = p.*/F → ret.ggf.*/F N; p.*/F → ret.ggg.NE/F D; p.*/F → ret.gggf.*/F N
//   p.*/F → ret.gggg.NE/F D

// Demand (entry | exit) = p.gg.NE/F | ret.*/F; p.gh.NE/F | ret.*/F; p.hg.NE/F | ret.*/F
//   p.hh.NE/F | ret.*/F; p.gg.NE/F | ret.h.*/F; p.gh.NE/F | ret.h.*/F; p.hg.NE/F | ret.h.*/F
//   p.hh.NE/F | ret.h.*/F; p.gg.NE/F | ret.hh.*/F; p.gh.NE/F | ret.hh.*/F; p.hg.NE/F | ret.hh.*/F
//   p.hh.NE/F | ret.hh.*/F; p.ggg.NE/F | ret.*/F; p.ggh.NE/F | ret.*/F; p.ggg.NE/F | ret.h.*/F
//   p.ggh.NE/F | ret.h.*/F; p.ggg.NE/F | ret.hh.*/F; p.ggh.NE/F | ret.hh.*/F
// Submitted = p.f.$/T N; p.g.*/F N; p.h.*/F N; p.gf.$/F N; p.gf.$/T N; p.gg.$/F N; p.gg.*/F N
//   p.gh.$/F N; p.gh.*/F N; p.ggf.$/F N; p.ggf.$/T N; p.ggg.*/F N; p.ggg.NE/T D; p.gggf.$/T N
//   p.gggg.NE/T D
// Raw initials = p.gg.*/F N; p.ggg.$/F N; p.ggg.*/F N; p.ggh.$/F N; p.ggh.*/F N; p.ggf.$/F N; p.gh.*/F N
//   p.hg.*/F N; p.hh.*/F N; p.gggf.$/F N; p.gggg.*/F N
Node read(Node p, Choice c) {
    if (c == null) return p.g;
    if (!c.useH) return read(p.g, c.next);
    Node t = read(p.h, c.next);
    return t.h;
}
// Published = p.gg.*/F → ret.M/F D; p.gh.*/F → ret.M/F D; p.hg.*/F → ret.M/F D; p.hh.*/F → ret.M/F D
//   p.gg.*/F → ret.h.M/F D; p.gh.*/F → ret.h.M/F D; p.hg.*/F → ret.h.M/F D; p.hh.*/F → ret.h.M/F D
//   p.gg.*/F → ret.hh.M/F D; p.gh.*/F → ret.hh.M/F D; p.hg.*/F → ret.hh.M/F D; p.hh.*/F → ret.hh.M/F D
//   p.ggg.*/F → ret.M/F D; p.ggh.*/F → ret.M/F D; p.ggg.*/F → ret.h.M/F D; p.ggh.*/F → ret.h.M/F D
//   p.ggg.*/F → ret.hh.M/F D; p.ggh.*/F → ret.hh.M/F D; p.gggf.*/F → ret.M/F D; p.gggg.*/F → ret.*/F N
//   p.gggg.*/F → ret.M/F D; p.gggf.*/F → ret.h.M/F D; p.gggg.*/F → ret.h.M/F D
//   p.gggf.*/F → ret.hh.M/F D; p.gggg.*/F → ret.hh.M/F D

```

## Recurrence and its proof scope

The clean return cone uses only the `g` recursive arm of the reader.
For a forward pair with depth `a ≥ 1`, the witness rows are
`[p.M/F | ret.gᵃ.*/F]` for the writer and
`[p.gᵃ.NE/F | ret.*/F]` for the reader. The saved base relation starts
the writer. A finite recursive unroll can give `gᵃ⁺¹.f` at the writer
output. The paired cap is `a+1`, so the forward result is `gᵃ⁺¹.NE`.
This can enter the reader both as the child STAR query and as a caller
binding. On the clean reader arm, reading one `g` and replaying the
deeper saved read on a shorter STAR produces root MAY/D. The published
reader row composes with the writer's cut. The root observation again
gives ZERO → DemandTarget.

Backward, the exact observation offers an exact root query at the reader.
One more `g` write in the reversed arm gives another cut, and the reversed
saved writer reads through the unknown suffix. Its result at the marking
point is MAY/D, so the next forward run can start the same marking
point. The two projected rows have depth `a+1`; the root Target key is
identical. The positive field cap preserves the head `h` on the
additional reversed branch, so that branch does not satisfy a clean
`g` output selector. A real NORMAL witness is impossible for this origin.

The Lean package calculates the two publications, the Target input and
the projected rows for arbitrary depths in this clean return cone. It
checks ordinary recursive writer and reader steps and same-direction and
opposite-direction NORMAL service. The induction uses the same fair
closure and retention of eligible providers and prepared child service
as the R39 recurrence. It does not establish that every native prepared
plan retains those providers at every depth. The cold reference checks
the whole paired model through run-5, and the extended pilot settled
through run-7. The native run-9 cutoff is a separate finite observation.
There is no hard limit in the scoped recurrence.

With R40, the complete path check proves absence for the only marking
origin. Its frozen certificate is available in run-3. Run-3 still closes
its current work and publishes DATA. At handoff the adapter removes the
certified root Target. Run-4 then has no root start, and run-5 has no
outgoing refinement. The repaired clean-cone proof shows a quiet suffix
for every later pair.

## Additional search rounds

| Search | Cases and result |
| --- | --- |
| Finite certificate versus independent word oracle | **882** unary nested grammars and regular languages. Nested chunks have length 0–2 over two fields. The independent oracle checks repeat counts through the square of the regular state count. Zero disagreements. |
| Cold C2, recursive body, C5, saved replay and handoff | **72** programs with different reader bases and field accesses before and after the recursive call. Marking and observation offsets include the root and one field. Three cases needed a continuation past run-7. All finished naturally through **run-11** with fixed inner worklists. Every shared-word case had a NORMAL observation and every certified empty case had none. |
| Native comparative positive controls | Adding a matching base preserves the original NORMAL observation at **run-7**. A second positive reaches the observer *only* through the nested arm, by reading `h.g.h`. Baseline and adapter both finish naturally at **run-5** with the NORMAL relation. The adapter performs zero handoff rewrites on the second case. |
| Native termination and boundary controls | A two-sided writer has a recurrence in the finite scalar pilot through **run-9**, but the native fixture stops naturally at **run-5**. It is a model alignment diagnostic. Existing loop, recursive and earlier comparative checks remain in the suite. |

The two-sided writer already differs at backward run-4. The scalar
reference produces root MAY/D and renews the source permission. Native
run-4 has two reader summary groups, zero writer summary groups and no
root Target. Run-5 therefore has an empty frontier. This locates the
first missing terminal transition in that control. The comparison did
not isolate the native admission or publication operation responsible.

The combined native suite passed **179 tests in 27 classes**. The Lean
audit passed **26 new constructive claims**. The cumulative receipt
contains **7,494 claims in 448 pinned modules**.

The independent repeat-count oracle is sufficient for this unary test
family. If an accepting derivation repeats the same pair of regular
states for the single nested owner along its chain, removing the part
between those two positions still gives a valid accepting derivation.
A shortest witness therefore needs at most the number of state pairs.
The generic empty-intersection proof has no such word or depth bound.

There is no further established termination or comparative soundness
counterexample in these checked families. Whole-engine progress and
complete extraction remain open. Two nested languages, alias effects
outside the complete route slice, and other unsupported grammar forms
keep their guidance. The previously recorded long native positive miss
also remains. It occurs before applying either path certificate.

[Proof sources and reproduction](../../spec/lean/proposals/two-sided-field-cycle-20261117/README.md).
The full captures are under `two-sided-field-cycle-20261117/` in the
[external data root](EXTERNAL_DATA.md).
