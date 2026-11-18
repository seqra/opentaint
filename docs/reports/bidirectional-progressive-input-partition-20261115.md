# Persistent input-partition investigation

15 November 2026. Production is unchanged. The proposal is
[progressive input partitions](../design/bidirectional-progressive-input-partition-20261115.md).
The previous owner-sharing solution is withdrawn as the solution to the
active task; its results remain historical.

The new mechanism keeps separate method/block owners and refines their
input plans. It has no pure-wrapper recognition precondition. The key
semantic changes are explicit: a refined local input selector can authorize
a deeper initial, and complete child services replace supported coarse
owned-query replay results. Output C5 remains paired with the original Dp.

## Results and latest reached runs

| Synthetic reference | Earlier selected approach | Persistent partition | Final DATA / Target demand |
| --- | --- | --- | --- |
| Nested read-two/write-two, three calls | Still repeats at run-31; uncapped recurrence proved separately | **run-9** | 0 / 0 |
| Read g, inner call, write g; three calls | Still repeats at run-31 | **run-11** | 0 / 0 |
| Field write/read round trip before call | Still repeats at run-31 | **run-9** | 0 / 0 |
| Post-call write g | Finishes run-13 | **run-13** | 0 / 0 |
| Two inner calls | Finishes run-15 | **run-15** | 0 / 0 |
| Read g before each call, no restoring write | — | **run-7** | 0 / 0; correctly no final observation |
| Old read f.g / write f, method-only | Existing terminating reference | **run-5** | 0 / 0 |
| Same transfers in inner read/write blocks | Existing terminating reference | **run-5** | 0 / 0 |
| Longer reader f.g.f.g.f | Existing terminating reference | **run-5** | 0 / 0 |
| Old ordinary read-two/write-two, uniform root | Existing terminating reference | **run-3** | 0 / 0 |

All positive rows retain the NORMAL observation. Every listed new completion
is checked from empty DATA/summary/trie stores, including within-run fixed
points and every handoff. The checker also verifies backward permission at
the actual producer before completion. The run-31 controls are bounded
exploratory captures; only the original nested control has the separate
uncapped recurrence proof. Do not infer an uncapped theorem for each variant
from a finite control capture.

No project experiment was run. Historical reached/completed/accepted-forward
positions stay OWASP **run-11/11/11**, Conductor **run-8/7/7** and
Stirling-PDF **run-11/10/9**. No integrated native non-empty-MAY implementation
was tested in this investigation.

## What makes the approach more general

All examples use ordinary analyzed code and configured T production and
observation rules. There are no loops, recursion, cleaners, library-MAY
models or special pass rules in the new counterexample family.

```java
// Producer: T is uniform only at return.f.g and descendants.
// Observer: checks T somewhere below its argument.

Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}

// Original nested case.
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}

// Positive nontransparent case. Each call preserves the outside g frame.
Node wrappedAtG(Node x, boolean down) {
    Node value = choose(x.g, down);
    Node result = new Node(); result.g = value;
    return result;
}

// Another nontransparent case, with two inner call stages.
Node twice(Node x, boolean a, boolean b) {
    return choose(choose(x, a), b);
}
```

Use three calls and an observation of the final result. `wrappedAtG` uses a
producer at `return.g.f.g`; the other positive examples use `return.f.g`.
The trie identifies an unknown accessor at the current operation, maps it
to the query's correlated suffix, and splits that input case on a later
same-direction run. Prefixes written/read around calls do not need a special
owner adapter. Complete child queries run the ordinary body, including its
ordinary calls, rather than trusting the presence of one NORMAL record as
proof of a complete callee model.

The read-only-g negative variant has no surviving three-call concrete path:
the first call returns a value under f; the next call requires g. Its empty
final observation is expected, not a missing positive regression.

## Proof scope

The current checker passes **375 new theorems**, **917 audited declarations**
across **45 modules**. Allowed foundational axioms are only `propext` and
`Quot.sound`. There are no custom axioms, classical choice, admitted claims
or native-evaluation proof shortcuts.

- `PartitionCover`: constructive point/child/residual ownership, whole
  continuation and transfer-image cover, paired-exit preservation, at-most-one
  installed edge, monotonicity and finite-priority progress.
- `PartitionMachine`: executable C2 planning, frozen shared masks, ordinary
  field transfers, direction-qualified saved replay, current-query binding,
  NORMAL precoverage, paired C5, real NE cuts and complete reply folding.
- Ten `Certificate*` modules: full cold states, quiescent rounds, every
  handoff/tree installation, backward producer permission and final DATA/Target
  frontier with the expected observations.
- `Compatibility`: dedicated MUST families remain independent of every trie,
  including the older selected-cleaner source families; unsupported operations
  keep their old results; no-demand saved replay on the real offer is unchanged.
  Earlier protected/cleaner, exact-root survivor, arbitrary-reader and wrapper
  repair proof packages are rechecked as dependencies.

The cleaner compatibility checks do not pretend to be a newly implemented
native cold scan. The new positive reference machine has no cleaner opcode;
cleaner transfer and the previously selected same-lane coverage are reused.
Native integration still needs the complete-child/correlation guards for
real marks, H, E/mx, aliases, ND and ports. Unsupported contributions remain
enabled. There is no proof of universal native termination.

## Differential screen and its limitation

Seed 15112026 generated 2,000 ordinary two-owner prefix-programs. Each has
one to three child branches, one or two parent branches, one to three outer
calls, and an EXACT or MUST producer. All naturally stopped before the
screening horizon **run-41**. The screen's maximum latest reached iteration
was **run-15**. A finite screen is not a termination
proof.

The screen classified 1,936 forward completions, 63 backward completions and
**one baseline-reference gap**, with no newly introduced failed check. The
backward completions were not treated as full observation proofs by this
screen. Its output checks are finite samples, not general language inclusion.

At case 1740, **both** the older and new executable reference stop at run-7
without a real point route. In path notation, the ordinary child branches
are `f -> f` and `g -> f.f`; parent branches are `read g; child` and
`child; write f.g`; production is exactly at g, with two parent calls.
The second parent branch twice permits:

```text
x.g.$/T -> y.f.g.f.f.$/T -> z.f.g.f.g.f.f.$/T
```

Both reference controls lose the last offer. This is outside the full-state
accepted reference certificates; it prevents interpreting the random screen
as whole-core completeness evidence. It is not evidence that the new input
partition caused this loss, or that production has the same issue. The
reproducer and old/new histories are saved by the screen and can be used for
an independent caller-guidance investigation. No production behavior was
changed to hide this case.

## Reproduction and artifacts

```bash
python scripts/demand_experiments/progressive-partition/capture.py \
  --out /absolute/external/reference \
  --lean-dir spec/lean/proposals/progressive-input-partition-20261115
python spec/lean/proposals/progressive-input-partition-20261115/check.py \
  --out /absolute/external/fresh-proof-directory
python scripts/demand_experiments/progressive-partition/audit.py \
  --count 2000 --out /absolute/external/random-screen.json
```

Current external directory:
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/progressive-partition-20261115/`.
It contains `proofs-v3/receipt.json`, all full reference captures under
`reference/`, and `random-screen-2000.json`. Generated logs, JSON and Lean
compiled artifacts stay outside the repository. The small Lean source
certificates remain in the repository for reproduction.

## Complete nested-case annotations

The owner frames use `x` for the parameter and `ret` for the return.
`[entry => exit]` is a paired demand in the current analysis direction.
Raw initials below are conditional FLOW/NORMAL hypotheses. Actual offers keep
their listed T/FLOW marks and layers. `$` is EXACT; NE is non-empty-MAY.
The executable MAY union can hide local refinement rows; all handoff rows
are listed separately. The annotations use the converged within-run state.

### Run-1, forward, limit 1

```java
// Demand: none
// Submitted: x.MAY/T,D, x.f.NE/T,D
// Initials: x.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published: x.*/FLOW -> ret.MAY/FLOW,D
// Handoff: ret.MAY/FLOW => x.*/FLOW
// Frozen trie: empty

// Demand: none
// Submitted: x.*/FLOW,N
// Initials: x.*/FLOW,N
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published: x.*/FLOW -> ret.MAY/FLOW,D; x.*/FLOW -> ret.f.NE/FLOW,D
// Handoff: ret.MAY/FLOW => x.*/FLOW; ret.f.NE/FLOW => x.*/FLOW
// Frozen trie: empty

```

Entry call packets: x.f.NE/T,D | y.MAY/T,D | z.MAY/T,D | w.MAY/T,D

### Run-2, backward, limit 1

```java
// Published: ret.*/FLOW -> x.MAY/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand: ret.MAY/FLOW => x.*/FLOW
// Submitted: ret.MAY/T,D
// Initials: ret.$/FLOW,N, ret.*/FLOW,N
// Handoff: x.MAY/FLOW => ret.*/FLOW
// Frozen trie: empty

// Published: ret.*/FLOW -> x.MAY/FLOW,D; ret.*/FLOW -> x.f.NE/FLOW,D; ret.f.*/FLOW -> x.MAY/FLOW,D; ret.f.*/FLOW -> x.f.NE/FLOW,D
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand: ret.MAY/FLOW => x.*/FLOW; ret.f.NE/FLOW => x.*/FLOW
// Submitted: ret.$/FLOW,N, ret.*/FLOW,N
// Initials: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.*/FLOW,N
// Handoff: x.MAY/FLOW => ret.*/FLOW; x.MAY/FLOW => ret.f.*/FLOW; x.f.NE/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.f.*/FLOW
// Frozen trie: empty

```

Entry call packets: w.MAY/T,D | z.MAY/T,D | y.MAY/T,D | x.MAY/T,D

### Run-3, forward, limit 2

```java
// Demand: x.MAY/FLOW => ret.*/FLOW
// Submitted: x.MAY/T,D, x.f.g.MUST/T,N
// Initials: x.$/FLOW,N, x.*/FLOW,N, x.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published: x.*/FLOW -> ret.MAY/FLOW,D; x.*/FLOW -> ret.f.NE/FLOW,D; x.f.*/FLOW -> ret.MAY/FLOW,D
// Handoff: ret.MAY/FLOW => x.*/FLOW; ret.MAY/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.*/FLOW
// Frozen trie: empty

// Demand: x.MAY/FLOW => ret.*/FLOW; x.MAY/FLOW => ret.f.*/FLOW; x.f.NE/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.f.*/FLOW
// Submitted: x.$/FLOW,N, x.*/FLOW,N, x.f.*/FLOW,N
// Initials: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published: x.*/FLOW -> ret.f.NE/FLOW,D; x.*/FLOW -> ret.f.f.*/FLOW,N; x.f.*/FLOW -> ret.MAY/FLOW,D; x.f.*/FLOW -> ret.f.MAY/FLOW,D; x.f.*/FLOW -> ret.f.NE/FLOW,D; x.f.*/FLOW -> ret.f.f.NE/FLOW,D
// Handoff: ret.MAY/FLOW => x.f.*/FLOW; ret.f.MAY/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.*/FLOW; ret.f.NE/FLOW => x.f.*/FLOW; ret.f.f.NE/FLOW => x.f.*/FLOW
// Frozen trie: x.f

```

Entry call packets: x.f.g.MUST/T,N | y.MAY/T,D | z.MAY/T,D | w.MAY/T,D

### Run-4, backward, limit 3

```java
// Published: ret.*/FLOW -> x.MAY/FLOW,D; ret.*/FLOW -> x.f.MAY/FLOW,D; ret.*/FLOW -> x.f.NE/FLOW,D; ret.*/FLOW -> x.f.f.*/FLOW,N; ret.f.*/FLOW -> x.MAY/FLOW,D; ret.f.*/FLOW -> x.f.NE/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand: ret.MAY/FLOW => x.*/FLOW; ret.MAY/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.*/FLOW
// Submitted: ret.MAY/T,D
// Initials: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.*/FLOW,N
// Handoff: x.MAY/FLOW => ret.*/FLOW; x.MAY/FLOW => ret.f.*/FLOW; x.f.MAY/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.f.*/FLOW
// Frozen trie: empty

// Published: ret.*/FLOW -> x.f.f.*/FLOW,N; ret.f.*/FLOW -> x.MAY/FLOW,D; ret.f.*/FLOW -> x.f.MAY/FLOW,D; ret.f.*/FLOW -> x.f.NE/FLOW,D; ret.f.*/FLOW -> x.f.f.NE/FLOW,D; ret.f.f.*/FLOW -> x.f.f.NE/FLOW,D
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand: ret.MAY/FLOW => x.f.*/FLOW; ret.f.MAY/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.*/FLOW; ret.f.NE/FLOW => x.f.*/FLOW; ret.f.f.NE/FLOW => x.f.*/FLOW
// Submitted: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.*/FLOW,N
// Initials: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.$/FLOW,N, ret.f.*/FLOW,N, ret.f.f.*/FLOW,N
// Handoff: x.MAY/FLOW => ret.f.*/FLOW; x.f.MAY/FLOW => ret.f.*/FLOW; x.f.NE/FLOW => ret.f.*/FLOW; x.f.f.NE/FLOW => ret.f.*/FLOW; x.f.f.NE/FLOW => ret.f.f.*/FLOW
// Frozen trie: ret.f

```

Entry call packets: w.MAY/T,D | z.MAY/T,D | y.MAY/T,D | x.MAY/T,D

### Run-5, forward, limit 4

```java
// Demand: x.MAY/FLOW => ret.*/FLOW; x.MAY/FLOW => ret.f.*/FLOW; x.f.MAY/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.f.*/FLOW
// Submitted: x.MAY/T,D, x.f.g.MUST/T,N, x.f.f.f.g.MUST/T,N
// Initials: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.*/FLOW,N, x.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published: x.*/FLOW -> ret.MAY/FLOW,D; x.*/FLOW -> ret.f.MAY/FLOW,D; x.*/FLOW -> ret.f.NE/FLOW,D; x.*/FLOW -> ret.f.f.*/FLOW,N; x.f.*/FLOW -> ret.MAY/FLOW,D; x.f.*/FLOW -> ret.f.MAY/FLOW,D; x.f.*/FLOW -> ret.f.NE/FLOW,D; x.f.*/FLOW -> ret.f.f.NE/FLOW,D; x.f.g.*/FLOW -> ret.f.NE/FLOW,D; x.f.g.*/FLOW -> ret.f.f.NE/FLOW,D; x.f.f.*/FLOW -> ret.f.NE/FLOW,D; x.f.f.*/FLOW -> ret.f.f.NE/FLOW,D
// Handoff: ret.MAY/FLOW => x.*/FLOW; ret.MAY/FLOW => x.f.*/FLOW; ret.f.MAY/FLOW => x.*/FLOW; ret.f.MAY/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.*/FLOW; ret.f.NE/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.f.g.*/FLOW; ret.f.NE/FLOW => x.f.f.*/FLOW; ret.f.f.NE/FLOW => x.f.*/FLOW; ret.f.f.NE/FLOW => x.f.g.*/FLOW; ret.f.f.NE/FLOW => x.f.f.*/FLOW
// Frozen trie: empty

// Demand: x.MAY/FLOW => ret.f.*/FLOW; x.f.MAY/FLOW => ret.f.*/FLOW; x.f.NE/FLOW => ret.f.*/FLOW; x.f.f.NE/FLOW => ret.f.*/FLOW; x.f.f.NE/FLOW => ret.f.f.*/FLOW
// Submitted: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.*/FLOW,N, x.f.f.*/FLOW,N
// Initials: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.*/FLOW,N, x.f.f.$/FLOW,N, x.f.f.*/FLOW,N
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published: none
// Handoff: none
// Frozen trie: x.f, x.f.f

```

Entry call packets: x.f.g.MUST/T,N | y.MAY/T,D, y.f.f.f.g.MUST/T,N | z.MAY/T,D, z.f.g.MUST/T,N | w.MAY/T,D, w.f.f.f.g.MUST/T,N

### Run-6, backward, limit 5

```java
// Published: ret.f.*/FLOW -> x.MAY/FLOW,D; ret.f.*/FLOW -> x.f.MAY/FLOW,D; ret.f.*/FLOW -> x.f.g.MAY/FLOW,D; ret.f.*/FLOW -> x.f.f.MAY/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand: ret.MAY/FLOW => x.*/FLOW; ret.MAY/FLOW => x.f.*/FLOW; ret.f.MAY/FLOW => x.*/FLOW; ret.f.MAY/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.*/FLOW; ret.f.NE/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.f.g.*/FLOW; ret.f.NE/FLOW => x.f.f.*/FLOW; ret.f.f.NE/FLOW => x.f.*/FLOW; ret.f.f.NE/FLOW => x.f.g.*/FLOW; ret.f.f.NE/FLOW => x.f.f.*/FLOW
// Submitted: ret.MAY/T,D
// Initials: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.$/FLOW,N, ret.f.*/FLOW,N, ret.f.f.*/FLOW,N
// Handoff: x.MAY/FLOW => ret.f.*/FLOW; x.f.MAY/FLOW => ret.f.*/FLOW; x.f.g.MAY/FLOW => ret.f.*/FLOW; x.f.f.MAY/FLOW => ret.f.*/FLOW
// Frozen trie: ret.f

// Published: none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand: none
// Submitted: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.$/FLOW,N, ret.f.*/FLOW,N, ret.f.f.*/FLOW,N
// Initials: none
// Handoff: none
// Frozen trie: ret.f, ret.f.f

```

Entry call packets: w.MAY/T,D | z.MAY/T,D | y.MAY/T,D | x.MAY/T,D

### Run-7, forward, limit 6

```java
// Demand: x.MAY/FLOW => ret.f.*/FLOW; x.f.MAY/FLOW => ret.f.*/FLOW; x.f.g.MAY/FLOW => ret.f.*/FLOW; x.f.f.MAY/FLOW => ret.f.*/FLOW
// Submitted: x.f.g.MUST/T,N, x.f.f.f.g.MUST/T,N, x.f.f.f.f.f.g.MUST/T,N
// Initials: x.$/FLOW,N, x.f.$/FLOW,N, x.f.g.MUST/FLOW,N, x.f.g.*/FLOW,N, x.f.f.$/FLOW,N, x.f.f.*/FLOW,N, x.f.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published: none
// Handoff: none
// Frozen trie: x.f

// Demand: none
// Submitted: x.$/FLOW,N, x.f.$/FLOW,N, x.f.g.MUST/FLOW,N, x.f.g.*/FLOW,N, x.f.f.$/FLOW,N, x.f.f.*/FLOW,N, x.f.f.f.*/FLOW,N
// Initials: none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published: none
// Handoff: none
// Frozen trie: x.f, x.f.f

```

Entry call packets: x.f.g.MUST/T,N | y.f.f.f.g.MUST/T,N | z.f.g.MUST/T,N, z.f.f.f.f.f.g.MUST/T,N | w.f.f.f.g.MUST/T,N, w.f.f.f.f.f.f.NE/T,D

### Run-8, backward, limit 7

```java
// Published: none
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand: none
// Submitted: ret.MAY/T,D
// Initials: none
// Handoff: none
// Frozen trie: ret.f, ret.f.f

// Published: none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand: none
// Submitted: none
// Initials: none
// Handoff: none
// Frozen trie: ret.f, ret.f.f

```

Entry call packets: w.MAY/T,D | z.MAY/T,D | y.MAY/T,D | x.MAY/T,D

### Run-9, forward, limit 8

```java
// Demand: none
// Submitted: x.f.g.MUST/T,N, x.f.f.f.g.MUST/T,N, x.f.f.f.f.f.g.MUST/T,N
// Initials: none
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published: none
// Handoff: none
// Frozen trie: x.f

// Demand: none
// Submitted: none
// Initials: none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published: none
// Handoff: none
// Frozen trie: x.f, x.f.f

```

Entry call packets: x.f.g.MUST/T,N | y.f.f.f.g.MUST/T,N | z.f.g.MUST/T,N, z.f.f.f.f.f.g.MUST/T,N | w.f.f.f.g.MUST/T,N, w.f.f.f.f.f.f.f.g.MUST/T,N

