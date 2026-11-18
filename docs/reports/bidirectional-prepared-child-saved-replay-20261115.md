# Existing child routing for saved replay

15 November 2026. [Proposal](../design/bidirectional-prepared-child-saved-replay-20261115.md).
Production is unchanged. The campaign remains paused.

The persistent-partition proposal can increase irrelevant body work. Its
metadata bound did not bound propagation. A reference regression had 18
executable summary rows instead of 2 at run-8, with no change in outer reply
packets or latest completed run-11.

The replacement applies existing prepared-child routing to a supported saved
NORMAL reader contribution. It creates no queries, refined initial origins,
new input bounds, persistent trie or extra call offers.

## Reference completions

| Required reference | New natural completion | Outcome |
| --- | --- | --- |
| Original nested read-two/write-two, three calls | **run-9** | NORMAL observation; DATA and Target demand empty |
| Prefix read g / call / suffix write g | **run-11** | Same |
| Ordinary field write/read round trip before call | **run-9** | Same |
| Post-call write g | **run-13** | Same |
| Two inner calls | **run-15** | Same |
| Read-only-g negative variant | **run-9** | Correctly no final observation |
| Old method-only read f.g / write f | **run-5** | NORMAL observation; complete frontier empty |
| Same transfers in inner read/write blocks | **run-5** | Same |
| Longer reader f.g.f.g.f | **run-5** | Same |
| Old uniform-root read-two/write-two | **run-3** | Same |
| Growth regression | **run-11** | Complete old state preserved at every run |

These are full cold reference checks. Every iteration starts from its actual
prior handoff, reaches an explicitly checked within-run fixed point and
retains backward producer permission. End assertions include the root
ZERO/Target frontier and expected report identity. Run-11/run-15 are natural
completions; the proof does not use a scan iteration hard limit.

No new native or project experiment was run. Historical reached/completed/
accepted-forward positions remain OWASP **run-11/11/11**, Conductor
**run-8/7/7**, Stirling-PDF **run-11/10/9**.

## Workload regression

The synthetic code has three ordinary wrapper branches and four ordinary
child branches. It has no loops, recursion, cleaners, special pass rule or
unresolved-library model. Production is uniform T at the returned g field;
two wrapper calls lead to a final MAY observation.

```java
Node child(Node x, int k) {
    Node t = new Node(), u = new Node(), r = new Node();
    switch (k) {
        case 0: t.f = x.g.g.g; u.g = t; r.f = u; return r;
        case 1: r.g = x.f.f; return r;
        case 2: t.f = x; u.f = t; r.g = u; return r;
        default: t.f = x.g.g; r.f = t; return r;
    }
}
Node wrapper(Node x, int branch, int a, int b) {
    if (branch == 0) return child(x.g.g, a);
    if (branch == 1) {
        Node t = new Node(); t.f = child(x.f, a);
        Node r = new Node(); r.f = t;
        return r;
    }
    return child(child(x.f.g.f, a), b);
}
```

| Metric | Old reference | Rejected persistent partition | Existing-child routing |
| --- | ---: | ---: | ---: |
| Run-8 raw entry keys | 4 | 21 | **4** |
| Run-8 executable summary rows | 2 | 18 | **2** |
| Run-8 local demand rows | 9 | 36 | **9** |
| Run-8 callee input facts | 13 | 29 | **13** |
| Run-8 outer reply facts | 4 | 4 | **4** |
| Sum of entry keys, runs 1–11 | 121 | 183 | **121** |
| Sum of executable summary memberships | 120 | 197 | **120** |
| Sum of local demand memberships | 121 | 209 | **121** |
| Sum of outer reply memberships | 65 | 72 | **65** |
| Latest reached/completed run | run-11 | run-11 | **run-11** |

These are reference memberships, not callback counts, elapsed times or JVM
memory. The growth certificate checks equal complete states in both modes
at **every run-1 through run-11**: method domains, current NORMAL/DEMAND rows,
outer packets, handoffs and retained NORMAL records. It does not infer
unchanged intermediate callback scheduling from equal final states.

## Why the new route is enough

At an owned call, an existing query P.* can replay a NORMAL reader requiring
v.f.f.* and produce MAY. The same prepared plan already has P.f.$ and P.f.*.
The point cannot read the remaining f; the suffix still produces MAY, with
the more precise premise P.f.*. Remove only the parent's duplicate reader
contribution, not another branch's MAY result.

The next backward row pairs that child with P.f.* instead of P.*. Its existing
relative C5 budget is two fields instead of one. This explains progress
without increasing a bound or creating a new query. The full reader need not
be solved by the first child, and the wrapper need not be transparent.

The original nested old-policy control still has the separately proved
uncapped cycle and was captured through run-31. The new DATA frontier is
empty after run-8; the real forward global cut/Target route remains until
**run-9**, when the NORMAL observation remains and all outgoing demand is empty.

## Screen and rejected alternatives

Two deterministic 600-program screens compare old and new complete reference
runs. They use positive ordinary prefix operations, nested calls, EXACT/MUST
production and MAY observation. One adds ordinary reads after calls.

| Screen | Largest new/old total summary-membership ratio | Latest new run reached |
| --- | ---: | ---: |
| Ordinary before-call reads / after-call writes | **1.000** | **run-21** |
| Additional after-call reads | **1.036** | **run-15** |

Two additional hierarchy diagnostics also complete: three relay owners above
the leaf at **run-13**, and two read/call/write wrappers at **run-11**. Both
have empty DATA/Target demand and two NORMAL final facts. These are finite
Python diagnostics, separate from the kernel-certified fixture set. Reproduce
with `hierarchy_cases.py --out /absolute/external/hierarchy-cases.json`.

All tested new references naturally completed within the run-31 screening
horizon. Finite completion and sampled counts are not a universal termination,
completeness or resource bound. The older reference-model point-route gap
(case 1740 in the previous report) remains an external validation limitation.

The slightly larger count is a remaining risk: dropping a broad MAY can
expose narrower facts, and future admission/caller work can increase. The
proved guarantee concerns a fixed prepared plan and native offer, not total
work over every subsequent iteration.

Exploratory alternatives were reduced before selecting this proposal:

- Dynamic loss-site origin refinement solved the required examples, but its
  newly created origins were unused in all of them. It was unnecessary.
- Composing a full saved guard into the current premise at once increased
  the two-inner-call reference's run-6 summary rows from 2 to 17. It is rejected.
- Restarting child inputs at method entry caused the growth regression above.

The selected candidate changes none of those mechanisms. Its hot path only
filters an old contribution using an already proved, stable child cover.

## Proofs and artifacts

The full checker passes **368 new theorems, 910 audited declarations across
46 modules**. It permits only `propext` and `Quot.sound`; there is no custom
axiom, classical choice, admitted claim or native proof shortcut.

The package checks concrete prefix coverage, point/suffix completeness,
unchanged native results, filter-only output/postprocessing bounds, unchanged
C2 families, safe fallbacks and complete cold states. Native alias, ND and
port adapters remain activation obligations; unsupported cases keep old work.
Proof counts and exact receipt are recorded in the linked package README.

```bash
python scripts/demand_experiments/operation-local-refinement/capture_prepared.py \
  --out /absolute/external/reference \
  --lean-dir spec/lean/proposals/prepared-child-saved-replay-20261115
python spec/lean/proposals/prepared-child-saved-replay-20261115/check.py \
  --out /absolute/external/fresh-proof-directory
python scripts/demand_experiments/operation-local-refinement/audit.py \
  --count 600 --out /absolute/external/growth-screen.json
python scripts/demand_experiments/operation-local-refinement/audit.py \
  --count 600 --post-reads --out /absolute/external/post-read-screen.json
```

External artifacts:
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/prepared-child-saved-replay-20261115/`.
This includes all per-run initial/demand/publication annotations as JSON,
proof receipts/logs and screening inputs. Small formal source certificates
remain in the repository; bulk outputs and compiled artifacts stay outside it.
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

```

Entry call packets: x.f.NE/T,D | y.MAY/T,D | z.MAY/T,D | w.MAY/T,D

### Run-2, backward, limit 1

```java
// Published: ret.*/FLOW -> x.MAY/FLOW,D; ret.*/FLOW -> x.f.NE/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand: ret.MAY/FLOW => x.*/FLOW
// Submitted: ret.MAY/T,D
// Initials: ret.$/FLOW,N, ret.*/FLOW,N
// Handoff: x.MAY/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.*/FLOW

// Published: ret.*/FLOW -> x.f.NE/FLOW,D; ret.f.*/FLOW -> x.MAY/FLOW,D; ret.f.*/FLOW -> x.f.NE/FLOW,D
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand: ret.MAY/FLOW => x.*/FLOW; ret.f.NE/FLOW => x.*/FLOW
// Submitted: ret.$/FLOW,N, ret.*/FLOW,N
// Initials: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.$/FLOW,N, ret.f.*/FLOW,N
// Handoff: x.MAY/FLOW => ret.f.*/FLOW; x.f.NE/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.f.*/FLOW

```

Entry call packets: w.MAY/T,D | z.MAY/T,D | y.MAY/T,D | x.MAY/T,D

### Run-3, forward, limit 2

```java
// Demand: x.MAY/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.*/FLOW
// Submitted: x.MAY/T,D, x.f.g.MUST/T,N
// Initials: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published: x.*/FLOW -> ret.MAY/FLOW,D; x.*/FLOW -> ret.f.NE/FLOW,D; x.f.*/FLOW -> ret.MAY/FLOW,D; x.f.g.*/FLOW -> ret.MAY/FLOW,D
// Handoff: ret.MAY/FLOW => x.*/FLOW; ret.MAY/FLOW => x.f.*/FLOW; ret.MAY/FLOW => x.f.g.*/FLOW; ret.f.NE/FLOW => x.*/FLOW

// Demand: x.MAY/FLOW => ret.f.*/FLOW; x.f.NE/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.f.*/FLOW
// Submitted: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.*/FLOW,N
// Initials: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.*/FLOW,N
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published: x.*/FLOW -> ret.f.f.*/FLOW,N; x.f.*/FLOW -> ret.MAY/FLOW,D; x.f.*/FLOW -> ret.f.MAY/FLOW,D; x.f.*/FLOW -> ret.f.NE/FLOW,D; x.f.*/FLOW -> ret.f.f.NE/FLOW,D; x.f.g.*/FLOW -> ret.f.NE/FLOW,D; x.f.g.*/FLOW -> ret.f.f.NE/FLOW,D
// Handoff: ret.MAY/FLOW => x.f.*/FLOW; ret.f.MAY/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.f.g.*/FLOW; ret.f.f.NE/FLOW => x.f.*/FLOW; ret.f.f.NE/FLOW => x.f.g.*/FLOW

```

Entry call packets: x.f.g.MUST/T,N | y.MAY/T,D | z.MAY/T,D | w.MAY/T,D

### Run-4, backward, limit 3

```java
// Published: ret.*/FLOW -> x.MAY/FLOW,D; ret.*/FLOW -> x.f.MAY/FLOW,D; ret.*/FLOW -> x.f.NE/FLOW,D; ret.*/FLOW -> x.f.g.MAY/FLOW,D; ret.*/FLOW -> x.f.f.*/FLOW,N; ret.f.*/FLOW -> x.MAY/FLOW,D; ret.f.*/FLOW -> x.f.MAY/FLOW,D; ret.f.*/FLOW -> x.f.NE/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand: ret.MAY/FLOW => x.*/FLOW; ret.MAY/FLOW => x.f.*/FLOW; ret.MAY/FLOW => x.f.g.*/FLOW; ret.f.NE/FLOW => x.*/FLOW
// Submitted: ret.MAY/T,D
// Initials: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.$/FLOW,N, ret.f.*/FLOW,N
// Handoff: x.MAY/FLOW => ret.*/FLOW; x.MAY/FLOW => ret.f.*/FLOW; x.f.MAY/FLOW => ret.*/FLOW; x.f.MAY/FLOW => ret.f.*/FLOW; x.f.NE/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.f.*/FLOW; x.f.g.MAY/FLOW => ret.*/FLOW

// Published: ret.*/FLOW -> x.f.f.*/FLOW,N; ret.f.*/FLOW -> x.f.MAY/FLOW,D; ret.f.*/FLOW -> x.f.g.MAY/FLOW,D; ret.f.*/FLOW -> x.f.f.NE/FLOW,D; ret.f.f.*/FLOW -> x.f.f.NE/FLOW,D
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand: ret.MAY/FLOW => x.f.*/FLOW; ret.f.MAY/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.f.g.*/FLOW; ret.f.f.NE/FLOW => x.f.*/FLOW; ret.f.f.NE/FLOW => x.f.g.*/FLOW
// Submitted: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.$/FLOW,N, ret.f.*/FLOW,N
// Initials: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.$/FLOW,N, ret.f.*/FLOW,N, ret.f.f.$/FLOW,N, ret.f.f.*/FLOW,N
// Handoff: x.f.MAY/FLOW => ret.f.*/FLOW; x.f.g.MAY/FLOW => ret.f.*/FLOW; x.f.f.NE/FLOW => ret.f.*/FLOW; x.f.f.NE/FLOW => ret.f.f.*/FLOW

```

Entry call packets: w.MAY/T,D | z.MAY/T,D | y.MAY/T,D | x.MAY/T,D

### Run-5, forward, limit 4

```java
// Demand: x.MAY/FLOW => ret.*/FLOW; x.MAY/FLOW => ret.f.*/FLOW; x.f.MAY/FLOW => ret.*/FLOW; x.f.MAY/FLOW => ret.f.*/FLOW; x.f.NE/FLOW => ret.*/FLOW; x.f.NE/FLOW => ret.f.*/FLOW; x.f.g.MAY/FLOW => ret.*/FLOW
// Submitted: x.MAY/T,D, x.f.g.MUST/T,N, x.f.f.f.g.MUST/T,N
// Initials: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.$/FLOW,N, x.f.g.MUST/FLOW,N, x.f.g.*/FLOW,N, x.f.f.$/FLOW,N, x.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published: x.*/FLOW -> ret.f.NE/FLOW,D; x.*/FLOW -> ret.f.f.*/FLOW,N; x.f.*/FLOW -> ret.MAY/FLOW,D; x.f.*/FLOW -> ret.f.MAY/FLOW,D; x.f.*/FLOW -> ret.f.NE/FLOW,D; x.f.*/FLOW -> ret.f.f.NE/FLOW,D; x.f.g.MUST/FLOW -> ret.f.NE/FLOW,D; x.f.g.*/FLOW -> ret.f.NE/FLOW,D; x.f.g.*/FLOW -> ret.f.f.NE/FLOW,D; x.f.f.*/FLOW -> ret.f.NE/FLOW,D; x.f.f.*/FLOW -> ret.f.f.NE/FLOW,D
// Handoff: ret.MAY/FLOW => x.f.*/FLOW; ret.f.MAY/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.*/FLOW; ret.f.NE/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.f.g.MUST/FLOW; ret.f.NE/FLOW => x.f.g.*/FLOW; ret.f.NE/FLOW => x.f.f.*/FLOW; ret.f.f.NE/FLOW => x.f.*/FLOW; ret.f.f.NE/FLOW => x.f.g.*/FLOW; ret.f.f.NE/FLOW => x.f.f.*/FLOW

// Demand: x.f.MAY/FLOW => ret.f.*/FLOW; x.f.g.MAY/FLOW => ret.f.*/FLOW; x.f.f.NE/FLOW => ret.f.*/FLOW; x.f.f.NE/FLOW => ret.f.f.*/FLOW
// Submitted: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.$/FLOW,N, x.f.g.MUST/FLOW,N, x.f.g.*/FLOW,N, x.f.f.$/FLOW,N, x.f.f.*/FLOW,N
// Initials: x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.$/FLOW,N, x.f.g.MUST/FLOW,N, x.f.g.*/FLOW,N, x.f.f.$/FLOW,N, x.f.f.*/FLOW,N
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published: none
// Handoff: none

```

Entry call packets: x.f.g.MUST/T,N | y.MAY/T,D, y.f.f.f.g.MUST/T,N | z.MAY/T,D, z.f.g.MUST/T,N | w.MAY/T,D, w.f.f.f.g.MUST/T,N

### Run-6, backward, limit 5

```java
// Published: ret.f.*/FLOW -> x.MAY/FLOW,D; ret.f.*/FLOW -> x.f.MAY/FLOW,D; ret.f.*/FLOW -> x.f.g.MAY/FLOW,D; ret.f.*/FLOW -> x.f.f.MAY/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand: ret.MAY/FLOW => x.f.*/FLOW; ret.f.MAY/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.*/FLOW; ret.f.NE/FLOW => x.f.*/FLOW; ret.f.NE/FLOW => x.f.g.MUST/FLOW; ret.f.NE/FLOW => x.f.g.*/FLOW; ret.f.NE/FLOW => x.f.f.*/FLOW; ret.f.f.NE/FLOW => x.f.*/FLOW; ret.f.f.NE/FLOW => x.f.g.*/FLOW; ret.f.f.NE/FLOW => x.f.f.*/FLOW
// Submitted: ret.MAY/T,D
// Initials: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.$/FLOW,N, ret.f.*/FLOW,N, ret.f.f.$/FLOW,N, ret.f.f.*/FLOW,N
// Handoff: x.MAY/FLOW => ret.f.*/FLOW; x.f.MAY/FLOW => ret.f.*/FLOW; x.f.g.MAY/FLOW => ret.f.*/FLOW; x.f.f.MAY/FLOW => ret.f.*/FLOW

// Published: none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand: none
// Submitted: ret.$/FLOW,N, ret.*/FLOW,N, ret.f.$/FLOW,N, ret.f.*/FLOW,N, ret.f.f.$/FLOW,N, ret.f.f.*/FLOW,N
// Initials: none
// Handoff: none

```

Entry call packets: w.MAY/T,D | z.MAY/T,D | y.MAY/T,D | x.MAY/T,D

### Run-7, forward, limit 6

```java
// Demand: x.MAY/FLOW => ret.f.*/FLOW; x.f.MAY/FLOW => ret.f.*/FLOW; x.f.g.MAY/FLOW => ret.f.*/FLOW; x.f.f.MAY/FLOW => ret.f.*/FLOW
// Submitted: x.MAY/T,D, x.f.MAY/T,D, x.f.g.MUST/T,N, x.f.f.f.g.MUST/T,N, x.f.f.f.f.f.g.MUST/T,N
// Initials: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.$/FLOW,N, x.f.g.MUST/FLOW,N, x.f.g.*/FLOW,N, x.f.f.$/FLOW,N, x.f.f.*/FLOW,N, x.f.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published: x.f.*/FLOW -> ret.f.MAY/FLOW,D
// Handoff: ret.f.MAY/FLOW => x.f.*/FLOW

// Demand: none
// Submitted: x.$/FLOW,N, x.*/FLOW,N, x.f.$/FLOW,N, x.f.*/FLOW,N, x.f.g.$/FLOW,N, x.f.g.MUST/FLOW,N, x.f.g.*/FLOW,N, x.f.f.$/FLOW,N, x.f.f.*/FLOW,N, x.f.f.f.*/FLOW,N
// Initials: none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published: none
// Handoff: none

```

Entry call packets: x.f.g.MUST/T,N | y.f.MAY/T,D, y.f.f.f.g.MUST/T,N | z.MAY/T,D, z.f.g.MUST/T,N, z.f.f.f.f.f.g.MUST/T,N | w.MAY/T,D, w.f.f.f.g.MUST/T,N

### Run-8, backward, limit 7

```java
// Published: none
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand: ret.f.MAY/FLOW => x.f.*/FLOW
// Submitted: ret.MAY/T,D
// Initials: ret.f.$/FLOW,N, ret.f.*/FLOW,N, ret.f.f.$/FLOW,N, ret.f.f.*/FLOW,N
// Handoff: none

// Published: none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand: none
// Submitted: ret.f.$/FLOW,N, ret.f.*/FLOW,N, ret.f.f.$/FLOW,N, ret.f.f.*/FLOW,N
// Initials: none
// Handoff: none

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

```

Entry call packets: x.f.g.MUST/T,N | y.f.f.f.g.MUST/T,N | z.f.g.MUST/T,N, z.f.f.f.f.f.g.MUST/T,N | w.f.f.f.g.MUST/T,N, w.f.f.f.f.f.f.f.g.MUST/T,N

