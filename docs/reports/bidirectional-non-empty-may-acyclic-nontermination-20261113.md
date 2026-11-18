# Non-empty MAY does not ensure termination on an acyclic program

13 November 2026. Counterexample to convergence under
[the non-empty-MAY specification](../../spec/non-empty-may.md), with **no
iteration limit**. No production change or project measurement is made.
Follow [the proof guide](../../spec/proof-guide.md).
No semantic change is proposed here: the example uses the selected C2,
C5, normalization, priority, call, Target and compaction rules as written.

The program and its call graph have no loop or recursion. Nevertheless, the
same root FLOW demand survives every forward handoff. This is a cycle
between analysis runs, not an infinite execution of one CFG.

The later [BB-demand retrace](bidirectional-non-empty-may-basic-block-retrace-20261113.md)
uses different internal summary scopes. Its read BB becomes precise at
run-4; a different enclosing-method demand cycle remains from run-5.
Do not reuse this document's root-row trace as the BB-policy trace.

## 1. Program and configuration

```java
class Box { Box f; Box g; }

void main(boolean flag) {
    Box a = sourceAtF();
    Box b = choose(a, flag);       // call 1
    Box c = choose(b, flag);       // call 2: the SAME analyzed MethodKey
    sinkAnywhere(c);
}

Box choose(Box p, boolean flag) {
    if (flag) {
        return p.f.g;
    } else {
        Box q = new Box();
        q.f = p;
        return q;
    }
}
```

The two APIs have these configured rules. They are external rule-bearing
APIs, not additional analyzed bodies or predefined transfer summaries:

```text
sourceAtF(): unconditional source; assign full mark T at ret.f and all
             descendants, including ret.f itself.
             Its result is ret.f.MUST/T, NORMAL.

sinkAnywhere(x): sink literal x.MAY/T; check x and its descendants.
                 Its reverse seed is x.MAY/T, DEMAND.
```

Use FULL marks, the selected `1,1,2,3,...` field limits and an uncapped run
schedule. Disable aliases to isolate the example; no alias inference is
needed. There is one full mark T, no cleaners, statics, ND, exclusions or
protected memberships. Both calls resolve to the same `choose` owner.

There are two analyzed blocks: `main` and `choose`. Neither requires loop
decomposition. `sourceAtF`, `sinkAnywhere` and allocation are modeled at
their call sites. They do not contain hidden loops or recursion.

Notation:

```text
N = NORMAL; D = DEMAND; M = MAY; NE = non-empty MAY; U = MUST
F = FLOW mark slot; $ = EXACT; * = correlated STAR

choose forward demand R_F:   p.*/F   -> ret.M/F, D
choose backward demand R_B:  ret.*/F -> p.M/F,   D
main control demand R_Z:     ZERO -> DemandTarget, D

For an incoming row write [entry Dc ; exit Dp].
All query initials below start as identities.
```

The annotations give a **closed witness trace**, including its admission
companions, for every run. They do not claim that these are the entire
engine dumps. Other queries, NORMAL providers and paired rows may coexist.
They are retained; section 4 explains why they cannot remove these witnesses.
In particular, the proof does not freeze an incomplete NORMAL store or
assume identical complete frontiers. Trivial ZERO completions and unchanged
parameter identities are not repeated in the code annotations.

## 2. Why two calls matter

The first actual is always `p.f.U/T,N`. With entry demand `p.M/F`, C2's
first-new-field policy emits:

```text
p.f.*/F -> p.f.*/F,N       // first new field; old MUST policy at this step
p.$/F   -> p.$/F,N         // selected conditional FLOW prefix probe
```

This does **not** use the same-head dedicated MUST lane: the submitted head
`p.f` is below the demand head `p`. The raw `p.f.*` query reads its known f,
then reads g from an unknown STAR suffix:

```text
p.f.*/F,N --read f--> temporary.*/F,N --read g--> ret.M/F,D
```

There is no field cut in this route. Applying its admitted summary to the
original actual `p.f.U/T,N` gives `b.M/T,D`. It does not replace that actual
by an invented MAY application view.

At call 2, this derived `b.M/T,D` supplies both same-head C2 alternatives:

```text
p.$/F -> p.$/F,N
p.*/F -> p.*/F,N
```

The second query publishes `R_F`. Because both calls use one owner, its
publication is also delivered to call 1. Each offer is demand-admitted;
delivery uses ordinary summary matching, not equality with the caller's
particular emitted initial list. Even before that delivery, the first
partial query has already supplied the second call. No circular input is
postulated to start the within-run derivation.

If the only source were `p.U/T,N` at the root, the dedicated MUST lane could
break this particular bootstrap. The named source field f is intentional.

## 3. Per-iteration trace

### Run-1: forward, field limit 1

```java
// Incoming demand: none (unrestricted run-1).
// Submitted: ZERO,N. Initial: ZERO -> ZERO,N.
void main(boolean flag) {
    Box a = sourceAtF();        // ZERO -> a.f.U/T,N; f fits limit 1.
    Box b = choose(a, flag);    // Submitted p.f.U/T,N.
                               // R_F application supplies b.M/T,D.
    Box c = choose(b, flag);    // Submitted p.M/T,D.
                               // R_F application supplies c.M/T,D.
    sinkAnywhere(c);           // DEMAND witness -> DemandTarget.
}
// Published cycle summary: ZERO -> DemandTarget,D.

// Incoming demand: none.
// Submitted at call 1: p.f.U/T,N; at call 2: p.M/T,D.
// Run-1 abstract initial: p.*/F -> p.*/F,N.
// The sink's ordinary run-1 mark request also enables p.*/T on D.
// Its T rows are covered by the matching FLOW rows below.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.f.g;          // p.* -> ret.M/F,D: an unknown-suffix read.
    } else {
        Box q = new Box();
        q.f = p;               // p.* -> q.f.*/F,N; one known field.
        return q;              // p.* -> ret.f.*/F,N.
    }
}
// Published NORMAL return provider: p.*/F -> ret.f.*/F,N.
// Published cycle demand R_F:       p.*/F -> ret.M/F,D.
// Handoff includes [ret.M/F ; p.*/F] for run-2.
```

### Run-2: backward, field limit 1

For backward runs, published summaries appear **above** each declaration;
incoming demand, submitted facts and initials appear **below** it.

```java
// Published cycle summary: ZERO -> DemandTarget,D.
void main(boolean flag) {
    Box a = sourceAtF();        // Reverse a.M/T,D overlaps the real source
                               // region a.f.U/T; record source permission
                               // and finish at DemandTarget.
    Box b = choose(a, flag);    // Reverse call 1 receives b.M/T,D;
                               // R_B gives a.M/T,D.
    Box c = choose(b, flag);    // Reverse call 2 receives c.M/T,D;
                               // R_B gives b.M/T,D.
    sinkAnywhere(c);           // Reverse seed: c.M/T,D.
}
// Incoming demand: [Target ; ZERO].
// Submitted: ZERO,N at the backward method boundary.
// Initial: ZERO -> ZERO,N. NormalTarget is not used backward.

// Published cycle demand R_B: ret.*/F -> p.M/F,D.
// The cut sibling ret.* -> p.f.NE/F,D is covered by R_B.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.f.g;          // Reverse ret.* -> p.f.g.*/F,N.
                               // Global limit 1 cuts it to p.f.NE/F,D.
    } else {
        Box q = new Box();
        q.f = p;               // Reverse unknown read f: q.* -> p.M/F,D.
        return q;              // Reverse ret.* -> q.*.
    }
}
// Incoming demand: [ret.M/F ; p.*/F].
// Submitted at call 2: ret.M/T,D, from the sink seed.
// Submitted at call 1: ret.M/T,D, derived by reverse call 2.
// Initials: ret.$/F -> ret.$/F,N; ret.*/F -> ret.*/F,N.
// Raw ret.$ can produce the cut child; raw ret.* produces R_B.
// Handoff includes [p.M/F ; ret.*/F] for run-3.
```

### Run-3: forward, field limit 2

```java
// Incoming demand: [Target ; ZERO].
// Submitted: ZERO,N. Initial: ZERO -> ZERO,N.
void main(boolean flag) {
    Box a = sourceAtF();        // Permitted by the real run-2 source hit:
                               // a.f.U/T,N.
    Box b = choose(a, flag);    // p.f.U/T,N -> partial-query ret.M/F,D
                               // applied to this actual -> b.M/T,D.
    Box c = choose(b, flag);    // b.M/T,D starts root p.*; R_F -> c.M/T,D.
    sinkAnywhere(c);           // ZERO -> DemandTarget,D.
}
// Published cycle summary: ZERO -> DemandTarget,D.

// Incoming demand includes [p.M/F ; ret.*/F].
// Submitted at call 1: p.f.U/T,N.
// Its initials: p.f.*/F -> p.f.*/F,N; p.$/F -> p.$/F,N.
// Derived submitted at call 2: p.M/T,D.
// Its initials: p.$/F -> p.$/F,N; p.*/F -> p.*/F,N.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.f.g;          // p.f.* -> ret.M/F,D; p.* -> ret.M/F,D.
    } else {
        Box q = new Box();
        q.f = p;               // p.$ -> q.f.$/F,N.
                               // p.f.* -> q.f.f.*/F,N.
        return q;              // The latter fits global limit 2, but its
                               // root paired Dp has budget 0+1=1:
                               // p.f.* -> ret.f.NE/F,D.
    }
}
// Raw p.$ NORMAL pair normalizes to p.* -> ret.f.*/F,N.
// Published partial demand: p.f.*/F -> ret.M/F,D.
// Its ret.f.NE sibling is covered by its root MAY conclusion.
// Published cycle demand R_F: p.*/F -> ret.M/F,D.
// Other paired rows may preserve extra NORMAL providers.
// Handoff AGAIN includes [ret.M/F ; p.*/F].
```

### Run-4: backward, field limit 3

```java
// Published cycle summary: ZERO -> DemandTarget,D.
void main(boolean flag) {
    Box a = sourceAtF();        // Reverse a.M/T,D again hits a.f.U/T;
                               // source permission is renewed.
    Box b = choose(a, flag);    // b.M/T,D -> a.M/T,D.
    Box c = choose(b, flag);    // c.M/T,D -> b.M/T,D.
    sinkAnywhere(c);           // Reverse seed c.M/T,D.
}
// Incoming demand: [Target ; ZERO].
// Submitted: ZERO,N. Initial: ZERO -> ZERO,N.

// Published cycle demand R_B: ret.*/F -> p.M/F,D.
// Extra paired row [ret.M/F ; p.f.*/F] can also retain the NORMAL
// relation ret.*/F -> p.f.g.*/F,N, with its own output budget 2.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.f.g;          // Reverse ret.* -> p.f.g.*/F,N.
                               // Under the ROOT paired Dp, budget 1
                               // still cuts this sibling to p.f.NE,D.
    } else {
        Box q = new Box();
        q.f = p;               // Reverse q.* -> p.M/F,D: no cut.
        return q;
    }
}
// Incoming demand includes [ret.M/F ; p.*/F].
// Submitted at call 2: ret.M/T,D, from the renewed sink seed.
// Submitted at call 1: ret.M/T,D, from reverse call 2.
// Initials for this row: ret.$/F,N and ret.*/F,N, both identities.
// The root row keeps ret.* -> p.M; it is not intersected using the
// deeper row's p.f exit. Do not mix the pairs.
// Handoff AGAIN includes [p.M/F ; ret.*/F].
```

### Every later forward run: run-(2k+1), k >= 2

This is the per-run trace for run-5, run-7, run-9, and every later odd run;
its global field limit is 2k.

```java
// Incoming demand contains [Target ; ZERO].
// Submitted: ZERO,N. Initial: ZERO -> ZERO,N.
void main(boolean flag) {
    Box a = sourceAtF();        // Renewed permission -> a.f.U/T,N.
    Box b = choose(a, flag);    // The partial query still supplies b.M/T,D.
    Box c = choose(b, flag);    // Its MAY offer still starts root p.*.
    sinkAnywhere(c);           // c.M/T,D still produces DemandTarget.
}
// Published: ZERO -> DemandTarget,D.
// A NORMAL report may also exist. It does not remove DemandTarget.

// Incoming demand contains [p.M/F ; ret.*/F].
// Submitted at call 1: p.f.U/T,N.
// Its initials: p.f.*/F,N and p.$/F,N, both identities.
// Derived submitted at call 2: p.M/T,D.
// Its initials: p.$/F,N and p.*/F,N, both identities.
// Saved NORMAL replay can add precise/MUST offers and their queries;
// it neither replaces nor cancels these successful admissions.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.f.g;          // Partial query -> ret.M/F,D.
                               // Root query -> ret.M/F,D.
    } else {
        Box q = new Box();
        q.f = p;
        return q;
    }
}
// Published and retained: R_F = p.*/F -> ret.M/F,D.
// Also derived: p.f.*/F -> ret.M/F,D; its separate retention is not needed.
// Existing NORMAL read/write/MUST providers stay available.
// Handoff contains [ret.M/F ; p.*/F] for run-(2k+2).
```

### Every later backward run: run-(2k+2), k >= 2

This covers run-6, run-8, run-10, and every later even run; its limit is
2k+1. The same trace also applies to run-4 for the root witness.

```java
// Published: ZERO -> DemandTarget,D.
void main(boolean flag) {
    Box a = sourceAtF();        // a.M/T,D reaches the actual source rule.
    Box b = choose(a, flag);    // b.M/T,D -> a.M/T,D.
    Box c = choose(b, flag);    // c.M/T,D -> b.M/T,D.
    sinkAnywhere(c);           // c.M/T,D is the reverse sink seed.
}
// Incoming demand contains [Target ; ZERO].
// Submitted: ZERO,N. Initial: ZERO -> ZERO,N.

// Published and retained: R_B = ret.*/F -> p.M/F,D.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.f.g;          // Known-prefix inverse; extra providers
                               // do not suppress the other branch.
    } else {
        Box q = new Box();
        q.f = p;               // Root STAR's unknown read f -> p.M/F,D.
        return q;
    }
}
// Incoming demand contains [ret.M/F ; p.*/F].
// Submitted at call 2: ret.M/T,D, derived from the sink.
// Submitted at call 1: ret.M/T,D, derived from reverse call 2.
// Initials: ret.$/F,N and ret.*/F,N, both identities.
// Handoff contains [p.M/F ; ret.*/F] for run-(2k+3).
```

## 4. Non-termination proof

Let H_r be the final post-compaction handoff after run-r. The invariant is:

```text
for every k >= 0:
    R_F belongs to the outgoing guidance at H_(2k+1)
    R_Z belongs to the outgoing guidance at H_(2k+1)

for every k >= 0:
    R_B belongs to the outgoing guidance at H_(2k+2)
    R_Z belongs to the outgoing guidance at H_(2k+2)
```

Membership means the retained logical membership, not a duplicate object or
callback count. An equal provider replacing the object is the same witness.

**Base.** Run-1 starts the ordinary root FLOW abstraction of `choose`.
The read branch emits its intrinsic root MAY; ordinary mark-request handling
lets its concrete application reach the sink. Thus it publishes R_F and
R_Z. The code derives the second call's MAY input from the first call.

**Backward step.** R_F gives the complete paired row
`[ret.M/F ; p.*/F]`. R_Z enables the root's backward ZERO and the sink seed.
The seed supplies `ret.M/T,D` at call 2. C2 admits raw `ret.*`, whose reverse
write reads f from an unknown suffix and produces `p.M/F,D`. C5 accepts this
**actual raw initial**, keeps the root MAY under exit `p.*`, and does not
cut it. Therefore R_B is published. Its application supplies the first
call's backward MAY input, then reaches the real `a.f` source. This renews
the source permission and the root terminal R_Z. No source hit is invented
by the proof; MAY overlaps the source's actual named field.

**Forward step.** R_B gives `[p.M/F ; ret.*/F]`. R_Z admits main's ZERO.
The renewed source supplies `p.f.U/T,N`. The complete C2 family contains
`p.f.*` and the conditional raw `p.$/FLOW` probe. The first query's read
branch produces root MAY; its summary application supplies the second
call's MAY input. That input admits raw `p.*`, whose read branch produces
root MAY again. Raw-entry C5 and the same paired root exit retain R_F.
Applying it at the second call reaches the sink on D and republishes R_Z.

The step uses **fresh derivations in this run**, not replay of old DEMAND
summaries. Repeating a query in a later run is allowed; within one run,
ordinary deduplication still handles each fixed membership once.

**Why retained NORMAL summaries do not break the invariant.** Saved NORMAL
replay runs first on each original actual, as specified. It can add valid
precise results, MUST results and a confirmed report. The selected call
policy still admits a successful C2 family and subscribes to current
summaries; NORMAL replay is not a short-circuit. The source's original
`a.f.U/T,N` remains an offer. A MAY/D offer is not deleted by a MUST/N fact:
the selected MUST canonicalization keeps mark/layer/flag classes, and adds
no MUST-to-MAY replacement. NormalTarget does not erase DemandTarget.

**Why compaction does not delete R_F or R_B.** Both have a root, unrestricted
FLOW original, an independent root MAY conclusion, Empty E/mx, and H=false.
There is no weaker DATA premise or broader MAY head in that owner. A
duplicate may replace them with an equal membership. A deeper-premise row,
MUST query, or concrete-mark row is not a weaker root FLOW original. No ZERO
producer exists inside `choose`, and the program has no ND origin.

The NORMAL STAR relations of its return branches are only specializations
of these two relations (and their inverses):

```text
p.f.g.* -> ret.*    // read two fields
p.*     -> ret.f.*  // write one field
```

Neither is an independent root MAY relation. For example, the input root
point and output root point are allowed by `p.* -> ret.M`, but neither
NORMAL branch relates that pair: the read requires f.g and the write adds
f. Normal correlated FLOW coverage cannot remove this independent MAY.
MAY/NE canonicalization can remove cut siblings, but it retains the root
MAY provider. This uses the selected subsumption rules, not an assumption
that no other summaries have been computed.

**No progress measure increases.** The two repeated witness conclusions
have concrete FL=0. Their paired Dp also has FL=0, hence budget 1. They are
already MAY before C5; `fieldCut` leaves them unchanged at every positive
limit. There is no lost known field to certify NE. C2's empty branch does
not replace the non-empty STAR branch, and processing EXACT first does not
cancel it. The f/g read can reset uncertainty to MAY in every run.

Thus the invariant holds by induction for all natural k. Every forward
handoff has outgoing refinement demand, so the specified empty-demand
stopping condition never fires. Each run has a finite CFG and finite field
limit. More explicitly, its field alphabet, bases, marks, owners and ports
are finite; at fixed limit L there are at most
`1 + |Sigma| + ... + |Sigma|^L` concrete chains per base. The finite tail,
support and exclusion headers leave a finite deduplicated membership domain.
Fair worklist completion therefore finishes each run. The infinite behavior
is an unbounded sequence of completed runs.
The temporary run-11 limit is not used anywhere in this argument.

## 5. Checked proof and its scope

[Cycle.lean](../../spec/lean/proposals/non-empty-may-acyclic-cycle-20261113/Cycle.lean)
imports the selected `Policy` and `Restriction` modules. It checks the
complete C2 command families for the witness offers, raw-initial C5,
per-row budgets, ordinary prefix transfers, both call applications, source
overlap, handoff reversal and induction over arbitrarily many F/B rounds.
The second call's offer is computed from the first call, not supplied as an
independent recurring input assumption.

The checked induction is a **witness projection**, not a compiled JVM or
whole-driver simulation. The ordinary-control and final-compaction
embedding is proved above against the selected specification; Lean does not
formalize every JVM instruction, actor queue, alias implementation or all
incidental summaries. In particular, the model does not prove a negative
claim about all side rows by silently resetting the NORMAL store. This is
a specification counterexample, not a claimed execution of a new-tail
production core, which does not yet exist.

The checker audits 21 cycle declarations plus the existing 79 reference
declarations. It rejects custom axioms, `sorryAx` and `Classical.choice`.
Only standard `propext` and `Quot.sound` are permitted. Reproduce with:

```sh
python3 spec/lean/proposals/non-empty-may-acyclic-cycle-20261113/check.py \
    --out /tmp/non-empty-may-acyclic-cycle-check
```

Result: **PASS, 5 modules, 100 audited declarations**. The receipt and Lean
logs are external under `non-empty-may-acyclic-cycle-20261113/proofs-v1/`
in the [report data archive](EXTERNAL_DATA.md).
The current checker also compiles the later BB retrace: 6 modules and
125 declarations in total. The original 100-check receipt is unchanged.

No new project iteration was run. Historical latest reached/completed/
accepted-forward positions remain OWASP **run-11/11/11**, Conductor
**run-8/7/7**, Stirling-PDF **run-11/10/9**. They are not evidence for the
infinite claim; the uncapped induction is.
