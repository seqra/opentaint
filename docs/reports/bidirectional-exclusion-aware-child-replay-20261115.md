# Exclusion-aware child replay: termination of the supplied references

17 November follow-up: [the ordinary-prefix audit](bidirectional-prefix-return-soundness-gap-20261117.md)
confirms case 165's broad-observation loss at natural run-5 and reduces it
to one straight-line call. Case 884 now passes the updated reference and
both native observation controls at run-5. The original receipts below
remain historical; their alignment-only status is superseded.


15 November 2026. Synthetic data-flow reachability. Follow
[proof-guide.md](../../spec/proof-guide.md).

The [approach](../design/bidirectional-exclusion-aware-child-replay-20261115.md)
reuses existing prepared child cases even when a matched NORMAL record or
its operand has real field exclusions. Native matching and all real E stay
unchanged. No query, callee offer, partition or full evidence composition
is added. Production is unchanged.

## Result and scope

All twelve complete cold references naturally terminate and retain their
expected NORMAL observations. The new pre/post-overwrite example stops at
**run-9**. The required references finish at **run-3 through run-15**;
the broader structured diagnostics reach **run-19**. There is no hard limit
in a natural-stop certificate. No project scan was run. Native validation
is component-only and does not establish a completed analyzer iteration.

| Reference | Naturally completed run | Observation |
|---|---:|---|

| Nested | run-9 | retained |
| Prefix | run-9 | none (negative control) |
| PrefixPostfix | run-11 | retained |
| Postfix | run-13 | retained |
| RoundTrip | run-9 | retained |
| Double | run-15 | retained |
| OldMethod | run-5 | retained |
| OldBB | run-5 | retained |
| LongReader | run-5 | retained |
| OrdinaryTwo | run-3 | retained |
| Growth | run-11 | retained |
| Overwrite | run-9 | retained |

Earlier cleaner/protected and uniform-root cases remain checked dependency
proofs, with the selected cleaner meaning. They are not replaced by a plain
FLOW subsumption law. The new concrete/protected/MUST fallback theorems
keep their existing replay path.

The strongest complete-state workload regression is `Growth`: new and old
states are equal at every run-1 through run-11, including originals, offers,
current summaries and handoff. Counts alone are not its certificate.

## Principal code

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
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce(); // configured T at x.f.g and descendants
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);        // configured CM(w.[any],T)
}
```

The ordinary producer body and compilable code are in the
[counterexample fixture](../../spec/lean/proposals/overwrite-saved-replay-cycle-20261115/OverwriteReplay.java).
There is no loop, recursion, cleaner, special pass rule, static or unresolved
MAY model. The two rules execute at the call sites in entry.

Derived saved records are Wg `x.* -> ret.f.f.* {g},N` and Rg
`x.f.f.* -> ret.* {g},N`. Wg is learned forward and Rg backward.
Previously real E alone disabled prepared-child routing. The root and child
MAY replies survived together, recreating the same paired root bound.
Now only the child owns the covered reader contribution. Its deeper premise
advances the ordinary next paired output limit. The code and NORMAL records
are unchanged.

`M=[any]`, `NE=[non-empty-may]`, `U=[any-taint]`; N/D are NORMAL/DEMAND.
`{g}` is a real suffix-scope field exclusion. All unshown E, mx and protection
flags are empty/false. A demand is its entry selector -> paired exit selector
in the current direction. Raw initials below are identity edges, all FLOW/N.
Forward demand, submitted facts and initials precede the declaration;
forward summaries follow it. Backward annotations use the reverse placement.

## Complete new trace of the overwrite case

| Run | Direction | Field limit | wrapper outgoing DATA demand | choose outgoing DATA demand | final marked DEMAND witnesses |
|---:|---|---:|---:|---:|---:|

| 1 | forward | 1 | 1 | 2 | 1 |
| 2 | backward | 1 | 2 | 3 | 1 |
| 3 | forward | 2 | 4 | 6 | 1 |
| 4 | backward | 3 | 7 | 4 | 1 |
| 5 | forward | 4 | 10 | 0 | 1 |
| 6 | backward | 5 | 4 | 0 | 1 |
| 7 | forward | 6 | 1 | 0 | 1 |
| 8 | backward | 7 | 0 | 0 | 1 |
| 9 | forward | 8 | 0 | 0 | 0 |

### Run-1: forward, limit 1

```java
// Demand:
//   {}
// Submitted:
//   x.M/T,D
//   x.f.NE/T,D
// Emitted raw initials:
//   x.*/FLOW -> x.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
```

```java
// Demand:
//   {}
// Submitted:
//   x.*/T,N
// Emitted raw initials:
//   x.*/FLOW -> x.*/FLOW,N
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
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
//   x.*/FLOW -> ret.f.NE/FLOW,D
```

```text
// Actual call packets, in traversal order:
//   x: x.f.NE/T,D
//   y: y.M/T,D
//   z: z.M/T,D
//   w: w.M/T,D
```

The remaining DEMAND witness supplies ZERO -> DemandTarget,D at the
observation. A NORMAL observation does not cancel that demand.


### Run-2: backward, limit 1

```java
// Published summaries:
//   ret.*/FLOW -> x.M/FLOW,D
//   ret.*/FLOW -> x.f.NE/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand:
//   ret.M/FLOW -> x.*/FLOW
// Submitted:
//   ret.M/T,D
// Emitted raw initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.f.NE/FLOW,D
//   ret.f.*/FLOW -> x.M/FLOW,D
//   ret.f.*/FLOW -> x.f.NE/FLOW,D
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
// Demand:
//   ret.M/FLOW -> x.*/FLOW
//   ret.f.NE/FLOW -> x.*/FLOW
// Submitted:
//   ret.$/T,N
//   ret.*/T,N
// Emitted raw initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
```

```text
// Actual call packets, in traversal order:
//   w: w.M/T,D
//   z: z.M/T,D
//   y: y.M/T,D
//   x: x.M/T,D
```

The final need reaches the configured producer at x.f.g. Its GEN supplies
the root ZERO -> DemandTarget,D and keeps ZERO admitted next run.


### Run-3: forward, limit 2

```java
// Demand:
//   x.M/FLOW -> ret.*/FLOW
//   x.f.NE/FLOW -> ret.*/FLOW
// Submitted:
//   x.M/T,D
//   x.f.g.U/T,N
// Emitted raw initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
//   x.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.*/FLOW -> ret.M/FLOW,D
//   x.f.g.*/FLOW -> ret.M/FLOW,D
```

```java
// Demand:
//   x.M/FLOW -> ret.f.*/FLOW
//   x.f.NE/FLOW -> ret.*/FLOW
//   x.f.NE/FLOW -> ret.f.*/FLOW
// Submitted:
//   x.$/T,N
//   x.*/T,N
//   x.f.$/T,N
//   x.f.*/T,N
//   x.f.g.*/T,N
// Emitted raw initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
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
// Published summaries:
//   x.*/FLOW -> ret.f.f.*/FLOW {g},N
//   x.f.*/FLOW -> ret.M/FLOW,D
//   x.f.*/FLOW -> ret.f.M/FLOW,D
//   x.f.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.*/FLOW -> ret.f.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.f.NE/FLOW,D
```

```text
// Actual call packets, in traversal order:
//   x: x.f.g.U/T,N
//   y: y.M/T,D
//   z: z.M/T,D
//   w: w.M/T,D
```

The remaining DEMAND witness supplies ZERO -> DemandTarget,D at the
observation. A NORMAL observation does not cancel that demand.


### Run-4: backward, limit 3

```java
// Published summaries:
//   ret.*/FLOW -> x.M/FLOW,D
//   ret.*/FLOW -> x.f.M/FLOW,D
//   ret.*/FLOW -> x.f.NE/FLOW,D
//   ret.*/FLOW -> x.f.g.M/FLOW,D
//   ret.*/FLOW -> x.f.f.*/FLOW {g},N
//   ret.f.*/FLOW -> x.M/FLOW,D
//   ret.f.*/FLOW -> x.f.M/FLOW,D
//   ret.f.*/FLOW -> x.f.NE/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand:
//   ret.M/FLOW -> x.*/FLOW
//   ret.M/FLOW -> x.f.*/FLOW
//   ret.M/FLOW -> x.f.g.*/FLOW
//   ret.f.NE/FLOW -> x.*/FLOW
// Submitted:
//   ret.M/T,D
// Emitted raw initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.f.f.*/FLOW {g},N
//   ret.f.*/FLOW -> x.f.M/FLOW,D
//   ret.f.*/FLOW -> x.f.g.M/FLOW,D
//   ret.f.*/FLOW -> x.f.f.NE/FLOW,D
//   ret.f.f.*/FLOW -> x.f.f.NE/FLOW,D
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
// Demand:
//   ret.M/FLOW -> x.f.*/FLOW
//   ret.f.M/FLOW -> x.f.*/FLOW
//   ret.f.NE/FLOW -> x.f.*/FLOW
//   ret.f.NE/FLOW -> x.f.g.*/FLOW
//   ret.f.f.NE/FLOW -> x.f.*/FLOW
//   ret.f.f.NE/FLOW -> x.f.g.*/FLOW
// Submitted:
//   ret.$/T,N
//   ret.*/T,N
//   ret.f.$/T,N
//   ret.f.*/T,N
// Emitted raw initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
//   ret.f.f.$/FLOW -> ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW -> ret.f.f.*/FLOW,N
```

```text
// Actual call packets, in traversal order:
//   w: w.M/T,D
//   z: z.M/T,D
//   y: y.M/T,D
//   x: x.M/T,D
```

The final need reaches the configured producer at x.f.g. Its GEN supplies
the root ZERO -> DemandTarget,D and keeps ZERO admitted next run.


### Run-5: forward, limit 4

```java
// Demand:
//   x.M/FLOW -> ret.*/FLOW
//   x.M/FLOW -> ret.f.*/FLOW
//   x.f.M/FLOW -> ret.*/FLOW
//   x.f.M/FLOW -> ret.f.*/FLOW
//   x.f.NE/FLOW -> ret.*/FLOW
//   x.f.NE/FLOW -> ret.f.*/FLOW
//   x.f.g.M/FLOW -> ret.*/FLOW
// Submitted:
//   x.M/T,D
//   x.f.g.U/T,N
//   x.f.f.f.g.U/T,N
// Emitted raw initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.$/FLOW -> x.f.g.$/FLOW,N
//   x.f.g.U/FLOW -> x.f.g.U/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
//   x.f.f.$/FLOW -> x.f.f.$/FLOW,N
//   x.f.f.*/FLOW -> x.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.f.NE/FLOW,D
//   x.*/FLOW -> ret.f.f.*/FLOW {g},N
//   x.f.*/FLOW -> ret.M/FLOW,D
//   x.f.*/FLOW -> ret.f.M/FLOW,D
//   x.f.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.*/FLOW -> ret.f.f.NE/FLOW,D
//   x.f.g.U/FLOW -> ret.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.f.NE/FLOW,D
//   x.f.f.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.f.*/FLOW -> ret.f.f.NE/FLOW,D
```

```java
// Demand:
//   x.f.M/FLOW -> ret.f.*/FLOW
//   x.f.g.M/FLOW -> ret.f.*/FLOW
//   x.f.f.NE/FLOW -> ret.f.*/FLOW
//   x.f.f.NE/FLOW -> ret.f.f.*/FLOW
// Submitted:
//   x.$/T,N
//   x.*/T,N
//   x.f.$/T,N
//   x.f.*/T,N
//   x.f.g.$/T,N
//   x.f.g.U/T,N
//   x.f.g.*/T,N
//   x.f.f.$/T,N
//   x.f.f.*/T,N
// Emitted raw initials:
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.$/FLOW -> x.f.g.$/FLOW,N
//   x.f.g.U/FLOW -> x.f.g.U/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
//   x.f.f.$/FLOW -> x.f.f.$/FLOW,N
//   x.f.f.*/FLOW -> x.f.f.*/FLOW,N
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
// Published summaries:
//   {}
```

```text
// Actual call packets, in traversal order:
//   x: x.f.g.U/T,N
//   y: y.M/T,D; y.f.f.f.g.U/T,N
//   z: z.M/T,D; z.f.g.U/T,N
//   w: w.M/T,D; w.f.f.f.g.U/T,N
```

The remaining DEMAND witness supplies ZERO -> DemandTarget,D at the
observation. A NORMAL observation does not cancel that demand.


### Run-6: backward, limit 5

```java
// Published summaries:
//   ret.f.*/FLOW -> x.M/FLOW,D
//   ret.f.*/FLOW -> x.f.M/FLOW,D
//   ret.f.*/FLOW -> x.f.g.M/FLOW,D
//   ret.f.*/FLOW -> x.f.f.M/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand:
//   ret.M/FLOW -> x.f.*/FLOW
//   ret.f.M/FLOW -> x.f.*/FLOW
//   ret.f.NE/FLOW -> x.*/FLOW
//   ret.f.NE/FLOW -> x.f.*/FLOW
//   ret.f.NE/FLOW -> x.f.g.U/FLOW
//   ret.f.NE/FLOW -> x.f.g.*/FLOW
//   ret.f.NE/FLOW -> x.f.f.*/FLOW
//   ret.f.f.NE/FLOW -> x.f.*/FLOW
//   ret.f.f.NE/FLOW -> x.f.g.*/FLOW
//   ret.f.f.NE/FLOW -> x.f.f.*/FLOW
// Submitted:
//   ret.M/T,D
// Emitted raw initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
//   ret.f.f.$/FLOW -> ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW -> ret.f.f.*/FLOW,N
```

```java
// Published summaries:
//   {}
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
// Demand:
//   {}
// Submitted:
//   ret.$/T,N
//   ret.*/T,N
//   ret.f.$/T,N
//   ret.f.*/T,N
//   ret.f.f.$/T,N
//   ret.f.f.*/T,N
// Emitted raw initials:
//   {}
```

```text
// Actual call packets, in traversal order:
//   w: w.M/T,D
//   z: z.M/T,D
//   y: y.M/T,D
//   x: x.M/T,D
```

The final need reaches the configured producer at x.f.g. Its GEN supplies
the root ZERO -> DemandTarget,D and keeps ZERO admitted next run.


### Run-7: forward, limit 6

```java
// Demand:
//   x.M/FLOW -> ret.f.*/FLOW
//   x.f.M/FLOW -> ret.f.*/FLOW
//   x.f.g.M/FLOW -> ret.f.*/FLOW
//   x.f.f.M/FLOW -> ret.f.*/FLOW
// Submitted:
//   x.M/T,D
//   x.f.M/T,D
//   x.f.g.U/T,N
//   x.f.f.f.g.U/T,N
//   x.f.f.f.f.f.g.U/T,N
// Emitted raw initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.$/FLOW -> x.f.g.$/FLOW,N
//   x.f.g.U/FLOW -> x.f.g.U/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
//   x.f.f.$/FLOW -> x.f.f.$/FLOW,N
//   x.f.f.*/FLOW -> x.f.f.*/FLOW,N
//   x.f.f.f.*/FLOW -> x.f.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.f.*/FLOW -> ret.f.M/FLOW,D
```

```java
// Demand:
//   {}
// Submitted:
//   x.$/T,N
//   x.*/T,N
//   x.f.$/T,N
//   x.f.*/T,N
//   x.f.g.$/T,N
//   x.f.g.U/T,N
//   x.f.g.*/T,N
//   x.f.f.$/T,N
//   x.f.f.*/T,N
//   x.f.f.f.*/T,N
// Emitted raw initials:
//   {}
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
// Published summaries:
//   {}
```

```text
// Actual call packets, in traversal order:
//   x: x.f.g.U/T,N
//   y: y.f.M/T,D; y.f.f.f.g.U/T,N
//   z: z.M/T,D; z.f.g.U/T,N; z.f.f.f.f.f.g.U/T,N
//   w: w.M/T,D; w.f.f.f.g.U/T,N
```

The remaining DEMAND witness supplies ZERO -> DemandTarget,D at the
observation. A NORMAL observation does not cancel that demand.


### Run-8: backward, limit 7

```java
// Published summaries:
//   {}
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand:
//   ret.f.M/FLOW -> x.f.*/FLOW
// Submitted:
//   ret.M/T,D
// Emitted raw initials:
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
//   ret.f.f.$/FLOW -> ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW -> ret.f.f.*/FLOW,N
```

```java
// Published summaries:
//   {}
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
// Demand:
//   {}
// Submitted:
//   ret.f.$/T,N
//   ret.f.*/T,N
//   ret.f.f.$/T,N
//   ret.f.f.*/T,N
// Emitted raw initials:
//   {}
```

```text
// Actual call packets, in traversal order:
//   w: w.M/T,D
//   z: z.M/T,D
//   y: y.M/T,D
//   x: x.M/T,D
```

The final need reaches the configured producer at x.f.g. Its GEN supplies
the root ZERO -> DemandTarget,D and keeps ZERO admitted next run.


### Run-9: forward, limit 8

```java
// Demand:
//   {}
// Submitted:
//   x.f.g.U/T,N
//   x.f.f.f.g.U/T,N
//   x.f.f.f.f.f.g.U/T,N
// Emitted raw initials:
//   {}
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   {}
```

```java
// Demand:
//   {}
// Submitted:
//   {}
// Emitted raw initials:
//   {}
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
// Published summaries:
//   {}
```

```text
// Actual call packets, in traversal order:
//   x: x.f.g.U/T,N
//   y: y.f.f.f.g.U/T,N
//   z: z.f.g.U/T,N; z.f.f.f.f.f.g.U/T,N
//   w: w.f.f.f.g.U/T,N; w.f.f.f.f.f.f.f.g.U/T,N
```

All actual final witnesses are NORMAL. There is no fresh DemandTarget.
Both method DATA frontiers are empty, so the complete continuation frontier
is empty. The NORMAL observation is retained. This is natural completion.

## Workload

For fixed plans, a new reply is either omitted or exactly the old reply.
The same inequality holds after any fixed native C5/postprocessing function.
The proof does not add a body restart, a caller input or a stronger origin.

For the overwrite case, these sums cover equal prefixes, run-1 through run-9:

| Membership sum | Previous routing | New routing |
|---|---:|---:|

| queries | 73 | 64 |
| summaries | 34 | 28 |
| calleeInputs | 50 | 41 |
| outerFacts | 39 | 36 |

The main saving is that the new complete execution ends at run-9. The old
counterexample's nonempty frontier repeats without any hard limit, as proved
in its separate package. The finite run-61 baseline is not the proof of that
statement.

Removing a coarse MAY can expose narrower memberships. Consequently the
fixed-plan inequality is not a whole-run cardinality bound. The diagnostics
measure this risk; they do not establish a native performance bound.

## Additional diagnostics

```json
{
  "count": 400,
  "horizon": 41,
  "latestReached": 15,
  "oldIncomplete": 0,
  "newIncomplete": 0,
  "newFindingRegressions": 0,
  "bothModelMismatches": 1,
  "maxRatios": {
    "queries": 1.0,
    "summaries": 1.0416666666666667,
    "calleeInputs": 1.0,
    "outerFacts": 1.0
  }
}
```

```json
{
  "count": 116,
  "horizon": 41,
  "latestReached": 19,
  "oldIncomplete": 5,
  "newIncomplete": 0,
  "newRegressions": 0
}
```

The random E-heavy screen uses 400 acyclic programs. It compares equal run
prefixes. The largest summary-membership ratio is 1.042; query, callee-input
and outer-fact sums do not increase in this screen. All new-mode cases finish;
the latest completed run is run-15.

The 116 structured variants vary read/write depth, overwrite placement,
concrete/uniform submitted source shape and number of calls. Five old-mode
executions remain unfinished at the diagnostic run-41 horizon; all new-mode
executions finish, at most run-19. Those five finite survivors are not five
additional non-termination proofs. No new finding regression is observed.

The diagnostic C2 adapter supplies the existing incoming-E rejection and
MUST own-E handling missing from the older empty-E Python table. This is
reference alignment; it is not a proposed change to native initial emission.

The independent untruncated diagnostic uses exact or uniform regions and
ordinary prefix reads/writes plus strong replacement with fresh unmarked
objects. It is used only as a comparison oracle, not as a runtime evidence
store or a proposed extra analysis.

### Existing reference-alignment gap

Random case 165 has a concrete reachable marked output, but both old and
new references finish at run-4 without it. Both have the same counts:
8 query memberships, 6 executable summaries, 5 callee inputs and 6 outer
facts. This is not fixed or introduced by the new routing. Its relevant
ordinary shape is:

```java
Node wrapper(Node x) {
    Node a = x.g.g;
    Node b = choose(a);
    Node c = new Node(); c.g = b;
    Node y = new Node(); y.g = c;
    return y;
}
Node choose(Node x) {
    if (branch) {
        Node y = new Node(); y.f = x.f;
        y.g = new Node();
        return y;
    }
    x.g = new Node();
    Node t = x.f.g.f;
    Node a = new Node(); a.f = t;
    Node y = new Node(); y.f = a;
    y.f = new Node();
    return y;
}
// T initially at x.g and below; two wrapper calls; observe below the result.
```

The first branch gives the concrete path sequence
`g.U -> U -> f.U -> g.g.f.U`, and the second wrapper retains `g.g.f.U`.
The screen does not prove native behavior for this case. It remains a
baseline admission/reference-alignment issue requiring separate investigation.
Do not use this screen or the local cover identity to claim universal
finding preservation. The supplied required cold examples and earlier
selected cleaner/protection results are checked separately.

## Proof and native validation

The [proof package](../../spec/lean/proposals/exclusion-child-replay-20261115/README.md)
contains:

- Constructive arbitrary-E child coverage at the original exclusion scopes.
- The same qualified paired output service and real truncation coverage.
- Every kept reply equals the old native reply; no extra fixed-plan work.
- Unchanged unsupported concrete, protected, MUST and other guarded services.
- Complete cold states, quiescence, handoff, actual producer permissions and
  final DATA plus Target emptiness for all twelve references.
- Complete Growth state equality under old and extended routing at each run.

Seven native component tests pass: the four original overwrite tests plus
three exclusion-scope tests. They cover an excluded first field, multiple
parent exclusions without rebasing them to a child, and both the premise
and result exclusions on a saved record. They do not implement the proposed
native adapter.

The full checker rebuilds previous proof packages, then checks the new
models and every new declaration's axiom dependencies. Only `propext` and
`Quot.sound` are allowed. No custom axiom, classical choice, admitted proof
or native proof shortcut is accepted. No hard iteration limit is used to
justify stopping. Bulk JSON, compiled proofs and native logs stay outside
the repo under external `docs/reports/data/exclusion-child-replay-20261115/`.
Production remains unchanged.

Full fresh proof rebuild passed: **399 new theorems, 1,397 audited declarations,
79 modules**. Seven native component tests passed.

