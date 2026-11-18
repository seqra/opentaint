# Acyclic non-termination after bounded demand refinement

14 November 2026. Specification counterexample under
[non-empty MAY](../../spec/non-empty-may.md) plus
[bounded demand refinement](../design/bidirectional-bounded-demand-refinement-20261114.md),
including its revision which keeps routing G local and adds no artificial
field exclusions. Follow [proof-guide.md](../../spec/proof-guide.md).
Production is unchanged.

**Scope update:** the user requires an example without a special pass
rule. The [ordinary-code counterexample](bidirectional-bounded-refinement-ordinary-cycle-20261114.md)
meets that narrower request. This earlier intrinsic-MAY example remains
a separate rule-language case, not the answer to the narrowed task.

**Result:** a permitted pass rule with an `AnyField` target produces an
intrinsic MAY. Forward and backward runs regenerate the same
`ZERO -> DemandTarget, DEMAND` forever. No loop, recursion, field cut or
unbounded field path is needed. Increasing the field limit cannot refine
this MAY.

This example uses the preserved library-rule contract. It does not claim
that the earlier ordinary read/write example still fails: that reference
now finishes at **run-5**. It also does not establish non-termination for a
narrower language which forbids `AnyField` pass targets.

## 1. Program and rules

```java
final class Example {
    static native Object sourceT();
    static native Object copyUnknownField(Object p);
    static native void sinkT(Object p);

    static void main() {
        Object x = sourceT();
        Object y = copyUnknownField(x);
        sinkT(y);
    }
}
```

Use these rules only, all with condition `true` except the stated sink
condition. Disable aliases and default getter models for this experiment.
The native declarations have no analyzable bodies. They are modeled by
rules, not predefined method summaries. `main` is the single analyzable
method/block; it has one straight-line basic block.

```text
S, sourceT:
    AssignMark(T, Result)                       // exact target

P, copyUnknownField:
    CopyMark(T, Argument(0), Result.AnyField)    // allowed pass TARGET

K, sinkT:
    ContainsMark(Argument(0), T)                 // exact-root check
```

The pass rule's input is exact, not `AnyField`. Therefore it does not use
the forbidden `AnyField` pass-input shape.

These are existing semantics, explicitly retained by the combined proposal:

```text
source target:        ZERO -> x.$/T, NORMAL
pass micro-edge:      p.$/T -> result.MAY/T, DEMAND
reverse pass result:  exact p.$/T, still DEMAND
MAY/T at y:           can satisfy an exact y.$/T check, on DEMAND
reverse source:       matching x.$/T reaches the real source;
                      its ZERO result becomes DemandTarget
```

The pass-target and reverse-layer rules are stated in
[interpreter.md, I14 and pass rules](../../spec/interpreter.md) and
[ap.md, W6/W8](../../spec/ap.md). A source with an `AnyField` target would
instead emit MUST; **that is not the rule here**. A pass target emits MAY,
which contains both the empty and nonempty suffixes.

The unresolved default identity can retain `x.$/T`; it cannot produce a
marked `y`. No other rule writes y. Thus there is no independent NORMAL
route to the sink which the trace omits.

## 2. Trace notation and controls

```text
Z = ZERO; DT = anonymous DemandTarget
$ = EXACT; M = MAY; N = NORMAL; D = DEMAND
all fields E/mx are empty; H=false

X := Z -> DT,D
C := Z -> Z,N                         // ordinary completion

Handoff(X): entry selector Dc=Target; paired exit selector Dp=Z
Write this complete demand row as [Target ; Z].
```

The next run receives **ZERO**, not Target. Target is its admission selector.
The existing control rules admit ZERO against Target, and permit a Target
conclusion against Dp=ZERO. Hence paired C5 accepts X in both directions.
No blanket Target restriction bypass or new ZERO seed is introduced.

All following annotations list the complete relevant block summaries:
C and X. Locals x and y do not escape this void root method. The native
calls introduce no additional analyzable block. The default identity of x
does not change any annotation at y or the terminal summary.

### Run-1: forward, limit 1

```java
// Previous demand: none; unrestricted run-1.
// Submitted: Z,N.
// Emitted initial: Z -> Z,N. No DATA initial.
static void main() {
    Object x = sourceT();             // Z -> x.$/T,N
    Object y = copyUnknownField(x);   // Z -> y.M/T,D; intrinsic pass target
    sinkT(y);                        // Exact check has a D witness: Z -> DT,D
}
// Published NORMAL: C = Z -> Z,N.
// Published DEMAND: X = Z -> DT,D.
// Next demand: [Target ; Z].
```

The base handoff is derived from a real source and pass application. It is
not supplied as a recurring hypothetical input.

### Run-2: backward, limit 1

For every backward run, published summaries are above the declaration;
demand, submitted facts and emitted initials are below it. The code remains
in source order; the comments describe its reverse processing order.

```java
// Published NORMAL: C = Z -> Z,N.
// Published DEMAND: X = Z -> DT,D.
static void main() {
    Object x = sourceT();             // x.$/T,D matches source S.
                                      // Reverse source's ZERO becomes DT,D.
    Object y = copyUnknownField(x);   // Reverse pass: y.$/T,D -> x.$/T,D
    sinkT(y);                        // Target-guided reverse seed: y.$/T,D
}
// Previous demand edge: X = Z -> DT,D; row [Target ; Z].
// Submitted: Z,N at the backward boundary.
// Emitted initial: Z -> Z,N. No DATA initial.
// Source permission produced: {S}.
// Next demand: [Target ; Z].
```

The `$` reverse result stays D because it comes through an `AnyField` pass
target. An exact tail alone does not make an edge NORMAL. The exact source
match is real and renews S; there is no carried or invented source permission.

### Run-3: forward, limit 2

```java
// Previous demand: X = Z -> DT,D; row [Target ; Z].
// Submitted: Z,N. Source permission: {S}, from run-2.
// Emitted initial: Z -> Z,N. No DATA initial.
static void main() {
    Object x = sourceT();             // Z -> x.$/T,N; permitted source
    Object y = copyUnknownField(x);   // Z -> y.M/T,D; same pass target
    sinkT(y);                        // Z -> DT,D; no NORMAL witness
}
// Published NORMAL: C = Z -> Z,N.
// Published DEMAND: X = Z -> DT,D.
// Next demand: [Target ; Z].
```

### Run-4: backward, limit 3

```java
// Published NORMAL: C = Z -> Z,N.
// Published DEMAND: X = Z -> DT,D.
static void main() {
    Object x = sourceT();             // x.$/T,D -> source hit S -> DT,D
    Object y = copyUnknownField(x);   // y.$/T,D -> x.$/T,D
    sinkT(y);                        // Reverse seed y.$/T,D
}
// Previous demand: X = Z -> DT,D; row [Target ; Z].
// Submitted: Z,N.
// Emitted initial: Z -> Z,N. No DATA initial.
// Source permission produced: {S}.
// Next demand: [Target ; Z].
```

### Run-5: forward, limit 4

```java
// Previous demand: X = Z -> DT,D; row [Target ; Z].
// Submitted: Z,N. Source permission: {S}, from run-4.
// Emitted initial: Z -> Z,N. No DATA initial.
static void main() {
    Object x = sourceT();             // Z -> x.$/T,N
    Object y = copyUnknownField(x);   // Z -> y.M/T,D
    sinkT(y);                        // Z -> DT,D
}
// Published NORMAL: C = Z -> Z,N.
// Published DEMAND: X = Z -> DT,D.
// Next demand: [Target ; Z].
```

### Run-6: backward, limit 5

```java
// Published NORMAL: C = Z -> Z,N.
// Published DEMAND: X = Z -> DT,D.
static void main() {
    Object x = sourceT();             // x.$/T,D -> source hit S -> DT,D
    Object y = copyUnknownField(x);   // y.$/T,D -> x.$/T,D
    sinkT(y);                        // Reverse seed y.$/T,D
}
// Previous demand: X = Z -> DT,D; row [Target ; Z].
// Submitted: Z,N.
// Emitted initial: Z -> Z,N. No DATA initial.
// Source permission produced: {S}.
// Next demand: [Target ; Z].
```

### Every later iteration

The following are parameterized per-iteration traces, not an extrapolation
from the first six runs. Let k be any natural number with k>=3.

```java
// Run-(2k+1), FORWARD, limit 2k.
// Previous demand: X = Z -> DT,D; row [Target ; Z].
// Submitted: Z,N. Source permission: {S}, produced by run-(2k).
// Emitted initial: Z -> Z,N. No DATA initial.
static void main() {
    Object x = sourceT();             // Z -> x.$/T,N
    Object y = copyUnknownField(x);   // Z -> y.M/T,D
    sinkT(y);                        // Z -> DT,D
}
// Published NORMAL: C = Z -> Z,N.
// Published DEMAND: X = Z -> DT,D.
// Next demand: [Target ; Z].
```

```java
// Run-(2k+2), BACKWARD, limit 2k+1.
// Published NORMAL: C = Z -> Z,N.
// Published DEMAND: X = Z -> DT,D.
static void main() {
    Object x = sourceT();             // x.$/T,D -> source hit S -> DT,D
    Object y = copyUnknownField(x);   // y.$/T,D -> x.$/T,D
    sinkT(y);                        // Reverse seed y.$/T,D
}
// Previous demand: X = Z -> DT,D; row [Target ; Z].
// Submitted: Z,N.
// Emitted initial: Z -> Z,N. No DATA initial.
// Source permission produced: {S}.
// Next demand: [Target ; Z].
```

## 3. Proof of non-termination

Let H_r be the demand set after the complete handoff of run-r. Let B and
F be complete backward and restricted-forward transitions for this root.
Let permission S mean a real reverse match of the source action above.

```text
H_1 = {X}
B({X})      = ({X}, {S})
F({X}, {S}) = {X}

Therefore, for every r>=1: H_r = {X} != empty.
```

**Base.** Run-1 emits exact normal T at x. The pass target is MAY/D, so the
exact y sink triggers on D and publishes X. C is NORMAL and contributes
no next-run demand.

**Backward step.** X supplies the qualified row `[Target ; Z]`, which
admits the existing backward ZERO. The sink supplies `y.$/T,D`. It overlaps
the pass rule's MAY target; the reversed pass produces `x.$/T,D`. This
matches S exactly, renews its permission, and converts the reverse ZERO
result to DemandTarget. The paired control intersection accepts X.

**Forward step.** The same row admits ZERO, and the renewed permission
allows S. Its output is exact and NORMAL. Applying P recreates `y.M/T,D`.
The sink and paired C5 recreate X. This derivation uses neither an old
DEMAND summary nor a saved failed input.

**Induction.** The base and both transitions give the displayed invariant
for every run. In particular X repeats at run-i and run-(i+2) for every
i>=3, including run-5 and all later removal points. It makes no progress.

**Why the new proposal cannot break the cycle:**

| Mechanism | Effect here |
| --- | --- |
| NE at a real cut | No concrete field is ever cut. All concrete path lengths are zero. The pass-generated MAY must remain MAY. |
| Preserve deeper post-C5 demand heads | There is no deeper DATA head; the only demand is typed Target control X. |
| One-field query planning | No DATA initial is needed in this root. There is no observed next field or child query. |
| Local routing G | No coarse unknown-field read is performed. An intrinsic pass target is not such a read and is unchanged. |
| Possible STAR bindings | No STAR offer or method/block DATA call exists. |
| NORMAL precoverage before C5 | The result requiring retirement is a DEMAND Target. It is expressly outside NORMAL FLOW precoverage. |
| Existing subsumption | C has a ZERO conclusion, not Target. No NORMAL Target, other demand provider, ND alternative or weaker terminal relation can remove X. |
| EXACT-first scheduling | The source is already exact and processed first. The pass still produces MAY/D. |
| Increasing global/relative field budgets | There is no field suffix to retain and no DATA summary to lengthen. |

No NORMAL marked result at y can appear in a later run: S writes x; the
default identity preserves x; P is the sole marked producer at y, and all
its outputs are D. Pass rules preserve H and do not create protection.
Therefore there is never a missing NORMAL sink witness which could turn
this trace into a completed normal report.

**Each run finishes.** It has a fixed, finite straight-line graph, three
call sites, one mark and a constant fact set. The model has exactly two
block summaries C and X on every run. Fair deduplicated execution has no
within-run infinite derivation. Non-termination is an infinite sequence
of completed runs, not an infinite worklist inside one run.

The specified stop rule requires empty outgoing demand. Since H_r is
nonempty for every r, it never fires. The proof has no run-11 limit and
does not use findings exposed by a cutoff.

## 4. Checked proof and limits

The [Lean package](../../spec/lean/proposals/bounded-refinement-acyclic-cycle-20261114/README.md)
imports the current no-artificial-E proposal reference. `IntrinsicMay.lean`
constructs the source, forward/reverse pass, exact sink, source permission,
typed controls, paired restriction, handoff and run transitions. Its
induction proves the same nonempty demand set for every natural round.
The next source permission is computed from the preceding backward run;
it is not an induction assumption independent of that run.

The new component is a complete scalar action/control model for this
synthetic program. DATA C2 is unused, not replaced by a different table.
The control adapter follows the selected Target/ZERO rules. This is not
a production Kotlin/JVM correspondence proof or a measured new-tail scan.
The unchanged pass contract and absence of a rule that can retire X embed
the component in the combined specification as explained above.

Reproduce with:

```sh
python3 spec/lean/proposals/bounded-refinement-acyclic-cycle-20261114/check.py \
  --out /tmp/bounded-refinement-acyclic-cycle-proof
```

The checker rejects proof holes, custom axioms and classical dependencies.
It records source hashes and Lean logs outside the repository. No new
core behavior or extra evidence store is introduced to produce the example.
Result: **PASS, 13 modules, 220 audited declarations**; 21 claims are new
and 199 come from the imported selected/proposal references. The external
receipt is linked in the package README.

The remaining issue is **intrinsic uncertainty with no available refinement
step**. The bounded proposal solves its supplied field-transfer cases; it
does not yet provide a retirement proof or a different completion rule for
this stationary control cycle. Repeating X is not itself a sound reason
to drop arbitrary Target demand. Whether to add a proved retirement rule,
change this library model, or define an explicit unresolved completion
contract is a separate semantic decision.

No project scan was run. Historical reached/completed/accepted-forward
positions remain OWASP **run-11/11/11**, Conductor **run-8/7/7**, and
Stirling-PDF **run-11/10/9**. This reference has no latest finite run:
the induction covers all runs, including and beyond **run-11**.
