# Code-only trace for an uncovered exact FLOW replay

Date: 29 October 2026. Source reviewed: `f99ed7c1a`.
Latest modeled iteration: **run-3**, forward, field limit 2.
Field limits are `1,1,2`. Marks use FULL mode.
Production code is unchanged.

This note replaces the earlier `opaqueMay` and `makePair` pass models.
Every data transfer below comes from Java code. The only configured rules
are one source rule and two sink rules. No method has a predefined summary.
The summaries in the trace are inferred from the method bodies.

This checks the proposed abstract EXACT extension with the current
target-EXACT application cell left unchanged. Current production rejects
that new typed shape. This is a design counterexample, not a JVM failure
observed on a project.

## 1. Code and rules

```java
final class ExactReplayExample {
    static final class Root { Inner f; }
    static final class Inner { Leaf h; }
    static final class Leaf { }
    static final class Box { Root value; }
    static final class Pair { Inner a; Box b; }

    static void source(Root q) { }
    static void sinkExact(Object x) { }
    static void sinkAny(Object x) { }

    static Inner helper(Root p) {
        return p.f;
    }

    static Box box(Root p) {
        Box z = new Box();
        z.value = p;
        return z;
    }

    static Pair wrapper(Root q) {
        Pair r = new Pair();
        Inner a = helper(q);
        r.a = a;
        Box b = box(q);
        r.b = b;
        return r;
    }

    public static void main(String[] ignored) {
        Root q = new Root();
        q.f = new Inner();
        q.f.h = new Leaf();
        source(q);
        sinkAny(q.f.h);           // Keep the source selected for run-3.
        Pair r = wrapper(q);
        sinkExact(r.a);
        sinkAny(r.b);
    }
}
```

Use these rules. This is rule notation, not another method implementation:

```text
source(Root):
    condition: true
    action: AssignMark(T, arg0.f.h.[any])

sinkExact(Object):
    condition: ContainsMark(arg0.$, T)
    end actions: none

sinkAny(Object):
    condition: ContainsMark(arg0.[any], T)
    end actions: none
```

A terminal `[any]` in the source position gives a MUST result
`arg0.f.h.[any-taint]/T`. It does not mark the parent object at `arg0.f`.
The source rule is unconditional. Its GEN premise is ZERO. The rule compiler
supports a field path followed by AnyField directly; no field-copy model or
alias back-projection is required to place this source at `q.f.h`.

All constructors have their ordinary bodies. Allocations and initialization
before `source(q)` introduce no T. There are no cleaners, conditional
sources, ND rules, statics, or custom pass rules. All propagated fact field
exclusions and mark exclusions in the displayed routes are empty. Ordinary
write-preservation micro-edges still have their field exclusions.

## 2. Instruction micro-edges and derived edge layers

N means NORMAL. D means DEMAND. `*` means STAR, `$` means EXACT, `[any]`
means MAY, and `[any-taint]` means MUST. FLOW is the abstract mark.
A displayed `A -> B, D` is an edge under analysis. It is not a DEMAND
instruction micro-edge.

Each ordinary value-transfer micro-edge below has STAR endpoints. The
instruction itself is NORMAL. An applied result can become DEMAND because
of an ancestor read, an existing DEMAND input, or a field-limit cut.

| Code | NORMAL value-transfer micro-edge |
|---|---|
| `return p.f` | `p.f.* / FLOW -> helperRet.* / FLOW` |
| `z.value = p` | `p.* / FLOW -> z.value.* / FLOW` |
| `return z` | `z.* / FLOW -> boxRet.* / FLOW` |
| `a = helper(q)` | Bind whole q to p; bind helperRet to a |
| `b = box(q)` | Bind whole q to p; bind boxRet to b |
| `r.a = a` | `a.* / FLOW -> r.a.* / FLOW` |
| `r.b = b` | `b.* / FLOW -> r.b.* / FLOW` |
| `return r` | `r.* / FLOW -> wrapperRet.* / FLOW` |

A field write also has the ordinary strong-preservation micro-edges for
its destination. These do not make the value-transfer edge weak. For the
shown routes:

```text
new Box z:             there is no tainted z fact to preserve or kill
z.value = p:           p.* supplies z.value.*; p.* is retained
new Pair r:            there is no tainted r fact
r.a = a:               writes the A route
r.b = b:               retains an existing r.a fact, since a and b differ
```

Alias analysis can preserve the real links `r.a = q.f` and
`r.b.value = q`. It does not make r, Box, and q the same object, and it
does not move a mark from `q.f.h` to the root of `r.a`. The objects have
distinct types and the fresh allocations cannot alias their Root input.
Ordinary argument identities and ZERO_KEEP are present. They supply no
additional NORMAL return relation at the helper or wrapper A output.

## 3. Run-1, field limit 1

### 3.1 Source and method admission

```text
source GEN before limiting:
    ZERO -> q.f.h.[any-taint]/T, D

source after limiting:
    ZERO -> q.f.[any]/T, D

wrapper actual input:
    q.f.[any]/T, D
wrapper initial and start:
    q.* / FLOW -> q.* / FLOW, N
```

Run-1 forces the concrete source result to DEMAND. The limit removes h
and changes the limited result to MAY. Wrapper's run-1 abstraction emits
the root FLOW initial. Its calls pass the whole q.

### 3.2 Helper and A route

```text
helper actual:         p.* / FLOW, N
helper initial/start:  p.* / FLOW -> p.* / FLOW, N
NORMAL read:           p.f.* / FLOW -> helperRet.* / FLOW
applied result:        p.* / FLOW -> helperRet.[any]/FLOW, D
```

The read premise is below the supplied p root. That application loses
suffix correlation. The instruction remains NORMAL; its result is MAY
in DEMAND.

```text
helper summary at wrapper:  q.* -> a.[any], D
r.a = a:                   q.* -> r.a.[any], D
r.b = b:                   retains the r.a.[any] fact
return r:                  q.* -> wrapperRet.a.[any], D
```

### 3.3 Box and B route: where the second DEMAND is created

```text
box actual:             p.* / FLOW, N
box initial/start:      p.* / FLOW -> p.* / FLOW, N
z.value = p:            p.* / FLOW -> z.value.* / FLOW, N
return z:               p.* / FLOW -> boxRet.value.* / FLOW, N
```

The path has one field, so the limit does not change the Box summary.
The completed run-1 record is NORMAL. It was inferred from `box` code.

Wrapper applies that inferred summary:

```text
call result before r.b = b:
    q.* / FLOW -> b.value.* / FLOW, N

NORMAL write r.b = b, before field limiting:
    q.* / FLOW -> r.b.value.* / FLOW, N

same write, after field limit 1:
    q.* / FLOW -> r.b.[any]/FLOW, D

return r:
    q.* / FLOW -> wrapperRet.b.[any]/FLOW, D
```

This is the replacement for `opaqueMay`. The DEMAND comes from a real
field-limit cut. No instruction or configured summary has an ANY target.

### 3.4 Relevant summaries and the next frontier

| Method | Premise | Result | Layer |
|---|---|---|---|
| helper | `p.* / FLOW` | `helperRet.[any]/FLOW` | D |
| box | `p.* / FLOW` | `boxRet.value.* / FLOW` | N |
| wrapper | `q.* / FLOW` | `wrapperRet.a.[any]/FLOW` | D |
| wrapper | `q.* / FLOW` | `wrapperRet.b.[any]/FLOW` | D |

Each method also has its ZERO and ordinary argument identities. Only the
NORMAL rows persist as reusable native records. The DEMAND rows give:

```text
helper B2:  entry helperRet.[any]/FLOW;    exit p.* / FLOW
wrapper B2: entry wrapperRet.a.[any]/FLOW; exit q.* / FLOW
wrapper B2: entry wrapperRet.b.[any]/FLOW; exit q.* / FLOW
```

There is no Box demand. Its NORMAL record remains available in run-2.
The concrete input in main can use the inferred FLOW summaries to satisfy
the sinks in run-1. No concrete helper initial is needed in that run.

## 4. Run-2, field limit 1

### 4.1 Keep the source selected

The independent `sinkAny(q.f.h)` seeds a concrete T requirement. Reversing
its field reads and applying the limit gives `q.f.[any]/T, D`. This reaches
the reversed source at f.h and records a source hit. Thus run-3 can execute
the source rule again. No abstract FLOW packet must cross a concrete source
gate to establish this hit.

### 4.2 A route constructs the helper exact record

```text
main exact sink:               r.a.$/T
backward wrapper actual:       wrapperRet.a.$/T
wrapper demand entry:          wrapperRet.a.[any]/FLOW
emitted wrapper initial/start: wrapperRet.a.$/FLOW -> itself, N
reverse return and r.a = a:    a.$/FLOW, N
reverse helper result binding: helperRet.$/FLOW, N
```

The helper receives FLOW metadata with an exact tail. A FLOW demand can
accept a FLOW actual, as in the existing overlap path. The new selected
policy retains the supplied EXACT tail:

```text
helper demand entry:     helperRet.[any]/FLOW
helper actual:           helperRet.$/FLOW
helper initial/start:    helperRet.$/FLOW -> itself, N
NORMAL reversed read:    helperRet.* / FLOW -> p.f.* / FLOW
raw helper summary:      helperRet.$/FLOW -> p.f.$/FLOW, N
```

C5 accepts the helper initial under its ANY entry and the exact result under
its STAR exit. Its live answer returns to wrapper:

```text
wrapper summary: wrapperRet.a.$/FLOW -> q.f.$/FLOW, N
```

C5 accepts this wrapper A row. Both exact rows persist. There is one helper
callsite in wrapper throughout the trace. A separate direct helper probe
and a shared context between two callers are not required.

### 4.3 B route keeps a root ANY demand

```text
main ANY sink:                r.b.[any]/T
backward wrapper actual:      wrapperRet.b.[any]/T
wrapper demand entry:         wrapperRet.b.[any]/FLOW
emitted wrapper initial:      wrapperRet.b.[any]/FLOW, D
reverse return and r.b = b:   b.[any]/FLOW, D
reverse Box result binding:   boxRet.[any]/FLOW, D
```

Use the inferred NORMAL Box record from run-1 in its reversed read view:

```text
record view: boxRet.value.* / FLOW -> p.* / FLOW, N
actual:      boxRet.[any]/FLOW, D
```

The actual is an ancestor of the record premise. The ordinary above-case
application returns `p.[any]/FLOW, D`. Binding p back to q gives:

```text
wrapper raw summary:
    wrapperRet.b.[any]/FLOW -> q.[any]/FLOW, D
```

No new Box initial or Box analysis is needed. Native record reuse handles
the call. Passing the q requirement through the earlier helper call uses
its argument identity; it does not turn it into a helper return requirement.

C5 accepts the B initial under its ANY entry. Its existing exit-side
restriction retains `q.[any]/FLOW` under `q.* / FLOW`. The new emitter-image
guard applies to the entry, not to this exit reduction.

The run-3 wrapper demand is therefore:

```text
entry q.[any]/FLOW; exit wrapperRet.b.[any]/FLOW
```

The helper exact row is NORMAL and creates no new helper demand.

## 5. Run-3, field limit 2

The source hit in run-2 enables this input:

```text
source result:         q.f.h.[any-taint]/T, N
wrapper demand entry:  q.[any]/FLOW
wrapper initial:      q.f.* / FLOW
wrapper start:        q.f.* / FLOW -> itself, N
helper actual:        p.f.* / FLOW, N
```

The first new field f resolves the demanded ANY. The selected policy stops
there. It does not consume h. This is an abstract FLOW STAR initial, so the
concrete-STAR DEMAND rule does not apply.

The ordinary Box route now has this shape:

```text
wrapper argument at Box call: q.f.* / FLOW, N
Box result at wrapper:       b.value.f.* / FLOW, N  // two fields fit
r.b = b, before limiting:    r.b.value.f.* / FLOW, N
after field limit 2:         r.b.value.[any]/FLOW, D
return r:                   wrapperRet.b.value.[any]/FLOW, D
```

This B result refines its run-1 shape. It is accepted under the existing
`wrapperRet.b.[any]/FLOW` exit demand. The trace claims no invariant B
frontier or unbounded cycle.

The persisted helper backward row has this forward read view:

```text
p.f.$/FLOW -> helperRet.$/FLOW, N
```

It is available at the caller even though helper has no new nonzero demand.
The normal wrapper A record has exact premise `q.f.$/FLOW`; it cannot itself
match the concrete source input whose mark is below h.

## 6. Unchanged exact application cell and the false NORMAL row

At the helper call the compared descriptors are:

```text
record premise: p.f.$/FLOW
caller actual:  p.f.* / FLOW, N
```

Geometric inside matching accepts this same-prefix pair. If the typed
abstract EXACT shape is admitted while the current target-EXACT cell stays
unchanged, replay returns:

```text
helperRet.$/FLOW, N
```

The ordinary return binding and actual field write `r.a = a` then produce:

```text
q.f.* / FLOW -> r.a.$/FLOW, N
q.f.* / FLOW -> wrapperRet.a.$/FLOW, N
```

The later write to r.b preserves this A fact because the fields differ.
The Box route reaches B, not A. It supplies no NORMAL STAR A cover.

The false NORMAL pair in that row is:

```text
input q.f.h/T -> output wrapperRet.a/T
```

The real Java helper preserves the suffix:

```text
q.f.h/T -> helperRet.h/T -> a.h/T -> wrapperRet.a.h/T
```

No code statement or rule assigns T to the root of A.

## 7. C5, persistence, and coverage inventory

The available NORMAL families do not cover the disputed helper result:

| Available family | Why it does not cover the A return relation |
|---|---|
| Helper and wrapper argument identities | Their result base is the argument |
| Box `p.* -> boxRet.value.*` | Another method and result type |
| Helper backward exact record | Exact premise and result, no STAR cover |
| Wrapper backward exact A record | Exact premise, not a broad correlated relation |
| ZERO rows | Different data bases |

Run-1 helper/A return summaries are DEMAND. No NORMAL `p.f.* -> helperRet.*`
row is inferred or retained by these methods before the disputed replay.

C5 sees only the run-3 wrapper B pair. It rejects the new A output because
a and b are apart. Current summary handling stores raw summaries before
C5 publication. Completed-run persistence reads those raw NORMAL rows.
It therefore retains the false A relation even though C5 does not publish
it. The trace does not assume that C5 publication and persistence are the
same operation.

## 8. Validation and decision boundary

The code, source/sink rules, instruction transfers, each field-limit cut,
initial admission, inferred/native records, C5 and handoff above define the
example. There is no `opaqueMay`, pass rule, predefined method, or declared
Pair constructor summary.

The constructive Lean certificate and complete phase data are embedded in
[the trace evidence](../reports/data/bidirectional-closed-exact-replay-20261029.json).
The active certificate is `RestrictedInitialPolicy.CodeOnlyExactReplay` in
[RestrictedInitialPolicy.lean](../../spec/lean/proposals/initial-emission/RestrictedInitialPolicy.lean).
Its 11 checked theorems cover the STAR instruction shapes, inferred Box
record, run-1 cut, run-2 demand, argument/field/control frames, helper-record
inventory, run-3 raw persistence, and the concrete false pair. Its executable
check returns `true`. All-theorem audits use only `propext` and `Quot.sound`.
It models the proposed abstract EXACT domain. The current Kotlin exact cell
is explicit, because the older Lean STAR/Universe cell has other behavior.
MUST certainty at admission is explicit. The model is a finite operator
trace, not a complete JVM or alias-analysis implementation proof.

The Java listing compiles with `javac`. This checks Java syntax and types;
it does not execute source/sink rules or validate the proposed AP domain.
The evidence includes that receipt separately from the Lean receipt.

The code boundaries used for the trace are:

| Part | Existing code boundary |
|---|---|
| Ordinary read and strong write transfers | `MicroEdgeBuilder.read`, `write`, and `strongKeep` |
| Direct unconditional source GEN | `JIRRuleForms.markTarget`, `source` |
| MAY from an ancestor read/application | Scalar `Reference.above` |
| Field-limit cut before propagation | `RunMethodAnalyzer.runStatement`, `cut(Cut.STATEMENT, ...)` |
| Native record matching and replay | `Reference.satisfies`, `recordDemand`, and summary application |
| Raw summary before C5, then persistence | `RunMethodAnalyzer` summary emission; `RecordStore` normal-record handling |

The remaining decision is the same: how an uncovered exact FLOW record can
apply to a broad STAR FLOW input. No DEMAND demotion, exact-only guard, or
new correlation payload is selected by this note. A retained NORMAL STAR
cover can remove a covered exact candidate before application; this example
has no such cover.
