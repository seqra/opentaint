# Worked facts: the two-loop handoff and the deep-loop Target

7 November 2026. Both native finding assertions still fail. This is a worked
trace of the current behavior, not a selected repair.

`T` is the full concrete mark, `FLOW` is the abstract mark, and
`F = Box.shared`. `$` means EXACT; `*` means STAR; `[any]` means MAY;
`S?` means STAR_OR_ANY. `N` and `D` mean NORMAL and DEMAND.
All facts shown have Empty E and no protection flag.
`ZERO -> value` means a fact with original ZERO, not a field of ZERO.

**Captured** facts come from the exact native trace. **Derived** steps apply
the pinned transfer/handoff/C2 source to captured facts. The traces do not
record every C2 input/result transaction. The [portable data](data/bidirectional-star-or-any-worked-fact-traces-20261107.json)
embeds both traces, the decisive XML files and sources with hashes. The
[earlier ledger](bidirectional-star-or-any-handoff-gap-20261107.md) retains the
full-suite and targeted results.

## 1. Two successive loops

The fixture has two real methods: `main` and `get`. `sourceAtG` and `sinkT`
are configured physical rule occurrences in `main`. Local loop blocks do not
create extra public methods. The required finding is at physical node 6.
The complete run sequence is F1/FL1, B2/FL1, F3/FL2. It ends at F3 with no
finding, although the source-to-sink path is required by the native test.

### Run 1: forward, field limit 1

```java
void main() {
    while (again1) {                      // L1; header node 1
        a = sourceAtG();                  // node 2: ZERO -> a.g.$/T, N
        F = a;                           // node 3: geometry F.g.$/T
        // F has counted field "shared"; F.g has two counted fields.
        // FL1 cuts it to F.[any]/T, D. [derived; result captured]
    }
    while (again2) {                      // L2; header node 4
        b = get();                       // node 5: FLOW result b.[any], D
        sinkT(b.g);                       // node 6 needs b.g.$/T
        // No NORMAL finding. A concrete T demand remains unresolved.
    }
}
Object get() {
    return F;                            // static read at getter node 1
    // Captured FLOW row takes F.* to ret.[any], D.
    // This is a run-1 static approximation, not a uniform NORMAL return.
}
```

Produced summaries and Targets, **captured**, after the declarations above:

```text
main, root:  ZERO -> F.[any]/T, D
get, root:   F.*/FLOW -> ret.[any]/FLOW, D
L2, entry10 -> exit8: F.*/FLOW -> b.[any]/FLOW, D
L2 Target:   F.*/T -> DemandTarget
```

These rows are in two-loop trace lines 8, 21, 32 and 35. The full-T Target is
separate from the abstract FLOW row; FLOW itself is not proof of mark T.
The source result `a.g.$/T,N` is captured at node3 (line63). The public getter
row is captured; this report does not attribute its MAY tail solely to a
field-limit cut inside the getter.

The getter row reverses into this B2 demand (**derived**):

```text
entry ret.[any]/FLOW  -> paired exit F.*/FLOW
```

Demand orientation matters: its entry selects the getter initial, and its
paired exit restricts the getter's completed backward output.

### Run 2: backward, field limit 1

The comments below follow the backward flow, from the sink toward the source.

```java
void main() {
    while (again1) {                      // L1
        a = sourceAtG();                  // backward source hit at node 2
        // Captured backward write result reaches here as a.S?/T, D.
        // The exact physical source occurrence is recorded for F3.
        F = a;                           // backwards: F.S?/T -> a.S?/T, D
    }
    while (again2) {                      // L2
        b = get();                       // b.g.$/T,N binds to ret.g.$/T,N
        // Apply the captured backward FLOW row from get:
        // its output is F.[any]/T,D on this marked caller input.
        sinkT(b.g);                       // seed: ZERO -> b.g.$/T, N
    }
}
Object get() {
    // Demand entry: ret.[any]/FLOW. Bound actual: ret.g.$/T,N.
    // C2 first-new-field output: ret.g.*/FLOW, N. [derived]
    // This raw FLOW initial and start are captured at getter nodes2/1/0.
    return F;
    // Reverse read has F.g geometry. FL1 gives F.[any]/FLOW,D.
    // The completed backward row is captured, not guessed from a source rule.
}
```

Produced summaries and the source hit, **captured**:

```text
get, root: ret.g.*/FLOW -> F.[any]/FLOW, D          // line53
caller output with original ZERO: F.[any]/T, D    // line106
L1 live original/start: F.S?/T, D                 // lines107-118
L1 public, entry10 -> exit4: F.*/T -> F.*/T, D     // line39
L1 public, entry4  -> exit4: F.*/T -> F.*/T, D     // line42
source hit: main node2, exact ZERO -> a.g.$/T      // line36
```

`ret.g.*/FLOW,N` is an abstract FLOW initial, not a concrete MUST or EXACT
initial. Its completed result is D. Applying that FLOW relation to the
caller's T-marked input produces the captured T-marked D output.

For L1, the current same-head MAY emission cell changes the selected MAY
initial into raw `F.S?/T,D`. The raw original and live fact are captured.
Public summary normalization changes both S? endpoints to STAR and preserves
D. The backward write and source hit succeed; F3 has the real physical source
permission. These points precede the later loss.

The paired L1 row reverses as follows (**derived** from captured line39):

```text
B2 producer: scope L1/entry10, output exit4
public row:  F.*/T -> F.*/T, D
F3 demand:   scope L1/entry4, paired output exit10
             entry F.*/T -> exit F.*/T
```

The entry4/exit4 row also supplies a repeat entry4/exit4 STAR pair. Handoff
keeps both control ports and the same full mark. It invents no descendant
`F.g` demand.

### Run 3: forward, field limit 2

```java
void main() {
    while (again1) {                      // L1
        a = sourceAtG();                  // authorized ZERO -> a.g.$/T,N
        F = a;                           // F.g.$/T,N now fits FL2
        // Produced at repeat exit4. To leave L1, control must first
        // re-enter its header through repeat entry4.
        // C2 demand entry F.*/T + actual F.g.$/T,N -> no initial. [derived]
    }
    while (again2) {                      // no captured F3 processing here
        b = get();                       // no F3 getter actor
        sinkT(b.g);                       // required finding is absent
    }
}
Object get() {
    return F;                            // not analyzed in captured F3
}
```

Produced L1 summaries, **captured**:

```text
L1, entry0 -> exit4: ZERO -> F.g.$/T, N            // line55
L1, entry4 -> exit4: ZERO -> F.g.$/T, N            // line56
main root: ZERO identity only; no Targets          // line54
end: COMPLETE / F3 / NO_DEMAND_EDGE; no finding    // lines1-4
```

Source permission is true (line7). F3 processing covers nodes1/2/3, including
`a.g.$/T,N`; it has no nodes4/5/6 and no getter actor (lines119–126).

The first rejected gate identified by the captured endpoints and current
source is **C2 admission**, with complete caller original ZERO:

```text
run3 FORWARD, FL2, scope L1/entry4
actual F.g.EXACT/T,N; demand F.STAR/T; E={}
actual path is strictly below demand path
STAR descendant cell: run==2 ? requested STAR : reject
```

Thus F3 rejects before that repeat input can reach the header and leave for
L2. This exact C2 call/result was not logged live; it is source-derived.
It is not a failure of STAR summary geometry: `F.*` geometrically covers
`F.g.$` with Empty E. Summary matching and C2's rule for starting a current
traversal are different operations. This statement does not assert that a
NORMAL saved STAR record exists at that interface.

## 2. Deep loop: “shouldn't there be Target demand with ANY?”

The new 193-line dump captures the block Targets and actual incoming paired
demands. The expected finding still fails at complete run5. Its XML has one
test and one failed finding assertion. No new proof PASS is claimed.

```java
void deep(Node arg) {
    x = arg;
    while (true) {                       // L = block2, repeat entry5
        sourceAtFFFF(x);                 // exact T at x.f.f.f.f
        x = x.f;
        sinkT(x);                        // exact T required at x itself
    }
}
```

Captured local Targets and their actual next-run demand rows:

| Producer Target | Incoming paired demand, captured before the next run |
| --- | --- |
| F3: `x.f.$/T -> DemandTarget`, L/entry5, terminal ROOT_EXIT=-2 (line63) | B4: L/entry-2, output5, `Target -> Data(x.f.$/T)` (line15) |
| B4: `x.ff.*/T -> DemandTarget`, L/entry5, terminal ROOT_ENTRY=-1 (line70) | F5: L/entry-1, output5, `Target -> Data(x.ff.*/T)` (line20) |

The raw emitted Target rows alone would not prove acceptance. Here the
incoming maps also contain their projections, so these specific rows were
accepted and handed off. **Neither captured row has a MAY exit.** The F3
Target has an EXACT original; the B4 Target has a STAR original.

MAY guidance does exist on another, distinct path:

```text
F3 DATA summary: ZERO -> x.f.[any]/T,D             // lines59,61
B4 repeat entry5, outputs1/5:
    Data(x.f.[any]/T) -> Zero                     // line14

B4 DATA summaries: x.ff.*/T -> ZERO,D             // lines68,69
F5 entries1/5, output5:
    Zero -> Data(x.ff.*/T)                        // lines18,19
```

The B4 first-new-field C2 rule can select `x.ff.*/T,D` from an actual deeper
than its `x.f.[any]/T` entry. It emits ordinary STAR in that cell; it does not
emit MAY and then decorate it with S?. The captured B4 processed original is
already `x.ff.STAR/T`. The complete C2 transaction is not logged, so this
policy explanation is source-derived. The Target keeps that original and
therefore hands off STAR. This is not an observed S?-to-STAR loss in that
B4 Target.

A typed `Target` entry is control, with no AP tail. “Target with ANY” means
ANY on its paired DATA **exit**. C2 uses a Target/Zero entry to admit ZERO,
not a nonzero DATA fact. A DATA exit can instead constrain a completed
ZERO-origin result through C5 at that exact scope and output port.

At Empty E, both exits `x.ff.[any]/T` and `x.ff.*/T` accept the already
produced `x.fff.$/T,N` in C5, with the same exit depth and budget. That is not
the later-run STAR-demand C2 rejection. It does not by itself prove that the
complete enclosing observer accepts this result.

The actual F5 repeat view additionally has `Data(x.f.$/T) -> Zero` at output11
(line18). Its exact DATA entry cannot admit the deeper `x.fff.$/T` actual.
The Target/STAR and Zero/STAR rows do not add a nonzero repeat initial.
The post-run query confirms `initials=[]` (line76); it is not a captured live
C2 transaction. A separate post-run query returns a shrinking saved NORMAL
row `x.f.*/FLOW -> x.*/FLOW` at the repeat scope (line77), not proof of replay.

This Target trace resolves the earlier uncertainty about those specific
paired rows. It does not select saved-repeat preplay, another consumer family,
new MAY guidance or a STAR admission change. Deep's complete repair remains
open. No core/test change or fresh project campaign was made for this report.

## Current recheck after the shared-carry C5 adapter repair

A separate C5 adapter defect is now repaired in the working tree. A raw MAY
carry can start S? and store STAR; C5 must recognize that valid raw preimage.
The adapter first keeps its existing same-slot pair. Only if that entry
rejects the stored STAR does it try the existing same-slot MAY pair, guarded
by unchanged `canStoreInitial`. It changes no C2, guidance or loop policy.
The 13 local adapter laws pass; they do not prove whole-engine equivalence.
The native boundary regression changed from 12 tests/1 failure to 12/0.

| Current check | Tests | Failures | Observed finding result |
| --- | ---: | ---: | --- |
| Static adapter and control bundle, including that boundary regression | 34 | 1 | All 33 other checks pass; the deep no-loop case still has no finding at complete F3. |
| Original loop suites recheck | 3 | 2 | Two-loop case still ends at F3 without its finding; DeepNoLeave still ends at F5 without its finding. |

In the separate no-loop case, let `G=C.g`. B2 now captures the physical source
hit, and F3 captures the actual `G.h.$/T,N` offer to the callee. Its captured
local demand is `G.*/T -> G.*/T`; the remaining F3 C2 rejection follows from
the unchanged descendant rule. The original two-loop rows39/55/56 are exactly
the same on recheck; four serialized lines differ only in the order of their row members. The data
preserves the original captures and appends the new XML, traces, receipts,
model/checker receipt and current `DemandStore` source pin. Finding assertions
and the pending behavior choices remain unchanged. No fresh project campaign
or full native gate pass is claimed.
