# Cleaner termination: two counterexamples and bounded repairs

17 November 2026. Synthetic data-flow reachability. FULL marks.
Baseline: `966a40c36472`. Follow [proof-guide.md](../../spec/proof-guide.md).
The [consolidated proposal](../design/bidirectional-demand-termination-approach-20261115.md)
now includes R35 and R36 below. Production code is unchanged.

**Result:** two cleaner patterns renewed Target demand without a field cut.
Both have an uncapped recurrence proof. R35 resolves the first at **run-1**;
R36 resolves the second at **run-3** in the reference. Unchanged native
diagnostics reach **run-15/POLICY**. That cutoff is not the recurrence proof.
A fresh finite search found no further counterexample in 2,551,500 cases;
its latest natural completion is **run-5**. Universal termination and the
general whole-analyzer soundness obligations remain open.

## 1. Contract and semantic changes

```text
M = MAY; NE = non-empty MAY; U = MUST (uniform taint)
$ = EXACT; * = correlated STAR; F = FLOW
T = one full mark; N/D = NORMAL/DEMAND; H = existing survivor protection
Z = ZERO; DT = DemandTarget; NT(id) = NormalTarget for one observation
E={f} excludes the subtree at the first field f, at this fact's own head.
```

| Rule | Before | After | Semantic effect |
|---|---|---|---|
| R35: selected EXACT on concrete MUST | Only the same-head exception keeps the input layer; a descendant cleaner demotes MUST to DEMAND | Keep the MUST input, E and layer for every relative cleaner position on the same base/mark | Extend the already selected MUST/EXACT coarsening under projection. The selected descendant point can remain NORMAL. This is not exact point deletion |
| R36: ALL/BELOW below a NORMAL concrete MUST | Only a one-field cleaner can use a precise exclusion; a deeper cleaner demotes the whole fact | After run-1, emit the exact residual along that one cleaner path | Remove an unnecessary approximation. Whole-subtree deletion remains precise. Run-1 stays unchanged |

R35 applies only to selected-mark EXACT cleaners in FULL mode. R36 applies
only to NORMAL concrete MUST in FULL mode, after run-1. A DEMAND input never
becomes NORMAL. Selected BELOW and selected/RemoveAll ALL are supported;
below-only RemoveAll stays prohibited. FLOW, other marks, rejected rule
shapes, source permissions, C2/C5, Targets, summary ownership and field caps
retain their selected rules. Apply the old transfer outside these guards.

R35 retains one input-shaped output. It can add a NORMAL observation at the
point that an exact point cleaner would delete. This is the explicit
extension of the accepted same-head policy; it is not a new claim that all
NORMAL observations have exact point-cleaner semantics. Nonuniform EXACT
facts still disappear when their selected point is cleaned.

## 2. First counterexample: selected descendant point

Rules assign T uniformly at x on allocation, clean T exactly at argument.f
on the call, and observe `CM(x.M,T)` at the end of main. The empty method
is fully analyzed. There is no unresolved transfer, special pass, loop,
recursion or predefined summary.

### Run-1, forward, limit 1, before R35

```java
// Demand: none (unrestricted run-1).
// Submitted: Z,N. Initial: Z -> Z,N.
void main() {
    Node x = new Node(); // Z -> x.U/T,N
    clearTAtF(x);       // action: Z -> x.U/T,D,H=1; no field was cut
    observe(x);         // Z -> DT,D
}
// Published: Z -> Z,N; Z -> DT,D. No NT.
// Handoff: [Target | Z].

// Submitted at the call: p.U/T,D,H=1 (plus the control offer).
// Run-1 structural initial: p.* / F -> p.* / F,N; control initial Z,N.
// No selected-T check occurs in this empty body.
void clearTAtF(Node p) {}
// Published body summaries: p.* / F -> p.* / F,N; Z -> Z,N.
// The cleaner action belongs to the caller's bound call stage, not this body.
```

The body identity is computed from code; it is not supplied as a model.
Its application preserves the caller's DEMAND and H. There is no return
DATA result. The caller's cleaner action supplies the marked partial row.

### Run-2, backward, limit 1, before R35

```java
// Published: Z -> Z,N; Z -> DT,D. Handoff: [Target | Z].
void main() {
    Node x = new Node(); // reverse marking consumes x.M/T,D,H=1;
                        // records the real source permission; produces Z -> DT,D
    clearTAtF(x);       // backward requirement stays x.M/T,D,H=1
    observe(x);         // creates x.M/T,D from the admitted Target route
}
// Demand: [Target | Z]. Submitted: the actually reached backward control Z.
// Initial: the existing Target/ZERO control route; no owned DATA/MAY initial.

// Saved opposite-direction body identity is applied. No current DATA summary.
void clearTAtF(Node p) {}
// Submitted: p.M/T,D. Current demand: empty. Current DATA initials: none.
// Saved NORMAL body replay runs before the empty current-demand test.
```

### Every run-(2n+3), forward, limit 2n+2, before R35

```java
// Demand: [Target | Z]. Submitted: Z with the real backward source permission.
// Initial: Z -> Z,N; no DATA initial.
void main() {
    Node x = new Node(); // Z -> x.U/T,N
    clearTAtF(x);       // Z -> x.U/T,D,H=1, at every limit
    observe(x);         // Z -> DT,D
}
// Published: Z -> Z,N; Z -> DT,D. Handoff: [Target | Z].

// Saved NORMAL body identity applies to p.U/T,D,H=1.
// Current demand/initials: empty; no new body analysis is needed.
void clearTAtF(Node p) {}
// New DATA summaries: none. Existing identity leaves the offered layer intact.
```

Every intervening backward run has the run-2 trace. The root has no DATA
summary to compact or retire. H prevents FLOW backing from removing the
selected survivor. The FLOW complement excludes T. R31 is a FLOW rule;
R34 does not change same-head MUST/MAY replay. None removes this Target.

### Uncapped proof

Let F be the complete forward state `(Z->Z,N; Z->DT,D; observation permission)`
and B the backward state with the same summaries and real marking permission.
Direct evaluation of the cold prefix gives `run1=F` and `back(F)=B`.
For every n, `forward(2n+3,B)=F`. Induction gives:

```text
∀n≥0: Handoff(run-(2n+1)) = Handoff(run-(2n+2)) = {[Target | Z]} ≠ ∅.
```

All relevant facts have an empty field path. `cut(k,fact)=fact` for every k.
Increasing the limit cannot change the transfer. Run-3 and run-5 have the
same literal demand, not just equal counts. Each run itself reaches closure.
The proof includes permissions, C5 control selection, the computed empty-body
identity and the inactive existing repairs.
[Constructive model](../../spec/lean/proposals/descendant-cleaner-cycle-20261117/DescendantCleanerCycle.lean).

### R35 repair and proof

```text
cleanSelectedExact(c, cl):
    if FULL and c is concrete MUST of cl.mark and c.base == cl.base:
        return existingSelectedProtection(c) // preserve fields/E/input layer
    return oldClean(c, cl)
```

Conceptually, split a uniform region along the one cleaner path. Keep the
outside region at each prefix. At the final head use the accepted same-head
MUST exception. The final child fills every preceding hole. The union is
the original region, including its original E. R35 returns that one fact
directly; it does not construct the conceptual spine.

The arbitrary-path/E proof equates membership in the conceptual union with
membership in the optimized output. It also proves layer preservation,
unchanged unsupported branches, exact nonuniform killing and natural
run-1 completion with `Z -> NT(id),N`. No later run is started.
[Repair model](../../spec/lean/proposals/descendant-cleaner-cycle-20261117/ExactMUSTClosure.lean).

## 3. Second counterexample: nested whole-subtree cleaning

Replace the cleaner rule with selected ALL at p.f.g. The selected BELOW
and RemoveAll/ALL variants have the same recurring state. R35 is inactive.

### Run-1, forward, limit 1, before/after R36

```java
// Demand: none. Submitted: Z,N. Initial: Z -> Z,N.
void main() {
    Node x = new Node(); // Z -> x.U/T,N
    clearTAtFG(x);      // ALL p.f.g: Z -> x.U/T,D,H=1
    observe(x);        // CM(x.M,T): Z -> DT,D
}
// Published: Z -> Z,N; Z -> DT,D. Handoff: [Target | Z].

// Submitted: p.U/T,D,H=1 and control. Structural/control initials as above.
void clearTAtFG(Node p) {}
// Published: p.* / F -> p.* / F,N; Z -> Z,N.
```

### Run-2, backward, limit 1, before/after R36

```java
// Published: Z -> Z,N; Z -> DT,D. Handoff: [Target | Z].
void main() {
    Node x = new Node(); // reverse marking accepts the real overlapping requirement
    clearTAtFG(x);      // x.M/T,D stays partial/D; no NORMAL upgrade
    observe(x);        // admits x.M/T,D from the Target route
}
// Demand: [Target | Z]. Submitted: backward control Z.
// Initial: the existing Target/ZERO control route, no owned DATA/MAY initial.

// Saved body identity replays; no new DATA summary.
void clearTAtFG(Node p) {}
// Submitted: p.M/T,D. Current demand/initials: empty.
```

### Run-3, forward, limit 2, with R36

```java
// Demand: [Target | Z]. Submitted: Z plus the real marking permission.
// Initial: Z -> Z,N.
void main() {
    Node x = new Node(); // Z -> x.U/T,N
    clearTAtFG(x);      // Z -> x.U/T {f},N,H=1
                       // Z -> x.f.U/T {g},N,H=1
    observe(x);        // CM(x.M,T): Z -> NT(id),N
}
// Published: Z -> Z,N; Z -> NT(id),N. Outgoing demand: empty; stop run-3.

// Saved identity applies to both NORMAL bound residuals, with their own E/H.
// Current demand/initials: empty.
void clearTAtFG(Node p) {}
// New DATA summaries: none.
```

BELOW additionally keeps `Z -> x.f.g.$/T,N,H=1`. All these paths fit limit 2.
RemoveAll/ALL keeps the same two T residuals (and processes each other mark
under its existing ownership). No mark at or below x.f.g survives ALL.

Without R36, every later forward run instead emits the run-1 partial MUST
row and DT. The two-field condition misses the current one-field special
case. Its full control transition equals the first counterexample's F/B
transition. Induction therefore proves nonempty demand for every pair.
[Counterexample and repaired protocol](../../spec/lean/proposals/uniform-cleaner-spine-20261117/NestedCleanerProtocol.lean).

## 4. R36 algorithm, bounds and soundness

Run the existing spatial walker first. Whole inside regions are killed;
disjoint/excluded regions are unchanged. For one NORMAL concrete MUST at
head q, with a strictly deeper cleaner q.f1...fd, use this residual builder
after run-1:

```text
residual(reach, remaining, E):
    if remaining is empty:
        return [] if reach == ALL else [EXACT(empty)] // selected BELOW
    f, rest = splitFirst(remaining)
    if f in E: return [MUST(empty, E)]
    return [MUST(empty, E ∪ {f})]
           ++ prepend(f, residual(reach, rest, EmptyE))

transfer(c, cl):
    if eligibleNormalMUSTSubtreeCase(c, cl):
        for region in residual(cl.reach, cl.path - c.path, c.E):
            emit ordinaryGlobalCut(keepPremiseLayerMarkAndH(c, region))
    else: oldClean(c, cl)
```

Do not copy a parent hole onto its child. Existing field caps remain
mandatory, including C5's later `min(global,FL(Dp)+1)` cap. Any real cut
emits NE/DEMAND with Empty E, as before. No initial, path or cap exception
is added. A runtime builder can stop at the cap and merge the cut suffix
into one NE row; there is no unbounded residual archive.

For arbitrary cleaner path, E and marked point w, the constructive proof gives:

```text
w ∈ union(residual(ALL,c,E))   ↔ w ∈ MUST(E) ∧ w ∉ subtree(c)
w ∈ union(residual(BELOW,c,E)) ↔ w ∈ MUST(E) ∧ w ∉ strictDescendants(c)
rows ≤ length(c) + 1
every new head is a prefix of c.
```

Thus every retained real point remains represented, cleaned whole-subtree
points disappear, and every uncut result is a valid NORMAL residual. A cut
overapproximates only its bounded output; it does not assert NORMAL certainty.
The ordinary premise, mark, H and input layer are retained. Selected survivors
keep the existing H producer; no pass acquires protection.
[Arbitrary-path proof](../../spec/lean/proposals/uniform-cleaner-spine-20261117/UniformCleanerSpine.lean).

For one uniform input, residuals are disjoint pieces. A later cleaner head
can lie in at most one piece; it removes or leaves the others. Across a
sequence of cleaners, heads come from the union of their path prefixes,
not a product of field choices. Two cleaners of depth three need at most
seven pieces in the checked family. This is not a global bound on unrelated
premises, marks, branch contexts or exclusion variants. R35 adds no rows;
R36 adds at most d rows per processed NORMAL input. All outputs use normal
deduplication; no new subscriptions or persistent stores are selected.

Earlier rules are unchanged outside these two guards. The one-field R36
case equals the existing native transfer; run-1 still has Empty E. The
older same-head cleaner case is a subset of R35. Generic membership proofs,
native controls and the previous source-hash-checked proof closure retain
the earlier evidence. They do not prove integration of the whole proposal.

## 5. Fresh search and validation

| Check | Result | Latest reached run |
|---|---|---|
| Current native EXACT, nested ALL, nested BELOW, nested RemoveAll/ALL diagnostics | Recurrence reproduced; 4 policy-cutoff controls | run-15/POLICY |
| R35 repaired reference | NORMAL Target, empty handoff, uncapped quiet suffix | natural run-1 |
| R36 ALL/BELOW repaired reference | Precise NORMAL residuals and Target; uncapped quiet suffix | natural run-3 |
| Fresh cleaner reference | 56,700 pipelines; 2,551,500 observation cases; zero recurrence or required-point losses | natural run-5 |
| Combined native regression/component suite | 111 tests pass, zero failures/errors | Earlier cold controls through natural run-9; diagnostic runs are separate |

The fresh search uses two fields; source EXACT/MUST paths of length 0..2;
two selected EXACT/ALL/BELOW cleaners with paths of length 0..3; and
EXACT/MAY/NE observations at paths of length 0..3. It checks all words of
length 0..5 for residual membership. Half the sources have Empty E and
describe the ordinary marking programs; half are real-E component inputs.
The latter are not claims that a marking rule creates nonempty E in run-1.
Source-E components test the scalar residual and permission calculation.
RemoveAll/ALL has the same single-mark residual as selected ALL and has
separate native checks. It is not a license for below-only RemoveAll.

The control model keeps Target demand, backward marking permission and
both NORMAL/DEMAND witnesses. An empty DATA frontier alone never stops it.
At run-5, every candidate in this finite family either stopped earlier or
has a fully representable precise residual. It has no remaining cut or
partial-MUST approximation. Checks compare the selected-policy residual
with an independent membership oracle, and preserve all retained actual
marked points. They do not require the extra exact-point observations
allowed by R35's stated coarsening.

This is a single-local acyclic cleaner scope. It does not cover arbitrary
conditional marking, ND, multiple methods, aliases, statics, groups or
concurrent completion. Earlier references/native tests retain their stated
call and conditional scopes; the new search does not replace them. No
further example was found in the combined checked scopes. General G1–G4
remain open. Production lacks these proposal repairs and the new tail.

Proof audit: **63 new constructive claims; 7,308 cumulative in 427
source-hash-checked modules**. Only `propext` and `Quot.sound` are allowed
in transitive axiom dependencies. No classical choice, custom axiom, gap
marker or native decision shortcut is allowed.

[Checker and scope](../../spec/lean/proposals/uniform-cleaner-spine-20261117/README.md).
Native sources:
[recurrence/controls](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/DescendantCleanerTerminationTest.kt),
[R35](data/bidirectional-experiment-sources-20261118/core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/ExactUniformCleanerClosureTest.kt),
[R36](data/bidirectional-experiment-sources-20261118/core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/UniformCleanerSpineTest.kt).

Compiled models, per-claim axiom logs, the search output, Gradle log and
111-test XML files are outside Git under `uniform-cleaner-spine-20261117/`
at the [external data root](EXTERNAL_DATA.md). There is no new project
performance measurement or whole-proposal production run.
