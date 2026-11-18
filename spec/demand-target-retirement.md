# Candidate specification for demand Target retirement

**Possible next iteration.** R37–R40 are under consideration. The
[active refinement spec](demand-refinement-and-termination.md) uses the
native Target handoff. The rules and run outcomes below describe the
checked reference models. Use the access-path notation, layers, C2/C5
pairs and scoped handoff from the active spec.

Retiring a root DemandTarget (DT) changes which backward ZERO starts
and source permissions remain available. Before selecting runtime
retirement, prove that native extraction covers the affected source
routes and every other consumer of the qualified guide.

## 1. R37/R38 terminal service proof

**Candidate change.** At a forward handoff, retire root `ZERO→DT`
only after proving service for every terminal origin and other use.
The proof model uses the native Target keys and typed compaction.
R37 tracks whether a terminal origin still requires refinement. R38
checks service for each marking action and binding of each origin.

For one goal g, fix the observer, FULL mark/position predicate and
graph/rule revision. S is its complete catalogue of marking actions
and bindings, including sites beyond the current cut or without
permission. U covers every possible native source-to-goal path.
N contains only paths backed by retained root NORMAL witnesses from
the same binding and mark to g.

```text
closeGoal(g):
    if S, U or N is unvalidated: return Unknown
    possible = S ∩ reverseReachable(U, g)
    served   = S ∩ reverseReachable(N, g)
    if every s in possible is in served or has validated NoRoute(s,g): return Closed
    return Open

at a completed forward seal: freeze Closed goals for the next forward run
for each admitted DT key: OR the bits of all derivations and relay the result
    local bit = true for an unknown goal or a goal outside the frozen set
    relay bit = OR of input bits under the complete binding
    process false-to-true upgrades to closure
root DT can retire iff bit == false and every other use has retained service
```

Other uses include scoped C2 ZERO admission, paired C5 and seed
activation. Each must have retained service or no required effect.
Induction over finite terminal derivations shows
that every open or unknown origin sets the root bit. The complete
source check serves every origin of a false bit. The separate control
condition preserves all other uses. Given validated views and NoRoute
results, closure costs `O(V+E+|S|)` per goal. Each DT key publishes once
and upgrades at most once.
[Source-specific proof](lean/proposals/mark-origin-soundness-20261117/OriginService.lean) ·
[Terminal relay proof](lean/proposals/recursive-target-service-20261117/TargetSupport.lean)

## 2. R39/R40 NoRoute proof models

In Section 1, NoRoute discharges one source/observer relation. Use a
read-only model at a forward seal or a reference fixture. Fix the mark,
both occurrences and resolved interfaces at the
same bound carrier. For marking position a and observer position q,
a route requires `writerWord · a = readerWord · q`.

```text
extract(role, boundInterfaces):
    build the value-flow cone between the exact resolved ports
    label identity/copy ε, verified fresh writer stores f, and reader loads f
    include all preserving CFG branches and resolved call alternatives
    if a relevant route, binding, alias or effect is unproved: return Unknown
    use reverse value-flow order for writers and direct order for readers
    emit A→ε at outputs and A→label·B for local edges
    at each invocation A→callee→C, compute the unique C-to-output word v
    omit a call with no path to the output
    if a reaching suffix has a call, a cycle or differing words: return Unknown
    emit A→start(callee)·v for each resolved callee interface

regularNoRoute(writer, reader):                       // R39
    if either grammar is incomplete or nonregular: return Unknown
    compile both grammars A→w or A→u·B to automata, with outer suffixes a and q
    split labels into accessors and include ε closure before each step and at finals
    visit matching-label state pairs from the starts
    return Possible at a joint final, otherwise NoRoute when the queue empties

nestedNoRoute(nested, regular, outer):                 // R40
    if either grammar is incomplete or both are nested: return Unknown
    compile the regular side with its own outer suffix
    seed (A,p,r) for A→w when r ∈ end(p,w)
    for each reached (B,m,n) and rule A→u·B·v:
        add (A,p,r) when m ∈ end(p,u) and r ∈ end(n,v)
    return Possible if (startNested,startRegular,r) can consume outer to a final
    return NoRoute when the cell queue empties
```

Use resolved accessor IDs. In the acyclic suffix cone, set `word(exit)=ε`.
In reverse topological order, set `word(p)` to the common
`edgeLabel · word(next)` over successors that reach the exit.
Validate extraction by induction on native paths and matched returns.
A relevant cleaner, hidden heap route or unsupported effect gives
Unknown. Only a validated NoRoute discharges the relation.

**Proof and work.** A shared word induces a reached product pair or
a nested cell by induction on its derivation. Append the outer word
after the entire derivation, e.g. `g.f · h = g.f.h`. R39 explores at most
`Qw·Qr` pairs after ε compilation. R40 uses at most `M·Q²` cells
and `O(C·Q⁴)` dense cell processing after fixed-word tables, for M
nonterminals, Q regular states and C clauses.
[Regular proof](lean/proposals/branching-field-cycle-20261117/RegularCertificate.lean) ·
[Nested proof](lean/proposals/two-sided-field-cycle-20261117/PairedContext.lean)

## 3. COMPLEX — terminal retirement and field languages

The recorded controls isolate the need for the following proof
conditions in their reference scopes.

| Candidate | Fact trace and disabled control | What suffices in the fixture |
| --- | --- | --- |
| R37/R38 [REC] [LOOP]. Mark `x.f.g.$/T`, then `r=wrap(x,n)`. `wrap(p,0)=p` and `wrap(p,n+1)` returns a fresh object with `f=wrap(p,n)`. | By run-3, `r.f.g.$/T,N` gives `ZERO→NT(id),N`. The cut route renews `ZERO→DT,D` in every later reference pair. Native diagnostic run-15/POLICY. | Source-specific service stops the single-source reference at run-7 and the two-source reference at run-9. R38 guards retirement. NoRoute cannot close the real route. |
| R39 [REC] [LOOP]. Writer `{g,h}*f`, reader `{g,h}*g`. | `z.M/T,D→DT` and the reverse permission recur. Native diagnostic run-9/POLICY. Certificate adapter run-5. | Required-field check below suffices. Reader ending in f instead has the shared word f. |
| R40 [REC]. Writer `g*f`, reader `R=g or g·R or h·R·h`. | `z.M/T,D→DT` and reverse permission recur. Native diagnostic run-9/POLICY. Certificate adapter run-5. | Required-field check still suffices. R39 cannot compile the nested right h. Writer base `h.g.h` yields a shared word. |

```text
must = fields(outerL) ∪ intersection(fields(w) for each L base word w)
may  = fields(outerR) ∪ union(fields of all R base, left and right chunks)
NoRoute if either orientation has a nonempty must − may
```

Require both complete extractions and a base clause on the must side.
Every finite derivation ends at a base and then includes its outer
word. This proves the set test, which costs one scan of the clause
fields. Both negative language fixtures require f on the writer and
exclude it on the reader. They establish no independent need for the
general product or chart in runtime. The alternating-generator
reference keeps its root DT through run-11 with ordinary replies and
stops at run-7 with the source-specific proof.
[Wrapper recurrence](../docs/reports/bidirectional-recursive-target-termination-20261117.md) ·
[Regular controls](../docs/reports/bidirectional-branching-field-termination-20261117.md) ·
[Nested controls](../docs/reports/bidirectional-two-sided-field-search-20261117.md) ·
[Catalogue verification](../docs/reports/bidirectional-termination-fix-validation-20261117.md)

## 4. Examples

| Input | Native handoff | Handoff with candidate rule |
| --- | --- | --- |
| R38. A and B can reach one observer. A supplies `ZERO→NT(id),N`. B uses `ZERO→DT,D`. | Guide `{ZERO→DT,D}`. | Guide `{ZERO→DT,D}`. A's witness cannot serve B's source permission. |

### R37 trace with two observer IDs

Both marking actions and observations are local to root.

```java
void root() {
    Node a = new Node();    // A assigns T at a.g.$.
    observe1(a.g);          // Exact T observation, id-1.
    Node x = new Node();    // B assigns T at x.f.f.f.f.$.
    Node r = x.f.f.f;
    observe2(r);            // CM(r.MAY, T), id-2.
}
```

Forward DATA facts have ZERO origin. The trace omits ordinary
`ZERO→ZERO`. The observer ID identifies the goal in the proof model.

| Run and guide input | Decisive facts and control | Native handoff | Handoff with candidate rule |
| --- | --- | --- | --- |
| run-1, forward K=1. Unrestricted root ZERO. | `a.g.$/T,N→NT(id-1)`. B cuts to `x.f.M/T,D` in the native analyzer and `x.f.NE/T,D` with NE. The reads yield `r.M/T,D→DT` at id-2. | Guide `{ZERO→DT,D}`. Report `{ZERO→NT(id-1),N}`. | Guide `{ZERO→DT,D}`. Report `{ZERO→NT(id-1),N}`. |
| run-2, backward K=1. Guide `{ZERO→DT,D}`, actual ZERO. | Root starts `ZERO→ZERO,N`. Observer id-2 emits reverse `r.M/T,D`. The reverse reads yield `x.f.M/T,D` in the native analyzer and `x.f.NE/T,D` with NE, both matching B's declared position. | `{ZERO→DT,D; permission(B)}`. | `{ZERO→DT,D; permission(B)}`. |
| run-3, forward K=2. Guide `{ZERO→DT,D}`, actual ZERO with `permission(B)`. | Retain `{ZERO→NT(id-1),N}`. B cuts to `x.f.f.M/T,D` in the native analyzer and `x.f.f.NE/T,D` with NE. The reads yield `r.M/T,D→DT`. | Guide `{ZERO→DT,D}`. | Guide `{ZERO→DT,D}` because id-2 remains open. |
| run-4, backward K=3. Guide `{ZERO→DT,D}`, actual ZERO. | Reverse id-2 yields `r.M/T,D`, then `x.f.f.f.M/T,D`. This includes the last f at B. | `{ZERO→DT,D; permission(B)}`. | `{ZERO→DT,D; permission(B)}`. |
| run-5, forward K=4. Guide `{ZERO→DT,D}`, actual ZERO with `permission(B)`. | B produces `x.f.f.f.f.$/T,N`. The reads produce `r.f.$/T,N`. Observer 2 emits `ZERO→NT(id-2),N`. | Guide `∅`. Reports `{ZERO→NT(id-1),N; ZERO→NT(id-2),N}`. | Guide `∅`. Reports `{ZERO→NT(id-1),N; ZERO→NT(id-2),N}`. |

At run-3, removing DT leaves `∅` and stops before run-4 grants
`permission(B)`. In the proof model, an id-1 derivation can contribute
false first. The open id-2 derivation upgrades the same key to true.
Native handoff retains `ZERO→DT,D`.

[Proof checks](lean/proposals/demand-spec-clarification-20261118/README.md) ·
[Comparative audit](demand-refinement-no-loss-audit.md)
