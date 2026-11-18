# R39: regular field-path goal service [REC] [LOOP]

17 November 2026. This extends the
[consolidated proposal](bidirectional-demand-termination-approach-20261115.md).
Follow [the proof guide](../../spec/proof-guide.md). Production is unchanged.
[Counterexample, cold traces and validation](../reports/bidirectional-branching-field-termination-20261117.md).

## 1. Selected change

R38 can close a goal after every possible marking point has a valid retained
NORMAL route. Its base-level upper view cannot reject some impossible field
paths. A recursive writer and reader can renew ZERO/DT forever, although
no exact mark can reach the observer. There is no NORMAL witness to serve.

R39 supplies a **proved NoRoute certificate** for eligible source/observer
pairs. It refines R38's upper view. This is a new terminal-handoff proof
class. A goal can now close without a NORMAL report when every possible
marking origin is proved absent. It does not confirm a report.

| Part | Before | After |
| --- | --- | --- |
| Source/goal service | NORMAL witness, or absence in a complete existing upper view | Also accept a complete regular field-path NoRoute proof |
| Query inputs | Bounded state and existing base-level possible-origin view | Also use complete pure-FLOW region equations from existing method forms, micro-edges, call bindings and CFG ports |
| Root ZERO/DT | Kept for an unserved origin | Omit only when all origins have NORMAL service or NoRoute service and the existing terminal OR certificate is closed |
| DATA, C2/C5, calls, cuts, layers, E/mx/H | Existing rules | Unchanged |

The new query needs complete structural effect equations. It is not an
edge-history-only repetition predicate. A sample of current summaries or
submitted facts does not prove completeness for later refinements.
No JVM type reasoning, rule rewrite, IR rewrite, new tail/mark, evidence on
DATA, or change to the stopping test is selected.

## 2. Eligible regions and word meaning

For an exact full-mark source at field word a, a prefix writer with word w
puts the binding at w·a. A reader consumes word r. An exact observer at q
matches only if:

```text
w · a = r · q
```

All words use actual accessor IDs, including array accessors when supported.
The initial scope is FULL, a concrete EXACT source position and one positive
exact CM observer. Multiple origins require separate complete proofs. Other
source/observer forms remain Unknown unless their word language is proved.
The source word must cover every initial binding for that mark point,
including aliases. A fresh empty unescaped allocation is the simple case.
Do not infer a singleton binding from the configured position alone.
The initial adapter starts at a source outside the two pure-FLOW regions.
An internal marking action needs a separate complete origin slice.
For example, `x.g=x; markT(x); z=x.g` cannot use source word epsilon alone.
A complete alias language is required, or the query stays Unknown.

An eligible writer SCC has neutral relevant input on its recursive call and
only prefix writes on the returned relevant value. An eligible reader SCC
has prefix reads before its recursive call and neutral relevant return.
Account for every base branch, resolved call target, binding and port:

```text
Writer[M] = union(base words)
          | union(prefix · Writer[N])
Reader[M] = union(base words)
          | union(prefix · Reader[N])
```

These equations are regular languages. Direct and mutual recursion can
use the same finite state graph. A loop with prefix writes needs reversed
instruction order in its writer view: writes g then h give prefix h.g.
Reader order stays forward. An already composed literal chunk is not
reversed again. Keep physical block ports and ordinary loop restriction.

The complete route slice must include every route from that marking point
to this observer. A selected pair of normal-return summaries is insufficient.
In particular, a method with no normal return can still reach an internal
observer. Use its actual observer port, or return Unknown. A separate bypass,
new mark assignment, alias path or boundary rule must not disappear.

Reject an unproved shape. This first compiler does not certify mixed
read/write SCCs, a call with field changes on both sides, nonlinear recursive
word equations, multiple calls on one relevant region route without a proved
finite shared representation, general ND/rule/alias/static effects, GROUP, or unresolved
bodies. Cross-owner empty-word recursion also needs a proved epsilon
elimination; the prototype returns Unknown. Identity base branches are legal.
No existing successful analysis is disabled by this eligibility test.

## 3. Finite certificate

Compile each equation to a finite word automaton. A clause with a literal
chunk and a callee has a chunk path to that callee's state. A base clause has
a chunk path to an accepting state. An empty base makes its owner accepting.
Share control states. Do not enumerate all CFG branch combinations or all
field paths. The reference clause validator checks every supplied clause
against the compiled paths. This validates grammar-to-automaton coverage;
code-to-complete-grammar coverage remains an explicit adapter obligation.

Append a to writer base words and q to reader base words. This represents
all source and observer positions without unfolding recursion. It is a view
of finite code/rule descriptors, not an over-limit emitted AP fact.

```text
sourceServed(s, goal):
    if retainedValidNORMALWitness(s, goal): return true       // R38
    slice = borrowCompletePureFLOWRegions(s, goal)
    if slice is Unknown: return false
    W = compileAndValidateAllWriterClauses(slice, sourceWord(s))
    R = compileAndValidateAllReaderClauses(slice, observerWord(goal))
    if W or R is Unknown: return false

    queue = [(W.start, R.start)]
    seen = {queue.first}
    while queue is not empty:
        (u, v) = queue.removeFirst()
        if u is W.final and v is R.final: return false       // possible route
        for W edge u -f-> u2:
            for R edge v -f-> v2:
                if seen.add((u2, v2)): queue.addLast((u2, v2))
    check start belongs to seen
    check every product edge out of seen ends in seen
    check no pair of accepting states belongs to seen
    return checksPassed                                    // NoRoute

atExistingJoinedSeal(goal):
    if completeMarkingCatalogue(goal) and all s: sourceServed(s, goal):
        retain ClosedGoal(goal) only
    discard temporary query state

onForwardStart(): freeze previously proved ClosedGoal values
atForwardHandoff(): use the unchanged R37/R38 terminal-OR/root-ZERO/DT filter
```

A possible word does not create a fact, source permission or NORMAL report.
It only prevents NoRoute pruning. Unknown also retains the original demand.
A source that has not executed is not automatically absent. A cut fact is
not evidence that the uncut field suffix is impossible.

Keep the goal key tied to its full mark, observer position/rule, source
catalogue and frozen graph/rule version. Another observer coordinate or
mark cannot borrow the certificate. NORMAL report IDs remain separate. If one report ID has several semantic
observer predicates, all must be covered. A proof for one compiled occurrence
cannot close another; an incomplete predicate map stays Unknown.
A mixed anonymous Target keeps the whole row when any origin is unserved.
Late terminal bit upgrades, current-run closure, backward behavior, all DATA
handoff rows, saved NORMAL records and source permissions stay unchanged.
Run-1 completes normally. A certificate established at its seal can enter
the frozen set for run-3; it cannot retroactively cancel run-1 work.

## 4. Soundness

For every valid exact relation in the eligible scope, complete region
extraction gives writer and reader derivations with the same field word.
The finite clause validator maps each derivation to an accepting automaton
path. Equal words give a path through the product to an accepting pair.
The checked closed product set therefore cannot certify that route empty.
This proof is constructive and covers arbitrary word lengths and recursion
depths, not just the finite search bounds.

Thus each NoRoute origin has no required source/full-mark/observer relation.
Each NORMAL-served origin keeps R38's valid witness. The existing terminal
OR invariant then permits omission only when every relayed goal is served.
No valid relation depends solely on the removed root permission.
All other terminal keys and all DATA remain under their current policies.

A missing branch can invalidate this proof. So can an omitted caller,
alias, rule, exceptional port or internal observation. The validator checks
all supplied clauses; it cannot prove that an incomplete clause list is the
whole program. The adapter must establish that separately. Unknown is the
required result when it cannot do so. General native obligations G1–G4 remain
open; a model theorem does not certify arbitrary native extraction.

## 5. Bounds and consequences

Let Qw,Qr be automaton state counts and Ew,Er their edge counts. They depend
on finite control/effect descriptions, not the run field limit or recursion
depth. Use a lazy product and index edges by field. At most Qw·Qr pairs enter
the queue. Product edge visits are bounded by the matching-symbol edge pairs;
with the complete product, at most Ew·Er pairs need comparison. Peak query
storage is O(Qw·Qr+Ew+Er). It is polynomial extra proof work, not a measured
whole-project speedup. Do not store expanded field words or a persistent
product graph per DATA edge.

Query one origin/goal slice at a time. Reuse immutable region automata and
cache the final ClosedGoal with its graph/rule version. Do not eagerly bind
all rules for a new census. Incomplete or unsupported queries keep guidance;
this is not a universal convergence theorem.

No new DATA initials, summaries, subscriptions, field-path combinations or
cap exceptions are added. Global, FL(Dc)+1 and FL(Dp)+1 limits remain mandatory.
The concrete counterexample uses two two-state automata; only two of the
four product pairs are reached. Its unchanged native diagnostic reaches
run-9/POLICY with 90 reader `SummaryStore.all()` row groups (not 90 unique facts). The adapter finishes
naturally at run-5. Positive short-word cases keep their NORMAL observation
and finish at run-7. Existing two-loop controls keep natural run-5.
[Proof sources and validation details](../../spec/lean/proposals/branching-field-cycle-20261117/README.md).
