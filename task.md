Follow a proof-first, CEGAR-style, test-driven development approach
for all the work, using Lean as the formal model. First, model all the
necessary parts in Lean with the invariants proved. Then design a formal model of
the feature and prove its invariants. Then use TDD to develop the feature.
Write only constructive formal models: no classical axioms, and every existence
proof must yield an executable witness. Refine the abstraction if it is
not complete, but the abstraction should be sound (at least within the
restricted scope in effect at any given moment). Use the formal model to
find bugs in the design. Use the formal model to distinguish the concept from the
optimization, and prove that they are functionally equivalent but that the
optimization has a different complexity, or a different complexity over some practical
scope. The core idea is for the implementation to be sound and complete
within some scope. The wider the scope the better, but stay practical: working in
real-world scenarios is crucial and is the guideline-quality gate.

Use ASD-STE100 Simplified Technical English language

Preface: read all related memories for this and all projects from `../opentaint*`

We plan to redesign alias analysis (let's focus on JVM for now).

Currently we use a usual congruence closure to handle alias relations and fields 
This is an efficient representation for the alias handling 
However, we see that we should preserve the assign direction 

Use directed graph in alias analysis

If(*) a = x else a = y
a -> x, a -> y

The crucial part is .f handling 
For example, after a.f = z, x.f and y.f both aliasing z
After the a is reassigned we don't have a relation between x and y anymore, but x.f and y.f still both aliasing z

Therefore, we need something like congruence closure to remain efficient, but with direction preservation

The main purpose: improve alias analysis precision.
For example, now the alias request for `x` returns `{x, a, y}`. But the more precise analysis (e.g. directed) can return the more precise `{x, a}`.

Write a complete design proposal for the new analysis. 
Use subagents.
