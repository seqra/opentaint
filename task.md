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

We are working on [bidirectional-task.md](bidirectional-task.md)

Now we have a complete spec for the AP (see `spec/ap.md`) and spec for the analyzer (see `spec/analyzer-core.md`) which covers phases 1 and 2.
Now we need to create an implementation proposal documents: for the ap and for the analyzer.
Focus on the implementation details: packages, entities and their interaction.
Provide code snippets. Generally, we should have more code snippets and less text. 
If you need to explain some concept: write a code snippet.
Maximize code sharing, so we can reuse as much as possible from the current analyzer implementation.
Put the specs into `spec/ap-impl.md` and `spec/analyzer-impl.md` wrt the repo root.

Use subagents.