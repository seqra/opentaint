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

We need to extend the AP spec. Currently, we have 3 possible fact tail kinds: *, $ and [any].
This is not enough, since we can't distinguish the demand edges and the [any] sources.
The proposed soultion: add one more tail kind -- [any-taint].
It works as [any] on read, but without promoting the edge layer. Therefore, we have a new complete edge kind: normal layer with [any-taint] tail.
The [any-taint] can be promoted to [any], if the field write exceeed the limit.
The [any-taint] shouldn't be used in the premise. Also, the [any-taint] shouldn't be used with the * at mark position. 
We may assume that the [any-taint] tail can be used for the concrete taint edge conlcusion (a source rule application result). 

Extend the spec. Write all required proofs. Specify all required parts: the demand, the abstraction and summary edge application.

Use subagents.