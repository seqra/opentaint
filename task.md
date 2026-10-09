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

We need to extend the analyzer-core spec. Currently, we have no clear termination criteria.
We should focus on complete edges. 
The obvious approach: the forward run has no demand edges -> terminate. 
The deeper approach: we should try to exclude methods without demand edges after forward from the analysis. 
So, we reduce the search space on each iteration.
The reason is: if the vuln was confirmed on the iteration i, then it will be confirmed on the all iterations j > i.
Another key observation: if the method has no forward demand edges at iteration i, then it will have no demanand edges on all iterations j > i, so the method is complete

Finally, we will have a simple time budget, for the entire process.
But we should design an approach, to efficiently localize the remaining need-to-analzye code.
If we have a good localization on practice, it will be easer to design a practical stop strategies later.

Use subagents.