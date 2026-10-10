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

Read project memory from the previous session: `~/.claude/projects/-drive-testcomp-opentaint-go-rules-opentaint-w3/`

Now we have a compete spec for the AP and analyzer (see spec/). 
The current step is: finalize the implementation proposal.
Here is the checklist:
1) Precisely analyze the demand edge handling, abstraction and summary emission/reduction. These operations must match the specification precisely  
2) All other operations also should match the spec. Review them.
3) The implementation proposal shouldn't use staled facts or rules. Review that all used rules are actual
If we found a major gap or misalignment -- aks me for the decision on how to fix it. I will specify the correct behavior.

Use subagents.