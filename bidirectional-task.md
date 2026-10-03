The new analysis approach idea: forward/bacward collaboration.
The notation: forward-i means forward analysis with field limit i, same for backward-i.
We should iterate forward-1, backward-2, forward-3, ... until we have no demand to continue.

Section 1. Fact representation and instruction handling.
The fact is represented as a tuple: (base, concrete field tree, field prefix kind (* abstract / [any] / $ exact), field exclusion, taint mark)
We can use AccessTree/AccessPath to represent field tree of a fnial/initial fact correspondingly.
A field tree my contains static, field or element accessors.
A field exclusion maybe epmty/conncrete/unverse. Every non-abstract field prefix must use the Empty exclusion.
The taint mark may be abstract (*) or concrete.
The field ecxclusion contains only excluded fields.

Consider the statements:
a = b --> simple fact rebase

a = b.f
1) (x, .f, *, E, *) -> (b, .f, *, E, *) : propagated as expected, resulting in (a, ., *, E, *)
2) (x, ., *, E, *) -> (b, ., *, E, *) : propagated as an incomplete edge resulting in (x, ., *, {}, *) -> (a, ., [any], {}, *)
3) (x, ., *, {f}, *) -> (b, ., *, {f}, *) : propagated as expected, nothing happens since f is excluded
4) (x, ., [any], {}, *) -> (b, ., [any], {}, *) : propagated as expected, resulting in (a, ., [any], {}, *)
5) (x, ., $, E, *) -> (b, ., $, E, *) : dropped, since the exact field chain is known and don't contain f

Note that we have no exclusion set updates or refinement requests on field read

a.f = b
1) (x, .g, *, E, *) -> (b, .g, *, E, *): results in  (a, .f.g, *, E, *) if the limit allows it, or if we have a bound of 1 collapsed to: (a, .f, [any], {}, *)
2) ... -> (a, .f, *, E, *) : dropped wrt the strong update rules (nothing happens in a case of weak update, e.g. array write)
3) ... -> (a, ., *, E, *) : propagated with exclusion set updated (a, ., *, E U {f}, *). Exclusion set is updated on a field write only. No refinement request happens here, exclusion set update only

Section 2. Rule and taint mark handling
Important: for the final fact, if the field chain is abstract, then the taint mark must be also abstract. It is allowed for the initial fact, to have abstract field chain with non-abstract mark.

x = source()
Simple, handled as expected resulting in (x, ., $, {}, T).

sink(x) where sink search for taint mark T
1) (x, ., $, {}, T) : works as expected -> sink triggered
2) (x, .f, $, {}, T) : works as expected -> sink not triggered
3) (x, ., [any], {}, T) : sink triggered
4) (x, ., *, {}, *) : sink not triggered. Exclusion set not updated. Instead, we emit a request for the taint mark T. The request is handled by the current method abstraction (see section 4) or propagated to the caller.

Section 3. Summary edges

We should distinguish 2 kind of summary edges: complete and demand. If the edge has no [any] it is complete, otherwise the edge is a demand edge.
The complete edges must be persisted and reused accross all runs (forward and backward). For example, the complete edge obtained at forward-2, can be used in backward-7
The complete edge can be reversed. So, if we have a forward edge (x, ., *, {}, *) -> (y, ., *, {}, *) we can obtain a corresponding complete backward edge (y, ., *, {}, *) -> (x, ., *, {}, *).

The demand edges must be stored separately. During the analysis-i (e.g. forward-3) this edges is used as a any other edge. However, the demand edges can't be reversed and shouldn't be persisted. The demand edges are used by the analysis-i to understand the demand from analysis-(i-1). The demand edges from the previous analysis iteration are used for the abstraction only (see section 4).

Summary edge application.
Summary edges are applied as usual using the delta-concat approach.
The fact in the caller context must be strong enough to satisfy the summary edge premise. So, if we have [any] in the premise, we should have [any] in the caller context.

Section 4. Abstraction

The abstraction is guided by the demand summaries from the previous analysis iteration. So, the abstraction for method M_forward in forward-6 is guided by the demand edges from M_backward in backward-5.
If we have an added fact with base x, and we have no complete summaries for the base x -> the most abstract fact is emitted (x, ., *, {}, *).
We have no fact refinement mechanism (de-abstraction). Instead, we emmit facts analyzing the demand.
If we have a demand (x, .f, [any], {}, *) and we have a corresponding added fact like (x, .f.g, *, {}, *) we emmit the fact.
The demand is computed as a set of all demmand summary edge finals.

The only special mechanic is a mark request handling. If we have a request for the mark T with the initial fact (x, .f, *, {}, *) we should consider the added facts. If we have an added fact with the requested mark exactly matching the requested one like (x, .f, $, {}, T) we emmit the (x, .f, $, {}, T) fact. Otherwise, if we have fact matching the requested not exactly like (x, .f.g.h, $, {}, T) we should emmit the (x, .f, *, {}, T) -> (x, .f, [any], {}, T).
If the request was not answered, we should propagate request to the callers.

Section 5. Notes and references.
1) We don't need fact iterative-deepening (as we have right now) (fact delay wrt the fact depth). The deepening is done by the analysis field limit.
2) We have a tree field limit implemetation in the saloed/any-field-limit. Use it for the reference.
3) We have backward analysis impl in saloed/backward-main. Use it for the reference.

The expected implementation phases are:
1) New AP with all required storages
2) New analyzer. We can reuse general scheduling structures like TaintAnalysisUnitRunnerManager or TaintAnalysisUnitRunner. But we should create a new replacement for the NormalMethodAnalyzer. Include forward-backward communication.
3) New TaintAnalyzer. It should run prescan using the current analyzer core. After the prescan we have all lambda resolved and a reduced rule set. Then we should run our new analyzer with forward/backward iterations. We can skip trace resolution during this phase.
4) Benchmarking on real projects and test. All tests should pass (wrt the trace resolution), the performance on real projects must be comparable to the current analyzer from origin/main. The discovered vulns must match exactly. We should fix all discovered isssues during this phase.
5) Add trace resolution based on the latest forward iteration. Use same precondition approach.
