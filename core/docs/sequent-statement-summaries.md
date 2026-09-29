# Sequent flow function via per-statement summaries

Status: approved design, 2026-09-29. Branch `saloed/sequent-summaries` (from `origin/main` ce24bbbb9).

## 1. Goal

Restructure the JVM sequent flow function (`JIRMethodSequentFlowFunction`) as

1. relevance check,
2. rules before the statement (reserved, not implemented),
3. fact transfer,
4. rules after the statement (method-exit source and sink rules).

The transfer is no longer computed per fact. Each statement is translated once into a
per-statement summary: a set of edges `InitialFactAp -> InitialFactAp`. A fact is propagated by
matching it against the edges exactly like a method summary edge is applied to a caller fact:
delta against the edge source, then concat of the delta onto the edge target. The `I -> I` form keeps
the summary trivially reversible (future preconditions and backward analysis swap `from` and `to`).

Success criterion: the forward suites keep their `origin/main` results - JVM `core/src/test`,
`opentaint-java-querylang`, `opentaint-dataflow-core:check`.

## 2. Exit handling

Method exits are the boundary instructions added by `JMethodBoundaryInstFeature`
(`JMethodExitNormalInst`, `JMethodExitExceptionalInst`).

- `return x` is a pure transfer `x -> Return`; `throw x` is a pure transfer `x -> Exception`.
  No rules are applied on `JIRReturnInst` / `JIRThrowInst`.
- `JMethodExitNormalInst` / `JMethodExitExceptionalInst`: identity transfer followed by the
  exit rules with method result `Return` / `Exception`: exit source rules, the exit sink worklist,
  `dropFinalFacts` (ClassStatic drop after an exit sink), `dropArgumentsLocalTaintMarks`.
  Unconditional exit sources (zero fact) are applied on `JMethodExitNormalInst`.
- Generated methods (`JIRLambdaMethod`, `OpentaintLambdaProxyMethod`, `SpringGeneratedMethod`)
  override `instList` and never pass through the `JIRInstExtFeature` pipeline, so today they have
  no boundary instructions (measured: 170 `JIRLambdaMethod` graphs in the Java/Kotlin reachability
  tests). Their `instList` lazily applies `JMethodBoundaryInstFeature.transformInstList` to the
  built list. No other transformer is applied to generated code.
- Consumers of the exit statement:
  - `JIRMethodSequentPrecondition` applies the exit source precondition on the exit boundary
    instructions; on `return` / `throw` it only rebases `Return` / `Exception` to the returned value.
    The precondition is otherwise unchanged (reversed-summary preconditions are a follow-up).
  - `VulnerabilityChecker` treats an exit boundary instruction as a final trace node (it has no
    successors).
  - SARIF resolves the location of a vulnerability reported on an exit boundary instruction from
    the preceding `return` / `throw` of its trace, as trace paths already do.
  - `JIRAnalysisManager.isTraceRequiredInstruction` follows the rule application point.

## 3. Per-statement summary

```
class JIRStatementSummary(
    val edges: Map<AccessPathBase, List<Edge>>,     // keyed by from.base
    val typeFilters: Map<AccessPathBase, List<JIRType>>,
) { data class Edge(val from: InitialFactAp, val to: InitialFactAp?) }
```

A base absent from `edges` is not touched by the statement. A touched base without an edge from some
part of its value loses that part (kill). All edges read the values before the statement, so
self-referencing statements (`a.x = a`) need no auxiliary base.

Notation: `y` is `mostAbstractInitialAp(y)` (`y.*`, empty exclusions), `y/{f}` is `y.*` excluding
`f`, `y.f` is `y.f.*`, `[e]` is `ElementAccessor`, `<C>.C` is `ClassStatic` with `ClassStaticAccessor`.

| Statement | Edges |
|---|---|
| `x = y`, `x = (T) y`, `x = a op b` | per operand `o`: `o -> o`, `o -> x` |
| `x = y.f` (`y != x`) | `y/{f} -> y`, `y.f -> y.f`, `y.f -> x`, `y/{f} -> A` for every alias `A` of `y` |
| `x = x.f` | composition of `tmp = x.f` and `x = tmp`: `x/{f} -> ⊥`, `x.f -> x` (+ `x/{f} -> A`) |
| `x = C.f` | `<C>/{C} -> <C>`, `<C>.C/{f} -> <C>.C`, `<C>.C.f -> <C>.C.f`, `<C>.C.f -> x` |
| `x = y[i]` | as `x = y.f` with `f = [e]` (`x = x[i]` by composition) |
| `y.f = x` | `y/{f} -> y`, `x -> x`, `x -> y.f`, `y/{f} -> A`, `x -> A.f` for every alias `A` of `y` |
| `y[i] = x` | `y -> y`, `x -> x`, `x -> y.[e]`, `x -> A.[e]` for every alias `A` of `y` |
| `C.f = x` | `<C>/{C} -> <C>`, `<C>.C/{f} -> <C>.C`, `x -> x`, `x -> <C>.C.f` |
| `return x` / `throw x` | `x -> x`, `x -> Return` / `x -> Exception` |
| `x = <other>` (new, constant, ...) | none from `x` (kill) |
| other statements | no edges |

The written local `x` gets no identity edge (`x = x` and `x = x op y` keep `x -> x` from the
operand). `A` stands for an alias path of `y` at the statement (`findAlias(base, statement)`,
local bases only); alias edges are plain edges.

**Kill edges.** `from -> ⊥` kills the matched part but keeps the refinement carried by `from`'s
exclusions. It appears only through composition.

**Composition.** A statement whose read target is its own instance (`x = x.f`, `x = x[i]`) is the
composition `S2 ∘ S1` of `S1 = (tmp = x.f)` and `S2 = (x = tmp)` with the temporary base eliminated.
For an `S1` edge `a -> b`:
- `b = ⊥` or `b.base` not touched by `S2`: `a -> b` is kept.
- otherwise, for every `S2` edge `c -> d` with `c.base == b.base`:
  - `c` is a prefix of `b` (`b = c.r`, `r` not starting with an accessor excluded by `c`):
    `a' -> d.r`, where `a' = a` if `r` is non-empty, else `a` with `c`'s exclusions added;
  - `b` is a strict prefix of `c` (`c = b.r`, `r` not starting with an accessor excluded by `a`):
    `a.r -> d` with `c`'s exclusions;
  - if no `S2` edge matches and `a` has exclusions: `a -> ⊥`.
- `S2` edges from bases `S1` does not touch are kept; edges from or to the temporary base are dropped.

Example: `S1 = {x/{f} -> x, x.f -> x.f, x.f -> tmp}`, `S2 = {tmp -> tmp, tmp -> x}` with `x` killed
gives `{x/{f} -> ⊥, x.f -> x}`. `x/{f} -> ⊥` is what makes an abstract `x.*` request `x.f.*`
(the delta of `x.*` against `x.f.*` is empty), exactly as the two separate statements do.

`typeFilters` carry the declared-type filtering of today's `filterFactBaseType`: for every access
of the statement, the operand base maps to the static types (cast type, local type, array type,
field instance type, field enclosing type). An incoming fact on that base is filtered with
`factTypeChecker.filterFactByLocalType` before edge matching; a rejected fact produces nothing.

## 4. Propagation

For an incoming fact `F` (Z2F, F2F, NDF2F):

1. Relevance: a fact whose base is not in `edges` is irrelevant to the transfer. On a statement
   without after-rules it yields `Unchanged`; on an exit boundary instruction it yields `Unchanged`
   when the exit rules leave it as is (current behaviour). `Unchanged` is produced only for
   irrelevant facts.
2. Apply `typeFilters[F.base]`.
3. For each edge with `from.base == F.base`, for each effect of
   `MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge(F, from)`:
   - `SummaryApRefinement(delta)`: `R = to.concat(typeChecker, delta)` with `F.exclusions`;
     emit with the unchanged initial fact. Nothing for a kill edge.
   - `SummaryExclusionRefinement(delta, ex)`: `R = to.concat(typeChecker, delta)` with `ex`;
     emit `FactToFact(initial.replaceExclusions(ex), R)` for F2F. For Z2F / NDF2F `ex` is
     `Universe` and the edge kind is kept. For a kill edge on F2F: emit
     `SideEffectRequirement(initial.replaceExclusions(ex))` when that differs from `initial`
     (refinement without a fact; the same sequent the JVM call summary handler emits for refined
     summaries); nothing otherwise.
   Results are emitted even when equal to `F` (no `Unchanged`).
4. After-rules on the exit boundary instructions (section 2) run on the transferred facts.

Zero-to-zero keeps its current content: type-info facts for lambda `new`, static-field
unconditional sources, unconditional exit sources (now on the normal exit).

## 5. `InitialFactAp.concat(FinalFactAp.Delta)`

New operation `InitialFactAp.concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp?`.

- Tree (`AccessPath` + `AccessTree`): empty delta -> abstract node built from the path accessors
  (`createAbstractNodeFromAccessors`) annotated with the delta deep exclusion; node delta -> the
  path accessors prepended to the delta node (`concatToLeafAbstractNodes` of the abstract path node,
  so type filtering and access limits match `AccessTree.concat`).
- Automata: `AccessGraphFinalFactAp(base, initial.access, exclusions).concat(typeChecker, delta)`.
- Cactus: built through `createAbstractNodeFromAp` + `AccessCactus.concat` when the manager is
  reachable, otherwise unsupported (the cactus initial fact is a stub).

## 6. Caching

`JIRMethodAnalysisContext` gets `cachedSequentFF(stmtIdx, generateTrace)` next to `cachedCallFF`,
reset in `resetAnalysisCache` (the `ApManager` changes between phases). `generateTrace` is part of the
key because it changes the Z2F handling of exit rules. The flow function computes its summary
with a synchronized `lazy`; the summary is immutable, so trace-resolution workers may share it.
