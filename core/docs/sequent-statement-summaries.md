# Sequent flow function via per-statement summaries

Status: implemented, 2026-09-29. Branch `saloed/sequent-summaries` (from `origin/main` ce24bbbb9), final commit f94be0921.

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
    On assignments, `return` and `throw` it uses the reversed statement summary (section 5a).
  - `VulnerabilityChecker` treats an exit boundary instruction as a final trace node (it has no
    successors).
  - SARIF treats an exit boundary instruction as a generated location and resolves it to the last
    `return` / `throw` of the relevant trace locations, falling back to the method's last
    `return` / `throw`, as trace paths already do.
  - `JIRAnalysisManager.isTraceRequiredInstruction` follows the rule application point.

## 3. Per-statement summary

```
class JIRStatementSummary(val transfers: Array<BaseTransfer>) {
    data class Edge(val from: InitialFactAp, val to: InitialFactAp?)
    class BaseTransfer(val base: AccessPathBase, val edges: Array<Edge>, val typeFilters: Array<JIRType>)
    fun find(base: AccessPathBase): BaseTransfer?
}
```

A statement touches one to three bases, so the summary is one `BaseTransfer` per touched base
(edges from that base and its type filters) found by a linear scan; no maps or linked collections.
A base without a `BaseTransfer` is not touched by the statement. A touched base without an edge from some
part of its value loses that part (kill). All edges read the values before the statement, so
self-referencing statements (`a.x = a`) need no auxiliary base.

Notation: `y` is `mostAbstractInitialAp(y)` (`y.*`, empty exclusions), `y/{f}` is `y.*` excluding
`f`, `y.f` is `y.f.*`, `[e]` is `ElementAccessor`, `<C>.C` is `ClassStatic` with `ClassStaticAccessor`.

| Statement | Edges |
|---|---|
| `x = y`, `x = (T) y`, `x = a op b` | per operand `o`: `o -> o`, `o -> x` |
| `x = y.f` (`y != x`) | `y/{f} -> y`, `y.f -> y.f`, `y.f -> x`, `A -> A`, `y/{f} -> A` for every alias `A` of `y` not based on `x` |
| `x = x.f` | `x/{f} -> ⊥`, `x.f -> x`, `A -> A`, `x/{f} -> A` for every alias `A` of `x` |
| `x = C.f` | `<C>/{C} -> <C>`, `<C>.C/{f} -> <C>.C`, `<C>.C.f -> <C>.C.f`, `<C>.C.f -> x` |
| `x = y[i]` | as `x = y.f` with `f = [e]` (`x = x[i]` as `x = x.f`) |
| `y.f = x` | `y/{f} -> y`, `x -> x`, `x -> y.f`, `A -> A`, `y/{f} -> A`, `x -> A.f` for every alias `A` of `y` |
| `y[i] = x` | `y -> y`, `x -> x`, `x -> y.[e]`, `x -> A.[e]` for every alias `A` of `y` |
| `C.f = x` | `<C>/{C} -> <C>`, `<C>.C/{f} -> <C>.C`, `x -> x`, `x -> <C>.C.f` |
| `return x` / `throw x` | `x -> x`, `x -> Return` / `x -> Exception` |
| `x = <other>` (new, constant, ...) | none from `x` (kill) |
| other statements | no edges |

The written local `x` gets no identity edge (`x = x` and `x = x op y` keep `x -> x` from the
operand). `A` stands for an alias path of `y` at the statement (`findAlias(base, statement)`,
local bases only); alias edges are plain edges.

**Kill edges.** `from -> ⊥` kills the matched part but keeps the refinement carried by `from`'s
exclusions. It appears only for a read whose target is its own instance (`x = x.f`, `x = x[i]`):
the old `x` is overwritten, so nothing of it survives except `x.f -> x`, yet `x/{f} -> ⊥` is what
makes an abstract `x.*` request `x.f.*` (the delta of `x.*` against `x.f.*` is empty). This is the
same result as the two statements `tmp = x.f; x = tmp`.

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
2. Apply the type filters of `F.base`.
3. For each edge with `from.base == F.base`, for each effect of
   `MethodSummaryEdgeApplicationUtils.tryApplySummaryEdge(F, from)`:
   - `SummaryApRefinement(delta)`: emit `R = to.concat(typeChecker, delta)` with `F.exclusions`.
     Nothing for a kill edge.
   - `SummaryExclusionRefinement(delta, ex)`: emit `R = to.concat(typeChecker, delta)` with `ex`.
     For a kill edge on F2F: emit
     `SideEffectRequirement(initial.replaceExclusions(ex))` when that differs from `initial`
     (refinement without a fact; the same sequent the JVM call summary handler emits for refined
     summaries); nothing otherwise.
   Results are emitted even when equal to `F` (no `Unchanged`).
   Emitting a fact `R` (transfer and exit rules alike): on F2F the initial fact takes `R`'s
   exclusions, `FactToFact(initial.replaceExclusions(R.exclusions), R)`, so initial and final
   exclusions always match; an `R` with `Universe` exclusions (a rule-created fact independent of the
   initial fact) is emitted as `ZeroToFact(R)`. Z2F / NDF2F only ever emit `Universe` facts (checked)
   and keep their edge kind.
4. After-rules on the exit boundary instructions (section 2) run on the transferred facts.

Zero-to-zero keeps its current content: type-info facts for lambda `new`, static-field
unconditional sources, unconditional exit sources (now on the normal exit).

## 5. `InitialFactAp.concat(FinalFactAp.Delta)`

New operation `InitialFactAp.concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp?`.

- Tree (`AccessPath` + `AccessTree`): empty delta -> abstract node built from the path accessors
  (`createAbstractNodeFromAccessors`) annotated with the delta deep exclusion; node delta -> the
  path accessors prepended to the delta node one by one (`AccessNode.addParent`, the operation
  behind `AccessTree.prependAccessor`, so access limits and normalization match prepend).
- Automata: `AccessGraphFinalFactAp(base, initial.access, exclusions).concat(typeChecker, delta)`.
- Cactus: unsupported. The cactus initial fact is a stub, so the JVM sequent flow function cannot
  run in Cactus mode.

## 5a. Preconditions from reversed summaries

`JIRStatementSummary.reversed()` swaps every forward edge `from -> to` into `to' -> from'`, where
`to'` is `to` with `from`'s exclusions (they describe the matched part of the value) and `from'` is
`from` without exclusions; kill edges are dropped. It is a pure swap because the forward summary is
closed: every edge target is a touched base. Alias targets are made touched by an identity edge
`A -> A` (their facts survive the statement, now as explicit edges instead of `Unchanged`). A base
the statement does not touch has no entry. The precondition uses `build(...).reversed()`.

`JIRMethodSequentPrecondition` computes the preconditions of an initial fact `q` as
`to'.concat(d)` with `q`'s exclusions for every reversed edge and every
`d in q.delta(from')`. The new `InitialFactAp.delta(other: InitialFactAp): List<InitialFactAp.Delta>`
returns the suffix of this fact after `other`'s path, filtered by `other`'s exclusions (tree: path
walk; automata: `AccessGraph.delta`; cactus: unsupported). An untouched base, or a result equal to
`[q]`, is `Unchanged`; a touched base without a matching edge has no precondition (kill).

## 6. Caching

`JIRMethodAnalysisContext` gets `cachedSequentFF(stmtIdx, generateTrace)` next to `cachedCallFF`,
reset in `resetAnalysisCache` (the `ApManager` changes between phases). `generateTrace` is part of the
key because it changes the Z2F handling of exit rules. The flow function computes its summary
with a synchronized `lazy`; the summary is immutable, so trace-resolution workers may share it.

## 7. Implementation notes

Accepted deviations/decisions from the design above:

1. Exit precondition: the queried fact at an exit boundary yields `Unchanged` plus exit-source
   preconditions; the identity from `preconditionForFact` is only used by the recursive conditional
   exit source (literal identity made SARIF show `return` twice).
2. Exit rules keep the condition-reader refinement for facts unchanged by the rules (emitted
   through the refinement path instead of `Unchanged`).
3. `isTraceRequiredInstruction` = `JIRReturnInst || JMethodExitNormalInst`.
4. A kill edge refinement is emitted as `SideEffectRequirement` (user decision).
5. Generated methods (`JIRLambdaMethod`, `OpentaintLambdaProxyMethod`, `SpringGeneratedMethod`)
   apply `JMethodBoundaryInstFeature` lazily in `instList`.
6. javac with kept local names never emits `x = x.f` on one local; the self-read case is
   unit-tested on a constructed instruction.
