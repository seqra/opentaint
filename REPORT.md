# Holes in the implementation proposals and the spec (review of 2026-10-08)

Scope: `spec/ap-impl.md` (Part I, Part II) and `spec/analyzer-impl.md` against `spec/ap.md`, `spec/interpreter.md`,
`spec/analyzer-core.md`. Method: 8 review agents (Part I ops, Part II interpreter, analyzer core, cross-document
interfaces, reuse of today's code, run-1 scenarios, run-sequence scenarios, the normative spec itself) gave 80 raw
findings. 4 adversarial agents re-derived every BLOCKER/MAJOR finding (and several MINOR ones) from the documents and
today's code. After de-duplication: 10 holes that need a decision (A: H1–H10), 11 verified proposal holes (B:
H11–H21), 12 single-reviewer MINOR items (H22), 11 spec-text holes (C), 5 refuted findings (D). Raw files: `p1-ops.md`, `p2-interp.md`, `an-core.md`, `xdoc.md`, `reuse.md`, `scen-fwd.md`, `scen-multi.md`,
`spec-internal.md`; verification: `verify-V1.md` .. `verify-V4.md` (same folder).

Ids: `P1`=p1-ops, `P2`=p2-interp, `AN`=an-core, `XD`=xdoc, `RU`=reuse, `SF`=scen-fwd, `SM`=scen-multi,
`SP`=spec-internal. `P:` = ap-impl.md line, `A:` = analyzer-impl.md line.

---

## A. Holes that need a decision (the spec does not decide; the fill changes the findings)

### H1 [MAJOR, CONFIRMED] The summary rewriter contradicts D20 (SP-2)
* interpreter.md §5.2 (int:790-796): the rewriter acts for every user rule "whose condition is not statically false".
  D20 (int:875): a cleaner with an undecided mark literal never acts. D23 (int:878): the rewriter acts on every result,
  the default identity too. Together: every CONDITIONAL user cleaner ALWAYS cleans at its positions.
* Example: `RemoveMark(T, Argument(0)) if ContainsMark(Argument(1), RAW)` on an unresolved `lib.m(a, b)` with a clean `b`:
  step 5.1 does not act (D20), the default identity goes through the rewriter (D23), and `a` loses `T`. Today `a` keeps
  `T`. Frequent: every Semgrep-generated rule is user-defined and its cleaners carry a state-mark literal.
* Options: (a, recommended) the rewriter is an explicit exception to D20; list the FN in int §0.1. (b) the rewriter
  also obeys D20: every generated cleaner becomes inert (many new FPs). (c) the rewriter acts only when the only mark
  literal is `ContainsMark(P, T)` at its own action position and mark (conflicts with the example at int:509-510).

### H2 [MAJOR, PLAUSIBLE] End facts: the backward run makes an unguarded forward source (AN-1, SP-3, SP-15)
* The reversed end-fact edge has no guard (int:607-608, ac:313-314). In a backward run a requirement on the end-fact
  target reaches the zero fact with no trigger: a normal backward REACH `{jb} → zero`. R1 persists it
  (P:2384-2393); R3 reverses it into the forward record `zero → jb` (P:2332); in run n+2 `replayRecords` applies it
  as EXACT to the zero fact of every caller (A:1430, :1451-1454). No source seed filters records.
* Example: `M(a){ sink(a); return a; }` (sink has the end fact `AssignMark(T2, Argument(0))`), no caller passes `T`;
  `c1(){ r = M(clean()); if (k) r = srcT2(); sink2(r); }` (real); `c2(){ r = M(clean()); sink2(r); }`. Run 2 seeds
  `c1.sink2`; the requirement enters `M`; the reversed end fact gives `{ret.$ (T2)} → zero`, persisted. Run 3: `c2`
  gets `r.$ (T2)` on `{zero}`, normal layer: a CONFIRMED false positive that run 1 does not have.
* Related: the forward end fact is a `{zero}` edge (as today, `CallToReturnZFact`), so it is context-insensitive and
  reaches every caller; S14/R1 call its records exact, and the Lean model has no end facts (SP-15). The stage model of
  analyzer-core §4.5 cannot compute end facts at all (input, guard, layer undefined; SP-3); both proposals use
  "apply the stage to `Reach.of(layer)` of the trigger".
* Options: (a, recommended) the result of a reversed end-fact edge is DEMAND (ap §2.2 gets the row; R1 drops it, and the
  caller REACH bits that come from it); (b) never persist a backward REACH record (costs performance only). Plus: list
  "end facts are context-insensitive zero-to-fact edges; their records are not exact" in ap §11.1, and copy the
  proposals' end-fact stage rule into analyzer-core §4.5 / int §4.1.

### H3 [MAJOR, CONFIRMED] One sink statement in two contexts is two vulnerabilities (SM-3)
* `VulnerabilityKey = (rule object, method key, statement)` (ap:2004, P:2578); the method key carries the context
  (`JIRInstanceTypeMethodContext` etc.). One statement → several entries, e.g. one CONFIRMED and one DEMAND; the stop
  rule keeps iterating for the DEMAND one. Today the key is `(ruleId, statement)`.
* Fill: keep the internal key per method key (the confirmation is per key); define a user-level key
  `(rule id, method, statement)`: CONFIRMED in any context or alternative wins, all witnesses stay; the stop rule reads
  the user-level key (ap §8.10, §6.6; `Report`, stop rule).

### H4 [MAJOR, CONFIRMED] What stays for the trace resolution does not cover the report (SP-5, AN-2, SM-1)
* The report holds CONFIRMED entries of any forward run, DEMAND entries of the last COMPLETE forward run and the entries
  of an incomplete run (ac §7.5). ac §7.6 keeps the stores of ONE forward run ("latest ... complete or incomplete"),
  while §7.5 reads the last complete one. An incomplete (or cancelled-before-start) run 3 replaces run 1's stores, so
  run 1's entries have no trace; today's pipeline drops a vulnerability without a trace. This is the usual end: an
  unconfirmable vulnerability keeps the iteration going until the timeout cuts the last run.
* Fill: do not replace `retained` on an incomplete run (no new peak: it is alive during that run anyway); keep a joined
  incomplete run beside it; never retain a run that failed before it started; build `TraceData` per `Entry.run`;
  entries of a non-joined run are reported without traces; say how a record step is traced.

### H5 [MAJOR, CONFIRMED; rare] The global-state rule with a conjunctive exit sink (SF-2, AN-4, XD-10, P2-7)
* int §4.7 step 3 drops an `S` item "an exit sink triggered on"; G2 says "read"; Part II says "the part a sink holds
  on". `checkSinks` adds `m.facts` to `parts` (A:1174) BEFORE the conjunctive branch, so one literal of an incomplete
  conjunctive sink drops the state fact: callers lose the state mark, a later state sink does not fire (FN). The
  generator makes exactly this shape (`addStateCheck`, `generateEndSink`). Today drops only the completing item of a
  reached sink.
* Fill: spec: "triggered" = a plain sink whose pattern holds, or a conjunctive sink whose NEW combination this item
  completes; earlier stored `S` inputs stay (order-dependent precision gap, as today). Code: add parts only then.

### H6 [MAJOR, CONFIRMED] The Spring dispatcher cleaner disappears (RU-1)
* Every rule query of the new design passes `fact = null`. `SpringRuleProvider.cleanerRulesForMethod` builds the
  `__cleanup__` cleaner from the fact (`fact ?: return emptyList()`), so it returns nothing: the kill of the `S` content
  outside the registry is lost, and static taint crosses dispatched controllers (new FPs on Spring projects). Not in
  §32/§34; the spec is silent on fact-dependent rule providers.
* Decide: give the provider a fact-free form (an unconditional kill of `S` outside the registry), or record it as a
  deviation.

### H7 [MAJOR, CONFIRMED] Forward liveness kills every local in code that reaches no exit (P2-3)
* `JIRLocalVariableReachability` works backward from `exitPoints()` on the UNWIRED forward graph; a node with no path to
  an exit gets `null`, so every local there is dead. `while (true) { req = q.take(); exec(req); }`: the fact on `req` is
  dropped before the sink (also today). Contradicts ap.md §13 item 13. The I11 (e) wiring exists only backward.
* Fill: int §2.1 step 1 "liveness on the exit-wired forward graph" (exact: a wiring edge adds no use); Part II builds
  `liveness` (and so the alias analysis) on `JIRExitWiredGraph(common)`; widen the graph parameter type.

### H8 [MAJOR, CONFIRMED; rare] A rule position with an inner or repeated `AnyField` (P2-1)
* `[arg0, ".*", ".f"]` or `.*.*` is legal in the rule format and handled today. Part II `pos()` does
  `check(AnyAccessor !in path)`: the form builder throws and the WHOLE run is FAILED. The spec does not define it.
* Fill: int §1.3 row: for sinks, conditions, sources and pass rules, cut at the first `AnyField` (sound:
  `[any]` is any continuation; `.*.*` = `.*`); for cleaners a rule error. `pos()` never throws.

### H9 [MINOR, CONFIRMED] Exit rules at the exceptional exit are not "as today" (RU-5, P2-6, SP-11)
* The new code fires unconditional exit sources and the `ZERO_PATTERN` exit sink (D22) at BOTH exits; today only at the
  normal exit (`JIRMethodSequentFlowFunction.kt:228-233`). SI11 says "None: as today"; SI12 says "normal exit" against
  D22 and §29. An unconditional exit sink can report twice per method.
* Decide: keep both exits (add a D row, drop "as today") or restrict the empty cube to the normal exit. Spec: an
  ARGUED item in ap §11.2 that the two-exit method is the model with a virtual exit (S4).

### H10 [MINOR, CONFIRMED] Gap rows the spec does not have (P2-9, P2-15, P2-5, P2-13)
* Catch handlers receive the facts AFTER the throwing statement (JIR graph), the catch local is not killed:
  `try { check(s); } catch (E e) { sink(s); }` with a cleaner on `check` → FN. Add G9 (as today).
* `<clinit>` is never analysed (no call site, not a root): a source stored by a static initializer is lost. Gap row.
* Static alias bases: AC1/AC2 vs I12 (c). Under A1 (depth 0) such an alias does not survive a call, so AC1 should skip
  `S`; with interprocedural depth > 0 it is a loss.
* Alias-analysis settings are not pinned (A1 depth 0, `useAliasAnalysis = false`, the time limit break A6 silently).

---

## B. Holes in the proposals (the spec decides; code missing or wrong)

### H11 [BLOCKER, CONFIRMED] The witness merge crashes on two alternatives of one sink rule (XD-1, P1-1, P1-7)
* All alternatives (cubes) of one rule share one `VulnerabilityKey`; `Shape` (P:2604) holds only (run, premise, layer)
  per edge; two cubes on two bases merge, `mergeAddDelta` throws at `check(groupKey)`, the runner fails, run 1 FAILED.
  `Argument(*)` sinks (`mkOr` over all arguments) produce this: `exec(s, t)` with both arguments tainted from `{zero}`.
* Fill: `SinkWitness` names its alternative (`sink: SinkRule` or its patterns); `Shape(run, patterns, edges)`; a
  `VulnerabilityStoreTest` row. Spec ap §8.10: "pattern" = the patterns of the alternative each witness triggered.

### H12 [BLOCKER (order-dependent FN), CONFIRMED] The alias guard calls the `[any]` start of a `*`-T answer an identity (SF-1)
* `summaryParts` (A:1049-1059) and `Origin.SUMMARY_EFFECT` (P:3202) compare a result with `startFact(j)`. For a run-1
  chain answer `(x, [], *, {}, T)` the start is `(x, [], [any], T)` (demand), COARSER than the premise. The leaf is
  called IDENTITY and is not copied to aliases, but the alias does not hold it (breaks AC3, AC5; today compares with the
  premise). Worse, the §8.1 subsumption drops the real effect `(x, g.$, T)` under the `[any] T` leaf when the LIFO
  worklist delivers the start first.
* Example: `h(){ x.f = src(); y = x; setG(x); sink(y.g); }`, `setG(p){ p.g = Lib.copy(p.f); }` with a
  `CopyMark(T, Argument(0) → Result)` rule: `sink(y.g)` is never reported (not even DEMAND), so no later run finds it.
* Fill: an identity part only when the start has the denotation of the premise; when `j.tail == STAR && j.mark is
  Concrete`, the whole delta is `SUMMARY_EFFECT`. Spec int AC4: "identity: the conclusion equals the premise, not its W2
  start fact".

### H13 [MAJOR, CONFIRMED] An empty JIR method gets no method key; the call drops the bound facts (P2-2)
* A JIR method with no instruction (native, abstract, no body) has no entry statement, so `resolveEntryPoints` gives no
  key; the plan has no `Callees` stage and no unresolved stage, so the bound facts are killed. Every `isEmpty` branch is
  dead. (A `void log(String s) {}` has a `return`, so it is not empty: SP-9 refuted.)
* Fill: `resolve()` adds an identity stage `ADDED → RETURNED` (`Origin.IDENTITY`) for a `ConcreteMethod` with an empty
  `instList` (gives exactly I8); spec ac §4.4/§4.9 says an empty JVM method has no entry statement.

### H14 [MAJOR, CONFIRMED] The report has no end status and no output contract (SM-2, AN-8, XD-4)
* `analyze` returns a `Report` with no `RunStatus`; a backward OOM or timeout leaves no mark; `bidi.status(report)`,
  `BidiEntry`, `toVulnerabilities` are names only. `Report.Entry` has no pattern, sink edges or end facts, though
  P:2642 says the driver builds the ap §8.10 report.
* Fill: `Report.end = (status, run, direction, reason: STOP_RULE | POLICY | ABNORMAL, allJoined)`; entries reach their
  witnesses via `witnessesOf(run)`; declare `BidiEntry` (or mark §8.1 as a sketch); fix P:2642.

### H15 [MAJOR, CONFIRMED] The fuzzer oracle `NaiveClosure` is a skeleton (AN-3, XD-3; XD-9, P2-10, P2-14)
* 11 rule bodies are `/* ... */`; `FuzzResult`, `ClosureResult`, `dominates`, `ToyProgram`, `ToyInterpreter` are not
  declared; so the main schedule-fuzz test (and proof-first TDD) cannot start. The oracle is writable from the shared
  code, but the comparison of results, the configs of runs 2 and 3 and the end order are left open.
* Minor parts: `FormsReference.apply/agrees` take no premise, so the static exception never applies in the reference
  (test 11 disagrees on `S.*` in run 1); no test rows for int §7.2 items 8–10; `staticWellFormed` and the contract
  helpers have no code; the I7 `$`-target clause is not asserted.

### H16 [MAJOR (hot callees), CONFIRMED] `AddedFactStore` index is O(links²) (P1-2)
* `PathTrie.addIfAbsent` does a linear `value !in ArrayList` per position, with one key per (caller key, caller
  premise, layer, call); `overlapping` enumerates every leaf of every candidate. Fill: a hash set per node (or per store)
  and a `walkPath` in `overlapping`.

### H17 [MAJOR (memory), CONFIRMED] `TrieInterner` drops two properties of today's interning (RU-3)
* Today's table sits behind a soft reference that the memory guard clears, and the store re-interns all its tries; the
  new table is a strong field and interns one trie per 100 adds. DD5 and the reuse row claim the old policy. Fill: hold
  the table through `SoftReferenceManager`; restore the store-wide pass or state the change.

### H18 [MAJOR (memory), CONFIRMED] The phase-3 sketch keeps the prescan alive (RU-4)
* `prescan(...)` → `bidi.run(...)` skips `resetApManager`; `TaintAnalyzer` keeps `ifdsEngine` and
  `JIRAnalysisManager.contexts`, so the prescan's edges, summaries and alias analyses stay for every bidi run. Fill:
  release the prescan engine after copying `prescanRuleIds()` / `prescanLambdas()`; keep only `factTypeChecker` and
  `externalMethodTracker`.

### H19 [MINOR, CONFIRMED; FN if done wrong] `graft` and the generic trie ops have no code (P1-4, SF-4, RU-8)
* `graft` must MERGE at nested occurrences (as `concatToLeafAbstractNodes`, AccessTree.kt:1321-1324); a "replace"
  version loses leaves. The port must also drop today's other depth bounds (`limitFieldAccess`, `limitElementAccess`
  with 2, the `containsStatic` guard), which the ADAPT rows do not say. `internBottomUp` has no code. (verify-V4 has a
  code sketch.)

### H20 [MINOR, CONFIRMED/PLAUSIBLE] End-of-run robustness (AN-5, AN-6, AN-10)
* A cancel through the injected `Cancellation` (a `CancellationException`) kills runners without `fail()`: the run
  waits for its timeout; phase 3 cannot reach `IterationDriver.cancel()`; an `activate()` race. Fill: catch `Cancelled`
  in `runLoop` → `fail(CANCELLED)`; activate in the `RunManager` constructor.
* `onZero` completes without setting `status`, so a late `fail()` (OOM, cancel) during `stopAndJoin` turns a COMPLETE
  run into an incomplete one. Fill: `status.compareAndSet(null, COMPLETE)`, first end wins.
* An exception on the driver thread (barrier, `HandOff`, `persist`) loses the whole report (today: `runCatching` at the
  call site). Fill: catch at the barrier, return the report so far with an error status (needs H14).

### H21 [MINOR] Small proposal holes (verified)
* `applyCombination` / `NdSummaryJoin.addConclusion` take `TaintTree`; the analyzer passes `Facts`: does not compile
  (XD-5, P1-5, SF-5 — found three times).
* `InitialFactStore.supported` is written (A:1818), never read, and holds only caller-premise sets (XD-7, SM-6). Fill
  it after the fixed point, or remove it and record the deviation from ap §8.2.
* W3 (non-decreasing field limit) has no check (AN-7): `require(policy.fieldLimit(n) >= config.fieldLimit)` in
  `HandOff.next`.
* The IR features (boundary instructions, lambda and string-concat transformers) are not stated, and the code degrades
  silently (`ExitRules.EMPTY`, `?: return graph`, empty `resolve()`); today's boundary assert is dropped (P2-4, SF-3).
  Production installs them, so MINOR.
* The primitive mark policy acts only at the root; today it also drops `b.[e].$ (T)` on `byte[]` (RU-2). "As today" in
  D11 is wrong. Precision only.
* `continueAfter` can stop after a backward run, so that run is wasted (SM-4); `driver_iteration_upto` ends after a
  forward run.
* Two of today's asserts are dropped (`to !is MemoryAccess`, a non-immediate call lhs): a wrong IR transformer now gives
  silent wrong edges (P2-12).

### H22 [MINOR, single reviewer, not re-verified]
* `MethodEdgeStore.edgesAt` (both overloads) has no body (P1-3).
* `CompiledEdge` checks S7, S8 but not W1: a non-empty exclusion on an edge with no `*` side filters the fold (P1-6).
* ap.md §13 items 5 and 9 have no test row in Part I §8 (P1-8).
* `RequestKind.Position` changed its path type to `PathNode`; no addition list records it (XD-6).
* W1–W3 and DD ids have two meanings in analyzer-impl.md (XD-8).
* `ruleApplied` of the external method tracker now counts the default getter rules (RU-6).
* `EntryPointTable` uses `ConcurrentReadSafeObject2IntMap`, which ap-impl says the new core does not use (RU-7).
* Line and name drifts in `path:line` references (RU-9: `MethodAnalyzerStorage.kt:37-50`, `JIRFactTypeChecker.kt:97-105`, ...).
* The case-3 chain (a source in a callee reached through a return) is not in analyzer-impl §4.6 and no test runs it (SM-7).
* D19 changes something only for a project functional interface; test 17 does not say which interface (P2-11).
* The progress log and `collectStats` are claimed kept but have no code (AN-9).
* The run-1 static exception at the entry/exit rule statements: the analyzer applies it (follows ap §4.10 item 1 and
  int §5.4); only int:145 says otherwise; both readings are sound (XD-2). Fix int:145 and name the boundary rule
  statements in ap §4.10 item 1, Part II §28.6, §23.3.

---

## C. Spec text holes (no decision needed; mechanical)

* Stale text after F61/F64/F65 (SP-16): ap:1985 (§8.9 union without the zero-drop); ac:929 (§7.5 support of the union
  without the zero-drop); ac:636-637 (`matches` uses the removed `premise.isZero`/`initials`: does not compile against
  ap §7.1); ac:168 (§4.1 edge key not per kind); ap:1911 (`Record.conclusion` omits REACH); int:964 (Q10 "G1–G6").
* Conjunction store key "(rule, statement, literal)": "rule" is undefined; the proposals already key per alternative.
  Write "per (conjunctive micro edge or sink alternative, statement, literal index)" (SP-4; ap §4.6, §4.9, §8.9, int §5.3).
* ap §9.2 lists the backward binding back without `zero.* → zero.*`; the proposals have it (SP-12).
* The application modes (STATEMENT / STAGE / GEN) are only in ap-impl §23.3; copy the table into ac §4.5/§4.9 and fix
  int §4.5 step 5.1 and §4.1 wording (SP-1).
* int §1.4 "one edge for each literal" vs §5.3 (a cube with ≥ 2 literals is an ND edge) (P2-8).
* The three kinds are not proved for run 1 with the static rule (`Statics.DS`); add to ap §11.2 ARGUED (SP-10).
* "kind" has two definitions; ap §7.2 says the premise set gives the kind, false for `{zero}` (SP-13).
* `Guard`, `SinkRule`, `ConjunctiveEdge`, `TypeFilter`, `Cleaner` are used in ac §4.9 and defined in no spec; the alias
  guard needs a fact origin that the plan model does not carry (SP-14).
* S8 says §4.1 asserts `ExactTargetConc`; §4.1 asserts neither it nor the second half of S7 (SP-7).
* S9 and the touched-base part of S10 are interpreter duties that no check or test covers (SP-8).
* D24 (a pass rule applied without its mark literal) is not precise under S1 and is not listed as an over-approximation
  in ap §11.1 (SP-6).

## D. Refuted

* SM-5 (a FAILED run confirmed like a truncated one): the spec decides it (ac:75, :940-942); the checks fire before a bad
  item makes a link or a witness.
* SP-9 (empty method runs the boundary rules): its example is not empty in JIR; the proposal follows I8. The real hole
  is H13.
* SP-1 and SP-4 as proposal holes: the proposals settle both; only the spec wording stays (section C).
* AN-10, the per-method half: the spec makes a run with an exception INCOMPLETE (ac §6.3).
