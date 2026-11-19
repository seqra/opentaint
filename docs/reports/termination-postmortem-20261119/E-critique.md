# E — Adversarial review of `spec/termination-driver-stop-proposal.md`

Read-only review against HEAD `758ad99ff`. Nothing was built or run.
`BIDI = core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi`.
VERIFIED = read in code / report at the cited line. INFERENCE = my reasoning, not executed.

Verdict in one paragraph: Stage 0 (measure) is right and should ship. Stage 1 (`FIXED_POINT`) is logically
sound under two unstated assumptions (determinism, complete K audit) but on the only measured instance it
fires at run-11, i.e. at the cutoff, and it cannot fire on the two projects that time out; it is a label
change, not a saving. Stage 2 (`QUIESCENT`) has a concrete loss mechanism (a flat flow of field depth 5-6 is
quiet at run-3/4/5 and confirms at run-7), its "expected effect" table does not follow from its own formulas
(Q2 fires at run-9, not run-7, on Conductor and Stirling-PDF), and the one existing data point says NORMAL
records keep changing long after reports are final, so Q1 will probably not fire where it is needed.

---

## S1. QUIESCENT can lose a confirmed report: quiet runs do not imply nothing is coming (§5) — most severe

**Mechanism (code VERIFIED, end-to-end behaviour INFERENCE).**

- A path deeper than the budget leaves *nothing* on the NORMAL layer. `limitTrie` (`BIDI/ap/Limit.kt:21-30`)
  emits `within` on the original layer and `overflow` on `Layer.DEMAND` (`Limit.kt:12-17`). For a single
  chain of counted depth d > K, `FieldLimitCut.keep` builds `kept` from `frame.node.leaf` plus kept children
  (`Limit.kt:83-84`); a chain has no leaf above the cut, so `kept` is empty (`takeIf { !it.isEmpty }`) and
  the whole fact becomes one DEMAND `[any]` stub.
- Only NORMAL is persisted: `persistOne` skips `facts.layer == Layer.DEMAND` (`BIDI/store/RecordStore.kt:255`).
- So a summary whose shortest exact form needs depth d produces zero persisted records in every run with K < d.

**Sketch.**

```java
Object m(Object x) { return new A(new B(new C(new D(new E(new F(x)))))); }   // one method, 6 wraps
void root(Req r)   { Object y = m(r.source()); sink(((A)y).a.b.c.d.e.f); }     // 6 reads
```

Leaf constructors/getters have depth-1 summaries that are NORMAL and persisted in run-1/run-2. `m`'s
summary `arg0.* -> ret.a.b.c.d.e.f.*` has depth 6. With limits `1,1,2,3,4,5,6` (runs 1..7,
`IterationPolicy.kt:42-52`) it is cut in runs 1-6 and first NORMAL in run-7 (K=6). Runs 3, 4, 5 persist no new
record, target or contributor, and confirm nothing. Q1 at i=5 (`newConfirmed_5==0 && newNormal_4==0 &&
newNormal_5==0`) and Q2 at i=5 (`newConfirmed_5==0 && newConfirmed_3==0`) both fire. The report that run-7
would confirm is downgraded to provisional (it is in L because `reachedSinkReportIds` is filled for a
DEMAND-layer witness too, `BIDI/engine/RunMethodLocalServices.kt:372-376`). Under §8 that is a lost confirmed
identity.

The general statement: intermediate depths leave NORMAL traces only when the program happens to have an
intermediate *summary boundary* (method or loop block) at that depth. Depth concentrated in one method body
leaves none. QUIESCENT is therefore "stop at the first K where two consecutive depths add nothing", which is
sound only if required depths are dense.

**Existing candidates that Stage 0 must look at first (VERIFIED they exist, content not measured):** the rule
suite has two natural stops at run-7 and one at run-9
(`docs/reports/bidirectional-work-reduction-performance-20261112.md:80-82`). If any of them confirms its
report at run-7/9 after a quiet run-5, Q1/Q2 fail the §3 gate on day one. C-real-stalls §4(d1) already flagged
the run-9 case; the proposal dropped that note.

**"No such case is in the four project logs" is an overclaim (VERIFIED against C-real-stalls §2, §3.1).**
There are three logs, not four (ThingsBoard never completes run-1). Observed quiet forward runs after the
last gain: OWASP 4 (runs 5,7,9,11), Stirling-PDF 2-3, Conductor exactly 1 (run-7; run-8 times out). And
`newNormal` has never been measured on any project (C §3.2 "NOT MEASURED").

**Stage 0 cannot measure the risk on the project the stop is for (INFERENCE from C per-run times).** The gate
compares against "the run-11 report", but Conductor never reaches run-9 (run-6 = 499 s, growth ~5x per
backward run). The shadow table for Conductor can only say "equal to the timeout baseline", which is true by
construction. The gate is vacuous exactly where QUIESCENT matters.

## S2. The §5 "expected effect" table contradicts the §5 formulas (VERIFIED arithmetic on C §2)

Confirmed counts per forward run: Conductor 2, 5, 7, 7 (runs 1,3,5,7); Stirling-PDF 7, 28, 32, 32; OWASP
2,120, 2,633, 2,633, 2,633.

- Q2 needs `newConfirmed_i == 0 && newConfirmed_{i-2} == 0`. Conductor: `newConfirmed_5 = 2`, so Q2 does not
  fire at run-7; first at run-9, which is never reached. Stirling-PDF: `newConfirmed_5 = 4`, first at run-9,
  i.e. after the 725 s run-9. OWASP: `newConfirmed_3 = 513`, first at run-7.
- So "Conductor: run-7, 842 s, completes" and "Stirling-PDF: run-7, 161 s" hold only under Q1 with an
  unmeasured `newNormal_6 == newNormal_7 == 0`. The sums themselves are right (841.8 s, 161.5 s).
- The one measurement that exists points the other way: on the selected OWASP entry (2 roots, 2 reports,
  constant) "at the run-9 handoff the ordered demands already match run-7 but the saved-record basis differs"
  (`docs/reports/bidirectional-useful-rule-cost-fixes-20261119.md:249-250`). NORMAL records were still
  changing at run-8/9, six runs after the reports were final. Expecting zero new NORMAL records in Conductor
  run-6, which handles 149,630 demand rows of new, deeper keys, is not supported by anything. INFERENCE: Q1
  will rarely fire before run-9/11 on real projects; then QUIESCENT is Q2 or nothing, and Q2 does not rescue
  Conductor.
- Net: on the evidence available, QUIESCENT saves about 17-26 s on OWASP (runs 8-11 = 17.1 s, runs 6-11 =
  26.4 s; the proposal's "20-30 s" is slightly generous) and nothing on the two timeout projects.

## S3. FIXED_POINT: logic is sufficient, but the premise "a run is a function of (demand, seeds, NORMAL, K)" is not established

**What holds (VERIFIED).**
- No run-index special case exists for index >= 3. All index reads are `run == 2`, `run < 3`, `run >= 3` or
  `run1`: `RestrictedInitialPolicy.kt:43,102`; `DemandStore.kt:67,98,137,336`; `BlockBoundaryDemandView.kt:77`;
  `RestrictedInitialEmission.kt:21`; `RunMethodLocalServices.kt:441`. Static completion and shared static
  carry are refused after run-2 (`DemandStore.kt:98`). Mark mode is FULL for every run > 1
  (`RunConfig.kt:45-46`). So for i >= 5 the remaining `RunConfig` inputs are exactly: `demand`, `records`,
  `seeds`, `roots` (constant), `normalTargets`, `fieldLimit` (`RunConfig.kt:15-26`,
  `IterationDriver.kt:237-243`), plus `shared.normalRuleContributors` read via `restoreOnce`
  (`RunMethodLocalServices.kt:79`).
- The stated condition is sufficient for the induction *if* runs are deterministic. Before run i-1 the state
  is (H_{i-2}, P_{i-2}); `newNormal_{i-1}=0` and `newNormal_i=0` give P_i = P_{i-2}; `demandKey_i =
  demandKey_{i-2}` gives the same demand; so run i+1 has run i-1's inputs at a larger K, and
  `kBound_{i-1}=0` makes it repeat, producing H_{i-1} again; then run i+2 repeats run i. No extra condition
  `demandKey_{i-1} == demandKey_{i-3}` is needed; it follows.

**What is missing.**

1. **Determinism (INFERENCE, strong circumstantial evidence).** `ClosedRunPair` takes
   `forward backward : Nat -> State -> State` (`ClosedRunPair.lean:4`) and `auditRun` is one deterministic
   work sequence (`:97-107`). Production runs are multi-threaded on `shared.dispatcher`
   (`SharedObjects.kt:34,55`). The prototype that the Lean file models required "one active root and one
   effective unit" (cost-fix report `:259-260`) and compared *ordered* demand and *saved-record index order*
   (`:251-253`; Lean doc comment `:1-3`). The proposal drops both restrictions and compares an unordered key
   set. The evidence says results are schedule-dependent: OWASP H11 has 975-1,153 rows on equal launches,
   Stirling-PDF run-9 costs 4.45 s / 390 s / 725 s and the fast shape has 2 extra provisional identities
   (C §2). If the demand output is schedule-dependent, one observed `S -> B -> S` does not prove the next pair
   returns to S. The proposal's obligation 2 notices the symptom but (a) assumes the cause is compaction order
   without evidence, and (b) frames it as cross-launch equality, when what the theorem needs is within-launch
   confluence. This is the "proof about a model that differs from production" failure again.
2. **The key is taken before compaction but the next run consumes the compacted store (VERIFIED).** The
   `DemandStore` is built only from `selection.kept` (`HandOff.kt:74-82`). `HandoffCompactor.selectGroup`
   drops whole *origins* in a stable sort by `(exit, protected, orderKey)` (`HandoffCompactor.kt:54-55`); ties
   fall back to input order, i.e. to `result.analyzers` and summary iteration order. Equal pre-compaction
   *row* sets with a different origin grouping can give different kept row sets. "Equal key ⇒ equal run input"
   therefore rests on "compaction is service-exact", which is an unlisted proof obligation (the class comment
   says the MAY-only removals are disabled because their proof is open, `HandoffCompactor.kt:21-22`).
3. **Other shared state between runs (VERIFIED present, effect INFERENCE).** `shared.contexts`
   (`MethodContextCache`), `shared.reportCatalog` (`SharedObjects.kt:48`), `ApManager` interners and soft
   caches (`ApManager.kt`, `TrieInterner.kt`, `FormsCache.kt`, `Groups.kt` use `SoftReference`). The prototype
   run cleared soft caches as a control; the proposal lists none of them. They are probably semantically
   neutral, but "probably" is what the audit is for.
4. **Persistent state is not grow-only (VERIFIED).** `FlowBackedSummaries.recompact` removes covered rows
   (`FlowBackedSummaries.kt:42-75`) and `rebuildIndexes` rebuilds every index from a `HashMap` at each barrier
   (`RecordStore.kt:149-161`, called twice, `:241,247`). `newNormal == 0` means "no addition was reported", not
   "same store"; it should be "empty delta and no removal".
5. **Hash only.** An "exact" stop decided on a hash should keep size plus a wide hash, or the set itself for
   the two retained handoffs. Minor.

## S4. FIXED_POINT has no measured benefit, and `kBound == 0` is unrealistic for a whole scan

- On the one entry where it was measured, global cuts at run-5/7/9 were 244 / 129 / 24 packets and reached
  zero only at run-10; the first qualifying pair is run-10/run-11 (cost-fix report `:245-254`). That is two
  roots. At run-11 `FIXED_POINT` returns the same report as `RUN_LIMIT` with L ⊆ C. Saved time: zero.
- `kBound` is a whole-scan counter. One cut in any of OWASP's thousands of roots blocks the stop. The global
  cut is the only widening in recursive/looping code (Conductor `replace`/`replaceList`), so there `kBound`
  is non-zero at every K by construction (INFERENCE). C §4(a) said explicitly that a useful version "must be
  per component"; the proposal removed the 4-root bound but kept the whole-scan scope.
- "Paired cap with depth >= K" can essentially never fire for i >= 3: exit patterns come from summaries stored
  under the previous run's limit (`MethodEdges.kt:87,117-118` assert `boundedDepth <= fieldLimit`), which is
  K-1. Harmless, but one of the three listed K events is dead (INFERENCE).
- Honest expected effect: OWASP's end label may change at run-11. §4 says "ends with a natural stop instead
  of RUN_LIMIT" without saying it saves no run.

## S5. `kBound` feasibility: the sites, and why "sites that already compare with K" is wrong (VERIFIED)

Every production read of the global limit:

| # | Site | Role | Hot? | Already compares? |
| --- | --- | --- | --- | --- |
| 1 | `engine/BlockRunState.kt:480-489` `cut` → `ops.limit(facts, limit, out)` | every instruction / successor result | hottest | no; decision is inside `limitTrie` (`Limit.kt:25`) |
| 2 | `engine/BlockRunState.kt:433`, `:897` | static summary / static producer routes | warm | no |
| 3 | `engine/RestrictedInitialEmission.kt:16` | every offered actual before C2 | hot | no |
| 4 | `ap/RestrictedInitialPolicy.kt:20` (`emit`), `:93` (`canEmitInitial`), `:147` (`legalInitial`), `:137` | entry depth rejection, per demand row x actual | hot | yes, but folded into a `null` return; the policy object is one shared instance (`RunConfig.kt:47`), so a counter needs a `LongAdder` or a reason code |
| 5 | `store/DemandStore.kt:278-291` `budget = if (depth >= global) global else depth + 1` | C5 paired cap, per selected output | hot | partial |
| 6 | `store/PreparedOutputPrograms.kt:107-109` | same formula, **baked into a cached `OutputProgramKey`** | prepare-time | the K decision is taken once per program, not per event |
| 7 | `engine/MethodBlockRuntime.kt:509-516` | block boundary cut | warm | **yes — the only site with a counter (`boundaryLimitCuts`)** |
| 8 | `engine/NeutralRelationBatch.kt:104`, `engine/OwnedJoinedStaticWriterBinding.kt:104`, `ap/RestrictedInitialPolicy.kt:103`, `engine/StaticInputGrammar.kt:14` | run-1 / run-2 only | n/a for i >= 5 | — |

Consequences:

- Only site 7 "already compares with K". The others delegate to `limitFacts`, which is shared with relative
  budgets (site 5, and the trial budgets in `engine/LoopOutputRestriction.kt:175-179`, which cut by design).
  The counter cannot live inside `limitFacts` without a flag; it must be at each call site or in a wrapper.
- The test is O(1) (`boundedDepth` is a cached field, `ap/Trie.kt:41`) but it is new code on the hottest path
  (site 1) and it passes through `transportProtection` splitting (`ap/ApOps.kt:157-158`). Use per-actor
  counters summed at the barrier, like `boundaryLimitCuts`; never a shared atomic.
- Site 6 is not a "cut happened" event: K is folded into a cache key. Site 5 is a `min`, not an event.
- "A test that fails if a new K site is added without the counter" is not mechanically possible while K is a
  bare `Int` reachable as `config.fieldLimit`, `mode.fieldLimit`, `policy.fieldLimit` and the private
  `limit` of `BlockRunState`. It needs an opaque limit type whose only accessors are audited. That is a
  refactor of code §2 declares untouched.

## S6. `newNormal_j` and `demandKey_j` feasibility (VERIFIED)

- "`RecordStore.persist` knows if a record is new" is false as written. `persistOne` calls `retain`
  (`RecordStore.kt:259`), and `retain` discards the delta (`:143-147`). The delta exists one level down:
  `FlowBackedSummaries.addAll` returns `List<Facts>` (`FlowBackedSummaries.kt:35-36`). A three-line change,
  but note records are *merged trees*, so the unit is "non-empty delta packets", not rows, and removals by
  `recompact` are invisible to it (S3.4).
- NORMAL targets: only forward barriers produce them (`Report.kt:34` returns early for backward).
  `NormalTargetStore` dedups in a private set (`engine/NormalTargetStore.kt:37-47`) and exposes no size; needs
  an accessor.
- Contributors: `NormalRuleContributorStore.publish` already returns "new geometry or metadata"
  (`NormalRuleContributorStore.kt:121-123`), but the driver calls it *after* the stop decision
  (`IterationDriver.kt:221-225` decide, `:229-232` publish). The stop test must move below the publish, or
  the contributor delta must be pre-computed. The comment at `:227` says the current order is deliberate.
- `demandKey`: key = `(HandoffOwner(method, scope, exit), entry kind/pattern, exit kind/pattern)` from
  `PairedDemand` (`HandoffCompactor.kt:111-131`). Hashing interned objects is cheap and stable *within* a
  launch. It is not comparable *across* launches (accessor ids, context allocation ids; the compactor itself
  avoids "opaque context allocation IDs", `:42`). Obligation 2 ("equal keys in repeated launches") therefore
  needs a canonical string rendering (`keys.order`), which is a per-row string build — fine for Stage 0
  diagnostics, not something to leave on in production for Conductor's 150k-480k-row handoffs.
- The key must also cover what the row set does not: nothing else, as far as I can see — the `DemandStore`
  after run-2 has no completion or carry (`DemandStore.kt:98`), and `Builder.add` dedups on the exact
  normalized row. Seeds are a separate `SeedIndex` and are named in the proposal.

## S7. Report handling under the new reasons (VERIFIED)

- `ReportBuilder.build` adds L∖C only when `end.reason == EndReason.RUN_LIMIT` (`Report.kt:70-74`).
  `QUIESCENT` "reports the same as RUN_LIMIT" therefore requires editing `Report.kt` and the `EndReason` enum
  (`Report.kt:8`); §2 lists only "the stop test" and "counters and logs" as changed. SARIF consumes the
  provisional flag (`core/.../sarif/SarifGenerator.kt:43`).
- The provisional set at a run-7 stop is L_7∖C, not L_11∖C. L is replaced at every forward barrier
  (`Report.kt:61-66`) and depends on that run's seeds and K. Stirling-PDF's 2 provisional identities appear at
  run-11 in the fast shape only. §8 covers this as a "listed difference", but the proposal should say that the
  provisional set is expected to differ, not "the same".
- Q1 is otherwise well-defined only after `newNormal` is pinned down (delta packets vs rows; removals;
  contributor timing).

## S8. Smaller inconsistencies

- §1 fact 1 ("runs after the last report change add zero confirmed reports") is true by definition of "last
  change". The real claim is about window length, and the windows are 1-4 forward runs (S1).
- §7 says Stirling-PDF must be fixed or pinned "before it is used as evidence"; §5 uses its per-run times as
  the expected effect and §3 includes it in the Stage 0 table.
- §3 `demandByOwner_j` is the first step of §6 and needs nothing from §4/§5; it is the measurement that
  addresses the largest loss (Conductor run-6, 499 s) and is buried as the last row.
- §8 "wall time and peak memory not worse than native in three interleaved launches" — native variance on
  Stirling-PDF is 160x; three launches cannot separate a counter's cost from noise there.
- The percentages 21 % / 77 % / 89 % divide engine seconds by driver seconds (C §2). Fine as orders of
  magnitude; they are not "driver time" shares.

## S9. What I would cut, add, reorder

1. **Keep Stage 0, shrink it.** Log per barrier: `newConfirmed`, `|L∖C|`, record delta packets (and
   removals), new NORMAL targets, contributor-changed flag, pre-compaction demand set hash + size, and
   `demandByOwner`. Count K cuts only at the existing site 7 plus one per-actor counter at
   `BlockRunState.cut`; do not build the audited-K refactor until a stop is shown to fire before run-11.
2. **Before any project run, answer S1 with tests that take minutes:** (a) dump per-run confirmed counts for
   the three rule tests that stop at run-7/run-9; (b) add the flat depth-6 fixture above (and a depth-8 one).
   If either shows quiet-then-gain, Q1 and Q2 are dead as specified.
3. **Test a different, cheaper invariant in shadow (INFERENCE, not verified):** `C_j ⊆ C_i ∪ L_i` for all
   later forward j. L is recorded for every forward sink witness on either layer
   (`RunMethodLocalServices.kt:372-376`), so it is plausibly an over-approximation of everything a deeper K
   can confirm. If it holds on the 585 tests and three projects, then "L_i ⊆ C_i" alone is a stop with no
   demand hash, no `kBound` and no `newNormal` — OWASP has 0 provisional and would stop at run-3. If it does
   not hold, at minimum add `L_i ⊆ C_i` to Q1/Q2: it blocks the S1 sketch, where the sink is DEMAND-reached.
4. **Compare QUIESCENT against the zero-code alternative.** Every project's reports are final at run-5. A
   lower `lastForwardRun` (`HardRunLimitPolicy`, `IterationPolicy.kt:24-27`) of 7 gives the §5 table exactly,
   with the existing `RUN_LIMIT` report semantics and no new counters. QUIESCENT must beat that on evidence,
   not on being "adaptive".
5. **Demote Stage 1** to "if Stage 0 shows `demandKey` repeats and `kBound == 0` before run-11 on a full
   project". If it is kept, state the two real obligations: within-launch confluence of a run's sealed output,
   and service-exactness of compaction; and make it per root component, as C §4(a) recommended.
6. **Promote the per-run budget (§6 last paragraph) and the Conductor key decode (§6 steps 1-2).** They are
   the only items aimed at where the time goes: Conductor run-6 (499 s) and run-8, Stirling-PDF run-9. A
   per-run cap changes nothing about soundness relative to today's timeout and needs no proof.
