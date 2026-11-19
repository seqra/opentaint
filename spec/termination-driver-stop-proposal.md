# Driver-level stopping for the bidirectional analyzer

Status: PROPOSAL, 19 November 2026, revision 2. Not implemented.

This proposal replaces the rule-level approach of
[demand-refinement-and-termination.md](demand-refinement-and-termination.md).
The reasons are in the
[postmortem](../docs/reports/bidirectional-termination-postmortem-20261119.md).
It follows the [design guide](design-guide.md).

Revision 1 was tested in two ways before this text was written: a
replay of its stop tests on 2,083 archived analyses
([D](../docs/reports/termination-postmortem-20261119/D-shadow-eval.md))
and an adversarial review against the code
([E](../docs/reports/termination-postmortem-20261119/E-critique.md)).
§6 lists what those tests removed.

## 1. Problem statement, from measurements

Native runtime at HEAD, run-11 cutoff, limits `1,1,2,…,10`.

| Project | End state today | Last report gain | Engine time after that gain | Real problem |
| --- | --- | --- | --- | --- |
| OWASP | `RUN_LIMIT`, run-11, 150 s engine | run-3 | runs 4–11 | Benign period-2 demand |
| Conductor | timeout in run-8, 1,034 s | run-5 | run-6: 499 s, run-7: 123 s, run-8: 193 s | Demand grows with K in two recursive owners |
| Stirling-PDF | timeout in run-11, 1,009 s | run-5 | run-9: 725 s | Work in one loop owner |
| ThingsBoard | memory guard in run-1 | — | — | Run-1 memory |

Facts that decide the design:

1. No analysis in the corpus confirms its first report at run-7 or
   later. No analysis has a forward run `i ≥ 5` with no gain that is
   followed by a gain. The corpus is 2,083 analyses: 8 project launches
   at HEAD, two 585-case rule suites, three launches to run-101, one
   uncapped rule run of 1,275,423 runs, and the refinement and
   prototype runs.
2. Natural termination has a measurable value only on OWASP, and there
   it is 20–30 s of 150 s.
3. The large costs are single runs: Conductor run-6 and Stirling-PDF
   run-9. A stop test cannot remove a run that precedes the stop.

Conclusion. Do not try to make the demand empty. Keep a policy cutoff,
make it adaptive, and work on the cost of one run as a separate
problem.

## 2. Selected semantic scope

Changed:

- `IterationPolicy`: one new policy that reads the run history. The
  driver already passes the history; no policy reads it today.
- `EndReason` and `Report.kt:70-74`: a new reason `QUIESCENT` that
  publishes provisional entries in the same way as `RUN_LIMIT`.
- Barrier log lines (§4).

Unchanged: field transfer, C2, C5, tails, layers, exclusions, summary
application, replay, publication, cleaners, the handoff and its
compaction, the run-1 and run-2 static views, the field-limit
schedule. The run-11 cutoff stays as the last guard.

No work is added per fact, per offer, per summary or per handoff row.

## 3. Step 1 — adaptive cutoff (`QUIESCENT`)

At a completed forward barrier of run `i`:

```text
stop if  i >= 5  and  confirmed_i == confirmed_{i-2}
```

Report: confirmed set `C` plus provisional `L \ C`, as at `RUN_LIMIT`.

This is a policy cutoff. It makes no claim of natural termination. It
has the same kind of error as the run-11 cutoff: a relation that needs
a larger limit is published as provisional, not as confirmed.

Replay on existing logs (decision only; nothing was rerun):

| Case | Fires at | Confirmed at stop / at real end | Engine time |
| --- | --- | --- | --- |
| OWASP | run-5 | 2,633 / 2,633 | 124 s, was 150 s |
| Conductor | run-7 | 7 / 7 | 842 s and completes, was timeout at 1,034 s |
| Stirling-PDF | run-7 | 32 / 32 | 161 s, was timeout at 1,009 s |
| 8 HEAD project launches | 8 of 8 | loss 0 | saves 3,267 s of 5,473 s |
| 585 rule tests, two suites | 3 early stops | loss 0 | less than 0.25 s |
| All 2,083 analyses | — | loss 0 | — |

Known limits of this evidence:

- **The margin is one run.** Three rule tests
  (`facesSelectItemGroupUnsafe`, `mapEntryUnsafe`,
  `BeanInjectionSamples#doPost`) have confirmed counts 0, 0, 1 at runs
  1, 3, 5. One quiet forward run is not finality. Only the floor
  `i >= 5` keeps them.
- **A loss mechanism exists.** A chain deeper than K leaves no NORMAL
  record (`ap/Limit.kt:12-17`, `store/RecordStore.kt:255`). A value
  wrapped 6 levels deep in one method and read 6 levels deep at the
  root gives quiet runs 3 and 5 and a confirmation at run-7. With this
  stop it is published as provisional. This case is not in the corpus.
  It is the first test to write.
- **Provisional output differs.** The stop publishes `L_i \ C`, not
  `L_11 \ C`. Two run-101 fixtures end with 0 confirmed and 1
  provisional; they need the provisional output. Stirling-PDF has 2
  provisional entries in the launches that complete run-11. The
  provisional set is not logged per run today, so the difference is
  not measured.
- **Counts, not identities, were compared across launches.**
- **A fixed cutoff at run-7 gives nearly the same table with a
  one-constant change.** The adaptive form differs only when a project
  still gains at run-5 and run-7. No such project is in the corpus.
  Step 1 must be compared with `lastForwardRun = 7`; if the two are
  equal on the gate, select the constant.

Gate for Step 1 (native, behind a flag, three interleaved launches):

1. The depth-6 fixture: record what each variant publishes.
2. The three late rule tests and both run-101 provisional fixtures.
3. 585 of 585 rule tests on HEAD keep their result.
4. Each project: confirmed identities equal to the run-11 baseline
   where that run completes; provisional difference listed and
   accepted explicitly.

## 4. Step 0 — measurements that the next steps need

Add to the barrier log of each run. All values exist at the barrier.

| Value | Why |
| --- | --- |
| Size and hash of `L \ C` | Measures the provisional difference of Step 1, and tests H1 below |
| Top owners by demand rows, with "in a call cycle" and "loop block" flags | Step 2 |
| Number of new NORMAL records (from `FlowBackedSummaries.addAll`) | Shows if a quiet run still changes persistent state |

H1 (not established): `C_later ⊆ C_i ∪ L_i` for each forward run
`i ≥ 3`. In words: each report confirmed later is already reached now.
If the logs support H1, the provisional output of Step 1 is a complete
upper bound, and `L_i ⊆ C_i` becomes a candidate for an exact stop.
If one case violates H1, record the case and drop the idea.

## 5. Step 2 — cost of one run (trace first, no rule yet)

Step 1 leaves Conductor at 842 s, of which run-6 is 499 s. This is the
main remaining cost and it is not a termination problem.

- **Conductor.** 88% of the H7 rows are in `ParametersUtils#replace`
  (two contexts) and `replaceList`, which are mutually recursive. Rows
  per owner grow while the owner count falls. The hypothesis "each
  larger K admits one more container level" is an inference from
  counts. Required order: confirm the owners with Step 0, decode the
  keys of one owner at H3, H5, H7, classify what is new, then select
  one rule and prototype it natively on Conductor. A widening of
  demand in recursive owners at the handoff is the first candidate to
  test. It is not selected.
- **Stirling-PDF.** `decodeMimeHeader` run-9 takes 4.45 s, 391 s or
  725 s on equal sources. This is a work-order defect at a loop
  boundary. Fix or pin it before Stirling-PDF is used as evidence for
  any other change.
- **ThingsBoard.** Run-1 memory. Out of scope here.
- **Per-run time budget.** Not selected. Conductor run-4 (needed, 1.8
  times all earlier runs) and run-6 (not needed, 2.3 times) are too
  close to separate with one factor.

## 6. Rejected after test

| Idea | Why rejected |
| --- | --- |
| Exact repeated-state stop (`FIXED_POINT`, closed run pair) | No measured benefit: the first qualifying pair on the measured OWASP entry is run-10/11, the cutoff. Strict state equality never holds on a full project within the cutoff. It also needs unproved premises: schedule-independent runs, service-exact compaction (`HandoffCompactor.kt:54-55` depends on input order), a grow-only record store (`recompact` removes rows) and a counter at each K site (K is a bare `Int`; `PreparedOutputPrograms.kt:107-109` puts K in a cache key). |
| Quiet test with two quiet forward runs | Never fires on Conductor; on Stirling-PDF it fires after the 725 s run. |
| Quiet test on "no new NORMAL record" | Not measured. On the OWASP entry the saved-record basis still differs at H9, so it probably fires late. Keep the counter in Step 0; do not put it in the stop. |
| Local demand retirement (R41, R42, R37/R38) | Zero effect at project scale; see postmortem §3. |
| Monotone demand memory across runs | Fits OWASP only, where the gain is 20–30 s. Needs new persistent state and an open proof for dropped coarse replies. |

## 7. What this proposal does not give

- A natural stop on OWASP. It ends with `QUIESCENT` instead of
  `RUN_LIMIT`.
- A fast Conductor. It completes, at about 842 s.
- A proof that no later run confirms a report. The evidence is
  empirical, and §3 names the mechanism that can break it.
