# Postmortem: the demand-refinement and termination spec

19 November 2026. Scope: why
[spec/demand-refinement-and-termination.md](../../spec/demand-refinement-and-termination.md)
and the [term-task](../../term-task.md) process did not solve the real
termination cases and caused a large performance loss, and why most of
its rules have no effect.

Nothing was rerun for this report. All numbers come from the reports
of 12–19 November, the archived native logs and the Git history.
Detailed evidence with file and line references is in three appendices:

- [A — root cause](termination-postmortem-20261119/A-root-cause.md)
- [B — rule table and rule gap](termination-postmortem-20261119/B-rule-gap.md)
- [C — real stalls in the HEAD runtime](termination-postmortem-20261119/C-real-stalls.md)
- [D — replay of early-stop tests on 2,083 archived analyses](termination-postmortem-20261119/D-shadow-eval.md)
- [E — adversarial review of the first proposal draft](termination-postmortem-20261119/E-critique.md)

The consequences are in the
[design guide](../../spec/design-guide.md) and the
[driver-level stop proposal](../../spec/termination-driver-stop-proposal.md).

## 1. What failed, in numbers

Implemented build `1197f72f7` against the previous bidirectional core:

| Project | Before (reached / completed runs) | After | Main change |
| --- | --- | --- | --- |
| OWASP | 11 / 11, `RUN_LIMIT` | 11 / 11, `RUN_LIMIT` | run-11 engine 3.2 → 6.1 s; 2,633 findings, 0 lost |
| Conductor | 8 / 7, timeout | 2 / 1, OOM | run-2 engine 41.3 → 219.1 s; 2 of 7 findings |
| Stirling-PDF | 11 / 10, timeout | 4 / 3, timeout | run-3 engine 4.2 → 419.0 s |
| ThingsBoard | run-1 memory guard | run-1 memory guard | no change |

No project gained a natural stop.

## 2. Root causes

### RC1. The campaign solved a different problem

The task defined the problem as "demand is renewed forever with no
hard limit" (`term-task.md:54`). The real projects fail differently:

| Project | Real failure | Is it demand renewal? |
| --- | --- | --- |
| OWASP | Exact period-2 demand from run-7; 3–6 s per run | Yes, and benign |
| Conductor | Demand grows with the limit in two mutually recursive container walkers; backward runs cost 46 → 135 → 499 s | No. It diverges, it does not repeat |
| Stirling-PDF | One loop owner takes 4.45 s, 390 s or 725 s on equal sources | No. Work inside one run |
| ThingsBoard | Run-1 heap | No |

Time and memory were not part of the definition of a counterexample.
Thus three of four projects were outside the task from the start.

### RC2. Synthetic scope excluded the one real recurrence

`term-task.md:12,49-53` required synthetic ordinary code and banned
library models. The catalogue has zero entries from a real project.
The OWASP `doSomething` stall was traced on 10 November, before the
campaign. It is a FLOW copy pair in a loop-free helper, renewed by the
relative C5 cap and a library-model inside read.
`spec/normal-backed-flow-demand-retirement.md` already proposed what
later became R41. The campaign catalogue is dominated by repeated root
Targets instead.

### RC3. Each counterexample was found against the proposal, not the runtime

Phase 1 said "keep all selected mechanisms enabled" and the catalogue
entries read "Counterexample to: all preceding fixes". Each new rule
therefore repaired a state that only the earlier proposed rules
create. The loop was closed over the model: example → rule → new
example of the new model → rule. No step returned to the native
runtime. This is why a rule can have a proved counterexample and no
effect natively (§3).

### RC4. The task banned the repair class that works

`term-task.md:94`: do not hide demand, cancel Targets or weaken the
stop test. The only admissible repairs then add service: a new tail
(NE), more starts, more kept rows, more guards. R18 ("run C5 even if a
saved NORMAL covers it") is the direct opposite of the OWASP fix. All
measured natural stops on real code come from removing demand or from
changing the stop test.

### RC5. Proofs covered a reference model, and never cost

The validation report states that the production driver "does not
implement the complete reference protocol". The no-loss audit of
17 November said "Do not activate the full proposal by default". Of
about 7,554 Lean claims, none concerns work or memory. "Give bounds"
was satisfied by local bounds such as "at most two starts per family".
A local bound of 2 on a route that carries 99.78% of 1,076,995 offers
(Conductor shared static carry, R32) is the measured OOM.

### RC6. No measured gate before implementation

No rule was run on a real project before the full implementation.
The first project measurement was the failed build. The task had no
per-project acceptance gate and no cost budget.

### RC7. Rule accretion on hot paths

About 30 of the 35 implemented rules act per fact, per offer or per
publication. Five rules (R20, R31, R32, R34, R38) exist only to repair
losses that earlier proposal rules introduce. The result is a rewrite
of the fact semantics, not a termination patch.

### RC8. The rules that stop anything were deferred

In the reference model about 12 of 24 stops rely on root-Target
retirement (R37/R38). These, and the loop and recursion rules
R39/R40, were postponed in the cleanup (`e342cdfba`). The implemented
set R01–R36 had the stop test unchanged and no retirement rule. It
could only add work. Note: the deferral did not cause the OWASP
failure. OWASP needs R41, and R37/R38 are also without effect natively.

### Where the performance loss came from

- Conductor: R32 fired on the shared static carry of run-2. Restoring
  the old start for the carry alone lets run-2 complete in 183.6 s.
  The qualified reply channel and lost cache hits (13,764 → 0) add to
  it. This comes from ablations that also change coverage, so it is a
  trigger, not a proved sole cause.
- Stirling-PDF: the revised loop observation makes a complete
  observation per attempted prefix: 1,455,858 observations in two
  contexts of `decodeMimeHeader`.

The spec predicted neither.

## 3. Why most rules are useless

Native isolated prototypes (18–19 November), 42 rule IDs:

| Verdict | Rules | Count |
| --- | --- | ---: |
| Useless (no new natural stop) | R01–R04, R06–R08, R10, R20, R27, R29, R31, R32, R34, R37, R38, R42 | 17 |
| Native parity or depends on NE; no separate prototype | R05, R09, R11, R12, R14–R16, R18, R19, R21–R25, R28, R30, R33 | 17 |
| Removed or postponed | R17, R39, R40 | 3 |
| Useful on a fixture | R13, R26, R35 (closed-callee form), R36, R41 | 5 |

Primary reason for each useless rule (classification by this review):

| Reason | Rules | Count | Strongest evidence |
| --- | --- | ---: | --- |
| Stack-relative: the renewal survives the rule alone | R01–R04, R06–R08, R10 | 8 | R07 and R08 change zero of 92 case end states, including their own fixtures |
| Repair of a loss that another proposal rule creates | R20, R31, R32, R34, R38 | 5 | R20 "required for the tested NE integration"; R38 repairs R37 |
| Not a termination mechanism | R27, R29 | 2 | R27's proof says results are order-independent |
| Guards too narrow to fire | R37 | 1 | Single root, copy-only method, no generated blocks |
| Fires, but demand is renewed | R42 | 1 | Frontier 6 → 3, "The Target remained" |

Three more facts:

- Six of the eight stack-relative rules do harm alone. R01–R03 take
  the global-cut fixture from 6 to 302 pairs. R10 takes the protected
  fixture from 7 to 240. R06 turns two natural run-5 stops into
  run-101.
- The trigger patterns are rare in real code. 583 of 585 rule tests
  stop naturally in the native runtime. R08 saw zero overruns on
  Conductor. R36 made zero partition calls on all four projects.
- The five useful rules are inactive at project scale. R26, R35 and
  R36 do not fire on any project. The sound form of R41 makes zero
  attempts on all four. The OWASP helper family that R41 targets is 72
  of 776 run-11 pairs, so R41 alone cannot stop the full scan.

What produced measured progress was work removal outside the rules:
joined index seal (rebuilds 202 → 101), loop replay skip (9,670,433
replays skipped in Stirling-PDF run-9), C5 index bypass (216,598
insertions on Conductor).

### Limits of the prototype campaign

- No useless rule was run on a project. No rule combinations.
- R37/R38 only in the copy-only scope. R39/R40 not at all.
- R31, R32 and R34 are soundness repairs. "Useless for termination"
  does not measure their purpose.
- Each "costly" label is one RSS sample of +0.15 to +0.56 GiB with the
  guard inactive. Native Conductor peaks alone span 9.75–10.24 GiB.
  Treat these labels as not measured.
- Stirling-PDF comparisons are unreliable (run-9: 725, 391 and 4.45 s
  on unchanged builds).
- The `globalCutGrowth` fixture ends at 4 pairs instead of 6 in at
  least 13 unrelated prototypes. "R42 6 → 3" is weak.

## 4. What the real cases need

Reports are final at run-3 (OWASP) or run-5 (Conductor, Stirling-PDF).
Later runs add zero confirmed reports and cost about 21%, 77% and 89%
of the driver time. The runtime keeps no memory of demand between
runs, and the stop test reads only "is the demand empty".

Thus the cheapest lever is the stop policy in the driver, not the fact
rules. A replay on 2,083 archived analyses shows that stopping at the
first forward run `i ≥ 5` without a new confirmed report loses zero
confirmed reports and saves 3,267 s of 5,473 s engine time on the
eight HEAD project launches. The remaining cost is single runs
(Conductor run-6, Stirling-PDF run-9), which no stop test removes. The
proposal has the design, its limits and its gates.
