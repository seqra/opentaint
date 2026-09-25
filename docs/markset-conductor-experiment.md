# Mark-set shallow scan on Conductor: experiment report

- **Date:** 2026-09-25.
- **Build:** `feat/markset-scan` at `095c132d8`, a single analyzer jar. The baseline is the same jar without `--mark-set-scan`; with the flag off, the code path is identical to main.
- **Spec:** `docs/markset-shallow-scan-spec.md`.
- **Plan task:** 10.

## Setup

**Project and rules.**
- Project: `opentaint-test/opentaint-test-conductor` (legacy `project.yaml`).
- Approximations: the passthrough approximations and `dataflow-compiled`.
- Rules: the bundled `rules/ruleset` plus the Conductor rules.
- Severities: error and warning.

**Invocation.** The analyzer jar is invoked directly, as CI does:
`java -Xmx16g -jar opentaint-project-analyzer.jar --project … --verbosity=DEBUG …`

**Modes.** Each was run 5 times, in interleaved rounds:

| Mode | Flags |
|---|---|
| base | none (baseline: prescan + full scan) |
| fi | `--mark-set-scan` (default: flow-insensitive, relevance on) |
| norel | `--mark-set-scan --mark-set-no-relevance` (forward applicability only) |
| rx | `--mark-set-scan --mark-set-relaxed` (option 4*) |
| fs | `--mark-set-scan --mark-set-flow-sensitive` (option 3*), run once |

**Machine.** 20 cores and 62 GB, shared. During the runs another user's 36 GB JVM used about 7 cores. The table therefore reports **medians over 5 runs**. One norel run and one rx run are outliers at about 2x and are absorbed by the median.

**How the numbers are measured.**
- *Prescan and full scan:* `Analysis done in` of the IFDS engine for each phase, in seconds.
- *Mark-set phase:* the `markset: time=` log line. It covers seal and scan.
- *Events:* the final `Progress: N` of each phase.
- *CPU:* process user + system time.
- *Findings:* compared on `(ruleId, path, startLine, startColumn, codeFlows count)`.

## Results

### Findings

All 21 runs report the **same 6 findings** as the baseline, with identical locations and identical code-flow counts.

### Timings (medians, 5 runs; fs is a single run)

| mode | prescan IFDS, s | mark-set phase, s | full-scan IFDS, s | full-scan events | wall, s | CPU, s |
|---|---|---|---|---|---|---|
| base | 24.1 | — | 20.8 | 540,375 | 85 | 341 |
| fi | 25.5 | 1.89 | 21.9 | 535,430 | 89 | 369 |
| norel | 25.2 | 1.89 | 21.7 | 532,727 | 89 | 373 |
| rx | 24.7 | 2.72 | 21.4 | 540,722 | 90 | 372 |
| fs | 25.7 | 1.66 (then fails open) | 22.0 | 539,600 | 89 | 364 |

### What the default mode selected (fi, identical in every run)

| Quantity | Value |
|---|---|
| Recorded program | 14,103 methods, 24,329 call edges, 1,898,354 sites, 1,258 distinct signatures, 6,472 roots (16 distinct root signature sets), 213 MB recorder estimate |
| Seal + scan | seal about 0.45 s, scan about 1.35 s |
| Needed marks | 320 |
| Source actions kept | **2,100 of 139,584 (1.5%; 98.5% removed)** |
| Source rule instances kept | 1,067 of 137,751 |
| Sinks kept | **22,779 of 1,760,550 (1.3%)** |

For comparison:
- **Without relevance (norel):** 11,065 source actions are kept (7.9%). Forward applicability alone therefore removes 92% of the actions, and the backward relevance pass removes a further 81% of what is left, which is the D4 effect.
- **Option 4* (rx):** 5,079 actions and 854,568 sinks are kept. It is coarser, as expected.
- **Option 3* (fs):** fails open with `flow-sensitive size`. Conductor has 6,472 roots, and the per-root reachable statement count exceeds the 50M guard.

### Coverage check with the production configuration

This run uses `--mark-set-scan --mark-set-debug-checks`. It gave `markset-check: e1=0 e2=0 violations=0` over 28,359 observed full-scan calls and 96,083 observed rule sites (spec §7, E1 and E2), with the same 6 findings.

## Answers to the three questions

1. **How long does the shallow scan take?**
   - The phase itself (seal + scan) takes **1.9 s** in the default mode, which is about **8% of the prescan**.
   - Recording during the prescan adds about **1.4 s**: the median prescan is 25.5 s against 24.1 s.
   - The total cost is about **3.3 s, roughly 14% of the prescan**. That is above the spec's 10% target (§8, Layer 4, gate 2).
2. **How many actions are removed?** **98.5% of source `AssignMark` actions** (2,100 kept of 139,584) and **98.7% of sink instances** are removed, with identical findings.
3. **How does the full scan change?** It **does not get faster**.
   - Full-scan events drop by only **0.9%**.
   - Full-scan time is +1.1 s at the median. That is within the noise of this machine, since the run-to-run spread is ±2 s at the minimum.
   - End-to-end wall time and CPU are slightly higher. The phase cost is not recovered.

## Why the full scan does not get faster on Conductor

These experiments use a throwaway build with unsound knobs. It is **not** on the branch; it lives in a scratch worktree only.

| Selection given to the full scan | full-scan events | full-scan IFDS |
|---|---|---|
| baseline | about 540,000 | about 21 s |
| mark-set (2,100 actions, 320 marks) | about 535,000 | about 22 s |
| keep only the marks of `ssrf.yaml` | 514,419 | — |
| keep only the marks of `sqli.yaml` | 513,641 | — |
| keep only the marks of `xss.yaml` | 512,671 | — |
| keep only the marks of `path-traversal.yaml` | 513,631 | — |
| drop **every** source action | 57,097 | 2.3 s |

Three findings explain the table.

1. **The removed actions were inert.** Their marks never reach an applicable sink, and most belong to Semgrep automaton transitions whose premises never hold. They contributed almost no facts to the baseline full scan, so removing them saves almost nothing.
2. **The needed marks carry all the cost, and marks are not additive.**
   - The kept actions are dominated by seven rules: sqli, ssrf, xss, graaljs, format-string, unsafe-reflection and path-traversal. Each puts its own `$UNTRUSTED` mark on the **same 310 Spring source statements**.
   - Keeping the marks of **any one** of these rules still costs about 95% of the full scan.
   - The reason is how the engine stores facts. An engine fact is a per-base access-path tree that holds all of that base's marks (spec §3), so the engine's work scales with tainted bases and paths, not with marks. Dropping marks helps only when **every** mark on a base disappears.
3. **Conductor has no headroom for rule selection.** Every one of the 6 findings comes from these `$UNTRUSTED` rules. So any selection that preserves the findings still costs about 95% of the baseline full scan, and the 5% lower bound (57k events) is only reachable by dropping findings.

## Conclusions and recommendations

- **Soundness is confirmed on a real project.** The findings are identical across 21 runs, and the E1/E2 checks pass in the production configuration.
- **The selection itself is large:** −98.5% of actions and −98.7% of sinks. It does not translate into full-scan time on Conductor, for the structural reason above.
  - Relevance-based pruning pays off only on projects where some rule's sources taint bases that no needed rule taints.
  - Conductor is not such a project.
  - The corpus-wide Layer 4 gate (spec §8, "selected actions ≤ 60% of the baseline", and "full scan no slower") should be judged on ThingsBoard and `known-projects`. Conductor passes the first criterion and is neutral on the second.
- **The phase cost is above target.** Recording plus the phase is about 14% of the prescan against a 10% target. The largest remaining lever is the recorder input: 1.76M of the 1.9M sites are sinks, and most are identical per method (noted in Task 5+6 fix round 1).
- **Option 3* is not usable on Conductor-sized root sets** as implemented. It fails open by design. This is consistent with spec §9's cost note: roots × points.
- **The next lever for full-scan cost is not rule selection.** It is sharing identical sources across rules. Seven rules taint the same 310 statements with seven distinct marks, and the engine carries all seven marks on the same bases. Unifying equivalent source definitions into one mark, and splitting per rule only at the sinks, is a separate design and outside this spec.
