# Demand progress reference

**Design status: the full relational-evidence/call-composition proposal is
withdrawn.** The checks remain mathematical reference artifacts. They do
not prove bounded analysis cost or authorize a parallel unabstracted
field-sensitive analysis. Read the
[withdrawal and bounded next candidate](../../../../docs/design/bidirectional-relational-loss-evidence-proposal-20261113.md)
before using the old handoff or call model as design evidence.

Read the [design investigation](../../../../docs/design/bidirectional-demand-progress-and-termination-20261113.md).
The selected target is proved retirement and precise eventual findings,
without an iteration cap or provisional stopping policy. Field bans are retired.

`Progress.lean` checks a structurally terminating acyclic prefix evaluator,
its exact inductive semantics and program-dependent result bound. It also
checks the raw NORMAL specialization example, the two existing demand-cycle
witnesses, the actual two-call MUST replay and the difference between
unbounded depth and finding precision. The replay checks do not mechanize
the native post-cut scheduler or certify a production deletion predicate.
This is a reference/counterexample component, not a native deletion theorem
or a termination proof for the production analyzer.

```sh
python3 spec/lean/proposals/demand-progress-20261113/check.py \
    --out /tmp/demand-progress-check
```

The package passes 146 audited declarations in seven modules, including
21 new checks. The checker compiles all dependencies in a fresh external directory and
rejects unfinished proofs and nonconstructive/custom axioms. Logs, Lean
objects and source hashes stay external. The successful receipt is
`demand-progress-20261113/proofs-v5/receipt.json` under the
[report data archive](../../../../docs/reports/EXTERNAL_DATA.md).

The [concrete handoff proposal](../../../../docs/design/bidirectional-relational-loss-evidence-proposal-20261113.md)
adds `Handoff.lean`: executable prefix composition, finite evidence
compilation, NORMAL coverage, retirement and uncovered-focus selection.
The 19 new checks prove exact compilation and preservation of every
precise unary prefix observation when the coverage checker accepts. Unknown
origins block retirement; origin arrival order does not affect the check.
Native evidence completeness, STAR-inside service, source/Target routing
and focus-row integration remain explicit adapter obligations.

```sh
python3 spec/lean/proposals/demand-progress-20261113/check.py \
    --handoff --out /tmp/relational-loss-handoff-check
```

This extension passes 165 declarations across eight modules. The external
receipt is `demand-progress-20261113/handoff-proofs-v5/receipt.json`.

`Calls.lean` adds 15 checks for method-relative prefix evidence: explicit
base rebinding, call composition, multiple alternatives, two call sites,
backward binding order, unknown evidence and callee Union updates. The
DEMAND-call checks keep the runtime layer separate from evidence, preserve
the caller operand while its reference is unresolved, and retain cut paths.

```sh
python3 spec/lean/proposals/demand-progress-20261113/check.py \
    --calls --out /tmp/relational-loss-calls-check
```

This includes the handoff checks and passes 180 declarations in nine
modules. Receipt: `demand-progress-20261113/demand-call-proofs-v1/receipt.json`.
It does not mechanize native publication timing or source/cleaner/Target
call stages. The proposal keeps those unsupported paths open.
