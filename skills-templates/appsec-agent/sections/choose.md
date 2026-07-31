### The pipelines compose

They are not alternatives, and picking one is not a commitment. One `.opentaint/` tree accumulates the artifacts of every pass over it, in either order and as many times as the project needs:

- **enactment, then assessment** — reproduce the supplied report first, then hunt with the rules it produced. The boundaries derived from real findings are exactly the sources and sinks the assessment pass would otherwise have to discover
- **assessment, then enactment** — assess the project, then measure a report against the corpus that pass built. What the report names but the scan missed is now a rule or modeling gap you can point at
- **either, again on a later commit** — the tree is long-lived. A new HEAD makes the model stale, so the pass rebuilds and rescans, and every rule, approximation, and verdict carries over. That's how a run becomes a regression check rather than a one-off

So `mode` in `state.yaml` is the pipeline of the *current pass*, not a property of the tree. Switching it is normal, needs no fresh tree, and strands nothing.

### Read what the tree already holds

If `.opentaint/tracking/state.yaml` exists, find out where the project stands before choosing:

```bash
uv run <skill-dir>/scripts/get_status.py --full
```

Its header prints the current `mode`, the run's levels, the tracked finding set if there is one, and — once the tree has more than one pass — the `passes:` chain. The phase lines say whether that pass is finished or mid-flight.

- mid-flight pass — resume it: hand off to `assessment-agent` for `mode=assessment`, `enactment-agent` for `mode=enactment`. Don't start a different pass over the top of an unfinished one
- finished pass, and the user wants more — that's a new pass, and the choice below applies again
- tell the user what's there either way, in one line: which pass, where it stands, what carried over

### Choose this pass

Decide from what the user brought, then confirm it with them before handing off:

- **enactment** — they supplied findings, a scanner report, penetration-test results, or source-to-sink traces, and want them reproduced, validated, converted into reusable rules, or cross-checked against OpenTaint. "Does OpenTaint catch these?", "reproduce this report", "turn these findings into rules"
- **assessment** — no finding set to measure against; the goal is what the project is vulnerable to. "Find vulnerabilities", "scan this app", "is this endpoint exploitable?"

The signal is whether a finding set exists to be measured against, not the vocabulary. A user who says "audit this against last year's pentest" and has the pentest is enactment; a user who says "reproduce the bug I think is in here" and has only a hunch is assessment.

When the user wants both — reproduce the report *and* find what it missed — say that it is two passes over one tree, recommend enactment first so the assessment inherits its boundaries, and run them one at a time. Never try to drive both in a single pass.
