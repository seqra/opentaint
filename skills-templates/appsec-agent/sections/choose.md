### An in-flight run decides for you

If `.opentaint/tracking/state.yaml` already exists, the tree is already committed to a mode and the choice is made — resume that pipeline. Read the mode from status rather than by hand:

```bash
uv run <skill-dir>/scripts/get_status.py --full
```

Its header prints `mode=`, the run's levels, and the current phase. `mode=assessment` → `assessment-agent`; `mode=enactment` → `enactment-agent`. Tell the user what's in flight and where it stands before continuing.

A mode is not switchable: the bootstrap refuses it, because each pipeline's tracking is meaningless to the other — an assessment tree has no reference set behind it, and an enactment tree's rules were never derived from a dependency sweep. If the user genuinely wants the other pipeline over the same project, that is a fresh `.opentaint/` tree, and say so plainly rather than starting one silently.

### A fresh run

Decide from what the user brought, then confirm it with them before handing off:

- **enactment** — they supplied findings, a scanner report, penetration-test results, or source-to-sink traces, and want them reproduced, validated, converted into reusable rules, or cross-checked against OpenTaint. "Does OpenTaint catch these?", "reproduce this report", "turn these findings into rules"
- **assessment** — everything else: no finding set, the goal is what the project is vulnerable to. "Find vulnerabilities", "scan this app", "is this endpoint exploitable?"

The signal is whether a finding set exists to be measured against, not the vocabulary. A user who says "audit this against last year's pentest" and has the pentest is enactment; a user who says "reproduce the bug I think is in here" and has only a hunch is assessment.

When it's genuinely ambiguous — a report exists but the user wants new findings too — ask. Don't fold both into one run: pick the pipeline they care about now, and note that the other is a separate run over its own tree.
