Begin by asking the user both things in a single AskUserQuestion call — two questions, scan level and triage level, presented together (never one call then another). Record the chosen `scan_level` and `triage_level` in `state.yaml`. The target language is not asked — `build-project` detects it and you record it in `state.yaml.language` (references/build.md), then name it on every later dispatch.

1. Scan level — `lite` · `normal` · `deep`
   - lite — build + scan with existing rules
   - normal — + approximation iteration
   - deep — + discover project-used sources, sinks from the taint frontier, and new lib rules
   - recommend by what's on disk: a cold start (no usable `.opentaint` artifacts) → deep, to build full coverage; a prior run's artifacts already present (model, rules, approximations) → lite, to reuse that coverage
2. Triage level — `static` · `dynamic`
   - static — classify findings from the model, no running app
   - dynamic — + a PoC per confirmed TP. This launches a few test services on the user's current machine (local instances and ports); they're torn down at the end of the run. Make that clear in the option

The run is one fixed pipeline; the two levels decide which steps execute. Walk it top to bottom — when you reach a step your levels include, load its reference and do it; skip the steps your levels omit. Don't load a step's reference until you reach it. At every gate `verify.py status` names the resume step and its next action for you (Scripts), so you never track position by hand.

```
build → references/build.md | every run
discover sources + source rules → references/source-rules.md | deep scan
scan → references/scan.md | every run
approximation iteration → references/approximations.md | normal, deep scan
author sinks + assemble + rescan  → references/sink-rules.md | deep scan
triage (generate findings + classify) → references/triage.md | every run
PoC + assemble vulnerabilities → references/poc.md | dynamic triage
```

From inside any step, when a rule or approximation won't behave, load references/escalation.md.
