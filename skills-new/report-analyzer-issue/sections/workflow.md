### 1. Gate

The inputs pick the kind: a `diagnosis` (+ `artifact`) is an `analysis` issue, a `setup` is a `resource` issue.

For an `analysis` issue, write only for a diagnosis already confirmed upstream. It must establish all three, if any is missing, return to the caller and ask for debugging first — don't verify or run anything yourself:

- not a rule fix — the rule's patterns are correct, tightening or broadening was ruled out
- not a missing model — no method on the source→sink path remains in `dropped-external-methods.yaml`
- it is the engine — taint is dropped at an instruction the engine should propagate through

For a `resource` issue, the gate is simpler: the caller confirms the scan ran out of memory and produced no valid SARIF even at `--max-memory 16G`. No diagnosis is required — write the report from the setup.

### 2. Write the report

Write `.opentaint/issues/<slug>.md` — the self-contained deliverable, `<slug>` a short kebab-case symptom name. Open with a fixed header so the engine team can triage at a glance, then free-form detail below it.

Header (both kinds):

- Type — `analysis` or `resource`
- Setup — the exact command that reproduces it: the `opentaint test rule …` / `test approximation run` for `analysis`, or the `opentaint scan` that ran out of memory for `resource`, each with its model, rulesets, and approximation dirs (and the `--max-memory` reached, for `resource`)
- Run logs — the run's log files, by path: for `analysis`, the debug log and the `debug-ifds-fact-reachability.sarif`; for `resource`, the scan's output log
- Minimal repro — the smallest set of files/folders that demonstrates it: for `analysis`, the test project `.opentaint/test-projects/<name>`; for `resource`, the project model, rulesets, and approximation dirs in play (with their rough size)
- TL;DR — 2–3 sentences: the symptom, and for `analysis` where taint dies and what the engine should do instead

Below the header, free-form — whatever makes the case, at least:

- `analysis` — the `artifact` under test (rule id + ruleset, or approximation target method(s)); observed vs expected (e.g. expected a finding at `Sink.java:42`, got none); the fact-reachability trace quoted up to the last reachable fact; the three ruled-out causes from the gate; a 1–3 sentence hypothesis of what the engine does wrong (a hypothesis, not a fix)
- `resource` — the model's rough size (classes/modules if known) and the commit hash (`git rev-parse HEAD`) it was built from

Keep it tight: the header plus about one screen of body.
