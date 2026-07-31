### 1. Gate

The inputs pick the kind: a `diagnosis` (+ `artifact`) is an `analysis` issue, a `setup` is a `resource` issue.

For an `analysis` issue, write from the caller's brief cause as supplied — don't verify, reproduce, or run anything yourself. This is a first-pass approximate hand-off to the engine team, not a proven diagnosis; whatever the caller gives is enough to write the report.

For a `resource` issue, the gate is simpler: the caller confirms the full-project scan completed its allowed retry/backstop without producing valid SARIF. No taint diagnosis is required — write the report from the setup.

### 2. Write the report

Write `.opentaint/issues/<slug>.md` — the self-contained deliverable, `<slug>` a short kebab-case symptom name. Open with a fixed header so the engine team can triage at a glance, then free-form detail below it.

Header (both kinds):

- Type — `analysis` or `resource`
- Setup — the exact command that reproduces it: the `opentaint test rule …` / `test approximation run` for `analysis`, or the failed `opentaint scan` for `resource`, each with its model, rulesets, and approximation dirs (plus final memory and timeout/backstop outcome for `resource`)
- Run logs — the run's log files, by path: for `analysis`, any debug log or fact-reachability SARIF the caller cited, if present; for `resource`, the scan's output log
- Minimal repro — the smallest set of files/folders that demonstrates it: for `analysis`, the test project `.opentaint/test-projects/<name>` if one was named; for `resource`, the project model, rulesets, and approximation dirs in play (with their rough size)
- TL;DR — 2–3 sentences: the symptom, and for `analysis` where taint appears to die and what the engine should do instead

Below the header, free-form — whatever makes the case, at least:

- `analysis` — the `artifact` under test (rule id + ruleset, or approximation target method(s)); the caller's brief cause; observed vs expected and any fact-reachability trace, if the caller supplied them; a 1–3 sentence hypothesis of what the engine does wrong (a hypothesis, not a fix)
- `resource` — the model's rough size (classes/modules if known) and the commit hash (`git rev-parse HEAD`) it was built from

Keep it tight: the header plus about one screen of body.
