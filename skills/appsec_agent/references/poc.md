# PoC

The dynamic-confirmation step, run on a dynamic run after triage. Confirm each TP on a running instance, then assemble the report. Dispatch per the Delegate template in SKILL.md.

Run PoCs one subagent at a time, never in parallel — concurrent exploits race on shared app state and ports. For each TP finding:

- first finding: generate-poc with no `<base-url>` — it builds and starts the app and returns the `<base-url>` it started
- every later finding: pass that `<base-url>` so the agent reuses the running instance

Inputs each time: `<finding>` = the TP finding file, `<project-root>`, poc-dir `.opentaint/pocs`, and `<base-url>` once known. Each sets `poc` (`confirmed`/`failed`) + `poc_script`; a `failed` repro does not flip the triage verdict. After all PoCs, assemble `.opentaint/vulnerabilities.md` from the confirmed findings yourself (subagents never write it; see SKILL.md). Set `phases.poc: done`.
