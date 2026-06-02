# PoC

Run PoCs one subagent at a time, never in parallel — concurrent exploits race on shared app state and ports. For each TP finding:

- first finding: generate-poc with no `<base-url>` — it builds and starts the app and returns the `<base-url>` it started
- every later finding: pass that `<base-url>` so the agent reuses the running instance

Inputs each time: `<finding>` = the TP finding file, `<project-root>`, poc-dir `.opentaint/pocs`, and `<base-url>` once known. Each sets `poc` (`confirmed`/`failed`) + `poc_script`; a `failed` repro does not flip the triage verdict. Each PoC subagent registers any instance it starts in `.opentaint/tracking/poc-servers.yaml` — that registry, not memory, is what's running (so a reuse-or-start decision and teardown both survive compaction).

After all PoCs, assemble `.opentaint/vulnerabilities.md` from the confirmed findings yourself (subagents never write it; see SKILL.md).

Then tear down — you own this, run it directly (don't dispatch a subagent). Read `poc-servers.yaml`; if it lists any instance, ask the user keep-vs-shutdown (default: shut down). Unless they say keep, stop each entry from its `kind` + `ref` (`process` → `kill <ref>`, `container` → `docker stop <ref>`, `compose` → `docker compose -f <ref> down`), confirm its `port` is free, and empty the registry. Only after teardown set `phases.poc: done`.
