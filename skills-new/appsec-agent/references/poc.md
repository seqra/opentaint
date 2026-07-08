# PoC

Run PoCs one subagent at a time, never in parallel — concurrent exploits race on shared app state and ports. For each `verdict: TP` finding `verify.py` lists without a PoC:

- first finding: generate-poc with no `base-url` — it builds and starts the app and returns the `base-url` it started
- every later finding: pass that `base-url` so the agent reuses the running instance

Inputs each: `project-root`, `language`, `finding` (the finding file), and `base-url` once known. Each sets `poc` (`confirmed`/`failed`) and appends its outcome to `notes`; a `failed` repro does not flip the verdict. Each registers any instance it starts in `poc-servers.yaml` — that registry, not memory, is what's running. When a finding needs several services, generate-poc brings them up with one `docker compose` registered as a single `compose` entry.

After all PoCs, refresh `.opentaint/vulnerabilities.md` — fold each TP's PoC outcome in, dynamically-confirmed first, the rest marked unconfirmed (a `failed` repro stays a TP). Drop any static-run carry-over.

Then tear down yourself (don't dispatch): read `poc-servers.yaml` and stop every instance — `process` → `kill <ref>`, `container` → `docker stop <ref>`, `compose` → `docker compose -f <ref> down` — confirm each `port` is free, and empty the registry. `verify.py status` reports `poc: done` only once every TP is PoC'd and the registry is empty.
