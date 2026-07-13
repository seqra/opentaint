# PoC

Dynamically reproduce each statically-confirmed TP on a running app instance — the run's last stage, reached only on a dynamic triage level.
Gate: `get_status.py` reports `poc` `DONE` when every `verdict: TP` finding is PoC'd and the instance registry is empty; otherwise it lists the TP findings still without a PoC.

### 1. Dispatch generate-poc, serially

Run one at a time — the one exception to parallel fan-out, since instances share app state and ports. For each TP finding `get_status.py` lists without a PoC:

Inputs:
- `project-root`
- `language`
- `finding` — the TP finding file to reproduce
- `base-url` (optional) — omit for the first finding so it starts the app and returns the `base-url`; pass that `base-url` to every later finding to reuse the running instance

Expect back — the finding's `poc` set to `confirmed` / `failed` (a `failed` repro stays a TP), and any started instance appended to `.opentaint/tracking/poc-servers.yaml`; that registry, is what's running.

### 2. Refresh the report, then tear down

Once every TP is PoC'd, refresh `.opentaint/vulnerabilities.md`: fold each TP's PoC outcome in, dynamically-confirmed first, the rest unconfirmed, and drop any static-run carry-over.

Then tear down yourself (don't dispatch): read `.opentaint/tracking/poc-servers.yaml` and stop every instance — `process` → `kill <ref>`, `container` → `docker stop <ref>`, `compose` → `docker compose -f <ref> down` — confirm each `port` is free, and empty the registry.

Run `uv run scripts/get_status.py` to confirm `poc` `DONE`.
