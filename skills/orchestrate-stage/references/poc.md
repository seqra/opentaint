# PoC

Dynamically reproduce each statically-confirmed TP on a running application, refresh the vulnerability report, and tear the test instances down.

## Dispatch generate-poc serially

Run one at a time — the exception to parallel fan-out, since instances share application state and ports. For each TP finding `get_status.py` lists without a PoC:

Inputs:
- `language`
- `finding`
- `base-url` (optional) — omit for the first finding so it starts the application and returns the base URL; pass that URL to later findings to reuse the instance

Expect back — the finding's `poc` set to `confirmed` / `failed` (`failed` stays a TP), and any started instance appended to `.opentaint/tracking/poc-servers.yaml`.

## Refresh the report, then tear down

Once every TP has an outcome, refresh `.opentaint/vulnerabilities.md`: fold each TP's PoC outcome in, dynamically-confirmed first, the rest unconfirmed, and drop the `Previously PoC-confirmed (not re-verified)` carry-over section.

Then read `.opentaint/tracking/poc-servers.yaml` and stop every instance — `process` → `kill <ref>`, `container` → `docker stop <ref>`, `compose` → `docker compose -f <ref> down` — confirm each port is free, and empty the registry.

## Stage gate

`get_status.py` reports `poc` `DONE` when every TP has a PoC outcome and the instance registry is empty; otherwise it lists the remaining findings or teardown.
