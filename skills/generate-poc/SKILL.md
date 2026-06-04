---
name: generate-poc
description: Reproduce a true-positive finding against the running application. Use when a finding needs dynamic confirmation
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Generate PoC

Try to make the vulnerability actually fire on a running instance via a Python script, and record the outcome — confirmed or failed

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Finding `<finding>` — the TP finding file. Default: `.opentaint/tracking/findings/<name>.yaml` (name is required)
- Project root `<project-root>` — sources to build and run. Default: current directory
- App endpoint `<base-url>` (optional) — base URL if the app is already running
- PoC directory `<poc-dir>` — where the PoC script is saved. Default: `.opentaint/pocs`

## Workflow

### 1. Start the app

Reuse `<base-url>` if given. Otherwise build and start the app the way the project expects (`spring-boot:run`, `java -jar`, `docker compose`, …), wait until it's listening, and note the base URL. The PoC must hit a live instance

When the app needs backing services (DB, broker, cache, …), bring them all up with one `docker compose` on a shared network rather than starting each by hand, and register it as a single `compose` entry

Bind to `127.0.0.1` (`--server.address=127.0.0.1`, `docker run -p 127.0.0.1:8080:8080`, a compose override on the port mapping) — never `0.0.0.0` or a public interface: a live exploit must not be reachable off-host. A specific non-local IP is fine when the test genuinely needs one, but never the public wildcard

Once it's listening, record it in the registry (see § Tracking) so the orchestrator can reap it later

### 2. Map the finding to a live request

From the finding's source location find the entry point — the route and method, and the param / header / body field that carries the tainted input — and a payload that drives it to the sink. Common shapes:

- SQL injection — `?id=1' OR '1'='1`
- command injection — `?cmd=;cat /etc/passwd`
- path traversal — `?path=../../../etc/passwd`
- XSS — `?q=<script>alert(1)</script>`
- SSRF — `?url=http://169.254.169.254/latest/meta-data/`
- XXE — an XML body with `<!ENTITY xxe SYSTEM "file:///etc/passwd">`

### 3. Write and run the PoC script

Write a self-contained Python script to `<poc-dir>/<finding_name>.py` that does any setup (auth, seed state), sends the request, and asserts the observable evidence — so it's re-runnable and self-checking.

Run it. Confirmation needs observable proof — rows returned, file contents, command output, a time delay, an out-of-band callback, an injection-revealing error and so on

### 4. Record the outcome

- confirmed — the script fired and proved the vuln. Set `poc: confirmed`, record `poc_script`, and in `notes` describe the working sequence (setup → request(s) → observed evidence), not just the final request
- failed — after several attempts you couldn't confirm the finding, or the app/route couldn't be reached. Set `poc: failed`, save the script, and in `notes` record the variants you tried and why each didn't fire

## Output

- The PoC script at `<poc-dir>/<finding_name>.py`
- The finding's `poc` set to `confirmed` or `failed`, `poc_script` recorded, evidence/reason in `notes`
- If you started the app, register it in `.opentaint/tracking/poc-servers.yaml` and leave it running so the next PoC can reuse it; report the `<base-url>`. You do not stop it — the orchestrator tears down every registered instance at the end of the PoC phase
- Report the outcome to the caller; if failed, call out that the finding is unconfirmed. Do not write `.opentaint/vulnerabilities.md` — main assembles that from the confirmed findings

## Tracking

If you started an instance, append it to `.opentaint/tracking/poc-servers.yaml` (PoCs run one at a time, so the append never races) — the orchestrator reads this to tear instances down (`kind` + `ref` give it the stop command):

```yaml
servers:
  - kind: process                     # process | container | compose
    port: 8080
    ref: "12345"                      # pid | container id/name | compose file path
```

In `<finding>`, set `poc` and `poc_script` and append the result to `notes`:

```yaml
poc: confirmed                        # confirmed | failed
poc_script: .opentaint/pocs/brave-hopper.py
notes: >
  <existing notes>
  poc: logged in as a seeded user (POST /login), then GET /api/orders?orderBy=id);SELECT pg_sleep(5)--
  — the injected ORDER BY delayed the response ~5s while a benign orderBy=id returned instantly → time-based SQLi confirmed
```

Failed instead — narrate the attempts, not a single request:

```yaml
poc: failed
poc_script: .opentaint/pocs/brave-hopper.py
notes: >
  <existing notes>
  poc: tried ' OR 1=1--, a UNION SELECT, and time-based pg_sleep on /api/orders and /api/orders/search;
  every variant returned 400 — orderBy is whitelisted to column names server-side → could not reproduce
```

## Gotchas

- Reproduce, don't theorize — a script you didn't run, or a 200 with no observable effect, is not a confirmation
- failed ≠ false positive — couldn't-reproduce isn't proof the code is safe (auth, missing state, wrong payload). Record `failed` and DO NOT flip `verdict` here
- Don't bind a started instance to `0.0.0.0` or a public interface — a running exploit must stay off-host (localhost, or a specific IP the test needs)
- Don't stop instances you started or skip registering them — the orchestrator owns teardown and can only reap what's in `poc-servers.yaml`
