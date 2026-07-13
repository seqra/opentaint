---
name: generate-poc
description: Reproduce a true-positive finding against the running application. Use when a finding needs dynamic confirmation
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.3"
---

# Skill: Generate PoC

Try to dynamically reproduce the vulnerability found by SAST and confirmed statically. Test it on a running instance via a Python script, and record the outcome

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions
- `finding` (required) — the TP finding to reproduce, `.opentaint/tracking/findings/<name>.yaml`
- `base-url` (optional) — the app's base URL when it is already running; otherwise build and start it

## Workflow

### 1. Start the app

Reuse `base-url` if given. Otherwise build and start the app the way the project expects (possible build and run commands are in the language reference), wait until it's listening (healthy), and note the base URL — the PoC must hit a live instance. When the app needs backing services (DB, broker, cache, …), bring them all up with one `docker compose` on a shared network rather than starting each by hand, and register it as a single `compose` entry. Bind the instance to loopback (per Constraints). Once it's listening, register it (per Tracking) so the orchestrator can reap it later.

### 2. Map the finding to a live request

From the finding's source location find the entry point — the route and method, and the param / header / body field that carries the tainted input — and a payload that drives it to the sink. Some common shapes:

- SQL injection — `?id=1' OR '1'='1`
- command injection — `?cmd=;cat /etc/passwd`
- path traversal — `?path=../../../etc/passwd`
- XSS — `?q=<script>alert(1)</script>`
- SSRF — `?url=http://169.254.169.254/latest/meta-data/`
- XXE — an XML body with `<!ENTITY xxe SYSTEM "file:///etc/passwd">`

### 3. Write and run the PoC script

Write a self-contained Python script to `.opentaint/pocs/<name>.py` that does any setup (auth, seed state), sends the request, and asserts the observable evidence — so it's re-runnable and self-checking. Run it. Confirmation needs observable proof — e.g. rows returned, file contents, command output, a time delay, an out-of-band callback, an injection-revealing error, and so on.

### 4. Record the outcome

- `confirmed` — the script fired and proved the described vulnerability. Set `poc: confirmed` and in `notes` describe the working sequence (setup → request(s) → observed evidence), not just the final request
- `failed` — after several attempts you couldn't confirm the finding, or the app/route couldn't be reached. Set `poc: failed`, save the script, and in `notes` record the variants you tried and why each didn't fire

## Output

### Artifacts

- `.opentaint/pocs/<name>.py` — the PoC script, kept whether it confirmed or not
- `.opentaint/tracking/findings/<name>.yaml` — the finding's `poc` and `notes` updated (per Tracking)
- `.opentaint/tracking/poc-servers.yaml` — the started instance registered, left running for reuse (per Tracking)

### Summary

- the outcome (confirmed / failed) and, if failed, that the finding is unconfirmed; the base URL when you started an instance

## Tracking

This skill writes only the finding's `poc` (`confirmed` / `failed`) and the outcome appended to `notes`; it never changes `verdict` or the other finding fields. When it starts an app instance it appends one entry to the server registry, and stops there — teardown isn't its job.

`.opentaint/tracking/findings/<name>.yaml` — one finding, bundling one rule's SARIF results and carrying it through triage and PoC. A script seeds each file from the scan — its `sarif_hashes`, `rule_id`, and the analyzer report in `notes`. Triage sets `verdict` and appends its reasoning. The PoC stage sets `poc` and appends its outcome. Keep it clear from comments

```yaml
sarif_hashes: [a1b2c3d4, e5f6a7b8]
rule_id: java/security/sqli.yaml:sqli
verdict: TP
notes: >
  <analyzer report for these results — seeded from the scan>
  triage: @RequestParam orderBy is attacker-controlled; reaches ${} in SelectProvider unsanitized → TP
  poc: logged in as a seeded user, then GET /api/orders?orderBy=id);SELECT pg_sleep(5)-- delayed ~5s → confirmed
poc: confirmed
```

`.opentaint/tracking/poc-servers.yaml` — the registry of app instances started for PoCs, read by the orchestrator to tear them down. One entry per instance: `kind` (`process | container | compose`), `port`, and the matching `ref` (a pid, a container id/name, or a compose file path) that gives the stop command. PoCs run one at a time, so appends never race. Keep it clear from comments

```yaml
servers:
  - kind: process
    port: 8080
    ref: "12345"
```

## Constraints

- Bind a started instance to loopback (or a specific IP the test genuinely needs), never `0.0.0.0` or a public interface — a live exploit must stay off-host
- Don't stop an instance you started, and always register it — the orchestrator owns teardown and can only reap what's in `.opentaint/tracking/poc-servers.yaml`
- The outcome goes in the finding file only — never write `.opentaint/vulnerabilities.md`

## Gotchas

- Reproduce, don't theorize — a script you didn't run, or a 200 with no observable effect, is not a confirmation
- failed ≠ false positive — couldn't-reproduce isn't proof the code is safe (auth, missing state, wrong payload). Record `failed` and DO NOT flip `verdict` here
