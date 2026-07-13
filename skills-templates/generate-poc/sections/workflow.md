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
