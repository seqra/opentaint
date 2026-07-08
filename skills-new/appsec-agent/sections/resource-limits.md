`verify.py status --full` prints the caps for this machine — `caps: global=<n> heavy=<n>` — recomputed on every call, so read them there rather than deriving them:

- global cap — never dispatch more than this many subagents at once, of any kind; bursting more reliably trips transient rate-limiting. Treat it as a ceiling and drop it by 1 for the rest of the run each time a subagent comes back rate-limited
- heavy cap — the RAM-heavy agents each spawn a heavy `opentaint` JVM (~2 GB), so they take a tighter bound on top of the global cap. The heavy set is exactly `build-project`, `run-scan`, `create-rule`, `create-dataflow-approximation`, and sometimes `debug-rule` (when it traces a real scan); never dispatch more than `heavy` of them at once

It's machine state, not run state — `verify.py` recomputes it each time, so don't track it. PoC is already sequential.
