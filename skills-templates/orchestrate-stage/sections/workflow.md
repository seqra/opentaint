Match the stage keyword to its reference and read it fully:

```
intake       → <skill-dir>/references/intake.md
boundaries   → <skill-dir>/references/boundaries.md
sources      → <skill-dir>/references/sources.md
approx-round → <skill-dir>/references/approx-round.md
sinks        → <skill-dir>/references/sinks.md
triage       → <skill-dir>/references/triage.md
poc          → <skill-dir>/references/poc.md
crossref     → <skill-dir>/references/crossref.md     (a tree carrying a reference set)
escalation   → <skill-dir>/references/escalation.md
```

`intake` is the only stage whose work depends on the run's `mode`; its reference carries a section per mode. Everything after it reads the same whichever mode produced the families.

Run the bundled script to get the setup overview before proceeding to the reference's instructions:

```bash
uv run <skill-dir>/scripts/get_status.py --full
```

Use `uv run <skill-dir>/scripts/get_status.py` at a stage gate or join, or when an updated list of remaining work is needed. It is the read-only view of the current stage.

Finish with one concise summary: counts completed and terminal items with one-line causes. Never paste file contents.
