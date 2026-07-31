### Artifacts

- `debug-ifds-fact-reachability.sarif` — the per-instruction fact-reachability trace the CLI emits next to the `-o` SARIF

### Summary

- the diagnosis: `file:line` and the instruction where taint is killed (or spuriously introduced), and which of the three causes owns the fix
- for an engine cause: the fact-reachability trace up to the last reachable fact (consumed by the engine-issue report), plus the exact debug command(s) and the model they ran against
