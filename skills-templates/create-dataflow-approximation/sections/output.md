### Artifacts

- `.opentaint/dataflow/<batch>` — the batch's approximation project: its pinned dependencies plus the code approximation source(s), one `@Approximate` class per target class, that the scan consumes; report the path and the exact test command used
- the passing methods present in the batch file's `build.done` (new methods appended; repaired methods already recorded, per Tracking)

### Summary

- the methods modeled and the test status (passing / non-converging)
