{% include "shared/engine/facts.md" %}

- This stage finds only sources — the methods where untrusted data enters; sinks are found later from the taint frontier.
- Work only your own plan and the source units its packages map to — never another agent's plan or unit, and never `coverage.yaml`. Plans partition packages disjointly, so each source unit has a single writer.
- Stored / second-order injection (data persisted then read back) is modeled by the engine itself — don't record a source for the read-back or a propagator for the store→read path.
- For a generic project the analyzer treats every public/protected method of a public class as an entry point.
