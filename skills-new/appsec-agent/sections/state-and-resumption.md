You write only the small state the tree can't derive — the knobs in `state.yaml` (`scan_level`, `triage_level`, `language`, `model_commit`, `build_jdk`, `max_memory`), the `history.yaml` audit log, and `vulnerabilities.md`. There is no phase map to maintain: `verify.py` derives every phase's state live from the artifacts, so nothing on disk can lie about progress.

Append one entry to `history.yaml` when a fresh run starts (model commit + levels), not on resume.

On start, and after any compaction or re-invocation, reconstruct position with one command — `uv run scripts/verify.py status --full`. It reads `state.yaml`'s levels and the whole tree and reports the resume phase, the `next:` action, and any integrity warning. Don't hand-walk the tree; act on what it reports:

- an interrupted run resumes at the first unfinished phase — reuse the `done` phases' artifacts as-is
- a re-invocation over evolved code shows up as `build: stale` (HEAD moved past `model_commit`) — rebuild, then let each downstream stage re-derive from the new model: a re-run of triage-dependencies/discover re-plans only members no prior run verdicted, and the findings script carries verdicts across the rescan by hash

Reuse over regeneration. The `.opentaint/` tree is long-lived — reuse what's there, re-derive only what the current code forces. The function approximations are trusted: a method already in a batch's `build.done` is never re-derived, and every existing approximation is applied on every scan (references/scan.md). Everything code-coupled — the model, the lib rules and joins, the findings — is reused as a baseline and re-validated against the current code: refine in place, author from scratch only for genuinely new surface. When a rescan shifts a finding's hash but the vulnerability is unchanged, the findings script surfaces it as a fresh `pending` finding under the same rule for triage to reconcile by flow, rather than clobbering the prior verdict (references/triage.md).
