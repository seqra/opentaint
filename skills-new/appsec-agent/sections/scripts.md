Two bundled helpers carry every deterministic step, so you neither reason it out nor read files by hand. Run both with uv from the project root.

verify.py — read-only, run it freely:

- `uv run scripts/verify.py status` — the current stage only: the first unfinished phase, why it's unfinished, and a `next:` line naming the exact command or subagent to dispatch. Run it at a stage's gate to decide the next move
- `uv run scripts/verify.py status --full` — the whole picture: every phase's state (level-gated, `N/A` when out of scope), the `caps:` line (Resource limits), `integrity:` warnings, and the resume point. Run it at run start, after a compaction or re-invocation, and before a large fan-out
- follow the `next:` line unless `integrity:` reports a problem or a subagent escalated — those are the only cues to open a file and reason. Run it at stage boundaries or to confirm a join, not after every single subagent

generate.py — writes; run only at a fan-out join:

- `uv run scripts/generate.py partition analyze` — dropped external methods → per-batch approximation plans
- `uv run scripts/generate.py partition discover` — coverage.yaml's project-used members → balanced discover plans
- `uv run scripts/generate.py mark-safe` — discover plans' verdicts → the classification.yaml ledger, then prunes the consumed plans
- `uv run scripts/generate.py merge-skipped` — every batch's skipped/engine_issues → approximations/skipped.yaml, then prunes the consumed plans
- `uv run scripts/generate.py findings .opentaint/results/report.sarif` — the scan's SARIF → per-rule finding files (idempotent; a rescan adds new result hashes without clobbering a triaged verdict)

Each step's reference names the script command for that stage. A leaf runs its own self-check (analyze-external-methods runs `check-coverage.py --batch` before returning) — that is the leaf's, not yours.
