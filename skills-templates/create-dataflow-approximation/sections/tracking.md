{% include "shared/tracking/approximations-batch.md" %}

This skill appends each method whose sample passes to `build.done` as `{ method, signature }` when absent. A newly assigned method that still fails, or one the engine provably can't propagate, stays out and is reported (per Output); an explicitly repaired method leaves its existing entry unchanged. Don't touch the classification buckets (`passthrough`/`dataflow`/`skipped`/`engine_issues`) or edit an entry already in `build.done`.
