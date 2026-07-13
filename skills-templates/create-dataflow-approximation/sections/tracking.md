{% include "shared/tracking/approximations-batch.md" %}

This skill appends each method whose sample passes to `build.done` as `{ method, signature }`. A method that still fails, or one the engine provably can't propagate, stays out of `build.done` and is reported (per Output), not marked here. Don't touch the classification buckets (`passthrough`/`dataflow`/`skipped`/`engine_issues`) or an entry already in `build.done`.
