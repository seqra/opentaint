{% include "shared/tracking/approximations-batch.md" %}

This skill only appends each cleanly-built method to `build.done` as `{ method, signature }` when absent. A newly assigned method that you failed to write stays out, so the loop comes back to it; an explicitly repaired method leaves its existing entry unchanged. Never touch the classification buckets or edit an entry already in `build.done`.
