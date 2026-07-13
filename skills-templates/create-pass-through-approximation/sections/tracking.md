{% include "shared/tracking/approximations-batch.md" %}

This skill only appends each cleanly-built method to `build.done` as `{ method, signature }`. A method that you failed to write stays out, so the loop comes back to it. Never touch the classification buckets or an entry already in `build.done`.
