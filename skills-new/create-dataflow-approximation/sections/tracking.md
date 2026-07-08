{% include "shared/tracking/approximations-batch.md" %}

This skill appends each method whose sample passes to `build.done` as `{ method, signature }`. A method still failing, or one you reported as non-converging, stays out so the loop returns to it. Never touch the classification buckets or an entry already in `build.done`.
