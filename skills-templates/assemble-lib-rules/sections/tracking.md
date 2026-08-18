This skill writes the joins tracking, one file per vuln class, setting each file's `stages.written: done`. Record concrete source/sink refs after expanding tags so deterministic status checks don't need to reimplement rule loading. The main scan verifies the joins; don't touch `verified`.

{% include "shared/tracking/joins.md" %}
