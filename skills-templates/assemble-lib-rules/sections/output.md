### Artifacts

- zero or more extension join files under `.opentaint/rules/<lang>/security/`, only for concrete source-to-sink combinations not already covered through an existing rule/tag join
- `.opentaint/tracking/rules/joins/<class>.yaml` — one per vuln class, recording the concrete components covered by existing and created joins (per Tracking)

### Summary

- one line per vulnerability class: concrete source/sink counts, reused tag-expanded joins, and any extension join created
