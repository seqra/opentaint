This skill writes only each finding's `verdict` and the reasoning appended to `notes`. A split additionally creates a new finding file — a fresh docker-like name, the moved `sarif_hashes`, and `rule_id` copied from the bundle, carrying the seeded analyzer report into its `notes` and leaving `poc` pending. Never touch the `poc` field, or the `sarif_hashes` of a finding you keep.

{% include "shared/tracking/findings.md" %}
