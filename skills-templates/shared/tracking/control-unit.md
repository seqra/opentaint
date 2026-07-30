`.opentaint/tracking/controls/<unit>.yaml` — one unit of precision work: the sanitizers, negative patterns, and context restrictions to land on a set of rules, plus what proved they were needed. `generate.py controls` seeds and refreshes it, so never create one by hand. The unit is named for its boundary `family` when the rules belong to one and for the rule file stem otherwise (`family: null` then). Each `targets` entry is one piece of evidence — `false-positive` from a triaged finding, `false-negative` from a reference finding the cross-reference blamed on the rule, `precision` from a boundary spec's own controls — and its `status` goes `landed` once the change is in the rule, `dropped` when the evidence turns out not to warrant one. `saturation` only reads `saturated` after a rescan round that fixed its targets without losing a trace or adding a new false positive. A `blocker` string settles a unit that cannot be made to converge. Keep it clear from comments

```yaml
family: ssrf
targets:
  - { rule_id: java/security/ssrf-webhook-ext.yaml:ssrf-webhook-ext, kind: false-positive, evidence: .opentaint/tracking/findings/fuzzy-hopper.yaml, status: landed }
  - { rule_id: java/lib/spring/webclient-ssrf-sink.yaml#webclient-ssrf-sink, kind: precision, evidence: .opentaint/tracking/boundaries/ssrf.yaml, status: pending }
sanitizers:
  - resolved-IP private-range rejection before the request is issued
negative_patterns:
  - URL built from a compile-time constant host
saturation:
  rounds: 2
  status: saturated
stages:
  landed: done
  verified: done
```
