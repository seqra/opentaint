`.opentaint/tracking/rules/joins/<class>.yaml` — one file per vuln class (class = filename), listing concrete source/sink refs and the existing or created security joins that cover them, verified later by the main scan. Tags are expanded before writing this state: `sources` and each `sink` remain concrete refs so status checks stay deterministic; several sinks may share one tag-expanded join `rule_id`. Built-in-vs-created is derived by ruleset membership. Keep it clear from comments

```yaml
sources:
  - java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
  - java/lib/spring/webflux-request-source.yaml#webflux-request-source
joins:
  - rule_id: java/security/ssrf.yaml:ssrf
    sink: java/lib/spring/webclient-ssrf-sink.yaml#webclient-ssrf-sink
  - rule_id: java/security/ssrf.yaml:ssrf
    sink: java/lib/generic/ssrf-sinks.yaml#java-ssrf-sink
stages:
  written: done
  verified: pending
```
