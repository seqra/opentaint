`.opentaint/tracking/rules/joins/<class>.yaml` — one file per vuln class (class = filename), each listing the joins written for it (one per sink rule), verified later by the main scan. `sink` is a plain ref; built-in-vs-created is derived by ruleset membership, so no tag is stored, and each join's artifact path is derivable from its `rule_id`. Keep it clear from comments

```yaml
sources:
  - java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
  - java/lib/spring/webflux-request-source.yaml#webflux-request-source
joins:
  - rule_id: java/security/ssrf-webclient-ssrf-sink-lib-ext.yaml:ssrf-webclient-ssrf-sink-lib-ext
    sink: java/lib/spring/webclient-ssrf-sink.yaml#webclient-ssrf-sink
  - rule_id: java/security/ssrf-java-ssrf-sink-lib-ext.yaml:ssrf-java-ssrf-sink-lib-ext
    sink: java/lib/generic/ssrf-sinks.yaml#java-ssrf-sink
stages:
  written: done
  verified: pending
```
