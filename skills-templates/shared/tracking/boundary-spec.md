`.opentaint/tracking/boundaries/<family>.yaml` — one boundary family: the single source and single sink every finding in the family factors through, plus the controls that recover precision. `candidate_patterns` are concrete enough for `create-rule` to test, and seed the family's source and sink units verbatim. `factorization` carries one entry per assigned reference finding, `status` one of `covered` (factors through both boundaries as-is), `needs-restriction` (factors only under a named `context_restrictions` entry), or `unfactored` (does not factor — explain in `open_questions` and split or add a pseudo-boundary). `saturation` records the widen-and-recheck rounds and only reads `saturated` once a full round changed neither the boundaries nor any factorization. `approximation_candidates` are opaque carriers noted for later — never acted on before a scan proves the trace stops there. Keep it clear from comments

```yaml
family: ssrf
findings: [DSC-014, DSC-021]
source:
  semantic_boundary: external request value entering a controller
  candidate_patterns:
    - { method: org.springframework.web.bind.annotation.RequestBody, signature: null, note: annotated controller parameter }
  context_restrictions: []
sink:
  semantic_boundary: outbound HTTP request with a caller-supplied URL
  candidate_patterns:
    - { method: org.springframework.web.client.RestTemplate#getForObject, signature: "(Ljava/lang/String;Ljava/lang/Class;[Ljava/lang/Object;)Ljava/lang/Object;", vuln_class: ssrf, note: egress with attacker URL }
  context_restrictions: []
sanitizers: []
negative_patterns: []
factorization:
  DSC-014: { source: request body callbackUrl, sink: RestTemplate#getForObject, status: covered }
  DSC-021: { source: request param targetUrl, sink: RestTemplate#getForObject, status: needs-restriction, restriction: admin-only controller }
approximation_candidates: []
open_questions: []
saturation:
  rounds: 3
  status: saturated
stages:
  units_seeded: done
```
