# Reference set + universal boundaries

Turn the supplied findings into a normalized reference set, generalize each finding family into one saturated source and sink boundary, and seed the source and sink units those boundaries imply. Enactment mode only — it replaces dependency discovery, and everything it writes feeds the ordinary rule-authoring stages.

## Normalize the reference set

`state.yaml` names the supplied findings under `findings` — a manifest, SARIF, report, or directory of finding documents. Write one `.opentaint/tracking/reference/<finding-id>.yaml` per supplied finding.

`.opentaint/tracking/reference/<finding-id>.yaml` — one supplied finding, normalized to a stable identity and carried through boundary discovery and the cross-reference. The file is named for the finding's own id. `family` ties it to its boundary spec and is rewritten when a family splits. `status` is `pending` until the cross-reference judges it, then `reproduced` or `unreproduced`; `cause` explains an `unreproduced` one so the pipeline knows who owns it — `rule` (a boundary, restriction, or sanitizer is wrong), `approximation` (an opaque carrier breaks the path), or `engine` (a modeling limit, paired with `blocker`). `blocked_at` lists the carriers still to model and is cleared once they are modeled or judged terminal. `matched_hashes` are the SARIF result hashes whose trace carries this finding's identity — never a rule-id match alone. Keep it clear from comments

```yaml
id: DSC-014
vuln_class: ssrf
family: ssrf
source: request body field `callbackUrl` on POST /api/webhook/register
propagation: WebhookReqVO -> WebhookDO -> WebhookService#dispatch
sink: RestTemplate#getForObject in WebhookService#dispatch
expected_location: yudao-module-infra/.../WebhookService.java:88
guards: URL parsed with new URI(...), no private-range rejection
status: reproduced
cause: null
blocker: null
blocked_at: []
matched_hashes: [a1b2c3d4e5f6a7b8]
crossref: done
notes: >
  crossref: join ssrf-webhook-ext fired at WebhookService#dispatch:88 with the trace entering at
  the registration body — same attack path as the reference finding
```

Give each finding a stable id of its own — the supplied one when it has one. Preserve separately triggerable attack paths as separate findings even when they share a sink. Never drop a finding for being a poor fit for taint analysis: an authorization, integrity, configuration, hard-coded-secret, or structural-control finding gets a reference file like any other, and becomes an explicit pseudo-boundary later.

Then group the findings into families and set `family` on each. Partition by vulnerability class or by a cohesive finding family — never by file batches or arbitrary count. A family is the set of findings you expect to share one source and one sink.

Fan out this normalization when the supplied set is large: one leaf per slice of the supplied report, each writing its own reference files. Assign the families yourself once every file exists, since that decision needs the whole set.

## Discover the boundaries

Fan out discover-universal-boundaries, one leaf per family.

Inputs each:
- `language`
- `findings` — the path `state.yaml` names
- `finding-ids` — the ids assigned to this family
- `family`

Expect back — `.opentaint/tracking/boundaries/<family>.yaml` with `saturation.status: saturated`, one `factorization` entry per assigned finding, and the controls listed separately from the positive boundaries. A leaf that splits its family writes one spec per subfamily and rewrites `family` on each reference finding it moved, so every finding still points at the spec that owns it.

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

A spec returning with an `unfactored` finding is not a failure to retry blindly — read its `open_questions`, and either re-dispatch the leaf with the finding split out as its own family or accept the pseudo-boundary it proposes.

## Seed the rule units

For each saturated spec, write its `candidate_patterns` into the family's source and sink units, then set `stages.units_seeded: done` on the spec. The unit file name is the family, so the two sides and the spec stay tied together.

`.opentaint/tracking/rules/sources/<package-kebab>.yaml` — one source unit per package (a dependency can span several packages, each its own unit), the file named for that package with `.` → `-`. `dependencies` names the dependency the package comes from, `sources` each an entry point `{ method, signature, note, rule_id }` (`signature` the member's JVM descriptor, always quoted so array types `[…` stay valid YAML in a flow mapping), `stages` tracks the unit through rule authoring, and a `blocker` string is added under it when the unit can't be made to pass. Keep it clear from comments

```yaml
dependencies:
  - org.springframework:spring-websocket:6.1.0
sources:
  - { method: org.springframework.web.socket.TextMessage#getPayload, signature: "()Ljava/lang/String;", note: untrusted WebSocket frame data, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

`.opentaint/tracking/rules/sinks/<package-kebab>.yaml` — one sink unit per package (a dependency can span several packages, each its own unit), the file named for that package with `.` → `-`. `dependencies` names the dependency the package comes from, `sinks` each a dangerous operation reached by the taint frontier `{ method, signature, vuln_class, note, rule_id }` — `signature` the member's JVM descriptor so overloads stay distinct, always quoted (array types contain `[`, which is invalid unquoted in a flow mapping), `vuln_class` per entry since one package can host several, `note` a few words on the danger, the tainted argument left unpinned. `stages` tracks the unit through rule authoring. Keep it clear from comments

```yaml
dependencies:
  - cn.hutool:hutool-core:5.8.20
sinks:
  - { method: cn.hutool.core.io.FileUtil#writeBytes, signature: "([BLjava/lang/String;)Ljava/io/File;", vuln_class: path-traversal, note: writes data to an untrusted path, rule_id: null }
stages:
  test_project: pending
  tests_passing: pending
```

Copy `method`, `signature`, and `note` from the spec's `candidate_patterns` (plus `vuln_class` on the sink side), leave `rule_id: null` and the `stages` pending, and fill `dependencies` with the dependency each pattern's package comes from — empty when the boundary is a project member, as a structural pseudo-boundary usually is. Do not carry `context_restrictions`, `sanitizers`, or `negative_patterns` into the units: the boundary is the positive pattern, and the controls land later through the controls stage.

## Stage gate

`get_status.py` drives `reference_set` then `boundaries`, naming findings without a family, families without a spec, unsaturated specs, unfactored findings, and unseeded specs. Finish when both are `DONE`, or when the next step it reports is source rules.
