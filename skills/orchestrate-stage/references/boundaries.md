# Universal boundaries

Generalize each family intake produced into one saturated universal source and one universal sink, and seed the source and sink units those boundaries imply. Every mode runs this stage: the families differ — a swept frontier, a diff or spec, a supplied finding set — but what comes out is the same universal rule material, and everything it writes feeds the ordinary rule-authoring stages.

Read the family list from `get_status.py`, which takes it from `.opentaint/tracking/scope.yaml` in onboarding and discovery mode, and from the reference findings' own `family` field in enactment mode.

## Discover the boundaries

Fan out discover-universal-boundaries, one leaf per family.

Inputs each:
- `language`
- `family`
- `evidence` — the ids the family carries: reference finding ids in enactment mode, the members or code areas `scope.yaml` recorded otherwise
- `findings` (enactment mode) — the supplied-findings path `state.yaml` names, so a leaf can read a finding beyond its normalized file

Expect back — `.opentaint/tracking/boundaries/<family>.yaml` with `saturation.status: saturated`, one `factorization` entry per assigned evidence item, and the controls listed separately from the positive boundaries. A leaf that splits its family writes one spec per subfamily; in enactment mode it also rewrites `family` on each reference finding it moved, and otherwise the split is recorded in the specs themselves — reconcile `scope.yaml` to the specs that came back so the family list and the specs still agree.

`.opentaint/tracking/boundaries/<family>.yaml` — one boundary family: the single universal source and single universal sink every piece of the family's evidence factors through, plus the controls that recover precision. `evidence` lists what the family was grouped from — reference finding ids in enactment mode, the members or code areas `scope.yaml` recorded otherwise. `candidate_patterns` are concrete enough for `create-rule` to test, and seed the family's source and sink units verbatim. `factorization` carries one entry per evidence item, `status` one of `covered` (factors through both boundaries as-is), `needs-restriction` (factors only under a named `context_restrictions` entry), or `unfactored` (does not factor — explain in `open_questions` and split or add a pseudo-boundary). `saturation` records the widen-and-recheck rounds and only reads `saturated` once a full round changed neither the boundaries nor any factorization. `approximation_candidates` are opaque carriers noted for later — never acted on before a scan proves the trace stops there. Keep it clear from comments

```yaml
family: ssrf
evidence: [DSC-014, DSC-021]
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

A spec returning with an `unfactored` evidence item is not a failure to retry blindly — read its `open_questions`, and either re-dispatch the leaf with that item split out as its own family or accept the pseudo-boundary it proposes.

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

Copy `method`, `signature`, and `note` from the spec's `candidate_patterns` (plus `vuln_class` on the sink side), leave `rule_id: null` and the `stages` pending, and fill `dependencies` with the dependency each pattern's package comes from — empty when the boundary is a project member, as a structural pseudo-boundary usually is. Do not carry `context_restrictions`, `sanitizers`, or `negative_patterns` into the units: the boundary is the positive pattern, and the controls stay listed in the spec.

Both sides are seeded here, and only the source side is authored before the first scan. That is deliberate: the sink boundary is decided now, on the evidence, and authored later against the frontier that scan names — never invented by a model round that found a carrier.

## Stage gate

`get_status.py` drives `boundaries`, naming families without a spec, unsaturated specs, evidence with no factorization, and unseeded specs. Finish when it reads `DONE`, or when the next step it reports is source rules.
