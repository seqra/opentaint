---
name: discover-universal-boundaries
description: Generalize a family of known finding traces into one reusable source and one reusable sink boundary, saturated against the whole family. Use before rule authoring when reproducing supplied findings, consolidating finding-specific rules, or replacing an incidental source such as a map access or an arbitrary method call
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Discover universal boundaries

Generalize one family of known finding traces into rule-ready boundaries: a single source and a single sink that every finding in the family factors through.

The goal is not the broadest syntax that happens to match every trace. It is the most primitive semantic boundary that stays inside the vulnerability class — general enough that the family needs one rule per side, specific enough that the rule still means something. Precision is recovered afterwards with context restrictions and sanitizers, listed separately, never by narrowing the boundary back down to the findings you started from.

A boundary is only universal once it has been saturated: widened, re-checked against the whole family, and left unchanged by a full round.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions
- `findings` (required) — path to the supplied finding manifest or report the reference set was normalized from
- `finding-ids` (required) — the reference finding ids assigned to this family. Their normalized files are `.opentaint/tracking/reference/<id>.yaml`
- `family` (required) — kebab-case name of the family; also the name of its spec and of the rule units seeded from it

## Workflow

### 1. Reconstruct every trace

For each assigned finding, read its reference file and then the project source it points at, and record:

1. the attacker or untrusted authority;
2. the first project-visible ingress;
3. the transformations and trust-domain crossings on the way;
4. the validators, guards, and authorization decisions it passes;
5. the primitive security-relevant effect at the end; and
6. the vulnerable invariant that is absent or defeated.

Read enough surrounding source to tell the real boundary from incidental syntax. A getter, collection lookup, DTO accessor, or service method is usually propagation or context, not ingress.

### 2. Propose the source

Move backward from the finding-specific expressions until you reach the earliest reusable trust-boundary value the family shares. Prefer, in order when applicable:

- request body, parameter, path, query, header, cookie, or multipart value;
- message, frame, packet, event, webhook, or callback payload;
- deserialized external object;
- persisted attacker-controlled record at a second-order re-entry boundary;
- tenant or user-controlled configuration at activation or read-back;
- environment or runtime configuration entering a security decision; or
- an explicit structural pseudo-source standing for attacker-selected identity or control state.

Reject a candidate that is merely a map or collection read after untrusted data has already entered (`$MAP.get(...)`, `$M[$K]`), a `$METAVAR.method(...)` with no boundary type, signature, declarative marker, or enclosing entrypoint, a ubiquitous getter that would taint trusted objects just as readily, or an internal carrier that ordinary propagation or a later approximation should handle.

Express narrow usage conditions separately, as typed patterns, the language's declarative markers, `pattern-inside`, and `...`. Never bake incidental access syntax into the source. On Go there is no annotation to lean on: a boundary is identified by its receiver type and the package it comes from, so the `import` guard that scopes it is part of the condition rather than a marker on the declaration.

### 3. Propose the sink

Move forward from the finding-specific service calls to the most primitive operation that realizes the vulnerability, while staying specific to its class. Prefer boundaries such as:

- network connect, request, send, or download for SSRF;
- process, script, expression, template, query, or deserialization execution for injection;
- path resolution plus filesystem read/write for traversal;
- privileged object read or disclosure for IDOR and data exposure;
- privileged object mutation or durable state commit for integrity and authorization failures;
- authentication or authorization decision for control bypass;
- redirect or token release for redirect and OAuth issues;
- signature verification or unsigned callback state commit for callback integrity;
- secret activation, credential construction, or outbound use for secret exposure; and
- logger argument consumption for log injection.

Don't stop at a controller-to-service call when the primitive effect is analyzable deeper in the project or a reusable library sink can express it. Use a structural sink only when the vulnerability *is* the missing control at that boundary, or when deeper propagation is genuinely unavailable.

### 4. Saturate

A boundary proposed from a few traces is a guess until it survives the whole family. Loop until a full round changes nothing.

Each round:

1. Factor every assigned finding — not only the new ones — through the current boundaries:

   ```text
   universal source -> finding-specific context -> propagation -> universal sink
   ```

2. For each finding that does not factor, generalize the offending side by exactly one step toward a more primitive boundary — never by adding a second alternative that merely spells out that finding's syntax. A `pattern-either` listing one branch per finding is the failure this skill exists to prevent.
3. Re-check the findings that already factored. A widening that breaks an earlier factorization is a widening too far: back it out and split instead.
4. Challenge the widened boundary in both directions — if the sink now admits a different vulnerability class, narrow it back to the primitive effect or add a class-specific context restriction; if the source now admits trusted values, record what separates them as a context restriction rather than shrinking the boundary.
5. Record the round: what changed, and which factorization statuses moved.

The family is saturated when a full round widened nothing, broke nothing, and left every assigned finding either `covered` or `needs-restriction` with a named restriction. Stop and split — or record the finding `unfactored` with the evidence in `open_questions` — rather than looping a fourth time on the same finding.

When the only boundary the whole family shares is arbitrary syntax, the family was wrong: split it. Each subfamily gets its own spec named `<family>-<qualifier>` and its own saturation loop, every assigned finding lands in exactly one subfamily, and each moved finding's reference file has its `family` rewritten to the subfamily that now owns it.

Keep independently triggerable paths distinct in the factorization even when they share both boundaries.

### 5. Identify the precision controls

List these separately from the positive boundaries — they are what the controls stage lands later, and they must never be folded into the boundary patterns:

- sanitizers that actually enforce the relevant invariant;
- `pattern-not` exclusions for safe expression forms;
- `pattern-not-inside` exclusions for safe guarded regions;
- `pattern-inside` contexts that constrain a universal boundary to the intended entrypoint, type, tenant, or vulnerability family; and
- validators that are *not* security-relevant, recorded explicitly so nothing later mistakes them for sanitizers.

Real sanitization looks like resolved-IP private-range rejection for SSRF, canonical-path containment for traversal, strict identifier ownership checks for IDOR, signature verification for callbacks, and CR/LF neutralization for log injection. Presence, length, parsing, or a declarative validation marker such as `@Valid` alone normally sanitizes none of these.

### 6. Write the specification

Write one spec per family or subfamily. `candidate_patterns` must be concrete enough for `create-rule` to test, in the member shape that language's rule units use — on `java` a fully-qualified method with its JVM descriptor, or the annotation and type that identify the boundary; on `go` `<import-path>.<Member>` or `(*pkg.Type).Method` with `signature` empty, since Go has neither descriptors nor overloads. The pattern shapes those units become live in `create-rule`'s `references/<language>.md`, plus `references/go-semgrep-examples.md` on Go. Record opaque carriers under `approximation_candidates`, and stop there: no approximation is created or recommended until a rule-first scan proves a trace stops at one.

## Output

Return every spec path written (one per family or subfamily) and, in a few lines each:

- the universal source, and which more incidental candidates you rejected;
- the universal sink, and the vulnerability-class scope it stays inside;
- how many saturation rounds it took and what the last round changed;
- the assigned finding ids by factorization status — `covered`, `needs-restriction`, `unfactored`;
- any family split, with the ids that moved and the reference files you rewrote;
- the sanitizers, negative patterns, and context restrictions listed for the controls stage; and
- unresolved boundary evidence, as the `open_questions` entries.

Never paste file contents.

## Tracking

This skill writes the boundary spec for its family, and — only when a split moves a finding — the `family` field on the reference files it moved. Leave `stages.units_seeded` pending: seeding the rule units is the calling stage's step. Touch no other reference field, no rule unit, and no rule.

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

## Constraints

- Work only the assigned finding ids, your family's spec, and the reference `family` field on a split
- Universal does not mean untyped or unconstrained — generalize the boundary, then recover precision with context restrictions and sanitizers, never by re-narrowing the boundary to the findings
- Never propose all methods, all map values, or all getters as a source, and never a `pattern-either` with one branch per finding
- Never mark the spec saturated on a round that widened, broke, or split anything
- Never propose a sanitizer that would suppress a trace the reference set says is real, and never record a validator as a sanitizer without the invariant it enforces
- Record a poor taint fit as an explicit pseudo-boundary; never drop the finding
- Don't create or recommend approximations here — note the opaque carriers and stop
