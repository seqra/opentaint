---
name: discover-attack-surface
description: Analyze a dependency package for potential sources and sinks not covered by the built-in rules. Use for the depth pass of attack-surface discovery
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Discover Attack Surface

Take one library the triage flagged, find how the project actually uses it, and follow untrusted data from the sources it introduces to the dangerous sinks they reach — recording every flow(s) the built-in rules miss as one rule requirement

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Package `<package>` — the flagged library to drill (a `pending` entry in `coverage.yaml`)
- Project root `<project-root>` — the project sources. Default: current directory
- Project model `<model-dir>` — the built model. Default: `.opentaint/project`
- Tracking directory `<tracking-dir>` — where the coverage record and rule files live. Default: `.opentaint/tracking`
- Loose pieces `<lib-pieces>` — the running list of sources/sinks no package pass could pair yet. Default: `.opentaint/tracking/lib-pieces.yaml`

## Workflow

Requires a built project model — without it you can miss entry points the analyzer actually sees

### 1. Find how the project uses the package

Search threw `<project-root>` sources for `<package>`'s imports and call sites. List the distinct methods of it the app calls — these, not the library's whole API, are the surface that matters

### 2. Source-first: find the sources and the sinks they feed

Among the used methods, find the ones that return attacker-controlled data — e.g. HTTP/RPC request data, message-broker payloads, or second-order rows read back from storage — and the ones that are dangerous operations — e.g. query construction, command/file/path ops, deserialization, template/EL evaluation, LDAP/JNDI, reflection. You don't trace every usage by hand: the analyzer does taint propagation at scan time. Identify what the library introduces, and for a source which dangerous sink classes the app exposes that it could feed — at the category level, not call by call. The sink may live in a different library than the source

Don't drop a library that only introduces sources — a request or HTTP-client library is the common case: its tainted data is consumed by sinks elsewhere you can't all see, so record the source as a loose piece in `<lib-pieces>` (step 3) for assemble-lib-rules to pair. Drop only a candidate that isn't genuinely untrusted

Verify each source is genuinely attacker-controlled (a request param, header, body, or message payload is; an app constant or server config is not) and each sink genuinely dangerous with tainted input (string-built SQL is; a parameterized query is not)

### 3. Check coverage, record each gap

Check the sources, sinks, and their pairings against the built-in rules (`opentaint health --rules`) and anything in `.opentaint/rules`:

- a built-in already covers the source→sink end to end → no rule
- a source you can pair to a dangerous sink for a real vuln class, not covered → a **join** rule requirement: write one `<tracking-dir>/rules/<name>.yaml`, named `<context>-<vuln-class>` in kebab-case (e.g. `mybatis-sqli`, `webclient-ssrf`), unique and stable — the name is the tracking file and follows the rule downstream. create-rule writes any missing source/sink lib rule and wires the join, referencing a built-in where one fits
- a genuine untrusted source you can't pair to a sink here, or a dangerous sink with no source in reach → append it to `<lib-pieces>`, not a rule. assemble-lib-rules pairs the loose pieces across packages into joins once every package is drilled — a source whose sink sits in a part of the app this pass doesn't see is the common case

State only what a rule author needs: the vuln class, which end a built-in covers and which must be written, and where it lives. Name the framework and the class, not a full traced flow with line numbers — the test project built later reads the real code. List every library the flow crosses under `dependencies`

Flip the package's `coverage.yaml` entry to `status: done` and add a one-line `notes` of what you found — write it the moment you finish so the walk resumes cleanly

## Output

- One `<tracking-dir>/rules/<name>.yaml` per paired flow, with `stages.description: done`, a short `requirements`, and `dependencies` (exact Maven GAVs from the build files — every library the flow crosses)
- Any unpaired source or sink appended to `<lib-pieces>` with `disposition: pending`
- The package's `coverage.yaml` entry set `status: done` with a one-line `notes`
- A brief summary to the caller: one line per proposed rule (name, source→sink) and a count of loose pieces left for assembly. The tracking files hold the detail — don't paste it back

## Tracking

`<tracking-dir>/coverage.yaml` — flip this package's entry when done:

```yaml
  - package: org.springframework.web.reactive.function
    status: done
    notes: ServerRequest source not covered by built-ins; reaches WebClient (SSRF) — webclient-ssrf
```

`<tracking-dir>/rules/<name>.yaml` — discovery-stage fields only:

```yaml
name: webclient-ssrf
rule_id: null               # filled later
finding: null               # filled later
requirements: >
  CWE-918 SSRF via Spring WebClient.
  source: user-supplied URL from request body — built-in spring source covers it
  sink: WebClient.get().uri($UNTRUSTED) — no built-in; needs a new sink rule
  lives in: run.halo.app.core.attachment.DefaultAttachmentService / ProxyFilter
dependencies:               # every library the flow crosses, exact GAV from the build files
  - org.springframework:spring-webflux:6.1.0
stages:
  description: done
  test_project: pending
  tests_passing: pending
notes: >
  free-form
```

`<tracking-dir>/lib-pieces.yaml` — append a source or sink you couldn't pair; assemble-lib-rules joins it:

```yaml
sources:
  - role: Apache HttpClient response body — data from a server the app calls
    package: org.apache.hc.client5.http
    dependency: org.apache.httpcomponents.client5:httpclient5:5.3
    disposition: pending     # pending | <join-name> once assembled | dropped: <reason>
sinks:
  - role: SnakeYAML load — untrusted YAML deserialization
    package: org.yaml.snakeyaml
    dependency: org.yaml:snakeyaml:2.2
    disposition: pending
```

## Engine notes

- Spring projects: the analyzer auto-discovers Spring endpoints, so `network` inbound sources are largely ones the built-ins already see — focus on which sinks those flows reach
- Generic projects: the analyzer treats all public/protected methods of public classes as entry points

## Gotchas

- Propose a rule only for a real gap; if a built-in already covers the source→sink, don't duplicate it
- Don't drop a source-only library because you can't trace its sinks — append the source to `<lib-pieces>` for assemble-lib-rules to pair; drop only a candidate that isn't genuinely untrusted
- Requirements name the missing source/sink and where it lives, not a full traced flow — keep them short; the test project reads the real code
- Don't grep dependency jars to find usage — read the app's own sources in `<project-root>`
