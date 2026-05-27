---
name: discover-attack-surface
description: Walk a JVM project's attack surface area by area and turn each coverage gap into a rule requirement. Use when a project needs rule coverage mapped across its attack-surface areas (requires a built project model)
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3"
---

# Skill: Discover Attack Surface

Cover the target's attack surface systematically. Walk a fixed checklist of attack areas, and for each one explore the project sources and its dependencies for untrusted flows the built-in rules miss. Every gap becomes one rule requirement; the checklist records what was explored so no area is silently skipped

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Project root `<project-root>` — the project sources. Default: current directory
- Project model `<model-dir>` — the built model. Default: `.opentaint/project`
- Tracking directory `<tracking-dir>` — where the coverage checklist and rule files are written. Default: `.opentaint/tracking`

## Workflow

Requires a built project model — without it you can miss entry points the analyzer actually sees

### 1. Seed the checklist

Seed `<tracking-dir>/coverage.yaml`'s `areas` list with one entry per area below, each `status: pending` and `rules: null` (null until you walk it; `[]` or names once done). These source-side and sink-side classes of taint flow are a minimum — add a project-specific area when a dependency exposes one they don't cover (comments for you, don't write them):

```yaml
- area: user-input        # untrusted data entering: HTTP params/headers/body, RPC, payloads, CLI args, config
  status: pending
- area: database          # SQL/HQL/NoSQL query construction (SQLi)
  status: pending
- area: filesystem        # paths built for file read/write/delete (path traversal)
  status: pending
- area: command-exec      # process or shell execution (command injection)
  status: pending
- area: outbound-request  # HTTP/URL clients (SSRF)
  status: pending
- area: deserialization   # object/JSON/XML deserialization of untrusted bytes
  status: pending
- area: templating        # template or expression evaluation (SSTI, EL injection)
  status: pending
- area: xml-parsing       # XML/document parsing (XXE)
  status: pending
- area: ldap              # directory queries (LDAP injection)
  status: pending
- area: response-output   # untrusted data rendered into a response (XSS)
  status: pending
- area: reflection        # dynamic class/method loading (code injection)
  status: pending
- area: redirect          # untrusted URL driving a redirect (open redirect)
  status: pending
- area: logging           # untrusted data into log/format APIs (log injection)
  status: pending
```

### 2. Walk every area

Go through each `pending` area in turn — never skip one. For each, explore both the project and its dependencies:

- read model for the libraries that expose this area
- search the sources for the matching sources or sinks
- note what untrusted data enters and which dangerous call it can reach

Then check coverage against the built-in rules (`opentaint dev rules-path`) and anything in `.opentaint/rules`, and decide:

- built-ins already detect every real flow here, or the area is absent from this project → no rule; leave `rules: []`
- a real, untrusted flow has no covering rule → propose a rule (step 3)

Verify the flow is real before recording it: the source is genuinely attacker-controlled (a request param, header, body, or message payload is; an app constant or server config is not), and the sink is genuinely dangerous with tainted input (string-built SQL is; a parameterized query is not). A pair that fails this isn't a rule

Update the area's entry in `coverage.yaml` the moment you finish it — set `status: done`, fill `rules` (`[]` or the proposed names), add a one-line `notes` of what you found — then move on. Write per area, not batched at the end, so the walk resumes cleanly and every area carries a record proving it was checked, not skipped

### 3. Record each proposed rule

For each gap, add the rule name to its area's `rules:` list and write one `<tracking-dir>/rules/<name>.yaml`. Name it `<context>-<vuln-class>` in kebab-case — the sink technology or framework plus the class, e.g. `mybatis-sqli`, `thymeleaf-ssti`, `resttemplate-ssrf`. It must be unique and stable: the name is the tracking file and follows the rule downstream

State only what a rule author needs: the vuln class, which built-in source/sink rules already apply, and which source or sink is missing and must be written. Name the framework and the class where the flow lives — not a full traced flow with line numbers. The test project built later reads the real code to reproduce it

## Output

- `<tracking-dir>/coverage.yaml` — every area `done`, each with proposed rules (or `[]`)
- One `<tracking-dir>/rules/<name>.yaml` per proposed rule, with `stages.description: done`, a short `requirements`, and `dependencies` (exact Maven GAV from the build files) the test project needs
- A brief summary to the caller: the areas covered, then one line per proposed rule (name, vuln class, source→sink). The tracking files hold the detail — don't paste it back

## Tracking

`<tracking-dir>/coverage.yaml` — one entry per area, filled as you walk:

```yaml
- area: database
  status: done            # pending | done
  rules: [mybatis-sqli]   # proposed rule names; [] when built-ins cover it or the area is absent
  notes: >
    MyBatis 3.5 mappers use ${} interpolation; built-in covers JDBC sinks but not MyBatis ${}
- area: filesystem
  status: done
  rules: []
  notes: only constant paths; no untrusted data reaches a file API
# ...
```

`<tracking-dir>/rules/<name>.yaml` — discovery-stage fields only:

```yaml
name: mybatis-sqli
rule_id: null               # filled later
finding: null               # filled later
requirements: >
  CWE-89 SQLi via MyBatis ${} interpolation.
  source: untrusted HTTP request param — built-in spring source covers it
  sink: ${} string interpolation in a @SelectProvider / mapper XML — no built-in; needs a new sink rule
  lives in: com.example.mapper.OrderMapper / OrderSqlProvider
dependencies:               # exact GAV the test project needs, from the build files
  - org.mybatis:mybatis:3.5.13
  - org.springframework:spring-webmvc:5.3.30
stages:
  description: done
  test_project: pending
  tests_passing: pending
notes: >
  free-form
```

## Engine notes

- Spring projects: the analyzer auto-discovers Spring endpoints, so `user-input` is largely sources the built-ins already see — focus on which sinks those flows reach
- Generic projects: the analyzer treats all public/protected methods of public classes as entry points

## Gotchas

- Propose a rule only for a real gap; if a built-in already covers the source→sink, don't duplicate it
- Requirements name the missing source/sink and where it lives, not a full traced flow — keep them short; the test project reads the real code
- A passing test won't catch a semantically wrong source or sink — verify both are real here, because nothing downstream re-checks it
