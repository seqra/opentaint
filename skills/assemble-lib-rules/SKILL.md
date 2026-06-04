---
name: assemble-lib-rules
description: Write the per-vuln-class security join rules that merge the created source/sink lib rules with the built-ins. Use after the per-package lib rules are created and tested, to wire them into project-level joins
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.2"
---

# Skill: Assemble Lib Rules

The per-package passes author source and sink lib rules but never pair them across packages. With every created lib rule and the whole built-in set in front of you, write the security joins — one per vuln class, each merging the created rules with the built-ins, mirroring the built-in security rules. These are verified by the main scan, not a test project

## Inputs

From the caller; if omitted, fall back to the default. Ask only when a required input is missing and has no sensible default

- Lib units `<lib-units>` — the per-package lib tracking files (`rules/lib/<package-kebab>.yaml`) with the created source/sink `rule_id`s and their vuln classes. Default: `.opentaint/tracking/rules/lib/`
- Rules directory `<rules-dir>` — where the security joins are written. Default: `.opentaint/rules`
- Tracking directory `<tracking-dir>` — where the join records are written. Default: `.opentaint/tracking`

Built-in rules are available at `opentaint health --rules`

## Workflow

### 1. Read the created lib rules and the built-ins

Read every per-package lib unit in `<lib-units>` (the source/sink `rule_id`s create-rule wrote, sinks carrying their `vuln_class`) and the built-in source/sink lib rules (`opentaint health --rules`). Collect every source rule (built-in + created) and every sink rule grouped by vuln class

### 2. Write one security join per (vuln class, sink rule)

A join references exactly ONE right-hand (sink) rule — you cannot merge several sinks into one join. So a vuln class with more than one relevant sink becomes several joins: one per sink rule, each refing all the relevant sources on the left. Sources are many; the sink is always one.

For each vuln class, and within it each sink rule that needs new wiring, write `<rules-dir>/java/security/<class>-<sink>-lib-ext.yaml` with `mode: join`, refing the relevant sources + that one sink, wiring only new-end combinations in `on:`:

- a created (new) sink ← from every relevant source (built-in + created)
- a built-in sink ← from created sources only (built-in source → built-in sink is already covered by the built-in join — repeating it double-reports)

Two rules that bite here:

- Unique id — use `id: <class>-<sink>-lib-ext`, never the bare class name; a custom join named `ssrf`/`xxe`/`path-traversal` collides silently with the built-in join of that id and is dropped with no error (only the scan's rule statistics reveal it)
- Same metavariable both sides — every `on:` clause connects the metavariable both lib rules bind (`$UNTRUSTED` by convention) as `source.$UNTRUSTED -> sink.$UNTRUSTED`; don't invent a new name on either end, or the join won't connect

```yaml
# java/security/ssrf-webclient-ssrf-sink-lib-ext.yaml
rules:
  - id: ssrf-webclient-ssrf-sink-lib-ext
    severity: ERROR
    message: Untrusted data reaches an SSRF sink
    metadata:
      cwe: CWE-918
      short-description: SSRF via untrusted input
    languages: [java]
    mode: join
    join:
      refs:
        - rule: java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
          as: servlet-source
        - rule: java/lib/spring/webflux-request-source.yaml#webflux-request-source
          as: webflux-source
        - rule: java/lib/spring/webclient-ssrf-sink.yaml#webclient-ssrf-sink
          as: sink
      on:
        - 'servlet-source.$UNTRUSTED -> sink.$UNTRUSTED'
        - 'webflux-source.$UNTRUSTED -> sink.$UNTRUSTED'
```

The same class's built-in sink is a second file (`ssrf-java-ssrf-sink-lib-ext.yaml`), refing only the created sources → that built-in sink. The `#` comments in these examples are for you — don't copy them into the rules you write

### 3. Stop — the main scan verifies

These joins carry no test project — the main scan applies them. Write them and stop; if the scan shows a join didn't load or fire, the orchestrator re-dispatches create-rule to fix it

## Output

- One `<rules-dir>/java/security/<class>-<sink>-lib-ext.yaml` per (vuln class, sink rule), each refing all relevant sources + its one sink
- One `<tracking-dir>/rules/join/<class>.yaml` per vuln class, listing every join it produced, with `stages.written: done`
- A brief summary to the caller: one line per join (class, sink, source count, which ends are new)

## Tracking

`<tracking-dir>/rules/join/<class>.yaml` — one file per vuln class, listing each join (one per sink rule), verified by the main scan:

```yaml
name: ssrf
sources:
  - ref: java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
  - ref: java/lib/spring/webflux-request-source.yaml#webflux-request-source
joins:
  - rule_id: java/security/ssrf-webclient-ssrf-sink-lib-ext.yaml:ssrf-webclient-ssrf-sink-lib-ext
    artifact: .opentaint/rules/java/security/ssrf-webclient-ssrf-sink-lib-ext.yaml
    sink: { new: java/lib/spring/webclient-ssrf-sink.yaml#webclient-ssrf-sink }
  - rule_id: java/security/ssrf-java-ssrf-sink-lib-ext.yaml:ssrf-java-ssrf-sink-lib-ext
    artifact: .opentaint/rules/java/security/ssrf-java-ssrf-sink-lib-ext.yaml
    sink: { builtin: java/lib/generic/ssrf-sinks.yaml#java-ssrf-sink }
stages:
  written: done
  verified: pending
notes: >
  free-form
```

## Gotchas

- One join references exactly one sink — a class with N relevant sinks yields N joins, each aggregating every relevant source; never pack two sinks into one join
- Ref the existing lib rules (built-in + created); never re-declare a source or sink
