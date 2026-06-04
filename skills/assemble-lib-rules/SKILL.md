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

### 2. Write one security join per vuln class

For each vuln class that has a **created** (new) sink or for which there is any **created** source, write `<rules-dir>/java/security/<class>.yaml` (file and `id` = the class), `mode: join`, refing the relevant sources and sinks and wiring **only new-end combinations** in `on:`:

- built-in sources + created sources → that class's **new** sinks
- created sources → that class's **built-in** sinks
- skip built-in source → built-in sink — the built-in join already covers it, so repeating it double-reports

```yaml
rules:
  - id: ssrf
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
          as: servlet-source          # built-in source
        - rule: java/lib/spring/webflux-request-source.yaml#webflux-request-source
          as: webflux-source          # created source
        - rule: java/lib/spring/webclient-ssrf-sink.yaml#webclient-ssrf-sink
          as: new-sink                # created (new) sink
        - rule: java/lib/generic/ssrf-sinks.yaml#java-ssrf-sink
          as: builtin-sink            # built-in sink
      on:
        - 'servlet-source.$UNTRUSTED -> new-sink.$UNTRUSTED'      # built-in source → new sink
        - 'webflux-source.$UNTRUSTED -> new-sink.$UNTRUSTED'      # created source → new sink
        - 'webflux-source.$UNTRUSTED -> builtin-sink.$UNTRUSTED'  # created source → built-in sink
```

(no `servlet-source -> builtin-sink` line — the built-in join already covers that pair)

### 3. Stop — the main scan verifies

These joins carry no test project — the main scan applies them. Write them and stop; if the scan shows a join didn't load or fire, the orchestrator re-dispatches create-rule to fix it

## Output

- One `<rules-dir>/java/security/<class>.yaml` per vuln-class join, refing the created + built-in lib rules
- One `<tracking-dir>/rules/join/<class>.yaml` per join, with `stages.written: done`
- A brief summary to the caller: one line per join (class, source/sink count, which ends are new)

## Tracking

`<tracking-dir>/rules/join/<class>.yaml` — the security join, verified by the main scan:

```yaml
name: ssrf                    # the vuln class; the join rule's file and id
rule_id: java/security/ssrf.yaml:ssrf
artifact: .opentaint/rules/java/security/ssrf.yaml
sources:                      # built-in + created
  - ref: java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
  - ref: java/lib/spring/webflux-request-source.yaml#webflux-request-source
sinks:                        # created + built-in
  - new: java/lib/spring/webclient-ssrf-sink.yaml#webclient-ssrf-sink
  - builtin: java/lib/generic/ssrf-sinks.yaml#java-ssrf-sink
stages:
  written: done
  verified: pending           # done once the main scan confirms it
notes: >
  free-form
```

## Gotchas

- One join per vuln class, aggregating every relevant source — don't write a separate join per source or per package
- Ref the existing lib rules (built-in + created); never re-declare a source or sink
