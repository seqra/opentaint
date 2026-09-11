---
name: assemble-lib-rules
description: Connect the shared untrusted-data source group to new reusable OpenTaint sink groups. Use to wire new sink tags into security joins
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Skill: Assemble Lib Rules

Reusable source rules share the single `untrusted-data-source` tag. Write only the security joins that connect it to sink tags reported as uncovered by `get_status.py`. An existing join automatically includes every new library rule carrying either tag. The main scan verifies the joins.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions

## Workflow

### 1. Get the missing sink tags

The orchestrator dispatches this skill only when `get_status.py` reports uncovered joins. Use that output as the complete worklist: each `untrusted-data-source -> sink-tag` line under `reusable tag groups are not fully joined` names one sink tag to connect. The script has already accounted for active built-in and custom library rules and for existing joins. Do not read those rules or recompute the matrix yourself.

### 2. Write one security join per missing sink tag

For each missing sink tag, write one `join` rule under `.opentaint/rules/<lang>/security/<vulnerability>.yaml`. Use the sink tag without its final `-sink` as the concise, globally unique `<vulnerability>` id — for example, `regex-dos-sink` becomes `regex-dos`. Reference the shared source tag and reported sink tag directly:

```yaml
rules:
  - id: regex-dos
    severity: ERROR
    message: Untrusted data reaches a regular-expression denial-of-service sink
    metadata:
      cwe:
        - CWE-1333
      short-description: Regular expression denial of service via untrusted input
    languages:
      - <language>
    mode: join
    join:
      refs:
        - tag: untrusted-data-source
          as: source
        - tag: regex-dos-sink
          as: sink
      on:
        - 'source.$UNTRUSTED -> sink.$UNTRUSTED'
```

Both endpoints use `$UNTRUSTED`. Sink tags and join ids name vulnerability classes, not packages, frameworks, or individual methods: a newly created rule for an existing vulnerability class reuses that class's sink tag and therefore needs no new join. Derive accurate security metadata from the sink tag.

### 3. Verify the matrix, then stop

Run `get_status.py` again. If it still reports an assigned sink tag, fix that join and repeat. Finish when every reusable sink tag is connected to `untrusted-data-source`.

## Output

### Artifacts

- one security join file per missing sink tag at `.opentaint/rules/<lang>/security/<vulnerability>.yaml`

### Summary

- one line per join: sink tag and rule id

## Gotchas

- Reference the reported sink tag directly, never re-declare or enumerate either tag group's lib-rule members
- Keep produced joins comment-free
