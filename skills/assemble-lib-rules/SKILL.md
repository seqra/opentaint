---
name: assemble-lib-rules
description: Expand rule-family tags and write only the per-vulnerability security joins still needed to connect created source/sink library rules with the built-ins. Use to wire lib rules into project-level joins
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# Skill: Assemble Lib Rules

Source and sink library rules expose open role families through tags. Related custom sources may share a project-specific tag, and a custom join may consume that family with one `tag:` ref. Expand the existing built-in and custom joins first: a created rule that reused a consumed family tag may already be wired without another file. Add only the security joins needed for uncovered source-to-sink combinations, using tags for deliberate family expansion and exact rule refs for isolated components. The joins carry no test project; the main scan verifies them.

## Inputs

Provided by the caller, fall back to the default value when omitted. Ask back only when a required input is missing and has no sensible default

- `project-root` (optional) — root of the target project. Opentaint keeps all analysis artifacts under the fixed `<project-root>/.opentaint/` directory, so every `.opentaint/...` path below resolves there. Default: current directory
- `language` (required) — target language for this project and language-specific instructions

## Workflow

### 1. Inventory components and expand existing joins

Read every source unit under `.opentaint/tracking/rules/sources/` and sink unit under `.opentaint/tracking/rules/sinks/` — the concrete `rule_id`s already recorded and each sink's `vuln_class` — plus every created library/security rule. Locate and read the built-in library/security rules through:

```bash
opentaint health --rules
```

For each source and sink component, record its concrete ref, tags, exposed metavariable, language, and relevant vulnerability class. A `tag:` ref is a language-scoped union of every active rule carrying that exact tag, whether the rules are built-in or custom; an explicit `rule:` ref selects only one rule. Several custom sources may therefore share one project-specific tag and be consumed together by a custom join. Expand both forms in every existing security join and enumerate the concrete source-to-sink pairs its `on` clauses cover. A created rule that reused a tag already consumed by a built-in or custom join is wired by that join automatically.

When custom join files already exist, use them as part of this baseline. Don't rewrite a join whose expansion already covers the intended pairs.

### 2. Add only uncovered combinations

For each vulnerability class, compare all relevant source × sink combinations with the expanded pairs from step 1. Write a new `mode: join` rule only for combinations still uncovered:

- Prefer `tag:` when every active member of that role family should participate. Tagged source and sink sides expand as a Cartesian product, so one join can deliberately cover several components.
- Use an exact `rule:` ref when tag expansion would pull in an unrelated component or duplicate a pair already covered elsewhere.
- A ref contains exactly one of `tag` or `rule`, every `as` alias is unique, and a join cannot reference another join.
- Read the component before writing `on`: custom components expose `$UNTRUSTED`, while a built-in may expose another name.

Use a unique extension id such as `<class>-lib-ext`; never reuse the built-in class id because duplicate ids are dropped. Preserve the built-in rule's user-facing metadata for that vulnerability class.

```yaml
rules:
  - id: ssrf-lib-ext
    severity: ERROR
    message: Untrusted data reaches an SSRF sink
    metadata:
      cwe: CWE-918
      short-description: SSRF via untrusted input
    languages: [java]
    mode: join
    join:
      refs:
        - tag: orders-untrusted-data-source
          as: orders-source
        - tag: ssrf-sink
          as: sink
      on:
        - 'orders-source.$UNTRUSTED -> sink.$UNTRUSTED'
```

This example intentionally adds every custom source whose `tags` list contains `orders-untrusted-data-source` to every active Java SSRF sink carrying `ssrf-sink`. If only one source should connect, replace its `tag:` ref with that component's exact `rule:` ref.

### 3. Record concrete coverage and verify

Update each class's joins tracking with concrete rule refs, even when the covering join uses tags: list every created source covered under `sources`, and one `joins` entry per concrete sink with the `rule_id` of the existing or newly created security join that covers it. Several sink entries may name the same tag-expanded join. Don't create a redundant join file merely to produce tracking state.

Expand all joins again and confirm there is no orphan or missing pair: every created source reaches every relevant sink class, every created sink is reachable from all relevant sources, and no pair is represented twice. Set `stages.written: done` (per Tracking) and return per Output.

## Output

### Artifacts

- zero or more extension join files under `.opentaint/rules/<lang>/security/`, only for concrete source-to-sink combinations not already covered through an existing rule/tag join
- `.opentaint/tracking/rules/joins/<class>.yaml` — one per vuln class, recording the concrete components covered by existing and created joins (per Tracking)

### Summary

- one line per vulnerability class: concrete source/sink counts, reused tag-expanded joins, and any extension join created

## Tracking

This skill writes the joins tracking, one file per vuln class, setting each file's `stages.written: done`. Record concrete source/sink refs after expanding tags so deterministic status checks don't need to reimplement rule loading. The main scan verifies the joins; don't touch `verified`.

`.opentaint/tracking/rules/joins/<class>.yaml` — one file per vuln class (class = filename), listing concrete source/sink refs and the existing or created security joins that cover them, verified later by the main scan. Tags are expanded before writing this state: `sources` and each `sink` remain concrete refs so status checks stay deterministic; several sinks may share one tag-expanded join `rule_id`. Built-in-vs-created is derived by ruleset membership. Keep it clear from comments

```yaml
sources:
  - java/lib/generic/servlet-untrusted-data-source.yaml#java-servlet-untrusted-data-source
  - java/lib/spring/webflux-request-source.yaml#webflux-request-source
joins:
  - rule_id: java/security/ssrf.yaml:ssrf
    sink: java/lib/spring/webclient-ssrf-sink.yaml#webclient-ssrf-sink
  - rule_id: java/security/ssrf.yaml:ssrf
    sink: java/lib/generic/ssrf-sinks.yaml#java-ssrf-sink
stages:
  written: done
  verified: pending
```

## Gotchas

- Ref the existing lib rules (built-in + created), never re-declare a source or sink
- A tag is an open family, not shorthand for one rule — use it only when every active same-language member should fan out through the join
- Keep produced joins comment-free
