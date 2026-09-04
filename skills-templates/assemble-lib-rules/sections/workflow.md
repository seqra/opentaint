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
