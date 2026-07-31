### 1. Read the created lib rules and the built-ins

Read every source unit under `.opentaint/tracking/rules/sources/` and sink unit under `.opentaint/tracking/rules/sinks/` — the `rule_id`s already recorded, the sinks carrying their `vuln_class` — and the built-in source/sink lib rules:

```bash
opentaint health --rules
```

Collect every source rule (built-in + created) and every sink rule grouped by vuln class. A rule is built-in when its ref resolves in the loaded built-in ruleset, created otherwise — that membership, not a stored tag, tells the two apart.

When join files already exist from a prior run, reuse them as the baseline: re-assemble to fold in any new lib rule — a new source widens the `on` of every join for its vuln class, a new sink adds a join — and leave a join whose wiring no new rule touches as-is. Don't rewrite joins that already hold.

### 2. Write one security join per (vuln class, sink rule)

A join references exactly ONE sink rule — several sinks can't merge into one join. So a vuln class with more than one relevant sink becomes several joins: one per sink rule, each refing all the relevant sources on the left. Sources are many, the sink is always one.

For each vuln class, and within it each sink rule that needs new wiring, write a join under `.opentaint/rules/<lang>/security/<class>-<sink>-lib-ext.yaml` with `mode: join`, refing the relevant sources + that one sink, wiring only the new-end combinations in `on`:

- a created sink ← from every relevant source (built-in + created)
- a built-in sink ← from created sources only (a built-in source → built-in sink pair is already covered by the built-in join)

Two rules here:

- Unique id — use `id: <class>-<sink>-lib-ext`, never the bare class name; a custom join named `ssrf`/`xxe`/`path-traversal` collides silently with the built-in join of that id and is dropped with no error (only the scan's rule statistics reveal it)
- Right metavariable each side — the source side is always `$UNTRUSTED`. The sink side is `$UNTRUSTED` for a custom rules, but a built-in sink may bind another name — read it from how that sink is wired in the built-in security rules and use it: `source.$UNTRUSTED -> sink.$<its-metavar>`

```yaml
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

The same class's built-in sink is a second file (e.g. `ssrf-java-ssrf-sink-lib-ext.yaml`), refing only the created sources → that built-in sink.

### 3. Verify every rule is wired, then stop

With the joins written, confirm no orphan before returning — a source or sink not merged into a join. Cross-check the `rule_id`s in the source and sink units against the joins: every created source rule must appear as a source end in the `on` of at least one join, and every created sink rule must be the sink of a join, and each created sink's join must ref all its relevant sources (built-in + created) on the left. Add a join (per step 2) for anything still unwired.

Set `stages.written: done` (per Tracking) and return per Output.
