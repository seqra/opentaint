# Skill framework

The single standard for writing and editing the OpenTaint skills. Source lives in
`skills-new/<skill>/` and compiles to `skills/<skill>/` via `build.py`. Two parts below:
general rules, then the per-section spec. Leave nothing "just in case" — every line earns its place.

## Build model

- Each skill = `main.md.j2` (frontmatter inline, `version: "{{ version }}"`) + `sections/*.md`, composed with `{% include %}`.
- `shared/` holds every repeated element as one source: input lines, tracking schemas, engine facts.
- `version` is the only scalar variable (`config.yaml`). Everything else repeated is a shared partial, not a variable.
- Reference a partial with `{% include "shared/..." %}`. Path literals live inside the partials — change once.

## General rules (every edit)

- Terse. No verbose formatting, no `**`. Keep each SKILL.md under 500 lines.
- Minimal edits. Don't add irrelevant info, abstract instructions without test evidence, or "just in case" warnings.
- Don't explain what the agent already knows. Third person, imperative.
- Consistent terminology; forward slashes in paths; MCP tools by full `Server:tool` name.
- Name a skill-bundled reference or script by its skill-relative path — `references/<lang>-rule.md`, `scripts/partition-methods.py` — never the bare filename (per the skills standard).
- One subagent = one skill. A dispatch loads exactly one skill and does only that skill's task; never bundle skills or steps into one agent. Rare exceptions only when genuinely unavoidable.
- Never reference another skill from a leaf skill. Point forward by stage or artifact instead — "this artifact is used later in the approximation stage", never "see assemble-lib-rules" / "debug-rule handles this" / "analyze-external-methods writes the sinks". An ownership boundary is stated as a white-list ("this skill writes only …"), never by naming the other writer.
- Keep focus: a leaf skill does only its own task and stays reusable beyond this workflow. All cross-agent decisions and adaptivity live in the orchestrator and its scripts, never in a leaf.
- A leaf doesn't do the orchestrator's job or act on its feedback: it doesn't run the pipeline's main scan, read that scan's error/output artifacts, or decide escalation, re-planning, or whether another stage or approximation is needed — those are the orchestrator's. (A skill whose own craft is an operation is the exception: run-scan runs the main scan; create-rule and the test-project skills run their own isolated diagnostic build/scan.) A leaf authors its artifact and self-checks it against its own inputs; its last step is a self-review of that output, not a "verify by the scan" or an escalation call.
- Context handed to you for understanding is not skill content — never copy it in.
- Don't store derivable data — no field that repeats a filename or path.
- No comments in YAML/schema/structure blocks; put that in the prose. Comments only in code/command examples; produced rule/config files are comment-free.
- Keep per-item tracking fields to one line; a notes field must not accrete prose across runs.
- Split regenerable script-generated inputs from durable agent-edited outputs; don't persist a regenerable artifact as durable state.
- Classifying methods/rules: a false positive beats a false negative (a missed flow can't be recovered) — model a genuinely suspicious method rather than skip it, without over-modeling.

## Scripts

- Skill-bundled scripts (run by the agent via `uv run scripts/…`): PEP723 inline deps, tested with uv/uvx. One algorithmic Python script over per-platform sh/ps1; separate scripts only when the cases aren't the same code.
- The `skills-new/` build tooling itself is a separate uv project (`pyproject.toml`), not PEP723.

---

# File & tracking ownership

Who may write each artifact. Parallelism is safe because fan-out agents write disjoint slices (partition gives each one a file no sibling touches) and every cross-slice merge is deferred to a single-threaded script at the join. Three writer classes:

- Subagent — only its own slice: the per-unit / per-batch tracking file it was dispatched for, plus the craft artifacts it produces (rule files, approximation configs, test projects, PoC scripts, the project model, the SARIF). Never another agent's slice, an orchestrator-owned file, or the main project model (only `run-scan` scans that; a `create-rule` diagnostic scans its own test model).
- Orchestrator, direct — only the small cross-cutting state it owns, written at joins: `state.yaml`, `vulnerabilities.md`, `history.yaml`, plus the terminal escalation marks it appends when a leaf reports a non-converging item (a `blocker` on that rule unit, an `engine_issues` entry on that approximation batch). Brief entries. It never does craft, never triages, never scans the main model.
- Orchestrator, via script (single-threaded, at the join) — every merge/aggregate across agents' slices, where race-safe handling matters: partition (plans), mark-safe (`classification.yaml`), merge-skipped (`skipped.yaml`), sarif-to-findings (`findings/*`). The orchestrator runs these, never hand-merges.

Ownership map — a multi-writer file is written at disjoint stages/fields, sequential via the on-disk artifact, so it still has a single writer at any moment:

```
state.yaml, vulnerabilities.md, history.yaml    orchestrator (direct)
rules/plans/*, approximations/plans/*           script: partition   (regenerable)
rules/classification.yaml                       script: mark-safe
approximations/skipped.yaml                     script: merge-skipped
findings/*                                      script: sarif-to-findings (create) → analyze-findings (verdict/notes) → generate-poc (poc)
coverage.yaml                                   triage-dependencies
rules/sources/*                                 discover-attack-surface → create-test-project → create-rule → orchestrator (blocker)
rules/sinks/*                                   analyze-external-methods → create-test-project → create-rule → orchestrator (blocker)
rules/joins/*                                   assemble-lib-rules
approximations/<batch>                          analyze-external-methods → create-test-project → create-pass-through / create-dataflow → orchestrator (engine_issues)
project model                                   build-project
results/report.sarif, dropped/approximated      run-scan
pass-through/*                                  create-pass-through-approximation
dataflow/*                                      create-dataflow-approximation
poc-servers.yaml, pocs/*                        generate-poc
issues/*                                         report-analyzer-issue
```

A skill's Tracking section white-lists only the fields it writes and never names the other writers (that is a cross-skill reference — forbidden). The full stage order lives in the orchestrator.

---

# Section spec (leaf skill)

Order, first four required, last three as needed:

`Preamble · Inputs · Workflow · Output · [Tracking] · [Constraints] · [Gotchas]`

## Preamble  (required)

- `# Skill: <Title>` + one short paragraph: a brief intro to what happens in this skill.
- Not "when to call it" — the skill is already loaded. No inputs, steps, or schemas.
- No role/relationship-to-other-skills notes (those are the orchestrator's concern, dropped from leaves).

## Inputs  (required)

- Opens with `{% include "shared/inputs-preamble.md" %}`.
- One bullet per input: `` - `<name>` (required|optional) — meaning ``. Append `Default: <value>` only when the input has a meaningful default; omit the clause otherwise.
- The `.opentaint/` working tree is fixed under `<project-root>`: the model is always `.opentaint/project/`, tracking `.opentaint/tracking/`, rules `.opentaint/rules/`, and so on. So a skill takes only `<project-root>` (default: current directory) — never a `model-dir` / `tracking-dir` / `rules-dir` path input — and names the fixed paths inline where it uses them, spelling out only the slice of the layout that skill touches. Don't hoist the layout into `shared/`; an agent needs its own skill's paths, not the whole tree up front. A per-unit sub-path whose name the orchestrator assigns (a test project under `.opentaint/test-projects/<name>`) is still passed.
- Canonical shared inputs (`project-root`, `language`) come verbatim from `shared/inputs/<name>.md`; accept the general wording.
- A rare input with a skill-specific meaning is written by hand — don't add a shared variant and reference it. Over-abstraction costs more than a one-off line.

## Workflow  (required)

- Numbered `### N. <step>`; commands in fenced bash blocks; a copyable checklist for long or fragile flows.
- No intro paragraph before `### 1` — Workflow opens on the first step. Framing that fits the Preamble goes there; an operational note (a re-invocation rule, a per-step pointer to the language reference) belongs inside the step it governs.
- Write feedback loops explicitly: run → read result → fix → repeat.
- The escalation trigger is the last step ("when it won't converge after ~2 fixes → report non-convergence, leave the stage pending").
- No tracking-file schema or structure here — reference tracking only briefly, e.g. "set `build.done` in the batch file (per Tracking)".
- The format of the work product this skill authors (rule YAML, passThrough config, dataflow source) stays inline here — that's the skill's craft, not a tracking schema. When it's language-specific, the format lives in the language reference (see Multi-language support), not the body.
- Point to sibling sections with "per Output" / "per Tracking", don't repeat them.
- Body stays language-agnostic — never name a language; point to the language reference for language-specific detail.

## Output  (required)

Two parts, so the orchestrator can advance a fixed workflow on this report alone — without re-opening the files or re-reading the scripts:

- Artifacts — the concrete files or globs created/modified, so the orchestrator knows what now exists. Give each a brief what-it-is note when it carries no Tracking section: a craft output the scan consumes (rule YAML, approximation config like `.opentaint/pass-through/cn-hutool-core-*.yaml`, PoC, the project model) or an analyzer-returned / script-generated one (`report.sarif`, `dropped-external-methods.yaml`, `findings/*`). That note is all the orchestrator gets for it.
- Exception — a tracking file the skill owns (schema in Tracking): its full path plus only a minimal tag (a few words), not a full gloss — the shape lives in Tracking.
- Summary — an abstract account of what was done plus the decision-relevant facts (counts, verdicts, blocked/failed items). Never paste back file contents; the files hold them.

## Tracking  (optional — only if the skill owns a slice)

- A Tracking section covers only a tracking file the skill owns and coordinates through — one a script generates from the agents' docs, one agents mark themselves, or one agents read and use. An analyzer-returned/automatic artifact or a craft output gets none: it's named in Output with a brief note (a craft output's authoring format lives in Workflow).
- Format reference only: the file's full schema via `{% include "shared/tracking/<file>.md" %}`; the partial carries the file's full `.opentaint/...` path and a one-line purpose, so don't restate them in prose here.
- White-list the fields this skill edits. When not to write is already in Workflow, not here.
- The schema structure is language-agnostic and lives here; a language-specific value format or field (signature notation, `java/` rule-path prefix, `build_jdk`) is documented in the language reference, not inline. Schema partials show the structure with one concrete example (Java today).

## Constraints  (optional)

- Hard rules that must hold — engine/DSL/format invariants and scope boundaries. Bullets.
- Reason is terse and optional; omit it when the point is just to force an action.
- Shared engine/format facts come from `shared/engine/*`; skill-specific invariants stay local.
- No diagnostics ("if you see X …") — those are Gotchas.
- Language-agnostic only; a language-specific invariant goes in the language reference's Constraints (see Multi-language support), not here.

## Gotchas  (optional)

- Everything else from the original skill that isn't a Constraint: non-obvious pitfalls, troubleshooting, symptom → cause → fix.
- The escalation trigger itself lives in Workflow's last step; residual troubleshooting lives here.
- Language-agnostic only; language-specific pitfalls go in the language reference's Gotchas.

## Constraints vs Gotchas (decision test)

- always true, obey it → Constraints
- may go wrong, here's the tell + fix → Gotchas
- file format / location → Tracking (or inline in Workflow for a work-product format)
- role / relationship to other skills → removed from leaves (orchestrator's concern)

---

# shared/ layout

```
shared/
  inputs-preamble.md
  inputs/     project-root.md language.md   # only project-root and language are inputs; fixed .opentaint/ paths are named inline per skill
  tracking/   state.md approximations-batch.md sink-unit.md source-unit.md joins.md
              findings.md skipped.md coverage.md classification.md poc-servers.md
  engine/     facts.md scan-flags.md boundaries.md
config.yaml   # version, currently "0.2"
```

- Granularity A: a tracking partial is the file's full canonical schema, included wherever that file is touched.
- `shared/` holds only the genuinely repeated — tracking schemas above all. Analyzer-returned artifacts (`dropped-external-methods.yaml`, `report.sarif`, `project.yaml`) have fixed external formats and are referenced by name inline, not schema'd here. Rare/specific content stays inline in its skill.

---

# Multi-language support

The engine targets multiple languages (Java today, Go next). A skill's workflow logic is written once and language-agnostic; everything language-specific — type names, signatures, sample/rule/approximation code, build commands — lives in a per-language reference the orchestrator names on dispatch.

Mechanism:
- A language-coupled skill carries `references/<lang>[-<facet>].md` — one reference per language when it suffices (`java.md`), split by framework/facet when a language diverges (`java-core.md` + `java-spring.md` + `java-reactor.md`). All are siblings one level from `SKILL.md`; the base (`<lang>` / `<lang>-core`) indexes the facets and directs a full read when the target matches ("Reactor/Mono target → read `java-reactor.md` fully"), so nothing chains deeper than that.
- The orchestrator records the target language (`build-project` detects it → `state.yaml.language`) and, on every dispatch, names the reference to read: "target language go; read `references/go.md` first". The shared input `<language>` carries it.
- The body never names a language — it points generically ("follow the language reference for the exact pattern / signature / sample").
- References are templates (`references/*.md.j2`), rendered by `build.py`; a chunk common across references comes from a `shared/` partial via `{% include %}`.
- This is the one sanctioned use of `references/` in a leaf: languages are mutually exclusive (one run = one language), so loading only the relevant one is real progressive disclosure.

Reference format — a reference reuses the skill's block vocabulary, but only the blocks that carry language detail, and never the contract blocks:
- Workflow — the language-specific "how", keyed to the body's step numbers (Tier 2: the full numbered Workflow, feedback loop and escalation included).
- Constraints — language-specific hard rules (e.g. Java-8 source, one `@Approximate` per class).
- Gotchas — language-specific pitfalls (e.g. implicit-receiver `this.method` unsupported).
- Output / Tracking — the block's structure (Output shape, Tracking schema/keys) stays in the skill and is language-agnostic. A language-specific value format or field an authoring skill must produce — JVM signature descriptors, `java/`-prefixed rule paths, `state.yaml.build_jdk`, package/module notation — is documented in the language reference: usually inside its Workflow, or as a short Output/Tracking note when the field or value format itself varies by language.
- Never Preamble / Inputs — always language-agnostic, skill-only.

Tiers — how language-coupled a skill is:
- Agnostic — no language reference; the body is complete. `run-scan`, `analyze-findings`, `assemble-lib-rules`, `report-analyzer-issue`, `debug-rule`, `triage-dependencies`.
- Mixed — general plan in the body, language idioms/examples/signatures in `references/<lang>.md`. `analyze-external-methods`, `create-rule`, `create-pass-through-approximation`, `discover-attack-surface`, `generate-poc`.
- Language-defined — the craft is the target language; the body holds only the concept + general advice, the full procedure is in `references/<lang>.md`. `build-project`, `create-test-project`, `create-dataflow-approximation`.

Rules:
- Body language-agnostic: no language names, no language-specific type/signature/sample in the body.
- Each language reference mirrors the body's step structure, so an agent maps body-step → reference-detail 1:1.
- Adding a language = add `references/<lang>[-<facet>].md` to the coupled skills; the body and workflow order don't change.
- `build.py` renders `references/*.md.j2`, so a reference can pull language-agnostic `shared/` partials; move a genuinely identical cross-skill language chunk to `shared/` only when it actually repeats, don't pre-abstract.

---

# Orchestrator (appsec-agent) — special

[PLACEHOLDER — the orchestrator does not follow the leaf section spec. Its sections (Setup, Choose workflow, Delegation, Resource limits, State/resumption, Tracking layout, Working directory, Key constraints) and its use of `references/` per-step stay. Confirmed rule: no gratuitous cross-stage "see scan.md" in prose; forward-pointers by stage/artifact are fine; the pipeline table mapping step → reference is the mechanism and stays. Full standard to be defined separately.]

---

Supersedes `skills/skill-writing-guidelines.md` (fold complete; remove that file once this is adopted).
