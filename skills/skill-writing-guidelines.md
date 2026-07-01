# Skill-writing guidelines

How to edit the OpenTaint skills. Apply on every change.

## Editing skills

- Follow the current skill style — terse, no verbose formatting, no `**`.
- Make minimal edits. Don't add irrelevant info, abstract instructions without test evidence, or "just in case" warnings.
- Don't explain what the agent doesn't need to know; scope each edit to that skill's task. If an agent never does X, it needn't know about X.
- Context given to you for understanding is not skill content — never copy it into the skills.
- If unsure whether some info belongs, ask — don't add it silently.
- Propose each skill edit as a plan first; apply only after explicit approval.

## Skill scope vs. orchestrator

- Keep each leaf skill single-task and reusable beyond this workflow. Put workflow/format coupling on the orchestrator side; adjust a leaf skill only enough to work with the new format.
- When a skill's task narrows, adjust it for that task but keep related capabilities together (e.g. create-rule keeps both sinks and sources).

## File and tracking format

- Don't store what's derivable — no field that just repeats the filename or path (e.g. an `id`/`root` equal to the file's name).
- Keep comments out of YAML/structure/schema blocks; put what a comment would say in the surrounding prose. Comments stay only in code and command examples, and produced config/rule files are comment-free.
- Give each fan-out agent a self-contained, per-agent input it can work from alone — don't make it read a large shared file or another agent's slice.
- Split script-generated, regenerable inputs from agent-edited, durable outputs; don't persist a regenerable artifact as durable state.
- Keep per-item fields terse — one line per item, strictly what's needed; don't let a notes field accrete prose across iterations.
- Prefer the simplest structure that works; don't add fields or sections that aren't needed.

## Scripts

- For external libs follow PEP723 and test with uv/uvx (https://agentskills.io/skill-creation/using-scripts#python).
- Prefer one algorithmic Python script over per-platform sh/ps1 — a single shared script when the cases are the same code, separate scripts when they aren't.

## Gathering context and testing

- Use subagents to gather context for coverage and depth.
- Test scripts with subagents on the projects under /drive-testcomp/claude-testing/, and have them verify the results.

## False positives vs. false negatives

- When classifying methods or rules, a false positive is far better than a false negative — a missed flow can't be recovered after the run. Prefer modeling a genuinely suspicious method over skipping it, but don't over-model carelessly.
