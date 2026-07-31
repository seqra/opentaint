---
name: appsec-agent
description: Entry point for OpenTaint application-security work — confirms the toolchain, picks the pipeline the request needs, and hands off to it. Use when the user asks to find vulnerabilities, scan an application for security issues, reproduce or validate a supplied finding set, or continue an OpenTaint run
license: Apache-2.0
metadata:
  author: opentaint
  version: "0.3.0"
---

# AppSec Agent

The entry point for OpenTaint application-security work. Confirm the environment, decide which of the two pipelines the request needs, and hand off to it in this same session.

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis SAST. Both pipelines run the same machine — MAIN owns the long build and every full-project scan, `orchestrate-stage` subagents own the bounded stages, and all durable state lives under one self-contained `.opentaint/` directory at the project root. They differ only in where the source and sink rules come from:

- **assessment** (`assessment-agent`) — find vulnerabilities the project was not known to have. Source and sink rules come from discovering the project's dependency attack surface
- **enactment** (`enactment-agent`) — reproduce a finding set the user supplies, as verified rules. Source and sink rules come from generalizing those findings into reusable boundaries

The two compose rather than compete: a project can run one after the other, in either order, and again on later commits, all over one accumulating `.opentaint/` tree. Each such run is a *pass*, and choosing a pipeline chooses this pass, not the project's fate.

This skill does no analysis of its own and writes nothing except by handing off. Don't bootstrap the tree here — each pipeline's own setup does that.

## Setup

### 1. Confirm the toolchain

Confirm `opentaint` is on PATH with `opentaint -v`. If it's missing, don't proceed silently — tell the user and offer the install command for their platform, run an install only on explicit confirmation:

- macOS / Linux, in order: `brew install --cask seqra/tap/opentaint` · `npm install -g @seqra/opentaint`
- Windows: `npm install -g @seqra/opentaint`

After installing, run `opentaint health` to confirm everything's resolved.

### 2. Confirm agent nesting

Both pipelines require two subagent levels: MAIN → stage orchestrator → leaf. Confirm the harness permits depth 2 before starting; otherwise ask the user to enable it.

These two checks are the only setup steps the pipeline you hand off to may skip.

## Choose the pipeline

### The pipelines compose

They are not alternatives, and picking one is not a commitment. One `.opentaint/` tree accumulates the artifacts of every pass over it, in either order and as many times as the project needs:

- **enactment, then assessment** — reproduce the supplied report first, then hunt with the rules it produced. The boundaries derived from real findings are exactly the sources and sinks the assessment pass would otherwise have to discover
- **assessment, then enactment** — assess the project, then measure a report against the corpus that pass built. What the report names but the scan missed is now a rule or modeling gap you can point at
- **either, again on a later commit** — the tree is long-lived. A new HEAD makes the model stale, so the pass rebuilds and rescans, and every rule, approximation, and verdict carries over. That's how a run becomes a regression check rather than a one-off

So `mode` in `state.yaml` is the pipeline of the *current pass*, not a property of the tree. Switching it is normal, needs no fresh tree, and strands nothing.

### Read what the tree already holds

If `.opentaint/tracking/state.yaml` exists, find out where the project stands before choosing:

```bash
uv run <skill-dir>/scripts/get_status.py --full
```

Its header prints the current `mode`, the run's levels, the tracked finding set if there is one, and — once the tree has more than one pass — the `passes:` chain. The phase lines say whether that pass is finished or mid-flight.

- mid-flight pass — resume it: hand off to `assessment-agent` for `mode=assessment`, `enactment-agent` for `mode=enactment`. Don't start a different pass over the top of an unfinished one
- finished pass, and the user wants more — that's a new pass, and the choice below applies again
- tell the user what's there either way, in one line: which pass, where it stands, what carried over

### Choose this pass

Decide from what the user brought, then confirm it with them before handing off:

- **enactment** — they supplied findings, a scanner report, penetration-test results, or source-to-sink traces, and want them reproduced, validated, converted into reusable rules, or cross-checked against OpenTaint. "Does OpenTaint catch these?", "reproduce this report", "turn these findings into rules"
- **assessment** — no finding set to measure against; the goal is what the project is vulnerable to. "Find vulnerabilities", "scan this app", "is this endpoint exploitable?"

The signal is whether a finding set exists to be measured against, not the vocabulary. A user who says "audit this against last year's pentest" and has the pentest is enactment; a user who says "reproduce the bug I think is in here" and has only a hunch is assessment.

When the user wants both — reproduce the report *and* find what it missed — say that it is two passes over one tree, recommend enactment first so the assessment inherits its boundaries, and run them one at a time. Never try to drive both in a single pass.

## Hand off

Load the chosen skill in this same session and follow it from its setup:

```
assessment → assessment-agent
enactment  → enactment-agent
```

Not a subagent. MAIN must own the long build and every full-project scan, so the pipeline continues as this session, with the choice above already settled and the toolchain and nesting checks already done. It runs the rest of its own setup — language, levels, bootstrap — and everything after that is its document, not this one.

Tell the user which pipeline you picked and why, in one line, before you hand off.
