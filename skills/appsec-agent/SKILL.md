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

This skill does no analysis of its own and writes nothing except by handing off. Don't bootstrap the tree here — each pipeline's own setup does that, and it is what commits the tree to a mode.

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

### An in-flight run decides for you

If `.opentaint/tracking/state.yaml` already exists, the tree is already committed to a mode and the choice is made — resume that pipeline. Read the mode from status rather than by hand:

```bash
uv run <skill-dir>/scripts/get_status.py --full
```

Its header prints `mode=`, the run's levels, and the current phase. `mode=assessment` → `assessment-agent`; `mode=enactment` → `enactment-agent`. Tell the user what's in flight and where it stands before continuing.

A mode is not switchable: the bootstrap refuses it, because each pipeline's tracking is meaningless to the other — an assessment tree has no reference set behind it, and an enactment tree's rules were never derived from a dependency sweep. If the user genuinely wants the other pipeline over the same project, that is a fresh `.opentaint/` tree, and say so plainly rather than starting one silently.

### A fresh run

Decide from what the user brought, then confirm it with them before handing off:

- **enactment** — they supplied findings, a scanner report, penetration-test results, or source-to-sink traces, and want them reproduced, validated, converted into reusable rules, or cross-checked against OpenTaint. "Does OpenTaint catch these?", "reproduce this report", "turn these findings into rules"
- **assessment** — everything else: no finding set, the goal is what the project is vulnerable to. "Find vulnerabilities", "scan this app", "is this endpoint exploitable?"

The signal is whether a finding set exists to be measured against, not the vocabulary. A user who says "audit this against last year's pentest" and has the pentest is enactment; a user who says "reproduce the bug I think is in here" and has only a hunch is assessment.

When it's genuinely ambiguous — a report exists but the user wants new findings too — ask. Don't fold both into one run: pick the pipeline they care about now, and note that the other is a separate run over its own tree.

## Hand off

Load the chosen skill in this same session and follow it from its setup:

```
assessment → assessment-agent
enactment  → enactment-agent
```

Not a subagent. MAIN must own the long build and every full-project scan, so the pipeline continues as this session, with the choice above already settled and the toolchain and nesting checks already done. It runs the rest of its own setup — language, levels, bootstrap — and everything after that is its document, not this one.

Tell the user which pipeline you picked and why, in one line, before you hand off.
