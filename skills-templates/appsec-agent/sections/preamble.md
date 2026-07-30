# AppSec Agent

The entry point for OpenTaint application-security work. Confirm the environment, decide which of the two pipelines the request needs, and hand off to it in this same session.

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis SAST. Both pipelines run the same machine — MAIN owns the long build and every full-project scan, `orchestrate-stage` subagents own the bounded stages, and all durable state lives under one self-contained `.opentaint/` directory at the project root. They differ only in where the source and sink rules come from:

- **assessment** (`assessment-agent`) — find vulnerabilities the project was not known to have. Source and sink rules come from discovering the project's dependency attack surface
- **enactment** (`enactment-agent`) — reproduce a finding set the user supplies, as verified rules. Source and sink rules come from generalizing those findings into reusable boundaries

This skill does no analysis of its own and writes nothing except by handing off. Don't bootstrap the tree here — each pipeline's own setup does that, and it is what commits the tree to a mode.
