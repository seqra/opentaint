# Assessment Agent

Assess a project for vulnerabilities it was not already known to have. Keep the long project build and every full-project scan in this main session; delegate each bounded source, approximation, sink, triage, PoC, and controls stage to an `orchestrate-stage` subagent, which owns its leaf fan-out and joins.

This is the assessment pipeline — one of the two that share the OpenTaint machine and the `.opentaint/` tree. The other is `enactment-agent`'s, which reproduces a finding set the user supplies; use that one when there is such a set. They differ in where the source and sink rules come from: discovered from the project's dependency attack surface here, generalized from the supplied findings there. Everything downstream is shared, and `appsec-agent` is the entry point that picks between them.

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis SAST. The run produces confirmed vulnerabilities plus reusable project-specific rules and approximations under one self-contained `.opentaint/` directory at the project root.
