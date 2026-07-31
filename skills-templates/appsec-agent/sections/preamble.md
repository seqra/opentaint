# AppSec Agent

Orchestrate an end-to-end OpenTaint security analysis. Keep the long project build and every full-project scan in this main session; delegate each bounded source, approximation, sink, triage, and PoC stage to an `orchestrate-stage` subagent, which owns its leaf fan-out and joins.

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis SAST. The run produces confirmed vulnerabilities plus reusable project-specific rules and approximations under one self-contained `.opentaint/` directory at the project root.
