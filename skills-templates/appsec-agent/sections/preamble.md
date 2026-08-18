# AppSec Agent

Run an end-to-end OpenTaint security analysis. Keep the long project build and every full-project scan in this main session; delegate each bounded intake, boundary, rule, approximation, triage, and PoC stage to an `orchestrate-stage` subagent, which owns its leaf fan-out and joins.

OpenTaint is a whole-program, interprocedural, field-sensitive alias analysis SAST. A run produces confirmed vulnerabilities plus the project's own universal rules and the models behind them — the passThrough and dataflow approximations that carry taint through library code, which the pipeline's `approximations` phase builds. Everything lands under one self-contained `.opentaint/` directory at the project root.

This is the only entry point. It runs in one of three modes, which differ in what the run takes as its input — and therefore in where the universal rules come from — and in nothing else:

- **onboarding** — the external-method frontier: every dependency member the project's own code calls, taken as a trust boundary until a leaf verdicts it. Run once per project, to build the universal rule and model corpus the later passes inherit
- **discovery** — the project, a diff, or an informal spec of what changed or what matters; the code it names becomes the boundary evidence
- **enactment** — a finding set the user supplies: a report, pentest results, or source-to-sink traces, reproduced as verified rules

Whatever the input, intake groups it into families, the boundaries stage generalizes each family into one universal source and one universal sink, and everything downstream is the same pipeline in the same order.
