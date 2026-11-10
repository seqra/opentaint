Use ASD-STE100 Simplified Technical English language.

# Current task: redundant demand elimination campaign

Follow [the campaign specification](docs/design/bidirectional-redundant-demand-elimination-campaign-20261110.md).
This replaces the completed migration implementation task as the active work.

## Required run pairs

- OWASP: run-9 and run-11.
- Conductor: run-5 and run-7.
- Stirling-PDF: run-7 and run-9.

For every full method key, find the nonempty intersection of its final outgoing
demand sets in the two runs. The complete sets do not have to be equal.
Dump all methods, edges, scopes, projections and comparison results.

The removal point is after the later run, run-(i+2), completes and before its
outgoing demand guides the next run. Run-i is evidence of repetition only.
Keep its demand and execution unchanged. Thus, the selected removal barriers
are OWASP run-11, Conductor run-7 and Stirling-PDF run-9.

Evaluate [P: NORMAL replay coverage](spec/normal-backed-flow-demand-retirement.md)
for every repeated edge at the later barrier, using the NORMAL records retained
there. Every repeated edge not covered there is an elimination target.

Process targets one at a time. Prove each new executable redundancy predicate
with [spec/proof-guide.md](spec/proof-guide.md), then test it against all remaining
targets and save each matched witness before selecting the next target.

Continue until every repeated edge has either:

1. A checked redundancy predicate and certificate.
2. A faithful code example, native test and fact trace that reproduce the
   repetition and show the loss of required behavior when that edge is removed
   after run-(i+2).

Unsupported or unexplained edges are not complete cases. Follow the detailed
specification's proof gates, deletion controls, artifact schema and completion
checks. Keep a durable ledger and resume it across turns.

## Execution constraints

Freeze the reference runtime and configurations from the campaign specification.
Use source Gradle `runProjectAnalyzer`, FULL mode and the `1,1,2,...` schedule.
Reuse suitable complete captures. Keep project scans serial. Work in the main
checkout; retain portable evidence in the repository.

This task is an investigation and proof campaign. Keep production analyzer
semantics unchanged. Use controlled deletion only in the small test cases.
Production optimization needs a subsequent implementation proposal and selection.
Highlight any required major semantic decision and ask for the intended behavior.

Always include the latest reached, completed and accepted forward run in reports.
Use subagents as specified by the campaign, with one coordinated target queue.
