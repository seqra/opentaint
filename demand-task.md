Use ASD-STE100 Simplified Technical English language.

# Current task: redundant demand elimination campaign

Follow [the campaign specification](docs/design/bidirectional-redundant-demand-elimination-campaign-20261110.md).
It defines the reference runtime, capture procedure, proof contract, artifact
schema, individual verdicts, joint plan and completion checks.

The main goal is to remove repetition itself. Track the demand evolution
graph and prefer closed-evolution patterns over replacing X with another
repeated provider; see the campaign's
[pattern guidance](docs/design/bidirectional-redundant-demand-elimination-campaign-20261110.md#main-pattern-goal-remove-repetition).

1. Compare the demand sets **after handoff** for OWASP run-9/run-11,
   Conductor run-5/run-7 and Stirling-PDF run-7/run-9. Include methods and
   all generated inner blocks. Find each unit's nonempty intersection and
   dump all results. Compare retained next-run demand rows, not pre-handoff
   summary origins or callback counts.
2. Check each repeated row against the known redundancy patterns. Rows
   without a checked certificate are the next elimination targets.
3. Process targets one at a time: FLOW, unprotected concrete marks, Target,
   then the rest. Prove each new predicate with
   [spec/proof-guide.md](spec/proof-guide.md), apply it to the complete
   remaining corpus, and generalize known patterns where sound.
4. Continue until each target has either a checked redundancy predicate or
   a faithful code example, native test and fact trace that show valid sink
   loss when only that demand row is removed.

Evaluate removal **during the run-(i+2) handoff**, after its ordinary demand
construction and before publication to run-(i+3). Keep run-i unchanged.
Use only demands, summary edges and submitted initial facts available by
that handoff. Assume no iteration limit. Necessary-edge examples must use
i >= 3. Keep individual verdicts and the jointly safe removal plan separate.

Reuse compatible evidence and keep a durable ledger. Reconcile historical
origin-based results with the post-handoff row inventory before reusing them.
Use the campaign's pinned runtime and configurations, source Gradle tasks
and serial project scans. Work in the main checkout. Keep large evidence
outside Git under [the external-data policy](docs/reports/EXTERNAL_DATA.md).

Keep production analyzer semantics unchanged. Highlight any required major
semantic decision and ask for the intended behavior. Always report the
latest reached, completed and accepted forward runs. Use subagents with one
coordinated target queue, as specified in the campaign.
