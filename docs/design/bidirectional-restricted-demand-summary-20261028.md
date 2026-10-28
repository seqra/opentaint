# Proposed modification summary

Scope: run-1, its transition to run-2, and later restricted runs.
“Original AP” means the original demand and summary protocol.
“Later logic” means an existing selected extension. “New logic” means a
change selected for this iteration. This table describes the final design,
not implementation completion.

| Part | Change | Before | After | Basis |
|---|---|---|---|---|
| Restricted initial emission | Modify | Actual queries can start work without demand | Start only from fixed demand; share FLOW starts; concrete entries need an actual matching mark | Original AP |
| Summary publication | Modify | SQ can permit raw answers and scan them again on new input | Apply complete paired entry/exit restriction; new inputs grant no new permission | Original AP |
| Outgoing demand selection | Modify | Select every run-1 publication | Use the original selection rule; keep other eligible NORMAL singleton summaries as records | Original AP |
| StrongQueries and query-policy state | Remove | Extra starts, raw-answer permission and automatic ANY-to-EXACT completion | Remove these permissions and their replay scans | Original AP authority |
| STAR handoff, intersection and validation | Modify | Widen STAR to ANY; reject valid static STAR; mishandle some E intersections | Keep STAR; correct concrete E intersections; accept bounded named-field STAR inputs | Original AP handoff plus later correlated-STAR logic |
| Abstract STAR demand exclusions | Modify | Preserve E or reject nonempty E | Ignore E on both demand endpoints; retain actual, concrete and native-record E | New logic |
| Run-1 static exit path | Modify | Insert the summary immediately | Jump to NormalExit; apply exit rules, then common summary emission; run no return transfer | Original AP exit processing plus a new run-1 shortcut |
| Static write-point supply | Modify | Nonstatic concrete writes need outward caller binding to supply the pool | Supply the executed concrete output immediately; keep the FLOW writer; summary processing is independent | New rule in later static handling |
| Added producer replay channel | Remove | Separate index and callbacks repeat caller binding before pool supply | Remove the index, delivery path and dedicated counters | Cleanup of the intermediate implementation |
| Static guidance stores | Add | Static/static rows and exit-killed writers are lost | Keep private B keys and thin exit candidates; retain lost keys after final survivor pruning | New logic |
| Joined writer binding | Add | A killed callee writer has no caller writer guide | Bind primitive and recursively caller-bound writer seeds through existing actual inputs before release | New logic |
| Static demand closure | Add | SQ covers some missing static guidance | Inherit B through callers; compose through static positions; freeze guidance for run-2 only | New logic |

Run-1 still has no ND edges. Keep existing field transfer, cleaners, full
rule guards, rule identities, aliases, mark modes, native-record handling
and run limits. New static completion creates demand guidance only; it
creates no NORMAL record, pool supply or executable run-1 summary.

The complete contract and proofs are in
[restricted-demand-static-closure.md](../../spec/restricted-demand-static-closure.md).
