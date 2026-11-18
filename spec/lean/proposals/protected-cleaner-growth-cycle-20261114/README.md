# Protected concrete cleaner/global-cut cycle

[Code and annotated traces](../../../../docs/reports/bidirectional-protected-cleaner-growth-nontermination-20261114.md).

The two-call ordinary read-ff/write-ff example has an exact-root selected
cleaner before its branches. The new MUST-preserving rule is in force.
Recurring nonempty inputs pass that cleaner with unchanged layers and
existing survivor protection. Real global cuts in concrete T relations
are outside the new unprotected FLOW/MUST-to-NE law. Source and sink are
ordinary whole-object rules; there is no pass rule, loop or recursion.

- `ProtectedGrowth.lean`: complete marked C2 witness cells and companions,
  MAY/NE selector variants, the selected cleaner, two actual one-field
  operations with a cut after each, own-row C5, and rejection/survival under
  an arbitrary uniform-coverage provider list.
- `ProtectedCycle.lean`: real two-call bindings, source/sink renewal,
  run-1 STAR/DEMAND request answer and body, run-2 bootstrap, NORMAL run-3
  reader, and an uncapped induction. The same ZERO-to-DemandTarget repeats
  after run-3/run-5 and every later forward run.

```sh
python3 spec/lean/proposals/protected-cleaner-growth-cycle-20261114/check.py \
  --out /tmp/protected-cleaner-growth-proof
```

The checker first rechecks the earlier 321 declarations, including all
previous example closures and `RootCleanerPolicy`. Latest result:
**38 new claims, 359 total, 21 modules**. Only `propext` and `Quot.sound`
are permitted; no classical/custom axiom or proof hole is accepted.
Sources are hashed in the external receipt:
`protected-cleaner-growth-cycle-20261114/proofs-v2/receipt.json`.

The formal witness replay reaches **run-31**; the induction has no cap.
Four native component/bootstrap tests pass, including a real **run-3**
helper analysis. The current core has MAY cuts rather than NE, so no
whole-program native execution of the proposed mechanism is claimed.
The report gives the remaining unchanged-compaction embedding argument;
this is not a full JVM/scheduler correspondence theorem. Production
code and the selected semantics remain unchanged.
