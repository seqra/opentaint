# Protected caller input: uncapped recurrence

Constructive Lean 4.35.0. Production unchanged.
[Code, root cause, trace and limits](../../../../docs/reports/bidirectional-protected-original-nontermination-20261117.md).

Only the analyzed second action changes from h.h.MUST to h.f.g.EXACT;
the inverse action is updated with it. Every analyzer definition is checked
against `FlagBody`, including the conservative `!originalH` guard. One mark,
two methods and three ordinary calls have no loops, recursion, cleaners,
special pass rules or unresolved models.

`OriginalCold` checks complete cold states and within-run fixed points.
`OriginalPhase`, `OriginalRounds` and `OriginalSteady` establish every stage
at arbitrary later field limits. `OriginalRecurrence` proves complete
run-9/run-10 state recurrence for every later pair, with 39/45 demand rows,
one NORMAL record and live ZERO/Target routing. `OriginalKernel` shows that
body closure and same-H service pass; only the protected-original guard fails.
`OriginalBounds` preserves all field caps, literal H and one-mark scope.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/protected-original-cycle-20261117/check.py \
  --out /tmp/protected-original-proofs

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ProtectedOriginalCycleTest \
  --tests org.opentaint.dataflow.bidi.ProtectedReplyServiceNativeTest --offline
```

Optional `--dependencies` reuses audited `flag-aware-reply-service-20261117`
proof output after source-hash checks. **172 new constructive claims; 6,763
cumulative claims in 356 modules** pass. Only `propext` and `Quot.sound`
are allowed. No custom axiom, classical choice, hole or native decision
oracle is used. No earlier stopping point or finite hard limit proves the cycle.

All **11 native tests pass**. The unchanged full-program diagnostic is
**run-31/POLICY**, zero NORMAL reports; the scoped reference retains its
NORMAL observation from run-5. This is not full production integration or
whole-engine equivalence. No repair is selected here. Raw data and compiled
artifacts remain outside the repository.
