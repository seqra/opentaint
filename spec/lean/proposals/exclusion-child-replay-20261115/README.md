# Existing child cover with native field exclusions

The proposed change extends owned saved-NORMAL reply routing to nonempty
operand and record field exclusions. It retains native matching, all E,
raw C2 queries, current matching, paired C5, cuts, caller offers and original
initial origins. Production is unchanged.

- `ExclusionCover.lean` proves constructive concrete reader coverage for
  arbitrary operand/premise/result exclusions at their original scopes.
  It also checks the fixed output service and real truncation coverage.
- `ExclusionRoutedCalls.lean` reuses the previous E-aware owner/call machine.
  The only changed operation is the reply filter. Every kept reply equals
  the old reply; any fixed native postprocessing performs no more work.
- `ExclusionCompatibility.lean` keeps unsupported concrete/MUST/protected
  services, empty-mask behavior and earlier cleaner/protection results.
- Twelve `ExclusionCertificate*.lean` modules check complete cold states,
  quiescence, handoff, producer permission and natural final DATA/Target
  emptiness. The Growth module also checks complete old/new state equality
  at every run-1 through run-11.

The latest required completed reference is **run-15**; the new overwrite
case completes at **run-9**. Structured diagnostics reach **run-19**. Native
validation is component-only: seven existing-operator tests pass. No project
run or whole-native-core termination proof is claimed.

Read the [approach](../../../../docs/design/bidirectional-exclusion-aware-child-replay-20261115.md)
and the [report](../../../../docs/reports/bidirectional-exclusion-aware-child-replay-20261115.md).
The report embeds the new principal trace and all key metrics. Larger JSON,
proof output and native logs are external under
`docs/reports/data/exclusion-child-replay-20261115/`.

Run in a fresh external directory:

```bash
python spec/lean/proposals/exclusion-child-replay-20261115/check.py \
  --out /absolute/external/fresh-proof-directory
```

The checker rebuilds the preceding selected approach, counterexample and old
acceptance packages, then all new claims. It rejects custom axioms,
classical choice, admitted claims and native proof shortcuts. Only `propext`
and `Quot.sound` may occur. Python generates untrusted witnesses; the Lean
kernel checks them. A finite screen horizon is never a termination proof.

The native adapter still must bind the existing qualified child-service
predicate to actual alias, rule and port handling. The independent screen
also identifies one unchanged baseline reference-alignment gap. Neither
limitation is hidden by the concrete prefix cover theorem.

Full fresh proof rebuild passed: **399 new theorems, 1,397 audited declarations,
79 modules**. Seven native component tests passed.
