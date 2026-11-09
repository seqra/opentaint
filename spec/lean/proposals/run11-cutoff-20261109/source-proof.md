# Run-11 cutoff: source correspondence before implementation

The selected major change is a default bidirectional execution cutoff after the
completed forward run-11 barrier. Before this change, the default increasing
policy continues while demand remains. After this change, the default policy
returns RUN_LIMIT at run-11 even with remaining demand. RUN_LIMIT is not a proof
of convergence. The separate report-confidence change has another owner.

Keep field transfer, C2/C5, layers, rules, aliases, targets, demand and the
1,1,2,... schedule unchanged. Keep the opt-in RUN_INDEX schedule. Keep the
legacy --iteration-limit diagnostic and ignored-value contract unchanged.

The current native driver establishes the following correspondence:

- RunManager returns a RunResult. runOnce enters the barrier only when status
  is COMPLETE. Failed or incomplete engines do not call the policy barrier.
- barrier prepares report state, persists accepted records, builds the handoff
  and logs the completed frontier before it selects Next.
- The first forward stop branch checks an empty outgoing demand map. It must
  stay before the policy branch. The cap must therefore not rename a genuine
  early convergence result.
- The policy callback is called only after a complete forward run. A decorator
  can stop run-11 there; backward run-10 still reaches forward run-11.
- All fallible preparation and cancellation checkpoints precede report.commit.
  The driver returns Next.End only after that commit. A barrier failure must
  preserve the previous accepted report rather than publish run-11 state.
- nextConfig asks the policy for the next field limit. A cutoff at run-11 must
  return Next.End and must not construct run-12.

Implementation mapping:

1. HardRunLimitPolicy delegates fieldLimitSchedule, fieldLimit and timeout.
   Its continuation is run.index < lastForwardRun AND delegate continuation.
   lastForwardRun is positive and odd; the configured default is 11.
2. IterationPolicy.stopReason(run) defaults to POLICY. The decorator returns
   RUN_LIMIT when its cap stops the run; before that it keeps the delegate's
   stop reason. The driver uses it in the existing policy stop branch.
3. configuredIncreasingLimits selects the same schedule as before, then adds
   the decorator. JVM normal-project and rule-test frontends already use that
   factory. Explicit native test policies remain explicit overrides.

Cap.lean is an executable abstraction of those ordered decisions. It proves a
positive eleven-index witness, odd forward run-11, no next run-12, convergence
priority, abnormal-run exclusion, earlier delegate behavior and the bound for
next steps from reachable indices. The cutoff theorem requires complete,
forward and nonempty demand. It claims no dataflow precision or termination
property for the prior unbounded policy.

Native tests must cover the default factories and a real persistent-demand
engine through run-11, earlier empty-demand completion, delegate stop reason,
schedule/timeout forwarding, and a failing final barrier. Provisional findings
and their identity are tested by their separate reporting change. Keep the
existing legacy cap option test green.

Reports.lean supplies separate constructive report-selection laws. It proves
confirmed precedence and latest-forward candidate selection at RUN_LIMIT; it does
not turn a provisional witness into a concrete source-to-sink path.
