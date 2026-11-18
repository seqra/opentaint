Use ASD-STE100 Simplified Technical English.

# Task: termination and soundness investigation

Improve the [demand refinement and termination spec](spec/demand-refinement-and-termination.md)
through repeated termination and soundness counterexample discovery and repair. Follow
[spec/proof-guide.md](spec/proof-guide.md). Keep the
[counterexample catalogue](docs/reports/bidirectional-demand-termination-counterexamples-20261115.md)
current. These documents define the selected rules and the known examples.

We analyze synthetic data-flow reachability. Use marking and observation
rules. Do not describe the examples as real vulnerabilities.

## Four-phase cycle

```text
repeat:
    1. Find and prove a new termination counterexample to the current approach.
    2. Fix the termination counterexample. Prove that the repair handles it
       and preserves the earlier examples. Update the consolidated proposal.
    3. Search for a soundness counterexample: the analyzer before the
       termination fixes tracks a valid mark-to-observer relation, but
       the current proposal loses it. If found, proceed to phase 4.
    4. Fix the soundness gap. Prove that the repair restores the lost
       relation and preserves earlier termination and reachability results.
       Update the consolidated proposal. Repeat phase 3 before phase 1.
```

If a proved open example already exists, start with phase 2 for a termination
counterexample or phase 4 for a soundness gap. The catalogue lists the current
proved open examples. Start with its first open example; do not use a
resolved historical case as the current target.
Do not rediscover it or treat an older repair as the current approach.
After a validated repair, perform phase 3 before returning to phase 1.
If phase 1 finds no new example, still perform phase 3. Continue while a new
termination or soundness counterexample is discovered. For the current goal,
finish only after all known open examples have a validated repair and fresh
searches in phases 1 and 3 find no further example in an explicitly stated
scope. Report the checked bounds and unsupported cases. Do not infer universal
termination or soundness from these results.
Maintain an active goal for the current phase.

## Phase 1: discover a termination counterexample

1. Pin the selected rules and proof sources. Keep all selected mechanisms
   enabled. Do not change a guard, transfer or activation condition to make
   an example fail.
2. Use fully analyzed ordinary code plus marking, observation and cleaner rules.
   Loops, including nested loops, and direct or mutual recursion are allowed.
   Use no special pass rules, unresolved
   library models or predefined summaries. Ordinary calls and field
   transfers are allowed. Prefer small examples and general failure patterns.
3. Assume no hard iteration limit. A finite run or repeated count is not a
   proof. Find an exact recurring demand or another constructive invariant
   that prevents natural termination. Check the cold prefix, the special
   run-1/run-2 policies and the fixed point within each run.
4. Provide the code and a per-run trace for every analyzable method/block.
   In forward runs, put demand, submitted facts and emitted initials above
   the body; put published NORMAL/DEMAND summaries after the complete body.
   In backward runs, reverse this placement. Use code variable names and
   show ZERO/Target routing, saved NORMAL replay, protection and exclusions
   when they affect the result.
5. Prove the uncapped recurrence in Lean. Add native regression/component
   tests. State any difference between the formal reference and production;
   a finite native cutoff does not prove the proposed approach nonterminating.
6. Record the example, root cause, proof scope and latest reached run in the
   catalogue. Then proceed to phase 2.

## Phase 2: fix the termination counterexample

1. Identify the mechanism that renews unresolved demand. Design a general
   progress or redundancy rule.
   Do not use example-specific field names, method names, mark names or
   iteration numbers as the repair.
2. State current versus proposed behavior. Highlight every major semantic
   change, affected invariant and proof. If the intended behavior is
   ambiguous, show a code example with its fact trace and ask for a decision.
   Do not silently change another mechanism to close a proof gap.
3. Prove that the repair terminates the example without a hard limit. Also
   preserve earlier termination results and valid mark-to-observer relations.
   Check negative controls and variants that break the repair's guards.
   Explain why no required route is lost. Do not claim universal termination
   from a finite collection of examples.
4. Analyze negative consequences, including additional initials, summaries,
   subscriptions, caller work, stored state and field-path combinations.
   Give bounds or representative before/after workload counts. A repair
   must not replace repetition with uncontrolled propagation or storage.
5. Keep truncation and ordinary global, FL(Dc)+1 entry and FL(Dp)+1 output
   limits. Enumerate and justify every proposed exception; exceeding a
   limit must not become the common case. Do not compose full suffix evidence
   across calls or introduce an unrestricted raw-summary archive.
6. Preserve increasing refinement precision and eventual precise observations
   under an uncapped schedule. Do not force termination by accepting unresolved
   candidates, hiding demand, canceling required Targets or weakening the
   stopping test. Prefer certificates based on existing demand, summary edges
   and submitted facts; add no JVM type reasoning.
7. Validate constructive proofs and relevant native tests. Update the
   consolidated proposal, example statuses and traces. Keep one consistent
   current contract; label earlier rules and proofs as historical where needed.
   In the consolidated proposal, mark recursion repair rules with `[REC]`
   and loop repair rules with `[LOOP]` next to their rule IDs. Use both
   markers when a rule fixes both kinds of issue. Link each rule to its
   counterexample and proof.
   Then perform phase 3 before searching for the next termination example.

## Phase 3: discover a soundness counterexample

1. Pin the baseline analyzer revision before the termination fixes and the
   current proposal's rules and proof sources. Compare the same program,
   rules, entry points, mark mode and field-limit schedule. Do not disable
   a selected proposal rule to make the example fail.
2. Use the example scope from phase 1, including cleaners, loops and recursion.
   Find a marking point, full mark and observer such that the baseline can
   track a valid reachability relation between them, but the proposal cannot.
   Compare that relation, not only report IDs or total report counts. A
   different witness is acceptable if it proves the same required relation.
3. Trace both analyses from the cold start. Use the annotation format from
   phase 1 for every method/block. Show the baseline derivation and the exact
   proposed step that loses the fact, initial, summary or demand needed for
   the observer. Include handoffs, source permissions and ZERO/Target routing.
4. Prove the loss without an iteration limit. Show either natural completion
   without the required relation or an invariant that prevents its recovery
   on every later run. A delay, timeout, policy cutoff or missing result in a
   finite scan is not enough. Check whether another retained route recovers it.
5. Prove the baseline witness and the proposed loss constructively in Lean.
   Add native baseline and regression/component tests. If the proposal is not
   implemented, distinguish its reference model or adapter from production.
   Do not count a model-alignment error as an analyzer counterexample.
6. Record the code, paired traces, lost relation, responsible proposal rule,
   proof scope and latest reached run for both analyses in the catalogue.
   Proceed to phase 4 for each proved loss. Keep the `[REC]` and `[LOOP]`
   marker requirements when the repair addresses recursion or loops.

## Phase 4: fix the soundness gap

1. Start from the proved loss in phase 3. Identify the rule that removes or
   blocks the required reachability. Design a general repair, not a special
   case for the example's fields, methods, marks or iteration numbers.
2. Apply phase 2's semantic review, workload bounds, field limits and
   conservative-control requirements. Highlight major semantic changes and
   obtain the intended behavior if it is ambiguous. Do not restore
   reachability through an unrestricted archive or field-path enumeration.
3. Prove constructively in Lean that the repaired proposal tracks the same
   required marking-point/mark/observer relation as the pinned baseline.
   Trace the restored route through initial emission, propagation, summary
   application, restriction and handoff. An unrelated report or matching
   report count is not a repair.
4. Preserve all earlier termination and reachability results. Check that the
   repair does not recreate a resolved demand cycle, weaken the stopping
   rule, bypass a field cap or accept an invalid observation. Validate the
   regression and negative controls with native tests or explicit proposal
   adapters; keep their scope separate from production.
5. Update the consolidated proposal, constructive proofs, paired traces and
   catalogue status. Use the `[REC]` and `[LOOP]` markers from phase 2 where
   applicable. Repeat phase 3 after the repair, then return to phase 1 when
   no further soundness gap is found in the checked scope.

## Working rules

Work in the main checkout. Production implementation stays unchanged unless
the user explicitly requests implementation. Proposal models, proofs and
native tests are in scope. Do not commit unless requested.

Keep large captures and compiled artifacts outside Git under
[the external-data policy](docs/reports/EXTERNAL_DATA.md). Keep the code,
essential trace and proof explanation readable in repository documents.
Always distinguish natural completion from a policy cutoff, and report the
latest reached/completed run, such as run-5 or run-10. State proof and native
validation scopes separately. Do not remove an older example from validation
merely because a later repair targets another mechanism.
