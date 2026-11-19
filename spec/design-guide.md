# Design guide: problem first, prototype before proof

Use ASD-STE100 Simplified Technical English language

Use this guide together with [proof-guide.md](proof-guide.md). 
A proof shows that a model has a property. It does not show that the
model is the runtime, that the property is the real problem, or that
the cost is acceptable. A native prototype shows those three.

## Rules
1. **Start from a real trace.** A rule needs one real-project instance
   of its trigger, with a measured count. A synthetic example is
   allowed only as a reduction of that instance.

2. **Find counterexamples against the native runtime.** A
   counterexample that needs earlier proposed rules is a defect of the
   proposal. Fix or drop the earlier rule. Do not add a repair rule.

3. **Prototype natively before proof.** Order of work:
   1. Ablation: remove or bypass the suspected cause by hand. Does the
      real case change?
   2. Native prototype of the one rule, behind a flag, in isolation.
   3. Measurement on all reference projects and the rule tests.
   4. Only then: Lean model, proofs, spec text.

   Proofs are for a mechanism that already works natively. A stop in a
   reference model is not evidence.

   Use worktrees for prototyping: (1) create a fresh branch, (2) create WT with the branch, (3) implement prototype, perform all measurements, (4) commit the branch and cleanup WT 

4. **Measure in shadow mode when you can.** If a change is a decision
   (stop, drop, skip), first log what it would decide and compare with
   the unchanged result. This costs one run and no risk.

5. **State the cost with a volume.** For each rule give: where it
   executes (per fact, per offer, per summary, per handoff, per run),
   and the measured volume of that site on the largest project. A local
   bound such as "at most two starts" is not a cost. New per-fact or
   per-offer work needs a measured saving that pays for it.

6. **Gate each rule alone, per project.** Confirmed findings equal to
   the pinned baseline; wall time and peak memory not worse. Use at
   least three interleaved launches. A difference smaller than the
   native variance is not a result.

7. **One rule in, or one rule out.** A rule that fails its gate is
   withdrawn. If the rule count grows while the real failure stays,
   stop and return to rule 1. Two repair-of-repair steps in a row are
   the signal.

8. **Do not ban a repair class in the task text.** State the property
   to keep (for example: confirmed reports equal to the baseline) and
   let the measurements select the mechanism. Removing work and
   changing a stop test are legal repairs when the property holds.

9. **Prefer the outermost layer.** Try the driver or the handoff
   before the fact rules. A change that runs once per run is easier to
   measure, prove and remove than a change to field transfer.

10. **Compare with the trivial alternative, and attack the draft.**
    Before a proposal is accepted, replay its decisions on existing
    logs, give it to a reviewer whose task is to break it against the
    code, and compare it with the cheapest change that could give the
    same result (a constant, a flag, a removed step). The first draft
    of the driver-stop proposal lost two of its three mechanisms in
    this step.

11. **Write down what was not measured.** Each report ends with the
    blind spots and the weakly supported verdicts.

## Checklist for a proposal

```text
[ ] Failure class and real trace (project, run, owner, count)
[ ] Ablation result on the real case
[ ] Native prototype result: findings, time, memory, 3 launches
[ ] Execution site and measured volume of each new operation
[ ] Selected semantic scope: changed / unchanged (proof-guide.md)
[ ] Proof scope, and each difference between model and production
[ ] Withdrawal condition
```
