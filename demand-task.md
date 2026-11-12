Use ASD-STE100 Simplified Technical English language.

# Stopped task: redundant demand elimination campaign

The user stopped this campaign on 12 November 2026 and requested final results.
Do not resume its queue automatically. The
[final patterns document](docs/design/bidirectional-demand-edge-redundancy-patterns.md)
collects the accepted rules. The campaign has 8,915 individual REDUNDANT
verdicts, 19,716 OPEN targets and a separate checked 6,955-origin joint plan.
The instructions below record the investigation contract. They do not imply
that all targets were classified or authorize further campaign execution.

Follow [the campaign specification](docs/design/bidirectional-redundant-demand-elimination-campaign-20261110.md).
This replaces the completed migration implementation task as the active work.

## Proof contract

Assume no iteration limit. The temporary run-11 limit must never justify
edge removal. A proof must preserve required behavior after any number of
later iterations. A capture that ends at run-11 is finite evidence only.

A pattern can inspect only demand edges, summary edges and submitted initial
facts. It can use their complete identities, ports, marks and field paths,
and their history across runs. Do not use project source, CFG properties,
rule forms, JVM type analysis, report state or other additional information
as an applicability guard. General analyzer semantics remain the subject
of the proof. Previously accepted proofs must meet this contract too.

Treat owner and type strings inside a literal edge key as opaque identity
values. Do not infer enum, immutability, assignability or library behavior
from them. Do not add such information to an edge key to bypass this rule.
An absent submitted-initial capture is missing evidence, not an empty
initial set. A normalized summary premise cannot recover the original C2
initial tail.

## Required run pairs

- OWASP: run-9 and run-11.
- Conductor: run-5 and run-7.
- Stirling-PDF: run-7 and run-9.

Analyze every summarizable unit: each method and each generated inner block
from loop decomposition, including sequential blocks, loop bodies and nested
blocks. Use the full method key and stable block identity to match the same
unit across runs. For each unit, find the nonempty intersection of its final
outgoing demand sets. The complete sets do not have to be equal.
Dump all units, their hierarchy, edges, ports, projections and comparisons.
An inner-block edge is a target even if it has no method-level summary.

The removal point is after the later run, run-(i+2), completes and before its
outgoing demand guides the next run. Run-i is evidence of repetition only.
Keep its demand and execution unchanged. Thus, the selected removal barriers
are OWASP run-11, Conductor run-7 and Stirling-PDF run-9.

## Individual verdicts and joint retirement

The user selected separate individual classifications and a jointly safe
retirement plan. This changes bookkeeping only. Previously, a classification
could be limited by the need to keep witnesses for one combined removal set.
Now classify each edge independently, then check the selected combined set.
Analyzer execution, required behavior and the proof contract stay unchanged.

For each project and later barrier, freeze O: the complete original outgoing
guidance from all methods and inner blocks, before any campaign removal.
Freeze the original retained NORMAL records, NormalTarget routes and other
barrier state too. An individual verdict for X tests removal of only X:
use O minus {X}, with every other original edge and route retained. A checked
individual REDUNDANT certificate can use any other original guidance edge
and any unchanged retained provider, including a guidance edge that has its
own individual REDUNDANT verdict. Such separate certificates do not form one
combined deletion certificate.

Record a joint plan separately. It selects a subset R of individually
REDUNDANT repeated edges and keeps K = O minus R. Edges outside the repeated
target universe stay fixed. Prove that removing all of R is safe together.
Every joint guidance witness must be available in the final K, or have a
checked replacement that ends there. Unchanged NORMAL and other retained
provider state remains available separately. Recheck the complete plan when
its retained witnesses change. Do not combine individual certificates with
mutual providers into an unsupported joint deletion.

A joint plan can keep an individually REDUNDANT representative. Its individual
verdict stays REDUNDANT. Do not call it NECESSARY, or leave it OPEN, only
because the plan keeps it. Conversely, membership in a safe joint removal set
does not replace the individual O-minus-{X} proof. Report individual verdict
totals and joint selected/retained totals separately.

Evaluate [P: NORMAL replay coverage](spec/normal-backed-flow-demand-retirement.md)
for every repeated edge at the later barrier, using the NORMAL records retained
there and the individual O-minus-{X} test. Every repeated edge not covered
there is an elimination target.
Keep P's proved scope unchanged; unsupported inner-block cases remain targets.
The historical P source/CFG guards do not satisfy the current proof contract.
Do not retain a classification under those guards without a new edge-only proof.

Process targets one at a time. Prove each new executable redundancy predicate
with [spec/proof-guide.md](spec/proof-guide.md), then test it against all remaining
targets and save each matched witness before selecting the next target.

Also look for sound generalizations of all known patterns. A wider pattern
can replace several earlier patterns and classify additional edges. State
which earlier patterns it covers, prove the wider contract, and test it
against the complete corpus. Keep existing individual certificates until the
replacement individual proof passes. Recheck all affected joint dependencies
before changing the retirement plan. A union of old predicates alone does
not establish additional coverage.

Use this priority for unresolved targets:

1. FLOW demand edges.
2. Concrete-mark edges without protection.
3. Target edges.
4. All other edges, including protected concrete-mark edges.

Keep unfinished evidence when a priority change defers a target. Deferral is
not a classification. Apply each accepted predicate to the entire target set,
including lower-priority edges, before selecting the next target.

A predicate can be complex. It can use all summary edges and submitted
initials from run-i, run-(i+1) and run-(i+2), across the relevant methods and
inner blocks. It need not be a local edge-shape test. Preserve submitted
facts and emitted C2 initials as separate evidence when both are needed.
The removal point remains after run-(i+2). A historical closure condition
still needs a proof that removal preserves later required behavior.

Continue until every repeated edge has either:

1. A checked redundancy predicate and certificate for its individual
   O-minus-{X} test.
2. A faithful code example, native test and fact trace that reproduce the
   repetition and make a valid sink unreachable when only that edge is removed
   after run-(i+2).

For a necessary-edge case, removing only that edge after run-(i+2) must make
the same valid sink unreachable. Identify the sink by its location and rule.
Use two controls with identical original state through the later barrier.
The baseline retains all of O and reaches the sink after that barrier. In the
deletion control, remove only the selected edge from O. Do not first apply a
joint plan or any other individually proved removal to either control. Keep
all other original demand edges, retained NORMAL providers and confirmed
NormalTarget routes. If any retained route still reaches the sink, the
example does not prove necessity.

Use this acceptance test: the same sink is reachable in the baseline after
run-(i+2), and is unreachable after removal of only the selected edge at that
barrier. A missing initial, summary or source permission is not enough.
Both controls must finish; a timeout cannot prove that a sink is unreachable.
An iteration cap cannot establish this result either.

For every necessary-edge example, i must be at least 3. The earliest valid
pair is run-3/run-5, with removal after run-5. A run-1/run-3 example does not
satisfy this requirement: run-1 has special handling that can invalidate
predicates for later runs.

Unsupported or unexplained edges are not complete cases. Follow the detailed
specification's proof gates, deletion controls, artifact schema and completion
checks. Completion requires individual verdicts for every repeated target and
a separately checked joint plan; it does not require retiring every edge
with an individual REDUNDANT verdict. Keep a durable ledger and resume it
across turns.

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
