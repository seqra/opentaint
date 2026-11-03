# Release closed execution roots before joined static binding

Date: 3 November 2026. Reference runtime:
`050b83cfb7b2e75856ea113c44d0a2d6b707250d`.
Status: **UNSELECTED**. No Kotlin, native test, reader or runtime change is included.
This package is separate from candidate-directed static pruning. Optimization
ranking remains provisional pending the measured heap dominance report.

## Semantic scope

Selected major semantic changes: **none**. The proposed lifecycle optimization
would detach selected execution roots after a successful runner join and after
necessary snapshots, before pure joined static binding. All bound outputs and
new-run handoff publication must remain identical. No source permission, ZERO,
C2/C5, layers, mark policy, field transfer, report identity, AP key equality or
hashing change is proposed. Existing owner, raw ID, port and mark identities must
remain unchanged; restoring equal-valued replacements is not permission to alter
canonical identity used by identity maps.

Currently RunManager joins the workers, borrows joined actor state for static
completion, then freezes analyzers and releases runners. A future implementation
would insert a separate execution-root detachment at the successful joined
boundary. Do not simply call the existing full analyzer freeze early: its actual
read/write footprint and data needed by joined binding have not been proved safe.
Diagnostic and normal-contributor snapshots must finish first.

The state model splits data into retained J and detachable execution X. S is the
completed diagnostic/contributor snapshot. The binder has signature
`J -> Except E Output`: it reads only J and cannot access X in this model.
**That signature/read-footprint equivalence has not been proved for Kotlin.**

## Required retained footprint J

Keep all actual binding inputs and immutable identity objects, including:

- ActualInput links and their full binding-required payloads, including ROOT
  subscriber inputs. The measured ActualInputs subgraph is not a release target.
- State common summaries, port/scoped summaries and Targets/outgoing Targets.
- Raw static candidate IDs, their raw interner rows/seeds and owner/port/mark data.
- Completed body-work/diagnostic counters and normal contributor snapshots, with
  child/scoped information copied before dropping the live execution owners.
- Shared AP managers/interners, IR objects and the existing rewrite SoftManager.
  This proposal must not clear, replace or weaken these shared structures.

J is the entire required read closure, not merely a list of top-level fields.
A Kotlin adapter must prove that no retained input link, summary, key, target or
snapshot aliases a container that the release clears in place. Preserve the
required links/objects themselves; a memory census cannot establish read safety.

## Candidate execution roots X

Only after successful join and completed snapshots, consider dropping references
to execution edge stores; local/call services; point resumes; completed work
queues and execution initial-store indices; physical/local publication lookup
indices and completions; and CFG delivery caches. These are candidates subject
to the real read-footprint proof. Initial-store indices are distinct from the
ActualInput and ROOT subscriber inputs that must stay in J. Likewise, publication
lookup machinery is distinct from immutable summary/port rows and any input
links still needed by static binding.

Detachment must use ownership-safe field/container operations. Do not mutate a
key or shared retained container to make a root smaller. No shared AP interner,
IR or rewrite SoftManager clearing is proposed. Dropping one field does not prove
that its objects are unreachable; retained aliases can keep the same data live.

## Constructive lifecycle model

The finite lifecycle is running -> joined -> snapshotted -> bindingReady -> bound,
with failure exits. Work, local publication and delivery are admitted only while
running. Successful joining is the required quiescence boundary; no transition
back to running is provided. The proof models the closed protocol contract, not
Kotlin threads, cancellation, outstanding messages or alias discipline.

Snapshot capture occurs while X is retained. Early release before this snapshot
is a no-op. Detachment changes only execution-root presence and readiness phase;
every projection/read of J and S stays equal. The generic proof preserves all
raw ID/owner/port/mark projections. It is not a proof of JVM reference identity.

The binder computes an immutable result from J. A failed join or binding attempt
exports no new-run result. Final commit is allowed only after successful binding.
Here `published` means the attempted run's new handoff, not a prior accepted
forward report. A failed attempt must preserve any prior accepted report outside
this new-run publication state.

Old and proposed paths are equal after binding/commit/final cleanup whenever the
input is snapshotted and the same J-only binder is used. Terminal-only final cleanup and the
early detach are idempotent. Final cleanup cannot skip a pending snapshot. The model includes a retained-alias witness showing
why this proves no garbage collection/free-byte result, and an execution-reading
binder counterexample showing why the read-footprint prerequisite is necessary.

## Unproved prerequisites and measurement limits

Before selecting a runtime implementation, prove its exact retained read closure
through joined static binding, completion, summary export and later handoff.
Prove successful joining closes every worker and excludes later live work,
publication and delivery; failure must not publish early. Verify snapshot ordering,
owner/port/raw-ID/mark/canonical identity and final cleanup idempotence with native
adapters. GC reachability/retained-byte effects and meaningful performance require
separate runtime and heap evidence. The Lean model proves none of those Kotlin,
collector, canonical-identity, native-adapter or project speedup properties.
