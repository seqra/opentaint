# Staged-analysis performance contract

## Problem definition

The ThingsBoard shallow scan reaches the same branch-heavy method through many
receiver and argument-type contexts. Some propagated states, notably zero and
class-static facts, do not depend on those contexts. If a method has \(C\)
contexts and its context-independent transfer costs \(W\), the unoptimized
shallow phase performs \(C * W\) work although all copies compute the same
result. ThingsBoard makes \(C\) large enough for this duplicated work to
dominate the phase.

A run has a performance failure when it exceeds the project time or memory
gate, or when workers can no longer reach cancellation checks. Unsynchronized
accessor interning was also observed to stop making progress.

## Mitigation

Only the shallow phase canonicalizes the method context of facts explicitly
classified as context-independent. Zero and class-static propagation use the
empty context; ordinary argument and receiver facts retain their exact context.
Lambda classes and functional-interface constraints also retain their context
because their concrete type can change call resolution.

The shallow scan has a static 5,000-entry-method admission budget and a
30-second runtime budget. If either bound is exceeded, trace-based refinement
fails open to the established method-level rule selection. The static gate
avoids starting work whose duplicated context-sensitive state can approach the
heap limit before cancellation completes. Prescan state remains available to
later phases because it includes lambda call-resolution facts required for
sound reachability.

The rule-selection pass is separate from IFDS scheduling. It confirms shallow
discoveries, resolves their interprocedural traces, and walks each trace to
collect the exact source, transformation, and sink rules. Trace resolution and
rule search share a small per-discovery processing-time budget. If the shallow
phase, confirmation, trace resolution, or rule search is incomplete, the
trace-based selection is discarded and the precise full scan uses the
prescan's method-level rule selection. An optimization failure therefore
cannot narrow the full scan beyond the established baseline selection.

Accessor interning uses concurrent forward and reverse indexes. Creation of a
new ID is serialized and publishes the reverse mapping before the forward
mapping. Existing lookups remain lock-free and cannot observe a partially
resized open-addressed table.

## Deliberately excluded refinements

This change does not add a context-independent direct-sink index, a
forward-action recorder, premise-independent worklist quotienting, or JVM
resolution caches. Those mechanisms are not required by the staged algorithm
and need independent design and review. In particular, worklist memoization is
postponed as a possible follow-up optimization.

## Verification contract

The focused regression compares one and six concrete call contexts. Ordinary
argument facts must retain the context multiplicity, while class-static
propagation must be shared and preserve the same finding. End-to-end gates for
ThingsBoard and Conductor must complete within their configured limits and
preserve the required SARIF finding multiset.
