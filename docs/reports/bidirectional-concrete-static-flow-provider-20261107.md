# Concrete static identities and missing FLOW providers

Date: 7 November 2026. Status: evidence only; no repair selected.

The latest native probe completes **run-3** with zero findings. The original
finding assertion still fails: one test, one failure. This probe uses the
current SOA implementation. It does not run the proposed plain-STAR redesign.

There is no available NORMAL FLOW provider for the concrete static identities
in this example. Also, the new runtime trace shows that saved ZERO summaries
do execute through the first loop and the block after it. The missing finding
is not caused by a simple failure to replay those ZERO summaries.

The [portable data](data/bidirectional-concrete-static-flow-provider-20261107.json)
embeds the complete native trace, its 59 pipeline records, XML, receipts,
diagnostic source, logging setup, and the source snapshots used below. It also
preserves the two unsuccessful logging attempts. The probe changes no
production code, rules, demand, saved records, or source permissions.

## Program and result

The existing test uses physical source, write, read, and sink operations:

```java
// sourceAtG assigns full mark T exactly at the returned object's g field.
while (again1()) {                 // L1
    a = sourceAtG();
    Box.shared = a;
}
while (again2()) {                 // L2, inside the complete AL1 block
    b = get();
    sinkT(b.g);
}
Object get() { return Box.shared; }
```

Use `CF` for `Box.shared`, `F` for FLOW, `$` for EXACT, and `N`/`D` for
NORMAL/DEMAND. In this capture, `CF=[1,4]`, `g=0`, and `T=1`. These IDs are
local labels. The decisive rows have empty field exclusions and no protection.

| Completed run | Direction and field limit | Outgoing demand rows | Target demand | Findings |
| --- | --- | ---: | ---: | ---: |
| run-1 | Forward, 1 | 13 | 4 | 0 |
| run-2 | Backward, 1 | 14 | 2 | 0 |
| run-3 | Forward, 2 | 0 | 0 | 0 |

The end is `COMPLETE / run-3 / FORWARD / NO_DEMAND_EDGE / FULL`. The required
finding remains `two loop static sink`. No finding expectation was weakened.

## Why the concrete identity remains

The joined run-2 L1 state contains these relations, among others:

```text
method/context: two loop static root [context]
block2, entry10 -> exit4: CF.STAR/T -> CF.STAR/T, D
block2, entry4  -> exit4: CF.STAR/T -> CF.STAR/T, D
```

They are precise STAR identities. They do not request a deeper field
refinement. The user rejected adding a companion FLOW admission, and these
identities must remain under the selected concrete-only policy.

A NORMAL `CF.STAR/F -> CF.STAR/F` provider at the same interface could cover
these unprotected T identities. That provider is absent:

1. **Run-1 does not seed static FLOW at the write-only L1.** Static FLOW
   hypotheses start at an activated static-read operation. The read is in
   `get`, reached through L2. L1 has no static read.
2. **The local `a/FLOW` route does not supply a static FLOW writer.** The source
   call's source stage has ZERO and its concrete source edge, with no
   `keep(a)` edge. The stage processes its explicit edges. The joined run-1
   trace has local `a -> a` FLOW identities on other exits, but no `a/FLOW`
   packet at the static write. A local-base identity cannot cover CF's static
   premise.
3. **Run-2 admits concrete T only.** The relevant demand and actual input carry
   T. C2 and the implicit static-carry family retain that mark; neither adds a
   FLOW initial. A concrete demand does not grant an abstract initial.
4. **Other FLOW rows are different relations.** The getter's backward FLOW row
   is `ret.g.STAR/F -> CF.ANY/F, D`. It has a different owner, input base, and
   output geometry. It is not a NORMAL L1 static identity.

Each block-entry/output-port store has its own admitted relation. Subsumption
uses providers in that owner. It does not create a FLOW provider from demand
guidance or import one from an unrelated scope.

There is no available NORMAL `S -> S` default in this native state. The shared
run-2 static-carry adapter is demand guidance, not an executable NORMAL summary.
A universal NORMAL static identity cannot be assumed through strong writes:

```java
void overwrite() { Box.shared = new Node(); }
// An unconditional NORMAL S.* -> S.* would preserve old T on shared.g.
// The strong write must kill that old dependency.
```

Thus this case does not show that subsumption rejected an available FLOW cover.
It shows that no such provider was inferred and admitted.

## Saved ZERO replay executes

The probe reads actual saved records before run-3. It finds NORMAL ZERO
identities at the prefix, L1 entry0/exit10, and AL1 entry10/root-exit. The
pipeline then records their application, not only their presence:

| Pipeline sequence | Captured run-3 operation |
| --- | --- |
| 1–5 | Prefix ZERO offer, identity application, and fresh completion at exit0 |
| 6–10 | L1 entry0 ZERO offer; saved ZERO identity applied and completed at leave exit10 |
| 18–22 | AL1 entry10 ZERO offer; saved ZERO identity applied and completed at root-exit `-2` |
| 35–36 | Root ZERO relation normalized and admitted by C5 at root-exit |

This follows the source order: `offerChild` calls `replaySaved` before current
demand admission. Saved AL1 completion can reach the root exit without running
the current L2 body. The trace does not show a fresh L2/getter traversal.

## The precise static result survives the growth check

Run-3 has the source permission. It produces the NORMAL static result and
publishes it at the first loop's repeat boundary:

```text
block2, entry0 -> exit4: ZERO -> CF.g.$/T, N
```

The captured pipeline is:

```text
43: C5 admits ZERO -> CF.g.$/T, N
44–45: apply that loop summary; grows=true
46: observe the exact result: one AL1 admission, zero repeat admissions
48–49: keep the exact NORMAL result; store a fresh completion
50: offer CF.g.$/T, N to block2 entry4, physical target 1
53–59: the repeated source result is admitted and kept again;
       its equal completion is a duplicate
```

The packet envelope says `ANY_TAINT`, but its only populated leaf is an
**exact** T membership at `[1,4,0]`. It is not a uniform-taint fact.

The precise result is not lost at the growth restriction or global field cut.
It reaches the repeat offer. No current T traversal follows that offer. The
source predicts that the retained `CF.STAR/T` demand rejects the strict
descendant `CF.g.$/T` at run-3. **The actual C2 return list was not logged.**
The observation's zero repeat-admission count supports this account, but is
not a direct capture of the later delivery call's C2 result.

The user says the precise STAR identity must not be refined. This report does
not change that policy or select blanket STAR-to-ANY handoff widening. The
remaining issue is how the required DATA path crosses these boundaries while
the precise identity and concrete-only admission stay intact.

## Evidence limits

The authoritative logging run emits all 59 attempted pipeline records, with
zero oversized records, dropped records, logger errors, or sink errors.
Attempt 1 runs the test but has an SLF4J NOP provider: it captures saved-record
queries and zero pipeline records. Attempt 2 fails test-engine startup and
runs no native program. Neither is used as proof of runtime replay.

The separate deep no-leave case last completes **run-5** in its prior trace
with zero findings. It was not rerun here and has a separate EXACT Target
guidance question. No new design, counterfactual repair, or project performance
campaign is validated by this evidence report.
