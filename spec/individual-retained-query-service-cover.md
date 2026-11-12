# Individual retained-query service cover

Status: accepted offline classification. The [publication](../docs/reports/data/redundant-demand-20261110/q-separated-individual-joint-v1/acceptance.json)
contains 8,915 individual verdicts. A separate joint plan selects 6,955.
No production retirement is installed.

## 1. Selected change and unchanged behavior

The user selected separate individual classifications and joint retirement.
This is a major bookkeeping change. It changes no analyzer transfer rule.

| Part | Earlier record | Selected record |
| --- | --- | --- |
| Individual verdict | REDUNDANT_Q also implied membership in one joint cut. | REDUNDANT_Q means that removing only X from original O is safe. |
| Witness | Classification could be blocked because another classified edge was selected for removal. | An individual proof can use any other original origin. |
| Joint selection | Derived from all REDUNDANT_Q statuses. | Stored and proved separately. It selects a subset of individual REDUNDANT targets. |
| Kept representative | Could remain OPEN only because a plan needed it. | Its individual verdict remains REDUNDANT. The plan keeps it as a provider. |

Keep the original O-minus-only-X sink-loss test for necessity. Do not test
necessity after earlier planned removals. Keep all other original guidance,
NORMAL providers and NormalTarget routes in that control. Both controls must
finish and must differ on the same valid sink after the later barrier.

Keep raw summaries, complete ND premises, protection memberships, source
permissions, C2, C5, fields, marks, aliases, Targets, reports and stopping
rules unchanged. Proof data stays outside runtime equality and hashing.
Production optimization requires a later implementation proposal.

## 2. Original state and legal inputs

For each selected project and later completed forward barrier, let O contain
every original outgoing guidance origin. Include methods and all generated
inner blocks. An origin has its full project, method/context, block, physical
ports and literal raw edge identity. Protected and plain origins stay distinct.

Let `emit(o)` be the complete native next-run projection set of origin o.
Keep every ND member projection and typed control row. A projection row is
not an origin. Several original origins can emit the same row.

The combined three-project domain has 96,575 origins and 90,931 rows. Its
repeated-target subset has 28,631 origins. The 67,944 other origins are
available witnesses. Counts do not define the predicate.

Remove X only after its later barrier: OWASP run-11, Conductor run-7 or
Stirling-PDF run-9. Keep the earlier repetition run unchanged. This rule uses
the pinned FULL analyzer and builtin late-run policy, at run-3 and later.

An instance can inspect only demands, summary edges and submitted initial
facts, with their full identities and history. This predicate needs positive
guidance witnesses, not an absence of submitted facts. A missing capture is
never an empty set. Owner and type strings are opaque keys. AP base and
accessor constructors can select the native operator case; JVM hierarchy,
immutability, CFG properties, rule forms, report state and iteration limits
cannot decide applicability.

Assume arbitrarily many later iterations and new field identities. The
temporary run-11 capture setting supplies no proof premise.

## 3. The two checked services

C2 supplies the complete initial family for an offered packet. It includes
initial identity, layer, FLOW companions, owner/trie support and MAY cursor
information. Its key includes the complete entry owner and typed entry.
The paired output does not select a C2 initial.

C5 checks a complete normalized original premise against the entry image,
then restricts the raw conclusion with that same row's paired output. It
keeps the physical exit, relative field budget and prepared-output support.
The whole original ND premise remains intact when a member admits it.

The executable service checks use these exact normalizations:

- A legal nonzero FULL concrete point entry at the same base/path/full mark
  has one C2 point profile for STAR with any legal field E, or EXACT with
  empty E. Its profile is EXACT with empty E. This is a comparison key only.
  Keep every other coordinate. Supported base constructors are This,
  Argument, Return, LocalVar, Exception and legal ClassStatic anchors.
- Other entries keep their complete literal value. ZERO and Target are
  distinct typed entries. FLOW and group entries do not use full-point
  normalization.
- A C5 DATA output with empty E uses one selector key for MAY and STAR at
  the same base/path/full mark. Keep output kind, physical exit and all other
  coordinates. Other outputs keep their full literal value.

The C5 entry guard passes if the canonical entries are equal. It can also
pass this proved point-to-MAY case: source entry is a FULL concrete point;
the witness has empty-E MAY at the same ordinary base and full mark; its path
is equal or is the parent of the first counted extension. Such an extension
has zero or more CLASS accessors followed by one FIELD or ELEMENT accessor,
with no later accessor. This adapter supports This, Argument, Return and
LocalVar. It does not extend the adapter to Exception or ClassStatic.

In both C5 cases, the complete canonical output, owner, physical exit and
typed control kind must agree. Input canonicalization does not retag a raw
fact, change a layer or merge protected and plain raw edges.

## 4. Executable individual certificate

`Q_ind(X, certificate)` is the following boolean check. All row lookups
decode complete native payloads; equal allocation numbers are insufficient.

```text
checkIndividual(X, certificate):
    require X is one original repeated target at its later barrier
    retained = O minus {X}
    require emit(X) is complete and nonempty
    require certificate covers every row in emit(X)

    for row x in emit(X):
        z = certificate.C2Witness(x)
        y = certificate.C5Witness(x)
        require z.origin in retained and z.row in emit(z.origin)
        require y.origin in retained and y.row in emit(y.origin)
        require fullOwner(z.row) == fullOwner(x)
        require C2Profile(z.row) == C2Profile(x)
        require fullOwnerAndExit(y.row) == fullOwnerAndExit(x)
        require canonicalOutput(y.row) == canonicalOutput(x)
        require canonicalEntry(y.row) == canonicalEntry(x)
             or provedPointToMayImageContains(y.row.entry, x.entry)
    return true
```

Z and Y can be different rows and origins. Different source projections can
use different witnesses. Every witness is an actual original membership and
differs from X. A witness can have its own individual REDUNDANT verdict:
that other origin remains present in the singleton control for X.

This is the existing RetainedQueryServiceBasis checker instantiated with
`K = O minus {X}` and the single removal list `[X]`. It is an executable
certificate predicate, not "remove X when it is harmless."

## 5. Separate joint check

Choose a subset R of individually REDUNDANT repeated targets. Use one
retained set `K = O minus R`. Check the same complete certificates for every
X in R, with every guidance witness in that same final K. Recheck the entire
plan when its witnesses change. Keep all outside-target origins retained.

Do not combine the singleton certificates as if they used this common K.
For example, if `emit(A) = emit(B) = {q}`, removing only A is safe and
removing only B is safe. Using each as the other's sole witness for a joint
deletion fails: neither remains to supply q.

The accepted joint plan selects 6,955 origins and keeps 89,620 original
origins. It keeps 1,960 individually REDUNDANT targets. It is not a maximum
joint-cut claim, and a kept target is not thereby necessary.

## 6. Proof and native correspondence

The existing constructive RQS theorem derives complete C2/C5 oracle equality
from the boolean guards and actual retained memberships. It preserves the
complete answer/support profiles for every later run and field limit. Equal
oracles then preserve every natural continuation length, with all unchanged
analysis state as arbitrary shared parameters.

The [individual binding](../docs/reports/data/redundant-demand-20261110/cases/retained-service-individual-lean-v1/receipt.json)
instantiates that theorem separately for all 8,915 X. It checks 20,256 witness
memberships, complete source emissions and exact singleton retention. Its
286 axiom audits pass. The [independent review](../docs/reports/data/redundant-demand-20261110/cases/retained-service-individual-formal-independent-v1/receipt.json)
checks the compiled data and consequences.

The [joint binding](../docs/reports/data/redundant-demand-20261110/cases/retained-service-joint-6955-lean-v1/receipt.json)
checks all 6,955 removals under one retained predicate. Its 222 new audits
and [independent compiled review](../docs/reports/data/redundant-demand-20261110/cases/retained-service-joint-6955-independent-v1/receipt.json)
pass. All witnesses are outside the entire cut. Both bindings permit only
`propext` and `Quot.sound`. Unknown rest rows and emissions remain arbitrary.
The actual counted classifier need agree only on stored field words; future
field identities remain unbounded.

The existing parameterized native RQS and CountedExtension tests supply the
operator correspondence. Changing the retained predicate adds no native
transfer case. The [publication review](../docs/reports/data/redundant-demand-20261110/cases/individual-joint-publication-independent-v1/receipt.json)
checks all original payloads, histories, both certificate contexts and the
separate stored plan. Missing inputs, one lost intermediate reply, equal
counts or a NORMAL record beside X cannot replace these gates.

The original valid-sink necessity gate is unchanged. A target that fails this
predicate stays OPEN until another proved predicate or a faithful native
sink-loss case classifies it. Latest original reached / completed / accepted
forward remain OWASP 11/11/11, Conductor 8/7/7 and Stirling-PDF 11/10/9.
