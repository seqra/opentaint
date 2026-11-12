# Retained demand service basis

**Status: proved offline classification predicate.** The complete observed
proof for all 6,949 removals and the independent final review pass. The
[campaign acceptance](../docs/reports/data/redundant-demand-20261110/q-retained-service-basis-v1/acceptance.json)
adds 1,311 verdicts and replaces 2,219 earlier certificates. No production
retirement is installed. A runtime change needs a separate proposal.

## 1. Scope and selected change

This is an offline demand classification rule for the pinned FULL analyzer.
It applies after a completed forward run of at least run-5. The earlier run
is evidence of repetition. Remove guidance only after the later barrier.
The campaign barriers are OWASP run-11, Conductor run-7 and Stirling-PDF
run-9.

The rule can inspect only demand edges, summary edges and submitted initial
facts, with their complete identities and history. It cannot use project
source, CFG properties, JVM type analysis, rule forms, report state or an
iteration limit as an applicability guard. General analyzer implementation
is used to prove the operator laws. Literal accessor kinds and AP base
constructors are edge coordinates, not additional type analysis.

Assume any number of later iterations. The proof must apply to each later
run and field limit. No temporary hard limit, completed finding set or
finite capture can justify a removal.

The change is in the proof and classifier decomposition:

| Earlier whole-row check | New service check |
| --- | --- |
| One retained row must cover the complete query. | One retained row Z preserves C2. A possibly different retained row Y preserves C5. |
| A witness of an old proof can block a new removal. | Recheck old and new removals against the final retained origins. Replace each failed old witness. |
| Separate predicates encode the same query cases. | One pair of local checks and one complete-origin checker supply a common contract. |

There is no new transfer or initial-emission rule. Keep raw current summaries,
complete ND premises, saved NORMAL records, source permissions, seeds,
NormalTargets, reports and both literal protection memberships. No field,
mark, alias, source, sink, loop-gate or stopping rule changes. Proof metadata
stays outside runtime equality and hashing. Classification alone changes no
production analyzer behavior. A production filter needs a later implementation
proposal and selection.

## 2. Origins, rows and complete identities

An **origin** is one original outgoing edge at the selected barrier. Its
identity includes the project, complete method/context key, block identity,
physical ports and literal edge membership. Protected and plain memberships
remain distinct. Removing an origin here means removing its outgoing
guidance contribution. It does not delete its raw summary or saved NORMAL
membership.

`emit(origin)` is its complete native next-run projection set. It includes
all ND member projections, typed control rows and physical ports. The
checker must obtain this set from the original capture. A sample, one ND
member or one selected port is insufficient.

A **row** contains:

- The complete C2 owner: project, method/context, block and physical entry
  identity, where that port is present.
- The typed entry: DATA, ZERO or Target. A DATA entry has a base, full
  accessor word, tail, full mark identity and field exclusions.
- The physical exit and typed output: DATA or ZERO, with the complete
  selector payload.

The native tails are EXACT (`$`), STAR (`*`), MAY (`[any]`) and MUST
(`[any-taint]`). The word "point" below names a comparison key. It is not a
new fact tail.

A full mark identity includes its name, group and kind. FLOW mark exclusions
remain literal where they occur in the native row. A field key includes its
complete accessor identity. Integers or hashes can index these values only
if the binding checks the full decoded values and detects collisions.

An origin and a row are different objects. Several retained or removed
origins can emit the same row. A witness must name an actual retained origin
and prove that the row belongs to its complete projection set. A row code
alone is not a retained provider.

## 3. The two demand services

**C2 is the entry service.** It gives the complete family of emitted initials
for a submitted packet. This includes each initial's layer, the FLOW
companions, owner/trie support and the MAY precision-cursor profile. C2
unions rows at the same entry. The paired exit does not select a C2 initial.

**C5 is the paired output service.** It first tests the complete normalized
original premise against the row's entry image. If admitted, it restricts
the raw result against that same row's output and applies the relative
field cut. It also supplies conditional prepared-output/base support.
Keep the complete original when one ND member passes the entry check. Do
not form a synthetic premise from members of different rows.

The two services are not interchangeable. An initial admitted by another
row does not by itself authorize X's output. Conversely, an output selector
that accepts X's stored premise need not emit X's complete C2 family.

A service answer includes the full packet result and its semantic support
profile. Support profiles are observations, not extra data publications.
Diagnostic row counts and allocation IDs are not service answers. The scope
excludes a custom policy that makes semantic choices from those counts.

## 4. Canonical service keys

Apply only the two proved comparison normalizations below. Do not change
the real row, submitted fact, stored premise or raw result.

### Concrete point entry key

At run-3 and later in FULL mode, these legal DATA entries share one point
key:

```text
x.p.*/T, with any legal field exclusion
x.p.$/T, with empty field exclusion
```

T must be the same full concrete mark. The base and complete path must be
equal. FLOW and group marks do not use this normalization. The supported
nonzero executable bases are This, Return, Argument, LocalVar, Exception
and legal ClassStatic anchors. Literal-backed values and internal cleaner
bases are outside the adapter. Keep the native static grammar checks.

Both entries emit the same exact concrete initial with the same
actual-derived layer. They emit no STAR primary or FLOW companion. They
have no MAY precision cursor. Their C5 image is exactly the same-path
concrete EXACT initial, with empty field exclusions and the required budget.

For every other entry, the comparison key is its full literal typed value.
In particular, a MAY entry remains MAY. ZERO and Target remain separate.

### Output selector key

For a DATA output with empty field exclusions, the existing selector law
permits MAY and STAR to use one comparison key. Keep the same output base,
complete path and full mark. Keep the typed output kind and physical port.
The path has the same counted length, so the relative budget is equal.
This law also applies to a DATA output paired with a literal ZERO or Target
entry. ZERO outputs remain literal.

Do not erase a nonempty output exclusion. Do not equate MUST with MAY or
STAR. Current raw result tails, field exclusions, mark exclusions, layers,
protection and packet grouping remain unchanged.

### C2 check

`C2Check(X, Z)` requires the same complete C2 owner and canonical entry key.
It does not compare the physical exit or output selector. This gives equal
complete C2 answers, equal trie/owner support and equal precision profiles.
Literal MAY entries must have the same complete cursor language. A point
entry cannot borrow a MAY cursor.

### C5 check

`C5Check(X, Y)` requires the same complete owner, physical exit, typed output
kind and canonical output selector. It then requires either:

1. Equal canonical entry keys; or
2. The point-to-MAY image containment below.

Only the entry admission test can differ in case 2. The output program
receives the same complete original and raw packet. It therefore returns
the same answer for every original admitted by X. Y can admit other originals;
Y was already present before removal.

## 5. Point-to-MAY C5 containment

Let X have a legal late full-concrete point entry `a.p.point/T`. Let Y have
an empty-exclusion MAY entry with the same base and full mark. Both bases
must be ordinary This, Return, Argument or LocalVar. The new containment
adapter excludes static and Exception bases.

Y's path can be:

- The same path p; or
- A strict prefix of p, where the suffix ends at its first counted accessor.

FIELD and ELEMENT count. CLASS does not count. Thus this is a first-counted
extension, not an arbitrary deeper prefix.

For a late point entry, a passing C5 member is exactly `a.p.$/T` with empty
field exclusions. A MAY entry at p accepts that exact point. A MAY entry at
the permitted prefix also accepts it. The parent's field budget follows
from the child's budget. For an ND original, use the same passing member
and preserve the entire original.

This gives C5 containment only. It requires an independent exact C2-profile
witness Z, even in the same-path case.

```text
X: entry a.f.point/T -> output Q
Z: entry a.f.point/T -> output R       # exact C2 support; R can differ
Y: entry a.[any]/T   -> output Q       # C5 support; f is first counted

Retain Z and Y. For X's C2 queries use Z. For X's C5 queries use Y.
The same rule permits Y entry a.f.[any]/T.
```

For example, submit `a.f.*/T, DEMAND`. X emits `a.f.$/T, DEMAND`. A same-path
MAY row instead emits a concrete STAR primary and its FLOW companion. An
ancestor MAY row can also emit a root exact FLOW companion. Therefore Y
alone does not preserve the exact point start. Z is mandatory.

## 6. Flat complete-origin certificate

Let O be the actual outgoing origin set. Let R be the full proposed removal
set, including all earlier accepted removals. Let F = O minus R be the final
retained origins. A witness must belong to F, not merely survive an earlier
step of a greedy selection.

For every removed origin, require a nonempty complete projection set. For
every row X in that set, save a C2 witness Z and a C5 witness Y. They can be
different rows or origins. Each must be a member of an actual origin in F.
Different projections of one raw origin can use different witnesses.

```python
def check_basis(original_origins, all_removals, certificates, actual_counted):
    retained = original_origins - all_removals
    for origin in all_removals:              # old and new together
        rows = complete_native_emit(origin)
        require rows is not empty
        for X in rows:                      # every ND projection and port
            Z, Z_origin, Y, Y_origin = certificates[origin, X]
            require Z_origin in retained and Y_origin in retained
            require Z in complete_native_emit(Z_origin)
            require Y in complete_native_emit(Y_origin)
            require C2Check(X, Z)
            require C5Check(X, Y, actual_counted)
    return checked_certificate
```

This certificate is flat. Every service ends directly at a final retained
origin. It needs no DAG, ranks or circular dependency argument. A semantic
containment can be transitive, but the saved certificate must still name
its actual final leaf. An earlier removed origin cannot supply that leaf.

Recheck every earlier removal. If a proposed removal retires an old witness,
replace the affected old certificate and save its previous proof. Keep an
unchanged old proof only if its dependencies still survive and its checks
pass against the final set. Accept the union in one cumulative gate. Do not
accept new rows first and repair their invalidated dependencies later.

The nonempty projection requirement is also a stopping guard. A checked
removed origin supplies a retained witness origin. Together with the entry
and output support profiles, this prevents the checked cut from creating
a false empty-demand or empty-owner decision. An empty captured projection
is not evidence of harmlessness.

Selection can use indexed keys and a greedy pass, but selection is not the
proof. The final complete certificate is the proof input. No minimum-basis
or optimal set-cover result is claimed.

## 7. Native service correspondence

The common contract covers all demand consumers in the pinned runtime:

| Consumer | Required invariant |
| --- | --- |
| Method/block C2 | Equal complete initial families, owners and physical entries. Preserve companions, layers and marks. |
| Trie and precision lookup | Equal base/path/mark profiles and complete MAY witness language. The current certified-budget shortcut returns no budget. |
| Direct and prepared C5 | Same paired selector and port, with entry-image containment. Preserve accepted output-base tickets even when a result is empty. |
| ND and controls | Keep the whole original. DATA, ZERO and Target kinds stay typed. Never combine independent entry/output permissions. |
| Loop observations and trial cuts | Preserve adjacent, repeat and enclosing C2/C5 services at their exact labelled ports, including each tested budget. |
| Prepared work thresholds | Overflow falls back to complete C5; no partial result escapes. Counts do not change semantic policy. |
| Saved replay and other state | NORMAL and NormalTarget views, source permissions, seeds and reports stay common. No lookup omission proves these channels absent. |

Packet order can differ where native semantics deduplicate a result union.
The proof preserves complete packet values and semantic membership, not
allocator order. It does not discard a layer or protection bit as a cosmetic
difference. Both protection memberships remain separate in the original
binding, and output transport uses the same raw packet and output program.

Static completion and shared static carry are absent in the supported late
incoming stores by the runtime validation rule. This is a general engine
invariant, not a project-specific absence guard.

## 8. Constructive proof and field extension

The proof has four steps:

1. Equal C2 keys give equal complete replies and support profiles.
2. A passing C5 check maps every X reply to Y with the same output program,
   complete original and raw packet. The point-to-MAY lemma supplies its
   only new image containment.
3. Each removed reply maps to Z or Y in an actual final retained origin.
   Retained replies already occur before removal. The complete oracle
   unions are therefore equal in both directions.
4. Equal demand oracles and common other state give the same semantic
   continuation. The run/limit-indexed wrapper permits arbitrary later runs,
   limits and shared programs. Induction holds for every finite continuation
   length, with no bound on that length.

`RetainedServiceBasis.lean` proves the Boolean checker soundness, split-row
cover, complete-origin cover, full oracle equality and old-plus-new
recertification. `UniversalRetainedServiceBasis.lean` proves equality of the
whole later-run/limit oracle family and the unbounded continuation result.
The checker does not receive an assumed future-equivalence Boolean.

A finite codebook cannot define future accessor kinds by a false default.
The actual `counted` function is a total function on all accessor IDs. Its
values outside the stored certificate words remain arbitrary. The finite
checker needs agreement only on the successfully decoded stored entry words
that its local guard inspects.

`CountedExtension.actual_checks_pass` transports the finite checks to that
actual function under this agreement. The universal query and continuation
proofs then use the actual function. No bound is imposed on future submitted
facts, raw results, field declarations or iteration count. The finite lookup
must be total as a lookup function, with checked `none` fallbacks. Missing
rows stay arbitrary common behavior; they do not mean globally absent state.

The stored-word bound covers entry words only. It need not cover output
words. A C5 witness keeps the complete canonical output selector equal,
including its path, mark, exclusions and port. Its output budget is therefore
equal under the same actual accessor classifier, even for output fields
outside the entry dictionary.

The observed proof must decode the complete closed lookup trees, not only
descriptive arrays. Check each partition, bound, leaf, fallback, origin's
complete emission set and retained flag. Opaque row and mark codes must map
injectively to the full native coordinates.

## 9. Earlier laws and rejection controls

This contract contains the earlier laws as service cases:

| Earlier law | Case in this contract |
| --- | --- |
| UnchangedProjectionCover | Literal equal C2 and C5 keys. |
| EquivalentDemandOutputSelectors | Equal C2 key and canonical empty-E MAY/STAR output. |
| SymmetricDemandOutputSelectorCover | The same canonical selector service in either orientation. |
| RetainedDemandQueryBasis | Equal query services with actual final retained-origin leaves. |
| EquivalentPointAndControlDemandQueries | Canonical concrete point entry and typed control-output cases. |
| AncestorMayConcretePointQueryCover | Exact C2-profile witness plus first-counted-child MAY C5 witness. The new adapter also permits same-path MAY. |

This is wider than an OR of those complete predicates. X's projections can
use different witnesses, and its C2 and C5 services can have different
providers. The proof does not widen any native emission rule.

These controls state the limits:

| Rejected change | Counterexample or failed check |
| --- | --- |
| Use only Y for point-to-MAY | A submitted concrete STAR DEMAND needs X's exact point start; MAY can emit STAR and companions instead. |
| Use only Z | Z can preserve the initial but have a different paired output. Removing Y loses C5. |
| Permit two counted suffix fields | `a.[any]/T` does not admit stored `a.f.g.$/T` when f and g are FIELDs. |
| Use a false default for fresh fields | With known FIELD f and fresh FIELD h, the partial model admits h.f as one extension; actual native C5 rejects it. Fixed f checks still agree. |
| Treat FLOW as a concrete point | FLOW STAR and EXACT have different C2 images. The concrete point theorem does not apply. |
| Include run-2 | A requested STAR can have the special run-2 descendant image. The late point proof excludes it. |
| Erase nonempty output exclusions | A STAR output excluding g rejects a g descendant which an empty-E MAY selector can admit. |
| Change a port, mark or control kind | The paired service, admission or control route can change. Full keys must match. |
| Keep a retired witness or cover one ND member only | The final membership or complete-projection check fails. |
| Retire every duplicate by a cycle | No witness belongs to the final retained set. |
| Use an empty emission set | The explicit nonempty-origin check fails; stopping support is not established. |

Failure of this predicate is not a necessity result. Necessity requires a
faithful native code case: after the later barrier, remove only X and make
the same valid sink unreachable while all other routes stay available.
A lost query, initial, source permission or one witness is not sufficient.

## 10. Evidence and acceptance

The following pinned component receipts support this contract. Paths are
relative to `docs/reports/data/redundant-demand-20261110/cases/`.

| Package | Receipt SHA-256 | Checked scope |
| --- | --- | --- |
| [retained-service-basis-kernel-v1](../docs/reports/data/redundant-demand-20261110/cases/retained-service-basis-kernel-v1/receipt.json) | `462dede557bae6b407e443b13601d1340f326f63166d82f36d1d29be31d0d7f1` | 28 flat-kernel and 2 varying-run audits; imported 17-law point proof. |
| [retained-service-basis-counted-extension-v1](../docs/reports/data/redundant-demand-20261110/cases/retained-service-basis-counted-extension-v1/receipt.json) | `ccc9fdeee867f5c482caaac598bef0e695ba09cf631a40cd89f21fa27b8d9d4c` | 15 finite-to-actual count-binding audits. |
| [retained-service-basis-native-v1](../docs/reports/data/redundant-demand-20261110/cases/retained-service-basis-native-v1/receipt.json) | `c8093cda966e140ec70d47aa94121be7de92f1136c06fb879b63297f21694e53` | 11 passed native core tests, full literal service roots, direct/prepared C5, ND, controls, precision and loop queries. |
| [retained-service-fresh-accessor-v1](../docs/reports/data/redundant-demand-20261110/cases/retained-service-fresh-accessor-v1/receipt.json) | `e9ffc121166ae01f8cadd7dae3a06a7fc45bac682325db577c8bc5f8594b0dc2` | One native test and eight local counter/transport audits. |
| [composed-query-service-candidate-v1](../docs/reports/data/redundant-demand-20261110/cases/composed-query-service-candidate-v1/receipt.json) | `72beda5cc0cdcc47f62a6ac0fe58c6803ecd5708217170b66bd187073beeb654` | Complete candidate data, native projection memberships and cumulative dependency checks; not an acceptance. |
| [retained-service-basis-observed-review-v2](../docs/reports/data/redundant-demand-20261110/cases/retained-service-basis-observed-review-v2/receipt.json) | `aae3400283558fbc98e0ea1dfd84d75a2584fbc8078318bebde1b735ff5011ac` | Independent full data/source compatibility for the first proof-tool-only variant. |
| [retained-service-basis-observed-review-v3](../docs/reports/data/redundant-demand-20261110/cases/retained-service-basis-observed-review-v3/receipt.json) | `5f75838c74062e68cca2eaca2654772552606e4140d5b02752295cee690c6143` | Exact unchanged data and real checked-group aggregation; full original decoder rerun. |
| [complete observed build](../docs/reports/data/redundant-demand-20261110/cases/retained-service-basis-observed-v2/receipt.json) | `8edc0216cf1744f586b1d9dc7f484dc8d10f70040d8654e17fc0fdb97d9483bd` | All six actual v3 modules pass; 73 constructive audits, including every removed origin and actual-field consequences. |
| [independent final review](../docs/reports/data/redundant-demand-20261110/cases/retained-service-basis-final-review-v1/receipt.json) | `d3ebefe3c2ac62c99050984575e19829c5d70a7aa27404ce7d2b99bcd13aec4d` | Complete formal/native/data correspondence, unbounded future fields/runs/limits, and reviewed cumulative acceptor. |

The accepted extension starts with 5,638 earlier removals. It adds 1,311
new removals: 1,276 Conductor and 35 Stirling-PDF. It explicitly replaces
2,219 prior certificates; 3,419 prior proof records stay unchanged. All
5,638 old proof rows remain archived. The checked union is 6,949.
All new verdicts are concrete-mark AP origins; this does
not classify the selected Conductor FLOW target `0c5f46ce...`.

The finite binding covers 4,620 distinct removed projection rows, 9,240 C2/C5
service witnesses and 6,372 full rows used by the proof. The full observed
build passes at 18223/0. The independent final check passes at 4179/0 and
85771/0. Root dry run 4296/0 and publication 27645/0 pass all gates, including
the unsafe-without-rebinding negative control. The acceptance SHA is
`153734bb8e8341f5d1ede445017a60382f338b7631d15512c83b02aff40121c7`.

The cumulative cut has 11,941 dependency memberships over 2,891 distinct
retained keys. There are 2,401 retained keys inside the repeated-edge
universe. No original raw edge or unaffected proof row is changed. The
current campaign has 6,949 redundant and 21,682 OPEN targets; it is not
complete.

Historical reached/completed/accepted forward runs remain OWASP 11/11/11,
Conductor 8/7/7 and Stirling-PDF 11/10/9. Component tests add no project
iteration. These are finite evidence boundaries, not proof horizons.

No speedup is claimed. Many raw origins can already share a demand-store
row. A later implementation must measure query and propagation work before
it can relate removed-origin counts to runtime or memory savings.
