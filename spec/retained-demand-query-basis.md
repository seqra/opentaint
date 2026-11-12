# Retain a basis for duplicate demand queries

Status: checked campaign predicate. Production behavior is unchanged.
The coordinator acceptance and per-edge certificates record classification.

## 1. Scope and selected change

The existing selector law proves equal demand services for equal canonical
query keys. Earlier matchers require every witness outside the entire
repeated-edge universe U. This matcher can retain an OPEN member of U as
a witness. It must keep that witness outside the complete cumulative removal
set. The final retained basis, not a pairwise comparison, is the certificate.

Keep the pinned FULL runtime and built-in iteration policy. Removal occurs
after a completed forward barrier of at least run-5. Retire only outgoing
guidance contributions. Keep raw current summaries, complete ND premises,
NORMAL providers, source permissions, seeds, Targets, reports and literal
protection memberships. No transfer, C2/C5, mark, alias, field limit, source,
sink or stop rule changes. Diagnostic counts can vary.

Let `emit(e)` be all native next-run projection rows of outgoing origin e.
Keep every ND member and physical port. A canonical query key is the full
project, method/context, block and port key plus its full row. For DATA rows
only, replace an empty-exclusion MAY output selector by STAR in this comparison
key. Do not change the real row, a C2 entry, a fact or a control output.
Control rows are equivalent only when their entire native payloads are equal.

## 2. Joint selection

Start with the actual outgoing origins after all prior accepted removals.
Count distinct origins per canonical query, not duplicate occurrences in
one ND origin. Use the user-selected FLOW/plain-T/Target/other priority.

```python
def select_duplicate_queries(outgoing, prior_removals, open_targets):
    remaining = outgoing - prior_removals
    providers = index_origins_by_canonical_query(remaining)
    removed = set()
    for X in ordered_by_priority(open_targets):
        queries = canonical_keys(complete_native_projection(X))
        if queries and all(len(providers[q]) >= 2 for q in queries):
            remaining.remove(X)
            removed.add(X)
            for q in queries:
                providers[q].remove(X)

    certificates = []
    for X in removed:
        witnesses = []
        for row in complete_native_projection(X):
            Y, kept_row = choose_actual_projection(
                remaining, canonical_key(row))
            witnesses.append((row, Y, kept_row))
        certificates.append((X, witnesses))
    return removed, remaining, certificates
```

Select witnesses from the final remaining set. An origin removed later in
the greedy pass cannot witness an earlier removal. Each source row needs
its own actual retained row; witnesses can use different origins. Prefer an
outside-U origin where available, but this preference is not a proof condition.

The kept OPEN origins remain OPEN. A sole final provider is not thereby a
necessary-edge case. Such a case must delete only X after run-(i+2), with
i >= 3, and keep every other demand edge and available NORMAL provider.
A valid sink must become unreachable. Loss of a fact or one witness is not
enough. Other original duplicate edges can still make single-edge deletion
harmless even when X is the sole provider in the chosen final basis.

## 3. Principal cases and rejection controls

```text
X emits {entry C, exit a; entry C, exit b}.
Y emits {entry C, exit a; entry C, exit c}.
Z emits {entry C, exit b; entry C, exit d}.

Retire X's guidance; retain Y and Z.
Both X rows remain available. All a/b/c/d permissions stay equal.
Keep X's original complete ND summary and current-run effects.
```

One retained a row alone cannot replace X. A b row at another physical port
cannot replace it either. Never mix entries and exits from different paired
rows to claim a match.

If X and Y are the only providers of one query, the greedy pass can retire
one and must keep the other. It cannot retire both by claiming circular cover.
An empty-E DATA exit STAR and MAY can share a query class. Different C2 entries
or a nonempty concrete STAR exit exclusion do not qualify under this law.

## 4. Proof and finite verifier

At each removal, every affected query still has another distinct origin.
The decrement uses one count per origin/query pair. Induction over the greedy
pass preserves the complete canonical query set. The final witness search
therefore yields an actual retained witness for every removed projection.

The existing constructive selector law proves equality of all DATA C2,
paired-C5, prepared-output, output-base and owner-support services for each
canonical query. Identical controls give identical control services. The
`Anchored` union theorem replaces every removed reply by a retained reply.
It preserves unrelated emissions as an arbitrary shared function. This
gives the same demand oracle and the same complete semantic transitions,
including loops, source permissions, Targets and report identity. The same
argument preserves later iterations. No exact-count custom policy is covered.

`RetainedQueryBasis.lean` extends that model. Its finite database contains
complete emissions of every removed and witness origin. Row codes are query
class labels only. They are not retained providers. The kernel checks that
each encoded full row has the canonical key named by its code. A certificate
must cover every row of its source, and each witness must be in the retained
portion of the actual origin database. Witness rows must belong to that actual
origin. Equal codes then prove equal complete canonical projections.

The executable checker uses Boolean bounds and equality tests. Constructive
soundness lemmas recover the original row, witness and certificate propositions.
This avoids constructing large numeric-bound proofs during finite evaluation;
it does not weaken a bound or a coverage test. No native-decide axiom, classical
axiom or assumed future-safety flag is permitted.

`ObservedRetainedQueryBasis.lean` binds the complete native encodings to this
verifier. The external independent gate must decode its row declarations,
control-key dictionaries, arrays, complete ND emissions, witness indices and
target range back to the original corpus. Opaque control codes preserve the
entire native payload. They cannot combine two different control rows.
It must also check the executable closed `LookupTree` constants, interpreter
and database bindings. Every leaf must match the descriptive arrays. Branch
partitions must cover every Nat, including each declared unbounded fallback.
Checking only the arrays is insufficient.

## 5. Cumulative dependency rule

The candidate starts after the 373 accepted removals. Those earlier anchors
are outside U, and this matcher removes only OPEN members of U. Their
providers therefore remain unchanged. All new witnesses must survive the
whole prior-plus-proposed removal set.

A later filter must check the entire cumulative removal set. It cannot remove
an inside-U witness on the basis of an already removed origin. Before such
a removal, re-establish every dependent row's surviving witness, or provide
a complete new proof for the affected union. Save the replacement chain and
its retained endpoint. Do not silently invalidate an accepted certificate.
Only REDUNDANT_P and REDUNDANT_Q remove guidance. NECESSARY_WITH_CASE is a
terminal classification but keeps its edge. The v1 frozen ledger has only
OPEN, REDUNDANT_P and REDUNDANT_Q rows; its acceptance gate checks this fact.
The cumulative dependency validator uses explicit redundancy statuses.

## 6. Evidence and limits

The candidate contains 4,419 origins and 5,548 projection witnesses: 714 OWASP,
3,527 Conductor and 178 Stirling-PDF. It includes 278 FLOW, 3,373 concrete and
768 Target origins; 714 origins are ND, including three selected NORMAL ND.
There are 817 method and 3,602 inner-block origins. Every full projection and
final witness is saved. There is no sample or top-N limit.

Original reached/completed/accepted forward runs are OWASP 11/11/11,
Conductor 8/7/7 and Stirling-PDF 11/10/9. Removal barriers are respectively
run-11, run-7 and run-9. Source preparations and component tests add no new
project activity to those captures.

Nine native tests, 37 constructive Lean audits and independent full corpus
and observed-model checks pass. The three closed finite checks are axiom-free.
The complete joint removal preserves canonical query keys, owners, physical
ports and controls. See the [acceptance record](../docs/reports/data/redundant-demand-20261110/q-retained-query-basis-candidate-v1/acceptance.json)
and [independent review](../docs/reports/data/redundant-demand-20261110/q-retained-query-basis-review-v1/final-review.json).
The unique Conductor URI query under current investigation is not covered.

Indexing and greedy selection take work proportional to complete emission
memberships plus witness lookup, with hash keys used only as indexes. Full
values must compare equal. The selection is a valid greedy basis, not a
minimum set-cover claim. Much duplicate guidance is already deduplicated by
the demand builder. Do not claim a proportional CPU or memory improvement
from the number of retired raw origins. No runtime optimization or measured
speedup is installed by this specification.
