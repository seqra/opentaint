# Unchanged projection cover

10 November 2026. This is a candidate removal predicate for the redundant
demand campaign. Acceptance needs the complete corpus certificates, formal
checks and native checks. It does not install a production optimization.

## 1. Selected scope

Apply the predicate after a completed restricted FULL forward run, at run-5
or later. The campaign barriers are OWASP run-11, Conductor run-7 and
Stirling-PDF run-9. Keep the earlier run and all current execution unchanged.

There is no selected change to analyzer semantics. The candidate omits a
redundant contribution to the next demand store. It preserves the complete
normalized demand set. It does not remove a current summary, change a
protection flag, change an AP tail, or change a rule, source or sink.

| Part | Current | Candidate |
| --- | --- | --- |
| Next-run projection | Every selected outgoing membership offers its projected rows | Omit X only when unchanged rows still offer every projected row of X |
| Current summaries and protected/plain memberships | Keep the final admitted stores | Keep the same stores |
| NORMAL records, reports, seeds and source hits | Existing persistence and handoff | Keep the same state |
| Next-run permissions and empty-demand stop | Use the normalized demand set | Use the same set |

The current handoff already deduplicates projected rows. Thus this predicate
does not, by itself, reduce next-run analysis work. It classifies redundant
outgoing contributions. Do not report a query reduction or a speedup from
this classification.

## 2. Predicate

Let O be the complete final outgoing set at the later barrier. Let U be its
fixed campaign target set: the exact repeated memberships from the selected
earlier/later pair. Keep the full layer, premise, protection flag, method
context, block and ports in each member of O and U.

Let project(X) be the set of normalized paired demand rows that the existing
handoff emits from X. A row contains the complete method context, block,
reversed ports, typed entry/exit endpoints, fields and full marks. Use actual
handoff normalization. Do not use short field names or output geometry alone.

```text
UnchangedProjectionCover(X, O, U):
    require X in O and X in U
    for each row q in project(X):
        find an actual Y in O such that:
            Y is not in U
            q is in project(Y)
        save (q, Y) as a witness
    return true
```

A different Y can cover each q. Every anchor Y is outside U. This campaign
can remove only members of U, so no accepted campaign predicate can remove
an anchor at this barrier. A repeated row cannot anchor another repeated
row, even if that row is still open.

For an ND edge, check every projected premise member. Do not replace AND
with OR in current summary storage. The existing handoff already projects
its members separately; the predicate preserves all those next-run pairs.

## 3. First project case

Conductor's `ParametersUtils.replace(input, documentContext, taskId)` has
these rows after run-7. T is the full mark
`java/security/path-traversal.yaml:path-traversal#spring-path-source;1;$UNTRUSTED;2`.
The method context fixes `arg(0)` to `java.util.HashMap`.

```java
Map<String, Object> replace(Map<String, Object> input,
                            DocumentContext documentContext, String taskId) {
    Map<String, Object> result = new HashMap<>();
    for (Entry<String, Object> e : input.entrySet()) {
        Object newValue;
        Object value = e.getValue();
        if (value instanceof String) {
            newValue = replaceVariables(value.toString(), documentContext, taskId);
        } else if (value instanceof Map) {
            newValue = replace((Map<String, Object>) value, documentContext, taskId);
        } else if (value instanceof List) {
            newValue = replaceList((List<?>) value, taskId, documentContext);
        } else {
            newValue = value;
        }
        result.put(e.getKey(), newValue);
    }
    return result;
}
// Return binding: ret = result.
// X: input.MapKey.*/T -> ret.[any]/T, DEMAND, protected.
//    The same X exists after run-5 and run-7.
// Y: input.MapKey.*/T -> ret.[any-taint]/T, DEMAND, protected.
//    Y exists after run-7 and is not in the run-5/run-7 repeated set.
```

This declaration identifies the original code and the return binding. It is
not a necessity fixture and does not replace the full captured method state.
The [case data](../docs/reports/data/redundant-demand-20261110/cases/unchanged-projection-cover/input.json)
contains the exact original X, Y, context and projection records.

Both rows project to the same backward demand:

```text
entry: ret.[any]/T
exit:  arg(0).MapKey.*/T
```

The existing handoff turns MUST into MAY. It does not carry the old
protection flag in a demand pattern. The candidate does not subsume X with
Y in summary storage. Both current protected rows remain. It omits only X's
duplicate offer of this next-run demand pair.

## 4. Joint-removal proof

Let R be any other accepted removal set with R contained in U. Let Q be any
set of targets with checked witnesses from section 2. Every anchor is in O
and outside U. Therefore every anchor survives removal of R and Q.

For each projected row from a removed X in Q, its saved anchor still offers
the same row. Every row offered by a retained edge was already offered
before removal. Consequently:

```text
project((O - R) - Q) = project(O - R)
```

This statement also holds when R and Q overlap. In particular, Q adds no
guidance loss to the six previously accepted P removals. The argument does
not claim that P itself preserves the whole demand set.

The constructive [Lean model](lean/proposals/redundant-demand-20261110/UnchangedProjectionCover.lean)
defines an executable checker. Its witnesses contain actual anchor IDs.
It proves target membership, anchor retention, equality of every demand
lookup, equality of the successor semantic state, and preservation of
future observations. It also proves equality of finite nondeterministic
traces. The stable state contains the unchanged raw stores, NORMAL records,
reports, seeds and source hits.

The native bridge must establish that full normalized membership defines
the C2/C5 permission set. The proof does not claim equal insertion order,
allocation IDs, timing or diagnostic callback counts. It is not a proof of
the whole Kotlin analyzer.

## 5. Source correspondence

After NORMAL persistence, handoff reads final admitted outgoing rows.
`guidancePattern` applies the existing field/mark normalization. Method and
inner-block projectors offer all pairs to `DemandStore.Builder`, which
deduplicates exact identities. Block projection reverses both ports.
ZERO and Target use typed control rows. NormalTarget is not refinement
demand.

The source/sink seed collections do not come from the outgoing origin being
omitted. They come from their separate actor stores. Keep those stores and
all current report preparation unchanged. Equal projected sets preserve the
final successful-insertion counts and the existing empty-demand stop test.

The [source audit](../docs/reports/data/redundant-demand-20261110/tools/unchanged-projection-cover-source.md)
maps these operations to the implementation. The native probe uses actual
method handoff, block projection, builder, C2 and C5 APIs. Its component
cases do not fabricate a project necessity example.

No complete upstream copy graph is needed for this predicate. The proof
holds for every execution that produced the same final state. All current
effects remain, and every permission from X is still present. In contrast,
a predicate that removes the last contributor to a pair needs a transfer
and observation proof, such as P's complete-origin proof.

## 6. Required rejections

Reject a certificate when:

- Its anchor is another member of U. Removing both could lose the row.
- An ND edge has an uncovered projected member.
- The method context, block, entry port or exit port differs.
- A full field or mark identity differs, even when its display name matches.
- The anchor is absent from the actual later outgoing set.
- It changes current summaries, flags, reports, NORMAL records or seeds.
- It uses a raw summary that the final handoff does not select.

The proof fixtures include circular support, a missing ND arm, a wrong port,
an absent anchor and a target outside U. Shared shape is not a certificate.

## 7. Corpus acceptance gate

For every positive target, retain all projected rows and one actual unchanged
anchor for each row. Check the complete earlier/later intersection and the
full later outgoing set. Recompute the native-corresponding projection for
both X and its anchors, and compare it with the captured projection links.
Check the whole successor frontier after all accepted P and Q removals.

Use a collision-checked, injective finite encoding of complete rows for the
observed Lean certificates. Unrelated outgoing contributions remain
arbitrary in the formal model; do not replace them with an empty set to make
a local check pass.

Accept the predicate only after the generic proof, native probe and all
per-target certificates pass. Then filter the entire remaining campaign
queue before selecting another target. Production implementation needs a
later proposal and selection.
