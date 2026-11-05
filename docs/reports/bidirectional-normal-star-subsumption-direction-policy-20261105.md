# NORMAL STAR relation subsumption and direction-limited inside matching

5 November 2026. Investigation only. Analyzer implementation unchanged.
Runtime: `52f32dd437d438aec4a700a02c18d94c31d58093`.

Latest original campaign reached / completed / accepted:

- Stirling-PDF: **run-9 / run-8 / run-7**.
- Conductor: **run-6 / run-5 / run-5**.

No new project performance run was made. The new controls use bounded
finite programs and the existing native engine. Their accepted endpoint
is **run-7**. Separate AP controls have no driver iteration endpoint.

## 1. Conclusions

The aligned NORMAL relation rule is correct in its stated scope:

```text
S: p.u.*   -> q.v.*
L: p.u.r.* -> q.v.r.*

S covers L.
```

The residual r must be identical on both endpoints. The owner, context,
direction, physical ports, layers and mark/exclusion conditions must be
compatible. The constructive model proves concrete inclusion for arbitrary
finite field paths and full mark values. No finding-loss counterexample was
found for the plain empty-exclusion FLOW case.

The earlier extra ANY/DEMAND output is not a counterexample to this relation
law. It is an approximation introduced by native ancestor application. The
implementation must not preserve a redundant NORMAL relation solely because
that relation generates an extra approximation.

Restricting strict-ancestor STAR matching to opposite-direction records is
a separate candidate. All eight complete finite-driver controls preserve
their findings. This is not a universal correctness proof. The policy also
does not prevent exponential fixed-depth width: an allowed opposite-direction
record can produce the MAY seed, after which ordinary equal-length rewrites
still visit `2^L` paths.

## 2. Why S covers L

STAR is a shared suffix variable. With empty field and mark exclusions:

```text
S contains every pair:
    p.u.sigma / T -> q.v.sigma / T

L contains every pair:
    p.u.r.tau / T -> q.v.r.tau / T
```

For each L pair, choose `sigma = r ++ tau`. It is then exactly an S pair.
This is a constructive witness, not a comparison of unrelated output facts.

Consequences proved in Lean:

- L is a subrelation of S.
- The union of S and L denotes exactly S.
- A family of aligned specializations adds no concrete pair to S.
- Reversing this pure geometry preserves inclusion.
- Exact descendant application gives the same result for both relations.
- Stored growth classification is identical, forward and backward:

```text
FL(v) > FL(u)  iff  FL(v ++ r) > FL(u ++ r)
```

Thus the earlier MUST short/long growth split is not a counterexample to
this rule. That example keeps one premise fixed and changes only its output.
Here both endpoints gain exactly the same residual.

The [portable proof and audit](data/bidirectional-normal-star-relation-cover-audit-20261105.json)
contain the Lean source, checker, kernel receipt, source snapshots and reused
native controls. Seventeen laws pass; the declaration audit covers 43
definitions and theorems. No Classical choice, `sorry`, axiom declaration or
native evaluation is used. The proof scope is pure relation geometry, not
the full analyzer transition.

### 2.1 Conditions outside the plain example

These are not counterexamples to the rule as stated, but matter when the
implementation compares real rows:

```text
Unaligned:
    p.*   -> q.*
    p.f.* -> q.*       // Removes f. Not covered by identity.

Different effect:
    p.* -> q.*
    p.* -> q.f.*       // Adds f. Not covered by identity.
```

A covering relation must also admit the longer relation's prefix and marks.
Equal nonempty exclusions alone are insufficient. For example, if both rows
have field exclusion `{f}`, `p.* -> q.*` rejects `p.f.g`, while
`p.f.* -> q.f.*` can accept it when g differs from f. Their exclusions act
after different known prefixes. Start with empty E. Add nonempty E only
with an explicit prefix-admission law. Likewise, S cannot cover a T flow if
its output excludes T and L permits T.

Do not compare different method contexts or physical exits. Do not use an
unrestricted candidate S that C5 rejected; S must actually remain available.
Concrete protected relations and ND premises are outside this plain FLOW
proof.

## 3. What the native ancestor example really shows

Current native application gives:

```text
actual: p.*/FLOW, NORMAL

S = p.*   -> q.*   gives q.*/FLOW,       NORMAL
L = p.f.* -> q.f.* gives q.f.[any]/FLOW, DEMAND
```

The second result loses input/output suffix correlation. It can represent
extra pairs that the exact L relation did not have. Their presence in that
approximation is not evidence of an L flow missing from S.

The correct design target is therefore relation subsumption. Do not try to
justify it by claiming that isolated NORMAL `q.*` fact-subsumes every
`q.f.[any]` fact under the old scalar law. It does not have that scalar law.
Instead, retain S and remove the covered L producer, with a proof that the
extra approximation is unnecessary for concrete discovery.

Current C2, exact loop observations and handoff can distinguish those two
native results. Their literal initial sets and demand counts can change when
L is removed. That is an implementation congruence obligation, not a semantic
counterexample. A valid counterexample must exhibit an uncovered concrete
pair or a lost real finding while the covering S remains available under
the agreed guards.

One correction to the previous audit is important: saved records are
replayed **before** current C2 admission, in both physical calls and local
block links. Removing L's demand does not itself prevent S from being
queried on an already offered input. Upstream delivery still needs a
complete proof, but the local replay-before-C2 path cannot be used as the
claimed failure.

### 3.1 A practical relation index

A candidate grouping can retain the common suffix as a guard:

```text
p.a.*     -> q.b.*      core=(a,b), residual=[]
p.a.f.*   -> q.b.f.*    core=(a,b), residual=[f]
p.a.f.g.* -> q.b.f.g.*  core=(a,b), residual=[f,g]
```

Within one compatible interface/header group, use a prefix trie over these
residuals. An actually retained shorter residual covers its extensions.
The core is obtained by removing the longest common field suffix from the
two known prefixes.

Do not replace an isolated longer row with its core. If only the `[f]` row
exists, inventing the empty-residual row would generalize the relation and
is unsound. This is an indexing idea, not an implemented canonicalizer.
The grouping algorithm and native adapter still need their proofs.

If L was published before S, it can already have produced downstream
approximations. Removing it from a NORMAL basis need not retract those
effects during the current run. A first implementation can prevent future
replay of L once S is retained and canonicalize the saved basis at the
barrier. Immediate removal of all derived demand is a larger change; do
not introduce a dependency/retraction mechanism silently.

## 4. Define direction-limited inside precisely

Use the stored record's producer direction:

```text
Current publication:    produced in the current run's direction.
Saved direct record:   record.direction == currentRun.direction.
Saved opposite view:   record.direction != currentRun.direction.
```

A backward run's current publication is still a current publication. It
is not an opposite view merely because its instructions were reversed.
Do not overload `record=true`: that flag currently enables other saved
matching behavior too.

The proposed policy should target only a **strict ancestor contribution**:
the incoming STAR leaf is above a deeper summary premise. Preserve
same-path matching, matches where the actual is below the premise, MAY,
MUST, and all ordinary instruction/field-read transfers.

```kotlin
allowStrictAncestor(actualLeaf, origin, scope) {
    if (actualLeaf.tail != STAR) return true
    if (scope == FLOW_ONLY && actualLeaf.kind != FLOW) return true
    return origin == OPPOSITE_RECORD
}
```

The external policy controls change restricted runs only. Run-1 matching
stays unchanged in those tests. This is a limit of the experiment, not an
implicit decision about every run-1 static or special-model path.

There are two meaningful scopes:

- FLOW-only: restrict incoming STAR/FLOW; keep concrete STAR request/refinement
  lanes unchanged.
- All incoming STAR: also restrict concrete STAR/DEMAND. This has a larger
  C2/application proof surface.

Changing only STAR *premises* is a different policy. A concrete STAR actual
can match a deeper EXACT premise, as in the earlier necessary example.
The controls test all interpretations separately. The user scope question
remains open; no interpretation is silently implemented.

The [source audit](data/bidirectional-star-inside-direction-source-audit-20261105.json)
lists physical calls, local blocks, saved replay, observer queries, ND,
Targets and static paths. It includes 17 source pins and the strict-spine
versus same-path distinction. Predefined transfers and reversed instruction
forms keep their ordinary micro-edge semantics.

## 5. Complete-driver controls

The tested program has an early precise input and a later coarse input to
the same helper. Its rules assign T at the exact source paths shown:

```java
void main() {
    Box early = sourceFG();       // T at ret.f.g.$
    Box late = sourceABCFG();     // T at ret.a.b.c.f.g.$
    sinkEarly(helper(early));
    sinkLate(wrapper(late));
}

Object wrapper(Box w) { return helper(w.a.b.c); }
Object helper(Box p) { return p.f.g; }
```

A second variant returns `transform(p.f.g)`, with the rule
`CM(arg0.$,T) -> assign U to ret.$`; its sinks check U. The marks differ,
so an ordinary T alias cannot manufacture the result.

Both programs run the real finite driver in FULL with one worker. The
configured limits are `1,1,2,3,4,5,6,7,8`; all executions stop after the
run-7 prefix, at limit six. No summary is injected into these driver programs.

| Matching policy | Getter program | Mark-changing program |
| --- | --- | --- |
| Current | Both findings; run-7 complete/accepted | Both findings; run-7 complete/accepted |
| Restrict incoming STAR ancestors to opposite views | Same | Same |
| Restrict incoming STAR/FLOW ancestors only | Same | Same |
| Restrict STAR-premise ancestors only | Same | Same |

These are eight successful complete-driver executions. They are bounded
controls, not a project performance comparison or universal correctness proof.

### 5.1 Why this attempt does not refute the policy

The early input creates a same-direction NORMAL forward reader in run-3.
It was tempting to assume that run-5 would depend on that reader's ancestor
match. The actual trace also has a coarse run-3 helper demand:

```text
run-3 precise helper relation:
    p.f.g.*/FLOW -> ret.*/FLOW, NORMAL

run-3 coarse helper relation:
    p.f.[any]/FLOW -> ret.[any]/FLOW, DEMAND
```

The latter guides backward run-4, which produces the NORMAL opposite record:

```text
ret.*/FLOW -> p.f.g.*/FLOW, NORMAL, producer=BACKWARD
```

Run-5 can use its forward read view. The proposed policy allows that route.
Thus the existing same-direction row is not evidence that its ancestor
application is necessary in this program. The complete trace rejects that
attempted counterexample.

The [portable controls](data/bidirectional-star-inside-direction-controls-20261105.json)
contain all eight outputs, 36 focused matching cells, external mutant and
role-wrapper source, class-loading receipts and source/bytecode pins.
The mutant gates only strict STAR spine contributions. The loop-free driver
programs cover physical-call replay; they do not certify every local-loop
reverse path. No repository production/test source or build output changed.

### 5.2 What still needs proof

Run-1 nonstatic initial paths are empty, so a proper-ancestor STAR match
against a deeper current nonstatic initial cannot arise there. After run-2,
current FLOW admission also supplies an initial at or above the admitted
actual path. This supports an own-analysis replacement argument for some
current publications.

Saved-direct replay is different: it occurs before C2 and can have no current
callee demand. The record store does not guarantee an opposite-direction
counterpart for every saved NORMAL record. No valid finding-loss example
was found in the tested programs, but absence of an opposite counterpart
cannot be assumed away in the general proof. Run-2's special admission and
scoped loop transfers need explicit coverage too.

The direction policy is therefore a plausible experiment, not a proved
universal replacement. Restricting the covered S/L family is a smaller
claim than disabling every unaligned same-direction STAR ancestor match.

## 6. Why the direction policy does not bound the explosion

The existing fixed-depth width mechanism survives the proposed restriction:

```text
current run: FORWARD
seed record: BACKWARD identity at 0^L.*
read it in reverse: allowed ancestor STAR -> 0^L.[any], DEMAND

repeat records: FORWARD equal-length prefix rewrites
    1^k 0 .* -> 0^k 1 .*   for k=0..L-1
```

After the seed, every actual has MAY tail. Its matching remains permitted.
The native control still visits all `2^L` length-L words for L=1..8, with
zero loop-consumer observations. The seed has a distinct first-entry scope;
the rewrite records have the repeat scope. These are legal AP/loop-gate
mechanism inputs, not summaries inferred from a Java binary-counter program.

This limitation also matters to the measured hypothesis. The 456 covered
MUST reader memberships from forward run-5 are read in reverse during
backward run-6. They are opposite-direction applications and remain allowed
by the new policy. Do not claim that the policy alone removes that observed
reader family or establishes a Thingsboard/Stirling speedup.

The NORMAL S/L law remains necessary independently of direction gating.
If S and L are forward records, their opposite backward views can still
produce the same old extra ANY/DEMAND distinction. A relation antichain can
remove L in both indexes; allowing only opposite ancestor matches cannot
serve as a substitute for that antichain.

## 7. Next design boundary

Treat aligned NORMAL STAR subsumption as the desired relation law. Keep
MUST/MAY canonicalization as its separate work item, including the previously
identified refinement contract. Do not mistake a changed demand count or
literal observer signature for a counterexample to concrete relation cover.

For direction gating, define incoming-tail scope, strict-ancestor matching
and explicit origin at every consumer before implementation. Prove the
replacement for saved-direct and run-2 paths, or retain those cells until
the proof exists. No source permissions, rejected-input history, grounding
labels, field rules or stopping policy are added by this investigation.

The implementation proof must connect relation canonicalization to native
matching, cuts, observer queries, handoff and later concrete reports. The
seventeen-law Lean model proves the mathematical relation part. The native
controls provide CEGAR evidence for the policy candidate. Neither is presented
as the missing whole-driver theorem.

No analyzer modification or project rerun is included. All external compiler
and probe processes have completed. Production/rules files remain identical
to the measured runtime.
