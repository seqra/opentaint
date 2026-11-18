# Comparative no-loss audit for demand refinement

Baseline `966a40c3647268cc006e5776591d6b68849379d0`, FULL,
limits `1,1,2,3,…`. Preserve each valid marking-point/full-mark/observer
track available to this analyzer. A surviving report ID is insufficient.
Compare completed analyses without a policy cutoff. A candidate produced
only by an over-approximation is still relevant if its guidance is needed
to obtain a later precise track.

## 1. R17 can lose a track while keeping its report

```java
void main(boolean choose, Node x) {
    Node out;
    if (choose) {
        out = new Node();       // A marks out and its descendants with T.
    } else {
        markB(x.f.f.f.f);       // B marks this exact location with the same T.
        Node a = x.f;
        Node b = a.f;
        out = b.f;
    }
    Node r = out;
    observeT(r);                // One observer checks T at r or below it.
}
```

Both alternatives have a ZERO original. The common consumer receives
`Z→r.MUST/T,N` from A and `Z→r.M/T,D` from B in the same continuation.
The two memberships have empty E and plain H. The NORMAL value is ready
first. Its region contains every location of the DEMAND value.

| Run | Baseline and guarded proposal | Value-only R17 adapter |
| --- | --- | --- |
| run-1, forward, limit 1 | A gives the NORMAL observation. B is cut at `x.f`. The reads give root MAY/D and produce a root DT. | Same. The adapter first tries the new omission on restricted runs. |
| run-2, backward, limit 1 | Observer seed follows the reverse field transfers and reaches B. The next run has its source permission. | Same. |
| run-3, forward, limit 2 | From B, the third read exhausts the known prefix and gives `r.M/T,D`. Its root DT keeps refinement. | Drops the D continuation before the observer. The root presents only A's NORMAL result, with an empty outgoing frontier. Natural stop. |
| run-4, backward, limit 3 | The reverse read chain at `x.f.f.f` still overlaps B at `x.f.f.f.f`. B's permission is restored. | No run. |
| run-5, forward, limit 4 | B gives the precise `r.f.$/T,N` at the observer. Both marking tracks exist. The frontier empties naturally. | No run and no B track. |

The pinned native driver gives one NORMAL report in all three variants.
The adapter intercepts only the eligible coarse delivery at the existing
observer continuation. Native rule handling, source permissions, saved
records and stopping remain in use. The proof checks both cut
representations. With NE, run-3 knows the first two fields and the third
read gives the same MAY/D. None of the other selected rules can supply
B's missing control route in this flat example with only local DATA.

**Fix proposal A.** Keep R17's spatial check as a necessary condition.
Omit the candidate only when the complete continuation also has a
certificate for its control and future admission effects. In particular,
prove that each required source track is already available or still has
a valid retained route. Unknown origin accounting retains the original
DEMAND continuation. Apply this same proof requirement to R16, R19 and
R24 at their respective delivery or handoff stages. Identical points,
a shared report ID and the same ZERO original supply no such certificate.
Use the existing complete marking catalogue or a complete native
continuation adapter. Do not add provenance to AP identity or emit
additional speculative work. A certificate may reuse already committed
service. Unsupported continuations continue normally.

**Proof.** The retained service must derive every needed control token
as well as each concrete point. A data token cannot certify B's
permission. If the certificate is unavailable, the D continuation remains
and the backward seed is generated exactly as before. With a certificate,
substitute each constructive derivation into the original continuation,
preserving scope, original and all AND premises. The simulation in
section 5 then keeps all required tracks. The native control with A served
and B unserved takes the fallback and reaches run-5.

## 2. R28 must keep the native NORMAL guidance classes

The compact text described projection of D rows. Native selection also
exports all admitted ND rows and NORMAL backward singleton ZERO rows.
NORMAL persistence alone does not replace either guide.

```java
Node main(Node p) {              // Mark p and its descendants with T.
    Node x = new Node();
    while (again()) {
        x.f = p;
        if (stop()) break;
    }
    return x.f;                 // Normal-exit observer checks ret.$/T.
}
```

Run-1 gives a loop write service and a root Target. At backward run-2 the
after-loop block publishes `ZERO→x.f.$/T,N`. Its reversed physical block
row gives the forward after-loop consumer a demand for `x.f.$/T`. At
run-3 the saved loop write supplies `x.f.MUST/T,N`. The after-loop block
admits the exact query and reaches the real normal-exit observer. A native
adapter that omits just that one backward ZERO guidance row has no observation and stops
at run-3. The baseline reaches the observation at run-3. An independent
native barrier test confirms that a NORMAL `{p/T,q/T}→ret/U` contributes
both paired member guides and can keep the frontier nonempty.

**Fix proposal B.** Restore the exact native selector before any
compaction or empty-frontier test.

```text
select(summary, direction):
    return summary.layer == DEMAND
        or summary.original is ND
        or (direction == BACKWARD and summary.original == ZERO)
```

Use it for method and scoped block rows. Backward executable ND remains
invalid. Project every selected leaf and complete premise member with
its reversed physical ports. This is the existing selection, including
its exceptions. Keep typed Target projection separately.

**Proof.** The selector is equal to the native truth table by case
analysis on layer, direction and premise. The existing projection then
preserves every selected member/leaf pairing and port. The actual backward
ZERO result still admits the forward exact query in the native loop
control. Keep any remaining selected row unless a complete updated
C2/C5 service proof covers it.

## 3. Additional protocol gaps and fix proposals

| Gap | Fix proposal and proof obligation |
| --- | --- |
| Run-1 static completion uses implicit pairs. A literal explicit-row C5 implementation misses read/write composition, lost-write guidance, static carry and the static Target shortcut. For example, a writer publishes `Z→C.f/T` and a reader publishes `C.f/T→DT`; the root needs the composed `Z→DT` guide. | **C.** Preserve the run-1→2 static completion and shared carry interfaces. Apply updated matching to their virtual paired rows as to explicit ones, with the selected mark label, owner route and anchor. Retain ordinary positive NO_DEMAND_EDGE logic. Test query-wise membership against the complete baseline static view before enabling an NE-aware provider. If that bridge is unproved, keep the baseline protocol for the affected analysis. |
| A reached backward ZERO at an exceptional block interface can require a normal-exit Target guide. Reversing DATA ports alone fails to express this case. | **D.** Keep the native borrowed-normal ZERO control path. For already reached ZERO only, check the normal view in addition to the physical view. Put a borrowed backward `ZERO→DT` back at the genuine normal invocation address. Do not seed an exceptional block or alias its DATA rows to the normal view. Same ports and same typed control operation give exact preservation. |
| R20's raw check is stricter than the baseline's normalized image. A normalized STAR witness does not prove that the actual raw EXACT start is legal, and rejecting the raw candidate removes a native publication unless another service covers it. The baseline also starts EXACT on same-head STAR offers. The selected run-2 relay replaces that command with STAR, and later precise C2 can reject it. The local Lean matrix checks those differences. | **E.** Validate raw C2 and C5 as a pair against the baseline service. Preserve legal support via complete native replay or an adequate current plan for each lost baseline service. Without such a bridge, retain the baseline admission/publication for the affected analysis. Never borrow an exit from another demand pair or promote an unsupported NE root to an exact witness. |
| A suppressed saved MUST residual or a hole-preserving R07/R08 query can remove a guide even if it preserves every current NORMAL value. Examples are `p.f.MUST` against a saved root MUST guard with empty current demand, and `p.f.*{g}` replacing an old hole-free FLOW companion used by another offer. These interface examples expose missing proof, independently of whether an arbitrary cold run reaches them. | **F.** Before suppressing the residual or replacing the family, prove future service for each affected consumer, including other actuals and every real paired row. Use only the conditional records whose masks and binding really apply. Keep the baseline path on a missing witness. Keep R08's single input-depth exception and all output caps. |
| A closed terminal goal does not prove that all effects of its anonymous root DT are redundant. The same root offer can activate another scope, a rule seed or another permissible continuation. Correct field-language extraction alone proves absence only for its own origin/observer pair. | **G.** For root retirement require complete control accounting in addition to the origin proof. Prove that all needed starts, seeds and later tracks using the removed root key have another retained route or are already discharged. A bit from known terminal leaves cannot certify a latent consumer outside the completed view. Without this proof keep the anonymous row. |

C and D preserve existing behavior. In C, the existing static C2/C5 views
participate in candidate enumeration, preflight, Target lookup and the
empty-frontier decision. There is no explicit static closure expansion.
D applies only to the current backward exceptional ZERO compatibility
path. The paired output remains tied to its actual port. For E–G use
positive proof of service or the native route. An enumeration result that
contains no known example is not a certificate of absence.

## 4. Disposition of every rule

A **native invariant** has exact preservation when its specified native
operation is retained. A **guarded rule** has a constructive proof of its
local effect with the listed service obligations. These obligations are
part of activation. A local proof does not enable that rule across an
unproved native boundary.

| Rules | Constructive proof and comparative condition |
| --- | --- |
| R01–R03 | A real cut retains the old point because the removed suffix is nonempty. Reading and writing preserve that interpretation. For native edges, aliases, packed regions and statics, validate transport of both the concrete point and the service that used old MAY. C and E apply. |
| R04–R06 | The split covers empty and nonempty suffixes in the proved scalar fragment. Possible admission stays D and companions are conditional. E applies to each old admission and compiled publication, with R22's suffix-lifting obligation for FLOW. |
| R07/R08 | Same-head E keeps the same geometry and the deeper map keeps the actual head and holes. The exhaustive cap proof preserves the global limit. F is required for effects on other admitted bindings and later guides. |
| R09/R10 | A child preserves the first named field and its own budget. The refinement view retains child service before execution union. Extra work is finite per row. A child cannot replace an omitted past or future consumer without a certificate. |
| R11/R12 | Split a matching suffix at the first field. The ready child's suffix service must cover the primitive or saved transfer including E, actual continuation, all effects and paired output. Keep the coarse branch if a required consumer is unproved. |
| R13 | No true exact point satisfies a deeper keep. Same-head E remains. Before suppressing loss-created output, keep any necessary guidance under the joint continuation proof. |
| R14 | Native invariant. Saved replay uses the original binding before current C2, including on an empty plan. |
| R15 | Definite matching covers each required MUST point. The rejected lane did not supply NORMAL support. F covers its former DEMAND effects and future guides. |
| R16/R17 | Actual point or uniform-region inclusion, with exact matching scope and H. A applies before omission. Point inclusion alone fails the native R17 control. |
| R18 | A retained saved record's whole native image keeps the duplicate NORMAL result, including masks and control effects. Check that skipping publication does not lose a required row or continuation in the final bundle. |
| R19 | Full uncut owned closure and committed whole bound replies prove the selected local service. Preserve complete ND and all effects. A still applies to later guidance and other origins. |
| R20–R22 | Raw membership and same-row intersection have executable witnesses. C5 preserves the points it selects relative to that pair and never upgrades D. Normalization needs a full suffix-preservation proof. C and E cover the native C5/entry bridge. |
| R23 | M contains NE. Merge execution values only when service is covered. Deeper qualified rows remain separately available. |
| R24 | With equal MUST originals and literal H, the NORMAL output covers each NE point. A also requires preservation of next-run guidance before retiring the NE summary. |
| R25/R27 | Induction substitutes witnesses from the final retained basis. Fair closure over unchanged service preserves the least result. Queue order cannot justify a future callback receipt. |
| R26/R35 | Selected EXACT-on-MUST coarsening keeps the original uniform region. It preserves existing points and can add a match. The allowed precision change does not exempt the rule from A/E at later continuations. |
| R28 | Native invariant with B, C and D. Preserve selected DATA, typed Targets, source seeding and physical scope. Any difference after compaction must satisfy the sealed-stop proof. |
| R29/R30 | Native invariants. Compare complete keys including protection. Whole positive derivation preserves every ND arm. Projected member guides do not execute the conjunction by themselves. |
| R31 | The safe suffix cone has no point cleaned by this action. The concrete witness remains unmasked including under FLOW normalization. Keep native effects on the other leaves. |
| R32 | The requested run-2 STAR relay has a legal raw witness and obeys both caps. It repairs the exercised nested overwrite case. E still applies to baseline exact service at an unproved route. |
| R33 | Native invariant. FLOW demand projection clears mx on both endpoints, leaving actual and saved masks intact. Same row and native policy give the old result. |
| R34 | The extra saved lane is D-only and preserves all old successful scalar results. Keep that lane visible to closure and future-admission checks. It supplies the tested prefix-return guide in the reference. |
| R36 | The bounded residual partitions the input into exactly the uncleaned points. At a real cut use NE. A/E ensure late admission and control service when these pieces replace a formerly broad contribution. |
| R37/R38 | Terminal OR lineage and same-origin NORMAL witnesses preserve the served tracks. G accounts for other consumers of the root key. |
| R39/R40 | Product reachability or nested state pairs exclude every common exact word in a proved complete slice. G still applies. Unknown extraction, two nested sides or unsupported effects keep guidance. |

## 5. Joint proof and activation

Check a changed branch against **native obligations**, not just represented
points. A proof key includes the relevant run phase, complete owner and
revision, ports, original, mark, protection, exclusions and effect
identity. The needed service can be a query, exact-publication witness,
typed Target, source permission, alias or rule effect, saved application or
source-specific observation. Map those proof keys to real native events.
They are not new AP storage keys.

```text
for each affected baseline action in a complete supported scope:
    take its complete available inputs, including controls
    build a finite replacement derivation in the final selected bundle
    check each step against an available native transfer
    check all of its inputs and exact context before accepting its result

at a proposed stop:
    require materialized retained witnesses for all serviced obligations
    require no unserved baseline continuation that can still supply a track
```

Use an acyclic order of steps within a replacement recipe. Recursive and
loop derivations may use induction on any finite witness length. They
cannot use an unavailable future permission to justify its own deletion.
Respect the actual stage and run in which each effect can occur. Captured
service can come from a different safe derivation, including a previously
retained precise track. Every recipe must end in the final retained basis,
not a record subsequently retired by another rule.

The constructive checker verifies finite seed and action recipes, including
availability and run order, before selecting the new graph. An invalid
bundle selects the baseline graph and seeds together. The checker derives
each requested token from the given available tokens. Substitute its checked recipes into the old derivation
by induction. This keeps every premise of every AND rule. For a stopped
execution, closure of the sealed result supplies the materialized track.
This proof is independent of the number of runs and does not require equal
intermediate frontiers. The baseline comparison still needs complete native
action and seed extraction and an adapter for the real scheduling and
source/Target effects. Those maps are activation obligations.

Keep the native algorithm for any analysis scope without a jointly
validated proof. A local fallback requires a proof that changed earlier
history and incoming boundaries can be translated to that native scope.
Otherwise select the native algorithm for the connected analysis at the
start. Do not activate the full proposal by default based on scalar
property tests. This is a deployment condition, not an instruction to run
both analyzers or archive unrestricted facts.

The combined validation passes **262 native tests in 40 classes**. These
include the two comparative losses and guarded controls, static completion,
physical-port handling and the earlier regression suite. The late marking
track is confirmed at run-5 and the loop exit track at run-3. The proof
audit checks **26 new constructive claims**, 7,527 cumulative in 452
source-hash-pinned modules. [Constructive checks](lean/proposals/demand-no-loss-audit-20261117/README.md).
