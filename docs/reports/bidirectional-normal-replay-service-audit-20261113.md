# NORMAL replay does not by itself cover demand service

13 November 2026. This continues [demand-task.md](../../demand-task.md).
The accepted result remains **4,635 REDUNDANT, zero NECESSARY, 20,754 OPEN**.
The checked joint cut remains 3,490. FLOW priority and target `1025a197…`
are unchanged. No production behavior or proof-input scope changed.

| Project | Latest reached | Latest completed | Latest accepted forward |
| --- | --- | --- | --- |
| OWASP | run-11 | run-11 | run-11 |
| Conductor | run-8 | run-7 | run-7 |
| Stirling-PDF | run-11 | run-10 | run-9 |

These are the original project runs. The new work uses frozen records and
small native operator tests. It makes no project scan.

## Stronger FLOW providers: zero candidates

The earlier NORMAL-envelope probe used precise STAR relations. This audit
also checks for stronger uniform postconditions:

```text
native unary NORMAL I.*/FLOW -> B.[any-taint]/FLOW
```

There are **zero** such providers in all 710,399 persisted NORMAL packets
at the three later handoffs. This count is global, before method, point or
protection filters. It supplies no new FLOW removal certificate.

The checked bindings and raw-packet inventory are in
`cases/normal-backed-concrete-point-inventory-v1/` in the external archive.

## Missing forward ZERO routes: zero candidates

Another candidate would need a known ZERO entry and no normal ZERO exit.
Its absence condition is false for every OPEN FLOW row:

| Project | OPEN FLOW rows | Exact forward NORMAL ZERO route present | Missing |
| --- | ---: | ---: | ---: |
| OWASP | 66 | 66 | 0 |
| Conductor | 9,396 | 9,396 | 0 |
| Stirling-PDF | 538 | 538 | 0 |
| Total | 10,000 | 10,000 | 0 |

The 10,000 rows use 179 physical interfaces. All 9,688 rows with nonstatic
endpoints also have the witness. Native direction is FORWARD; block ports
are swapped back from the next backward query. No same-method or wrong-port
substitute is used. BACKWARD records are not treated as forward witnesses.

This is a presence census, not a proof that missing ZERO implies an
unreachable return. A ZERO GEN or Target shortcut does not prove that a
ZERO initial entered through the ordinary CFG. No such inference is used.

The complete row/route bindings are in
`cases/flow-forward-zero-route-inventory-v1/`.

## Empty instruction lists: zero internal identity candidates

The literal block keys give this count:

```text
10,000 OPEN FLOW rows
    255 rows have block.instructions = []
        244 LOOP rows, across 24 physical interfaces
         11 SEQUENTIAL rows, across 3 physical interfaces
    171 Conductor rows + 84 Stirling-PDF rows; zero OWASP rows
```

All 27 interfaces own nested children with instructions. Their empty
direct instruction list does not make the block empty. In particular,
the three SEQUENTIAL interfaces contain 49, 157 and 262 descendant-owned
instructions. All 11 SEQUENTIAL rows also have next-backward ports
`METHOD_EXIT -> LOOP_NORMAL_EXIT`. No empty leaf interface is identified.

The three sequential interfaces have 158 native NORMAL FLOW memberships.
Only 46 are strict identity leaves, all on bases other than Return. There
are no strict Return-input identity leaves and 73 strict Return-input
nonidentity leaves. For example, one forward NORMAL leaf is:

```text
var(19).[].*/FLOW -> ret.tasksToBeScheduled.[].*/FLOW
```

This is a data transfer in a container that spans a method boundary.
The census does not assign its cause to that boundary. Neither an empty
direct instruction list nor one identity leaf proves complete identity
behavior. The census supplies
no new removal certificate. No CFG-based eligibility guard is used.

The complete coordinate, hierarchy and NORMAL packet bindings are in
`cases/flow-empty-block-coordinate-inventory-v1/`.

## Concrete points are a reference case, not an activated campaign rule

For comparison, the shared service proof was tested on concrete points:

```text
X = (entry I/T, exit B/U), with STAR or EXACT point coordinates
Z = another actual retained row with the same C2 entry service
N = saved unary NORMAL I.$/T -> B.$/U
```

The reference inventory finds 353 OPEN rows with such N witnesses, 24 with
both literal protection memberships. Fourteen of those 24 have an EXACT
exit; ten have STAR. All matching N records preserve the mark. None changes
T to another mark. These are preliminary bindings, not classifications or
a change to the selected FLOW queue.

The native C2 domain is a single exact point after run-2. Its C5 output
domain is broader:

| X exit | Offered current conclusion | Native C5 result | Point N covers it? |
| --- | --- | --- | --- |
| `B.*/U` | `B.f.$/U`, NORMAL | Keeps the NORMAL child at relative budget `FL(B)+1` | No |
| `B.$/U` | `B.[any]/U`, DEMAND | `B.$/U`, DEMAND | Same point geometry |
| `B.$/U` | `B.[any-taint]/U`, NORMAL | `B.$/U`, NORMAL | Same point geometry |
| `B.$/U` | `B.*/U`, DEMAND | Keeps STAR | Broader immediate geometry |

The STAR-exit child is a direct native service hole. The EXACT-exit STAR
case is not by itself an eventual finding-loss proof: late concrete STAR
and EXACT entries have the same point admission service. The source audit
also suggests that some STAR outputs are unreachable from exact-owned
origins. That induction is not a completed retirement proof.

Both normal protection variants are retained separately. The tests never
use a plain edge to subsume a protected one, or the reverse.

## Equal output facts can lose a caller's paired permission

Even an exact leaf match needs a caller adapter. This native example makes
both caller origins legal through C2. T, U and V are distinct FULL marks in
one group. All locations have EXACT tails and empty exclusions.

```text
Callee saved NORMAL providers, one per literal protection flag:
    I/T -> B/U

Callee ND publication:
    {I/T, J/V} -> B/U

Caller demand:
    (OI/T ; OTHER/V)
    (OJ/V ; B/U)

C2 admits OI/T and OJ/V independently.

Saved unary N application:
    I/T -> B/U, with caller original OI

Complete ND application:
    {I/T,J/V} -> B/U, with caller original {OI,OJ}

The complete result Facts are equal: same B/U, layer and protection flag.

Caller C5 under OI:
    OI row has the wrong output base; OJ row has no matching origin.
    Result: empty.

Caller C5 under {OI,OJ}:
    OJ row accepts B/U.
    Result: one B/U output.
```

The four cases cover NORMAL/DEMAND I support and both protection flags.
Both saved N variants coexist and persist. T differs from U, so this is
not an identity-alias suppression example.

This disproves immediate caller service equality from output-fact equality
alone. It does not establish ordinary body reachability, rule/source
permissions, valid sink loss or an unbounded finding difference. A weaker
premise is not automatically a paired-demand witness.

The accepted row-service law does not make that substitution. Its retained
C5 witness receives the **same complete original premise** and raw packet
as the removed row. It uses the same paired output program. The new
counterexample changes the original from `{OI,OJ}` to `OI`, so it is
outside that law. The independent accepted-state audit rechecked all
4,635 classifications, 9,270 individual witness memberships, 6,980 joint
witness memberships and 263 compiled proof artifacts. They still pass.

## Checks and remaining work

The point-domain package checks 448 native cells, 16 singleton cuts and
336 full/cut C2-family comparisons. Its eight small Lean claims are
axiom-free. The corrected caller example checks four native cases and five
axiom-free Lean claims. The pinned runtime is
`14d7b63369d94f49d4c551be8405ed7719f267cc`.

External packages:

```text
normal-backed-concrete-point-inventory-v1/
flow-forward-zero-route-inventory-v1/
flow-empty-block-coordinate-inventory-v1/
concrete-point-c5-domain-v1/singleton-v2/
concrete-point-service-source-audit-v2/
proof-input-obstruction-audit-v1/accepted-state-recheck.json
```

Their checkers and receipts preserve complete bindings and earlier versions.
They accept no redundancy predicate. Future NORMAL compaction, ND original
transport, source permissions, Target routing and eventual refinement still
need the required native adapters before any point rule can be activated.

For FLOW, the stronger-provider, missing-ZERO and empty-block branches
have zero candidates. The remaining
work is still a checked unbounded closure predicate or a faithful
original-row sink-loss example. Generic operator gaps do not classify
the selected OWASP row.

## The proof-input limit

The [constructive decision model](../../spec/lean/proposals/redundant-demand-proof-input-boundary-20261113/README.md)
states the exact remaining obligation. For a complete allowed history h:

```text
P(h) = remove
    implies forall W consistent with h:
        deleting X preserves the required findings of W
```

The existing native counterpair gives equal complete histories through
H5, but only one program loses U after the cut. A sound history-only
predicate must reject that shared history. It cannot infer closure from
finite repetition, saved root copies or a finite set of successful probes.
All eight new Lean axiom audits are empty.

This result does not prove that the actual project corpus is impossible
to classify. The counterpair is not mapped to actual target `1025a197…`.
It also does not authorize instruction-level AP models, CFG guards or
additional JVM data. The proof-input question remains pending. Until a
checked allowed-state closure or actual-row sink-loss witness is supplied,
the selected target remains OPEN.

The same proof package also checks the fixed NORMAL library. On an EXACT
input point, every STAR/FLOW replay preserves the suffix after a prefix
replacement. Unions and any finite number of compositions cannot create
a field absent from the input and all provider outputs. Nine constructive
claims check this invariant and compute a fresh field witness. The current
OWASP library has 21 such NORMAL views, nine DEMAND MUST views and one
ZERO identity. Composing its NORMAL providers cannot cover the fresh
rename used in the earlier probe. This rules out that repair of the
NORMAL-envelope test. Eventual recovery through demand, new summaries and
caller feedback remains a separate, unproved obligation. The exact native
bindings are in `cases/normal-envelope-composition-no-go-v1/`.
