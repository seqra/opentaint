# Termination repair and the next counterexample search

17 November 2026. Synthetic data-flow reachability. Production unchanged.
[Current approach](../design/bidirectional-demand-termination-approach-20261115.md).
[Selected delta](../design/bidirectional-native-bound-reply-service-20261117.md).
[Complete cold traces](bidirectional-native-bound-reply-service-trace-20261117.md).

## Result

The protected caller-input counterexample is resolved. Its reference retains
its NORMAL observation at run-5 and reaches an empty forward frontier at
run-7. A uniform-input control retains its NORMAL observation at run-7 and
reaches an empty forward frontier at run-9. The five earlier service
references keep their run-5 stops. Each has a constructive uncapped
quiet-suffix proof; no hard limit establishes these stops.

The next search found no new counterexample in its 252 reference
configurations. This is a scoped result, not a universal termination theorem.
The catalogue retains all historical examples and their original scopes.

## Why the old reply survived

The first repaired case used a plain actual and relevant protected outputs.
Same-H NORMAL service closed it. Changing one action to assign T at
`r.h.f.g.$` makes the next actual protected. The same-H path then rejects
its original H. A separate shorter-STAR guard also rejects an exact-premise
record whose conclusion C5 has cut.

Representative packet, with actual `p.f.g.$/T,N,H=1`:

| Item | Shape |
|---|---|
| Already owned strong initial | `p.f.g.$/T,N` |
| Complete raw return for this actual | `ret.h.f.g.$/T,N,H=1` |
| Current C5-cut return | `p.f.g.$/T -> ret.h.f.NE/T,D,H=1` |
| Existing NORMAL service | `p.f.g.$/T -> ret.h.f.g.$/T,N,H=1` |
| Applied NORMAL image | The complete `h.f.g.$/T,N,H=1` image in this caller context |

The NORMAL exact return does **not** geometrically cover the entire coarse
NE region. It covers every real return of this completed strong query in
that region. This complete-answer certificate is the reason the coarse
current continuation can be omitted. A short NORMAL row by itself is not
enough. No stored DEMAND record is removed.

The uniform control exposes the exact-only closure guard. C2 already owns
its NORMAL MUST query, but does not create an exact point query. The new
adapter can close that existing query and use its actual NORMAL answer.
Canonical NORMAL MUST data can cover a removed scalar image; requiring that
removed scalar as a literal receipt would unnecessarily reject service.

Existing native binding transports input H and handles mark restoration.
The proposal compares these actual bound values. It does not clear H,
merge protected/plain storage, or alter field transfer to make a match pass.

## Search scope and counts

The first 216 configurations use two methods with ordinary allocation,
return, h reads and one to three unrolled calls. Positive marking actions
use a deep field guard and a root-MAY guard. Parameters vary:

- Entry path length 1–3 and EXACT/MUST entry marking.
- Deep guard length 2–4.
- EXACT/MUST broad-action result and a uniform deep-action result.
- One full mark or two alternating full marks.
- One, two or three calls in the acyclic caller.

The remaining 36 reference controls vary real E, inherited protection and
sibling/disjoint result fields. These are packet/admission controls; the
arbitrary initial E/H controls are not claimed as 36 separately realized
cold production programs. No analyzed example uses a loop, recursion,
cleaner, special pass rule, unresolved model or predefined summary.

| Natural empty forward frontier | Configurations |
|---|---:|
| run-3 | 12 |
| run-5 | 80 |
| run-7 | 127 |
| run-9 | 33 |
| Total | 252 |

Largest helper DATA demand frontier: **70 rows**. All 252 within-run checks
are fixed points through the latest diagnostic run, **run-25**. No stopped
reference revives in that capture. Final observations agree with direct
uncapped concrete evaluation in every configuration: zero lost and zero
extra observations in this family. The Lean family theorem separately
checks the run-9 frontiers and observations and proves an uncapped quiet
suffix. It does not generalize beyond the enumerated family.

The complete new and five prior cold references have kernel-checked
within-run fixed points. The wider family's prefix fixed-point checks are
executable diagnostics; do not confuse them with a general theorem that a
fixed number of rounds suffices for arbitrary methods.

## Proof and native scopes

Validation passes: **246 new constructive claims; 7,009 cumulative audited
claims in 399 source-hash-checked modules**. The axiom audit permits only
`propext` and `Quot.sound`.

The proof package checks constructive native witness extraction, complete
owned graph closure, whole-region coverage with literal bound H, actual
mark identity, persistence, owner DEMAND handoff and field limits. The
selector cannot add a query, path, summary or subscription. Generic
continuation preservation requires a valid full-closure adapter; the new
executable adapter is the finite positive-unary leaf model. Unknown child,
ND, alias, cleaner or other effects must not be omitted to claim closure.
Earlier acceptance models retain their scoped results; their largest
previous natural stop is run-15.

The native suite has **19 passing tests**, including eight new checks for
protected input, incoming-H transport, mark restoration, real MUST holes,
whole coverage, exact/same-head current premises and rejected contexts.
They validate the existing AP/application contracts. The whole proposal is
not integrated into production. The historical production diagnostic still
reaches **run-31/POLICY** and has the previously documented NORMAL-report
alignment difference from the scalar reference. It is neither an uncapped
proof nor a new-policy project measurement.

[Proof source and commands](../../spec/lean/proposals/native-bound-reply-service-20261117/README.md).
All bulk captures, receipts, compiled modules and XML stay outside Git at:
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/native-bound-reply-service-20261117/`.
