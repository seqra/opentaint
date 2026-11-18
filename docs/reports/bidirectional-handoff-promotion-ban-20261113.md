# Separate STAR-to-MAY promotion bans

**Retired candidate.** The user set aside field bans. Continue with the
[demand progress and redundancy investigation](../design/bidirectional-demand-progress-and-termination-20261113.md).
The historical checks below are retained for reproducibility.

13 November 2026. Candidate analysis under
[proof-guide.md](../../spec/proof-guide.md). No production or canonical-spec
change. The selected operation is to omit the banned coarse MAY result.

**A promotion ban is not a field exclusion.** This fixes the earlier
clipped-NORMAL-reader counterexample. A field-only ban derived from one
NORMAL child relation can still suppress a different branch's required
refinement. The two issues have different causes.

**Correction after retaining both demands:** the first version removed
`ret.f.M` using ordinary MAY-prefix subsumption. A promotion ban changes
the retained parent's service, so that deletion is not justified by the
old language-inclusion argument. The trace below now explicitly keeps
both `ret.M` and `ret.f.M`. The remaining issue is narrower: an ancestor
STAR offer cannot start the deeper demand under the selected C2 rules.
With a MAY offer, the second demand does recover the reader.

## 1. Separate operational metadata

Keep semantic field exclusion E unchanged. Attach a separate query-local
`promotionBan` to the unrefined raw STAR start from a MAY demand. Concrete
field refinements, raw EXACT probes and MUST starts have no such ban.

```text
commands = C2(demand, originalOffer)
for command in commands:
    command.promotionBan =
        handoffBan(demand)
        if demand.tail == MAY
           and command.initial.path == demand.path
           and command.initial.tail == STAR
        else {}

transfer(command, operation):
    if operation would read unknown field f from STAR
       and f in command.promotionBan:
        omit only that STAR-to-MAY result
    else:
        use the ordinary transfer
```

The unknown-field test is about the symbolic suffix, not a field already
present in the concrete path. For example:

| Operation | Input; ban | Result |
| --- | --- | --- |
| `y = x.f` | `x.*`; `{f}` | omit coarse `y.MAY,D` |
| `y = x.f` | `x.f.*`; `{f}` | ordinary `y.*` |
| `y = x.f` | `x.MUST`; `{f}` | ordinary `y.MUST` |
| `y = x.f` | `x.MAY`; `{f}` | ordinary MAY transfer |
| reverse `return p.g` | `ret.*`; `{f}` | ordinary `p.g.*`, with unchanged E |

Do not emit STAR in place of the omitted MAY. Do not feed the ban into
native matching, mark checks, E, or public NORMAL summaries. It is not
evidence that the field is untainted. AP equality, public summary keys,
raw C2 admission, C5 and layers stay unchanged; the candidate removes work
inside a query. It must not make a banned query suppress another query's
unbanned derivation through deduplication.

This is a semantic pruning proposal, not a representation-only change.
Every omitted result needs a coverage argument.

## 2. The earlier wrapper is repaired

In the [previous E-based trace](bidirectional-handoff-star-only-exclusions-20261113.md),
the backward input `ret.*` produced the NORMAL reader
`ret.* {f} -> p.g.* {f}`. Its negative field information caused the loss.
With a separate ban, reverse `return p.g` is a known prefix write. It now
publishes the full NORMAL reader:

```text
choose: ret.* -> p.g.*, NORMAL
wrap:   ret.k.* -> p.g.*, NORMAL
```

Later forward replay carries the actual `p.g.MUST/T` to `ret.k.MUST/T`,
including its f field. The old clipped-reader proof does not refute this
new candidate.

## 3. A different branch still needs the omitted promotion

Keep the earlier handoff criterion: a broad same-premise MAY conclusion
can obtain a ban for f from a retained NORMAL child conclusion at f.
That NORMAL relation need not cover every branch that accesses f.
Keep the child MAY demand as well; do not rely on deleting it.

```java
class Box { Box f; Box g; Box h; Box k; }

void main(boolean first, boolean second) {
    Box a = sourceAtH();       // Assign T at a.h and ALL its descendants.
    Box r = wrap(a, first, second);
    sinkExact(r.k.f);          // Check T exactly at r.k.f.$.
}

Box wrap(Box p, boolean first, boolean second) {
    Box x = choose(p, first, second);
    Box q = new Box();
    q.k = x;
    return q;
}

Box choose(Box p, boolean first, boolean second) {
    if (first) return p.g;
    Box q = new Box();
    if (second) q.f = p.h;     // Real flow: p.h -> ret.f.
    else q.f = p;             // Other correlation: p -> ret.f.
    return q;
}
```

FULL mode, aliases disabled, empty E/mx, H=false; limits `1,1,2,3,...`.
There are no loops, recursion, statics, cleaners or ND. The source/sink
rules apply at the displayed calls. F=FLOW, M=MAY, U=MUST, N=NORMAL,
D=DEMAND. `[Dc ; Dp]` denotes a complete incoming demand pair. Initials
listed below are identities. The annotations show the principal DATA
routes; ordinary ZERO control and saved replay are not disabled.

### Run-1, forward, limit 1

```java
// Unrestricted; submitted/initial p.*/F,N.
Box choose(Box p, boolean first, boolean second) {
    if (first) return p.g;     // p.* -> ret.M/F,D.
    Box q = new Box();
    if (second) q.f = p.h;     // p.* -> ret.f.M/F,D.
    else q.f = p;             // p.* -> ret.f.*/F,N.
    return q;
}
// Published D: p.* -> ret.M/F AND p.* -> ret.f.M/F; retain BOTH.
// Published N: p.* -> ret.f.*/F. Handoff chooses promotionBan={f}.

// Unrestricted; submitted/initial p.*/F,N.
Box wrap(Box p, boolean first, boolean second) {
    Box x = choose(p, first, second);
    Box q = new Box();
    q.k = x;
    return q;
}
// Published principal D: p.* -> ret.k.M/F.
// The direct writer's ret.k.f.* really cuts to ret.k.NE/F,D.
// No NORMAL return provider for either writer at this limit.
```

Main submits and starts ZERO,N. The source supplies `a.h.U/T,N`.
Coarse return candidates reach the sink and produce DemandTarget.

### Run-2, backward, limit 1

The exact sink's two-field requirement cuts to `r.k.NE/T,D`. As in the
earlier wrapper, this creates only a STAR query at wrap's return k and
only a STAR offer at choose's return root.

Keeping a demand row does not by itself start its analysis. C2 must admit
the actual submitted fact. Here are the two retained rows separately:

| Demand entry Dc | Submitted fact | Emitted initial |
| --- | --- | --- |
| `ret.M/F` | `ret.*/F,N` | `ret.*/F,N`, with ban f |
| `ret.f.M/F` | `ret.*/F,N` | none: demand is deeper than a submitted STAR |
| `ret.f.M/F` | `ret.M/F,D` | `ret.f.$/F,N` and `ret.f.*/F,N`, without bans |
| `ret.f.M/F` | `ret.f.*/F,N` | `ret.f.*/F,N`, without bans |

The last two rows explain when the second demand handles the branch
correctly. The wrapper produces the second row, not either of those offers.
`wrap` starts `ret.k.*` from `ret.k.NE`; undoing its known k write then
submits `ret.*` to choose. There is no remaining MAY offer at that call.

```java
// CHOOSE newly publishes N: ret.*/F -> p.g.*/F, without exclusions.
// CHOOSE publishes no DATA demand from this current query.
Box choose(Box p, boolean first, boolean second) {
    if (first) return p.g;     // Reverse: prefix g; p.g.*,N survives.
    Box q = new Box();
    if (second) q.f = p.h;     // Reverse: read f from ret.* is banned.
                              // Missing intermediate MAY would prefix h.
    else q.f = p;             // Reverse: read f from ret.* is also banned.
    return q;
}
// Demands [ret.M/F ; p.*/F] AND [ret.f.M/F ; p.*/F].
// Submitted ret.*/F,N.
// First demand: initial ret.*/F,N; promotionBan={f}; E remains empty.
// Second demand: NO initial; ancestor STAR cannot refine to a known f.

// WRAP publishes N: ret.k.*/F -> p.g.*/F.
// WRAP also publishes D: ret.k.*/F -> p.M/F.
Box wrap(Box p, boolean first, boolean second) {
    Box x = choose(p, first, second);
    Box q = new Box();
    q.k = x;                   // Reverse: strip known k, submit x.*.
    return q;
}
// Demand [ret.k.M/F ; p.*/F]. Submitted ret.k.NE/T,D.
// Initial ret.k.*/F,N. No EXACT alternative at this same head.
```

Saved choose replay still applies its NORMAL opposite `ret.f.* -> p.*`
to the **original**, unbanned `ret.*` offer. It produces `p.M/F,D` in
wrap's active query. This explains the retained wrap demand and preserves
the source permission at h for run-3. It is not a new choose summary with
choose's own current initial. No reader for p.h has been learned.

Without the ban, choose's current query would publish both
`ret.* -> p.h.M/F,D` and `ret.* -> p.M/F,D`; the broad same-premise MAY
has no ban in that baseline and can cover the former. Thus choose would have its own outgoing DATA demand
and would be eligible for the forward h refinement next run.

With an actual MAY offer instead, the retained child row starts
`ret.f.$/F,N`. Reverse `q.f = p.h` reads a known f, yielding `p.h.$/F,N`;
normalization and C5 publish NORMAL `ret.f.* -> p.h.*`. This directly
preserves the required reader. It is incorrect to claim loss for that
MAY-offer case. Keeping both rows repairs it.

### Run-3, forward, limit 2

```java
// WRAP demand [p.M/F ; ret.k.*/F]. Submitted p.h.U/T,N.
// Initials p.h.*/F,N and conditional p.$/F,N, both without bans.
Box wrap(Box p, boolean first, boolean second) {
    Box x = choose(p, first, second);
    Box q = new Box();
    q.k = x;
    return q;
}
// On p.h.*: direct saved writer gives ret.k.f.h.* -> ret.k.f.NE/F,D.
// On p.$: direct saved writer learns N p.* -> ret.k.f.*.
// The saved g reader has no match for the h source.

// No current choose DATA demand; no DATA initial from these offers.
// Saved NORMAL replay runs before that empty-demand check.
// Offers include p.h.*/F and p.$/F from wrap's two active queries.
Box choose(Box p, boolean first, boolean second) {
    if (first) return p.g;
    Box q = new Box();
    if (second) q.f = p.h;
    else q.f = p;
    return q;
}
// No new current DATA summary. Saved p.* -> ret.f.* remains available.
```

The actual h source passes through the direct writer into `ret.k.f.h.U/T`.
Its two-field cut is `ret.k.f.NE/T,D`, which cannot satisfy the exact
same-head sink at `ret.k.f.$`. The saved g reader cannot match h. The
precise NORMAL relation learned by the prefix probe also has the direct
writer's correlation: it puts the h source under `ret.k.f.h`, not at
`ret.k.f`.

Without the ban, choose's own demand admits the h refinement and its
middle branch learns **NORMAL `p.h.* -> ret.f.*`**. Wrap then learns
NORMAL `p.h.* -> ret.k.f.*`, which fits limit 2. Applying that relation to
the actual source yields `ret.k.f.U/T,N`. The exact sink has NORMAL support.
The direct writer cannot subsume this reader: on input `p.h.$`, the reader
returns `ret.f.$`, while the writer returns `ret.f.h.$`.

Keeping later iterations does not supply the missing input automatically.
The residual `ret.k.f.NE` demand rejects an exact same-head offer. Saved
opposite direct replay reaches `p.$/T`; saved opposite g replay reaches
`p.g.f.$/T`. Neither reaches the h source. This is not an argument based
on the temporary run-11 cap.

## 4. Proof scope and consequence

[PromotionBan.lean](../../spec/lean/proposals/handoff-may-exclusion-20261113/PromotionBan.lean)
checks the unchanged raw C2 image, unchanged E, unchanged allowed transfers,
known-prefix/MUST exceptions, the old wrapper repair, the three branch
transfers, both distinct suppressed routes, raw-image C5, original-offer
saved replay, the wrapper's retained h refinement, the wrong saved
correlation, NE's exact-root rejection, and the missing NORMAL reader.
The additional two-row checks keep both demands, show the ancestor-STAR
rejection, and construct the missing NORMAL reader from a MAY offer.

```sh
python3 spec/lean/proposals/handoff-may-exclusion-20261113/check.py \
    --promotion-ban --out /tmp/handoff-promotion-ban-check
```

Result: **PASS, 9 modules, 192 audited declarations**, including 34 new
separate-ban checks. Receipt: `handoff-may-exclusion-20261113/` +
`promotion-ban-proofs-v3/receipt.json` under the [external archive](EXTERNAL_DATA.md).
The failed first preparation is kept separately. This is a constructive
scalar reference and a mathematical program embedding, not an implemented
new-tail scan or a mechanized whole-driver execution.

The representation correction is valid. The remaining proof obligation
is about pruning: a retained NORMAL child relation must cover the result
of **the particular suppressed derivation**, with its input/output suffix
correlation. Alternatively, a separately admitted child query can preserve
the reader, as the MAY-offer check demonstrates. A retained child demand
alone is insufficient when C2 admits no query for the submitted STAR.
Subsumption must not discard that child merely because the parent MAY
contains its output language: compare the effective service with the ban.
No new coverage mechanism is selected here.

No project scan was run. The counterexample is evaluated through run-3;
the baseline confirms there. Historical latest reached/completed/accepted
forward positions remain OWASP **run-11/11/11**, Conductor **run-8/7/7**,
Stirling-PDF **run-11/10/9**.
