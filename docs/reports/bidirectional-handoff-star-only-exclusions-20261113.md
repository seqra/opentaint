# Exclusions only on unrefined STAR initials

13 November 2026. Candidate investigation, following
[proof-guide.md](../../spec/proof-guide.md). No production or canonical-spec
change.

**Historical candidate:** this report uses real field exclusions E. The
latest clarification uses a separate STAR-to-MAY promotion ban instead.
The clipped-NORMAL-reader argument below does not apply to that revised
mechanism. See the [separate-ban analysis](bidirectional-handoff-promotion-ban-20261113.md).

**The update fixes the previous exact-refinement counterexample.** It does
not establish general soundness: a wrapper can submit STAR at the MAY head
without an EXACT alternative. Masking that STAR can remove the reader needed
when the sink's field becomes representable in a later run.

## 1. Precise updated policy

Keep the preceding NORMAL-only witness criterion for computing a handoff
mask. Do not remove that field from the demand selector itself. Run ordinary
C2 first, then attach the mask only to a raw same-head STAR command:

```text
commands = ordinaryC2(demand, originalOffer)
for command in commands:
    if demand.tail == MAY
       and command.initial.path == demand.path
       and command.initial.tail == STAR:
        command.initial.E += handoffMask(demand)
    emit command unchanged otherwise
```

The guard is evaluated **before FLOW normalization**. A raw EXACT/FLOW
probe that later normalizes to a public STAR key stays unmasked. Concrete
field refinements, including deeper STAR initials, stay unmasked. So do
MUST commands. Layers, marks, flags and ports do not change.

C5 must use the raw image of this updated C2. The check grants the candidate
that consistent update; it does not reject masked initials merely because
the old raw-image implementation omitted them. NORMAL exclusions persist
and ordinary field-exclusion semantics remains in force. No alternative
seed, new source permission or new tail kind is added.

For demand a.MAY with mask f:

| Original offer | Raw commands |
| --- | --- |
| a.f.$/T | a.f.$/FLOW and conditional a.$/FLOW, both unmasked |
| a.f.NE/T | a.f.STAR/FLOW and conditional a.$/FLOW, both unmasked |
| a.MAY/T | a.$/FLOW unmasked; a.STAR/FLOW with E={f} |
| a.STAR/FLOW | only a.STAR/FLOW with E={f} |
| a.MUST/T forward | dedicated a.MUST/FLOW, unmasked |

The first row restores the exact admission and NORMAL reader from
[the previous counterexample](bidirectional-handoff-normal-summary-exclusions-20261113.md).
The fourth row is the remaining case below.

## 2. A wrapper creates exactly that STAR-only offer

```java
class Box { Box f; Box g; Box k; }

void main(boolean flag) {
    Box a = sourceAtG();        // T at a.g and ALL its descendants.
    Box r = wrap(a, flag);
    sinkExact(r.k.f);           // Exact T check at r.k.f.$.
}

Box wrap(Box p, boolean flag) {
    Box x = choose(p, flag);
    Box q = new Box();
    q.k = x;
    return q;
}

Box choose(Box p, boolean flag) {
    if (flag) return p.g;
    Box q = new Box();
    q.f = p;
    return q;
}
```

Use FULL mode, aliases disabled, Empty initial E/mx, H=false and field
limits `1,1,2,3,...`. There are no loops, recursion, statics, cleaners or ND.
Source/sink APIs are configured at their call sites. The real true-branch
flow is `a.g.f -> r.k.f`.

Abbreviations: F=FLOW, M=MAY, U=MUST, N=NORMAL, D=DEMAND. `[Dc ; Dp]` is a
complete incoming pair. All listed initials are identities. The tables are
the relevant scalar route, not claimed complete actor dumps.

## 3. Run-1: the handoff mask has a genuine NORMAL witness

```java
// CHOOSE: unrestricted; submitted abstract p.*/F,N; initial p.*/F,N.
Box choose(Box p, boolean flag) {
    if (flag) return p.g;       // p.* -> ret.M/F,D.
    Box q = new Box();
    q.f = p;
    return q;                  // p.* -> ret.f.*/F,N, within limit 1.
}
// CHOOSE publishes DEMAND p.* -> ret.M and NORMAL p.* -> ret.f.*.
// Handoff records mask {f} for the ret.M demand.

// WRAP: unrestricted; initial p.*/F,N.
Box wrap(Box p, boolean flag) {
    Box x = choose(p, flag);    // x.M/F,D and x.f.*/F,N.
    Box q = new Box();
    q.k = x;                   // ret.k.M/F,D on the read route.
                               // ret.k.f.* cuts to ret.k.NE/F,D on the writer.
    return q;
}
// WRAP principal demand: p.*/F -> ret.k.M/F,D.
// Same-premise MAY covers the NE sibling. No NORMAL DATA return provider yet.
```

Main submits ZERO,N, starts ZERO,N and obtains the coarse marked return
through ordinary run-1 requests. The sink publishes `ZERO -> DemandTarget,D`.

## 4. Run-2: no concrete refinement reaches choose

The sink's exact requirement has two fields. At limit 1 its real field cut
produces `r.k.NE/T,D`.

```java
// WRAP publishes:
//   NORMAL ret.k.*/F -> p.g.*/F with conclusion E={f}
//   DEMAND ret.k.*/F -> p.M/F
Box wrap(Box p, boolean flag) {
    Box x = choose(p, flag);    // Reverse offer to choose: ret.*/F,N.
    Box q = new Box();
    q.k = x;                   // Reverse known k: q.k.* -> x.*.
    return q;
}
// WRAP incoming [ret.k.M/F ; p.*/F].
// Submitted ret.k.NE/T,D -> only initial ret.k.*/F,N.
// Heads are both ret.k, so no EXACT command or conditional prefix probe.

// CHOOSE newly publishes NORMAL:
//   ret.*/F {f} -> p.g.*/F {f}
// No outgoing DATA demand on this current query.
Box choose(Box p, boolean flag) {
    if (flag) return p.g;       // Reverse: write prefix g, retain E={f}.
    Box q = new Box();
    q.f = p;                   // Reverse read f is blocked by the exclusion.
    return q;
}
// CHOOSE incoming [ret.M/F ; p.*/F], mask f.
// Submitted ret.*/F,N -> only raw ret.*/F with E={f}, N.
```

Saved NORMAL writer replay still runs on the **original unmasked** offer
before current C2. Its opposite view `ret.f.* -> p.*` maps original ret.*
to `p.M/F,D`. That result belongs to wrap's enclosing query, not to the new
choose query. It supplies wrap's DEMAND row and reaches the actual source
region, so main's source permission for run-3 is retained.

Thus the failure is not fabricated by withholding saved replay or source
permission. The newly inferred reader itself has been clipped at f.

## 5. Run-3: concrete g refinement is preserved, but the saved reader is clipped

```java
// WRAP incoming [p.M/F ; ret.k.*/F].
// Source offer p.g.U/T,N -> initials p.g.*/F,N and p.$/F,N.
// Both are unmasked under the proposed rule, even if the handoff supplies g.
Box wrap(Box p, boolean flag) {
    Box x = choose(p, flag);    // No choose DATA demand; saved replay first.
                               // Reader replay: x.*/F with E={f}, NORMAL.
                               // Writer replay: x.f.g.*/F,N.
    Box q = new Box();
    q.k = x;                   // Reader: ret.k.* {f}, NORMAL.
                               // Writer: ret.k.f.g.* -> cut ret.k.f.NE,D.
    return q;
}
// WRAP publishes, among the relevant rows:
//   NORMAL p.g.*/F -> ret.k.*/F with conclusion E={f}
//   DEMAND p.g.*/F -> ret.k.f.NE/F
// The unmasked raw p.$ probe separately learns:
//   NORMAL p.*/F -> ret.k.f.*/F.
```

These are distinct routes. The last NORMAL row is the false-branch writer.
It does not cover the true dependence from p.g.f to ret.k.f.

Applying the NORMAL reader to the actual source's `p.g.U/T,N` produces
`ret.k.U/T,N` **excluding f**. It cannot satisfy the exact sink at ret.k.f.
The false writer places this source under ret.k.f.g; its cut NE fact also
cannot satisfy the root point ret.k.f.$. Neither route triggers this exact
sink in run-3, so no new DemandTarget or reverse sink seed is obtained from
it. This is already a loss of the real finding, not just delayed NORMAL
confirmation.

## 6. Later exact-offer probe: the remaining frontier cannot recover it

The larger run-4 limit 3 could represent the exact sink requirement fully:
`ret.k.f.$/T,N`. Wrap's remaining demand has entry `ret.k.f.NE`. The next
block is an **additional operator probe**, granting that exact offer; it
is not an asserted next-run seed from the sink that stopped firing above.

```java
// WRAP publishes no new true-reader DATA relation for this offer.
Box wrap(Box p, boolean flag) {
    Box x = choose(p, flag);    // No current wrap DATA initial reaches here.
    Box q = new Box();
    q.k = x;
    return q;
}
// Incoming principal pair [ret.k.f.NE/F ; p.g.*/F].
// Probe offer ret.k.f.$/T,N -> C2 emits NOTHING: same-head NE versus EXACT.
// Saved clipped reader cannot match the f suffix under ret.k.
// Saved false writer ret.k.f.* -> p.* gives p.$/T,N, which misses source g.
```

Choose has no fresh DATA demand from run-2 either. Ordinary ZERO completion
cannot seed an arbitrary DATA initial. The isolated program has no new
sink witness to regenerate the missing route; even granting the exact offer
does not revive it through the retained rows. No special action for an
unanswered demand is part of this policy. The temporary run-11 limit is not
used in this loss argument.

## 7. Without the mask, run-3 confirms the real finding

The same wrapper STAR offer in run-2 would let choose learn:

```text
choose NORMAL: ret.*/F -> p.g.*/F                  // no exclusion
wrap NORMAL:   ret.k.*/F -> p.g.*/F                // no exclusion
```

In run-3, saved opposite replay on the actual source gives
`p.g.U/T,N -> ret.k.U/T,N` without excluding f. The exact sink at ret.k.f
has NORMAL support. The real path was representable at the new limit; the
candidate lost its required guide while that field was still unknown.

## 8. Checked scope and conclusion

[StarOnly.lean](../../spec/lean/proposals/handoff-may-exclusion-20261113/StarOnly.lean)
checks the repaired exact/descendant/MUST cells, the MAY/STAR distinction,
the wrapper's real cut and sole STAR query, the updated raw-image C5,
exclusion-aware transfers, original-offer saved replay, paired wrapper C5,
the later exact rejection and the baseline NORMAL source application.

```sh
python3 spec/lean/proposals/handoff-may-exclusion-20261113/check.py \
    --star-only --out /tmp/handoff-star-only-check
```

Result: **PASS, 8 modules, 158 audited declarations**, including 27 new
STAR-only checks. The external receipt is
`handoff-may-exclusion-20261113/star-only-proofs-v3/receipt.json` under the
[report data archive](EXTERNAL_DATA.md). The failed first preparation is
kept separately and is not validation evidence.

This is a scalar constructive specification trace. It is not execution of
an implemented new-tail core or a complete mechanized driver. The report
supplies the ordinary source/Target embedding. No canonical spec policy,
field-limit schedule, cleaner or source behavior was changed to repair a
proof. NORMAL exclusions are persisted as already specified.

The update is a narrower proposal and repairs the previous exact-input
counterexample. It still cannot infer that an unknown f suffix is redundant
merely from a NORMAL child relation with a different correlation. Later
concrete refinement needs either the omitted route's guidance or a NORMAL
provider that already covers that route.

No project scan was run. The candidate trace loses the sink at run-3; the
run-4 exact-offer cell is a separate probe, not an assumed reached seed.
The baseline confirms the NORMAL finding at run-3. Historical latest reached/completed/
accepted-forward positions remain OWASP **run-11/11/11**, Conductor
**run-8/7/7**, Stirling-PDF **run-11/10/9**.
