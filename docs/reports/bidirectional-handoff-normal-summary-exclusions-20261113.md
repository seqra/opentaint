# NORMAL-only demand exclusions are not sufficient

13 November 2026. Candidate investigation. No production or canonical-spec
change. Follow [the proof guide](../../spec/proof-guide.md).

**No: the NORMAL label alone is insufficient.** A NORMAL child summary
preserves its own input/output correlation. A different branch can still
require the coarse MAY demand to discover another dependence into that field.
Saved replay can succeed and still omit the real source route.

The later [STAR-only update](bidirectional-handoff-star-only-exclusions-20261113.md)
leaves concrete refinements unmasked and fixes this document's exact-input
counterexample. Its separate wrapper trace checks the remaining same-head
STAR case. Do not apply this document's old rejection rule to that update.

The interpretation here is that retained NORMAL `X -> Z` supplies the
exclusion witness for DEMAND `X -> a.MAY`. Existing handoff behavior stays:
NORMAL rows are persisted/replayed; they do not become new DEMAND rows.
Requiring both rows to be NORMAL would not apply to loss-created MAY.

## 1. Program and run-1

Change the false branch of
[the previous counterexample](bidirectional-handoff-may-exclusion-20261113.md)
to a single field write. Its child summary is now genuinely NORMAL:

```java
class Box { Box f; Box g; }

// MAIN: no demand; submitted ZERO,N; initial ZERO,N.
void main(boolean flag) {
    Box a = sourceAtG();         // Source T at a.g and ALL its descendants.
    Box r = choose(a, flag);    // Coarse read result r.MAY/T,D.
    sinkExact(r.f);             // Exact check at r.f.$/T.
}
// MAIN publishes ZERO -> DemandTarget,D, without a NORMAL sink witness.

// CHOOSE: unrestricted run-1, field limit 1.
// Submitted p.g.MUST/T,N; abstract initial p.*/FLOW,N.
// Ordinary mark requests supply T; there is no NORMAL read provider yet.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.g;            // p.* -> ret.MAY/FLOW,D.
    } else {
        Box q = new Box();
        q.f = p;               // p.* -> q.f.*/FLOW,N; no field cut.
        return q;
    }
}
// Same original X=p.*/FLOW:
//   D: X -> ret.MAY/FLOW, DEMAND
//   N: X -> ret.f.*/FLOW, NORMAL
```

Use FULL mode, aliases disabled, Empty E/mx, H=false and limits `1,1,2,...`.
There are no loops, recursion, cleaners, ND or statics. The source/sink are
external rule-bearing APIs, not hidden analyzed bodies.

N passes the proposed NORMAL guard and is retained in persistent storage.
The candidate excludes f from D's next entry selector. The previous premise
is unchanged:

```text
incoming pair:       [ret.MAY/FLOW excluding f ; p.*/FLOW]
saved NORMAL record: p.*/FLOW -> ret.f.*/FLOW
```

Forward application of N to the source's actual fact gives
`ret.f.g.MUST/T,N`, not exact `ret.f.$/T`. At limit 1 it can be cut to
`ret.f.NE/T,D`, which also excludes that root point. Only the coarse read
result provisionally reaches this sink in run-1.

## 2. Run-2: saved replay is included

The selected call order remains saved NORMAL replay first, then C2:

```java
// MAIN: the replayed DATA requirement does not complete the source route.
void main(boolean flag) {
    Box a = sourceAtG();        // a.$/T,N does not overlap source a.g.MUST/T.
    Box r = choose(a, flag);   // Offered ret.f.$/T,N.
                              // Saved N backwards -> p.$/T,N.
                              // Excluded broad C2 -> no current initial.
    sinkExact(r.f);            // Reverse seed r.f.$/T,N.
}
// MAIN demand [Target ; ZERO]; submitted ZERO,N; initial ZERO,N.

// CHOOSE: no new DATA summary or NORMAL reader is published.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.g;           // This branch needs p.g.f.$/T.
    } else {
        Box q = new Box();
        q.f = p;              // Saved N already answered this branch exactly.
        return q;
    }
}
// Incoming [ret.MAY/FLOW excluding f ; p.*/FLOW].
// Submitted ret.f.$/T,N.
// Saved opposite view ret.f.* -> p.* gives p.$/T,N.
// Current emitted initials: NONE.
```

The replayed root requirement is correct for `q.f = p`: that branch marks
q.f's root only if p's root has T. Our source marks p.g and its descendants,
so that requirement fails to reach the source. Successful NORMAL replay
does not establish that all other dependencies into ret.f were covered.

Keeping an existing child DEMAND `ret.f.NE` does not rescue this exact
offer: that selector rejects same-head EXACT. Turning N into an additional
child demand would be a different handoff rule, not the current candidate.

## 3. Without exclusion: run-2 learns the missing NORMAL reader

```java
// CHOOSE publishes NORMAL ret.*/FLOW -> p.g.*/FLOW,N.
// A cut child demand ret.f.* -> p.g.NE can coexist.
Box choose(Box p, boolean flag) {
    if (flag) {
        return p.g;           // ret.f.$ -> p.g.f.$ -> cut p.g.NE,D.
                              // Structural ret.$ probe -> p.g.$, NORMAL.
    } else {
        Box q = new Box();
        q.f = p;              // Saved N gives the separate p.$ requirement.
        return q;
    }
}
// Incoming [ret.MAY/FLOW ; p.*/FLOW].
// Submitted ret.f.$/T,N.
// Initials ret.f.$/FLOW,N AND conditional ret.$/FLOW,N.
// Complete FLOW normalization of the probe result stores ret.* -> p.g.*.
```

The marked backward requirement under p.g reaches the real source and
records source permission. In run-3, saved replay of the new reader gives:

```text
actual source:      p.g.MUST/T,N
NORMAL reader:     p.g.*/FLOW -> ret.*/FLOW,N
result:            ret.MUST/T,N
sink ret.f.$/T:    NORMAL witness
```

The candidate loses this provider and its real source-to-sink route. The
selected unanswered-demand policy adds no special continuation that would
reconstruct it. A larger field limit or temporary run cap does not repair
the missing admission.

## 4. Exact correlation witness

```text
source binding: p.g.f.$/T
true reader:    p.g.* -> ret.*    gives ret.f.$/T
NORMAL writer:  p.* -> ret.f.*    gives ret.f.g.f.$/T
```

The NORMAL writer preserves that particular suffix mapping. It does not
cover the reader's different mapping. This refutes whole-field coverage
even with a NORMAL witness, matching marks and the same stored premise.

An exclusion needs retained coverage **for the same actual binding and
required continuation**, including query/source guidance. Merely finding
a NORMAL output beneath f is insufficient. No new coverage predicate,
summary rule or NORMAL-to-DEMAND promotion is selected here.

## 5. Checked results and limits

[NormalOnly.lean](../../spec/lean/proposals/handoff-may-exclusion-20261113/NormalOnly.lean)
adds 12 constructive checks for the NORMAL child, actual saved backward
replay, its missed source overlap, the omitted reader requirement, the
baseline C5 provider and the explicit correlation witness:

```sh
python3 spec/lean/proposals/handoff-may-exclusion-20261113/check.py \
    --normal-only --out /tmp/handoff-normal-only-check
```

Result: **PASS, 7 modules, 131 audited declarations**, including 12 new
NORMAL-only checks. The receipt is
`handoff-may-exclusion-20261113/normal-proofs-v2/receipt.json` under the
[external report data archive](EXTERNAL_DATA.md). The failed initial syntax
preparation is separate and is not validation evidence.

The model checks scalar transfers and selected C2/C5 cells. The ordinary
ZERO/Target/source embedding is traced above; this is not a mechanized
whole-driver or native new-tail execution. No production behavior was
changed to obtain the result.

No project scan was run. The candidate loses its DATA route at run-2;
the original policy reaches the NORMAL finding at run-3. Historical latest
reached/completed/accepted-forward positions remain OWASP **run-11/11/11**,
Conductor **run-8/7/7**, Stirling-PDF **run-11/10/9**.
