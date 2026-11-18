# Protected unrelated NORMAL return: an uncapped demand cycle

16 November 2026. Synthetic data-flow reachability. FULL marks.
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
[Consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md).

**Historical counterexample, now repaired.** The
[layer-aware completion repair](../design/bidirectional-layer-aware-point-service-20261116.md)
checks NORMAL-layer full closure with protection preserved, then plain service
for every overlapping terminal return. The updated reference naturally stops
at **run-5**, retaining its NORMAL observation; all earlier supplied examples
retain their results. [Updated complete trace](bidirectional-layer-aware-point-service-trace-20261116.md).
The old uncapped recurrence and proof below remain evidence for why the
repair is needed. Production is unchanged; latest native diagnostic remains
**run-31/POLICY**, with the model/native observation difference stated below.

**Before that repair, this is a counterexample to the executable completion
adapter, including reply-scoped completion.** The generic geometric
observation-preservation theorem remains sound; its current eligibility
checks do not certify this program.

The complete reference states repeat **run-11/run-12 forever**. The helper
has **70/82 DATA demand rows** and ten persisted NORMAL records. A root
DemandTarget and the next backward entry-marking permission remain active.
The NORMAL observation is retained from **run-5**; it does not cancel the
separate DemandTarget. No hard iteration limit enters the proof.

Latest finite unchanged native diagnostic: **run-31/POLICY**, with zero
NORMAL reports. The proposal reference retains a NORMAL observation from
run-5. This inherited native/reference difference remains explicit.

## 1. Fully analyzed code and rules

```java
class Box { Box f; Box g; Box h; Box k; }

// Entry marking rule: assign T only at a.f.g.$.
void root(Box a) {
    Box x = make(a).h;
    Box y = make(x).h;
    Box z = make(y).h;
    // Observation rule: CM(z.M,U).
}

Box make(Box p) {
    Box r = new Box();
    // Six ordinary positive unary marking rules at this point:
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST.    // H=1
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST.    // H=1
    return r;
}
```

`$` = EXACT; `*` = correlated STAR; M = MAY; NE = nonempty MAY;
MUST = uniform mark. N/D are NORMAL/DEMAND. H=1 is the existing protected
(non-subsumable) membership. H=0 is plain. All E/mx are empty.

The call graph is root -> make. It has three sequential call sites and
no recursive edge. Both methods have acyclic CFGs. Every `.h` is an ordinary
field read. There is no cleaner, configured pass rule, unresolved transfer,
predefined summary, field overwrite, static field or opaque operation.
The only configured effects are positive unary marking and observation rules.

Both marks are assigned and checked. Mark-set reduction cannot remove either
mark or the k actions merely because the helper's caller reads h. The k action
assigns a mark to a fresh output position; it is not an identity operation
and is not backed by an ordinary p-to-k FLOW relation.

The only program change from the previous h-read example is:

```text
old third action:  CM(p.M,T) -> assign U to r.k.MUST
new third action:  CM(p.M,T) -> assign T to r.k.MUST

old sixth action:  CM(p.M,U) -> assign T to r.k.MUST
new sixth action:  CM(p.M,U) -> assign U to r.k.MUST
```

The selected same-mark assignment law creates H=1 on these two results.
Protection is checked against the triggering conclusion's mark. A configured
pass does not create it. No protection law is changed for this investigation.

## 2. NORMAL and protected are independent

For the first precise input, the deep guard rejects:

```text
submitted / initial: p.f.g.$/T, N, H=0
CM(p.f.g.g.M,T):     false for this exact point

real raw returns:
    p.f.g.$/T -> ret.h.h.MUST/U, N, H=0
    p.f.g.$/T -> ret.k.MUST/T,   N, H=1
```

The second return stays **NORMAL**. H does not demote its layer. A same-mark
assignment can be exact as a conditional transfer and still be non-subsumable.
The native control checks precisely this result.

C5 admits h.h/U for the relevant h output selectors and discards k/T:

```text
ret.h.h.MUST/U intersects ret.h.*/U = ret.h.h.MUST/U
ret.k.MUST/T   intersects ret.h.*/U = empty
```

The k return is disjoint by field and mark. It is not a truncation artifact:
it has one field and fits every positive field limit. It is never delivered
through the caller's h read. No protected k NORMAL summary is retained merely
to support a completion flag.

## 3. The exact blocking checks

The current selected adapter uses:

```text
plainNormal(c) := not c.demand and not c.protected

bodyClosed(I,k) :=
    eligible NORMAL exact I
    and forall raw return c:
          plainNormal(c) and FL(c) <= k

replyAdapter(I,region) :=
    eligible NORMAL exact I
    and forall raw return c: plainNormal(c)
    and forall raw return c overlapping region:
          admitted whole NORMAL service covers c
```

These are the source-identical definitions of `ReplyBody.bodyClosed` and
`ReplyCore.completeFor`. The whole and full-mark adapters also keep their
selected plain-support checks.

For the h reply, every **terminal** requirement is already satisfied:

```text
region:                    ret.h.M/U
relevant raw returns:      {ret.h.h.MUST/U,N,H=0}
admitted NORMAL service:   p.f.g.$/T -> ret.h.h.MUST/U,N,H=0
same-context native image: x.h.MUST/U,N,H=0
```

Nevertheless, both full-raw scans reject `ret.k.MUST/T,N,H=1` **before**
terminal projection can help. The new closure bit stays absent; the
reply-specific check also fails independently. This holds at every field
limit, not just an early truncated run.

This isolates a conservative **adapter eligibility limitation**. It does
not show that NORMAL and protected are the same property, that the geometric
projection theorem is false, or that H may be removed. No guard is weakened
here. The investigation keeps the selected fallback to ordinary delivery.

## 4. How the demand repeats

The surviving coarse query still has a possible deep match:

```text
same actual: p.f.g.$/T,N,H=0
coarse C2 initial: p.f.*/T,D,H=0
possible deep guard -> ret.h.M/U,D,H=0
ordinary caller read .h -> x.M/U,D,H=0
```

The fine route yields only a child region at the caller:

```text
p.f.g.$/T,N,H=0 -> ret.h.h.MUST/U,N,H=0
ordinary caller read .h -> x.h.MUST/U,N,H=0
```

The child NORMAL MUST cannot cover root MAY. Actual-packet coverage keeps
the coarse root MAY, and the completion adapters do not remove it. The next
two ordinary calls renew root MAY with alternating U/T/U. All three calls
share the make owner, so its next plan again has broad and bounded child
queries. The k outputs stay irrelevant to the caller but keep blocking the
adapter's full-raw plain scan.

For each m in {T,U}, with flip(T)=U and flip(U)=T, the complete forward
frontier contains this plain DEMAND summary:

```text
p.f.*/m -> ret.h.M/flip(m), D, H=0
```

The next backward frontier includes its paired demand and emits a broad arm:

```text
entry demand: [ret.h.M/flip(m) | p.f.*/m]
backward summary: ret.h.*/flip(m) -> p.M/m, D, H=0
next forward demand: [p.M/m | ret.h.*/flip(m)]
```

That forward demand admits p.f.* again. The backward h read is handled
normally before the reversed call. Other refined rows also remain; they do
not remove this broad row. No demand is dropped because of the temporary
run-11 limit or because another edge repeats.

## 5. Complete cold trace and uncapped proof

[The per-block trace](bidirectional-protected-return-trace-20261116.md)
lists all demands, submitted facts and emitted initials above each forward
body, with published summaries below its return. Backward placement is
reversed. It includes all twelve cold runs, literal H memberships, and the
unpublished protected NORMAL return which blocks completion.

| Run | Helper DATA demand rows | Persisted NORMAL rows | Whole / mark / current closure keys | Root state |
|---|---:|---:|---:|---|
| run-1 | 6 | 0 | 0 / 0 / 0 | DemandTarget |
| run-2 | 6 | 0 | 0 / 0 / 0 | entry-marking permission |
| run-3 | 15 | 1 | 0 / 0 / 0 | DemandTarget |
| run-4 | 40 | 1 | 0 / 0 / 0 | entry-marking permission |
| run-5 | 42 | 8 | 0 / 0 / 0 | NORMAL observation and DemandTarget |
| run-6 | 67 | 8 | 0 / 0 / 0 | entry-marking permission |
| run-7 | 68 | 10 | 0 / 0 / 0 | DemandTarget |
| run-8 | 82 | 10 | 0 / 0 / 0 | entry-marking permission |
| run-9 | 70 | 10 | 0 / 0 / 0 | DemandTarget |
| run-10 | 82 | 10 | 0 / 0 / 0 | entry-marking permission |
| run-11 | 70 | 10 | 0 / 0 / 0 | DemandTarget |
| run-12 | 82 | 10 | 0 / 0 / 0 | entry-marking permission |

The constructive result is:

```text
forall n >= 0:
    history(11 + 2*n) = complete run-11 state
    history(12 + 2*n) = complete run-12 state

forall n >= 0:
    the displayed forward demand belongs to history(11+2*n)
    the displayed backward demand belongs to history(12+2*n)
    the forward stop test is false
```

The proof checks complete cold transitions through run-12, then every
within-run delivery/publication stage at arbitrary budget 8+n. Generic
run/parity lemmas connect those stages to every later field limit. An
induction proves the complete state cycle. Each within-run state is a fixed
point; the eight-round evaluation bound is not the reason for divergence.
No earlier forward run satisfies the stop test either.

Every ordinary initial keeps the global and own-Dc+1 caps. Every summary
output keeps the global and own-Dp+1 caps. All E/mx remain empty. The earlier
NORMAL-MUST/real-hole input exception is ineligible. Protection creates no
new field and changes no layer. Increasing the global limit cannot make
`not protected` true for the k return. The retained NORMAL observation does
not cancel an already emitted DemandTarget.

## 6. Validation and scope

[Constructive Lean package](../../spec/lean/proposals/protected-return-cycle-20261116/README.md).
The checker source-compares every selected admission, C5, whole/mark/reply
completion, receipt, publication, persistence and Target function against
`ReplyBody`. Only the analyzed k actions and their reverse transfer change.
The H result follows the existing native same-mark assignment law; it is
not a newly selected analyzer semantic change.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/protected-return-cycle-20261116/check.py \
  --out /tmp/protected-return-proofs

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ProtectedReturnCycleTest \
  --tests org.opentaint.dataflow.bidi.ReplyScopedPointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.ScopedPointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.UnadmittedFieldCycleTest --offline
```

The proof audit passes **184 new constructive claims; 6,102 cumulative claims
in 312 source-hash-checked modules**. Only `propext` and `Quot.sound` occur
in the new proof dependencies; no classical choice or custom axiom is used.

All **20 native component/control tests pass**, including three new tests.
They verify NORMAL+H=1 from an ordinary same-mark assignment, no new H from
the pass control, disjoint C5 rejection, relevant NORMAL service, and the
unchanged run-31/POLICY full-program diagnostic with DemandTarget.
The diagnostic has zero NORMAL reports; the proposal reference has its
NORMAL observation from run-5. No complete production NE/completion feature,
whole-engine/JVM/alias equivalence or project-performance claim is made.

This counterexample concerns the **currently selected conservative executable
adapter**, including its plain-H checks. A future stronger adapter might
certify this body; no such repair is selected here. The generic theorem
which requires a valid complete NORMAL service is not refuted by a program
whose adapter refuses that certificate. Production remains unchanged.

Raw captures, test XML, compiled proofs and audit receipts are outside the
repository under
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/protected-return-cycle-20261116/`.
The report and companion trace embed the fact data needed to review the case.
