# Retire FLOW demand covered by saved summaries

10 November 2026. This is a design proposal. Production code is unchanged.
The reference runtime is `14d7b63369d94f49d4c551be8405ed7719f267cc`.
The latest OWASP measurement reached, completed and accepted **run-11**.

## 1. The selected pattern P(X)

**A FLOW demand can retire when every concrete transfer behind it already
has an independently retained NORMAL replay route.**

The test concerns the complete transfer behind X, not the arbitrary suffixes
introduced by its MAY approximation. A similar output path or a repeated
two-run cycle is not sufficient.

The first version accepts a restricted FULL run and a method-level edge:

```text
X = (A.p.*/FLOW -> B.q.[any]/FLOW), DEMAND
```

Both endpoints are nonstatic DATA. X has one premise. Field exclusions and
mark exclusions are empty. The source scope has a finite, acyclic copy graph.
Its DATA operations are ordinary STAR/FLOW copies, binding, local assignment
and field reads. Its call stages have no unknown callee or opaque transfer.
An unsupported scope makes P false. ZERO, Targets, concrete marks, protected
relations, static completion and loop summary ports are outside this version.

Let C be a complete finite copy relation for the scope. It contains prefix
rules, not enumerated concrete facts. For example:

```text
(A, a -> B, b) denotes all pairs (A.a.suffix/T -> B.b.suffix/T)
```

Restrict C to input paths below `A.p` and output paths below `B.q`. Keep
input/output correlation. Call the resulting finite set C(X).

P(X) is true exactly when the scope is supported and **every R in C(X)** has
a retained NORMAL record N with these properties:

1. Its native view V in the current direction covers R by the existing
   aligned NORMAL relation rule. One suffix extends both endpoints:
   `R.input = V.input + s` and `R.output = V.output + s`. The bases and complete
   method/context/interface match.
2. Its replay can accept every necessary input, including STAR. If N is a
   same-direction record, V's input prefix must be a prefix of X's input
   prefix. An opposite-direction record uses the existing `SAVED_OPPOSITE`
   matching rule, which permits a STAR ancestor.
3. N is admitted NORMAL data, retained independently of X. Use the native
   store after NORMAL persistence at the completed barrier. A demand edge,
   raw rejected candidate or proposed future normal summary is not a witness.

This condition is a sufficient test, not a necessary test for redundancy.
Unknown coverage leaves X in place.

## 2. Executable test

```text
P(X, scope, nativeRecords, currentDirection):
    if not eligibleRestrictedFullFlowDemand(X): return false
    C = completeCopyRelation(scope)
    if C is UNKNOWN: return false

    // These restrictions operate on paired prefix relations.
    origins = restrictInput(C, X.premise)
    origins = restrictOutput(origins, X.conclusion.prefix)

    for R in origins:
        covered = false
        for N in nativeRecords.atExactly(scope):
            if N is not eligible NORMAL STAR/FLOW: continue
            V = nativeView(N, currentDirection)
            if N.direction == currentDirection:
                if not isPrefix(V.input.path, X.premise.path): continue
            // Opposite records retain SAVED_OPPOSITE; do not relabel them.
            if alignedNormalRelationCovers(V, R):
                covered = true
                break
        if not covered: return false
    return true
```

An empty C(X) is safe only when C is complete: it proves that X's region has
no concrete copy transfer. An incomplete graph is UNKNOWN, not an empty graph.

This is not a test on the two stored endpoints alone. It also uses the scope's
complete copy graph and retained NORMAL basis. Those checks prevent a covered
producer from hiding a second, uncovered producer of the same MAY edge.

### Construct C without path enumeration

A row `a -> b` copies an arbitrary suffix unchanged. To compose rows
`a -> b` and `c -> d`, require matching intermediate bases, then use:

| Prefix relation | Composed row |
| --- | --- |
| `b = c.s` | `a -> d.s` |
| `c = b.s` | `a.s -> d` |
| b and c are disjoint | No row |

The two equal-prefix cases give the same row. Union control-flow branches;
compose sequential stages. Preserve untouched bases and local kills. Do not
invent a pass-through for a touched base. Input/output restriction uses the
same composition with an identity row at the requested prefix.

This construction is finite for the selected acyclic copy graph. It does not
require arbitrary-depth concrete suffixes. Filters and memory-effect guards
can be ignored only to form a conservative superset, and that entire superset
must pass the NORMAL coverage test. Sources, conjunctions, static operations,
nonempty cleaner/action lists and unknown callees reject this first DATA
graph adapter. Rule observations remain outside the copy graph, as specified
below. This does not declare the whole method to be predefined.

## 3. What can change

| Part | Current | Proposed |
| --- | --- | --- |
| Next-run FLOW frontier | Every final FLOW DEMAND row is projected | Omit X when P(X) is true |
| Known transfer | Re-analysis can recreate a MAY approximation of a known transfer | Saved NORMAL records supply that transfer before demand admission |
| Intrinsic read uncertainty | A STAR read can recreate method-local MAY demand indefinitely | Retire the local obligation when native replay already handles the read |
| Current-run propagation and observations | Use current summaries and rules | Keep this behavior |
| Initial emission, C5 and field limits | Existing rules | Existing rules |
| Concrete demand, source permissions, ZERO and Targets | Existing rules | Keep all of them |

The first implementation should make the decision at the completed handoff,
after NORMAL persistence. It must not erase current-run instruction facts,
cancel a rule application, remove a Target or suppress a source hit. This
changes the refinement frontier and can reduce later method analysis. It
does not introduce a new NORMAL fact or a new tail kind.

P does not mean NORMAL STAR subsumes arbitrary DEMAND MAY. It establishes an
independent replay route for the original transfers represented by the debt.
Speculative MAY combinations are not a requirement to create extra concrete
flows. This proposal preserves required flows, not the number of abstract
callbacks or provisional over-approximation paths.

## 4. The OWASP edges that pass

Use `bytes` for `String#<string-bytes>`, `javaBytes` for `String#bytes`, and
`[]` for the array element accessor. Let B range over the two byte fields.
All shown marks are FLOW.

| Runs | Edge X | Number |
| --- | --- | ---: |
| run-7, run-9, run-11 | `param.B.* -> ret.[any]` | 2 per run |
| run-7, run-9, run-11 | `param.B.[].* -> ret.D.[any]`, D is either byte field | 4 per run |
| run-8, run-10 | `ret.* -> param.B.[any]` | 2 per run |
| run-8, run-10 | `ret.D.* -> param.B.[].[any]`, D is bytes, javaBytes or content | 6 per run |

**All six forward and all eight backward FLOW demand relations pass P.**
The check covers 34 edge instances across runs 7–11, with 124 paired origin
rows and no missing replay witness. The byte fields remain distinct.

The full compiled DATA graph reduces to 12 parameter-to-return prefix rows.
The null branch returns a constant and has no parameter-to-return DATA flow.
The calculation includes every call-stage copy and alias edge. It does not
infer completeness from the few relations observed at the return statement.
It conservatively includes guarded alias copies and ignores deleting filters.

### 4.1 A C5 cut

```text
retained NORMAL S: param.* -> ret.*
suffix:            bytes.[]
precise relation:  param.bytes.[].* -> ret.bytes.[].*
C5 approximation:  param.bytes.[].* -> ret.bytes.[any], DEMAND
```

S already supplies the precise relation. The omitted cut is refinement work
for a transfer which S can replay. The complete C(X) test also checks the
other compatible copy paths, so it does not mistake this one witness for
coverage of the entire merged edge.

### 4.2 The forward constructor MAY

```text
X: param.bytes.* -> ret.[any], DEMAND

underlying reader R:
   param.bytes.[].* -> ret.*, NORMAL

retained BACKWARD record N:
   ret.* -> param.bytes.[].*, NORMAL

forward native view of N:
   param.bytes.[].* -> ret.*, NORMAL, SAVED_OPPOSITE
```

For a submitted `param.bytes.*/T`, this opposite view accepts the STAR
ancestor and emits the same conservative `ret.[any]/T` at the caller. For a
precise submitted `param.bytes.[].$/T`, it emits precise `ret.$/T`. It does
not require a current callee demand or a callee analyzer to perform that
replay. Thus retiring X does not discard the array-element read.

R is one of six clipped origins for this X. All six have retained witnesses;
the test is not based on R alone.

### 4.3 The backward constructor MAY

```text
X: ret.* -> param.bytes.[any], DEMAND

retained FORWARD record N:
   param.bytes.* -> ret.bytes.*, NORMAL

backward native view:
   ret.bytes.* -> param.bytes.*, NORMAL, SAVED_OPPOSITE
```

An incoming `ret.*/T` can use this view even though it does not name `bytes`.
The existing ancestor-read transfer emits `param.bytes.[any]/T` at the caller.
The more precise input `ret.bytes.$/T` gets `param.bytes.$/T`. This is the
existing native operation, not a new STAR admission policy.

The result is still allowed to be DEMAND. The optimization removes repeated
method-local inference of a known transfer. It does not claim that a broad
input becomes precise or that all caller demand will disappear.

## 5. Why the test is safe in this scope

### Complete paired origins

For prefix composition, suppose the intermediate location is `b.t` and must
also equal `c.u`. Either b is a prefix of c, c is a prefix of b, or they are
disjoint. The two nonempty cases give the composition table in section 2,
with an explicit remaining suffix witness. Induction over the finite graph
then enumerates every concrete copy path. Clipping retains exactly the paths
in X's input/output region. It never combines unrelated premises and results.

### NORMAL coverage

If `R = specialize(V, s)`, then an R transfer with residual suffix t is exactly
V's transfer with residual `s.t`. The mark and endpoint identity are unchanged.
This proves relation inclusion, including every longer concrete suffix. A
MAY approximation can retire because the original transfer remains available;
there is no need to interpret the MAY suffix as a new concrete effect.

### Replay availability

Saved records are applied on every original caller offer **before** current
demand admission. Retirement therefore cannot gate its own provider.
Same-direction providers must satisfy the prefix test in P. For an opposite
provider, current `satisfyingPart(... SAVED_OPPOSITE)` admits STAR ancestors,
and `applyRecordLeafPart` calls the same compiled edge operation used for
the copy transfer. The existing global field cut at the caller remains active.

The native probe checks 60 combinations of input geometry, mark kind and
layer against the ordinary micro-edge operation. It also checks that a deeper
same-direction reader rejects the broad STAR input. A NORMAL record with the
wrong read role is not a valid witness.

### Rule observations and source permissions

Retire only restricted-run FLOW DATA guidance. Such a demand emits FLOW
initials; it cannot authorize a concrete T initial. `markCheckFacts` returns
None for FLOW in a restricted run. A FLOW operand also cannot satisfy the
concrete premise of a reversed source action. Removing these redundant FLOW
queries therefore does not remove a concrete sink witness or source hit.

Keep concrete-mark demand and its FLOW companions, saved normal rule
contributors, ZERO, all Target rows, seeds and current-run rule execution.
Unconditional rule control follows ZERO, not the retired DATA permission.
The source/sink path in the caller can use the native record before callee
admission. The input-alias-closure contract from the existing subsumption
spec remains required; this proposal changes no alias classifier.

The actual helper is **not** free of configured sinks: the compiled plans
contain one sink at getBytes and eight at the constructor. Skipping all its
rules would be wrong. P does not do that. Concrete demand still causes normal
rule processing; the retired FLOW queries cannot satisfy these mark checks.

### Context and reversal

Replace an occurrence of an origin row on a caller path with its retained
NORMAL witness and the explicit suffix above. The endpoint, mark and call
binding remain the same. Repeat this replacement along the path. All external
source/sink sites stay on the path. The same construction works in reverse,
which preserves routes to source actions instead of relying on equal report
counts. The Lean model proves this boundary-path replacement theorem.

The theorem is for the declared copy scope and native replay contract. It
is not a proof of the whole Kotlin analyzer or of driver termination.

## 6. Conditions that must reject retirement

```java
Object choose(Box p) {
    if (flag()) return p.f;
    return p.g;
}
// Known only: p.f.* -> ret.*, NORMAL.
// Coarse merged edge: p.* -> ret.[any], DEMAND.
```

The known f reader does not cover the g reader. C(X) contains both. P is
false. With `sourceT(p.g); sinkT(choose(p));`, dropping the whole demand on
the basis of the f reader could lose the required g route.

Also reject these shortcuts:

- A same-direction `p.f.* -> ret.*` alone does not replace the broad STAR
  query `p.* -> ret.[any]`. Its direct replay rejects `p.*`. An opposite record
  or an applicable broader provider is required.
- `p.* -> ret.*` alone does not justify deleting a root MAY edge. It preserves
  suffix correlation; a field reader may move a child mark to the return root.
- Equal demand sets in two runs are not a certificate. There may be an
  uncovered reader, longer write, concrete source or live Target obligation.
- An explicit MAY transfer, unknown callee, loop, mark-changing rule or
  unsupported exclusion is not silently treated as a copy matrix.
- One covered contribution does not justify removing a merged edge with an
  uncovered contribution. The complete C(X) test is essential.

## 7. Evidence and proof limits

The [data record](../docs/reports/data/bidirectional-normal-backed-demand-20261110.json)
contains the complete forms, 12-row copy closure, all 34 edge certificates,
the native probe, source pins and validation receipts. The scoped constructive
model and observed certificates are in
[the proof package](lean/proposals/normal-backed-demand-20261110/README.md).

The forms capture completes **run-11**, with all **2,633 exact finding
locations unchanged**. The native probe and Lean checks pass. No retirement
filter has been installed in the runtime. These are coverage and replay
checks, not a measured post-optimization speedup or a demonstration that
OWASP now stops early. Other methods' Target demands remain outside this
local result.
