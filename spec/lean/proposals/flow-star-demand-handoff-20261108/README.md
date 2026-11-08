# Correlated FLOW demand: C5 and handoff format

8 November 2026. Implementation correction under the finalized
[spec](../../../edge-subsumption-initial-emission-demand-intersection.md),
sections 4 and 5. The proof uses the pinned `AnnotatedC5Exit` operator.
It adds no transfer, admission command, tail kind or refinement rule.

The first Conductor experiment on `e1838296f` reached an engine-complete
**run-3**. Its handoff failed on an old ANY-only assertion. The next run
was not committed. This package is a component reproducer. It does not
identify the exact Conductor method row which first failed that assertion.
The real-project replay remains a separate check.

## Principal format trace

Write the previous complete demand as `Dp -> Dc`. At run-3:

```text
Previous demand:
  Dp = ret.$/T
  Dc = p.ANY/T

Current raw candidate:
  P = p.*/FLOW
  C = ret.ANY/FLOW, DEMAND, E={}, mx={U}, U != T

C5 entry:
  P is the authorized FLOW companion of p.*/T.

C5 paired output:
  ret.ANY/FLOW,D intersects ret.$/T
  = ret.$/FLOW,D, E={}, mx={U}

Existing whole-FLOW publication normalization:
  p.*/FLOW -> ret.*/FLOW,D, E={}, mx={U}

Existing handoff projection:
  next Dc = ret.*/FLOW, E={}, mx={}
  next Dp = p.*/FLOW, E={}, mx={}
```

No field cut occurs. The exact selector caused the EXACT result; ordinary
FLOW normalization then produced STAR. The raw candidate passes the old
pre-C5 ANY assertion. The published STAR result fails the old post-C5 ANY
assertion. Thus “the raw candidate is ANY” does not prove that its admitted
public output is ANY.

There is a second legal cell. C5 can retain an already correlated
`ret.*/FLOW,D` above `ret.f.ANY/T`. Keep its STAR, layer and actual E/mx.
The existing guidance projection clears only the FLOW selector E/mx. It
must not mutate the admitted summary. The native tests cover empty and
nonempty raw E in forward and backward directions.

## Selected implementation correction

```text
candidate -> existing whole-FLOW normalization -> C5 -> admitted summary
          -> existing guidancePattern on both paired endpoints
          -> demand builder -> next RunConfig
```

Remove obsolete ANY-only assertions before C5 and at method/block handoff.
The typed fact checks, canonical FLOW-pair check, paired C5, counted cap,
normal guidance projection and demand-builder checks remain active.
`DemandStore.validateIncoming` accepts the specified STAR/ANY FLOW entry
at every restricted run. The separate run-2-only static-completion check
remains unchanged.

Do not convert every STAR to ANY. Do not promote DEMAND to NORMAL. Do not
drop the row. Do not relax C2: a later precise STAR demand still rejects a
strictly deeper submitted fact. The native regression checks this rejection.
No full-mark or Target behavior changes here.

## Proofs and native correspondence

`Handoff.lean` proves 16 constructive component statements:

- C5 retains a legal correlated STAR/DEMAND output in both directions.
- Its layer and E survive when there is no counted cut.
- An exact paired selector can turn raw ANY/FLOW into EXACT/FLOW/DEMAND.
- Whole-FLOW normalization then gives STAR/FLOW/DEMAND.
- Existing projection preserves both complete endpoints and STAR tails.
- Existing FLOW selector normalization clears E/mx only in the guide.
- Existing MUST projection remains MAY; ordinary MAY projection is unchanged.
- Every offered pair has its own executable projection.
- The projected STAR FLOW entry is legal at every restricted run.

The checker first verifies the pinned 1,245-declaration component package,
then checks this bridge and its axiom audit. It permits only `propext` and
`Quot.sound` as in the existing checker. It rejects proof holes, custom
axioms and classical/noncomputable definitions. This is a format and
paired-row preservation result. It is not a native-analyzer or whole-project
soundness theorem.

```bash
python3 spec/lean/proposals/flow-star-demand-handoff-20261108/check.py \
  --output-directory /tmp/flow-star-handoff-UNIQUE

cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.CorrelatedFlowDemandHandOffTest \
  --tests org.opentaint.dataflow.bidi.NormalizedHandOffTest \
  --tests org.opentaint.dataflow.bidi.BlockHandOffTest \
  --tests org.opentaint.dataflow.bidi.RunConfigTest \
  --tests org.opentaint.dataflow.bidi.RedesignedInitialEmissionTest \
  --offline --no-daemon --max-workers=2
```

`CorrelatedFlowDemandHandOffTest` uses real native C5 and summary publication.
It covers raw ANY -> EXACT -> public STAR, retained raw STAR with E/mx,
method and block projection, exact physical port reversal, next-run config
validation and unchanged C2 non-refinement. The pre-repair component run
fails at the old candidate and block-handoff assertions. The project guard
also needs the post-C5 raw-ANY case above; the test traces that complete
format conversion separately.

## Repeated check result

The committed [receipt](receipt.json) records a successful repeated check:
1,245 pinned declarations plus 16 bridge declarations. The
[axiom audit](axiom-audit.txt) contains the bridge's actual dependencies.
`allPrincipalProgramsProved` and `nativeAnalyzerProved` remain false.

The [native receipt](native-checks.json) records 36 passing tests in the five
listed suites. Its principal class has three tests. The real project replay
is still required after the repaired runtime is built and committed.
