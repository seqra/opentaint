# Precise NORMAL replay envelope: selected OWASP obstruction

This is a rejected sufficient coverage test, not an edge verdict. The
selected row stays OPEN. No runtime semantics or campaign classification
changed. There is no native sink-loss case here.

## State and proposed guard

At the OWASP run-11 handoff, row `a76bfe14…` is:

```text
X: (entry = ret.bytes.[any]/FLOW;
    output = arg(1).bytes.[].*/FLOW)
```

The owner is `BenchmarkTest01985.doSomething(request, string)`. The names
identify the captured keys. They are not type or source-code guards. The
original latest reached/completed/accepted forward runs are run-11/run-11/
run-11. This probe starts no engine iteration or project scan.

One possible sufficient removal test would require saved NORMAL replay to
cover every precise result that the row can admit and retain:

```text
EnvelopeCovered(X, N) :=
  for every legal offer A and candidate relation S:
    if C2(X, A) admits S.premise and C5(X, S) retains S:
      scalarReplay(N, A) covers each required precise NORMAL result of S(A)
```

This test is stronger than eventual refined-finding preservation. Its
failure does not prove that X is necessary. It only refutes this blanket
precise-result cover from the actual retained NORMAL relation set.

## Counterexample to that cover

Let `h` be one fresh opaque FIELD accessor. No project type property is
used. All exclusions and FLOW mark exclusions below are empty.

```text
Offer A, NORMAL: ret.bytes.h.$/T
C2(X,A):        ret.bytes.h.*/FLOW, NORMAL

Hypothetical NORMAL relation S:
  ret.bytes.h.*/FLOW -> arg(1).bytes.[].h.*/FLOW

C5(X,S): retains S
  entry is in the native constructive C2 image;
  output has FL=3, within FL(X.output)+1=3.

S(A), NORMAL: arg(1).bytes.[].h.$/T
```

S is a legal candidate accepted by the native admission and restriction
operators. It is **not** claimed to be a relation produced by this Java
method. The example refutes a universal native-envelope argument; it is
not a faithful necessity case for the project.

The retained diagonal has an extra field in this application:

```text
Saved BACKWARD NORMAL:
  ret.*/FLOW -> arg(1).bytes.[].*/FLOW

On A, NORMAL:
  arg(1).bytes.[].bytes.h.$/T
```

Other retained precise readers produce different paths. None covers
`arg(1).bytes.[].h.$/T`. However, a saved forward MUST relation gives a
coarse result in the opposite read:

```text
Saved FORWARD NORMAL:
  arg(1).bytes.[].[any-taint]/FLOW -> ret.bytes.[any-taint]/FLOW

Native opposite view:
  ret.bytes.*/FLOW -> arg(1).bytes.[].[any]/FLOW, DEMAND

On A:
  arg(1).bytes.[].[any]/T, DEMAND
```

The MAY result geometrically covers the desired point. It does not supply
the precise NORMAL delivery. A proof that this coarse route eventually
replaces all required uses remains separate and open. Caller alias work,
other retained demands and whole-engine source/sink routes are not removed
or disproved by this scalar test.

## Native and formal checks

The portable runner is
[`probe_normal_envelope.py`](../../../../scripts/demand_campaign/probe_normal_envelope.py).
It checks all 29 captured NORMAL memberships, with their direct/opposite
roles and the native MUST inversion. The exact ZERO identity is disjoint
from the Return offer. Ten legal input cells cover FLOW/full T, STAR/EXACT/
MUST and actual NORMAL/DEMAND layers. No precise NORMAL cover exists in
these cells; coarse DEMAND covers do exist. Native C2 and C5 accept the
hypothetical relation. An isolated scalar probe is not a whole-engine test.

The native output paths bind to the following finite word family. Let `b`
be `bytes`, `e` be `[]`, and `s` be the distinct `<string-bytes>` accessor:

```text
NORMAL outputs on ret.bytes.h.*:
  [b,h], [e,b,h], [s,b,h], [s,e,b,h],
  [b,b,h], [b,e,b,h], [h], [s,h]

Required output: [b,e,h]
```

`NormalEnvelopeObstruction.lean` proves prefix noncoverage for this complete
observed precise output family with arbitrary distinct parameters and a
fresh h. It also checks that the coarse prefix `[b,e]` covers the target.
The three constructive claims use only `propext` and `Quot.sound`.

The final native and formal receipts are in the external campaign archive:

```text
redundant-demand-rows-20261112/cases/
  owasp-normal-envelope-obstruction-v4/
    receipt.json
    normal-paths.json
    NormalEnvelopeProbe.java
    compile.txt
    execute.txt
    lean-control-receipt.json
    lean-control.txt
```

The runtime is the verified source build at `pinned-runtime-source-build-v3`.
Its exact source revision is `14d7b633…`; historical whole-binary parity is
not claimed. The probe verifies all 438 classpath file hashes before use.
The first draft had an ambiguous Java import. A later draft used a Python
string operation unavailable on Python 3.8. Those failed attempts remain
outside Git; only v4 is the final native receipt.
