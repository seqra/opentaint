# BaseOnly trace-resolution fuzz evidence

## Result

Before the fix, the retained `nestedFactory` case was not a forward-analysis miss. BaseOnly created the vulnerability, but trace-path resolution rejected it:

```text
Total vulnerabilities: 1
Trace has no resolved paths
Filter out 1 vulnerabilities without traces
```

`BaseOnlyAccessOps.splitDelta` is not faulty in this case. The stored F2F summary used a field-slot abstraction for its initial access while its final access used a suffix-slot abstraction. Backward summary resolution therefore reconstructed `%1.<field-*>`, which was incompatible with the recorded `%1.value.*` edge. Normalizing the initial abstraction to the suffix slot gives `%1.*`, for which `fieldsCompatible(value, NO_ACCESSOR)` holds.

## Implemented fix

For an F2F summary with initial access `(s, ABSTRACT_MARK, NO_ACCESSOR)` and a suffix-abstract final access, summary storage now also records the normalized initial alias:

```text
(s, ABSTRACT_MARK, NO_ACCESSOR)
    -> (s, NO_ACCESSOR, ABSTRACT_MARK)
```

The original edge is retained because forward summary application intentionally treats suffix-AP prefixes as field-kind-strict; replacing it outright makes forward analysis lose the vulnerability. The normalized alias is used by backward resolution. The per-statement BaseOnly F2F edge lookup recognizes the same alias so that an inner summary trace with the normalized method initial can still match the originally recorded method edge.

With these two aligned aliases, the retained BaseOnly regression test passes without changing `splitDelta`, `fieldsCompatible`, or global prefix semantics.

## Complete summary-edge inventory

The pre-fix analysis emitted 19 summary edges: 8 `ZeroToZero`, 11 `FactToFact`, no `ZeroToFact`, and no `NDFactToFact`. All summaries required by the ideal trace existed; the initial abstraction position was the incompatible part.

```text
nestedFactory:
  Z -> Z                                      at return

source:
  Z -> Z                                      at return "tainted"

sink:
  Z -> Z                                      at return
  arg(0).* -> arg(0).*                        at return

envelope:
  Z -> Z                                      at return %0
  arg(0).* -> arg(0).*                        at return %0
  arg(0).* -> ret.box.*                       at return %0

Box(String), real constructor:
  Z -> Z                                      at return
  arg(0).* -> this.value.*                    at return
  arg(0).* -> arg(0).*                        at return

Box(String, synthetic access constructor):
  Z -> Z                                      at return
  arg(0).* -> this.value.*                    at return
  arg(0).* -> arg(0).*                        at return

Envelope(Box), real constructor:
  Z -> Z                                      at return
  arg(0).<field-*> -> this.box.*              at return
  arg(0).<field-*> -> arg(0).<field-*>        at return

Envelope(Box, synthetic access constructor):
  Z -> Z                                      at return
  arg(0).<field-*> -> this.box.*              at return
  arg(0).<field-*> -> arg(0).<field-*>        at return
```

## First divergence

The outer `nestedFactory -> envelope` application is correct:

```text
summary          = arg(0).* -> ret.box.*
caller fact      = result.box![tainted].$/*
matched fact     = result.box.*/*
delta            = ![tainted].$
mapped initial   = sourceTemp.*
reconstructed    = sourceTemp![tainted].$/*
contains edge    = true
```

Resolution then expands the `envelope` summary. Immediately after the synthetic `Envelope` constructor call, the trace edge is:

```text
MethodTraceEdge(initialFact=arg(0).*, fact=%0.box.*)
statement = %0.<init>(%1, null)
```

The applicable constructor summary is:

```text
arg(0).<field-*> -> this.box.*
```

The resolver performs:

```text
caller fact          = %0.box.*
mapped summary final = %0.box.*
splitDelta           = BaseOnlyEmptyInitialDelta
mapped initial       = %1.<field-*>
reconstructed fact   = %1.<field-*>
```

The two operands passed to `splitDelta` are identical, so its empty result is correct. The reconstructed fact is field-abstract, not bare. Diagnostic output renders it as `%1/{}` because `BaseOnlyApManager.renderAccess` prints `.*` only for a suffix-slot `ABSTRACT_MARK`; it does not print an abstract marker stored in the field slot. `BaseOnlyInitialFactAp` cannot contain the truly empty access, so the apparently bare rendering is unambiguous here.

Forward analysis actually applied the generic constructor summary to `%1.value.*`, and its stored edge proves the mismatch:

```text
containsEntryEdge query      = MethodTraceEdge(initialFact=arg(0).*, fact=%1.<field-*>)
stored candidates            = [%1.value.*]
contains result              = false
next statement               = %1.<init>(value, null)
result                       = no call action; trace terminates
```

The stored-edge lookup works correctly. For this comparison, `BaseOnlyFinalFactAp.contains` calls:

```text
BaseOnlyAccessOps.containsAccess(
    final   = value.*,
    initial = <field-*>
)
```

`fieldsCompatible(value, ABSTRACT_MARK)` is false. Although `fieldsCompatible(value, NO_ACCESSOR)` would be true, the reconstructed fact's field slot is `ABSTRACT_MARK`, not `NO_ACCESSOR`.

## Why output inversion cannot work

The forward operation was effectively:

```text
concrete caller predecessor  = %1.value.*
callee summary               = arg(0).<field-*> -> this.box.*
forward result               = %0.box.*
```

Forward summary application obtains the input-side `.value.*` refinement by comparing the concrete caller input with the summary initial. Appending it to the already field-qualified BaseOnly summary final collapses it into `%0.box.*`. Both `%1.value.*` and a less-qualified input can therefore produce the same abstract output.

Backward resolution instead compares `%0.box.*` with the mapped summary final `%0.box.*`. That comparison contains no `.value` information. Consequently,

```text
mappedSummaryInitial.concat(callerFact.splitDelta(mappedSummaryFinal))
```

cannot recover the input field refinement by itself. The summary-storage normalization supplies a compatible suffix-abstract precondition without changing `splitDelta`.

In this case the normalized `%1.*` precondition is contained by the stored `%1.value.*` fact and is also compatible with the following `Box` summary, allowing the existing resolver to continue.

## Ideal trace

The ideal trace, shown backward from sink to source, is:

```text
nestedFactory:
  sink(%4), fact %4.*
  <- %4 = %3.value, fact %3.value.*
  <- %3 = result.box, fact result.box.*
  <- result = envelope(%0), summary arg(0).* -> ret.box.*
  <- %0 = source(), fact %0.*
  <- source rule

envelope(String), initial fact arg(0).*:
  return %0, fact %0.box.*
  <- %0.<init>(%1, null), summary arg(0).<field-*> -> this.box.*,
     required concrete predecessor %1.value.*
  <- %1.<init>(value, null), summary arg(0).* -> this.value.*
  <- method entry arg(0).*

Box(String, synthetic access constructor):
  this.value.*
  <- private Box(String), summary arg(0).* -> this.value.*
  <- method entry arg(0).*

Box(String), real constructor:
  this.value = arg(0)
  <- method entry arg(0).*

Envelope(Box, synthetic access constructor):
  this.box.*
  <- private Envelope(Box), summary arg(0).<field-*> -> this.box.*
  <- method entry arg(0).<field-*>

Envelope(Box), real constructor:
  this.box = arg(0)
  <- method entry arg(0).<field-*>
```

The critical bridge is `%1.value.*` between the valid `Box` and `Envelope` constructor summaries. Current trace resolution reconstructs the broader `%1.<field-*>`; `containsEntryEdge` finds the concrete stored candidate but does not refine the trace edge to it, disconnecting two otherwise complete summary traces.

## Reproduction

```bash
cd core
./gradlew :test \
  --tests 'org.opentaint.jvm.sast.dataflow.JavaDataFlowReachabilityTest.base-only flow - trace resolves through nested factory result' \
  -x :opentaint-ir:go:buildGoServer \
  --no-daemon --max-workers=1
```

Temporary probes dumped every summary edge and the values around `resolveCallPassSummary` and `containsEntryEdge`; they were removed after collection. The complete diagnostic output from this investigation is retained at `/tmp/bo-full-diag.out` in the current workspace.
