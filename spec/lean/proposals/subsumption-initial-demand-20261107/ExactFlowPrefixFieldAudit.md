# Existing field behavior for the exact FLOW prefix

Source-only audit at exact baseline
`52829d5890ec3b3145cc996a1d8162d85cb8ceda`. No native test was run for this
audit. The [pins and embedded excerpts](exact-prefix-field-kernel-pins.json)
record the native scalar/tree operations, normalization and existing tests.
The audit does not use the dirty SOA prototype as its baseline.

The new policy emits an extra C2 identity. Executing its exact FLOW fact
requires no field-kernel change. These states already occur after existing
same-head ANY/FLOW admission of an exact actual.

Let the new raw seed be `p.$/FLOW,N`. E and mx start empty.

| Operation | Existing raw result | Summary boundary |
| --- | --- | --- |
| `return p` | `ret.$/FLOW,N` | Complete pair becomes `p.* -> ret.*`, N |
| `return p.f` | No return result from this seed | Exact p is a read barrier; retain the descendant primary |
| Strong `p.f = null` | `p.$/FLOW,N`, E={f} | Output becomes STAR with E={f}; do not restore f |
| Strong `p.f.g = null` | Outer exact FLOW/N with E={f}, plus inner `p.f.ANY/FLOW,D` | Keep the ANY/D residual and its layer |
| `RemoveAll(p)` | No FLOW result | Do not publish a surviving identity |
| `RemoveAll(p.f)` | Outer exact FLOW/N with E={f} | Same whole-position field-kill law |
| `RemoveAll(p.f.g)` | Same outer and inner residuals as the nested write | Do not promote the inner residual to NORMAL |
| Selected root cleaner T | Same geometry/layer, mx contains T | Preserve mx; the result cannot transport T |

Named selected cleaners retain their existing read/temp/strong-write lowering.
This exact prefix alone cannot read their temporary value; the descendant
primary is necessary. Weak writes keep their existing weak-update law.

Three shortcuts are invalid:

1. Normalizing the live exact seed to STAR before execution would enable
   child reads which this probe does not represent.
2. Dropping E during normalization would carry a marked overwritten field
   through the inferred STAR summary.
3. Dropping mx or making every residual NORMAL would restore cleaned marks
   or turn an uncertain nested region into a NORMAL proof.

The existing EXACT/FLOW query-view bridge remains in use after writes. It
can ignore that raw fact's E for C2 calculation while retaining the original
actual and E in the binding. Whole-FLOW normalization preserves paths, E,
mx and layers. Concrete exact facts and control results are not relabeled.

The generic new-emitter proof checks that the normalized prefix key already
belongs to the prior expanded C5 image. The new raw EXACT/FLOW image under
concrete selectors still requires the new proof; an old primary-only image
claim does not cover the expanded command stream.

Typed static anchors, mark catalogs, native scheduling/port correspondence
and root report adapters remain separate checks. This source audit does not
prove whole-program recovery or convergence.
