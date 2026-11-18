# Shared analysis owner for certified forwarding methods

15 November 2026. Production is unchanged. See the
[proposal](../../../../docs/design/bidirectional-transparent-forwarder-termination-20261115.md)
and [complete old/new reference report](../../../../docs/reports/bidirectional-transparent-forwarder-termination-reference-20261115.md).

| Module | Scope |
| --- | --- |
| `OwnerProjection.lean` | Strict certificate traits; exact relay execution/observation/exception equivalence; arbitrary relay chains; frame/cut/protection invariants; ordinary fallback |
| `DirectMachine.lean` | Original input goes directly to choose's old call service; no wrapper C2/store/C5 |
| `ProxyCertificates.lean` | Complete cold run-1 through run-9 states, quiescence and handoff; keep the run-7 real cut, empty run-9 frontier |
| `ProxyAcceptance.lean` | Guarded dispatch, all old acceptance cases and arbitrary reader suffixes, final empty DATA/Target frontier with retained NORMAL observation |

The original nested counterexample remains as an old-policy regression.
Its unchecked survival screen is not used as proof of either result.
The new reference's natural stop follows the full quiescent empty frontier;
there is no analysis iteration cap in that argument.

Recheck everything into a fresh directory outside the repo:

```sh
python3 spec/lean/proposals/transparent-forwarder-termination-20261115/check.py \
  --out /tmp/forwarder-proof-fresh
```

The command rechecks the previous packages, including the original counter,
then the new modules. It passes **55 new theorems**, **597 audited
declarations in 36 modules**. Every theorem has an axiom audit; custom or
Classical axioms, holes and `native_decide` are rejected. Only Lean's
`propext` and `Quot.sound` are allowed.

`scripts/demand_experiments/no-cleaner-counterexample/capture_proxy.py`
generates the cold witness literals and exploratory capture. The generated
literals are checked independently with kernel `decide` against the Lean
machine. `render_proxy_report.py` renders their annotations. Python is not
a proof oracle.

The reference interface assumes a valid method-form certificate. It does
not prove that a Kotlin/JIR recognizer produces that certificate, or that
the native core already has proxy/NE support. Twelve native component tests
check the reused services separately. Unsupported contexts must fall back;
this is not a general saved-replay pruning rule or global termination proof.

Latest reached/completed: new reference **run-9/run-9**; original control
**run-31** plus its uncapped recurrence; old required references
**run-1/run-3**. Native forward/backward operators use run-9/run-8 field
geometry, and include an existing run-3 body check. No project scan was run.
