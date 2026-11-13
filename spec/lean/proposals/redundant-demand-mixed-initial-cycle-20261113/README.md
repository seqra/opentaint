# Mixed initial demand cycle

13 November 2026. Run with `lake env lean MixedOfferCycle.lean` from the
repository's `spec/lean` project.

This constructive component implements the empty-E/mx FLOW cells used by
the [native cycle report](../../../../docs/reports/bidirectional-mixed-initial-demand-cycle-20261113.md).
It proves a local cycle for all later natural-numbered steps and preserves
all computed NORMAL providers. `step` does not feed saved replay results
back into the query; `pointSupported` checks their exact point service
separately. The native component replays providers before C2 on fixed
offers, without caller feedback. Only its reached EXACT/STAR/ANY cells
have native correspondence checks.

It assumes the initial rows and external
EXACT/STAR offers. It does not prove that a whole program produces those
inputs, that a corpus edge is necessary, or that an actual sink is lost.

All eleven theorem audits use `propext` only. The model adds no analyzer
semantics and installs no deletion rule.
