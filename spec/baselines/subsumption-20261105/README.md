# Original subsumption design: frozen baseline

7 November 2026. This directory freezes the design before the current
`task.md` implementation. These files are evidence, not a new implementation.

- Pre-implementation checkout: `52829d5890ec3b3145cc996a1d8162d85cb8ceda`.
- First implementation: `8331bf9e326ddd1bd5083dbc50456963d6b26b52`.
- Reviewed analyzer: `52f32dd437d438aec4a700a02c18d94c31d58093`.
- The two baseline revisions have the same complete `core` tree:
  `6a3e587954faf5a5f9bcaf34f47e919edf69b95b`.

The [manifest](manifest.json) gives each original path, Git blob and SHA-256.
Each snapshot is an exact copy from the pre-implementation commit. Relative
links inside a snapshot retain their original text; use its original path
and revision from the manifest to resolve them. The current working-tree
copies include later corrections and are not substitutes for these snapshots.

Read the [original implementation proposal](original-implementation-proposal.md)
for the selected canonical facts, aligned NORMAL relations and directional
STAR matching. Its source designs are the
[field-path design](original-field-path-design.md) and
[relation/matching audit](original-relation-and-matching-audit.md).
The [FLOW-backed specification](original-flow-backed-spec.md) and
[correlated-concrete extension](original-correlated-concrete-spec.md) give
the earlier concrete relation and protection contracts which it reuses.

The new [baseline description](../../subsumption-redesign-baseline-20261107.md)
and [principal examples](../../subsumption-principal-examples-20261107.md)
separate the original design, later user decisions and the proposed emission
redesign. No baseline project campaign was rerun. No runtime source was
changed for this reset.
