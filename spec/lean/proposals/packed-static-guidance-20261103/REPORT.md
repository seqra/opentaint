# Packed static guidance proof report

Status: **SELECTED DESIGN / NO KOTLIN IMPLEMENTATION**.
Reference runtime: `050b83cfb7b2e75856ea113c44d0a2d6b707250d`.

## Executable witness

`intern` returns a geometry index and a table that preserves all old indices.
`compileFrom` emits primitive references in the exact input order.
`compileFrom_decode` proves complete ordered decode for every finite input,
including repeated rows and metadata with exclusions or typed ZERO values.

`packed_pair_roundtrip`, `packed_word_bound` and `colored_word_not_flow`
prove radix encoding when codes fit the radix and a mapped data row has a
nonzero endpoint code. Kotlin bitwise operations and current mark-ID bounds
still need their native adapter tests.

## Query and composition observations

`all_query_streams_equal` quantifies over every ordered old candidate plan
and executable keep predicate. It preserves duplicates and invalid-index
skip behavior in the finite plan. `index_plan_equal` covers any deterministic
plan rebuilt from the same complete decoded row stream.

`callback_trace_equal` preserves both the callback accumulator and the exact
consumed prefix through a false callback. `estimate_count_equal` and
`existence_equal` preserve count and boolean observations. Exact owner
projection, full mark relations and geometry metadata are preserved.

`complete_oracle_equal` proves equality of the complete finite query oracle.
`all_composition_prefixes_equal` then preserves every finite sequence of
query-dependent composition states. This includes a finite BFS expressed
with the unchanged oracle and transition. It does not introduce a new AP
join law, prove the existing BFS's unbounded termination, or verify a new
Kotlin index implementation.

## Cost scope

The trace model counts rich row allocations. Eager capture allocates one per
row; packed capture allocates none and lookup allocates only the selected
query results. A rejected keep candidate can still need marked endpoint
Patterns in Kotlin. This is not hidden by the row-allocation theorem.

The metadata/reference volume model proves a strict reduction in its stated
unit model when geometry count is at most row count and the input is nonempty.
For one geometry and repeated marks, it proves the exact variable path-cost
saving. These are allocation/storage unit laws, not exact JVM byte bounds,
a CPU bound for the executable linear reference interner, an actual GC free,
or a measured saving of the observed 1.37 GB builder.

## Correspondence limits

The old normalization/domain/classification adapter supplies the input stream.
Its AP operations, full/group selector policy and typed terminal rules are
not redefined in this model. The model includes complete symbolic endpoint
metadata and exact input/output labels; it proves no new semantic filter.

The Kotlin migration must preserve old local ordinal order, geometry group
order, first-insertion normalized dedup, all W/R/terminal methods and B's
existing common-method visibility. Native differential tests must compare
sequences, callback traces, estimates, scopes, logical counters and complete
static composition. A finite theorem about this catalog is not verification
of those Kotlin adapters.

The checker rejects unproved axioms, `sorry`, unsafe evaluation, Classical,
choice and noncomputable definitions in this source. It audits every explicit
public definition and theorem and permits only foundational `propext` and
`Quot.sound`. See the generated receipt for exact theorem/declaration counts.
