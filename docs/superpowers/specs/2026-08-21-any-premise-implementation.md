# `[any]` as a first-class premise accessor — implementation log

Implements `2026-08-21-any-premise-design.md` on branch `saloed/14-any-premise-impl`,
branched from `saloed/13-any-premise-design` (which is `saloed/5-default-get` @ `4c358d2e1`
plus the design doc).

The design's §10 sequencing is followed exactly; each step is one commit and is
independently testable.

| step | design ref | content | commit | gate |
|---|---|---|---|---|
| 0 | — | baseline test gate on the unmodified branch | — | |
| 1 | §5.1, §5.2 | `maxDepth` 10_000 -> 10; ban `[any]` below a taint mark; deep `containsAnyInThisOrDeepNodes` flag + collapse invariant; nested-`[any]` absorption in `AccessTreeAnySuffixMatcher` | | |
| 2 | §3.4 | concat absorption below `[any]`, constraints C0-C4 | | |
| 3 | §6.3 #1,#2,#3,#7 | `[any]` representable in `AccessPath` | | |
| 4 | §6.5 (#8) | replace the `allNodes()` blanket with the two-arm rule | | |
| 5 | §6.3 #4,#9 | `TreeInitialFactAbstraction` emits `[any]` premises | | |
| 6 | §3.3 | the unroll cap, default off | | |
| 7 | §11 | pack `AccessNode` flags into one byte | | |
| 8 | §12 | free wins | | |

## Gate definition

`scratchpad/gate-impl.sh <label>` runs `test`, `:opentaint-java-querylang:test`,
`:opentaint-go-querylang:test` in the impl worktree and reports pass/fail counts plus
the names of any failures. Every step must be green before the next starts.

## Results

(filled in as steps land)
