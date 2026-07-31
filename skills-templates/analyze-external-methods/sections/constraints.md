{% include "shared/engine/facts.md" %}

- Judge intrinsic propagation only, never per-project flow. Don't skip a carrier because its data doesn't seem to reach a sink here, and don't gate a sink on where its data goes — whether a flow reaches a sink is the analyzer's job, not yours
- Classify every method the plan assigns and only those — each is a real place data was lost, don't invent methods outside the plan. `check-coverage.py --batch` must report `0 UNCOVERED` before you return
