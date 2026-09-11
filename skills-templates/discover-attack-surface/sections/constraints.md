{% include "shared/engine/facts.md" %}

- This stage finds only sources — the boundaries where untrusted data enters, sinks are found later from the taint frontier
- Work only your own plan and the source units it maps to — never another agent's plan or unit, shared coverage/classification state, or `tags.yaml`. Plans partition their write ownership according to the language reference
- Stored / second-order injection (data persisted then read back) is modeled by the engine itself — don't record a source for the read-back or a propagator for the store→read path
