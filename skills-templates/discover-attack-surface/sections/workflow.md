Read `references/<language>.md` before starting. Its numbered steps provide the language-specific details for the workflow below.

### 1. Inspect the plan's members

The assigned plan's `scopes` contains the already-extracted project-used dependency members that still need a verdict. Inspect only those members. Confirm their dependency identity and exact signatures, then read application source, dependency source and API documentation, representative usages, and relevant framework configuration to understand how data enters the project.

### 2. Classify the plan's members

A source is the exact boundary where untrusted data first enters from a network, persistence, serialization, messaging, execution, or another external channel. For a callable member, decide whether it returns or otherwise exposes attacker-controlled data. A member that merely passes along data it was handed is a propagator, not a source.

Classify behavior rather than package or class names. For an individual member, prefer recording a borderline source with the uncertainty noted: later scan and triage can reject a false positive, while an omitted source becomes an unrecoverable false negative.

### 3. Record verdicts and source units

Complete the plan's source list in the form required by the language reference. Record every discovered source in its plan and write its source unit with `tag: untrusted-data-source`; resolving that unit to an existing or new rule happens later in `create-rule`. Non-sources create no unit. Mark an empty result explicitly so the reconcile join can distinguish it from a plan whose agent never returned. Where an owned unit already exists, merge new entries without rewriting its existing entries or stages.

### 4. Verify before returning

Re-check the full assigned scope against the classification. Re-read every rejected member and make sure it does not establish an external-input boundary. Confirm every source appears both in the completed plan and its source unit, no rejected member has a unit, and no pending/null verdict remains.
