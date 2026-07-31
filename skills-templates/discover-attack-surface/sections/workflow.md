### 1. Settle built-in coverage first

Before anything, for each package the plan touches see what the built-in source rules already match for its members — `opentaint health --rules` prints the built-in rules root path; browse it and the project's own rules (per the language reference). This decides whether you write a source unit:

- full — existing rules already match the project-used sources → write no unit, stop, don't drill further
- partial — some project-used sources matched, others missed → plan only the missing used members
- none — plan the package's project-used sources from scratch

### 2. Classify the plan's members

The members are the FQNs under the plan's `scopes` — the project-used scope, already extracted, and only the members not yet classified in a prior run. Confirm each package's dependency identity and inspect its signatures/docs while classifying (per the language reference); read app source, dependency API/docs, and framework config to classify the listed members.

Find the sources among them — the exact place untrusted data first enters from a boundary (network, persistence, serialization, messaging, execution and more): a method that returns attacker-controlled data. NOT a method that merely passes along data it was handed — that's a propagator the engine already handles. General, not class-tagged.

Better safe than sorry — when in doubt, record a borderline source rather than drop it: a false positive is filtered out later at the scan and triage stages, but a real one dropped here is a false negative the run can never recover. Note the doubt, and verify in the dependency when it's quick.

### 3. Write the source units

Two writes, both per Tracking: record every source under the plan's top-level `source` list, and write each package's sources into its source unit. Always write the `source` list — an empty list when the plan yields no source — so the reconcile join can tell your finished plan from one whose agent never returned (a plan still carrying `source: null` is left for re-dispatch, not merged). Where a package already has a unit from a prior run, add to it rather than rewriting — leave its existing entries and stages as-is.

### 4. Verify before returning

Re-check the full plan against your classification: confirm every plan member is accounted for, then re-read the ones you did NOT record as sources and make sure none of them is actually a source. A source left out here is a false negative the run can never recover. Add any you missed to the `source` list and its unit. This is a re-read of what you already wrote — simple grep or re-read is fine, no need to use some scripts.
