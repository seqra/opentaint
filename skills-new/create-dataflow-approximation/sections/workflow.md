### 1. Understand the propagation

Find and read each dataflow method's real source — skip the ones already in `build.done` (built and verified, leave them and their source as-is). An app-internal method sits in the project's own sources, a library method's source comes from its dependency (the language reference has how to get it). Read it to see how data moves from the method's inputs (receiver, arguments) to its outputs (return value, arguments it writes into, state it stores), gather the full context you need to fully understand the function's behavior.

### 2. Write the approximation

Reproduce that propagation as code under `.opentaint/dataflow/<batch>`, one `@Approximate` class per target class. Cover every dataflow method and overload the batch lists, add new methods to the existing source rather than rewriting it. The engine is field-sensitive — taint is tracked per field — so route data field-to-field exactly as the source does rather than tainting the whole object. The test project's negative samples (if present) verify this by storing taint in one field and reading another, so an over-broad model makes them fire. The code form, annotations, and patterns are in the language reference.

### 3. Test against the test project

Run the approximation test over the compiled test project, applying this batch's sources, and iterate until the samples pass. Feedback loop: a failing sample might be caused by: the model's target class or signature doesn't match what the analyzer sees, or the body doesn't route taint from the real source to the modeled output — diagnose the mismatch, fix, and re-run, don't rationalize a non-result. When the cause isn't obvious, localize where taint dies with a fact-reachability trace before guessing further per `references/debugging.md`. On a pass, append the method to `build.done` (per Tracking).

### 4. Escalate

When the trace points to a clear cause you can't fix here — taint dying past your model, at a plain instruction the engine should propagate through — or the sample won't converge after ~3 fixes, leave the method out of `build.done` and report it, for the orchestrator to intervene.
