### 1. Classify propagation

Take the members from the plan's `scopes`, judge each one, and write the verdict to the batch file `.opentaint/tracking/approximations/<batch>.yaml` — `<batch>` is your plan's filename stem, the batch id, reused for the coverage check below.

Always classify from the method's real code, never from its name. Start by reading the method's source — the language reference describes how to get it. Then answer, for each method: where does its input data go? Data that arrives on the receiver or an argument — does it come back out, through the return value, an argument the method writes into, the receiver, or an object or field it stores the data in? That answer picks the bucket:

- `passthrough` — the method carries the data by a plain copy from one place to another: a getter, a simple arg-to-result copy, a builder, a writer that stashes the argument into the receiver or another object, a collection put-then-get, and the like
- `dataflow` — the method carries the data through a function, lambda, or callback parameter, or an async chain. Any method that takes a function goes here
- `skipped` — the method carries the data nowhere, give a short `reason`. This is exactly where a flow ends. A few examples: a predicate or inspector that only tests, compares, or measures its input (handing back a boolean or a number); a conversion that collapses the data into a scalar that no longer holds it (a size, a parse into a number, a one-way hash — the `size()` from the preamble); a side-effect that keeps none of the data. These are illustrations of the idea, not a closed list — many methods and cases fall outside it, so decide each on what its code does

The common trap is skipping an implicit carrier — a method that moves its data somewhere other than the plain return value. A `void` method that writes its argument into the receiver or another object still carries the data: it lives on in that object and the flow continues. A sanitizer or encoder is a carrier too — it returns a transformed copy of its input, so the data flows through it; model it, never skip it (whether the transform actually neutralizes the taint is settled later by the rules, not here). When in doubt, model it: over-approximating an inert method is cheap, dropping a real carrier is a false negative the run can't recover.

Every entry records the method's `signature` from the plan, so overloads stay distinct — a differently-propagating overload is its own entry. Placing each method in its bucket is all that's needed here; the build stage reads the method's own code to model exactly how the data moves.

A dropped method may be application-internal, not only library code — the analyzer drops it when its body is opaque to it (native, abstract, generated). Classify it the same way, by what its code does.

### 2. Classify sinks (deep run only)

When the `sinks` input is set, make a second pass over the same members for a different property: is the method a sink? A sink is a security-sensitive operation that turns into a vulnerability once attacker-controlled data reaches it — the call executes or interprets its input, or acts on it against a sensitive resource, in a way that can be abused: running it as a query or OS command, using it as a file path or URL, deserializing it, rendering it into output, or resolving it through reflection or a naming/directory lookup, among many others.

Judge sink-ness from the method's own code and behaviour, independent of how the project uses it — don't trace whether taint can actually reach the call, that is the analyzer's job. And judge it apart from propagation: the propagation verdict never settles sink-ness, and finding a sink never changes it. Sinks might sit among the carriers you just modeled, and a `skipped` method can be a sink too — carrying nothing onward says nothing about whether the call itself is dangerous.

Record each sink in its owning package's sink unit `.opentaint/tracking/rules/sinks/<package-kebab>.yaml` (per Tracking).

### 3. Verify coverage

After classifying, run the bundled check from the project root over your plan:

```bash
uv run scripts/check-coverage.py --batch <batch>
```

Pass your `<batch>`. It lists every batch method not yet in a classification bucket. Classify each one it prints and re-run until it reports `0 UNCOVERED`. Don't return while anything is uncovered.

### 4. Re-verify the skips

Before returning, review each method you skipped and confirm that it truly moves no data — the name is not good enough evidence. Get back to step 1 to reclassify any method that appeared to be carrier and remove it from `skipped`. Keep only methods proven non-carriers by their code
