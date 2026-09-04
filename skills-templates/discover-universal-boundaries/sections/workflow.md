### 1. Reconstruct every trace

For each assigned evidence item, read what the pass recorded for it — a reference finding's normalized file, or the member or code area `scope.yaml` named — and then the project source it points at, and record:

1. the attacker or untrusted authority;
2. the first project-visible ingress;
3. the transformations and trust-domain crossings on the way;
4. the validators, guards, and authorization decisions it passes;
5. the primitive security-relevant effect at the end; and
6. the vulnerable invariant that is absent or defeated.

Read enough surrounding source to tell the real boundary from incidental syntax — the language reference says how to reach a dependency member's source, and which local shapes are propagation rather than ingress. A getter, collection lookup, or service method is usually propagation or context, not ingress.

### 2. Propose the source

Move backward from the evidence's own expressions until you reach the earliest reusable trust-boundary value the family shares. Prefer, in order when applicable:

- request body, parameter, path, query, header, cookie, or multipart value;
- message, frame, packet, event, webhook, or callback payload;
- deserialized external object;
- persisted attacker-controlled record at a second-order re-entry boundary;
- tenant or user-controlled configuration at activation or read-back;
- environment or runtime configuration entering a security decision; or
- an explicit structural pseudo-source standing for attacker-selected identity or control state.

The language reference names the boundaries its built-in source rules already carry — one they match needs no new boundary — and what identifies a boundary in that language. Reject a candidate that is merely a map or collection read after untrusted data has already entered, a `$METAVAR.method(...)` with no boundary type, signature, declarative marker, or enclosing entrypoint, a ubiquitous getter that would taint trusted objects just as readily, or an internal carrier that ordinary propagation or a later approximation should handle.

Express narrow usage conditions separately, as typed patterns, `pattern-inside`, `...`, and whatever declarative marker the language offers. Never bake incidental access syntax into the source.

### 3. Propose the sink

Move forward from the evidence's own service calls to the most primitive operation that realizes the vulnerability, while staying specific to its class. Prefer boundaries such as:

- network connect, request, send, or download for SSRF;
- process, script, expression, template, query, or deserialization execution for injection;
- path resolution plus filesystem read/write for traversal;
- privileged object read or disclosure for IDOR and data exposure;
- privileged object mutation or durable state commit for integrity and authorization failures;
- authentication or authorization decision for control bypass;
- redirect or token release for redirect and OAuth issues;
- signature verification or unsigned callback state commit for callback integrity;
- secret activation, credential construction, or outbound use for secret exposure; and
- logger argument consumption for log injection.

The language reference names the packages that realize these effects, and its built-in sinks. Don't stop at a controller-to-service call when the primitive effect is analyzable deeper in the project or a reusable library sink can express it. Use a structural sink only when the vulnerability *is* the missing control at that boundary, or when deeper propagation is genuinely unavailable.

### 4. Saturate

A boundary proposed from a few traces is a guess until it survives the whole family. Loop until a full round changes nothing.

Each round:

1. Factor every assigned evidence item — not only the new ones — through the current boundaries:

   ```text
   universal source -> item-specific context -> propagation -> universal sink
   ```

2. For each item that does not factor, generalize the offending side by exactly one step toward a more primitive boundary — never by adding a second alternative that merely spells out that item's syntax. A `pattern-either` listing one branch per evidence item is the failure this skill exists to prevent.
3. Re-check the items that already factored. A widening that breaks an earlier factorization is a widening too far: back it out and split instead.
4. Challenge the widened boundary in both directions — if the sink now admits a different vulnerability class, narrow it back to the primitive effect or add a class-specific context restriction; if the source now admits trusted values, record what separates them as a context restriction rather than shrinking the boundary.
5. Record the round: what changed, and which factorization statuses moved.

The family is saturated when a full round widened nothing, broke nothing, and left every assigned item either `covered` or `needs-restriction` with a named restriction. Stop and split — or record the item `unfactored`, with what blocked it in `open_questions` — rather than looping a fourth time on the same one.

When the only boundary the whole family shares is arbitrary syntax, the family was wrong: split it. Each subfamily gets its own spec named `<family>-<qualifier>` and its own saturation loop, and every assigned item lands in exactly one subfamily. A moved reference finding has its own file's `family` rewritten to the subfamily that now owns it; other evidence moves with the spec it is listed in, and the calling stage reconciles the family list to the specs you return.

Keep independently triggerable paths distinct in the factorization even when they share both boundaries.

### 5. Identify the precision controls

List these separately from the positive boundaries — the spec records them, and they must never be folded into the boundary patterns:

- sanitizers that actually enforce the relevant invariant;
- `pattern-not` exclusions for safe expression forms;
- `pattern-not-inside` exclusions for safe guarded regions;
- `pattern-inside` contexts that constrain a universal boundary to the intended entrypoint, type, tenant, or vulnerability family; and
- validators that are *not* security-relevant, recorded explicitly so nothing later mistakes them for sanitizers.

Real sanitization looks like resolved-IP private-range rejection for SSRF, canonical-path containment for traversal, strict identifier ownership checks for IDOR, signature verification for callbacks, and CR/LF neutralization for log injection. Presence, length, and parsing alone normally sanitize none of these; the language reference names the usual impostors and what the real controls look like in that language.

### 6. Write the specification

Write one spec per family or subfamily, listing the assigned ids under `evidence`. `candidate_patterns` must be concrete enough for `create-rule` to test, in the member shape that language's rule units use — the language reference gives that shape and the dependency identity to record with it. Record opaque carriers under `approximation_candidates`, and stop there: no approximation is created or recommended until a rule-first scan proves a trace stops at one.
