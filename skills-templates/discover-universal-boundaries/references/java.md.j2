# discover-universal-boundaries — Java / JVM

## Workflow

### 1. Reconstruct every trace

Dependency members come from the resolved jars under `.opentaint/project/dependencies`: locate a class with `unzip -l <jar> | grep <class-as-path>`, read its signatures with `javap -p -s -classpath <jar> <fully.qualified.Class>`, and prefer the source jar or a decompiler when the body matters.

Java-shaped propagation that is not ingress: a DTO or entity getter, `Map#get` after the request was already bound, a service method delegating a value it was handed, an `Optional`/stream chain over it, and framework binding of a value the endpoint already accepted.

### 2. Propose the source

Built-in Java source rules live under `java/lib/{generic,spring}/` within the `opentaint health --rules` root, the project's own under `.opentaint/rules/java`. A boundary they already match needs no new one, and their reach is wider than it looks:

- `lib/spring/untrusted-data-source.yaml` taints *every* non-scalar parameter of a method annotated `@RequestMapping`/`@GetMapping`/`@PostMapping`/`@PutMapping`/`@PatchMapping`/`@DeleteMapping`, whatever the parameter's own annotation — so `@RequestBody`, `@RequestParam`, `@PathVariable`, and `@ModelAttribute` on a Spring MVC endpoint are already sourced, as is a cookie read through `WebUtils#getCookie`
- `lib/generic/servlet-untrusted-data-source.yaml` taints the `HttpServletRequest` parameter of a servlet entry method (`doGet`, `doPost`, `doPut`, `doDelete`, `doTrace`, `_jspService`) as a whole object, plus `MessageBodyReader#readFrom`, a commons-fileupload `parseRequest(...).getName()`, and `Part#getSubmittedFileName`
- `lib/spring/untrusted-path-source.yaml` and `lib/generic/seam-untrusted-data-source.yaml` carry their own shapes

A Java family's shared source is therefore usually *outside* those shapes, and that is where to aim: a non-HTTP transport (`TextMessage#getPayload`, `ConsumerRecord#value`, a JMS or gRPC payload), a reactive `ServerRequest`/`ServerHttpRequest` accessor, a non-Spring stack's own request accessor, or a second-order re-entry where a persisted attacker-controlled record is read back.

Two shapes carry a Java boundary: an annotation on the declaration, with the enclosing annotated class or method as its `pattern-inside` context, or an accessor on a boundary type. Take the annotated parameter or the accessor itself, never the DTO getter downstream of it — the getter would taint trusted objects just as readily, and the binding step is already propagation.

### 3. Propose the sink

Where the primitive effects live, with the built-in `java/lib/` coverage named:

- SSRF — `RestTemplate`, `URL#openConnection` (`generic/ssrf-sinks.yaml`); `WebClient` and `HttpClient#send` are not built in
- command injection — `Runtime#exec`, `ProcessBuilder` (`generic/command-injection-sinks.yaml`)
- SQL — `Statement#execute*`, `JdbcTemplate`, an `EntityManager` native query (`spring/jdbc-sqli-sinks.yaml`)
- path traversal — `Files#*` reached through `Paths#get`/`Path#resolve` (`generic/path-traversal-sinks.yaml`)
- SSTI, expression, and code injection — the template engine's `process`/`merge` (`generic/template-injection-sinks.yaml`), `SpelExpressionParser` (`spring/spel-injection-sinks.yaml`), `generic/code-injection-sinks.yaml`
- deserialization — `ObjectMapper#readValue`, a SnakeYAML `load` (`generic/unsafe-deserialization-sinks.yaml`); `ObjectInputStream#readObject` is not built in
- log injection — the `Logger` call's message or argument (`generic/logging-sinks.yaml`)
- and their own files for XXE, LDAP, SMTP, reflection, unvalidated redirect, response splitting, and XSS response writes

Check the bundled set before proposing a sink boundary: it is broad enough that a family often needs only the source side. Prefer the library boundary over the project wrapper that calls it — a reusable library sink keeps the rule useful past this run.

### 5. Identify the precision controls

Java's validation impostors: `@Valid`/`@Validated` with Bean Validation constraints, `@NotNull`, `@Size`, or `@Pattern` on a shape that is not the invariant, and a `parse`/`valueOf` that only proves the value's type. Record them as not-security-relevant validators rather than sanitizers.

Real Java controls: `InetAddress#getByName` plus a private-range rejection for SSRF, `Path#normalize` plus a `startsWith` containment check for traversal, an owner-scoped repository lookup for IDOR, `MessageDigest#isEqual` or HMAC verification for callbacks, and a context-correct encoder or CR/LF stripping for output and log injection.

A restriction usually reads as `pattern-inside` on the enclosing annotated class or method — that is what keeps a universal accessor scoped to the endpoint that actually takes untrusted input.

### 6. Write the specification

`candidate_patterns` entries take `method` as `owner.Class#member` with `signature` its quoted JVM descriptor, so overloads stay distinct. An annotation-carried boundary takes the annotation's own FQN as `method` with `signature: null`, as the spec format shows. The dependency identity to record on the seeded units is the Maven GAV, `group:artifact:version`.

`create-rule`'s `references/java.md` holds the pattern shapes those units turn into.
