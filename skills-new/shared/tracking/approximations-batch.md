`.opentaint/tracking/approximations/<batch>.yaml` — one batch's method classification, `<batch>` the plan's filename stem. Every method sits in exactly one verdict bucket, keyed with its `signature` (the JVM descriptor, always quoted so array types `[…` stay valid YAML) so overloads stay distinct:
- `passthrough`, `dataflow` — modeled carriers; each entry `{ method, signature }`
- `skipped` — non-carriers; each `{ method, signature, reason }`
- `engine_issues` — carriers the engine can't model; each `{ method, signature, reason }`

`dependencies` lists the dependency identifiers a dataflow test project needs. The `build` block tracks the build — `test_project` records each dataflow method's test-project status (`done` if a sample was written into the batch's test project, `failed` if none could be written so the method was excluded from it), and `done` holds the finished `{ method, signature }`. Keep it clear from comments

```yaml
passthrough:
  - { method: "com.foo.Wrapper#getValue", signature: "()Ljava/lang/String;" }
dataflow:
  - { method: "com.foo.Reactor#flatMap", signature: "(Ljava/util/function/Function;)Lcom/foo/Reactor;" }
skipped:
  - { method: "org.slf4j.Logger#info", signature: "(Ljava/lang/String;)V", reason: "void side-effect" }
engine_issues: []
dependencies: []
build:
  test_project:
    - { method: "com.foo.Reactor#flatMap", signature: "(Ljava/util/function/Function;)Lcom/foo/Reactor;", status: done }
  done: []
```
