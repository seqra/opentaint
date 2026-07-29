### 1. List the dependencies

Read `.opentaint/project/project.yaml` — the `dependencies:` list under each per-language projects entry (e.g. `javaProjects:`) is every third-party dependency the model resolved. Resolve each to the library it is. Most of a large project's dependencies are transitive infrastructure

A `goProjects:` entry carries no such list — read the module's own `go.mod` (`require` blocks) and `go.sum` for its dependency modules instead, and identify each by module path rather than by a coordinate

### 2. Mark each library

For each library decide: could it introduce an attacker-controlled source — a method returning untrusted data (HTTP/RPC request data, message-broker payloads, deserialized untrusted input and so on)? Judge by the library's identity itself, read sources to get overviews, docs

Dismiss the obvious infrastructure by identity — logging (logback/slf4j; Go `go.uber.org/zap`, `log/slog`), build plugins, annotations, bytecode tooling (ASM, byte-buddy) or codegen runtimes (`google.golang.org/protobuf`), test libraries (Go `github.com/stretchr/testify`), pure data structures. When unsure, peek: grep the project's sources for the library's imports or call sites — for Go that grep on the import path is the only peek available, there is no jar to inspect

### 3. Write the flag list

Write in `.opentaint/tracking/coverage.yaml` (per Tracking) a flat list of the flagged libraries' packages

When `coverage.yaml` already exists from a prior run, reconcile rather than overwrite: keep every listed package and add any dependency newly added to the model that could introduce a source. A flagged package whose usage shifted (new call sites, a version bump) needs no re-open — source discovery automatically plans any used member not yet verdicted. When unsure whether a package belongs, list it: an over-flag only costs one discovery pass, a missed library loses its sources on every later stage

### 4. Verify before returning

Re-check the full dependency list against your flags: confirm every dependency was judged, then re-read the ones you did NOT flag and make sure none of them can actually introduce a source. A library left out here loses its sources on every later stage and the run can't recover it. Add any package you missed to the list. This is a re-read of what you already wrote — simple grep or re-read is fine, no need to use some scripts.
