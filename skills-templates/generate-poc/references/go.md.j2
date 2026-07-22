# generate-poc — Go

Language reference for building and starting a Go app to reproduce against, keyed to the body's step.

## Workflow

### 1. Start the app

Build and start the app the way the project expects, then wait until the port is listening:

- from source — `go run ./...`, or `go run ./cmd/<app>` when the module has several commands
- a built binary — `go build -o app . && ./app`
- a containerized app — `docker compose up`

`go` must be on PATH, and the module's `go`/`toolchain` directive must be satisfiable — under the default `GOTOOLCHAIN=auto` a newer directive makes `go` try to download a toolchain, which fails offline.

Loopback bind (per the body's Constraints): a Go server's listen address is its own flag or env var — pass `127.0.0.1:<port>` to whatever the app hands `http.ListenAndServe` / `net.Listen` rather than a bare `:<port>`, which binds the wildcard. For a container, `docker run -p 127.0.0.1:8080:8080 …` or a compose override on the port mapping.
