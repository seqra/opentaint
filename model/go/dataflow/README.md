# Built-in Go models

These Go models describe how taint moves through functions that the analyzer cannot inspect.
Each directory is an independent Go module. Each module has its own pinned dependencies.
A model can import the library that it models. Modules that need different versions of one
library do not share a module graph, so use one module for each dependency version line.

| Module   | Models                                | Pins                             |
|----------|---------------------------------------|----------------------------------|
| `modelcontextprotocol-go-sdk-v1` | MCP Go SDK server callbacks: tool, prompt, resource, middleware, server option and HTTP server factory handlers | `github.com/modelcontextprotocol/go-sdk` v1.7.0 |
| `github-mcp-server` | GitHub MCP server tool handlers registered with `inventory.NewServerToolWithContextHandler` | `github.com/modelcontextprotocol/go-sdk` v1.7.0 |

The build copies these modules to `model/go/dataflow/` in the analyzer JAR. The analysis
loader extracts them and loads every module that has a `go.mod` file. A model package applies
only when its target package is present in the analyzed project.

## Adding a module

1. Create a directory for the library, such as `gin-v1` or `grpc-go`. Add a `go.mod`:

   ```text
   module opentaint

   go 1.25.0

   require github.com/gin-gonic/gin v1.10.0
   ```

   The module name must be `opentaint`. Pin exact dependency versions. A model can also
   import the analyzed project's packages and their dependencies.

2. Put each model under `<target-import-path>/`. Use the target package name in the package
   clause. For example, `github.com/modelcontextprotocol/go-sdk/mcp/` models
   `github.com/modelcontextprotocol/go-sdk/mcp`. Each target package can have only one model
   across all modules. A duplicate model makes the analysis fail when it loads the models.

You do not need to edit a build file. The `go-config` build copies `model/go` into the
analyzer JAR, and the loader finds each directory that has a `go.mod` file.

## Writing a model

Use the same form for built-in and custom models. See
`skills/create-dataflow-model` for the full instructions. Use the `opentaint/`
prefix to address the target package. Keep each modeled function's exact name, receiver and
signature. Use target types through their original imports. Declare a partial target struct
when Go needs a local type, for example for a method receiver. List only the fields that the
model uses. Do not use an empty body.

OpenTaint analyzes model bodies. It does not run them. It does not use model `init`
functions.

A model replaces the body of the function. Pass-through rules in `../config` apply only to
calls without a body. Use both forms together when a flow enters a stored callback and then
passes through an operation of a library value. The MCP models call each stored handler with
a request value that marks the MCP request and the generic tool input as external input.
