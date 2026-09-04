# Configuration

OpenTaint can be configured through a configuration file or environment variables. Command-line flags always take precedence over configuration file settings and environment variables.

## Configuration File

Create a YAML configuration file and specify it with the `--config` flag:

```bash
opentaint scan --config /path/to/config.yaml /path/to/project
```

### Example Configuration

```yaml
# Scan settings
scan:
  timeout: 15m
  max_memory: 16G
  baseline: baselines/main.sarif

# Output (terminal-side controls)
output:
  debug: false   # true streams JAR output to stderr and shows debug-only fields
  color: auto    # auto, always, never
  quiet: false   # suppress spinners, progress bars, JAR streaming

# Java runtime settings
java:
  version: 23

# Which rules the analyzer runs
rules:
  only: []                                  # if set, only these rules run
  exclude: [cookie-missing-httponly]                # these rules never run
```

### Available Options

| Setting | Description | Default |
|---------|-------------|---------|
| `scan.timeout` | Analysis timeout duration | `15m` |
| `scan.max_memory` | Maximum memory for analyzer (e.g., `8G`, `1024m`) | `8G` |
| `scan.baseline` | Previous SARIF report used for comparison and suppression inheritance; relative paths resolve from the config file | none |
| `output.debug` | Enable debug output (stream JAR subprocess output, show debug fields) | `false` |
| `output.color` | Color mode: `auto`, `always`, `never` | `auto` |
| `output.quiet` | Suppress interactive console output (spinners, progress bars, JAR streaming) | `false` |
| `java.version` | Java version for running the analyzer | `23` |
| `rules.only` | Run only the rules matching these patterns | all rules |
| `rules.exclude` | Never run the rules matching these patterns | none |

### Selecting rules

`rules.only` and `rules.exclude` control which rules the analyzer loads. They
are rule *selection*, not suppression: an excluded rule never runs, so it
produces nothing in the report and nothing to review later. To hide a finding a
rule did produce, accept it with `opentaint triage` instead.

Each entry matches a full `path/to/file.yaml:rule-id` exactly, a bare rule name
exactly, or a doublestar glob over the full id — the same grammar as the
summary command's `--rule-id` filter. Globs never match the bare name alone:

```yaml
rules:
  only:
    - sql-injection                        # exact rule name
    - java/security/**                     # every rule under that directory
    - java/security/sqli.yaml:*            # every rule in that file
  exclude:
    - cookie-missing-httponly
```

A pattern that matches no rule in the active ruleset produces a warning, so a
typo'd exclusion cannot silently look effective.

`exclude` is applied after `only`. An exclusion-only list is passed to the
analyzer as the excluded rule ids themselves — excluding one rule adds one
argument, not the whole ruleset's complement. A library rule that a selected
rule joins against always keeps working, even if a pattern excluded it, since
dropping it would leave a rule that can never match. A selection that ends up
matching no rules is an error rather than a scan that silently checks
nothing — `--dry-run` reports it without compiling.

The `--rule-id` flag overrides both lists, and the `--exclude-rule-id` flag
overrides `rules.exclude`, following the usual rule that flags outrank the
configuration file. The two flags compose: `--rule-id` selects, then
`--exclude-rule-id` subtracts.

The per-run log file (`~/.opentaint/logs/<project>/<timestamp>.log`) always
captures full JAR subprocess output regardless of these flags. They control
only what is shown on the terminal.

## Environment Variables

All configuration options can also be set via environment variables with the `OPENTAINT_` prefix. Use underscores to separate nested keys:

```bash
export OPENTAINT_SCAN_TIMEOUT=30m
export OPENTAINT_SCAN_MAX_MEMORY=16G
export OPENTAINT_OUTPUT_DEBUG=true
export OPENTAINT_OUTPUT_COLOR=always
export OPENTAINT_OUTPUT_QUIET=false
export OPENTAINT_JAVA_VERSION=23

opentaint scan /path/to/project
```

## Priority Order

Configuration values are resolved in this order (highest to lowest priority):

1. Command-line flags
2. Environment variables
3. Configuration file
4. Default values

## Persistent Configuration

For persistent settings, create a configuration file at `~/.opentaint/config.yaml`:

```yaml
scan:
  max_memory: 16G
  timeout: 20m
```

Then use it with every scan:

```bash
opentaint scan --config ~/.opentaint/config.yaml /path/to/project
```
