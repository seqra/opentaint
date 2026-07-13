`.opentaint/tracking/poc-servers.yaml` — the registry of app instances started for PoCs, read by the orchestrator to tear them down. One entry per instance: `kind` (`process | container | compose`), `port`, and the matching `ref` (a pid, a container id/name, or a compose file path) that gives the stop command. PoCs run one at a time, so appends never race. Keep it clear from comments

```yaml
servers:
  - kind: process
    port: 8080
    ref: "12345"
```
