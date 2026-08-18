`.opentaint/tracking/scope.yaml` — what this pass's intake scoped, and the families the boundaries stage generalizes one at a time. `scope` is one line on what the pass was given, so a later reader knows what the family list came from. Each family carries the `evidence` it was grouped from: the frontier members a sweep verdicted, or the members, endpoints, and code areas a diff or spec resolved to. Enactment mode writes no scope file — its families live on the reference findings, which carry the same assignment on the file that moves with them. Keep it clear from comments

```yaml
mode: discovery
scope: docs/2026-07-webhooks.md — partner webhook registration and delivery
families:
  - name: ssrf-webhook
    evidence:
      - com.acme.webhook.WebhookController#register
      - com.acme.webhook.WebhookService#dispatch
  - name: upload-path
    evidence:
      - com.acme.upload.UploadController#store
```
