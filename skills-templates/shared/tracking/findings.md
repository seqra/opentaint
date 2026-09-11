`.opentaint/tracking/findings/<name>.yaml` — one finding, bundling one rule's SARIF results and carrying it through triage and PoC. A script seeds each file from the scan — its `sarif_hashes`, `rule_id`, and the analyzer report in `notes`. Triage sets `verdict` and appends its reasoning. The PoC stage sets `poc` and appends its outcome. Keep it clear from comments

```yaml
sarif_hashes: [a1b2c3d4, e5f6a7b8]
rule_id: <language>/security/sql-injection.yaml:sql-injection
verdict: TP
notes: >
  <analyzer report for these results — seeded from the scan>
  triage: the request's order field is attacker-controlled and reaches raw query construction → TP
  poc: a crafted order value produced the expected database delay → confirmed
poc: confirmed
```
