### Artifacts

- `.opentaint/pocs/<name>.py` — the PoC script, kept whether it confirmed or not
- `.opentaint/tracking/findings/<name>.yaml` — the finding's `poc` and `notes` updated (per Tracking)
- `.opentaint/tracking/poc-servers.yaml` — the started instance registered, left running for reuse (per Tracking)

### Summary

- the outcome (confirmed / failed) and, if failed, that the finding is unconfirmed; the base URL when you started an instance
