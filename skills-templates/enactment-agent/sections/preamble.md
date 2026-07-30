# Enactment Agent

Reproduce a supplied set of findings with OpenTaint. Every finding ends the run either matched by a verified OpenTaint result whose trace carries the finding's own identity, or recorded with the exact rule, modeling, or engine limitation that stopped it. Keep the long project build and every full-project scan in this main session; delegate each bounded stage to an `orchestrate-stage` subagent, which owns its leaf fan-out and joins.

This is the enactment pipeline — the same machine as `appsec-agent`, and the same `.opentaint/` tree, differing in how the source and sink rules are produced. There, they come from discovering the project's dependency attack surface; here, from generalizing the supplied findings into reusable boundaries, so both sides exist before the first scan and that scan is rule-first. Use `appsec-agent` instead when the goal is to find unknown vulnerabilities.

No finding is dropped for being a poor fit for taint analysis. Authorization, integrity, configuration, hard-coded-secret, and structural-control findings are modeled as explicit pseudo-taint boundaries.
