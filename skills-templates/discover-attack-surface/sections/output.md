Short and concise report of what was done

### Artifacts:

- `.opentaint/tracking/rules/sources/<package-kebab>.yaml` — the source unit(s), one per package the plan touched (none for a fully-covered package)
- `.opentaint/tracking/rules/plans/<id>.yaml` — your plan, with the sources recorded under `source`

### Summary:

- the sources found, one line each, and any package already fully covered
- anything blocked or left uncertain
