Short and concise report of what was done

### Artifacts:

- `.opentaint/project/` — the opentaint project model

### Summary:

- model path and (for a multi-module project) the module count it covers
- the language-specific build fields defined by the selected reference, with the values used by the successful build
- how the model was built (autobuilder or manual), and any build config the skill changed to make it build (e.g. re-enabled modules)
- exact build command and arguments if `opentaint project` was used
- if the build did not converge: that it is left pending, with the blocking error and your fix attempts
