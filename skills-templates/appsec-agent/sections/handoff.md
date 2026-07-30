Load the chosen skill in this same session and follow it from its setup:

```
assessment → assessment-agent
enactment  → enactment-agent
```

Not a subagent. MAIN must own the long build and every full-project scan, so the pipeline continues as this session, with the choice above already settled and the toolchain and nesting checks already done. It runs the rest of its own setup — language, levels, bootstrap — and everything after that is its document, not this one.

Tell the user which pipeline you picked and why, in one line, before you hand off.
