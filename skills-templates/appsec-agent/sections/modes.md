### What each mode takes in

- **onboarding** — no input beyond the project itself. The frontier sweep flags the dependencies that can carry untrusted data, partitions the members the project actually calls, and verdicts each one: a trust boundary, an effect, or neither. It is the widest intake there is, and its output — a classified frontier, universal rules for the stack, and the models behind them — is what makes every later pass cheap
- **discovery** — a diff, a spec, a ticket, or a sentence about what the project does and what would be bad. Ask for whatever the user has and record its path; with nothing supplied the scope is the whole project. Intake reads it, resolves it to code, and groups that code into families
- **enactment** — the supplied findings, as a manifest, SARIF, scanner report, or a directory of finding documents. Ask for the path when it isn't given. If the user only described the findings in conversation, write them to a file first and use that; the pipeline resumes from disk, not from this thread

### Onboarding runs once

The frontier sweep is the expensive pass, and its corpus is durable: the classification ledger, the universal rules, and the models stay on disk and apply to every scan afterwards, whichever mode ran it. So onboard a project once and then work in discovery or enactment. Bootstrap refuses a second onboarding pass over a tree that already had one and says so; a genuinely new dependency stack is a new tree.

### The modes compose

They are not alternatives, and picking one is not a commitment. One `.opentaint/` tree accumulates the artifacts of every pass over it, in any order and as many times as the project needs:

- **onboarding, then anything** — the natural start. A discovery or enactment pass over an onboarded tree finds most of its boundaries already ruled and modeled, and spends its work on what its own input names
- **enactment, then discovery** — reproduce the supplied report first, then hunt with the rules it produced. Boundaries derived from real findings are exactly the ones a discovery pass would otherwise have to argue for
- **discovery, then enactment** — assess the project, then measure a report against the corpus that pass built. What the report names but the scan missed is now a rule or modeling gap you can point at
- **any of them, again on a later commit** — the tree is long-lived. A new HEAD makes the model stale, so the pass rebuilds and rescans, and every rule, model, and verdict carries over. That's how a run becomes a regression check rather than a one-off

So `mode` in `state.yaml` is the intake of the *current pass*, not a property of the tree. Switching it is normal, needs no fresh tree, and strands nothing.

### Read what the tree already holds

If `.opentaint/tracking/state.yaml` exists, find out where the project stands before choosing:

```bash
uv run <skill-dir>/scripts/get_status.py --full
```

Its header prints the current `mode`, the run's levels, the tracked finding set or spec if there is one, and — once the tree has more than one pass — the `passes:` chain. The phase lines say whether that pass is finished or mid-flight.

- mid-flight pass — resume it rather than starting a different one over the top of it
- finished pass, and the user wants more — that's a new pass, and the choice below applies again
- tell the user what's there either way, in one line: which pass, where it stands, what carried over

### Choose this pass

Decide from what the user brought, then confirm it with them before bootstrapping:

- **enactment** — they supplied findings and want them reproduced, validated, converted into reusable rules, or cross-checked against OpenTaint. "Does OpenTaint catch these?", "reproduce this report", "turn these findings into rules"
- **discovery** — no finding set to measure against; the goal is what the project is vulnerable to, in the whole project or in what a diff or spec names. "Find vulnerabilities", "scan this app", "did this PR introduce anything?"
- **onboarding** — the tree has never been onboarded and the user wants the project's own rule and model corpus built before anything is measured. Recommend it on a cold start when the run is not urgent; it is the pass that makes the others accurate

The signal for enactment is whether a finding set exists to be measured against, not the vocabulary. A user who says "audit this against last year's pentest" and has the pentest is enactment; a user who says "reproduce the bug I think is in here" and has only a hunch is discovery.

When the user wants both — reproduce the report *and* find what it missed — say that it is two passes over one tree, recommend enactment first so the discovery pass inherits its boundaries, and run them one at a time. Never try to drive two modes in a single pass.
