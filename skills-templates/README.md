# skills-new — templated source for the OpenTaint skills

Structured source for the OpenTaint skills: each skill is a `main.md.j2` plus `sections/*.md` (and optional `references/`, `scripts/`), compiled into the standard `skills/` tree consumed by the agent. Authoring and section rules live in `FRAMEWORK.md`.

Build (a uv project — `uv run` provisions deps):

```bash
cd skills-new
uv run build.py               # -> skills-new/dist (non-destructive default)
uv run build.py --out ../skills   # replace the real tree
```
