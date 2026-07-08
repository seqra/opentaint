# skills-new — templated source for the OpenTaint skills

The canonical `skills/` directory (the Claude-skills-standard layout consumed by the
agent) is **generated** from this folder. You edit structured sources here; a build step
renders them into a correct `skills/` tree. This makes it explicit *what changes where*:
section order/composition/titles live in `main.md.j2`, prose in `sections/*.md`, the YAML
header in `frontmatter.md`. There is **no separate manifest** — everything the build needs
is the folder itself plus `main.md.j2`, so nothing can drift out of sync with the template.

## Layout

```
skills-new/
  build.py            # renders every skill/main.md.j2 -> <out>/<skill>/SKILL.md (+ assets)
  migrate.py          # one-time: splits an existing skills/ tree into these sources
  <skill-name>/
    frontmatter.md    # the raw `--- ... ---` YAML header, kept verbatim
    main.md.j2        # THE main template — composes the sections below via {% include %}
    sections/
      preamble.md     # the `# Skill: <Title>` line + any intro before the first ## section
      input.md        # FIXED section: the dispatch contract (what the caller passes in)
      output.md       # FIXED section: the artifact/return contract (what the skill produces)
      workflow.md
      tracking.md
      gotchas.md ...
    references/       # (appsec-agent, create-test-project) copied verbatim into the output
    scripts/          # copied verbatim into the output
```

`input` and `output` are the **fixed contract sections**. A leaf skill has both; the
orchestrator (`appsec-agent`) has neither. The build derives this from the folder and fails
if a skill has exactly one of the pair — no `kind`/manifest field needed. Skill name = folder
name; `references/`/`scripts/` are copied when present.

## Commands

This is a normal uv project (`pyproject.toml` with `jinja2` + `pyyaml`). Run the scripts
inside it — `uv run` provisions the dependencies from `pyproject.toml`. Default paths are
resolved relative to this folder, so no path args are needed.

```bash
cd skills-new

# compile the sources into a standard skills tree (non-destructive default: skills-new/dist)
uv run build.py
# when ready to replace the real tree:
uv run build.py --out ../skills
```

(From the repo root instead: `uv run --project skills-new skills-new/build.py`.)

Jinja2 is used with **default delimiters** (`{{ }}`, `{% %}`); the current corpus contains
none of these, so markdown/code samples pass through untouched. If a section ever needs a
literal `{{`, wrap it in `{% raw %}...{% endraw %}`.
