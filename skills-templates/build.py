"""
Compile the skills-new/ structured sources into a standard skills/ tree.
Run inside this uv project: `cd skills-new && uv run build.py` (or `uv run --project skills-new skills-new/build.py`).
"""
import argparse
import shutil
import sys
from pathlib import Path

from jinja2 import Environment, FileSystemLoader, StrictUndefined


def load_config(src_root):
    # config.yaml holds only flat scalar variables (currently just `version`), so a tiny
    # `key: value` reader keeps the build dependency-free — no yaml parser needed.
    cfg = {}
    path = src_root / "config.yaml"
    if path.is_file():
        for line in path.read_text(encoding="utf-8").splitlines():
            line = line.split("#", 1)[0].strip()
            if not line or ":" not in line:
                continue
            key, val = line.split(":", 1)
            cfg[key.strip()] = val.strip().strip('"').strip("'")
    return cfg


def build_skill(skill_dir, src_root, out_root, context):
    name = skill_dir.name

    # Contract check, derived from the folder — no manifest. A leaf skill is defined by having
    # both fixed contract sections; the orchestrator has neither. Having exactly one is the bug.
    has_in = (skill_dir / "sections" / "input.md").is_file()
    has_out = (skill_dir / "sections" / "output.md").is_file()
    if has_in != has_out:
        missing = "output" if has_in else "input"
        raise SystemExit(f"[{name}] has one of the fixed contract sections but not the other "
                         f"— missing sections/{missing}.md")

    env = Environment(
        loader=FileSystemLoader([str(skill_dir), str(src_root)]),
        keep_trailing_newline=True,
        trim_blocks=True,
        undefined=StrictUndefined,
        autoescape=False,
    )
    rendered = env.get_template("main.md.j2").render(**context)

    out = out_root / name
    out.mkdir(parents=True, exist_ok=True)
    (out / "SKILL.md").write_text(rendered, encoding="utf-8")

    # scripts: copied verbatim (run by the agent as-is).
    copy_verbatim(skill_dir / "scripts", out / "scripts")

    # references: render *.md.j2 -> *.md (so a reference can pull shared/ partials and version),
    # copy everything else verbatim.
    render_references(skill_dir, out / "references", env, context)
    return name


def copy_verbatim(src, dst):
    if dst.exists():
        shutil.rmtree(dst)
    if src.is_dir():
        shutil.copytree(src, dst, ignore=shutil.ignore_patterns("__pycache__"))


def render_references(skill_dir, dst, env, context):
    src = skill_dir / "references"
    if dst.exists():
        shutil.rmtree(dst)
    if not src.is_dir():
        return
    dst.mkdir(parents=True, exist_ok=True)
    for f in sorted(src.rglob("*")):
        if "__pycache__" in f.parts:
            continue
        rel = f.relative_to(src)
        if f.is_dir():
            (dst / rel).mkdir(parents=True, exist_ok=True)
        elif f.suffix == ".j2":
            target = (dst / rel).with_suffix("")
            target.parent.mkdir(parents=True, exist_ok=True)
            tmpl = env.get_template(f"references/{rel.as_posix()}")
            target.write_text(tmpl.render(**context), encoding="utf-8")
        else:
            (dst / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(f, dst / rel)


def main():
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--src", default=str(here), help="structured sources root")
    ap.add_argument("--out", default=str(here / "dist"), help="output skills tree")
    args = ap.parse_args()

    src_root = Path(args.src)
    out_root = Path(args.out)
    context = load_config(src_root)
    skills = sorted(p.parent for p in src_root.glob("*/main.md.j2"))
    if not skills:
        print(f"no <skill>/main.md.j2 under {src_root}", file=sys.stderr)
        return 2
    for sk in skills:
        print(build_skill(sk, src_root, out_root, context))
    print(f"\nbuilt {len(skills)} skills into {out_root}/")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
