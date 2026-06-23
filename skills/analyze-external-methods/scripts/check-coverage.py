#!/usr/bin/env python3
"""
check-coverage.py — report dropped methods not yet classified.

UNCOVERED = dropped - methods: - done: - skipped, FQN-level (a `(params)`
overload suffix is stripped on both sides). Zero args, run from the project root:
reads .opentaint/results/dropped-external-methods.yaml and every *.yaml under
.opentaint/tracking/approximations/. Exit 1 if any UNCOVERED, 0 if none, 2 if the
dropped file is missing.
"""
import glob
import re
import sys
from pathlib import Path

DROPPED = ".opentaint/results/dropped-external-methods.yaml"
APPROX_DIR = ".opentaint/tracking/approximations"

# a dropped entry's identity line: `- method: "FQN"` (quotes optional)
METHOD_RE = re.compile(r'^\s*-?\s*method:\s*"?([^"\n]+?)"?\s*$')
# a top-level key at column 0 (resets the section); captures any inline value
KEY_RE = re.compile(r'^([A-Za-z_][\w-]*):\s*(.*)$')
# a block list item under a key: `  - "FQN"`, `  - FQN`, or legacy `  - target: "FQN"`
ITEM_RE = re.compile(r'^\s*-\s*(?:target:\s*)?"?([^"\n]+?)"?\s*$')
# items inside an inline list: methods: ["a", "b"]
INLINE_RE = re.compile(r'"?([^",\[\]]+?)"?(?:,|$)')


def fqn(s):
    """Bare FQN: drop quotes, whitespace, and any (params) overload suffix."""
    s = s.strip().strip('"').strip("'")
    i = s.find("(")
    if i != -1:
        s = s[:i]
    return s.strip()


def dropped_methods(path):
    out = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        m = METHOD_RE.match(line)
        if m:
            out.add(fqn(m.group(1)))
    return out


CLASSIFIED_KEYS = {"methods", "done"}


def classified_methods(approx_dir):
    """Every FQN under a `methods:` or `done:` key across all files — units'
    pending and built methods, plus skipped.yaml's skips (its skips live under
    `methods:`)."""
    out = set()
    for p in sorted(glob.glob(str(approx_dir / "*.yaml"))):
        section = None
        for line in Path(p).read_text(encoding="utf-8").splitlines():
            key = KEY_RE.match(line)
            if key:
                section, inline = key.group(1), key.group(2).strip()
                if section in CLASSIFIED_KEYS and inline.startswith("["):
                    out.update(fqn(x) for x in INLINE_RE.findall(inline[1:-1]) if x.strip())
                continue
            if section in CLASSIFIED_KEYS:
                item = ITEM_RE.match(line)
                if item:
                    out.add(fqn(item.group(1)))
    return out


def main():
    dropped_path = Path(DROPPED)
    if not dropped_path.is_file():
        print(f"no dropped file at {DROPPED} — nothing to check")
        return 2

    dropped = dropped_methods(dropped_path)
    classified = classified_methods(Path(APPROX_DIR))
    uncovered = sorted(dropped - classified)

    covered = len(dropped) - len(uncovered)
    print(f"coverage: {covered}/{len(dropped)} dropped methods classified, "
          f"{len(uncovered)} UNCOVERED")
    if uncovered:
        print("\nUNCOVERED — classify each (model or skip) before the phase is done:")
        for m in uncovered:
            print(f"  {m}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
