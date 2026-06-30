# /// script
# requires-python = ">=3.9"
# dependencies = ["pyyaml==6.0.3"]
# ///
"""
Split method-classification work into per-agent plans (run with uv).
`analyze` writes one plan per dropped-method package, hard-capped at 20 methods (a bigger
package is split by sub-package/class), each method carrying its signature/factPositions
so the plan is self-contained. `discover` extracts project-used members of coverage.yaml's
pending packages and balances them into ~100-member plans. Already-classified items dropped.
"""
import argparse
import glob
import math
import re
import subprocess
import sys
from pathlib import Path

import yaml

ROOT = Path(".opentaint")
MODEL = Path(".opentaint/project")
ANALYZE_CAP = 20                          # hard cap: one package per plan, split a package past it
DISCOVER_TARGET, DISCOVER_BAND = 100, 25  # balanced merge across packages


def class_of(fqn):
    return fqn.split("#", 1)[0].strip()

def package_of(fqn):
    cls = class_of(fqn)
    return cls.rsplit(".", 1)[0] if "." in cls else ""

def in_packages(cls, prefixes):
    # dotted-boundary match: `a.b.collect` never matches a sibling `a.b.collectX`
    return any(cls == p or cls.startswith(p + ".") for p in prefixes)

def fqn_base(s):
    s = s.strip().strip('"').strip("'")
    i = s.find("(")
    return (s[:i] if i != -1 else s).strip()


def atomize(fqns, cap):
    # split into atomic scopes (prefix, [fqns]) each <= cap; a class over cap stays oversized
    scopes = []

    def recurse(prefix, items):
        if len(items) <= cap:
            scopes.append((prefix, items))
            return
        depth = len(prefix.split("."))
        buckets, leaf = {}, []
        for f in items:
            pkg = package_of(f)
            segs = pkg.split(".") if pkg else []
            if pkg == prefix or len(segs) <= depth:
                leaf.append(f)
            else:
                child = ".".join(segs[: depth + 1])
                buckets.setdefault(child, []).append(f)
        if leaf:
            if len(leaf) <= cap or not buckets and len({class_of(f) for f in leaf}) == 1:
                scopes.append((prefix, leaf))
            else:
                by_class = {}
                for f in leaf:
                    by_class.setdefault(class_of(f), []).append(f)
                for cls, cf in by_class.items():
                    scopes.append((cls, cf))
        for child, cf in buckets.items():
            recurse(child, cf)

    top = {}
    for f in fqns:
        pkg = package_of(f)
        top.setdefault(pkg.split(".")[0] if pkg else class_of(f), []).append(f)
    for seg0, items in top.items():
        recurse(seg0, items)
    return scopes


def pack(scopes, target, cap):
    # longest-processing-time: place largest scope into least-loaded plan, grow plan
    # count only until none exceeds cap; start target-centred so plans land near target
    items = sorted(scopes, key=lambda s: len(s[1]), reverse=True)
    if not items:
        return []
    total = sum(len(v) for _, v in items)
    k = max(1, math.ceil(total / cap), round(total / target))
    while True:
        loads = [0] * k
        bins = [{} for _ in range(k)]
        for prefix, v in items:
            i = min(range(k), key=lambda j: loads[j])
            bins[i][prefix] = v
            loads[i] += len(v)
        if max(loads) <= cap or k >= len(items):
            return [b for b in bins if b]
        k += 1


def write_plans(plans, out_dir, prefix_id):
    out_dir.mkdir(parents=True, exist_ok=True)
    paths = []
    for i, scopes in enumerate(plans, 1):
        pid = f"{prefix_id}-{i:03d}"
        norm = {p.replace(".", "-"): sorted(v, key=lambda x: x["method"] if isinstance(x, dict) else x)
                for p, v in sorted(scopes.items())}
        path = out_dir / f"{pid}.yaml"
        path.write_text(
            yaml.safe_dump({"id": pid, "scopes": norm}, sort_keys=False,
                           default_flow_style=False, allow_unicode=True),
            encoding="utf-8",
        )
        paths.append(str(path))
    return paths


def fqns_under_keys(path, keys):
    # every FQN held under any of `keys` (lists of FQN strings)
    doc = yaml.safe_load(Path(path).read_text(encoding="utf-8")) or {}
    out = set()
    for key in keys:
        for item in doc.get(key, []) or []:
            out.add(fqn_base(str(item)))
    return out


def collect_fqns(yaml_dir, keys):
    out = set()
    for p in sorted(glob.glob(str(yaml_dir / "*.yaml"))):
        out |= fqns_under_keys(p, keys)
    return out


def cmd_analyze(args):
    dropped = yaml.safe_load(
        (ROOT / "results" / "dropped-external-methods.yaml").read_text(encoding="utf-8")) or []
    classified = collect_fqns(ROOT / "tracking" / "approximations",
                              {"methods", "done", "engine_issues"})
    rows = []
    for e in dropped:
        if not (isinstance(e, dict) and e.get("method")):
            continue
        if fqn_base(e["method"]) in classified:
            continue
        row = {"method": e["method"]}
        if e.get("signature"):
            row["signature"] = e["signature"]
        if e.get("factPositions"):
            row["factPositions"] = e["factPositions"]
        rows.append(row)
    if not rows:
        print("nothing to plan — every dropped method already classified", file=sys.stderr)
        return 0
    cap = ANALYZE_CAP
    by_pkg = {}
    for r in rows:
        by_pkg.setdefault(package_of(r["method"]), []).append(r)
    plans = []                                   # one scope per plan — packages never merge
    for pkg, prows in by_pkg.items():
        methods = {r["method"] for r in prows}
        if len(methods) <= cap:
            plans.append({pkg: prows})
        else:                                    # split this package until each piece fits
            for scope, fqns in atomize(sorted(methods), cap):
                fset = set(fqns)
                plans.append({scope: [r for r in prows if r["method"] in fset]})
    for p in write_plans(plans, ROOT / "tracking" / "approximations" / "plans", "ext"):
        print(p)
    return 0


def yaml_list(model_yaml, key):
    # values of every `key` list in project.yaml, at any depth
    doc = yaml.safe_load(model_yaml.read_text(encoding="utf-8")) or {}
    vals = []

    def walk(node):
        if isinstance(node, dict):
            for k, v in node.items():
                if k == key and isinstance(v, list):
                    vals.extend(str(x) for x in v)
                else:
                    walk(v)
        elif isinstance(node, list):
            for x in node:
                walk(x)

    walk(doc)
    return vals


CALL_RE = re.compile(r"//\s*(?:Interface)?Method\s+(\S+?)\.(<?\w+>?):")


def extract_usages():
    # disassemble project classes, collect // Method / // InterfaceMethod call sites
    fqns = set()
    for entry in yaml_list(MODEL / "project.yaml", "moduleClasses"):
        p = MODEL / entry
        if p.is_dir():
            classes = [str(c.relative_to(p))[:-6].replace("/", ".")
                       for c in p.rglob("*.class")]
            cp = str(p)
        elif p.is_file():
            try:
                listing = subprocess.run(["jar", "tf", str(p)], capture_output=True,
                                         text=True, check=True).stdout
            except (OSError, subprocess.CalledProcessError):
                continue
            classes = [c[:-6].replace("/", ".") for c in listing.splitlines()
                       if c.endswith(".class")]
            cp = str(p)
        else:
            continue
        for i in range(0, len(classes), 200):           # batch to keep argv under the limit
            batch = classes[i:i + 200]
            try:
                out = subprocess.run(["javap", "-c", "-p", "-classpath", cp, *batch],
                                     capture_output=True, text=True).stdout
            except OSError:
                continue
            for owner, method in CALL_RE.findall(out):
                fqns.add(f"{owner.replace('/', '.')}#{method}")
    return fqns


def pending_packages():
    cov = yaml.safe_load((ROOT / "tracking" / "coverage.yaml").read_text(encoding="utf-8")) or {}
    return tuple(e["package"] for e in cov.get("packages", []) or []
                 if isinstance(e, dict) and e.get("status") == "pending" and e.get("package"))


def cmd_discover(args):
    packages = pending_packages()
    if not packages:
        print("nothing to plan — no pending package in coverage.yaml", file=sys.stderr)
        return 0
    used = {f for f in extract_usages() if in_packages(class_of(f), packages)}
    verdicted = collect_fqns(ROOT / "tracking" / "rules" / "plans", {"source", "safe"})
    todo = sorted({f for f in used if fqn_base(f) not in verdicted})
    if not todo:
        print("nothing to plan — every used member already verdicted", file=sys.stderr)
        return 0
    cap = DISCOVER_TARGET + DISCOVER_BAND
    plans = pack(atomize(todo, cap), DISCOVER_TARGET, cap)
    for p in write_plans(plans, ROOT / "tracking" / "rules" / "plans", "lib"):
        print(p)
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    a = sub.add_parser("analyze", help="partition dropped external methods, one plan per package")
    a.set_defaults(func=cmd_analyze)

    d = sub.add_parser("discover", help="partition coverage.yaml's pending packages' used members")
    d.set_defaults(func=cmd_discover)

    args = ap.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
