# /// script
# requires-python = ">=3.9"
# dependencies = ["pyyaml==6.0.3"]
# ///
"""
Split method-classification work into per-agent plans (run with uv).
`analyze` groups the dropped methods by library root, packs each root into batches of
~20 methods (a root over budget is split, never mixed with another root; roots with few
methods are pooled into one `misc` batch), and writes one self-contained plan per batch.
`discover` extracts project-used members of coverage.yaml's pending packages and balances
them into ~50-member plans. Members already verdicted in rules/classification.yaml dropped.
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
ANALYZE_BUDGET = 20                       # methods per batch; a single class over it stays oversized
ANALYZE_MISC = 6                          # roots with <= this many methods are pooled into one misc batch
ROOT_DEPTH = 2                            # library root = first 2 dotted segments
DISCOVER_TARGET, DISCOVER_BAND = 50, 15   # project-used members per discover plan (~50, loose)


def class_of(fqn):
    return fqn.split("#", 1)[0].strip()

def package_of(fqn):
    cls = class_of(fqn)
    return cls.rsplit(".", 1)[0] if "." in cls else ""

def root_of(fqn, depth=ROOT_DEPTH):
    segs = class_of(fqn).split(".")
    return ".".join(segs[:depth]) if len(segs) >= depth else class_of(fqn)

def in_packages(cls, prefixes):
    # dotted-boundary match: `a.b.collect` never matches a sibling `a.b.collectX`
    return any(cls == p or cls.startswith(p + ".") for p in prefixes)

def fqn_base(s):
    s = str(s).strip().strip('"').strip("'")
    i = s.find("(")
    return (s[:i] if i != -1 else s).strip()


def atomize(fqns, cap):
    # split into atomic scopes (prefix, [fqns]); each scope is a whole (sub)package (or a subtree
    # under cap) — a package is NEVER split across scopes, so it lands in exactly one bin and no two
    # agents ever share a package's per-package unit (source/sink). A package over cap stays oversized.
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
            # the methods sitting directly in `prefix` are one whole package — keep them together
            # whatever the size (an oversized package becomes its own bin in pack), never class-split
            scopes.append((prefix, leaf))
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
    # longest-processing-time bin-packing. An atomic scope larger than cap (a package that can't
    # be split) gets its own bin instead of forcing the whole set to one-scope-per-bin.
    plans = [{p: v} for p, v in scopes if len(v) > cap]
    items = sorted((s for s in scopes if len(s[1]) <= cap), key=lambda s: len(s[1]), reverse=True)
    if items:
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
                break
            k += 1
        plans += [b for b in bins if b]
    return plans


def write_plans(plans, out_dir, prefix_id):
    out_dir.mkdir(parents=True, exist_ok=True)
    paths = []
    for i, scopes in enumerate(plans, 1):
        pid = f"{prefix_id}-{i:03d}"
        norm = {p.replace(".", "-"): sorted(v, key=lambda x: x["method"] if isinstance(x, dict) else x)
                for p, v in sorted(scopes.items())}
        path = out_dir / f"{pid}.yaml"
        path.write_text(
            yaml.safe_dump({"scopes": norm}, sort_keys=False,
                           default_flow_style=False, allow_unicode=True),
            encoding="utf-8",
        )
        paths.append(str(path))
    return paths


def ledger_verdicted():
    # FQNs already verdicted in the durable rules ledger (source ∪ safe), skipped next run
    p = ROOT / "tracking" / "rules" / "classification.yaml"
    if not p.is_file():
        return set()
    doc = yaml.safe_load(p.read_text(encoding="utf-8")) or {}
    return {fqn_base(x) for key in ("source", "safe") for x in (doc.get(key) or [])}


# a method counts as classified once it sits in any batch file's classification bucket
# (passthrough/dataflow/skipped), in build.done, or in skipped.yaml (methods/engine_issues)
CLASSIFIED_KEYS = ("passthrough", "dataflow", "skipped", "methods", "engine_issues")


def classified_methods():
    out = set()
    for p in sorted(glob.glob(str(ROOT / "tracking" / "approximations" / "*.yaml"))):
        doc = yaml.safe_load(Path(p).read_text(encoding="utf-8")) or {}
        for key in CLASSIFIED_KEYS:
            for item in doc.get(key, []) or []:
                out.add(fqn_base(item["method"] if isinstance(item, dict) else item))
        for item in (doc.get("build") or {}).get("done", []) or []:
            out.add(fqn_base(item["method"] if isinstance(item, dict) else item))
    return out


def cmd_analyze(args):
    dropped = yaml.safe_load(
        (ROOT / "results" / "dropped-external-methods.yaml").read_text(encoding="utf-8")) or []
    classified = classified_methods()
    rows = []
    for e in dropped:
        if not (isinstance(e, dict) and e.get("method")):
            continue
        if fqn_base(e["method"]) in classified:
            continue
        row = {"method": e["method"]}
        if e.get("signature"):
            row["signature"] = e["signature"]
        rows.append(row)
    if not rows:
        print("nothing to plan — every dropped method already classified", file=sys.stderr)
        return 0

    # group by library root, pooling roots with few methods into one "misc" batch
    by_root = {}
    for r in rows:
        by_root.setdefault(root_of(r["method"]), []).append(r)
    count = lambda rs: len({fqn_base(r["method"]) for r in rs})
    misc = []
    for root in [k for k, rs in by_root.items() if count(rs) <= ANALYZE_MISC]:
        misc += by_root.pop(root)
    if misc:
        by_root["misc"] = misc

    out_dir = ROOT / "tracking" / "approximations" / "plans"
    out_dir.mkdir(parents=True, exist_ok=True)
    paths = []
    for root in sorted(by_root):
        by_fqn = {}
        for r in by_root[root]:
            by_fqn.setdefault(fqn_base(r["method"]), []).append(r)
        bins = pack(atomize(sorted(by_fqn), ANALYZE_BUDGET), ANALYZE_BUDGET, ANALYZE_BUDGET)
        for i, b in enumerate(bins, 1):
            scopes = {}
            for f in {f for v in b.values() for f in v}:           # re-group the batch by class
                scopes.setdefault(class_of(f), []).extend(by_fqn[f])
            norm = {cls: sorted(v, key=lambda x: (x["method"], x.get("signature", "")))
                    for cls, v in sorted(scopes.items())}
            pid = f"{root.replace('.', '-')}-{i:03d}"
            path = out_dir / f"{pid}.yaml"
            path.write_text(
                yaml.safe_dump({"scopes": norm}, sort_keys=False,
                               default_flow_style=False, allow_unicode=True),
                encoding="utf-8",
            )
            paths.append(str(path))
    for p in paths:
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
    # coverage.yaml is a flat flag-list of packages triage flagged to drill; a package is done
    # implicitly once all its used members are verdicted (ledger_verdicted), so all listed are candidates
    cov = yaml.safe_load((ROOT / "tracking" / "coverage.yaml").read_text(encoding="utf-8")) or {}
    return tuple(p for p in (cov.get("packages") or []) if isinstance(p, str) and p)


def cmd_discover(args):
    packages = pending_packages()
    if not packages:
        print("nothing to plan — no pending package in coverage.yaml", file=sys.stderr)
        return 0
    used = {f for f in extract_usages() if in_packages(class_of(f), packages)}
    verdicted = ledger_verdicted()
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

    a = sub.add_parser("analyze", help="partition dropped external methods into per-root batches")
    a.set_defaults(func=cmd_analyze)

    d = sub.add_parser("discover", help="partition coverage.yaml's pending packages' used members")
    d.set_defaults(func=cmd_discover)

    args = ap.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
