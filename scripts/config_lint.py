#!/usr/bin/env python3
"""Structural lint for the Java passThrough config (model/java/config).

Invariants (see docs/superpowers/specs/2026-07-23-rule-storage-rekey-design.md):
  I1 no class has a slot written by one property and read by a different one
  I2 every named slot has at least one writer and one reader
  I3 every array param feeding a scalar target has an explicit [*] edge
  I4 no [*] on a non-array-typed position
  I5 no out-of-range arg(n)
  I6 no <rule-storage> anywhere in the Java config (final gate)
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from typing import NamedTuple, Optional

import yaml


class Copy(NamedTuple):
    frm: tuple
    to: tuple


class Entry(NamedTuple):
    file: str
    func: object
    sig: object
    copies: list


class Finding(NamedTuple):
    code: str
    file: str
    func: str
    detail: str


def _pos(v) -> tuple:
    return tuple(v) if isinstance(v, list) else (v,)


def func_name(func) -> str:
    return func if isinstance(func, str) else json.dumps(func, sort_keys=True)


def load_entries(root: str) -> list:
    entries = []
    for dirpath, _, files in os.walk(root):
        for name in sorted(files):
            if not name.endswith((".yaml", ".yml")):
                continue
            path = os.path.join(dirpath, name)
            with open(path) as fh:
                doc = yaml.safe_load(fh)
            if not isinstance(doc, dict):
                continue
            rel = os.path.relpath(path, root)
            for raw in doc.get("passThrough") or []:
                copies = [Copy(_pos(c["from"]), _pos(c["to"])) for c in raw.get("copy") or []]
                entries.append(Entry(rel, raw.get("function"), raw.get("signature"), copies))
    return entries


def _git(args, cwd) -> str:
    """Run a git command, returning stdout; raises RuntimeError with stderr on failure."""
    proc = subprocess.run(["git", *args], cwd=cwd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or proc.stdout).strip() or f"git {' '.join(args)} failed")
    return proc.stdout


def load_entries_at_ref(ref: str, root: str) -> list:
    """Same entries as load_entries(root), read from git ref <ref> instead of the
    working tree. `root` must live inside a git working tree; touches neither the
    working tree, the index, nor HEAD. Raises RuntimeError if `ref` (or a path
    under `root`) cannot be resolved."""
    top = _git(["rev-parse", "--show-toplevel"], root).strip()
    rel_root = os.path.relpath(os.path.abspath(root), top)
    rel_root = "" if rel_root == "." else rel_root

    ls_args = ["ls-tree", "-r", "--name-only", ref]
    if rel_root:
        ls_args += ["--", rel_root]
    paths = [p for p in _git(ls_args, top).splitlines() if p.endswith((".yaml", ".yml"))]

    tmpdir = tempfile.mkdtemp(prefix="config_lint_ref_")
    try:
        for path in paths:
            content = _git(["show", f"{ref}:{path}"], top)
            dest_rel = os.path.relpath(path, rel_root) if rel_root else path
            dest = os.path.join(tmpdir, dest_rel)
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            with open(dest, "w") as fh:
                fh.write(content)
        return load_entries(tmpdir)
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


def arity(sig) -> Optional[int]:
    """Number of declared parameters, or None when unknown/wildcarded."""
    if isinstance(sig, dict):
        # A dict signature constrains selected positions; it does not declare
        # how many parameters the method has, so no index can be proven
        # out of range.
        return None
    if not isinstance(sig, str) or not sig.startswith("("):
        return None
    inner = sig[1:sig.index(")")].strip()
    if "*" in inner:
        return None
    return 0 if inner == "" else len(inner.split(","))


_ARG = re.compile(r"arg\((\d+)\)")


def check_arg_range(entries) -> list:
    findings = []
    for e in entries:
        n = arity(e.sig)
        if n is None:
            continue
        for c in e.copies:
            for side in (c.frm, c.to):
                m = _ARG.fullmatch(side[0])
                if m and int(m.group(1)) >= n:
                    findings.append(Finding(
                        "I5", e.file, func_name(e.func),
                        f"{side[0]} but signature declares {n} parameter(s)"))
    return findings


SCALAR_PRIMITIVES = {
    "byte", "short", "int", "long", "float", "double", "char", "boolean", "void",
}
KNOWN_SCALAR_CLASSES = {
    "java.lang.String", "java.lang.CharSequence", "java.lang.Integer", "java.lang.Long",
    "java.lang.Boolean", "java.lang.Character", "java.lang.Double", "java.lang.Float",
    "java.lang.Short", "java.lang.Byte", "java.lang.Class", "java.net.URL", "java.net.URI",
}


def is_element_safe(type_name) -> bool:
    """True when an ElementAccessor on this type is not provably dead."""
    if type_name is None:
        return True
    if type_name.endswith("[]"):
        return True
    return type_name not in SCALAR_PRIMITIVES and type_name not in KNOWN_SCALAR_CLASSES


def _split_signature(sig):
    """({param index: type}, return type); params is None when unknown."""
    if isinstance(sig, dict):
        params = sig.get("params")
        types = None
        if params is not None:
            types = {p["index"]: p.get("type") for p in params}
        return types, sig.get("return")
    if not isinstance(sig, str) or not sig.startswith("("):
        return None, None
    inner = sig[1:sig.index(")")].strip()
    ret = sig[sig.index(")") + 1:].strip() or None
    if "*" in inner:
        return None, ret
    types = [] if inner == "" else [t.strip() for t in inner.split(",")]
    return {i: t for i, t in enumerate(types)}, ret


def _parse_slot(accessor: str):
    """(owner, role, type) for a well-formed `.Owner#role#Type` key, else None."""
    parts = accessor.split("#")
    if len(parts) != 3:
        return None
    return parts[0].lstrip("."), parts[1], parts[2]


def position_type(entry, pos: tuple):
    """Declared type of the slot the accessors land on, or of the base."""
    tail = [a for a in pos[1:] if a != "[*]"]
    if tail:
        parsed = _parse_slot(tail[-1])
        return parsed[2] if parsed else None
    params, ret = _split_signature(entry.sig)
    base = pos[0]
    if base == "result":
        return ret
    if base == "this":
        return "java.lang.Object"
    m = _ARG.fullmatch(base)
    if m and params is not None:
        return params.get(int(m.group(1)))
    return None


def check_element_targets(entries) -> list:
    findings = []
    for e in entries:
        for c in e.copies:
            for side in (c.frm, c.to):
                if "[*]" not in side:
                    continue
                prefix = side[:side.index("[*]")]
                t = position_type(e, prefix)
                if not is_element_safe(t):
                    findings.append(Finding(
                        "I4", e.file, func_name(e.func),
                        f"[*] on {'.'.join(prefix)} of scalar type {t}"))
    return findings


def _dst_holds_element(entry, to: tuple) -> bool:
    """True when the destination can hold an array element, so a whole copy
    carries src[i] with it and no explicit [*] edge is needed."""
    tail = [a for a in to[1:] if a != "[*]"]
    if tail:
        parsed = _parse_slot(tail[-1])
        t = parsed[2] if parsed else None
        return t is None or t == "java.lang.Object" or t.endswith("[]")
    t = position_type(entry, to)
    return t is None or t.endswith("[]")


def check_element_carrier(entries) -> list:
    findings = []
    for e in entries:
        present = {(c.frm, c.to) for c in e.copies}
        for c in e.copies:
            if "[*]" in c.frm or "[*]" in c.to:
                continue
            src_t = position_type(e, c.frm)
            if src_t is None or not src_t.endswith("[]"):
                continue
            dst_t = position_type(e, c.to)
            if _dst_holds_element(e, c.to):
                continue  # element-holding target: the whole copy carries elements
            if (c.frm + ("[*]",), c.to) in present:
                continue
            findings.append(Finding(
                "I3", e.file, func_name(e.func),
                f"{'.'.join(c.frm)} (type {src_t}) -> {'.'.join(c.to)} (type {dst_t}) "
                f"has no explicit [*] carrier"))
    return findings


_PREFIXES = ("set", "get", "add", "is", "put", "has")


def property_of(method: str):
    for p in _PREFIXES:
        if method.startswith(p) and len(method) > len(p):
            return method[len(p):].lower()
    return None


def _is_shared_by_design(slot: str, shared: set) -> bool:
    """True when a slot legitimately carries one value across every accessor.

    The config's convention: a Capitalised role is a container's or wrapper's
    contents (`Iterable#Element`, `Map#MapValue`, `HttpEntity#Body`) that every
    accessor shares on purpose, while a camelCase role is a named property that
    only its own getter and setter may touch. `shared` carries per-slot
    exceptions from the allowlist.
    """
    if slot in shared:
        return True
    parsed = _parse_slot(slot)
    return parsed is not None and parsed[1][:1].isupper()


def load_allowlist(path: str) -> dict:
    with open(path) as fh:
        doc = yaml.safe_load(fh) or {}
    return {
        "renderers": list(doc.get("renderers") or []),
        "source_fed_slots": list(doc.get("source_fed_slots") or []),
        "shared_slots": list(doc.get("shared_slots") or []),
    }


def _entry_identity(func):
    """(class, method) for slot-usage purposes, or None when func is unrecognised.

    String form (`pkg.Cls#method`) and map form with a literal `name:` both
    identify one exact method -- same meaning, see SerializedNameMatcher.kt.
    `class` is the fully-qualified owner when it can be read literally
    (string form, or map form with literal `package:`/`class:`); it is None
    when the owner itself is pattern-matched, since no single class name can
    be attributed to the entry.

    Map form with `name: {pattern: ...}` identifies a family of methods by
    regex, not a single name; it is represented as a sentinel that never
    matches a known getter/setter prefix, so property_of() reports it as "not
    a named property" and it can never be paired against a real accessor as a
    cross-property (I1) leak. It still carries a (file, class, sentinel)
    identity so it counts as a real reader/writer for orphan-slot (I2)
    purposes.
    """
    if isinstance(func, str):
        if "#" not in func:
            return None
        cls, method = func.rsplit("#", 1)
        return cls, method
    if isinstance(func, dict):
        pkg, klass = func.get("package"), func.get("class")
        cls = f"{pkg}.{klass}" if isinstance(pkg, str) and isinstance(klass, str) else None
        name = func.get("name")
        if isinstance(name, str):
            return cls, name
        if isinstance(name, dict) and isinstance(name.get("pattern"), str):
            return cls, f"<pattern:{name['pattern']}>"
    return None


def _slot_usage(entries):
    """slot -> (writers, readers) as sets of (file, method, class)."""
    writers, readers = {}, {}
    for e in entries:
        identity = _entry_identity(e.func)
        if identity is None:
            continue
        cls, method = identity
        for c in e.copies:
            for side, acc in ((c.to, writers), (c.frm, readers)):
                for a in side[1:]:
                    if a == "[*]":
                        continue
                    acc.setdefault(a, set()).add((e.file, method, cls))
    return writers, readers


def _is_renderer(cls, method, renderers) -> bool:
    """True when a bare method name or a `Class#method` scoped entry in the
    allowlist's `renderers` exempts this (class, method)."""
    return method in renderers or (cls is not None and f"{cls}#{method}" in renderers)


def check_shared_slot(entries, allow) -> list:
    renderers = set(allow["renderers"])
    shared = set(allow.get("shared_slots") or ())
    writers, readers = _slot_usage(entries)
    findings = []
    seen = set()
    for slot in sorted(set(writers) & set(readers)):
        if _is_shared_by_design(slot, shared):
            continue
        for wfile, wm, wcls in sorted(writers[slot]):
            wp = property_of(wm)
            for rfile, rm, rcls in sorted(readers[slot]):
                if _is_renderer(rcls, rm, renderers) or _is_renderer(wcls, wm, renderers):
                    continue
                rp = property_of(rm)
                if wp is None or rp is None or wp == rp:
                    continue
                # The owning class is part of writers/readers identity (so a
                # scoped renderer can exempt one class's method but not
                # another's with the same name), but not part of the Finding
                # itself: several owning classes sharing the same (file,
                # method) writer or reader would otherwise report the exact
                # same (file, slot, detail) finding once per class.
                finding = Finding(
                    "I1", wfile, slot,
                    f"{wm} writes and {rm} reads the same slot {slot}")
                if finding in seen:
                    continue
                seen.add(finding)
                findings.append(finding)
    return findings


def check_orphan_slots(entries, allow) -> list:
    """One I2 finding per file that participates in an orphan slot, not one
    arbitrary file -- a slot written across several files but never read is
    equally "caused by" each of them, and `--changed` must catch it however
    the changed-file set intersects that group. Every such finding for a
    given slot carries identical detail text, so it reads as one underlying
    issue reported once per participating file rather than as unrelated
    findings."""
    exempt = set(allow["source_fed_slots"])
    writers, readers = _slot_usage(entries)
    findings = []
    for slot in sorted(set(writers) | set(readers)):
        if slot in exempt:
            continue
        if slot not in readers:
            side, verb, reason = writers[slot], "written", "never read"
        elif slot not in writers:
            side, verb, reason = readers[slot], "read", "never written"
        else:
            continue
        files = sorted({f for f, _, _ in side})
        methods = sorted({m for _, m, _ in side})
        detail = f"{slot} is {verb} ({', '.join(methods)}) but {reason}"
        for file in files:
            findings.append(Finding("I2", file, slot, detail))
    return findings


def check_no_rule_storage(entries) -> list:
    findings = []
    for e in entries:
        for c in e.copies:
            for side in (c.frm, c.to):
                for a in side[1:]:
                    if isinstance(a, str) and "<rule-storage>" in a:
                        findings.append(Finding(
                            "I6", e.file, func_name(e.func), f"{a} must be re-keyed"))
    return findings


def _all_findings(entries, allow, gate_i6) -> list:
    findings = (
        check_shared_slot(entries, allow)
        + check_orphan_slots(entries, allow)
        + check_element_carrier(entries)
        + check_element_targets(entries)
        + check_arg_range(entries)
    )
    if gate_i6:
        findings += check_no_rule_storage(entries)
    return findings


def run(root, allow_path, changed=None, gate_i6=False, compare_ref=None):
    """Returns (failures, reports, preexisting_changed).

    failures: findings to gate on.
    reports: findings outside `changed`, reported but never enforced.
    preexisting_changed: only non-empty with `compare_ref` set — findings in
        `changed` files that already existed at `compare_ref`; reported, not
        enforced, and kept distinct from `failures` (new findings) and from
        `reports` (untouched files).

    Without `changed`, every finding is a failure (whole-config gate).
    With `changed` but no `compare_ref`, every finding in a changed file is a
    failure, matching the pre-`--compare-ref` behaviour.
    With `changed` and `compare_ref`, only findings in changed files that are
    NEW relative to `compare_ref` are failures; findings are compared by
    (code, file, func, detail) identity, not by count.
    """
    entries = load_entries(root)
    allow = load_allowlist(allow_path)
    findings = _all_findings(entries, allow, gate_i6)
    if changed is None:
        return findings, [], []
    if compare_ref is None:
        failures = [f for f in findings if f.file in changed]
        reports = [f for f in findings if f.file not in changed]
        return failures, reports, []
    ref_entries = load_entries_at_ref(compare_ref, root)
    ref_ids = {tuple(f) for f in _all_findings(ref_entries, allow, gate_i6)}
    failures = [f for f in findings if f.file in changed and tuple(f) not in ref_ids]
    preexisting_changed = [f for f in findings if f.file in changed and tuple(f) in ref_ids]
    reports = [f for f in findings if f.file not in changed]
    return failures, reports, preexisting_changed


def main(argv=None) -> int:
    import argparse
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=os.path.join(here, "..", "model", "java", "config"))
    ap.add_argument("--allowlist", default=os.path.join(here, "config_lint_allowlist.yaml"))
    ap.add_argument("--changed", nargs="*", default=None,
                    help="config-relative paths to enforce; others are reported only")
    ap.add_argument("--gate-i6", action="store_true")
    ap.add_argument("--compare-ref", default=None,
                    help="git ref to diff --changed findings against; only findings "
                         "new relative to this ref fail, pre-existing ones are reported")
    args = ap.parse_args(argv)
    if not os.path.isdir(args.root):
        print(f"error: config root not found: {args.root}", file=sys.stderr)
        return 2
    if not os.path.isfile(args.allowlist):
        print(f"error: allowlist not found: {args.allowlist}", file=sys.stderr)
        return 2
    if args.changed is not None and len(args.changed) == 0:
        print("error: --changed given with no paths -- this would enforce nothing "
              "and exit 0 vacuously; omit --changed entirely to enforce everything, "
              "or pass at least one path", file=sys.stderr)
        return 2
    if args.compare_ref is not None:
        try:
            _git(["rev-parse", "--verify", f"{args.compare_ref}^{{commit}}"], args.root)
        except RuntimeError as exc:
            print(f"error: --compare-ref {args.compare_ref}: {exc}", file=sys.stderr)
            return 2
    changed = set(args.changed) if args.changed is not None else None
    try:
        failures, reports, preexisting_changed = run(
            args.root, args.allowlist, changed, args.gate_i6, args.compare_ref)
    except RuntimeError as e:
        print(f"error: --compare-ref {args.compare_ref}: {e}", file=sys.stderr)
        return 2
    for f in failures:
        print(f"FAIL {f.code} {f.file} {f.func}: {f.detail}")
    if preexisting_changed:
        counts = {}
        for f in preexisting_changed:
            counts[f.code] = counts.get(f.code, 0) + 1
        print("pre-existing in changed files (reported, not enforced): "
              + ", ".join(f"{k}={counts[k]}" for k in sorted(counts)))
    if reports:
        counts = {}
        for f in reports:
            counts[f.code] = counts.get(f.code, 0) + 1
        print("pre-existing (reported, not enforced): "
              + ", ".join(f"{k}={counts[k]}" for k in sorted(counts)))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
