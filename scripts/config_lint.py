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
import sys
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


def arity(sig) -> Optional[int]:
    """Number of declared parameters, or None when unknown/wildcarded."""
    if isinstance(sig, dict):
        params = sig.get("params")
        return None if params is None else len(params)
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
    """(param type list, return type) or (None, None) when unknown."""
    if isinstance(sig, dict):
        params = sig.get("params")
        types = None
        if params is not None:
            types = [p.get("type") for p in sorted(params, key=lambda p: p["index"])]
        return types, sig.get("return")
    if not isinstance(sig, str) or not sig.startswith("("):
        return None, None
    inner = sig[1:sig.index(")")].strip()
    if "*" in inner:
        return None, sig[sig.index(")") + 1:].strip() or None
    types = [] if inner == "" else [t.strip() for t in inner.split(",")]
    return types, sig[sig.index(")") + 1:].strip() or None


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
    if m and params is not None and int(m.group(1)) < len(params):
        return params[int(m.group(1))]
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


def _slot_usage(entries):
    """slot -> (writers, readers) as sets of (file, method)."""
    writers, readers = {}, {}
    for e in entries:
        if not isinstance(e.func, str) or "#" not in e.func:
            continue
        method = e.func.rsplit("#", 1)[1]
        for c in e.copies:
            for side, acc in ((c.to, writers), (c.frm, readers)):
                for a in side[1:]:
                    if a == "[*]":
                        continue
                    acc.setdefault(a, set()).add((e.file, method))
    return writers, readers


def check_shared_slot(entries, allow) -> list:
    renderers = set(allow["renderers"])
    shared = set(allow.get("shared_slots") or ())
    writers, readers = _slot_usage(entries)
    findings = []
    for slot in sorted(set(writers) & set(readers)):
        if _is_shared_by_design(slot, shared):
            continue
        for wfile, wm in sorted(writers[slot]):
            wp = property_of(wm)
            for rfile, rm in sorted(readers[slot]):
                if rm in renderers or wm in renderers:
                    continue
                rp = property_of(rm)
                if wp is None or rp is None or wp == rp:
                    continue
                findings.append(Finding(
                    "I1", wfile, slot,
                    f"{wm} writes and {rm} reads the same slot {slot}"))
    return findings


def check_orphan_slots(entries, allow) -> list:
    exempt = set(allow["source_fed_slots"])
    writers, readers = _slot_usage(entries)
    findings = []
    for slot in sorted(set(writers) | set(readers)):
        if slot in exempt:
            continue
        if slot not in readers:
            f = sorted(writers[slot])[0]
            findings.append(Finding("I2", f[0], slot, f"{slot} is written ({f[1]}) but never read"))
        elif slot not in writers:
            f = sorted(readers[slot])[0]
            findings.append(Finding("I2", f[0], slot, f"{slot} is read ({f[1]}) but never written"))
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


def run(root, allow_path, changed=None, gate_i6=False):
    entries = load_entries(root)
    allow = load_allowlist(allow_path)
    findings = (
        check_shared_slot(entries, allow)
        + check_orphan_slots(entries, allow)
        + check_element_carrier(entries)
        + check_element_targets(entries)
        + check_arg_range(entries)
    )
    if gate_i6:
        findings += check_no_rule_storage(entries)
    if changed is None:
        return findings, []
    failures = [f for f in findings if f.file in changed]
    reports = [f for f in findings if f.file not in changed]
    return failures, reports


def main(argv=None) -> int:
    import argparse
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=os.path.join(here, "..", "model", "java", "config"))
    ap.add_argument("--allowlist", default=os.path.join(here, "config_lint_allowlist.yaml"))
    ap.add_argument("--changed", nargs="*", default=None,
                    help="config-relative paths to enforce; others are reported only")
    ap.add_argument("--gate-i6", action="store_true")
    args = ap.parse_args(argv)
    changed = set(args.changed) if args.changed is not None else None
    failures, reports = run(args.root, args.allowlist, changed, args.gate_i6)
    for f in failures:
        print(f"FAIL {f.code} {f.file} {f.func}: {f.detail}")
    if reports:
        counts = {}
        for f in reports:
            counts[f.code] = counts.get(f.code, 0) + 1
        print("pre-existing (reported, not enforced): "
              + ", ".join(f"{k}={counts[k]}" for k in sorted(counts)))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
