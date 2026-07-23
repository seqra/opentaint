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


def position_type(entry, pos: tuple):
    """Declared type of the slot the accessors land on, or of the base."""
    tail = [a for a in pos[1:] if a != "[*]"]
    if tail:
        parts = tail[-1].split("#")
        return parts[-1] if len(parts) == 3 else None
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
            if is_element_safe(dst_t) and (dst_t is None or dst_t.endswith("[]")):
                continue  # array target: the whole copy carries elements
            if (c.frm + ("[*]",), c.to) in present:
                continue
            findings.append(Finding(
                "I3", e.file, func_name(e.func),
                f"{'.'.join(c.frm)} (type {src_t}) -> {'.'.join(c.to)} (type {dst_t}) "
                f"has no explicit [*] carrier"))
    return findings
