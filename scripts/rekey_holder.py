#!/usr/bin/env python3
"""Collapse a HOLDER class's <rule-storage> slot onto the base position.

Mechanical half of docs/superpowers/specs/2026-07-23-rule-storage-rekey-design.md.
Routing is the operator's call: pass the classes explicitly with --class.
"""
import argparse
import sys

import yaml

# The config was serialised at PyYAML's width=80. Any other width reflows long
# `signature:` lines across ~14 unrelated files and drowns the semantic diff.
# Verified: at width=80 the identity round-trip is byte-exact for 120 of 125
# config files.
DUMP_WIDTH = 80


def _as_list(v):
    return list(v) if isinstance(v, list) else [v]


def _rewrite(pos, classes):
    parts = _as_list(pos)
    kept = [parts[0]]
    for acc in parts[1:]:
        if isinstance(acc, str) and "<rule-storage>" in acc:
            owner = acc.split("#")[0].lstrip(".")
            if owner in classes:
                continue
        kept.append(acc)
    return kept[0] if len(kept) == 1 else kept


def collapse(doc: dict, classes: set) -> dict:
    out_entries = []
    for entry in doc.get("passThrough") or []:
        # Only entries that actually reference a targeted class are rewritten.
        # Anything else passes through as the identical object: the transform
        # must not de-duplicate or reformat copies it was not asked to touch.
        has_targeted_refs = False
        for c in entry.get("copy") or []:
            for pos in [c.get("from"), c.get("to")]:
                pos_list = _as_list(pos)
                for item in pos_list:
                    if isinstance(item, str) and "<rule-storage>" in item:
                        owner = item.split("#")[0].lstrip(".")
                        if owner in classes:
                            has_targeted_refs = True
                            break
                if has_targeted_refs:
                    break
            if has_targeted_refs:
                break

        if not has_targeted_refs:
            out_entries.append(entry)
            continue

        # Process copies: rewrite and deduplicate.
        seen, copies = set(), []
        for c in entry.get("copy") or []:
            frm = _rewrite(c["from"], classes)
            to = _rewrite(c["to"], classes)
            key = (tuple(_as_list(frm)), tuple(_as_list(to)))
            if key in seen:
                continue
            seen.add(key)
            copies.append({"from": frm, "to": to})
        # Drop an entry only when this transform is what emptied it. Entries
        # reaching here always started with a non-empty copy list (the
        # pre-scan above already passed through anything untargeted), so an
        # empty result here means the collapse emptied it.
        if not copies:
            continue
        new = dict(entry)
        new["copy"] = copies
        out_entries.append(new)
    result = dict(doc)
    result["passThrough"] = out_entries
    return result


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--file", required=True)
    ap.add_argument("--class", dest="classes", nargs="+", required=True)
    args = ap.parse_args(argv)
    with open(args.file) as fh:
        doc = yaml.safe_load(fh)
    out = collapse(doc, set(args.classes))
    with open(args.file, "w") as fh:
        yaml.safe_dump(out, fh, default_flow_style=False, sort_keys=False, width=DUMP_WIDTH)
    return 0


if __name__ == "__main__":
    sys.exit(main())
