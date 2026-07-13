#!/usr/bin/env python3
"""
sarif-to-findings.py — turn an OpenTaint SARIF report into per-rule finding
tracking files under .opentaint/tracking/findings/.

One file per rule_id, bundling that rule's result hashes into sarif_hashes.
Grouping is trivial (by rule_id) — no clustering. The triage skill
(analyze-findings) later splits a rule's bundle into distinct logical findings.

Idempotent: re-running after a re-scan adds only result hashes not already
present in any of that rule's finding files, resets the touched file's verdict
to `pending`, and leaves existing verdict/notes/poc and triage splits intact.

SARIF assumptions — adjust the two helpers below if the real OpenTaint SARIF
differs:
- result.ruleId holds the full rule id (e.g. java/security/sqli.yaml:sqli)
- a stable per-result hash comes from result.fingerprints / partialFingerprints
  when present, else is computed from ruleId + locations + code-flow locations
- result.message.text seeds the analyzer report in `notes`
"""
import argparse
import glob
import hashlib
import json
import re
from pathlib import Path

ADJ = ["brave", "calm", "eager", "fuzzy", "gentle", "jolly", "keen", "lucid",
       "merry", "noble", "proud", "quiet", "rapid", "sly", "tidy", "vivid",
       "witty", "zesty", "amber", "bold"]
NOUN = ["hopper", "eagle", "otter", "falcon", "maple", "comet", "harbor",
        "willow", "pixel", "river", "ember", "cobra", "lotus", "raven",
        "quartz", "badger", "cedar", "drake", "finch", "gull"]


def docker_name(seed, taken):
    """Stable adjective-noun slug from the rule id; suffixed on collision."""
    h = int(hashlib.sha1(seed.encode()).hexdigest(), 16)
    base = f"{ADJ[h % len(ADJ)]}-{NOUN[(h // len(ADJ)) % len(NOUN)]}"
    name, n = base, 2
    while name in taken:
        name, n = f"{base}-{n}", n + 1
    return name


_FP_PREFERENCE = ("vulnerabilitySourceSinkHash", "vulnerabilityWithTraceHash")


def result_hash(res):
    fp = res.get("fingerprints") or res.get("partialFingerprints")
    if isinstance(fp, dict) and fp:
        for pref in _FP_PREFERENCE:
            for k, v in fp.items():
                if k.startswith(pref):
                    return str(v)[:16]
        return str(sorted(fp.values())[0])[:16]
    parts = [res.get("ruleId", "")]
    locs = list(res.get("locations", []))
    for cf in res.get("codeFlows", []):
        for tf in cf.get("threadFlows", []):
            locs += [st.get("location", {}) for st in tf.get("locations", [])]
    for loc in locs:
        pl = loc.get("physicalLocation", {})
        parts.append(pl.get("artifactLocation", {}).get("uri", ""))
        parts.append(json.dumps(pl.get("region", {}), sort_keys=True))
    return hashlib.sha1("|".join(parts).encode()).hexdigest()[:16]


def scan_results(sarif):
    """rule_id -> {hash: message}"""
    out = {}
    for run in sarif.get("runs") or []:
        for res in run.get("results") or []:
            rid = res.get("ruleId") or "unknown"
            msg = (res.get("message", {}) or {}).get("text", "").strip()
            out.setdefault(rid, {})[result_hash(res)] = msg
    return out


NAME_RE = re.compile(r'^finding_name:\s*(.+?)\s*$', re.M)
RULE_RE = re.compile(r'^rule_id:\s*(.+?)\s*$', re.M)
HASHES_RE = re.compile(r'^sarif_hashes:\s*\[(.*)\]\s*$', re.M)
HASHES_BLOCK_RE = re.compile(r'^sarif_hashes:\s*\n((?:[ \t]+-[^\n]*\n?)+)', re.M)


def parse_hashes(text):
    """Hashes from either flow style ([a, b]) or block style (- a / - b)."""
    m = HASHES_RE.search(text)
    if m:
        return [h.strip() for h in m.group(1).split(",") if h.strip()]
    m = HASHES_BLOCK_RE.search(text)
    if m:
        return [ln.strip().lstrip("-").strip()
                for ln in m.group(1).splitlines() if ln.strip().lstrip("-").strip()]
    return []


def replace_hashes(text, merged):
    """Rewrite the sarif_hashes entry (either style) as a flow list; if the key
    is missing entirely, prepend it so merged hashes are never silently lost."""
    line = "sarif_hashes: " + fmt_list(merged)
    if HASHES_RE.search(text):
        return HASHES_RE.sub(lambda m: line, text, count=1)
    if HASHES_BLOCK_RE.search(text):
        return HASHES_BLOCK_RE.sub(line + "\n", text, count=1)
    return line + "\n" + text


def parse_existing(text):
    name = NAME_RE.search(text)
    rid = RULE_RE.search(text)
    return (name.group(1) if name else None,
            rid.group(1) if rid else None,
            parse_hashes(text))


def fmt_list(hashes):
    return "[" + ", ".join(hashes) + "]"


def new_file_text(name, rid, hashes, notes):
    body = "\n".join("  " + ln for ln in (notes or "(no analyzer message)").splitlines())
    return (f"finding_name: {name}\n"
            f"sarif_hashes: {fmt_list(hashes)}\n"
            f"rule_id: {rid}\n"
            f"verdict: pending\n"
            f"notes: >\n{body}\n"
            f"poc: pending\n"
            f"poc_script: null\n")


def main():
    ap = argparse.ArgumentParser(
        description="SARIF -> per-rule finding tracking files (idempotent)")
    ap.add_argument("sarif", help="path to report.sarif")
    ap.add_argument("-o", "--out", default=".opentaint/tracking/findings",
                    help="findings dir (default: .opentaint/tracking/findings)")
    args = ap.parse_args()

    by_rule = scan_results(json.loads(Path(args.sarif).read_text(encoding="utf-8")))

    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    existing = {}
    taken = set()
    for p in sorted(glob.glob(str(out / "*.yaml"))):
        name, rid, hashes = parse_existing(Path(p).read_text(encoding="utf-8"))
        if name:
            taken.add(name)
        if rid:
            existing.setdefault(rid, []).append((Path(p), hashes))

    created = updated = unchanged = 0
    for rid, hashmap in sorted(by_rule.items()):
        scanned = set(hashmap)
        files = existing.get(rid)
        if not files:
            name = docker_name(rid, taken)
            taken.add(name)
            notes = "\n".join(sorted({m for m in hashmap.values() if m}))
            (out / f"{name}.yaml").write_text(
                new_file_text(name, rid, sorted(scanned), notes), encoding="utf-8")
            created += 1
            continue
        already = set().union(*(set(h) for _, h in files))
        new = sorted(scanned - already)
        if not new:
            unchanged += 1
            continue
        path, hashes = files[0]
        merged = sorted(set(hashes) | set(new))
        text = path.read_text(encoding="utf-8")
        text = replace_hashes(text, merged)
        text = re.sub(r'^verdict:\s*.+$', "verdict: pending", text, count=1, flags=re.M)
        path.write_text(text, encoding="utf-8")
        updated += 1

    print(f"findings: {created} created, {updated} updated, {unchanged} unchanged "
          f"({len(by_rule)} rules in scan)")


if __name__ == "__main__":
    main()
