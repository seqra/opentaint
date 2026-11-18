#!/usr/bin/env python3
"""Audit the different-coordinate uniform reply cycle against the complete consolidated policy."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def main():
    q = argparse.ArgumentParser()
    q.add_argument('--out', type=Path, required=True)
    q.add_argument('--dependencies', type=Path)
    a = q.parse_args()
    pkg = Path(__file__).resolve().parent
    out = a.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if a.dependencies:
        base = a.dependencies.resolve()
        receipt = json.loads((base / 'receipt.json').read_text())
        for name, entry in receipt['models'].items():
            assert hashlib.sha256(Path(entry['source']).read_bytes()).hexdigest() == entry['sha256'], name
            for suffix in ('.olean', '.lean', '.txt'):
                src = base / (name + suffix)
                if src.exists() and src.resolve() != (out / src.name).resolve():
                    shutil.copy2(src, out / src.name)
    else:
        subprocess.run(['python3', str(pkg.parent / 'definite-reply-support-20261116/check.py'),
                        '--out', str(out)], check=True)
        receipt = json.loads((out / 'receipt.json').read_text())

    source = pkg / 'DifferentReply.lean'
    content = source.read_text()
    assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b|\bnative_decide\b', content, re.M)
    shutil.copy2(source, out / source.name)
    env = {**os.environ, 'LEAN_PATH': str(out)}
    compiled = subprocess.run(['lean', '-o', 'DifferentReply.olean', source.name], cwd=out,
                              env=env, text=True, capture_output=True)
    log = compiled.stdout + compiled.stderr
    (out / 'DifferentReply.txt').write_text(log)
    assert compiled.returncode == 0 and 'warning:' not in log, log
    claims = re.findall(r'^theorem (\w+)', content, re.M)
    audit = 'import DifferentReply\n' + ''.join(
        '#print axioms DifferentUniformReply.' + name + '\n' for name in claims)
    (out / 'DifferentReplyAudit.lean').write_text(audit)
    checked = subprocess.run(['lean', 'DifferentReplyAudit.lean'], cwd=out, env=env,
                             text=True, capture_output=True)
    log = checked.stdout + checked.stderr
    (out / 'DifferentReplyAudit.txt').write_text(log)
    assert checked.returncode == 0, log
    found = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log)
    assert len(found) == len(claims), (len(found), len(claims))
    for name, axioms in found:
        assert set(axioms.replace('\n', '').split(', ')) - {''} <= {'propext', 'Quot.sound'}, (name, axioms)
    receipt['models']['DifferentReply'] = dict(source=str(source),
        sha256=hashlib.sha256(source.read_bytes()).hexdigest(), auditedDeclarations=len(found))
    receipt.update(status='PASS', newDeclarations=len(found),
        auditedDeclarations=sum(v['auditedDeclarations'] for v in receipt['models'].values()),
        scope='Two acyclic fully analyzed owners with ordinary T-to-U conditional marking rules; cold run-1 through run-6, qualified child heads, bounded preparation, raw C5, extra EXACT and g-guard records, same-layer canonicalization and latest definite EXACT/MUST reply support enabled. Uncapped root Target recurrence from run-6 while helper demand is empty and both observations already NORMAL. No loop, recursion, cleaner, pass, aliases or real cuts. Scoped model with native adapter evidence, not a whole-engine bisimulation.')
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', newDeclarations=len(found),
        auditedDeclarations=receipt['auditedDeclarations'], modules=len(receipt['models']),
        receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
