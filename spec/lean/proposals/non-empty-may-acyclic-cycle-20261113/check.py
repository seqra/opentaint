#!/usr/bin/env python3
"""Compile the selected references and the acyclic cycle witness externally."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    reference = package.parent / 'non-empty-may-20261113'
    repo = package.parents[3]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    models = {}
    total = 0
    for name in ['NonEmptyMay', 'Policy', 'Restriction', 'Coverage', 'Cycle', 'BbTrace']:
        source = (package if name in {'Cycle', 'BbTrace'} else reference) / (name + '.lean')
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b',
                             source.read_text(), re.M), source
        shutil.copy2(source, out / source.name)
        result = subprocess.run(['lean', '-o', name + '.olean', source.name],
            cwd=out, env={**os.environ, 'LEAN_PATH': str(out)},
            text=True, capture_output=True)
        log = result.stdout + result.stderr
        (out / (name + '.txt')).write_text(log)
        if result.returncode:
            print(log)
            raise SystemExit(result.returncode)
        audited = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", log)
        assert audited, name
        for theorem, axioms in audited:
            assert set(axioms.replace('\n', '').split(', ')) - {''} <= {'propext', 'Quot.sound'}, (theorem, axioms)
        total += len(audited)
        models[name] = dict(source=str(source.relative_to(repo)),
            sourceSha256=sha(source), objectSha256=sha(out / (name + '.olean')),
            auditedDeclarations=len(audited))
    receipt = dict(leanVersion=subprocess.check_output(['lean', '--version'], text=True).strip(),
        scope='acyclic and BB-local witness projections; see reports for control/compaction embedding',
        models=models, auditedDeclarations=total)
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', modules=len(models), auditedDeclarations=total,
                         receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
