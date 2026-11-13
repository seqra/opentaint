#!/usr/bin/env python3
"""Compile and audit the complete non-empty-MAY proposal model outside Git."""
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
    repo = package.parents[3]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    result = {
        'leanVersion': subprocess.check_output(['lean', '--version'], text=True).strip(),
        'scope': 'scalar field-string reference; not full analyzer/driver correspondence',
        'models': {},
    }
    total = 0
    for name in ['NonEmptyMay', 'Policy', 'Restriction', 'Coverage']:
        source = package / (name + '.lean')
        target = out / source.name
        shutil.copy2(source, target)
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b',
                             target.read_text(), re.M), source
        run = subprocess.run(['lean', '-o', name + '.olean', source.name], cwd=out,
                             env={**os.environ, 'LEAN_PATH': str(out)}, text=True,
                             capture_output=True)
        log = run.stdout + run.stderr
        (out / (name + '.txt')).write_text(log)
        if run.returncode:
            print(log)
            raise SystemExit(run.returncode)
        assert 'sorryAx' not in log and 'Classical.choice' not in log
        audited = []
        for line in log.splitlines():
            if 'does not depend on any axioms' in line:
                audited.append(line)
            elif 'depends on axioms:' in line:
                dependencies = set(re.search(r'\[(.*)\]', line)[1].split(', '))
                assert dependencies <= {'propext', 'Quot.sound'}, line
                audited.append(line)
        assert audited, name
        total += len(audited)
        result['models'][name] = {
            'source': str(source.relative_to(repo)), 'sourceSha256': sha(source),
            'objectSha256': sha(out / (name + '.olean')), 'auditedDeclarations': len(audited),
        }
    result['auditedDeclarations'] = total
    (out / 'receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'modules': len(result['models']),
                      'auditedDeclarations': total, 'receipt': str(out / 'receipt.json')}, indent=2))


if __name__ == '__main__':
    main()
