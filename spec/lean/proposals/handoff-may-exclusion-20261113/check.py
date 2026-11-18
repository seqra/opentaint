#!/usr/bin/env python3
"""Check the exclusion counterexample against the selected C2/C5 externally."""
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
    parser.add_argument('--normal-only', action='store_true', help='also check the NORMAL-provider variant')
    parser.add_argument('--star-only', action='store_true', help='also check the same-head STAR-only mask')
    parser.add_argument('--promotion-ban', action='store_true', help='also check the separate operational promotion ban')
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    reference = package.parent / 'non-empty-may-20261113'
    cycle = package.parent / 'non-empty-may-acyclic-cycle-20261113'
    repo = package.parents[3]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    models = {}
    total = 0
    names = ['NonEmptyMay', 'Policy', 'Restriction', 'Coverage', 'Cycle', 'Exclusion']
    if args.normal_only or args.star_only or args.promotion_ban:
        names.append('NormalOnly')
    if args.star_only or args.promotion_ban:
        names.append('StarOnly')
    if args.promotion_ban:
        names.append('PromotionBan')
    for name in names:
        directory = cycle if name == 'Cycle' else package if name in {'Exclusion', 'NormalOnly', 'StarOnly', 'PromotionBan'} else reference
        source = directory / (name + '.lean')
        assert not re.search(r'^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|^\s*classical\b',
                             source.read_text(), re.M), source
        shutil.copy2(source, out / source.name)
        result = subprocess.run(['lean', '-o', name + '.olean', source.name], cwd=out,
            env={**os.environ, 'LEAN_PATH': str(out)}, text=True, capture_output=True)
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
        models[name] = dict(source=str(source.relative_to(repo)), sourceSha256=sha(source),
            objectSha256=sha(out / (name + '.olean')), auditedDeclarations=len(audited))
    receipt = dict(leanVersion=subprocess.check_output(['lean', '--version'], text=True).strip(),
        scope='separate operational STAR-to-MAY promotion ban; branch-sensitive counterexample' if args.promotion_ban else
              'handoff exclusion counterexample; raw same-head STAR-only variant included' if args.star_only else
              'handoff exclusion counterexample; normal-provider variant included' if args.normal_only else
              'candidate handoff exclusion counterexample; selected C2/C5 and scalar program transfers',
        models=models, auditedDeclarations=total)
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', modules=len(models), auditedDeclarations=total,
                         receipt=str(out / 'receipt.json')), indent=2))


if __name__ == '__main__':
    main()
