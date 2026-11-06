#!/usr/bin/env python3
"""Root-only constructive check of incremental all-H/MAY retention laws."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
LEAN_ROOT = HERE.parents[1]
MODEL = HERE / 'AllProtectionRetention.lean'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    model = MODEL.read_text()
    source = re.sub(r'/\-.*?\-/', '', model, flags=re.S)
    source = re.sub(r'--[^\n]*', '', source)
    assert re.findall(r'^import (.+)$', source, re.M) == ['Std']
    assert not re.search(r'^\s*(?:axiom|opaque|noncomputable)\b', source, re.M)
    assert not re.search(r'\b(?:sorry|admit|Classical)\b', source)
    names = re.findall(r'^theorem (\w+)', model, re.M)
    printed = re.findall(r'^#print axioms (\w+)', model, re.M)
    assert names and len(names) == len(set(names)) and names == printed
    with tempfile.TemporaryDirectory(prefix='all-protection-retention-') as temporary:
        command = ['lake', 'env', 'lean', '-M2048', '-o',
                   str(Path(temporary) / 'AllProtectionRetention.olean'), str(MODEL)]
        result = subprocess.run(command, cwd=LEAN_ROOT, env=dict(os.environ), text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(result.stdout)
        assert 'error:' not in result.stdout and 'sorryAx' not in result.stdout
    for dependencies in re.findall(r'depends on axioms:\s*\[([^]]*)\]', result.stdout, re.S):
        assert set(filter(None, dependencies.replace('\n', '').replace(' ', '').split(','))) <= {'propext', 'Quot.sound'}
    audit = [line for line in result.stdout.splitlines() if line.startswith("'AllProtectionRetention.")]
    assert len(audit) == len(names)
    assert 'ALL_H_RETENTION=true' in result.stdout and 'ALL_H_RETENTION=false' not in result.stdout
    receipt = {
        'schema': 'incremental-all-protection-retention-proof-check-v1',
        'state': 'PASS_LOCAL_INCREMENTAL_LAWS_ONLY_NO_NATIVE_DATA_NORMAL_FORM',
        'model': MODEL.name, 'modelSha256': sha(MODEL), 'checkerSha256': sha(Path(__file__)),
        'theorems': len(names), 'theoremNames': names, 'axiomAudit': audit,
        'allowedFoundationAxioms': ['propext', 'Quot.sound'],
        'scope': 'Arbitrary restoreCurrent/oldDataAdmit parameters; literal all-H union and exact freshness, H carrier embedding, requested D/ANY MAY union, proof-bearing duplicate precheck; effective EXACT ignores wrappers and spans retain exact typed E.',
        'DATAConfluenceOrGlobalIdempotenceAssumed': False,
        'duplicatePrecheckScope': 'Selected MAY included plus exact H included; no full literal DATA payload inclusion or native DATA freshness equivalence is asserted.',
        'physicalMAYEqualityConditionalOn': ['H subset payload for both native inputs', 'DATA admission creates no extra selected MAY coordinate'],
        'notProved': ['Native old DATA admission/restoreCurrent/embedding equivalence',
                      'Canonical wrapper placement and full native E/header conversion',
                      'Every producer/adaptor, native DATA freshness, full DATA order independence or global normal-form law',
                      'Native pass/assignment/cleaner/call/ND/alias/static effects or project recovery'],
    }
    encoded = json.dumps(receipt, indent=2) + '\n'
    if args.output:
        assert args.output.resolve().parent == HERE and args.output.name == 'all-protection-checks.json'
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
