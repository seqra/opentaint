#!/usr/bin/env python3
"""Root-only check of the separate defensive pass-protection policy model."""
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
MODEL = HERE / 'PassProtectionPolicy.lean'


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
    with tempfile.TemporaryDirectory(prefix='pass-protection-policy-') as temporary:
        env = dict(os.environ)
        command = ['lake', 'env', 'lean', '-M2048', '-o',
                   str(Path(temporary) / 'PassProtectionPolicy.olean'), str(MODEL)]
        result = subprocess.run(command, cwd=LEAN_ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(result.stdout)
        assert 'error:' not in result.stdout and 'sorryAx' not in result.stdout
    for dependencies in re.findall(r'depends on axioms:\s*\[([^]]*)\]', result.stdout, re.S):
        assert set(filter(None, dependencies.replace('\n', '').replace(' ', '').split(','))) <= {'propext', 'Quot.sound'}
    audit = [line for line in result.stdout.splitlines() if line.startswith("'PassProtectionPolicy.")]
    assert len(audit) == len(names)
    assert 'PASS_PROTECTION_POLICY=true' in result.stdout
    assert 'PASS_PROTECTION_POLICY=false' not in result.stdout
    receipt = {
        'schema': 'pass-protection-policy-proposal-proof-check-v1',
        'state': 'PASS_LOCAL_TYPED_PASS_POLICY_ONLY_NO_NATIVE_EQUIVALENCE',
        'model': MODEL.name, 'modelSha256': sha(MODEL), 'checkerSha256': sha(Path(__file__)),
        'theorems': len(names), 'theoremNames': names, 'axiomAudit': audit,
        'allowedFoundationAxioms': ['propext', 'Quot.sound'],
        'scope': 'Defensive typed ActionRole/RuleKind PASS_THROUGH exclusion, direct/reversed dispatch from preserved forward metadata, pass non-introduction and exact transport of existing H.',
        'nativePassBugClaim': False,
        'genericSummaryCanAddCycleProtection': True,
        'assignmentCleanerPoliciesExplicit': True,
        'notProved': ['Native AP transfer equivalence', 'Complete source, cleaner, summary or cycle policy correctness',
                      'Protection storage/non-subsumption across all owners', 'Shared-loop or project recovery'],
    }
    encoded = json.dumps(receipt, indent=2) + '\n'
    if args.output:
        forbidden = {'checks.json', 'packed-checks.json', 'preparation.json', 'packed-preparation.json'}
        assert args.output.resolve().parent != HERE or args.output.name not in forbidden
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
