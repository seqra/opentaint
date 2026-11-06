#!/usr/bin/env python3
"""Root-only check of the ordered embedRawProtection bag model; no analyzer run."""
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
ROOT = HERE.parents[3]
MODEL = HERE / 'EmbedRawProtectionOrdered.lean'
PREPARATION = HERE / 'ordered-embed-preparation.json'
SOURCE = ROOT / 'core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/SpatialCanonical.kt'


def sha_bytes(value):
    return hashlib.sha256(value).hexdigest()


def sha(path):
    return sha_bytes(path.read_bytes())


def native_function():
    text = SOURCE.read_text()
    start = text.index('internal fun ApManager.embedRawProtection(')
    end = text.index('/** Copy only already-current flags', start)
    return text[start:end].rstrip() + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root-owned-execution', action='store_true', required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    assert args.root_owned_execution
    if args.output:
        assert args.output.resolve().parent == HERE
        assert args.output.name == 'ordered-embed-checks.json'
        assert not args.output.exists(), 'Use a new reviewed receipt; do not replace prior evidence.'

    prepared = json.loads(PREPARATION.read_text())
    before = {'model': sha(MODEL), 'checker': sha(Path(__file__)),
              'nativeFunction': sha_bytes(native_function().encode())}
    assert before['model'] == prepared['files'][MODEL.name]['sha256']
    assert before['checker'] == prepared['files'][Path(__file__).name]['sha256']
    assert before['nativeFunction'] == prepared['nativeBinding']['functionSha256']
    model = MODEL.read_text()
    code = re.sub(r'/\-.*?\-/', '', model, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert re.findall(r'^import (.+)$', code, re.M) == ['Std']
    assert not re.search(r'^\s*(?:axiom|opaque|noncomputable)\b', code, re.M)
    assert not re.search(r'\b(?:sorry|admit|Classical)\b', code)
    names = re.findall(r'^theorem (\w+)', code, re.M)
    audits = re.findall(r'^#print axioms (\w+)', code, re.M)
    assert names and len(names) == len(set(names)) and names == audits

    with tempfile.TemporaryDirectory(prefix='ordered-embed-root-check-') as temporary:
        command = ['lake', 'env', 'lean', '-M2048', '-o',
                   str(Path(temporary) / 'EmbedRawProtectionOrdered.olean'), str(MODEL)]
        result = subprocess.run(command, cwd=LEAN_ROOT, env=dict(os.environ), text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
        if result.returncode:
            raise RuntimeError(result.stdout)
    assert 'error:' not in result.stdout and 'sorryAx' not in result.stdout
    for dependencies in re.findall(r'depends on axioms:\s*\[([^]]*)\]', result.stdout, re.S):
        actual = set(filter(None, dependencies.replace('\n', '').replace(' ', '').split(',')))
        assert actual <= {'propext', 'Quot.sound'}, actual
    printed = [line for line in result.stdout.splitlines()
               if line.startswith("'EmbedRawProtectionOrdered.")]
    assert len(printed) == len(names)
    assert 'ORDERED_EMBED=true' in result.stdout and 'ORDERED_EMBED=false' not in result.stdout
    after = {'model': sha(MODEL), 'checker': sha(Path(__file__)),
             'nativeFunction': sha_bytes(native_function().encode())}
    assert before == after

    receipt = {
        'schema': 'ordered-embed-raw-protection-check-v1',
        'state': 'PASS_ORDERED_BAG_MODEL_ONLY_NATIVE_DAG_REFINEMENT_OPEN',
        'buildOwner': 'root', 'projectRan': False,
        'theoremCount': len(names), 'theoremNames': names, 'axiomAudit': printed,
        'allowedFoundationAxioms': ['propext', 'Quot.sound'],
        'inputHashes': before, 'inputsStable': True,
        'leanToolchain': (LEAN_ROOT / 'lean-toolchain').read_text().strip(),
        'scope': prepared['proofScope'],
        'nativeBinding': {'path': str(SOURCE), 'functionSha256': before['nativeFunction']},
        'DATAConfluenceOrGlobalIdempotenceAssumed': False,
        'notProved': prepared['nativeGaps'],
        'stdoutSha256': sha_bytes(result.stdout.encode()),
    }
    encoded = json.dumps(receipt, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
