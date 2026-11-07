#!/usr/bin/env python3
"""Repeat the local component checks; this is not a native analyzer proof."""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
LEAN = HERE.parent.parent
REPO = LEAN.parent.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def uncomment(source):
    result, cursor, depth = [], 0, 0
    while cursor < len(source):
        if source.startswith('/-', cursor):
            depth += 1
            cursor += 2
        elif depth and source.startswith('-/', cursor):
            depth -= 1
            cursor += 2
        elif depth:
            result.append('\n' if source[cursor] == '\n' else ' ')
            cursor += 1
        elif source.startswith('--', cursor):
            end = source.find('\n', cursor)
            cursor = len(source) if end < 0 else end
        else:
            result.append(source[cursor])
            cursor += 1
    assert depth == 0, 'Unclosed Lean comment'
    return ''.join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-directory', type=Path, required=True)
    args = parser.parse_args()
    out = args.output_directory.resolve()
    assert not out.exists(), 'Keep old receipts; select a new output directory.'
    manifest = json.loads((HERE / 'manifest.json').read_text())
    sources = {module: REPO / entry['source']
               for module, entry in manifest['modules'].items()}

    def verify_pins():
        for module, entry in manifest['modules'].items():
            assert sha(sources[module]) == entry['sha256'], module
        for entry in manifest['baselineHelpers']:
            assert sha(REPO / entry['source']) == entry['sha256'], entry['source']
        assert sha(Path(__file__)) == manifest['checkerSha256']

    verify_pins()
    out.mkdir(parents=True)
    receipt = dict(state='STARTED', proofScope=manifest['proofScope'],
                   nativeAnalyzerProved=False, allPrincipalProgramsProved=False,
                   checkedAtUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   manifestSha256=sha(HERE / 'manifest.json'), runs=[], theoremAxioms=[])

    def run(module, command, env):
        result = subprocess.run(command, cwd=LEAN, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = out / (module + '.log')
        log.write_text(result.stdout)
        receipt['runs'].append(dict(module=module, exitCode=result.returncode,
                                    logSha256=sha(log)))
        assert result.returncode == 0, f'{module}: see {log}'
        assert 'sorryAx' not in result.stdout, f'{module}: unexpected proof hole'
        assert not re.search(r'\berror(?:\([^)]*\))?:', result.stdout), module
        return result.stdout

    try:
        env = dict(os.environ, LEAN_PATH=str(out))
        run('BaselineImports', ['lake', 'build', 'ApSpec.CorrelatedConcreteImplementation'], env)
        for module, source in sources.items():
            code = uncomment(source.read_text())
            assert not re.search(r'\b(?:sorry|admit|axiom|Classical|noncomputable|unsafe|partial)\b', code), module
            run(module, ['lake', 'env', 'lean', '--root=' + str(source.parent),
                         '-M2048', '-o', str(out / (module + '.olean')), str(source)], env)

        expected = [name for entry in manifest['modules'].values()
                    for name in entry['checkedTheorems']]
        audit = out / 'Audit.lean'
        audit.write_text(''.join(f'import {module}\n' for module in sources)
                         + ''.join(f'#print axioms {name}\n' for name in expected))
        output = run('Audit', ['lake', 'env', 'lean', '--root=' + str(out),
                              '-M2048', str(audit)], env)
        found = re.findall(r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)", output, re.M)
        assert found == expected, 'The axiom audit must include each declared theorem.'
        for name, dependencies in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.S):
            used = sorted(filter(None, dependencies.replace('\n', '').replace(' ', '').split(',')))
            assert set(used) <= {'propext', 'Quot.sound'}, (name, used)
            receipt['theoremAxioms'].append(dict(theorem=name, axioms=used))
        for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
            receipt['theoremAxioms'].append(dict(theorem=name, axioms=[]))
        assert len(receipt['theoremAxioms']) == len(expected)
        verify_pins()
        receipt.update(state='PASS_LOCAL_COMPONENTS_ONLY', checkedTheorems=len(expected))
    except Exception as error:
        receipt.update(state='FAILED_NO_PROOF_CLAIM', error=repr(error))
        (out / 'checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
        raise
    (out / 'checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in ('state', 'checkedTheorems',
                                                  'allPrincipalProgramsProved')}, indent=2))


if __name__ == '__main__':
    main()
