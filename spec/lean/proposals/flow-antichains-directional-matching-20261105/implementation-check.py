#!/usr/bin/env python3
"""Kernel-check selected laws and their implementation bridge; pin native sources only.

This checker does not prove Kotlin correspondence or whole-engine completeness.
The original proposal checker retains its unchanged-runtime reference boundary.
"""
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'spec/lean/lean-toolchain').is_file())
MODULES = ['Canonical', 'Relations', 'Matching', 'Reachability', 'Implementation']
TOOLCHAIN = 'leanprover/lean4:v4.33.1'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    scanner_file = ROOT / 'spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py'
    spec = importlib.util.spec_from_file_location('declaration_scanner', scanner_file)
    scanner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(scanner)
    names, counts = [], {}
    for module in MODULES:
        raw = (HERE / (module + '.lean')).read_text()
        clean = scanner.uncomment(raw)
        assert not re.search(r'\b(?:axiom|sorry|admit|unsafe|partial|noncomputable|native_decide|Classical)\b', clean)
        assert all(n in ['Std'] + MODULES for n in re.findall(r'^import\s+(\S+)', clean, re.M))
        declarations, counts[module] = scanner.declarations(raw)
        names.extend(declarations)
    assert len(names) == len(set(names))
    assert (ROOT / 'spec/lean/lean-toolchain').read_text().strip() == TOOLCHAIN
    sources = list((ROOT / 'core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi').rglob('*.kt'))
    inputs = [HERE / (n + '.lean') for n in MODULES] + [Path(__file__).resolve(), scanner_file,
        ROOT / 'spec/proof-guide.md', ROOT / 'spec/impl-proposal-guide.md',
        ROOT / 'spec/lean/lean-toolchain',
        ROOT / 'docs/design/bidirectional-canonical-facts-normal-relations-directional-inside-implementation-20261105.md']
    pins = {str(p.relative_to(ROOT)): sha(p) for p in inputs + sources}
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    work = ROOT / 'spec/lean/.lake/verification/flow-antichains-directional-matching-20261105' / ('implementation-' + stamp)
    work.mkdir(parents=True)
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_PATH=str(work))
    lean = shutil.which('lean')
    assert lean
    version = subprocess.check_output([lean, '--version'], env=env, text=True).strip()
    assert 'version 4.33.1' in version

    def limits():
        if hasattr(os, 'sched_getaffinity'):
            os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})

    def run(args, log):
        result = subprocess.run(args, cwd=HERE, env=env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=180, preexec_fn=limits)
        (work / log).write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r'\b(?:error|warning):', result.stdout), result.stdout
        return result.stdout

    for module in MODULES:
        run([lean, '-j', '1', '-M', '900', '-o', str(work / (module + '.olean')),
             str(HERE / (module + '.lean'))], module + '.log')
    audit = work / 'Audit.lean'
    audit.write_text(''.join('import ' + n + '\n' for n in MODULES) +
                     ''.join('#print axioms ' + n + '\n' for n in names))
    output = run([lean, '-j', '1', '-M', '900', str(audit)], 'Audit.log')
    found = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", output))
    assert found == set(names)
    axioms = set()
    for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output):
        axioms.update(n.strip() for n in group.split(',') if n.strip())
    assert axioms <= {'propext', 'Quot.sound'}, axioms
    assert all(sha(ROOT / name) == value for name, value in pins.items()), 'Inputs changed during check'
    (HERE / 'implementation-audit.txt').write_text(output)
    receipt = {'status': 'IMPLEMENTATION_LAWS_PASS', 'utc': stamp, 'leanVersion': version,
        'moduleTheoremCounts': counts, 'theoremCount': sum(counts.values()),
        'auditedDeclarationCount': len(names), 'axioms': sorted(axioms), 'inputsStable': True,
        'sourceHashes': pins, 'scope': [
            'Constructive spatial, correlated-relation, directional-filter and finite-path models.',
            'Transitive masked FLOW cover, implicit specialization and cofinite union bridge.',
            'Native Kotlin sources are pinned, not kernel-verified.',
            'No whole-engine finding, convergence, scheduling or performance theorem.'],
        'auditSha256': sha(HERE / 'implementation-audit.txt')}
    (HERE / 'implementation-checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ['status', 'theoremCount', 'auditedDeclarationCount', 'axioms', 'inputsStable']}, indent=2))


if __name__ == '__main__':
    main()
