#!/usr/bin/env python3
"""Check the standalone proposal. No project build or runtime change."""
import datetime
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import time

HERE = pathlib.Path(__file__).resolve().parent
TOOLCHAIN = 'leanprover/lean4:v4.33.1'
VERSION = '4.33.1'


def repository_root():
    for directory in HERE.parents:
        if (directory / 'spec/lean/lean-toolchain').is_file() and (directory / 'core').is_dir():
            return directory
    raise RuntimeError('Cannot find the repository root from this checker')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def child_limits():
    if hasattr(os, 'sched_getaffinity') and hasattr(os, 'sched_setaffinity'):
        os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
    if hasattr(os, 'nice'):
        os.nice(10)


def run(command, directory, environment):
    options = {'cwd': str(directory), 'env': environment, 'capture_output': True,
               'text': True, 'timeout': 60}
    if os.name == 'posix':
        options['preexec_fn'] = child_limits
    start = time.monotonic()
    result = subprocess.run(command, **options)
    return result, time.monotonic() - start


def main():
    root = repository_root()
    declared = (root / 'spec/lean/lean-toolchain').read_text().strip()
    if declared != TOOLCHAIN:
        raise RuntimeError('Expected pinned toolchain {}, found {}'.format(TOOLCHAIN, declared))
    lean = shutil.which('lean')
    if lean is None:
        raise RuntimeError('Lean is not available on PATH; use the cached pinned toolchain')
    environment = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN)
    version, _ = run([lean, '--version'], HERE, environment)
    if version.returncode != 0 or not re.search(r'\bversion ' + re.escape(VERSION) + r'\b', version.stdout):
        raise RuntimeError('The available Lean does not match {}: {}'.format(VERSION, version.stdout + version.stderr))

    # spec/lean/.gitignore already excludes .lake/. No proof output is written
    # beside the source or into another model's cached module directory.
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    verification = root / 'spec/lean/.lake/verification/query-replay' / stamp
    verification.mkdir(parents=True)
    environment['LEAN_PATH'] = str(verification)
    runs = []
    for name in ['QueryReplay', 'Audit']:
        command = [lean, '-j', '1', '-M', '768', '-o',
                   str(verification / (name + '.olean')), str(HERE / (name + '.lean'))]
        result, elapsed = run(command, HERE, environment)
        log = verification / (name + '.log')
        log.write_text(result.stdout + result.stderr)
        runs.append({
            'command': ['lean', '-j', '1', '-M', '768', '-o',
                        '<verification>/' + name + '.olean', name + '.lean'],
            'cwd': str(HERE.relative_to(root)),
            'exit_code': result.returncode, 'wall_seconds': elapsed,
            'log': str(log.relative_to(root)), 'log_sha256': sha(log),
            'source_sha256': sha(HERE / (name + '.lean')),
        })
        if result.returncode != 0:
            break

    source = (HERE / 'QueryReplay.lean').read_text()
    theorems = re.findall(r'^theorem (\w+)', source, re.M)
    pure_defs = [name for name in re.findall(r'^def (\w+)', source, re.M)
                 if name != 'checkControls']
    expected = {'QueryReplay.' + name for name in theorems + pure_defs}
    audit_path = verification / 'Audit.log'
    audit = audit_path.read_text() if audit_path.exists() else ''
    seen = set(re.findall(r"'([^']+)' (?:depends on axioms|does not depend on any axioms)", audit))
    dependencies = set()
    for declaration in re.findall(r'depends on axioms: \[([^\]]*)\]', audit):
        dependencies.update(part.strip() for part in declaration.split(',') if part.strip())
    allowed = {'propext', 'Quot.sound'}
    model_log = (verification / 'QueryReplay.log').read_text()
    checks = {
        'both_commands_exit_zero': len(runs) == 2 and all(row['exit_code'] == 0 for row in runs),
        'all_source_theorems_and_pure_definitions_audited': expected == seen,
        'only_allowed_kernel_axioms': dependencies <= allowed,
        'no_classical_choice_or_sorry_dependency': 'Classical.choice' not in dependencies and 'sorryAx' not in dependencies,
        'no_sorry_admit_or_custom_axiom_declaration': re.search(r'^\s*(?:sorry|admit|axiom)\b', source, re.M) is None,
        'fifteen_controls_pass_model': 'Query replay controls: 15 passed' in model_log,
        'fifteen_controls_pass_audit': 'Query replay controls: 15 passed' in audit,
        'expected_theorem_and_audit_counts': len(theorems) == 24 and len(expected) == 37,
        'preserved_original_model_bytes': sha(HERE / 'QueryReplay.lean') == '37fa7d73b17f43a50660c547851608c66c9f3e81b508b67308373d2bfbafb47a',
        'preserved_original_audit_bytes': sha(HERE / 'Audit.lean') == '779258e1bc8e76cb6f1cd9da58272bf3e2aa4ea736d8c5bccd22657bc03f5973',
    }
    base = pathlib.Path('core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi')
    runtime_sources = [base / 'engine/StrongQueries.kt', base / 'engine/RunMethodAnalyzer.kt',
                       base / 'store/RunSummaries.kt']
    receipt = {
        'state': 'PASS' if all(checks.values()) else 'FAILED',
        'status': 'PROPOSAL_NOT_IMPLEMENTED',
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'reference_revision': 'fcfe2e90558665d813bd74207832d4ae3fc83aec',
        'reference_core_tree': '57ca8d4940e8fb52e7eed6151928d4025c7d7ad9',
        'scope': 'Finite canonical-initial authorization transition; no whole-engine/source-adapter or runtime-saving theorem.',
        'toolchain': TOOLCHAIN, 'lean_version': version.stdout.strip(),
        'limits': {'Lean_workers': 1, 'CPU_affinity_count_on_supported_hosts': 1,
                   'Lean_memory_MiB': 768, 'command_timeout_seconds': 60},
        'verification_directory': str(verification.relative_to(root)),
        'verification_outputs_gitignored': True,
        'checks': checks, 'theorem_count': len(theorems), 'theorems': theorems,
        'audited_declaration_count': len(expected), 'pure_definitions': pure_defs,
        'control_count': 15, 'observed_axioms': sorted(dependencies),
        'model_sha256': sha(HERE / 'QueryReplay.lean'),
        'audit_sha256': sha(HERE / 'Audit.lean'),
        'checker_sha256': sha(pathlib.Path(__file__).resolve()),
        'README_sha256': sha(HERE / 'README.md'),
        'runtime_source_sha256_at_check': {str(path): sha(root / path) for path in runtime_sources},
        'runs': runs,
        'not_proved': ['AP geometry/subsumption laws', 'whole-engine/source-adapter correspondence',
                       'regular raw-delta delivery/fairness', 'performance factor',
                       'broader StrongQueries policy removal', 'a new runtime candidate index'],
    }
    (HERE / 'checks.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'state': receipt['state'], 'theorems': len(theorems),
                      'audited_declarations': len(expected), 'controls': 15,
                      'checks': checks, 'axioms': sorted(dependencies),
                      'verification_directory': str(verification.relative_to(root))}, indent=2))
    if not all(checks.values()):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
