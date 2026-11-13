#!/usr/bin/env python3
"""Bind all selected native row-service witnesses to constructive Lean guards.

Generated data, source batches, objects and logs stay in the external archive.
This does not accept classifications or alter the campaign ledger.
"""
import argparse
import collections
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
POINT = {'This', 'Return', 'Argument', 'LocalVar', 'Exception'}
ORDINARY = {'This', 'Return', 'Argument', 'LocalVar'}
TAILS = {'EXACT': 'exact', 'STAR': 'star', 'ANY': 'may', 'ANY_TAINT': 'must'}


def can(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':'), ensure_ascii=False)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(path):
    with gzip.open(path, 'rt') as stream:
        return [json.loads(line) for line in stream]


def write(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def dictionary(values):
    keys = sorted({can(value) for value in values})
    return {key: i for i, key in enumerate(keys)}, [json.loads(key) for key in keys]


def point_base(entry):
    kind = entry['baseType'].rsplit('$', 1)[-1]
    if kind == 'ClassStatic':
        path = entry['path']
        return (len(path) >= 2 and path[0]['kind'] == 'CLASS' and path[1]['kind'] == 'FIELD') or (
            len(path) == 1 and path[0]['kind'] == 'CLASS' and entry['tail'] == 'EXACT')
    return kind in POINT


def base_key(entry):
    return {k: v for k, v in entry.items() if k not in ('path', 'tail', 'mark', 'E')}


def owner_key(project, row):
    return [project, {k: v for k, v in row['unit'].items() if k != 'exit'}]


def output_key(row):
    result = {k: v for k, v in row.items() if k != 'entry'}
    out = result.get('exit')
    if out is not None and out['tail'] == 'ANY' and not out['E']:
        result['exit'] = dict(out, tail='STAR')
    return result


def lean_list(xs):
    return '[' + ','.join(str(x) for x in xs) + ']'


def run_model(build, name, expected):
    command = ['elan', 'run', 'leanprover/lean4:v4.33.1', 'lean',
               '-o', str((build / name).with_suffix('.olean')), name]
    result = subprocess.run(command, cwd=build, env=dict(os.environ, LEAN_PATH=str(build)),
                            text=True, capture_output=True)
    output = result.stdout + result.stderr
    (build / (name + '.txt')).write_text(output)
    assert result.returncode == 0, (name, output)
    audits = re.findall(r"^'[^']+' (?:does not depend on any axioms|depends on axioms: \[[^\]]*\])", output, re.M)
    assert len(audits) == expected, (name, expected, audits)
    for audit in audits:
        if 'does not depend' in audit:
            continue
        axioms = re.search(r'\[([^\]]*)\]', audit).group(1)
        assert {x.strip() for x in axioms.split(',')} <= {'propext', 'Quot.sound'}, audit
    assert 'sorryAx' not in output and 'Classical.choice' not in output
    return dict(source=name, sourceSha256=sha(build / name), logSha256=sha(build / (name + '.txt')),
                objectSha256=sha((build / name).with_suffix('.olean')), audits=expected, exitCode=0)


def build(campaign, out, batch_size):
    assert not out.exists(), 'Use a fresh external result directory.'
    out.mkdir(parents=True)
    manifest = json.loads((campaign / 'manifest.json').read_text())
    assert manifest['runtime'] == '14d7b63369d94f49d4c551be8405ed7719f267cc'
    ledger_path = campaign / 'ledger.jsonl.gz'
    ledger = read(ledger_path)
    targets = [row for row in ledger if row.get('knownPatternCandidate')]
    assert targets, 'No selected service candidates.'
    pins = {str(ledger_path): sha(ledger_path), str(campaign / 'manifest.json'): sha(campaign / 'manifest.json')}
    originals = {}
    for project, run in [('OWASP', 11), ('conductor', 7), ('Stirling-PDF', 9)]:
        path = campaign / f'snapshots/{project}/run-{run}-post-handoff.jsonl.gz'
        pins[str(path)] = sha(path)
        for record in read(path):
            row = record['edge']
            rid = record['edgeId']
            assert hashlib.sha256(can(row).encode()).hexdigest() == rid
            key = (project, rid)
            assert key not in originals
            originals[key] = row
    original_keys = sorted(originals)
    native_ids = {key: i for i, key in enumerate(original_keys)}
    relevant, triples = set(), []
    for target in targets:
        project, rid = target['project'], target['rowId']
        x = (project, rid)
        assert originals[x] == target['row']
        z = (project, target['knownPatternCandidate']['c2']['rowId'])
        y = (project, target['knownPatternCandidate']['c5']['rowId'])
        assert x != z and x != y and z in originals and y in originals
        relevant.update((x, z, y))
        triples.append((target, (x, z, y)))
    relevant = sorted(relevant)
    data = [(project, rid, originals[project, rid]) for project, rid in relevant]
    # Every non-geometric entry coordinate remains part of its opaque base key.
    control_base = {'controlBase': True}
    control_mark = {'controlMark': True}
    bases, base_values = dictionary([control_base] + [base_key(r['entry']) for _, _, r in data if r.get('entry')])
    marks, mark_values = dictionary([control_mark] + [r['entry']['mark'] for _, _, r in data if r.get('entry')])
    owners, owner_values = dictionary([owner_key(p, r) for p, _, r in data])
    ports, port_values = dictionary([r['unit'].get('exit', 'METHOD_EXIT') for _, _, r in data])
    outputs, output_values = dictionary([output_key(r) for _, _, r in data])
    accessors = {}
    for _, _, row in data:
        entry = row.get('entry')
        if entry:
            for accessor in entry['path'] + entry['E']:
                assert accessor['kind'] in ('CLASS', 'FIELD', 'ELEMENT')
                accessors[can(accessor)] = accessor
    # Parity is only the finite test encoding. The generic transport theorem
    # leaves classification outside stored guard words arbitrary.
    accessor_ids, accessor_values = {}, []
    counters = collections.Counter()
    for key, accessor in sorted(accessors.items()):
        counted = accessor['kind'] != 'CLASS'
        code = counters[counted] * 2 + int(counted)
        counters[counted] += 1
        accessor_ids[key] = code
        accessor_values.append(dict(id=code, value=accessor, counted=counted))

    def entry_value(row):
        e = row.get('entry')
        if e is None:
            kind = {'Zero': 'zero', 'Target': 'target'}[row['entryKind']]
            return f'⟨.{kind},{bases[can(control_base)]},false,false,[],.other {marks[can(control_mark)]},.exact,[]⟩'
        mark = e['mark']
        if mark == {'kind': 'FLOW', 'mx': []}:
            mark_text = '.flow'
        elif mark['kind'] == 'CONCRETE' and mark['value']['kind'] == 'Full':
            mark_text = '.full ' + str(marks[can(mark)])
        else:
            mark_text = '.other ' + str(marks[can(mark)])
        args = ['.data', str(bases[can(base_key(e))]), str(bool(point_base(e))).lower(),
                str(e['baseType'].rsplit('$', 1)[-1] in ORDINARY).lower(),
                lean_list(accessor_ids[can(a)] for a in e['path']), mark_text, '.' + TAILS[e['tail']],
                lean_list(accessor_ids[can(a)] for a in e['E'])]
        return '⟨' + ','.join(args) + '⟩'

    def row_value(key):
        p, _ = key
        r = originals[key]
        kind = '.data' if r.get('exit') is not None else '.zero'
        assert kind == '.data' or r.get('exitKind') == 'Zero'
        args = [str(native_ids[key]), str(owners[can(owner_key(p, r))]),
                str(ports[can(r['unit'].get('exit', 'METHOD_EXIT'))]), kind,
                entry_value(r), str(outputs[can(output_key(r))])]
        return '⟨' + ','.join(args) + '⟩'

    codebook = dict(schema='ObservedDemandRowGuardCodebook-v1', originalKeys=original_keys,
                    bases=base_values, marks=mark_values, owners=owner_values, ports=port_values,
                    outputs=output_values, accessors=accessor_values,
                    relevantRows=[dict(project=p, rowId=rid, nativeKey=native_ids[p, rid],
                                       row=originals[p, rid], lean=row_value((p, rid))) for p, rid in relevant],
                    inputs=pins, dictionaryKeysInjective=True,
                    actualClassifierAgreementOnStoredWords=True, futureClassifierNotBoundByParity=True)
    write(out / 'codebook.json', codebook)
    write(out / 'triples.json', [dict(targetId=t['targetId'], project=t['project'],
          rowIds=[key[1] for key in keys], nativeKeys=[native_ids[key] for key in keys]) for t, keys in triples])
    build_dir = out / 'lean'
    build_dir.mkdir()
    sources = [('AncestorMayPointQuery.lean', 17), ('RetainedServiceBasis.lean', 28),
               ('RowCut.lean', 9), ('ObservedRowGuards.lean', 7)]
    results = []
    for name, audits in sources:
        (build_dir / name).write_bytes((HERE / name).read_bytes())
        results.append(run_model(build_dir, name, audits))
    batches = []
    for start in range(0, len(triples), batch_size):
        selected = triples[start:start + batch_size]
        name = f'ObservedBatch{start // batch_size:04d}.lean'
        lines = ['import ObservedRowGuards', 'set_option maxRecDepth 100000',
                 'set_option maxHeartbeats 0', 'namespace RetainedDemandRowCut.Observed.Corpus',
                 'open RetainedServiceBasis', 'def finiteCounted (n : Nat) : Bool := n % 2 == 1',
                 'def triples : List Triple := [']
        lines += [('  ⟨' + ','.join(row_value(key) for key in keys) + '⟩' +
                   (',' if i + 1 < len(selected) else '')) for i, (_, keys) in enumerate(selected)]
        lines += [']', f'theorem observed_guards : checkBatch finiteCounted {len(originals)} triples = true := by decide',
                  '#print axioms observed_guards', 'end RetainedDemandRowCut.Observed.Corpus']
        (build_dir / name).write_text('\n'.join(lines) + '\n')
        model = run_model(build_dir, name, 1)
        results.append(model)
        batches.append(dict(source=name, first=start, count=len(selected),
                            targetIds=[t['targetId'] for t, _ in selected]))
        print(json.dumps(dict(batch=len(batches), processed=start + len(selected), total=len(triples))), flush=True)
    assert all(sha(Path(path)) == value for path, value in pins.items()), 'Inputs changed during proof.'
    receipt = dict(schema='ObservedDemandRowGuardBinding-v1', status='ALL_SELECTED_NATIVE_ROW_GUARDS_PROVED',
                   candidates=len(triples), relevantRows=len(relevant), originalRows=len(originals),
                   perProject=dict(collections.Counter(t['project'] for t, _ in triples)),
                   batchSize=batch_size, batches=batches, compiledModels=results,
                   actualAxiomAudits=sum(m['audits'] for m in results),
                   allowedAxioms=['propext', 'Quot.sound'], inputs=pins,
                   source=sha(Path(__file__)), genericProofReceipt=sha(HERE / 'receipt.json'),
                   codebookSha256=sha(out / 'codebook.json'), triplesSha256=sha(out / 'triples.json'),
                   actualClassifierTransportProved=True, guardTrueByKernelReduction=True,
                   fullTypedKeysInjective=True, distinctRowWitnesses=True,
                   individualCutsOnly=True, jointCutAccepted=False,
                   productionModified=False, ledgerModified=False,
                   classificationsAccepted=False, nativeTestsRerun=False,
                   finiteGuardChecksAreNotFutureProof=True)
    write(out / 'receipt.json', receipt)
    print(json.dumps({k: v for k, v in receipt.items() if k not in ('batches', 'compiledModels', 'inputs')}, sort_keys=True))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--campaign', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--batch-size', type=int, default=32)
    args = parser.parse_args()
    assert args.batch_size > 0
    build(args.campaign.resolve(), args.out.resolve(), args.batch_size)
