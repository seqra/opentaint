#!/usr/bin/env python3
"""Check the exported finite domain and generate constructive Q certificates.

All emissions outside the explicitly captured target/anchor support remain
an arbitrary function parameter. This script never substitutes empty rows
for the other ~90,000 outgoing edges and never edits the campaign ledger.
"""
from pathlib import Path
import argparse
import collections
import datetime
import gzip
import hashlib
import importlib.util
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'spec/lean/lean-toolchain').is_file())
MODEL = HERE / 'UnchangedProjectionCover.lean'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False)


def digest(value):
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def jsonl(path):
    with gzip.open(path, 'rt') as stream:
        yield from (json.loads(line) for line in stream)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-directory', type=Path, required=True)
    parser.add_argument('--output-source', type=Path, required=True)
    parser.add_argument('--output-directory', type=Path, required=True)
    args = parser.parse_args()
    folder, source_path, output = args.input_directory.resolve(), args.output_source.resolve(), args.output_directory.resolve()
    output.mkdir(parents=True, exist_ok=True)
    source_path.parent.mkdir(parents=True, exist_ok=True)
    domain_path = folder / 'domain.json'
    domain = json.loads(domain_path.read_text())
    assert domain['predicate'] == 'UnchangedProjectionCover' and domain['version'] == 1
    assert not domain['ledgerModified'] and not domain['productionModified']
    for ref in domain['sourceArtifacts'] + domain['artifacts']:
        assert sha(ROOT / ref['path']) == ref['sha256'], 'Changed source artifact: ' + ref['path']
    formal_path = ROOT / domain['formalGenericReceipt']['path']
    formal = json.loads(formal_path.read_text())
    assert sha(formal_path) == domain['formalGenericReceipt']['sha256']
    assert formal['modelSha256'] == sha(MODEL)
    assert all(r['exitCode'] == 0 for r in formal['runs']) and formal['axiomAudit']['exitCode'] == 0
    # Use the archived input ledger. Acceptance changes the live ledger later.
    ledger_refs = [r for r in domain['sourceArtifacts'] if r['path'].endswith('/input-ledger.jsonl.gz')]
    assert len(ledger_refs) == 1, 'An immutable input-ledger archive is required'
    archived_ledger = ROOT / ledger_refs[0]['path']
    assert sha(archived_ledger) == domain['sourceLedgerSha256']
    targets = list(jsonl(archived_ledger))
    target_pairs = {(r['project'], r['edgeId']) for r in targets}
    assert len(target_pairs) == len(targets) == domain['globalTargetUniverse']
    target_by_id = {r['targetId']: r for r in targets}
    index = collections.defaultdict(dict)
    edge_ids = collections.defaultdict(set)
    for value in jsonl(folder / 'edge-index.jsonl.gz'):
        project, number, eid = value['project'], value['edgeNumber'], value['edgeId']
        assert number not in index[project] and eid not in edge_ids[project]
        assert value['fullEdgeHash'] == eid
        assert value['isRepeated'] == ((project, eid) in target_pairs)
        index[project][number] = value
        edge_ids[project].add(eid)
    encoding_path = folder / 'projection-encoding.json'
    encoding = json.loads(encoding_path.read_text())
    assert encoding['injective']
    encoded = {}
    full_keys = set()
    for row in encoding['rows']:
        rank = row['rank']
        assert rank not in encoded and canonical(row['payload']) not in full_keys
        assert digest(row['payload']) == row['fullProjectionId']
        encoded[rank] = row
        full_keys.add(canonical(row['payload']))
    assert set(encoded) == set(range(len(encoded)))
    assert len({r['fullProjectionId'] for r in encoded.values()}) == len(encoded)
    certificates = list(jsonl(folder / 'certificates.jsonl.gz'))
    assert len(certificates) == domain['totalCandidates']
    assert len({c['targetId'] for c in certificates}) == len(certificates)
    by_project = collections.defaultdict(list)
    project = load('native_projection', ROOT / 'docs/reports/data/redundant-demand-20261110/tools/decode.py').project
    used_rank = set()
    for name, info in domain['projects'].items():
        total, cut, repeated = info['totalOutgoing'], info['nonRepeatedCut'], info['repeatedCount']
        assert cut + repeated == total
        assert set(index[name]) == set(range(total))
        for number, row in index[name].items():
            assert row['isRepeated'] == (number >= cut)
        assert sum(1 for p, _ in target_pairs if p == name) == repeated
        known = {v['edgeNumber']: v for v in info['knownEmit']}
        assert len(known) == len(info['knownEmit'])
        for number, row in known.items():
            assert 0 <= number < total and index[name][number]['edgeId'] == row['edgeId']
            actual = row['actualRecord']
            assert actual['edgeId'] == row['edgeId'] == digest(actual['edge'])
            native_rows = collections.Counter(canonical(q) for q in project(actual['edge']))
            known_rows = collections.Counter()
            for rank in row['projectionRanks']:
                payload = encoded[rank]['payload']
                assert payload['project'] == name
                assert payload['projection']['unit']['methodId'] == actual['edge']['unit']['methodId']
                known_rows[canonical(payload['projection'])] += 1
                used_rank.add(rank)
            assert native_rows == known_rows, 'Known emission is not the complete native projection'
        info['knownByNumber'] = known
    for cert in certificates:
        name, number = cert['project'], cert['edgeNumber']
        info = domain['projects'][name]
        known = info['knownByNumber']
        assert number in info['Q'] and info['nonRepeatedCut'] <= number < info['totalOutgoing']
        assert target_by_id[cert['targetId']]['edgeId'] == cert['edgeId'] == index[name][number]['edgeId']
        assert target_by_id[cert['targetId']]['edge'] == cert['original']['edge']
        assert cert['earlierRun'] >= 3 and cert['laterRun'] == cert['removalBarrier'] == info['removalBarrier']
        assert cert['nativeProjectionRecomputed']
        assert {w['projectionRank'] for w in cert['witnesses']} == set(known[number]['projectionRanks'])
        for w in cert['witnesses']:
            anchor, rank = w['anchorNumber'], w['projectionRank']
            assert 0 <= anchor < info['nonRepeatedCut']
            assert w['anchorEdgeId'] == known[anchor]['edgeId'] == index[name][anchor]['edgeId']
            assert (name, w['anchorEdgeId']) not in target_pairs
            assert w['anchor']['edge'] == known[anchor]['actualRecord']['edge']
            assert w['fullProjection'] == encoded[rank]['payload']
            assert rank in known[anchor]['projectionRanks']
        by_project[name].append(cert)
    assert used_rank == set(encoded)
    lines = [MODEL.read_text(), '\nnamespace UnchangedProjectionCover.Observed\n',
             'set_option maxRecDepth 8192\nset_option maxHeartbeats 10000000\n']
    theorem_names, mapping = [], []
    for name, info in domain['projects'].items():
        namespace = 'P_' + re.sub('[^A-Za-z0-9_]', '_', name)
        prefix = 'UnchangedProjectionCover.Observed.' + namespace + '.'
        lines.append('namespace ' + namespace + '\n')
        lines.append('def O : List Edge := List.range ' + str(info['totalOutgoing']) + '\n')
        lines.append('def U : List Edge := List.range\' ' + str(info['nonRepeatedCut']) + ' ' + str(info['repeatedCount']) + '\n')
        known = info['knownByNumber']
        def qs(values):
            return '[' + ', '.join('encodedRow ' + str(v) for v in values) + ']'
        lines.append('def known : List (Edge × List Projection) := [' + ', '.join(
            '(' + str(number) + ', ' + qs(row['projectionRanks']) + ')' for number, row in sorted(known.items())) + ']\n')
        lines.append('def emit (rest : Edge → List Projection) := withKnownRows known rest\n')
        for number, row in sorted(known.items()):
            lemma = 'known_' + str(number)
            lines.append('theorem ' + lemma + ' (rest : Edge → List Projection) : emit rest ' + str(number) + ' = ' + qs(row['projectionRanks']) + ' := by\n')
            lines.append('  exact withKnownRows_of_lookup known rest ' + str(number) + ' ' + qs(row['projectionRanks']) + ' (by decide)\n')
            theorem_names.append(prefix + lemma)
        certs = sorted(by_project[name], key=lambda c: c['edgeNumber'])
        assert {c['edgeNumber'] for c in certs} == set(info['Q'])
        assert {c['targetId'] for c in certs} == set(info['QTargetIds'])
        for i, cert in enumerate(certs):
            witness_values = ', '.join('⟨encodedRow ' + str(w['projectionRank']) + ', ' + str(w['anchorNumber']) + '⟩' for w in cert['witnesses'])
            lines.append('-- target ' + cert['targetId'] + '\n')
            lines.append('def c' + str(i) + ' : Certificate := ⟨' + str(cert['edgeNumber']) + ', [' + witness_values + ']⟩\n')
            lemma = 'checked_' + str(i)
            lines.append('theorem ' + lemma + ' (rest : Edge → List Projection) : check (emit rest) O U c' + str(i) + ' = true := by\n')
            lemmas = ['known_' + str(cert['edgeNumber'])] + ['known_' + str(w['anchorNumber']) for w in cert['witnesses']]
            lines.append('  simp [check, c' + str(i) + ', O, U, List.mem_range, List.mem_range\'_1, ' + ', '.join(sorted(set(lemmas))) + ', validWitness]\n')
            theorem_names.append(prefix + lemma)
            mapping.append({'targetId': cert['targetId'], 'project': name,
                            'edgeNumber': cert['edgeNumber'], 'theorem': prefix + lemma})
        lines.append('def certificates : List Certificate := [' + ', '.join('c' + str(i) for i in range(len(certs))) + ']\n')
        lines.append('def Q := certificates.map Certificate.target\n')
        lines.append('theorem checked_all (rest : Edge → List Projection) : checkAll (emit rest) O U Q certificates = true := by\n')
        if certs:
            lines.append('  apply checkAll_mapped_targets\n  intro c hc\n  simp only [certificates, List.mem_cons, List.not_mem_nil, or_false] at hc\n')
            lines.append('  rcases hc with ' + ' | '.join('rfl' for _ in certs) + '\n')
            lines.extend('  · exact checked_' + str(i) + ' rest\n' for i in range(len(certs)))
        else:
            lines.append('  simp [Q, certificates, checkAll]\n')
        lines.append('theorem joint_projection (rest : Edge → List Projection) (R : List Edge)\n    (hR : ∀ e ∈ R, e ∈ U) (q : Projection) :\n    HasProjection (emit rest) (without (without O R) Q) q ↔ HasProjection (emit rest) (without O R) q := by\n  exact projection_set_unchanged (emit rest) O U R Q certificates (checked_all rest) hR q\n')
        lines.append('theorem joint_state {Stable : Type} (stable : Stable) (rest : Edge → List Projection)\n    (R : List Edge) (hR : ∀ e ∈ R, e ∈ U) :\n    buildState stable (emit rest) (without (without O R) Q) = buildState stable (emit rest) (without O R) := by\n  exact semantic_state_unchanged stable (emit rest) O U R Q certificates (checked_all rest) hR\n')
        lines.append('theorem joint_future {Stable Observation : Type} (stable : Stable) (rest : Edge → List Projection)\n    (R : List Edge) (hR : ∀ e ∈ R, e ∈ U) (step : State Stable → State Stable)\n    (observe : State Stable → Observation) (n : Nat) :\n    observe (run step n (buildState stable (emit rest) (without (without O R) Q))) =\n      observe (run step n (buildState stable (emit rest) (without O R))) := by\n  exact future_observations_unchanged stable (emit rest) O U R Q certificates (checked_all rest) hR step observe n\n')
        theorem_names.extend(prefix + value for value in ['checked_all', 'joint_projection', 'joint_state', 'joint_future'])
        lines.append('end ' + namespace + '\n')
    lines.append('end UnchangedProjectionCover.Observed\n')
    lines.extend('#print axioms ' + name + '\n' for name in theorem_names)
    generated = ''.join(lines)
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b|\bClassical\.|^\s*axiom\b', generated, re.M)
    source_path.write_text(generated)
    command = ['lake', 'env', 'lean', str(source_path)]
    result = subprocess.run(command, cwd=ROOT / 'spec/lean', text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = output / 'observed-lean.txt'
    log.write_text(result.stdout)
    assert result.returncode == 0, result.stdout
    dependencies = set()
    for line in result.stdout.splitlines():
        if 'depends on axioms:' in line:
            dependencies.update(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', line.split('depends on axioms:')[1]))
    assert dependencies <= {'propext', 'Quot.sound'}
    for name in theorem_names:
        assert name in result.stdout, 'Missing observed theorem audit: ' + name
    receipt = {
        'schema': 'redundant-demand-unchanged-projection-observed-lean-v1',
        'createdAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'predicate': 'UnchangedProjectionCover', 'version': 1,
        'domainSha256': sha(domain_path), 'genericModelSha256': sha(MODEL),
        'generatorSha256': sha(Path(__file__)),
        'source': str(source_path.relative_to(ROOT)), 'sourceSha256': sha(source_path),
        'command': command, 'exitCode': result.returncode, 'log': log.name, 'logSha256': sha(log),
        'actualEdgeCertificates': len(mapping),
        'knownEmissions': sum(len(p['knownEmit']) for p in domain['projects'].values()),
        'fullProjectionDictionarySize': len(encoded),
        'fullProjectionEncodingInjective': True,
        'allObservedTheoremsAudited': len(theorem_names), 'axiomDependencies': sorted(dependencies),
        'allUnlistedEmissionsRemainArbitrary': True,
        'projects': {name: {k: value[k] for k in ['totalOutgoing', 'nonRepeatedCut', 'repeatedCount', 'Q']}
                     for name, value in domain['projects'].items()},
        'targetTheorems': mapping, 'sourceArtifacts': domain['sourceArtifacts'],
        'latestRuns': domain['latestRuns'],
        'nativeSourceCorrespondenceFromDomainReceipt': domain['nativeReceipt'],
        'ledgerModified': False, 'productionModified': False,
    }
    (output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ['actualEdgeCertificates', 'knownEmissions',
                                           'fullProjectionDictionarySize', 'allObservedTheoremsAudited',
                                           'allUnlistedEmissionsRemainArbitrary']}))


if __name__ == '__main__':
    main()
