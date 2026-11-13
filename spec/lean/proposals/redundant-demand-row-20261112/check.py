#!/usr/bin/env python3
"""Compile the constructive row-cut kernel and audit its actual dependencies.

This checks generic laws and controls, not campaign corpus classifications.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import xml.etree.ElementTree as ET
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'demand-task.md').is_file())
RUNTIME = '14d7b63369d94f49d4c551be8405ed7719f267cc'
KERNEL_ORIGIN = ('docs/reports/data/redundant-demand-20261110/cases/'
                 'retained-service-basis-kernel-v1/lean/')
SOURCES = {
    'AncestorMayPointQuery.lean': ('b29e58ea82bd91437cf0f90cc90baa20bd2a81a99ccf75fc6f2afb7d5a195787', 17),
    'RetainedServiceBasis.lean': ('e573c90914f38555679402343b355315e77d42db7f6f6dce95ba04c7e448d54a', 28),
    'RowCut.lean': (None, 9),
    'RowCutControls.lean': (None, 11),
    'ObservedRowGuards.lean': (None, 7),
}
OPERATOR_PINS = {
    'ap/RestrictedInitialPolicy.kt': '8473d936c94d3e96c543e495309da53501098ad2a69fc29c82f3e3a32f392cbd',
    'store/DemandStore.kt': 'a664e74e3c32f2d07f9b18ef626cd46c8f44d857ea7798e95a80795a91737e68',
    'store/FrozenDemandTrie.kt': 'f260e08cbde6024c1aacca83e21d8c90c4d6116504eeecf22edb64e6bfd52b62',
    'store/PreparedOutputPrograms.kt': '682b774936ee5cc56857a4d2be79e4ccb59778fb05cc475203f347f403c2a747',
    'engine/LoopConsumerObservation.kt': '6d98f705f055f6223ab97a061dd278a41fb0d5797375c4189b19b2691555518c',
    'engine/LoopOutputRestriction.kt': 'c9381026696953188374d5fa4f170f252967ffcbfcf5903792a05623d82f7c28',
}
NATIVE_RECEIPT = ('docs/reports/data/redundant-demand-20261110/cases/'
                  'retained-service-basis-native-v1/receipt.json')
NATIVE_RECEIPT_SHA = 'c8093cda966e140ec70d47aa94121be7de92f1136c06fb879b63297f21694e53'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def historical_native_correspondence():
    archive = json.loads((ROOT / 'docs/reports/external-data.json').read_text())
    base = ROOT / NATIVE_RECEIPT
    if not base.exists():
        base = Path(archive['archiveRoot']) / NATIVE_RECEIPT
    assert sha(base.read_bytes()) == NATIVE_RECEIPT_SHA
    native = base.parent
    campaign = native.parents[1]
    receipt = json.loads(base.read_text())
    assert receipt['status'] == 'NATIVE_COMPONENT_PASS'
    assert receipt['productionBaselineRevision'] == RUNTIME
    assert receipt['productionUnchanged'] and not receipt['projectBootstrap']
    assert not receipt['iterationLimitAssumed'] and receipt['exitCode'] == 0
    for name, digest in receipt['artifacts'].items():
        assert sha((native / name).read_bytes()) == digest, name
    for pin in receipt['inputPins']:
        assert sha((campaign / pin['path']).read_bytes()) == pin['sha256'], pin
    for pin in receipt['sourcePins']:
        blob = subprocess.check_output(['git', 'show', RUNTIME + ':' + pin['path']], cwd=ROOT)
        assert sha(blob) == pin['sha256'], pin
    # The observed test checkout had the same complete production source tree.
    subprocess.run(['git', 'diff', '--quiet', RUNTIME, receipt['checkoutHeadAtExecution'],
                    '--', 'core', 'model', 'rules', 'scripts'], cwd=ROOT, check=True)
    xml = ET.parse(native / 'execution-v1/native-tests.xml').getroot()
    assert int(xml.attrib['tests']) == 11
    assert all(int(xml.attrib[k]) == 0 for k in ('failures', 'errors', 'skipped'))
    assert len(xml.findall('testcase')) == 11
    launch = json.loads((native / 'execution-v1/attempt-2/launch.json').read_text())
    assert launch['expectedTests'] == 11
    assert ':opentaint-dataflow-core:opentaint-dataflow:test' in launch['command']
    assert 'runProjectAnalyzer' not in launch['command']
    for name in ('LiteralServiceBasis.kt', 'RetainedServiceBasisNativeTest.kt'):
        data = (native / 'execution-v1/attempt-2/source' / name).read_bytes()
        assert sha(data) == launch['sources']['source/' + name]
        assert data == (native / name).read_bytes()
    with zipfile.ZipFile(native / 'execution-v1/attempt-2/compiled-test-classes.jar') as jar:
        assert any(name.endswith('/LiteralServiceBasisKt.class') for name in jar.namelist())
        assert any(name.endswith('/RetainedServiceBasisNativeTest.class') for name in jar.namelist())
    inputs = json.loads((native / 'inputs.json').read_text())
    assert len(inputs['basisRows']) == 6372 and len(inputs['basisRoots']) == 4620
    metrics = {}
    for line in xml.findtext('system-out').splitlines():
        if line.startswith(('ANCESTOR_', 'SAME_PATH_', 'BASIS_')):
            label, *pairs = line.split()
            metrics[label] = dict(pair.split('=', 1) for pair in pairs)
    assert metrics == receipt['metrics']
    assert metrics['BASIS_MEMBERSHIP']['missingAndRemovedLeafRejected'] == 'true'
    assert metrics['BASIS_LITERALS']['fullRows'] == '6372'
    assert metrics['BASIS_LITERALS']['roots'] == '4620'
    return dict(path=NATIVE_RECEIPT, sha256=NATIVE_RECEIPT_SHA,
                checkedArtifacts=len(receipt['artifacts']), checkedInputPins=len(receipt['inputPins']),
                checkedSourcePins=len(receipt['sourcePins']), tests=11, failures=0, errors=0, skipped=0,
                productionTreeEqualAtExecution=True, literalRows=6372, literalRoots=4620,
                testsRerun=False, freshCorpusClassifications=False)


def verify():
    operator_pins = []
    for suffix, expected in OPERATOR_PINS.items():
        path = 'core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/' + suffix
        value = subprocess.check_output(['git', 'show', RUNTIME + ':' + path], cwd=ROOT)
        assert sha(value) == expected, path
        operator_pins.append(dict(path=path, sha256=expected))
    models = []
    with tempfile.TemporaryDirectory(prefix='retained-demand-row-cut-') as tmp:
        build = Path(tmp)
        for name in SOURCES:
            source = (HERE / name).read_text()
            assert not re.search(r'\b(sorry|admit|noncomputable|axiom)\s', source), name
            (build / name).write_text(source)
        for name, (expected, count) in SOURCES.items():
            digest = sha((HERE / name).read_bytes())
            assert expected is None or expected == digest, name
            command = ['elan', 'run', 'leanprover/lean4:v4.33.1', 'lean',
                       '-o', str((build / name).with_suffix('.olean')), name]
            result = subprocess.run(command, cwd=build,
                                    env=dict(os.environ, LEAN_PATH=str(build)),
                                    text=True, capture_output=True)
            output = result.stdout + result.stderr
            assert result.returncode == 0, output
            audits = re.findall(r"^'[^']+' (?:does not depend on any axioms|depends on axioms: \[[^\]]*\])", output, re.M)
            assert len(audits) == count, (name, len(audits), count, output)
            for audit in audits:
                if 'does not depend' in audit:
                    continue
                used = re.search(r'\[([^\]]*)\]', audit).group(1)
                assert {a.strip() for a in used.split(',')} <= {'propext', 'Quot.sound'}, audit
            assert 'sorryAx' not in output and 'Classical.choice' not in output
            models.append(dict(path=name, sha256=digest, audits=count, exitCode=result.returncode,
                               outputSha256=sha(output.encode())))
    native = historical_native_correspondence()
    return dict(schema='RetainedDemandRowCutProof-v1', status='GENERIC_PROOF_AND_CONTROLS_PASS',
                productionRevision=RUNTIME, productionModified=False,
                copiedKernelOrigin=KERNEL_ORIGIN, models=models, operatorPins=operator_pins,
                actualAxiomAudits=sum(x['audits'] for x in models),
                allowedAxioms=['propext', 'Quot.sound'],
                rowsNotOrigins=True, singletonAndJointCuts=True,
                noRemovedRowAsProvider=True, unboundedIterations=True,
                arbitraryLaterRunsFieldsLimitsAndSharedPrograms=True,
                corpusClassificationsEstablished=False,
                nativeTestsRerun=False, closedEvolutionPredicateEstablished=False,
                historicalNativeCorrespondence=native,
                artifacts={p.name: sha(p.read_bytes()) for p in sorted(HERE.iterdir())
                           if p.is_file() and p.suffix in ('.lean', '.py', '.md')})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seal', action='store_true')
    args = parser.parse_args()
    result = verify()
    destination = HERE / 'receipt.json'
    if args.seal:
        assert not destination.exists(), 'Do not overwrite a sealed receipt.'
        destination.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    else:
        assert json.loads(destination.read_text()) == result, 'Receipt differs.'
    print(json.dumps({k: v for k, v in result.items() if k not in ('artifacts', 'models', 'operatorPins')}, sort_keys=True))
