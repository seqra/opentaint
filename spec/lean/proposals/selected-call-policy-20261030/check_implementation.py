#!/usr/bin/env python3
"""Bind the selected-policy kernel to reviewed Kotlin adapters and test evidence.

This is a source-adapter audit. It is not a Kotlin verifier or an end-to-end
finding-completeness proof. The original model checker remains independent.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'spec/lean/lean-toolchain').is_file())
BASE = 'edb2e06cdb17eecafbe03415236bf56c57910239'
RUNTIME = 'core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/'
TESTS = 'core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/'
XML_DIR = ROOT / 'core/opentaint-dataflow-core/opentaint-dataflow/build/test-results/test'
REQUIRED_TESTS = [
    'SelectedCallPolicyTest', 'SelectedCallPolicyHelpersTest',
    'RestrictedInitialTransportTest', 'RunMethodHandlersTest', 'RunShellTest',
    'AnyDeliveryTest', 'RecordDemotionTest', 'RecordReplayTest',
    'CallZeroTest', 'PredefinedSummaryTest',
]
# Strings are single tokens. Braces in diagnostic messages do not delimit code.
TOKEN = re.compile(r'//[^\n]*|/\*[\s\S]*?\*/|"""[\s\S]*?"""|'
                   r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|'
                   r'`[^`]*`|[A-Za-z_][A-Za-z_0-9]*|\S')


def digest(value):
    return hashlib.sha256(value if isinstance(value, bytes) else value.encode()).hexdigest()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT).decode()


def base_source(relative):
    return git('show', BASE + ':' + RUNTIME + relative)


def source(relative):
    return (ROOT / RUNTIME / relative).read_text()


def tokens(value):
    return [m.group() for m in TOKEN.finditer(value)
            if not m.group().startswith(('//', '/*'))]


def block(value, anchor):
    start = value.index(anchor)
    stream = list(TOKEN.finditer(value, start + len(anchor)))
    opened = next(i for i, item in enumerate(stream) if item.group() == '{')
    depth = 0
    for item in stream[opened:]:
        if item.group() == '{': depth += 1
        if item.group() == '}':
            depth -= 1
            if not depth:
                return value[stream[opened].start():item.end()]
    raise RuntimeError('Unclosed source block: ' + anchor)


def without_replay_counters(value):
    return re.sub(r'^\s*statistics\?\.persistedReplay(?:Candidate|Matched)\(\)\s*$', '', value, flags=re.M)


def all_passed_test_xml():
    rows = []
    for path in sorted(XML_DIR.glob('TEST-*.xml')):
        tree = ET.parse(path).getroot()
        rows.append({'path':str(path.relative_to(ROOT)), 'sha256':digest(path.read_bytes()),
                     'class':tree.attrib['name'], 'tests':int(tree.attrib.get('tests', '0')),
                     'failures':int(tree.attrib.get('failures', '0')),
                     'errors':int(tree.attrib.get('errors', '0')),
                     'skipped':int(tree.attrib.get('skipped', '0')),
                     'timestamp':tree.attrib.get('timestamp'),
                     'cases':[test.attrib.get('name') for test in tree.findall('testcase')]})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--test-log', type=Path,
                        help='Successful full Gradle core/JVM suite log; not a test runner')
    args = parser.parse_args()
    checks, evidence = {}, {}
    def check(name, value, details=None):
        checks[name] = bool(value)
        if details is not None: evidence[name] = details

    # All AP/transfer/store files and their semantic keys must retain base bytes.
    unchanged_paths = git('ls-tree', '-r', '--name-only', BASE, '--',
        RUNTIME+'ap', RUNTIME+'store', RUNTIME+'interp').splitlines()
    unchanged_paths += [RUNTIME+'engine/'+name for name in [
        'ProtocolContracts.kt', 'CalleeSubscriptions.kt', 'SummaryStorage.kt',
        'PublicationIndex.kt', 'RunMethodLocalServices.kt', 'EngineAlgebra.kt',
        'RunManager.kt', 'InFlight.kt', 'RunConfig.kt', 'Run1Abstraction.kt',
        'DeltaWorklist.kt', 'CfgDeliveryCache.kt', 'Run1StaticService.kt',
    ]]
    unchanged = []
    for path in unchanged_paths:
        old = subprocess.check_output(['git', 'show', BASE+':'+path], cwd=ROOT)
        current = (ROOT/path).read_bytes()
        unchanged.append({'path':path, 'baseSha256':digest(old), 'currentSha256':digest(current),
                          'equal':old == current})
    check('apKeysTransfersStoresAndProtocolUnchanged', all(row['equal'] for row in unchanged), unchanged)

    old_calls = base_source('engine/RunMethodCallServices.kt')
    calls = source('engine/RunMethodCallServices.kt')
    analyzer = source('engine/RunMethodAnalyzer.kt')
    old_analyzer = base_source('engine/RunMethodAnalyzer.kt')
    native = source('engine/PersistedSummaryReplay.kt')
    emission = source('engine/RestrictedInitialEmission.kt')
    subscriptions = source('engine/SubscriptionManager.kt')
    old_subscriptions = base_source('engine/SubscriptionManager.kt')
    old_loop = block(old_subscriptions, 'for (leaf in ops.leaves(part.added))')
    new_loop = block(native, 'for (leaf in ops.leaves(part.added))')
    check('persistedReplayLoopEqualsBaseExceptAggregateCounters',
          tokens(old_loop) == tokens(without_replay_counters(new_loop)),
          {'baseLoopTokenSha256':digest(json.dumps(tokens(old_loop))),
           'currentLoopWithoutCountersTokenSha256':digest(json.dumps(tokens(without_replay_counters(new_loop))))})
    check('persistedReplayTemporaryStateAndBindings', all(text in native for text in [
        'val records = config.records', 'val direction = config.direction', 'val mode = config.mode',
        'val cancellation = ops.manager.cancellation', 'val seen = HashSet<Record>()',
        'val seenViews = HashMap<RecordLeafView, Boolean>()', 'check(config.restricted && !part.zeroOnly)']))
    check('currentSummaryReplayDoesNotReplayRecords',
          'replayRecords' not in subscriptions and 'replayPersistedSummaries' not in subscriptions)
    # Initial starts and every summary application retain their prior code.
    anchors = ['internal fun addInitial(', 'private fun startAt(']
    check('initialAdmissionAndBoundaryStartUnchanged', all(
        tokens(block(old_analyzer, anchor)) == tokens(block(analyzer, anchor)) for anchor in anchors))
    anchors = ['override fun applySummary(', 'override fun applyRecord(',
               'override fun applyRecordView(', 'private fun resumeCallees(',
               'private fun summaryParts(', 'private fun zeroAtCall(']
    check('recordCurrentReturnAndZeroPipelinesUnchanged', all(
        tokens(block(old_calls, anchor)) == tokens(block(calls, anchor)) for anchor in anchors))

    # Exact complete query extraction: the differential suite supplies key-set evidence.
    validation_anchor = 'for (leaf in ops.leaves('
    old_validation = block(block(old_analyzer, 'fun addLink('), validation_anchor)
    old_validation = re.sub(r'\bcheckRun2StaticAnchors\b', 'config.index == 2', old_validation)
    old_validation = re.sub(r'\blimit\b', 'config.fieldLimit', old_validation)
    new_validation = block(emission, validation_anchor)
    check('boundedLeafValidationEqualsBase', tokens(old_validation) == tokens(new_validation))
    check('oneCompleteEmissionQueryOnOriginalOffer', all(text in emission for text in [
        'ops.limit(actual, config.fieldLimit, object : ApOut', 'val result = LinkedHashSet<InitialAp>()',
        'config.demand).initials(callee, bounded, config.admissionPolicy)',
        'return result.toList()']) and emission.count('.initials(') == 1)
    add_link = block(analyzer, 'fun addLink(')
    check('rawLinkIsRun1OnlyAndHasNoDemandLookup',
          'check(config.run1)' in add_link and '.initials(' not in add_link and 'ops.limit(' not in add_link
          and 'checkNotNull(abstraction).emit(ref, added)' in add_link)

    entry = block(calls, 'private fun enterCallees(')
    run1 = block(entry, 'if (core.config.run1)')
    check('run1SubscribeAndRawDeliveryUnchanged', tokens(run1) == tokens('''{
        core.runnerPort.subscribe(part)
        core.ap.cancellation.checkpoint()
        core.runnerPort.link(callee, ref, part.linkLayer, part.added)
        continue
    }'''))
    restricted = entry[entry.index('replayPersistedSummaries('):]
    phases = ['replayPersistedSummaries(core.config, core.ops, part, core, statistics)',
              'emitRestrictedInitials(core.config, core.ops, callee, part.added, statistics)',
              'if (initials.isEmpty()) continue', 'core.runnerPort.subscribe(part)',
              'core.runnerPort.startInitials(callee, initials)']
    positions = [restricted.find(phase) for phase in phases]
    check('persistedDemandGateCurrentAndKeyDeliveryOrder', min(positions) >= 0 and positions == sorted(positions))
    check('restrictedBranchHasNoRawLinkOrFreshAdmissionGate',
          '.link(' not in restricted and '.admit(' not in restricted and 'added =' not in restricted)
    check('fullCallerBindingUnchanged', 'val ref = CallerRef(core.key, fact.premise, ctx.callerLayer, ctx.node, ctx.plan.stages.indexOf(stage))' in entry
          and 'val part = Subscription(callee, ref, fact.facts.layer, fact.facts)' in entry)

    events = source('engine/RunEvent.kt')
    handlers = source('engine/RunMethodHandlers.kt')
    unit = source('engine/UnitRunner.kt')
    event = block(events, 'class InitialsIn(')
    receive = block(handlers, 'is RunEvent.InitialsIn ->')
    deliver = block(unit, 'override fun startInitials(')
    check('packetIsDetachedNonemptyImmutableCanonicalKeyList',
          'Collections.unmodifiableList(ArrayList(initials))' in event
          and 'require(this.initials.isNotEmpty())' in event
          and 'is RunEvent.InitialsIn -> callee' in events
          and 'class InitialsIn(val callee: MethodKey, initials: Collection<InitialAp>)' in events)
    check('receiverStartsKeysWithoutRepeatingDemandOrLimit',
          'check(port.config.restricted)' in receive and 'val actor = port.analyzer(event.callee)' in receive
          and 'port.shared.cancellation.checkpoint()' in receive and 'actor.addInitial(initial)' in receive
          and '.initials(' not in receive and '.limit(' not in receive)
    check('ownerRoutingCancellationAndRequiredSend', all(text in deliver for text in [
        'check(!run.ended && !closed.get())', 'check(config.restricted)',
        'shared.cancellation.checkpoint()', 'RunEvent.InitialsIn(callee, initials)',
        'shared.unitResolver.resolve(callee.method) == unit', 'handler.handle(event)',
        'val accepted = send(event)', 'check(accepted)']))

    model = json.loads((HERE/'checks.json').read_text())
    model_current = all((ROOT/path).is_file() and digest((ROOT/path).read_bytes()) == expected
                        for path, expected in model['moduleSourceHashes'].items())
    check('constructiveModelReceiptCurrentAndPass', model['status'] == 'PASS' and model_current
          and all(model['checks'].values()) and model['axiomDependencies'] == ['Quot.sound', 'propext']
          and model['checkerSha256'] == digest((HERE/'check.py').read_bytes())
          and model['proposalSha256'] == digest((ROOT/'docs/design/bidirectional-selected-call-policy-implementation-20261030.md').read_bytes()),
          {'receipt':'spec/lean/proposals/selected-call-policy-20261030/checks.json',
           'sha256':digest((HERE/'checks.json').read_bytes()), 'namedTheorems':model['theoremCount'],
           'auditedDeclarations':model['auditedDeclarationCount'],
           'scope':'Finite selected-policy kernel only; no whole-analyzer proof.'})

    tests = all_passed_test_xml()
    by_class = {row['class'].split('.')[-1]:row for row in tests}
    check('requiredAdapterSuitesPass', all(name in by_class and by_class[name]['tests'] > 0
          and not any(by_class[name][key] for key in ['failures', 'errors', 'skipped']) for name in REQUIRED_TESTS),
          {name:by_class.get(name) for name in REQUIRED_TESTS})
    check('allAvailableCoreTestReportsPass', bool(tests) and all(
        row['failures'] == 0 and row['errors'] == 0 for row in tests),
        {'suiteCount':len(tests), 'testCount':sum(row['tests'] for row in tests),
         'failures':sum(row['failures'] for row in tests), 'errors':sum(row['errors'] for row in tests)})
    test_log = None
    if args.test_log and args.test_log.is_file():
        log = args.test_log.read_text()
        test_log = {'path':str(args.test_log.resolve()), 'sha256':digest(args.test_log.read_bytes())}
        passed_log = 'BUILD SUCCESSFUL' in log and 'BUILD FAILED' not in log
    else: passed_log = False
    check('successfulSuiteCommandLogProvided', passed_log, test_log)

    bound_paths = sorted(set(unchanged_paths + [RUNTIME+'engine/'+name for name in [
        'RunMethodCallServices.kt', 'RunMethodAnalyzer.kt', 'SubscriptionManager.kt',
        'PersistedSummaryReplay.kt', 'RestrictedInitialEmission.kt', 'RunEvent.kt',
        'RunnerPort.kt', 'RunMethodHandlers.kt', 'UnitRunner.kt', 'N2Statistics.kt']]
        + [TESTS+name+'.kt' for name in REQUIRED_TESTS]
        + [TESTS+'fixtures/'+name+'.kt' for name in [
            'MethodAnalysisFixtures', 'PipelineFixtures', 'ProductionSchedule',
            'NaiveClosure', 'EngineShellFixtures', 'SelectedDemandReference']]))
    receipt = {'status':'PASS' if all(checks.values()) else 'FAILED',
               'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'baseRuntime':BASE, 'observedHead':git('rev-parse', 'HEAD').strip(),
               'checkerSha256':digest(Path(__file__).read_bytes()),
               'checks':checks, 'evidence':evidence,
               'sourceHashes':{path:digest((ROOT/path).read_bytes()) for path in bound_paths},
               'testReportHashes':{row['path']:row['sha256'] for row in tests},
               'scope':'Source adapter and passing-test evidence for the selected caller policy. '
                       'Token equality is a source check, not a compiler semantics proof. '
                       'Tests cover finite programs and protocol schedules. '
                       'The Lean kernel does not verify Kotlin coroutines, arbitrary callbacks, '
                       'or whole-project finding completeness. Project measurements remain a separate gate.'}
    (HERE/'implementation-checks.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'status':receipt['status'], 'checks':checks}, indent=2))
    if receipt['status'] != 'PASS': raise SystemExit(1)


if __name__ == '__main__': main()
