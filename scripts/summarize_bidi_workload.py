#!/usr/bin/env python3
"""Read JFR events with bounded export buffering and report disjoint work scopes.

Execution samples are Java samples, not elapsed-time shares. Allocation weights
estimate churn, not retained heap. Callback scopes have explicit precedence.
Only five distinct example stacks per scope are retained; no full event export
or per-event history is saved. Run with the analyzer's JDK on PATH.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess

from summarize_bidi_profiles import method_name, parse_date, phase_windows, seconds


SCOPES = {
    'c5_restriction': ['.DemandStore.intersect', '.DemandStore.acceptsTarget'],
    'current_delivery': ['.SubscriptionManager.onDelivery'],
    'saved_replay': ['.PersistedSummaryReplayKt.replayPersistedSummaries'],
    'ordinary_statement': ['.RunMethodAnalyzer.runStatement'],
    'direct_call': ['.RunMethodCallServices.process'],
    'other': [],
}


def scope(frames):
    for name, anchors in SCOPES.items():
        if any(anchor in frame for anchor in anchors for frame in frames):
            return name
    return 'other'


def events(stream):
    """Consume jfr print's events array; do not retain the entire JSON export."""
    decoder = json.JSONDecoder()
    buffer = ''
    while '"events"' not in buffer:
        chunk = stream.read(65536)
        if not chunk:
            raise ValueError('JFR export has no events array')
        buffer += chunk
    pos = buffer.index('[', buffer.index('"events"')) + 1
    whitespace = re.compile(r'[\s,]*')
    while True:
        pos = whitespace.match(buffer, pos).end()
        if pos < len(buffer) and buffer[pos] == ']':
            return
        try:
            event, end = decoder.raw_decode(buffer, pos)
        except json.JSONDecodeError:
            buffer = buffer[pos:]
            pos = 0
            chunk = stream.read(65536)
            if not chunk:
                raise ValueError('JFR export ended inside an event')
            buffer += chunk
            continue
        yield event
        pos = end
        if pos > 65536:
            buffer = buffer[pos:]
            pos = 0


def counters():
    return dict(samples=0, scopes=Counter(), leaf=Counter(), inclusive=Counter(),
                allocation_samples=0, allocation_bytes=0, allocation_scopes=Counter(),
                allocation_classes=Counter(), allocation_sites=Counter(),
                gc_events=0, gc_pause_seconds=0., examples={})


def add(counter, event):
    kind, values = event['type'], event['values']
    if kind == 'jdk.GarbageCollection':
        counter['gc_events'] += 1
        counter['gc_pause_seconds'] += seconds(values.get('sumOfPauses')) or 0.
        return
    frames = [method_name(frame) for frame in
              (values.get('stackTrace') or {}).get('frames', [])]
    if kind == 'jdk.ExecutionSample' and frames:
        counter['samples'] += 1
        category = scope(frames)
        counter['scopes'][category] += 1
        counter['leaf'][frames[0]] += 1
        counter['inclusive'].update(set(frames))
        examples = counter['examples'].setdefault(category, [])
        if len(examples) < 5 and frames not in examples:
            examples.append(frames)
    elif kind == 'jdk.ObjectAllocationSample':
        weight = values['weight']
        counter['allocation_samples'] += 1
        counter['allocation_bytes'] += weight
        counter['allocation_scopes'][scope(frames)] += weight
        counter['allocation_classes'][(values.get('objectClass') or {}).get('name', '?')] += weight
        counter['allocation_sites'][next((f for f in frames if '.bidi.' in f), '<no bidi frame>')] += weight


def ranking(counter, denominator, limit=30):
    return [dict(name=name, count=count, percent=100 * count / denominator if denominator else 0.)
            for name, count in counter.most_common(limit)]


def finish(counter):
    return dict(samples=counter['samples'],
                disjoint_scopes=ranking(counter['scopes'], counter['samples']),
                leaf=ranking(counter['leaf'], counter['samples']),
                inclusive=ranking(counter['inclusive'], counter['samples']),
                allocation_samples=counter['allocation_samples'],
                sampled_allocation_bytes=counter['allocation_bytes'],
                allocation_disjoint_scopes=ranking(counter['allocation_scopes'], counter['allocation_bytes']),
                allocation_classes=ranking(counter['allocation_classes'], counter['allocation_bytes']),
                allocation_bidi_sites=ranking(counter['allocation_sites'], counter['allocation_bytes']),
                gc_events=counter['gc_events'], gc_pause_seconds=counter['gc_pause_seconds'],
                bounded_example_stacks=counter['examples'])


def summarize(directory, recording='continuous.jfr'):
    manifest = json.loads((directory / 'manifest.json').read_text())
    summary = json.loads((directory / 'summary.json').read_text())
    start = parse_date(manifest['started_utc'])
    end = start + summary['command_wall_seconds']
    day = int(start // 86400) * 86400
    log = (directory / 'analyzer.log').read_text(errors='replace')
    windows = phase_windows(log, day, end)
    for name, (begin, stop) in list(windows.items()):
        if re.fullmatch(r'run-\d+', name):
            windows[name + '-last-30s'] = (max(begin, stop - 30), stop)
            if stop >= begin + 60:
                windows[name + '-after-60s'] = (begin + 60, min(stop, begin + 90))
    groups = {name: counters() for name in windows}
    total = counters()
    selected = 'jdk.ExecutionSample,jdk.ObjectAllocationSample,jdk.GarbageCollection'
    command = ['jfr', 'print', '--json', '--stack-depth', '256', '--events', selected,
               str(directory / recording)]
    first_event, last_event = None, None
    with (directory / 'jfr-reader.log').open('w') as errors:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=errors, text=True)
        try:
            for event in events(process.stdout):
                timestamp = parse_date(event['values']['startTime'])
                first_event = timestamp if first_event is None else min(first_event, timestamp)
                last_event = timestamp if last_event is None else max(last_event, timestamp)
                add(total, event)
                for name, (begin, stop) in windows.items():
                    if begin <= timestamp <= stop:
                        add(groups[name], event)
        except BaseException:
            process.terminate()
            raise
        finally:
            process.stdout.close()
            code = process.wait()
        if code:
            raise RuntimeError(f'JFR reader failed: {code}; inspect jfr-reader.log')
    return dict(project=manifest['project'], revision=manifest['revision'],
                latest_reached=summary['latest_bidi_iteration'],
                latest_complete=summary['latest_complete_bidi_iteration'],
                latest_accepted=summary['latest_accepted_forward_report'],
                source=str(directory), recording=str(directory / recording), scope_precedence=SCOPES, limits=__doc__,
                first_event=first_event, last_event=last_event,
                continuous=finish(total),
                phases={name: dict(begin=begin, end=min(stop, last_event or stop),
                                   **finish(groups[name]))
                        for name, (begin, stop) in windows.items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--recording', default='continuous.jfr',
                        help='Use a completed-run snapshot if the continuous capture rolled out that phase')
    args = parser.parse_args()
    default_name = 'workload-profile-summary.json' if args.recording == 'continuous.jfr' else \
        Path(args.recording).stem + '-workload-profile-summary.json'
    output = args.output or args.directory / default_name
    output.write_text(json.dumps(summarize(args.directory.resolve(), args.recording), indent=2) + '\n')
    print(output)


if __name__ == '__main__':
    main()
