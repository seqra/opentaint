#!/usr/bin/env python3
"""Shadow evaluation of QUIET-Q2 / QUIET-Q1' / REPEAT from existing analyzer logs.
usage: shadow.py LISTFILE OUT.json   (LISTFILE: one 'label<TAB>path' per line)"""
import re, sys, json, gzip

FR = re.compile(r'^(\d\d):(\d\d):(\d\d)\.(\d+) .*Run (\d+) \((FORWARD|BACKWARD)\) frontier: analysed (\d+), demand edges (\d+) in (\d+) method keys, left (\d+), record crossings (\d+), target demand (\d+), reports (\d+), seeds (\d+), zero only (\d+) \((\d+) edges\)')
TS = re.compile(r'^(\d\d):(\d\d):(\d\d)\.(\d+) ')
KV = re.compile(r'(\w+)=((?:\d+h )?(?:\d+m )?[\d.]+(?:s|ms|us|ns)|\S+)')
DUR = re.compile(r'(?:(\d+)h )?(?:(\d+)m )?([\d.]+)(s|ms|us|ns)$')

def dur(s):
    m = DUR.match(s)
    if not m: return None
    v = float(m.group(3)) * {'s': 1, 'ms': 1e-3, 'us': 1e-6, 'ns': 1e-9}[m.group(4)]
    return v + 60 * int(m.group(2) or 0) + 3600 * int(m.group(1) or 0)

def ts(line):
    m = TS.match(line)
    if not m: return None
    return int(m.group(1)) * 3600 + int(m.group(2)) * 60 + int(m.group(3)) + float('0.' + m.group(4))

def kvs(line):
    out = {}
    line = line[:3000]
    body = line.split(' - ', 1)[1] if ' - ' in line else line
    # durations contain spaces: handle k=1m 2.3s
    for m in re.finditer(r'(\w+)=((?:\d+h )?(?:\d+m )?[\d.]+(?:ms|us|ns|s)\b|\S+)', body):
        out[m.group(1)] = m.group(2)
    return out

def parse(path):
    op = gzip.open if path.endswith('.gz') else open
    analyses, cur, sample = [], None, None
    def new():
        return {'sample': sample, 'runs': {}, 'end': None, 'stats': None}
    with op(path, 'rt', errors='replace') as f:
        for line in f:
            if '|D|' in line[:20]: continue
            if 'RULE_TEST_START' in line:
                k = kvs(line); sample = (k.get('sample'), k.get('rule'))
                continue
            if 'BIDI_' not in line and 'frontier: analysed' not in line: continue
            if 'BIDI_RUN_START' in line:
                k = kvs(line)
                if cur is None or cur['end'] is not None or (k.get('run') == '1' and cur['runs']):
                    if cur is not None and cur['runs']: analyses.append(cur)
                    cur = new()
                r = cur['runs'].setdefault(int(k['run']), {})
                r['dir'] = k.get('direction'); r['limit'] = k.get('limit'); r['t_start'] = ts(line)
                continue
            if cur is None: cur = new()
            if 'BIDI_RUN_END' in line:
                k = kvs(line); r = cur['runs'].setdefault(int(k['run']), {})
                r['status'] = k.get('status'); r['engine'] = dur(k.get('engineTime', '')); continue
            if 'BIDI_HANDOFF_COMPACTION' in line:
                k = kvs(line); r = cur['runs'].setdefault(int(k['run']), {})
                r['comp_rows'] = int(k['rows']); r['comp_origins'] = int(k['origins']); r['residualMay'] = k.get('residualMay'); continue
            if 'BIDI_BARRIER_END' in line:
                k = kvs(line); r = cur['runs'].setdefault(int(k['run']), {})
                r['iter'] = dur(k.get('iterationTime', '')); r['t_barrier'] = ts(line); continue
            if 'BIDI_ANALYSIS_END' in line:
                k = kvs(line)
                cur['end'] = {'run': int(k['run']), 'status': k['status'], 'reason': k['reason'],
                              'elapsed': dur(k.get('elapsed', '')), 't': ts(line)}
                continue
            if 'BIDI_REPORT_STATISTICS' in line:
                k = kvs(line)
                cur['stats'] = {'confirmed': int(k['confirmed']), 'provisional': int(k['provisional'])}
                continue
            if 'frontier: analysed' not in line: continue
            m = FR.match(line[:600])
            if m:
                g = m.groups(); run = int(g[4]); r = cur['runs'].setdefault(run, {})
                names = ['analysed', 'demand', 'keys', 'left', 'crossings', 'target', 'reports', 'seeds', 'zeroOnly', 'zeroEdges']
                r['dir'] = g[5]; r['f'] = dict(zip(names, map(int, g[6:])))
    if cur is not None and cur['runs']: analyses.append(cur)
    return analyses

def dt(a, b):
    if a is None or b is None: return None
    d = b - a
    return d + 86400 if d < -1 else d

def evaluate(a):
    runs = a['runs']
    done = sorted(r for r, v in runs.items() if 'f' in v)      # runs with a frontier line (barrier completed)
    fwd = [r for r in done if r % 2 == 1]
    c = {r: runs[r]['f']['reports'] for r in fwd}
    last = done[-1] if done else 0
    final_conf = a['stats']['confirmed'] if a['stats'] else (c[fwd[-1]] if fwd else None)
    final_prov = a['stats']['provisional'] if a['stats'] else None
    end = a['end'] or {}
    t_end = end.get('t')
    def strict(i, j): return runs[i]['f'] == runs[j]['f']
    def loose(i, j):
        ks = ('demand', 'keys', 'target', 'reports', 'seeds')
        return all(runs[i]['f'][k] == runs[j]['f'][k] for k in ks)
    fire = {}
    for name in ('Q2', 'Q1p', 'REPEAT', 'REPEAT_loose'):
        for i in fwd:
            if i < 5: continue
            ok = False
            if name == 'Q2': ok = all(x in c for x in (i - 2, i - 4)) and c[i] == c[i - 2] == c[i - 4]
            elif name == 'Q1p': ok = (i - 2) in c and c[i] == c[i - 2]
            else:
                need = (i, i - 1, i - 2, i - 3)
                if all(x in runs and 'f' in runs[x] for x in need):
                    eq = strict if name == 'REPEAT' else loose
                    ok = eq(i, i - 2) and eq(i - 1, i - 3)
            if ok:
                natural_end_here = (end.get('run') == i and end.get('reason') in ('NO_DEMAND_EDGE', 'RUN_LIMIT', 'STOP_RULE', 'POLICY'))
                later_engine = sum((runs[r].get('engine') or 0) for r in runs if r > i)
                later_iter = sum((runs[r].get('iter') or runs[r].get('engine') or 0) for r in runs if r > i)
                fire[name] = {'run': i, 'count_at_stop': c[i], 'loss': (final_conf or 0) - c[i],
                              'natural_end_here': natural_end_here,
                              'saved_engine_s': later_engine, 'saved_iter_s': later_iter,
                              'saved_wall_s': dt(runs[i].get('t_barrier'), t_end)}
                break
    # quiet then gain
    qg = []
    for idx, i in enumerate(fwd):
        if i >= 3 and (i - 2) in c and c[i] == c[i - 2]:
            later = [(j, c[j]) for j in fwd[idx + 1:] if c[j] > c[i]]
            if later: qg.append({'quiet_run': i, 'count': c[i], 'gain_run': later[0][0], 'gain_count': later[0][1]})
    last_gain = max([r for r in fwd if (r == fwd[0] and c[r] > 0) or (r != fwd[0] and c[r] > c[fwd[fwd.index(r) - 1]])], default=None)
    total_engine = sum((v.get('engine') or 0) for v in runs.values())
    return {'sample': a['sample'], 'end': a['end'], 'stats': a['stats'], 'last_complete': last,
            'fwd_counts': c, 'final_confirmed': final_conf, 'final_provisional': final_prov,
            'fire': fire, 'quiet_then_gain': qg, 'last_gain_run': last_gain, 'total_engine_s': total_engine,
            'runs': {r: {'dir': v.get('dir'), 'limit': v.get('limit'), 'status': v.get('status'), 'engine': v.get('engine'), 'iter': v.get('iter'),
                         'comp_rows': v.get('comp_rows'), **(v.get('f') or {})} for r, v in sorted(runs.items())}}

if __name__ == '__main__':
    out = []
    for line in open(sys.argv[1]):
        line = line.rstrip('\n')
        if not line: continue
        label, path = line.split('\t')
        print('FILE', path, file=sys.stderr, flush=True)
        try:
            for n, a in enumerate(parse(path)):
                e = evaluate(a); e['label'] = label; e['path'] = path; e['n'] = n; out.append(e)
        except Exception as ex:
            print('ERR', path, ex, file=sys.stderr)
    json.dump(out, open(sys.argv[2], 'w'))
    print(len(out), 'analyses')
