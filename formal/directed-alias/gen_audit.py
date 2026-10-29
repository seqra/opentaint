#!/usr/bin/env python3
"""Regenerates AxiomAudit.lean: one `#print axioms` per public theorem.

Private lemmas need no separate entry: `#print axioms` reports axioms
transitively, so every private lemma a public theorem uses is covered."""
import glob, re

names = []
for path in sorted(glob.glob('DirectedAlias/**/*.lean', recursive=True)):
    ns = []
    for line in open(path):
        m = re.match(r'\s*namespace\s+(\S+)', line)
        if m:
            ns.append(m.group(1))
            continue
        m = re.match(r'\s*end\s+(\S+)\s*$', line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
            continue
        m = re.match(r'\s*(?:@\[[^\]]*\]\s*)?theorem\s+(\S+)', line)
        if m:
            n = m.group(1)
            names.append(n[len('_root_.'):] if n.startswith('_root_.') else '.'.join(ns + [n]))
with open('AxiomAudit.lean', 'w') as out:
    out.write('import DirectedAlias\n\n')
    out.write('\n'.join(f'#print axioms {n}' for n in names) + '\n')
print(f'{len(names)} public theorems')
