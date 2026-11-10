#!/usr/bin/env python3
"""Generate standalone Lean certificates from the source-checked finite copy matrix."""
from pathlib import Path
import argparse,json
HERE=Path(__file__).resolve().parent
ROOT=next(p for p in HERE.parents if(p/'spec/lean/lean-toolchain').is_file())
p=argparse.ArgumentParser();p.add_argument('--closure',type=Path,required=True);a=p.parse_args()
x=json.loads(a.closure.read_text());fields=json.loads((ROOT/'docs/reports/data/bidirectional-owasp-helper-cycle-20261110.json').read_text())['analysis']['fields']
fs={'String#<string-bytes>':1,'String#bytes':2,'*':3,'CharSequence#content':4};bs={'arg(1)':0,'ret':1}
def path(v):return '['+', '.join(str(fs[s])for s in v)+']'
def row(v):return f'⟨0, {bs[v[0]]}, {bs[v[2]]}, {path(v[1])}, {path(v[3])}⟩'
s=(HERE/'NormalBackedDemand.lean').read_text()+'\nnamespace NormalBackedDemand.Observed\n'
for k,e in enumerate(x['perEdge']):
 assert e['P'] and not e['missing']
 ws=e['certificates'];basis=[]
 for w in ws:
  v=w['witness'];item=(v['role']=='SAVED_OPPOSITE',v['native'])
  if item not in basis:basis.append(item)
 s+=f'def normal{k} : List (Bool × Row) := ['+', '.join('('+str(t).lower()+', '+row(r)+')'for t,r in basis)+']\n'
 s+=f'def origins{k} : List Row := ['+', '.join(row(w['origin'])for w in ws)+']\n'
 s+=f'def proof{k} : List Witness := ['+', '.join('⟨'+row(w['origin'])+', '+row(w['witness']['native'])+', '+str(w['witness']['role']=='SAVED_OPPOSITE').lower()+', '+path(w['witness']['shift'])+'⟩'for w in ws)+']\n'
 inp=[fields[str(i)]for i in e['demand']['premise'][0]['path']]
 s+=f'theorem edge{k}_is_retirable : P true normal{k} {path(inp)} origins{k} proof{k} = true := by decide\n#print axioms edge{k}_is_retirable\n'
s+='end NormalBackedDemand.Observed\n';(HERE/'ObservedCertificates.lean').write_text(s)
print(len(x['perEdge']),'observed certificates generated')
