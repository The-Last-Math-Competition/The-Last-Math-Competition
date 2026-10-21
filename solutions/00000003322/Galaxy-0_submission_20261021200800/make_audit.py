#!/usr/bin/env python3
"""Enumerate every top-level authored theorem in all mathematical modules."""
from pathlib import Path
import re,json
ROOT=Path(__file__).resolve().parent
modules=['PolynomialCore','RawPolynomial','PolynomialRing','TwoExtras','ThreeCore','ThreeRaw','ThreeRing','ThreeGrading','ThreeExtras','Graphs','Principal','TriangleCore','TriangleModule','TriangleGraded','TriangleBetti','Main']
names=[]
for module in modules:
    text=(ROOT/(module+'.lean')).read_text()
    text=re.sub(r'/\-.*?\-/','',text,flags=re.S)
    scopes=[]
    for line in text.splitlines():
        line=re.sub(r'--.*','',line).strip()
        m=re.match(r'namespace\s+(\S+)',line)
        if m: scopes.append(m[1]); continue
        if re.match(r'(noncomputable\s+)?section\b',line): scopes.append(''); continue
        if re.match(r'end\b',line):
            assert scopes,(module,line)
            scopes.pop();continue
        m=re.match(r'(?:@\[[^]]*\]\s*)?theorem\s+([^\s:{(]+)',line)
        if m:names.append('.'.join([x for x in scopes if x]+[m[1]]))
    assert not scopes,(module,scopes)
assert len(names)==len(set(names))
(ROOT/'Audit.lean').write_text('import Main\n\n'+''.join(f'#check {n}\n#print axioms {n}\n' for n in names))
(ROOT/'theorem-manifest.json').write_text(json.dumps({'modules':modules,'theorems':names},indent=2)+'\n')
print(f'{len(names)} mathematical theorems across {len(modules)} modules')
