#!/usr/bin/env python3
"""Generate independent axiom/type review commands from locally copied Lean source."""
import pathlib,re,sys,json
root=pathlib.Path(sys.argv[1]); files=[pathlib.Path(x) for x in sys.argv[2:]]
imports=[]; declarations=[]
for f in files:
    text=(root/f).read_text()
    imports.append(f.stem)
    namespaces=[]
    for line in text.splitlines():
        m=re.match(r'\s*namespace\s+([\w.]+)',line)
        if m:
            namespaces.append(m[1]); continue
        m=re.match(r'\s*end(?:\s+([\w.]+))?\s*$',line)
        if m and namespaces:
            namespaces.pop(); continue
        m=re.match(r'(?:\s*@\[[^\]]+\]\s*)?(?:\s*(?:noncomputable|private|protected)\s+)?\s*(?:theorem|def|abbrev|structure|inductive)\s+([\w.\']+)',line)
        if m:
            declarations.append('.'.join(namespaces+[m[1]]))
(root/'ReviewAxioms.lean').write_text('\n'.join('import '+m for m in imports)+'\n\n'+'\n'.join('#print axioms '+x for x in declarations)+'\n')
(root/'review-declarations.json').write_text(json.dumps(declarations,indent=2)+'\n')
print(f'Generated {len(declarations)} named-declaration axiom checks.')
