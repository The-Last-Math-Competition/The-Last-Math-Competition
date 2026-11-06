#!/usr/bin/env python3
"""Supplemental textual check; kernel replay and axiom audits remain decisive."""
import pathlib,re,sys
root=pathlib.Path(sys.argv[1])

def remove_comments_and_strings(text):
    out=[]; i=0; depth=0; string=False
    while i<len(text):
        if string:
            if text[i]=='\\':i+=2
            elif text[i]=='"':string=False;i+=1
            else:i+=1
        elif text.startswith('/-',i):depth+=1;i+=2
        elif depth and text.startswith('-/',i):depth-=1;i+=2
        elif depth:i+=1
        elif text.startswith('--',i):
            end=text.find('\n',i)
            i=len(text) if end<0 else end
        elif text[i]=='"':string=True;i+=1
        else:out.append(text[i]);i+=1
    assert depth==0 and not string,'Unclosed block comment or string'
    return ''.join(out)

files=sorted(root.glob('*.lean'))
for f in files:
    code=remove_comments_and_strings(f.read_text())
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',code),f.name
    assert 'ofReduceBool' not in code,f.name
print(f'PASS: {len(files)} authored Lean files contain no forbidden proof-bypass tokens outside comments and string literals.')
