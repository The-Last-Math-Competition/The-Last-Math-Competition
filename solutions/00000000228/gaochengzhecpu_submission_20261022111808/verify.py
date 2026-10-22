"""Exact Stern recurrence and three-bit block checks; supplementary only."""
from functools import lru_cache
from fractions import Fraction
import json

@lru_cache(None)
def stern(n):
    if n<2:return n
    if n%2==0:return stern(n//2)
    return stern(n//2)+stern(n//2+1)

def pair(n):
    a,b=0,1
    for bit in bin(n)[2:]:
        a,b=(a,a+b) if bit=='0' else (a+b,b)
    return a,b

rows=[(1,0),(3,1),(2,1),(3,2),(1,1),(2,3),(1,2),(1,3),(0,1)]
for n in range(10001):
    a,b=stern(n),stern(n+1)
    assert pair(n)==(a,b)
    for r,(x,y) in enumerate(rows):
        assert stern(8*n+r)==x*a+y*b
    for r in range(8):
        assert max(stern(8*n+r),stern(8*n+r+1))<=5*max(a,b)

samples=[]
for n in range(1,10001):
    m=0
    while 8**(m+1)<=n:m+=1
    assert 8**m<=n<8**(m+1)
    assert n*n<8**(2*m+2)
    assert stern(n*n)<=5**(2*m+2)==25**(m+1)
    bound=25*Fraction(25,27)**m
    assert Fraction(stern(n*n),27**m)<=bound
    if n in (1,8,64,512,4096,10000):
        samples.append({'index':n,'stern_square':stern(n*n),'block_index':m,
                        'certified_ratio_upper':str(bound)})
assert Fraction(25,27)<1
print(json.dumps({'status':'PASS','block_identities_n':10001,
                  'normalized_square_checks_n':10000,'samples':samples},indent=2))
