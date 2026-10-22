"""Independent exact finite algebra checks; not a spectral theorem or Lean oracle."""
from fractions import Fraction as Q
import json
checked=0
for shift in range(-10,11):
 c=Q(2*shift-1,2)
 assert c and c*c
 for n in range(20,220):
  exact=1/(Q(n)+c)
  assert Q(n*n)*(exact-1/Q(n)) == -c/(1+c/n)
  assert Q(n**3)*(exact-1/Q(n)+c/Q(n*n)) == c*c/(1+c/n)
  for order in range(1,9):
   truncated=sum(((-c)**j/Q(n**(j+1)) for j in range(order)),Q(0))
   remainder=(-c)**order/(Q(n**order)*(Q(n)+c))
   assert exact == truncated+remainder
   checked+=1
print(json.dumps({'status':'PASS','exact_checks':checked,
 'integer_index_shifts':[-10,10], 'geometric_orders':[1,8],
 'one_based_scaled_second_coefficient':'1/2',
 'scope':'Exact rational identities for pi times the known spectral sequence. Does not prove operator spectral identification or infinite limits.'},indent=2))
