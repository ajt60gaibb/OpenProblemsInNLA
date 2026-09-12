#!/usr/bin/env python3
"""Independent exact diagnostics; never extrapolates finite tests to a universal proof."""
from itertools import product, permutations
from fractions import Fraction
from math import factorial, ceil
from pathlib import Path
import hashlib,json

def rows_of(flat,n): return tuple(tuple(flat[i*n:(i+1)*n]) for i in range(n))
def hadamard(a):
    n=len(a)
    return all(len(row)==n and all(x in (-1,1) for x in row) for row in a) and all(
      sum(a[i][k]*a[j][k] for k in range(n))==(n if i==j else 0)
      for i in range(n) for j in range(n))
def all_small(n):
    return [a for flat in product((-1,1),repeat=n*n) if hadamard(a:=rows_of(flat,n))]
def construct(a,b,sigma):
    return tuple(a[i]+b[i] for i in range(len(a)))+tuple(a[i]+tuple(-x for x in b[i]) for i in sigma)
def decode(c):
    m=len(c)//2
    a=tuple(row[:m] for row in c[:m]);b=tuple(row[m:] for row in c[:m])
    inverse_rows={row:i for i,row in enumerate(a)}
    assert len(inverse_rows)==m
    sigma=tuple(inverse_rows[row[:m]] for row in c[m:])
    assert sorted(sigma)==list(range(m))
    assert construct(a,b,sigma)==c
    return a,b,sigma
cases=[]
for m in (1,2):
    inputs=all_small(m);seen={};triples=0
    for a,b,sigma in product(inputs,inputs,permutations(range(m))):
        c=construct(a,b,sigma);assert hadamard(c)
        triple=(a,b,sigma);assert decode(c)==triple
        assert c not in seen or seen[c]==triple
        seen[c]=triple;triples+=1
    assert triples==factorial(m)*len(inputs)**2==len(seen)
    cases.append({'input_order':m,'exact_input_hadamard_count':len(inputs),
                  'all_input_triples':triples,'distinct_valid_outputs':len(seen),
                  'all_outputs_decode_to_exact_labeled_inputs':True,
                  'complete_count_at_output_order_claimed':False})
assert [(r['exact_input_hadamard_count'],r['distinct_valid_outputs']) for r in cases]==[(2,4),(8,128)]
recurrence=[];lower=1
for K in range(1,13):
    m=2**(K-1);lower=factorial(m)*lower**2
    if K>=2:
        rhs_exponent=(2**K)*(K-1)*(K-2)
        assert lower**8>=2**rhs_exponent
        r=m//2;assert factorial(m)>=r**r
        E=lambda t:Fraction((2**t)*(t-1)*(t-2),8)
        assert E(K)==2*E(K-1)+(K-2)*(2**(K-2))
        recurrence.append({'K':K,'lower_count_bit_length':lower.bit_length(),
          'lower_count_sha256':hashlib.sha256(lower.to_bytes((lower.bit_length()+7)//8,'big')).hexdigest(),
          'eighth_power_comparison_passed':True,'factorial_bound_passed':True,
          'rational_exponent_recurrence_exact':True})
constants=[]
for C in [Fraction(1,100000000),Fraction(1,2),Fraction(1),Fraction(1000),Fraction(10**12,7)]:
    k=max(3,ceil(16*C)+1)
    assert k>2 and k>16*C
    gap=Fraction(k*(k+1),8)-C*(k+2);assert gap>0
    constants.append({'C':str(C),'selected_k':k,'exact_exponent_gap':str(gap)})
result={'status':'PASS: independent finite integer/rational diagnostics only',
'scope':'No Lean proof, universal injectivity, infinite recurrence or all-real-C theorem is inferred from these finite checks.',
'small_construction_cases':cases,'recurrence_diagnostics':recurrence,
'archimedean_choice_diagnostics':constants}
p=Path(__file__).with_name('reconstruction.json');p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}))
