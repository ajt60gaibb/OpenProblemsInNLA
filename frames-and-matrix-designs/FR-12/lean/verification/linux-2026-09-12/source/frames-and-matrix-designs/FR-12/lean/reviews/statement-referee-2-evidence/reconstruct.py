"""Independent exact FR-12 statement diagnostics, not a universal proof.
No imports from the author's checker. Matrix labels and permutation direction
are retained explicitly; recursive bounds are checked without logarithms.
"""
from itertools import product,permutations
from fractions import Fraction as F
from math import factorial,ceil
from pathlib import Path
import json

def hadamard(a):
    n=len(a)
    return all(x in (-1,1) for row in a for x in row) and all(
        sum(a[i][k]*a[j][k] for k in range(n))==(n if i==j else 0)
        for i in range(n) for j in range(n))

def all_small(n):
    return [tuple(tuple(a[i*n+j] for j in range(n)) for i in range(n))
            for a in product((-1,1),repeat=n*n)
            if hadamard(tuple(tuple(a[i*n+j] for j in range(n)) for i in range(n)))]

def construct(a,b,sigma):
    m=len(a)
    return tuple(a[i]+b[i] for i in range(m))+tuple(
        a[sigma[i]]+tuple(-x for x in b[sigma[i]]) for i in range(m))

def recover(c):
    m=len(c)//2
    a=tuple(row[:m] for row in c[:m])
    b=tuple(row[m:] for row in c[:m])
    sigma=[]
    for row in c[m:]:
        candidates=[i for i in range(m) if a[i]==row[:m]]
        assert len(candidates)==1
        sigma.append(candidates[0])
    return a,b,tuple(sigma)

small={n:all_small(n) for n in (1,2)}
assert len(small[1])==2 and len(small[2])==8
h4=((1,1,1,1),(1,-1,1,-1),(1,1,-1,-1),(1,-1,-1,1))
h4b=tuple(tuple(-x for x in row) for row in reversed(h4))
assert hadamard(h4) and hadamard(h4b) and h4!=h4b
domains=[(1,small[1],True),(2,small[2],True),(4,[h4,h4b],False)]
records=[]
for m,matrices,full in domains:
    outputs={}
    for a,b in product(matrices,repeat=2):
        for sigma in permutations(range(m)):
            c=construct(a,b,sigma)
            assert hadamard(c)
            assert recover(c)==(a,b,sigma)
            assert c not in outputs
            outputs[c]=(a,b,sigma)
    assert len(outputs)==len(matrices)**2*factorial(m)
    records.append({'m':m,'input_matrix_count_per_factor':len(matrices),
                    'entire_order_m_matrix_set_enumerated':full,
                    'permutations':factorial(m),'distinct_valid_outputs':len(outputs),
                    'every_input_recovered':True})

# Independent recurrence checks. Raising to the eighth power clears the
# displayed lower-bound exponent's denominator without numerical logarithms.
lower=2
recurrences=[]
for K in range(1,11):
    m=2**(K-1)
    lower=factorial(m)*lower**2
    if K>=2:
        assert factorial(m)>=(m//2)**(m//2)
        target_power=2**K*(K-1)*(K-2)
        assert lower**8>=2**target_power
        k=K-2
        assert F(2**K*(K-1)*(K-2),8)==F(2**(k+2)*k*(k+1),8)
        recurrences.append({'K':K,'n':2**K,'integer_recurrence_bound_bit_length':lower.bit_length(),
                            'eighth_power_bound_checked':True})

constant_checks=[]
for C in (F(1,1000),F(1,2),F(1),F(7),F(1000)):
    k=ceil(16*C+2)+1
    assert F(k*(k+1),8)>C*(k+2)
    constant_checks.append({'C':str(C),'k':k,'strict_exponent_gap':str(F(k*(k+1),8)-C*(k+2))})

out={'status':'PASS','scope':'Supplementary exact finite diagnostics only',
     'exact_small_input_counts':{'H1':len(small[1]),'H2':len(small[2])},
     'construction_domains':records,'recurrence_checks':recurrences,
     'constant_diagnostics':constant_checks,
     'universal_reason':'For k>16C+2, k>=2 gives C(k+2)<=2Ck<k²/8<k(k+1)/8; actual Archimedean and power/log bridges remain Lean proof obligations.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
