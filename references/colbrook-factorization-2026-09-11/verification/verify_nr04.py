#!/usr/bin/env python3
"""Exact checks for the upper certificate and arithmetic in the NR-04 proof.
The geometric lower bound is proved in the accompanying manuscript, not by
numerical search. Requires sympy; writes results/nr04_verification.json.
"""
from pathlib import Path
import json
import sympy as s

ROOT=Path(__file__).resolve().parents[1]
t=list(range(-4,5))
d=s.Matrix(9,9,lambda i,j:(i-j)**2)
w=s.Matrix(9,7,lambda i,k: int(abs(t[i])==k) if k<5 else 2*max(t[i],0) if k==5 else 2*max(-t[i],0))
h=s.Matrix(7,9,lambda k,j:(k-abs(t[j]))**2 if k<5 else 2*max(-t[j],0) if k==5 else 2*max(t[j],0))
checks={
    'factor_product_exact':w*h==d,
    'factor_entries_nonnegative_integers':all(x.is_Integer and x>=0 for x in list(w)+list(h)),
    'ordinary_rank_three':d.rank()==3,
    'leading_three_minor_eight':d[:3,:3].det()==8,
    'factor_dimensions':w.shape==(9,7) and h.shape==(7,9),
    'zero_diagonal':all(d[i,i]==0 for i in range(9)),
    'strictly_positive_off_diagonal':all(d[i,j]>0 for i in range(9) for j in range(9) if i!=j),
}
allowed=[(a,b) for a in range(3,7) for b in range(3,7) if a+b<=9]
checks['sylvester_forces_factor_rank_at_most_four']=all(min(a,b)<=4 for a,b in allowed)
checks['two_rank_five_factors_impossible']=5+5-6>3
checks['six_vertex_3polytope_facet_bound_eight']=2*6-4==8
assert all(checks.values()),checks
result={
 'arithmetic':'exact integer/rational sympy',
 'checks':checks,'checks_passed':sum(checks.values()),
 'upper_certificate_W':[[int(x) for x in row] for row in w.tolist()],
 'upper_certificate_H':[[int(x) for x in row] for row in h.tolist()],
 'upper_certificate_factor_ranks':[w.rank(),h.rank()],
 'candidate_six_term_factor_rank_pairs_allowed_by_sylvester':allowed,
 'scope':'Checks supplement the geometric proof; no numerical infeasibility claim is made.'
}
path=ROOT/'results'/'nr04_verification.json';path.parent.mkdir(exist_ok=True)
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
