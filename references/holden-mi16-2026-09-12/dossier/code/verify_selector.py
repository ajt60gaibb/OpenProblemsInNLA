#!/usr/bin/env python3
"""Exact small-order selector checks, including the full conservative p bound."""
import json
import math
import time
from fractions import Fraction as Q
from pathlib import Path
from exact_algebraic import moment_order,solve

start=time.monotonic()
p=moment_order(2,9,2)
mu=sum((Q(math.comb(p,j)*5**(p-j)*(-2)**j,2*j+1) for j in range(p+1)),Q())
assert 3**p < mu < 5**p
cases=[]
for lam in [[0],[2],[0,1],[1,3],['1/2','5/3'],[2,2],[2,2,2]]:
    result=solve(lam)
    cases.append({'spectrum':lam,**{k:str(v) for k,v in result.items()}})
output={'status':'PASS',
 'full_bound_selector_case':{'spectrum':[1,3],'B':9,'gap':2,'p':p,
  'lower_candidate':3,'upper_candidate':5,'selected_maximum':5,
  'exact_inequalities':'3^p < moment_p < 5^p',
  'moment_computation':'independent exact one-dimensional Haar integral expansion'},
 'end_to_end_cases':cases,
 'elapsed_seconds':round(time.monotonic()-start,3)}
out=Path(__file__).resolve().parents[1]/'verification'/'selector_checks.json'
out.write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
