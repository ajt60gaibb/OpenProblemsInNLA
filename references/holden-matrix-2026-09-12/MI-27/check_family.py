#!/usr/bin/env python3
"""Exact domain checks and high-precision (non-proof) ratio evaluations."""
from fractions import Fraction as F
from decimal import Decimal,localcontext
import json


def dec(x):return Decimal(x.numerator)/Decimal(x.denominator)

def main():
 rows=[]
 for k in (1,2,4,8,16,32,64,128):
  t=F(1,10**k);eta=t*t;d=(1-2*eta)*t*(1-t)
  S=[[1-t,F(0)],[F(0),t]]
  B=[[eta*(1-t)+d,d],[d,eta*t+d]]
  A=[[S[i][j]-B[i][j] for j in range(2)] for i in range(2)]
  for H in (A,B):
   assert H[0][0]>0 and H[1][1]>0
   assert H[0][0]*H[1][1]-H[0][1]*H[1][0]>0
  b=B[0][0]+B[1][1]
  assert A[0][0]+A[1][1]+b==1
  with localcontext() as ctx:
   ctx.prec=400
   bd=dec(b);td=dec(t)
   num=2*dec(d)*((1-td)/td).ln()
   ent=-bd*bd.ln()-(1-bd)*(1-bd).ln()
   ratio=num/ent
   rows.append({'t':f'1e-{k}','positive_definiteness':'EXACT PASS',
                'normalization':'EXACT PASS','ratio_numerical':str(ratio)[:36]})
 print(json.dumps({'result':'PASS','warning':'Ratios are numerical; the limit is proved in result.md.','cases':rows},indent=2))

if __name__=='__main__':main()
