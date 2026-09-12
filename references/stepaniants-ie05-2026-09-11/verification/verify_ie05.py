#!/usr/bin/env python3
"""Exact rational certificate for the IE-05 order-eight counterexample.

Uses Python integers and fractions only. No floating-point or external packages.
All arrays below reproduce the matrices and stage tables in full-proof.md.
This checks a finite certificate; it is not a formal proof-assistant verification.
"""
from fractions import Fraction as F
import json

H = [
 [1,-1,-3,-21,-41,-101,-325,63],
 [-1,3,1,17,71,291,1179,31],
 [-1,-1,13,-19,-56,-196,-752,16],
 [-1,-1,-3,189,-28,-98,-376,8],
 [-1,-1,-3,-51,581,-49,-188,4],
 [-1,-1,-3,-51,-213,1507,-94,2],
 [-1,-1,-3,-51,-213,-873,2589,1],
 [-1,1,-5,-55,-183,-683,-2683,1],
]
D = [8,16,240,47640,472430,3644970,16148136,5272]
T_expected = [
 [1,-1,-3,-21,-41,-101,-325,63],
 [0,2,-2,-4,30,190,854,94],
 [0,0,8,-44,-67,-107,-223,173],
 [0,0,0,120,-106,-116,-70,338],
 [0,0,0,0,397,-183,48,672],
 [0,0,0,0,0,1190,190,1342],
 [0,0,0,0,0,0,3063,2683],
 [0,0,0,0,0,0,0,5272],
]
H0 = [
 [1,-5,-8,-12,-16,-16,0,64],
 [-1,13,-4,-6,-8,-8,0,32],
 [-1,-3,51,-3,-4,-4,0,16],
 [-1,-3,-11,169,-2,-2,0,8],
 [-1,-3,-11,-43,511,-1,0,4],
 [-1,-3,-11,-43,-171,1365,0,2],
 [-1,-3,-11,-43,-171,-683,1,1],
 [-1,-3,-11,-43,-171,-683,-1,1],
]
D0 = [8,248,3286,36146,349184,2796544,2,5462]

def certify(M, squared_norms, zero_exception):
 n=len(M)
 assert all(len(row)==n for row in M)
 assert all(x>0 for x in squared_norms)
 for j in range(n):
  for k in range(n):
   assert sum(M[i][j]*M[i][k] for i in range(n)) == (squared_norms[j] if j==k else 0)
 L=[[F(int(i==j)) if i<=j else F(-1) for j in range(n)] for i in range(n)]
 if zero_exception:L[7][1]=F(0)
 U=[[F(v)for v in row]for row in M]
 maxima=[];locations=[];multipliers=[]
 for k in range(n):
  # Actual squared entries of the positively column-normalized active matrix.
  candidates=[(U[i][j]**2/squared_norms[j],i,j)for i in range(k,n)for j in range(k,n)]
  val,i,j=max(candidates)
  maxima.append(val);locations.append([i+1,j+1])
  assert U[k][k]>0
  # Exact largest-magnitude pivot check; equality is allowed.
  assert all(abs(U[i][k])<=U[k][k]for i in range(k,n))
  for i in range(k+1,n):
   ell=U[i][k]/U[k][k]
   assert ell==L[i][k] and abs(ell)<=1
   multipliers.append([i+1,k+1,str(ell)])
   for j in range(k+1,n):U[i][j]-=ell*U[k][j]
   U[i][k]=F(0)
 # Verify complete H=L U, not merely its pivots.
 assert all(sum(L[i][k]*U[k][j]for k in range(n))==M[i][j]for i in range(n)for j in range(n))
 rho2=max(maxima)/maxima[0]
 return U,maxima,locations,multipliers,rho2

U,mx,loc,mult,rho2=certify(H,D,True)
assert U==T_expected
assert mx==[F(a*a,5272)for a in [63,94,173,338,672,1342,2683,5272]]
assert rho2==F(5272,63)**2
assert [max(abs(row[j])for row in H)for j in range(8)]==[1,3,13,189,581,1507,2683,63]
U0,mx0,loc0,mult0,rho20=certify(H0,D0,False)
assert [U0[i][i]for i in range(8)]==[1,8,31,106,341,1024,1,5462]
assert mx0==[F(2601,3286)]+[F(a*a,5462)for a in [96,176,344,684,1366,2731,5462]]
assert rho20==F(17948132,2601)
assert [max(abs(row[j])for row in H0)for j in range(8)]==[1,13,51,169,511,1365,1,64]
gap=rho2-rho20
assert gap==F(117335164,1147041) and gap>0
print(json.dumps({
 'status':'PASS',
 'arithmetic':'Exact Python integers and fractions only',
 'dimension':8,
 'counterexample':'Positive-diagonal QR factor of L8 + e8 e2^T',
 'pivot_rule':'First available row among largest-magnitude active-column entries',
 'row_exchanges':0,
 'counterexample_stage_maxima_squared':list(map(str,mx)),
 'canonical_stage_maxima_squared':list(map(str,mx0)),
 'counterexample_maximizing_locations':loc,
 'canonical_maximizing_locations':loc0,
 'counterexample_growth':'5272/63',
 'counterexample_growth_squared':str(rho2),
 'canonical_growth_squared':str(rho20),
 'positive_squared_gap':str(gap),
 'counterexample_multipliers':mult,
 'canonical_multipliers':mult0,
},indent=2))
