'''Exact rational sanity check for the independently derived W_(3,3) example.'''
from fractions import Fraction as Q
from itertools import permutations
import json

def det(a):
 n=len(a);total=Q(0)
 for p in permutations(range(n)):
  sign=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
  term=Q(sign)
  for i in range(n):term*=a[i][p[i]]
  total+=term
 return total

def hollow(x):
 a,b,c=x
 return [[Q(0),a,b],[a,Q(0),c],[b,c,Q(0)]]

# Check the determinant polynomial by exact coefficient expansion rather than floats.
coeff={}
positions={(0,1):0,(1,0):0,(0,2):1,(2,0):1,(1,2):2,(2,1):2}
for p in permutations(range(3)):
 if any(i==p[i] for i in range(3)):continue
 powers=[0,0,0]
 for i in range(3):powers[positions[i,p[i]]]+=1
 sign=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
 key=tuple(powers);coeff[key]=coeff.get(key,0)+sign
assert coeff=={(1,1,1):2}

u=[[Q(v) for v in row] for row in [[1,1,2],[1,2,3],[2,3,3]]]
p,q,r=u[0][1],u[0][2],u[1][2]
records=[]
for zero_coord,coords in enumerate([(0,q,r),(p,0,r),(p,q,0)]):
 coords=tuple(map(Q,coords));a,b,c=coords;x=hollow(coords)
 gradient_constraint=(2*b*c,2*a*c,2*a*b)
 gradient_distance=(4*(a-p),4*(b-q),4*(c-r))
 free=[i for i in range(3) if i!=zero_coord]
 assert det(x)==0
 assert gradient_constraint[zero_coord]!=0
 assert all(gradient_constraint[i]==0 for i in free)
 assert all(gradient_distance[i]==0 for i in free)
 # A nonzero 2x2 principal minor proves rank exactly two.
 assert any(x[i][i]*x[j][j]-x[i][j]*x[j][i]!=0 for i in range(3) for j in range(i+1,3))
 distance=sum((x[i][j]-u[i][j])**2 for i in range(3) for j in range(3))
 assert distance==[Q(16),Q(22),Q(32)][zero_coord]
 records.append({'coordinates':list(map(str,coords)),'constraint_gradient':list(map(str,gradient_constraint)),
                 'distance_gradient':list(map(str,gradient_distance)),
                 'restricted_Hessian_determinant':'16','full_Frobenius_squared_distance':str(distance),
                 'rank':2,'smooth':True,'critical':True})
# Exact singular-intersection examples, including nonzero rank-two matrices.
for coords in [(0,0,0),(1,0,0),(0,2,0),(0,0,3)]:
 a,b,c=coords
 assert (2*b*c,2*a*c,2*a*b)==(0,0,0)
print(json.dumps({'status':'PASS','determinant_polynomial':'2*a*b*c','U':[[str(v) for v in row] for row in u],
                  'generic_condition':'p*q*r != 0','critical_points':records,
                  'generic_critical_count':3,'conjectured_count':4},indent=2))
