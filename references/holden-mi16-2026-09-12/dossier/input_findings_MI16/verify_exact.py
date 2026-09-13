#!/usr/bin/env python3
"""Exact rational regression checks for the proved MI-16 spectral subcase."""
from fractions import Fraction as F
from itertools import permutations
from math import comb,factorial
import random,json


def permanent(H):
 n=len(H);total=F(0)
 for sigma in permutations(range(n)):
  v=F(1)
  for i,j in enumerate(sigma):v*=H[i][j]
  total+=v
 return total


def elementary(t):
 e=[F(1)]+[F(0)]*len(t)
 for x in t:
  for j in range(len(t),0,-1):e[j]+=x*e[j-1]
 return e


def expansion(n,alpha,beta,t):
 return sum(F(factorial(j))*beta**(n-j)*(alpha-beta)**j*ej
            for j,ej in enumerate(elementary(t)))


def candidates(n,alpha,beta):
 return [sum(F(comb(k,j)*factorial(j))*beta**(n-j)*(alpha-beta)**j/F(k)**j
             for j in range(k+1)) for k in range(1,n+1)]


def compositions(total,n):
 if n==1:
  yield (total,);return
 for x in range(total+1):
  for tail in compositions(total-x,n-1):yield (x,)+tail


def main():
 rng=random.Random(160912);random_tests=0;support_tests=0;grid_tests=0
 for n in range(1,7):
  for _ in range(12):
   alpha=F(rng.randrange(7),rng.randrange(1,5));beta=F(rng.randrange(7),rng.randrange(1,5))
   v=[rng.randrange(-3,4) for _ in range(n)]
   if not any(v):v[0]=1
   scale=sum(x*x for x in v);t=[F(x*x,scale) for x in v]
   H=[[beta*int(i==j)+(alpha-beta)*F(v[i]*v[j],scale) for j in range(n)] for i in range(n)]
   value=permanent(H)
   assert value==expansion(n,alpha,beta,t)
   assert value<=max(candidates(n,alpha,beta))
   random_tests+=1
  for alpha,beta in [(F(0),F(0)),(F(0),F(1)),(F(1),F(0)),(F(1),F(1)),(F(1,3),F(7,4)),(F(4),F(1,2))]:
   vals=candidates(n,alpha,beta)
   for k in range(1,n+1):
    H=[[beta*int(i==j)+(alpha-beta)*F(int(i<k and j<k),k) for j in range(n)] for i in range(n)]
    assert permanent(H)==vals[k-1];support_tests+=1
   if alpha>=beta:assert max(vals)==vals[-1]
   if beta==0:assert max(vals)==F(factorial(n))*alpha**n/F(n)**n
 for n in range(1,6):
  for alpha,beta in [(F(0),F(1)),(F(1,4),F(1)),(F(3,4),F(1)),(F(1),F(1)),(F(2),F(1))]:
   bound=max(candidates(n,alpha,beta))
   for c in compositions(6,n):
    t=[F(x,6) for x in c]
    assert expansion(n,alpha,beta,t)<=bound;grid_tests+=1
 assert candidates(3,F(0),F(1))==[F(0),F(1,2),F(4,9)]
 print(json.dumps({'result':'PASS','random_exact_permanent_comparisons':random_tests,
                   'equal_support_exact_permanent_comparisons':support_tests,
                   'rational_simplex_grid_checks':grid_tests,
                   'note':'Finite regression checks supplement the written universal subcase proof.'},indent=2))

if __name__=='__main__':main()
