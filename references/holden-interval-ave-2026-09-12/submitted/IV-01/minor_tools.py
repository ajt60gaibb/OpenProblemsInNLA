#!/usr/bin/env python3
"""Exact minors and sign regularity checks. Standard library only."""
from fractions import Fraction as Q
from itertools import combinations
from math import lcm

def det(A):
    n=len(A)
    if n==0:return Q(1)
    B=[[Q(v) for v in r] for r in A];d=Q(1)
    for k in range(n):
        p=next((i for i in range(k,n) if B[i][k]),None)
        if p is None:return Q(0)
        if p!=k:B[k],B[p]=B[p],B[k];d=-d
        pivot=B[k][k];d*=pivot
        for i in range(k+1,n):
            if not B[i][k]:continue
            r=B[i][k]/pivot
            for j in range(k+1,n):B[i][j]-=r*B[k][j]
            B[i][k]=Q(0)
    return d

def minor(A,I,J):return det([[A[i][j] for j in J] for i in I])

def all_minors(A):
    out=[]
    for k in range(1,min(len(A),len(A[0]))+1):
        for I in combinations(range(len(A)),k):
            for J in combinations(range(len(A[0])),k):out.append((I,J,minor(A,I,J)))
    return out

def check_sr(A,signature,nonsingular=True):
    stats={k:{'positive_signed':0,'zero':0,'negative_signed':0} for k in range(1,len(signature)+1)};bad=[]
    for I,J,v in all_minors(A):
        s=signature[len(I)-1]*v
        stats[len(I)]['positive_signed' if s>0 else 'negative_signed' if s<0 else 'zero']+=1
        if s<0:bad.append({'rows_0based':I,'cols_0based':J,'value':str(v)})
    nonsing=det(A)!=0
    return {'valid':not bad and (not nonsingular or nonsing),'nonsingular':nonsing,'minor_counts':stats,'bad':bad}

def coordinate_bounds(A,signature,i,j):
    n=len(A);lo=hi=None;lowers=[];uppers=[]
    for k in range(1,n+1):
        for I in combinations(range(n),k):
            if i not in I:continue
            for J in combinations(range(n),k):
                if j not in J:continue
                a=signature[k-1]*minor(A,I,J)
                co=signature[k-1]*(-1)**(I.index(i)+J.index(j))*minor(A,[r for r in I if r!=i],[c for c in J if c!=j])
                if co>0:
                    bound=-a/co
                    if lo is None or bound>lo:lo=bound;lowers=[(I,J)]
                    elif bound==lo:lowers.append((I,J))
                elif co<0:
                    bound=-a/co
                    if hi is None or bound<hi:hi=bound;uppers=[(I,J)]
                    elif bound==hi:uppers.append((I,J))
                elif a<0:raise ValueError('Input is not SR')
    return lo,hi,lowers,uppers

def scale_to_integers(A):
    q=lcm(*(Q(v).denominator for r in A for v in r))
    return [[int(Q(v)*q) for v in r] for r in A],q

def vandermonde_sr(n,signature,t=Q(1,10)):
    x=[Q(i+1,n+1) for i in range(n)];prev=1;lam=[]
    for j,e in enumerate(signature):lam.append(e*prev*t**j);prev=e
    A=[[sum(lam[k]*(x[i]*x[j])**k for k in range(n)) for j in range(n)] for i in range(n)]
    out=check_sr(A,signature)
    if not out['valid'] or any(v['zero'] for v in out['minor_counts'].values()):raise ValueError('Scale is not SSR')
    return A
