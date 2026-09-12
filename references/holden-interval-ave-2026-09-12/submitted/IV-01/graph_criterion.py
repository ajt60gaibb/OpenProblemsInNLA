#!/usr/bin/env python3
"""Check the extra combinatorial hypothesis of result.md.

Does NOT verify endpoint SR hypotheses; call minor_tools.check_sr separately.
A negative answer means this sufficient criterion does not apply, not that
there is a counterexample to IV-01.
"""
from collections import deque
from fractions import Fraction as Q

def fixed_graph_certificate(A,B,epsilon1):
    n=len(A)
    if epsilon1 not in (-1,1) or len(B)!=n or any(len(r)!=n for r in A+B):raise ValueError('Invalid data')
    A=[[Q(v) for v in r] for r in A];B=[[Q(v) for v in r] for r in B]
    if any((-1)**(i+j)*(B[i][j]-A[i][j])<0 for i in range(n) for j in range(n)):
        raise ValueError('Endpoints not checker-ordered')
    edges=[];zero_fixed=[]
    for i in range(n):
        for j in range(n):
            if A[i][j]!=B[i][j]:continue
            if A[i][j]==0:zero_fixed.append((i,j));continue
            if epsilon1*A[i][j]<=0:raise ValueError('Nonzero entry sign disagrees with epsilon1')
            edges.append((n+j,i) if epsilon1*(-1)**(i+j)>0 else (i,n+j))
    adj=[[] for _ in range(2*n)];indeg=[0]*(2*n)
    for u,v in edges:adj[u].append(v);indeg[v]+=1
    todo=deque(i for i in range(2*n) if not indeg[i]);order=[]
    while todo:
        u=todo.popleft();order.append(u)
        for v in adj[u]:
            indeg[v]-=1
            if not indeg[v]:todo.append(v)
    acyclic=len(order)==2*n
    zero_one_parity=len({(i+j)%2 for i,j in zero_fixed})<=1
    out={'acyclic':acyclic,'zero_fixed_one_parity':zero_one_parity,
         'criterion_applies':acyclic and zero_one_parity,'edges_0based':edges,'zero_fixed_0based':zero_fixed}
    if acyclic:
        h=[0]*(2*n)
        for k,u in enumerate(order):h[u]=k
        r=h[:n];c=[-v for v in h[n:]]
        assert all(h[u]<h[v] for u,v in edges)
        out.update({'row_potentials':r,'column_potentials':c,'topological_order':order})
    return out
