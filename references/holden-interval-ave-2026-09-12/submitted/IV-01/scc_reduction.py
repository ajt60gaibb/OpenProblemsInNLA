#!/usr/bin/env python3
"""Exact graph certificate for cycle_reduction.md.
Does not decide SR or the unrestricted conjecture. Indices are zero based.
"""
from fractions import Fraction as Q
from collections import deque
from graph_criterion import fixed_graph_certificate

def scc_certificate(A,B,epsilon1):
    n=len(A);base=fixed_graph_certificate(A,B,epsilon1)
    edges=base['edges_0based'];N=2*n
    adj=[[] for _ in range(N)];rev=[[] for _ in range(N)]
    for u,v in edges:adj[u].append(v);rev[v].append(u)
    seen=set();post=[]
    for start in range(N):
        if start in seen:continue
        seen.add(start);stack=[(start,0)]
        while stack:
            u,k=stack[-1]
            if k==len(adj[u]):post.append(u);stack.pop();continue
            v=adj[u][k];stack[-1]=(u,k+1)
            if v not in seen:seen.add(v);stack.append((v,0))
    comp=[-1]*N;count=0
    for start in reversed(post):
        if comp[start]>=0:continue
        comp[start]=count;todo=[start]
        while todo:
            u=todo.pop()
            for v in rev[u]:
                if comp[v]<0:comp[v]=count;todo.append(v)
        count+=1
    cedges=sorted({(comp[u],comp[v]) for u,v in edges if comp[u]!=comp[v]})
    cadj=[[] for _ in range(count)];indeg=[0]*count
    for u,v in cedges:cadj[u].append(v);indeg[v]+=1
    todo=deque(i for i in range(count) if not indeg[i]);h=[0]*count;visited=0
    while todo:
        u=todo.popleft();visited+=1
        for v in cadj[u]:
            h[v]=max(h[v],h[u]+1);indeg[v]-=1
            if not indeg[v]:todo.append(v)
    assert visited==count
    height=[h[comp[u]] for u in range(N)]
    assert all(height[u]<height[v] for u,v in edges if comp[u]!=comp[v])
    assert all(height[u]==height[v] for u,v in edges if comp[u]==comp[v])
    return {'components':comp,'heights':height,'row_exponents':height[:n],
            'column_exponents':[-x for x in height[n:]],
            'cycle_edges':[(u,v) for u,v in edges if comp[u]==comp[v]],
            'opened_edges':[(u,v) for u,v in edges if comp[u]!=comp[v]],
            'zero_fixed_0based':base['zero_fixed_0based']}

def scaled_endpoint(B,certificate,t):
    t=Q(t)
    if t<=0:raise ValueError('t must be positive')
    r=certificate['row_exponents'];c=certificate['column_exponents']
    return [[Q(v)*(1+t)**(r[i]+c[j]) for j,v in enumerate(row)] for i,row in enumerate(B)]
