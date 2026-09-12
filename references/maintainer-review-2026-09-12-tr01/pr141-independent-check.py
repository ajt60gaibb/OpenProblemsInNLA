"""Independent finite combinatorial and exact block checks for PR141.
No submitted scripts, Lean files, or stored audit results are imported.
These checks supplement the analytic all-parameter manuscript audit.
"""
from collections import Counter,defaultdict
from fractions import Fraction as F
from random import Random
from pathlib import Path
import json

def partitions(n):
    w=[0]*n; counts=[1]
    def rec(i):
        if i==n:
            if min(counts)>=2:yield tuple(w)
            return
        for j in range(len(counts)):
            w[i]=j; counts[j]+=1
            yield from rec(i+1)
            counts[j]-=1
        if n-i>=2:
            w[i]=len(counts);counts.append(1)
            yield from rec(i+1)
            counts.pop()
    yield from rec(1)

def graph(w):
    n=len(w);p=n//2;v=max(w)+1
    ed=[tuple(sorted((w[j],w[(j+1)%n]))) for j in range(n)]
    multiplicity=Counter(ed)
    odd=set()
    for (a,b),m in multiplicity.items():
        if a!=b and m%2:odd.update((a,b))
    return p-v,len(odd),sum(m for (a,b),m in multiplicity.items() if a==b),ed

def rank(rows):
    basis={}
    for x in rows:
        while x:
            j=x.bit_length()-1
            if j in basis:x^=basis[j]
            else:basis[j]=x;break
    return len(basis)

allparts={p:list(partitions(2*p)) for p in range(2,6)}
counts={}; pairs_checked=0; surviving=0
for p,words in allparts.items():
    freq=Counter()
    for w in words:
        s,t,ell,ed=graph(w)
        assert ell<=4*t+12*s+2
        freq[(s,t)]+=1
    for (s,t),number in freq.items():
        assert number<=8*p*3**p*(4*p+1)**(74*(s+t))
    counts[p]={'equality_partitions':len(words),'zero_defect_count':freq[(0,0)],'classes':len(freq)}
    if p>4:continue
    for w in words:
        s,t,ell,ed=graph(w)
        for rho in words:
            blocks=defaultdict(list)
            for j,b in enumerate(rho):blocks[b].append(j)
            rows=[];forbidden=False
            for block in blocks.values():
                z=0
                for j in block:
                    a,b=ed[j];z^=(1<<a)^(1<<b)
                if len(block)==2 and z.bit_count()==2:
                    forbidden=True;break
                rows.append(z)
            pairs_checked+=1
            if forbidden:continue
            surviving+=1
            h=rank(rows);d=p-len(blocks)
            assert t<=12*d+4*h

# Exact 2x2 projection-block transfer, including nonreal-root traces.
def mm(A,B):return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
rng=Random(141);blockchecks=0;negative=0
for case in range(500):
    a,b=rng.randrange(1,25),rng.randrange(1,25)
    lam=F(a*a,a*a+b*b); off=F(a*b,a*a+b*b)
    theta=F(rng.randrange(1,100),100)
    eta=F(rng.randrange(1,100),100)
    delta=theta*eta*eta/F(rng.randrange(64,150)) if case%2 else F(rng.randrange(1,50),100)
    A=[[(1-delta)*(lam-theta),(1-delta)*off],[-delta*off,-delta*(1-lam-theta)]]
    a2=delta*(1-delta)*theta*(1-theta)
    power=[[F(1),F(0)],[F(0),F(1)]]
    for exponent in range(1,13):
        power=mm(power,A)
        if exponent%2:continue
        p=exponent//2;tr=power[0][0]+power[1][1]
        assert tr>=-2*a2**p
        if tr<0:negative+=1
        if delta<=theta*eta*eta/64:
            indicator=int(abs(lam-theta)>theta*eta)
            assert indicator*(theta*eta/2)**(2*p)<=tr+2*a2**p
        blockchecks+=1

# The rank threshold at x=20000 and all explicit constant inequalities.
K0=576*4**24;R0=2**20000;C=200*R0+8196*K0
assert 80053<2**17 and 20000-1-1000*17>0
assert C>=200*R0 and C>=2048*K0
assert F(3,4)*2048>=64*16
for p in range(2,257):assert 128*p*(4*p+1)<=64**p
report={'status':'PASS','pr_head':'2c7655f234bbb3b3134133ebae34eb479e9469e1','proof_commit':'ed21181197ac839eac95f549404f94e7e3aa6e10','equality_counts':counts,'joint_partition_pairs_checked':pairs_checked,'nonforbidden_binary_rank_checks':surviving,'exact_two_projection_block_checks':blockchecks,'negative_even_trace_cases':negative,'scope':'finite corroboration; universal validity assessed by reading the complete proof'}
Path('/private/tmp/nla-review-trace/pr141-independent-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
