"""Independent finite checks for PR130; all-n proof is reviewed analytically.
No submitted verification code is loaded. Fractions only for decisions.
"""
from fractions import Fraction as F
from random import Random
from pathlib import Path
import json, subprocess, hashlib
rng=Random(130)

def matrix(n):
    return [[F(1) if j==n-1 or i==j else F(-1,2) if i>j else F(0) for j in range(n)] for i in range(n)]
def check(A,n):
    eps=F(1,2**(n*n+n+1)); bound=eps; C=F(3,2)**(n-1)
    original=max(abs(z) for row in A for z in row); peak=original
    m=n; k=0
    while m:
        expected=matrix(n)
        for i in range(m):
            for j in range(m):
                target=F(3,2)**k if k+j==n-1 else expected[k+i][k+j]
                assert abs(A[i][j]-target)<=bound<=F(1,8)
        peak=max(peak,max(abs(z) for row in A for z in row))
        assert A[0][0]>0
        if m==1:break
        assert A[0][0]>max(abs(row[0]) for row in A[1:])
        A=[[A[i][j]-A[i][0]*A[0][j]/A[0][0] for j in range(1,m)] for i in range(1,m)]
        k+=1;m-=1;bound*=2**(n+2)
    assert peak/original>C/2
    return peak/original

runs=0
for n in range(2,13):
    W=matrix(n); eps=F(1,2**(n*n+n+1))
    assert check(W,n)==F(3,2)**(n-1)
    for case in range(12):
        # First two boxes use same-sign endpoints; others use independent dyadic interior values.
        A=[[z+eps*(F(-1) if case==0 else F(1) if case==1 else F(rng.randrange(-8,9),8)) for z in row] for row in W]
        check(A,n);runs+=1

for n in range(2,257):
    B=2**(n+2);d=F(1,2**(n*n+n+1));c=F(3,2)**(n-1)
    assert B**(n-1)*d==F(1,8)
    assert 2+2**(n+1)<=B
    assert c<=2**n
    assert (c-F(1,8))/(1+d)>=F(7,9)*c>c/2
    assert n*n*(n*n+n+5)<=3*n**4

examples=[]
for c1,c2 in [(1,F(1)),(10,F(1)),(2,F(1,10**6)),(50,F(1,100))]:
    n=2
    while True:
        x=F(3,2)**(n-1)/(2*n**c1);K=n*n*(n*n+n+5)
        if x>=1 and c2*x>K:break
        n+=1
    examples.append({'c1':c1,'c2':str(c2),'n':n,'x':str(x),'K':K})
repo=Path('/private/tmp/nla-pr130');p='linear-systems-and-elimination/IE-04/README.md'
a=subprocess.check_output(['git','show','origin/main:'+p],cwd=repo);b=(repo/p).read_bytes();marker=b'## Context and notation'
assert a[a.index(marker):]==b[b.index(marker):]
report={'head':'397c70a40e8ee785201800d20f798c7d9b73c22f','verdict':'PASS','arithmetic':'fractions.Fraction only','unperturbed_dimensions':[2,12],'perturbed_checks':runs,'scalar_dimensions':[2,256],'illustrative_contradictions':examples,'unchanged_original_target_suffix_sha256':hashlib.sha256(b[b.index(marker):]).hexdigest(),'scope':'Finite corroboration; the all-n proof and every-real-constant quantifier are checked analytically.'}
Path('/private/tmp/nla-review-trace/pr130-independent-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({**report,'illustrative_contradictions':[{k:v for k,v in t.items() if k!='x'} for t in examples]},indent=2))
