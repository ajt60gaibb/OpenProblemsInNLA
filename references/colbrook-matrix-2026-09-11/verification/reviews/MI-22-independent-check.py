"""Independent rational audit; parses R,S from original TeX, no submitted code."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[4]
SOURCE = ROOT / 'references/colbrook-matrix-2026-09-11/original-proofs'
def normtext(path):
    return path.read_bytes().decode('utf-8').replace('\r\n', '\n')
def mm(a,b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))), F(0)) for j in range(len(b[0]))] for i in range(len(a))]
def diag(v):
    return [[F(v[i]) if i==j else F(0) for j in range(len(v))] for i in range(len(v))]
def sub(a,b): return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def power(a,n):
    result=diag([1]*len(a))
    for _ in range(n): result=mm(result,a)
    return result
def det(a):
    result=F(0)
    for p in permutations(range(len(a))):
        v=F((-1)**sum(p[i]>p[j] for i in range(len(a)) for j in range(i+1,len(a))))
        for i,j in enumerate(p): v*=a[i][j]
        result+=v
    return result
def minors(a):
    assert a==list(map(list,zip(*a)))
    return [det([r[:k] for r in a[:k]]) for k in range(1,len(a)+1)]
def frob(a): return sum((x*x for row in a for x in row),F(0))

tex=normtext(SOURCE/'MI-22.tex')
roots={}
for name in ['R','S']:
    body=re.search(name+r'=10\^{-15\}\\begin\{pmatrix\}(.*?)\\end\{pmatrix\}',tex,re.S).group(1)
    roots[name]=[[F(int(x.strip()),10**15) for x in row.split('&')] for row in body.strip().split('\\\\')]
R,S=roots['R'],roots['S']
A=diag([256,F(1,256),1])
B=[[F(x) for x in row] for row in [[17,-4,0],[-4,16385,-8192],[0,-8192,4096]]]
Ai=diag([F(1,16),16,1]); C=mm(mm(Ai,B),Ai)
assert C==[[F(17,256),-4,0],[-4,4194560,-131072],[0,-131072,4096]]
assert minors(B)==[17,278529,4096]
comparisons={
    'B-2^-10 I':sub(B,diag([F(1,1024)]*3)),
    'C-2^-10 I':sub(C,diag([F(1,1024)]*3)),
    'R-9/20 I':sub(R,diag([F(9,20)]*3)),
    '8I-R':sub(diag([8]*3),R),
    'S-9/20 I':sub(S,diag([F(9,20)]*3)),
    '4I-S':sub(diag([4]*3),S),
}
certminors={key:minors(value) for key,value in comparisons.items()}
assert all(v>0 for row in certminors.values() for v in row)
residuals=[frob(sub(power(R,8),C)),frob(sub(power(S,8),B))]
assert all(r<F(1,10**16) for r in residuals)
assert F(9,20)**8>F(1,1024)
assert 2**23<64**4
assert sum(C[i][i] for i in range(3))<8**8
assert sum(B[i][i] for i in range(3))<4**8
error=32*16*F(64,10**8)*(4**7+8*7*4**6)
assert error==F(6291456,78125)<100
approx=mm(mm(mm(diag([32,F(1,32),1]),R),diag([16,F(1,16),1])),power(S,7))
assert approx[0][1]>11000
right=frob(mm(A,B))
assert right==F(6807858741265,65536)<10200**2
report={
    'status':'PASS',
    'method':'Independent Python fractions, permutation determinants, sequential powers; R/S parsed from original TeX',
    'normalized_tex_sha256':{p.stem:hashlib.sha256(normtext(p).encode('utf-8')).hexdigest() for p in [SOURCE/'MI-04.tex',SOURCE/'MI-22.tex',SOURCE/'MI-09-partial.tex']},
    'positive_leading_minors':{k:list(map(str,v)) for k,v in certminors.items()},
    'root_residual_frobenius_squared':list(map(str,residuals)),
    'rational_left_entry':str(approx[0][1]),
    'rational_left_entry_gt_11000':True,
    'propagated_error':str(error),
    'right_frobenius_squared':str(right),
    'limitations':'Finite exact arithmetic only; analytic proof requires separate written review.'
}
Path(__file__).with_name('MI-22-independent-check.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in report.items() if k in ['status','normalized_tex_sha256','propagated_error','right_frobenius_squared']},indent=2))
