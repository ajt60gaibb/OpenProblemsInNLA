"""Independent reviewer arithmetic; standard library only, no supplied verifier imports."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import hashlib, json, math

ROOT = Path(__file__).resolve().parents[4]
def mat(rows): return [[F(x) for x in r] for r in rows]
def eye(n): return mat([[int(i == j) for j in range(n)] for i in range(n)])
def diag(xs): return mat([[x if i == j else 0 for j in range(len(xs))] for i,x in enumerate(xs)])
def transpose(a): return list(map(list,zip(*a)))
def add(a,b): return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(a,x): return [[v*x for v in r] for r in a]
def mul(a,b): return [[sum(x*y for x,y in zip(r,c)) for c in zip(*b)] for r in a]
def power(a,n):
    out=eye(len(a))
    for _ in range(n): out=mul(out,a)
    return out
def det(a):
    n=len(a)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*math.prod(a[i][p[i]] for i in range(n)) for p in permutations(range(n)))
def tr(a): return sum(a[i][i] for i in range(len(a)))
def fro2(a): return sum(x*x for r in a for x in r)
def char2(a,lam): return det(add(a,scale(eye(2),-lam)))
out={}
for ID in ['MI-19','MI-21','MI-23','MI-26','MI-29']:
    raw=(ROOT/'references/colbrook-matrix-2026-09-11/original-proofs'/f'{ID}.tex').read_bytes()
    txt=raw.decode('utf-8').replace('\r\n','\n').replace('\r','\n')
    normalized=txt.encode('utf-8')
    out[ID]={'sha256_utf8_lf':hashlib.sha256(normalized).hexdigest(),'original_bytes':len(raw),'normalized_bytes':len(normalized),'bare_cr_count':raw.count(b'\r')-raw.count(b'\r\n')}

X=mat([[13,0,13,13],[1,1,-2,1]])
A=mul(transpose(X),X)
assert A==mat([[170,1,167,170],[1,1,-2,1],[167,-2,173,167],[170,1,167,170]])
full=[F(0)]*7; restricted=[F(0)]*7
for p in permutations(range(4)):
    inv=sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
    v=math.prod(A[i][p[i]] for i in range(4))
    full[inv]+=v
    if p[1]==1: restricted[inv]+=v
assert full==[4999700,4886140,-199231,4712758,9568969,4886140,115600]
assert restricted==[4999700,4741130,0,4741130,9482260,4999700,0]
diff=[a-b for a,b in zip(full,restricted)]
factor=[145010,-344241,315869,-229160,115600]
expanded=[F(0)]*7
for i,x in enumerate(factor): expanded[i+1]+=x; expanded[i+2]+=x
assert diff==expanded
gap=sum(x*F(7,8)**i for i,x in enumerate(diff))
assert gap==F(-3235575,16384)
out['MI-19'].update(full_coefficients=full,restricted_coefficients=restricted,gap=gap)

C=diag([F(12,37),F(21,29)]); E=diag([F(35,37),F(20,29)])
S=scale(mat([[15,8],[8,-15]]),F(1,17)); I=eye(2)
assert add(power(C,2),power(E,2))==I and power(S,2)==I and transpose(S)==S
D=mul(mul(S,E),S); delta=F(5,3)
assert delta**2==det(D)/det(C)
h=tr(mul(diag([1/C[0][0],1/C[1][1]]),D))+2*delta
assert h==F(61697295,8682716)
N=add(D,scale(C,delta))
assert N==scale(mat([[443355,33000],[33000,605715]]),F(1,310097))
G2=scale(power(N,2),1/h)
assert G2==scale(mat([[3516940,616000],[616000,6547660]]),F(1,12158163))
L=add(G2,mul(mul(S,G2),S))
assert L==scale(mat([[8216600,-985600],[-985600,11912600]]),F(1,12158163))
w=mat([[1],[-4]]); lam=F(1351000,1350907); other=F(7970200,12158163)
assert mul(L,w)==scale(w,lam) and lam-1==F(93,1350907)
assert char2(L,other)==0 and tr(L)==lam+other and 0<other<1<lam
out['MI-21'].update(h=h,N=N,G_squared=G2,L=L,eigenvalues=[lam,other])

D=diag([16,F(1,12),1]); T=mat([[2,1,2],[1,25,-10],[2,-10,10]])
minors=[det([row[:i] for row in T[:i]]) for i in (1,2,3)]
assert minors==[2,49,150]
A=power(D,2); B=mul(mul(D,power(T,8)),D)
G=mul(mul(D,T),D); H=mul(mul(D,power(T,7)),D)
gh=mul(G,H)[0][2]; ab2=fro2(mul(A,B))
assert gh==F(1260589125202,9) and gh>140000000000
assert ab2==F(2009446159144992718181231562721,107495424) and ab2<138000000000**2
certificate=gh**2-ab2
assert certificate==F(99434824489435745411095588895,107495424)>0
assert det(power(G,2))*det(power(H,2))==det(power(A,2))*det(power(B,2))
out['MI-23'].update(T_minors=minors,GH_13=gh,AB_frobenius_squared=ab2,gap_certificate=certificate)

P=mat([[1,0],[0,0]]); Q=scale(mat([[9,12],[12,16]]),F(1,25))
assert power(P,2)==P and power(Q,2)==Q
def f(a): return add(a,scale(power(a,2),-1))
pq=add(P,Q); fpq=f(pq)
assert fpq==scale(mat([[-18,-12],[-12,0]]),F(1,25))
assert char2(fpq,F(6,25))==0 and char2(fpq,F(-24,25))==0
assert mul(fpq,mat([[1],[-2]]))==scale(mat([[1],[-2]]),F(6,25))
assert char2(pq,F(8,5))==0 and char2(pq,F(2,5))==0
A=add(P,scale(I,F(1,20))); B=add(Q,scale(I,F(1,20)))
for a in [A,B]:
    assert char2(a,F(21,20))==0 and char2(a,F(1,20))==0
    assert char2(f(a),F(19,400))==0 and char2(f(a),F(-21,400))==0
ab=add(A,B)
assert char2(ab,F(17,10))==0 and char2(ab,F(1,2))==0
assert char2(f(ab),F(1,4))==0 and char2(f(ab),F(-119,100))==0
assert F(1,4)>F(19,200)
out['MI-26'].update(PSD_eigenvalues=[F(6,25),F(-24,25)],PD_target_max=F(1,4),PD_orbit_upper_bound=F(19,200))

A=diag([2,1,F(1,2)]); M=mat([[-1,2,0],[2,1,2],[0,2,1]]); B=scale(M,F(1,5))
assert det(B)==F(-1,125) and transpose(B)==B
D=power(A,6); H=power(mul(mul(M,power(A,2)),M),4); J=power(mul(mul(A,power(M,2)),A),4)
assert det(H)==det(J)
def detpoly(d,k):
    coeff=[F(0)]*4
    for perm in permutations(range(3)):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(3) for j in range(i+1,3))
        term=[F(sign)]
        for i in range(3):
            nxt=[F(0)]*(len(term)+1)
            for j,x in enumerate(term): nxt[j]+=x*d[i][perm[i]]; nxt[j+1]+=x*k[i][perm[i]]
            term=nxt
        coeff=[a+b for a,b in zip(coeff,term)]
    return coeff
coeff=[a-b for a,b in zip(detpoly(D,J),detpoly(D,H))]
assert coeff==[0,F(2089017,16),F(-31188746592549,1024),0]
z=F(1,5**8); left=det(add(D,scale(H,z))); right=det(add(D,scale(J,z)))
assert left==F(136990346414301954149,61035156250000000000)
assert right==F(4537743716162890657,1907348632812500000)
gap=right-left
assert gap==F(21036678407451,156250000000000)>0
out['MI-29'].update(det_B=det(B),difference_coefficients=coeff,left_determinant=left,right_determinant=right,right_minus_left=gap)
out['result']='PASS: all independent exact assertions completed'
print(json.dumps(out,indent=2,default=str))
