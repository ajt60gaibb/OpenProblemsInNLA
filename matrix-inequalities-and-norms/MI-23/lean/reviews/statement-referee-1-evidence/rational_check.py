"""Independent exact arithmetic for the MI-23 statement review.
Uses only Python Fraction; no eigenvalue, CFC, or Lean proof claim.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

def M(rows):return [[Q(x) for x in row] for row in rows]
def diag(xs):return [[Q(xs[i]) if i==j else Q(0) for j in range(len(xs))] for i in range(len(xs))]
def mul(A,B):return [[sum((A[i][k]*B[k][j] for k in range(len(B))),Q(0)) for j in range(len(B[0]))] for i in range(len(A))]
def tr(A):return list(map(list,zip(*A)))
def pow(A,n):
 out=diag([1]*len(A))
 for _ in range(n):out=mul(out,A)
 return out

def det(A):
 if len(A)==0:return Q(1)
 return sum(((-1)**j*A[0][j]*det([row[:j]+row[j+1:] for row in A[1:]]) for j in range(len(A))),Q(0))
def serial(A):return [[str(v) for v in row] for row in A]
D=diag([16,Q(1,12),1]);Di=diag([Q(1,16),12,1])
T=M([[2,1,2],[1,25,-10],[2,-10,10]])
L=M([[1,0,0],[Q(1,2),1,0],[1,Q(-22,49),1]])
P=diag([2,Q(49,2),Q(150,49)])
assert mul(mul(L,P),tr(L))==T and det(L)==1
assert [det([row[:k] for row in T[:k]]) for k in [1,2,3]]==[2,49,150]
assert mul(D,Di)==diag([1,1,1]) and mul(Di,D)==diag([1,1,1])
A=pow(D,2);B=mul(mul(D,pow(T,8)),D)
G=mul(mul(D,T),D);H=mul(mul(D,pow(T,7)),D)
assert mul(mul(Di,B),Di)==pow(T,8)
GH=mul(G,H);AB=mul(A,B)
entry=GH[0][2];frob=sum((x*x for row in AB for x in row),Q(0));gap=entry*entry-frob
assert entry==Q(1260589125202,9)
assert frob==Q(2009446159144992718181231562721,107495424)
assert gap==Q(99434824489435745411095588895,107495424)>0
assert entry>140000000000 and frob<Q(138000000000)**2
assert Q(1,8)<Q(1,4) and 0<=Q(1,8)<=1 and 2>=1
result={'status':'PASS supplementary exact arithmetic only','LDL_factorization':True,'det_L':str(det(L)),'positive_pivots':[str(P[i][i]) for i in range(3)],'leading_minors':[str(det([row[:k] for row in T[:k]])) for k in [1,2,3]],'D_inverse_both_sides':True,'normalized_B_equals_T8':True,'T2':serial(pow(T,2)),'T7':serial(pow(T,7)),'T8':serial(pow(T,8)),'A':serial(A),'B':serial(B),'G':serial(G),'H':serial(H),'GH':serial(GH),'AB':serial(AB),'frobenius_entry_square_terms':[[str(x*x) for x in row] for row in AB],'GH_0_2':str(entry),'frobenius_squared_AB':str(frob),'strict_squared_gap':str(gap),'all_admissible_parameters':{'r':'1','s':'1','p':'2','t':'1/8'},'known_narrow_t_interval_avoided':True}
Path(__file__).with_name('rational-check.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: exact LDL, all nine product/Frobenius entries, rational squared gap, and canonical witness parameters.')
