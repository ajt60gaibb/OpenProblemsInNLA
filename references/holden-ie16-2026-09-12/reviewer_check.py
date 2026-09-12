"""Reviewer-written independent checks of the elementary finite proof."""
from fractions import Fraction as F
from itertools import combinations
from cmath import exp, pi

e=F(1,1000)
D=1+e+3*e**2+e**3+e**4
c=-(1+e)/D
m=3*e*(1+e+e**2)/D
U=(1+e)**3
V=1-F(3,2)*e-F(3,2)*e**2+e**3
W2=F(27,4)*(e-e**2)**2
assert (1+U*c)**2 == (1+V*c)**2+W2*c*c == m*m
assert 1+U*c == -m
assert U*(1+U*c)<0<V+c*(V*V+W2)
H=1-3*e+e**2-3*e**3+e**4
Q=(1+e)**2*(1+e+e**2)
assert H+2*Q==3*D
assert H*U*(1+c*U)+2*Q*(V+c*(V*V+W2))==0
coarse=e*(9+36*e+36*e**2+16*e**3)/(4*(1-e)**4)
assert m==F(3003003000,1001003001001)>F(299,100000)
assert coarse<F(23,10000)
assert F(299,100000)/F(23,10000)==F(13,10)>4/F(31,10)
print('Independent rational cubic-image minimax, weight identity, and analytic coarse bounds: PASS')
# Separate floating-point diagnostic, not the basis for rigorous inequalities.
w=exp(2j*pi/3)
z=[w**a+float(e)*w**b for a in range(3) for b in range(3)]
values=[]
for S in combinations(z,5):
    lagranges=[]
    for j in range(5):
        cardinal=1+0j
        for h in range(5):
            if h!=j: cardinal*=(-S[h])/(S[j]-S[h])
        lagranges.append(abs(cardinal))
    values.append(1/sum(lagranges))
assert len(values)==126
print('Independent complex-arithmetic enumeration diagnostic: B =',max(values),'ratio =',float(m)/max(values))
