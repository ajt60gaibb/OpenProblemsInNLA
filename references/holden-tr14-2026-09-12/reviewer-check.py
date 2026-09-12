from fractions import Fraction

def rank(a):
    a=[list(map(Fraction,row)) for row in a]; r=0
    for c in range(len(a[0])):
        p=next((i for i in range(r,len(a)) if a[i][c]),None)
        if p is None: continue
        a[r],a[p]=a[p],a[r]; v=a[r][c]; a[r]=[x/v for x in a[r]]
        for i in range(r+1,len(a)):
            v=a[i][c]
            if v: a[i]=[x-v*y for x,y in zip(a[i],a[r])]
        r+=1
    return r
cases=0
for k in range(1,4):
  for q in range(1,5):
    a=k*q+1; b=q//2; c=q-b; p1=a+b; p2=a+c; D=(2*k+1)*q
    E=[[0]*(p1+p2) for _ in range(3*a)]
    for i in range(a):
      E[i][i+b]=1; E[a+i][i]=-1; E[a+i][p1+i+c]=1; E[2*a+i][p1+i]=-1
    assert rank(E)==p1+p2
    sparse=[[(j,v) for j,v in enumerate(row) if v] for row in E]
    for d in range(D+1):
      def skew(i,j):
        if i<p1 and j>=p1: return int(i+j-p1==d)
        if j<p1 and i>=p1: return -int(j+i-p1==d)
        return 0
      K=[[0]*(3*a) for _ in range(3*a)]
      for u in range(a):
        for v in range(a):
          K[u][a+v]=int(u+v+q==d); K[a+u][v]=-int(u+v+q==d)
          K[u][2*a+v]=-int(u+v+b==d); K[2*a+u][v]=int(u+v+b==d)
          K[a+u][2*a+v]=int(u+v==d); K[2*a+u][a+v]=-int(u+v==d)
      for i in range(3*a):
        for j in range(3*a):
          assert K[i][j]==sum(vi*vj*skew(si,sj) for si,vi in sparse[i] for sj,vj in sparse[j])
      cases+=1
fourier=0
for m in range(3,11):
  for ell in range(1,13):
    N=(m-1)*(ell-1)+1
    assert [j for j in range(m*(ell-1)+1) if (j-(ell-1))%N==0]==[ell-1]
    fourier+=1
print(f'PASS: {cases} moment-basis Koszul identities, 12 exact rational full-column-rank checks for E, {fourier} Fourier exponent-range checks. Independent script; no submission imports.')
