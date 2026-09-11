"""Finite certificates reconstructed from the earlier work; not formal proofs."""
from exact import *

def fib(n):
    a,b=0,1
    for _ in range(n): a,b=b,a+b
    return a

def band_bound(p,q):
    if p==0: return 1
    h=[0]
    for k in range(1,p+q+1): h.append(1+sum(h[max(1,k-p):k]))
    return h[-1]
def band_example(p,q):
    if p<1 or q<0: raise ValueError('p >= 1 and q >= 0 required')
    j=p+q+1; n=j+p; L=eye(n)
    for i in range(n):
        for k in range(max(0,i-p),i): L[i][k]=-Q(1)
    order=[p]+list(range(p))+list(range(p+1,n)); A=[[Q(0)]*n for _ in range(n)]; eta=Q(1,2**p)
    for k in range(j-1):
        u=[Q(0)]*n
        if k<=p:
            u[0]=Q(1)
            for i in range(1,k+1): u[i]=Q(2**(i-1))
        else: u[k]=Q(1)
        col=mv(L,u)
        for i,row in enumerate(order): A[row][k]=eta*col[i]
    for i in range(p,n): A[i][j-1]=Q(1)
    for k in range(j,n): A[k][k]=Q(1)
    return A,order,j

def ie13():
    count=0
    for p in range(1,7):
        for q in range(10):
            A,order,j=band_example(p,q); n=len(A)
            assert max(abs(v) for r in A for v in r)==1
            assert all(A[i][k]==0 for i in range(n) for k in range(n) if i>k+p or k>i+q)
            growth,schur,_=gepp(A,order,j-1)
            assert schur[j-1][j-1]==band_bound(p,q)==growth
            assert det(A)!=0; count+=1
    for p in range(1,13):
        assert band_bound(p,p)==2**(2*p-1)-Q(p-1)*Q(2)**(p-2)
        assert band_bound(p,0)==2**(p-1)
        for q in range(1,p+2): assert band_bound(p,q)==2**(p+q-1)-Q(q-1)*Q(2)**(q-2)
    for q in range(20):
        assert band_bound(1,q)==q+1
        assert band_bound(2,q)==fib(q+4)-1
    return {'status':'PASS','attaining_examples_checked':count,'small_table':[[band_bound(p,q) for q in range(7)] for p in range(1,5)]}

def cyclic_example(n):
    if n<4: raise ValueError('n >= 4 required')
    L=eye(n); U=[[Q(0)]*n for _ in range(n)]
    for i in range(n):
        for j in (i-1,i-2):
            if j>=0: L[i][j]=-Q(1)
        U[i][i]=Q(1,2) if i==1 else Q(1)
    U[0][1]=Q(1,2)
    for i in range(n): U[i][-1]=Q(fib(i+2)+(i==n-1))
    C=mm(L,U); order=[0,n-1]+list(range(1,n-1)); A=[[Q(0)]*n for _ in range(n)]
    for i,j in enumerate(order): A[j]=C[i]
    return A,L,U,order

def ie14():
    data=[]
    for n in range(4,31):
        A,L,U,order=cyclic_example(n)
        assert max(abs(v) for r in A for v in r)==1
        assert A[0][-1]==1 and A[-1][0]==-1
        assert all(A[i][j]==0 for i in range(n) for j in range(n) if abs(i-j)>1 and (i,j) not in [(0,n-1),(n-1,0)])
        growth,out,_=gepp(A,order)
        assert growth==fib(n+1)+1 and out==U
        data.append([n,growth])
    return {'status':'PASS','attaining_examples_checked':len(data),'values':data}

def lsmr_iterate(A,b,k):
    H=mm(tr(A),A); g=mv(tr(A),b); cols=[g]
    for _ in range(1,k): cols.append(mv(H,cols[-1]))
    V=tr(cols); F=mm(H,V); c=solve(mm(tr(F),F),mv(tr(F),g)); x=mv(V,c)
    assert mv(tr(F),sub(g,mv(H,x)))==[0]*k
    return x

def ie17():
    A=mat([[1,0,0],[0,6,0],[0,0,5],[0,0,0]]); b=list(map(Q,(11,1,1,1)))
    xs=[lsmr_iterate(A,b,k) for k in (1,2,3)]
    assert xs[0]==[Q(z,31201) for z in (11231,6126,5105)]
    assert xs[1]==[Q(z,55219) for z in (87659,7599,16865)]
    assert xs[2]==[Q(11),Q(1,6),Q(1,5)]
    C=mm(A,tr(A)); H=mm(tr(A),A)
    def quantities(x):
        z=mv(A,x); r=sub(b,z); s=dot(x,x); rr=dot(r,r)
        D=scale(1/s,add(add(scale(rr,eye(4)),scale(-1,outer(r,r))),outer(z,z)))
        nr=mv(tr(A),r); tilde=dot(nr,solve(add(scale(s,H),scale(rr,eye(3))),nr))
        return z,r,s,rr,D,tilde
    z,r,s,rr,D,t1=quantities(xs[0]); w=list(map(Q,(250,-1,1,27)))
    omega=dot(w,w); h=dot(w,z); kappa=Q(1979,2000)
    row=dot(w,mv(C,w))/omega; column=dot(w,mv(D,w))/omega
    assert row==Q(62561,63231) and max(row,column)<kappa
    c0=sub(r,[v*dot(w,r)/omega for v in w]); a0=sub([h*v/s for v in xs[0]],mv(tr(A),w))
    E=add(add(scale(-1/omega,mm(outer(w,w),A)),scale(1/s,outer(c0,xs[0]))),scale(h/(omega*s*kappa-h*h),outer(c0,a0)))
    B=add(A,E); assert mv(tr(B),sub(mv(B,xs[0]),b))==[0,0,0]
    upper_minors=principal_minors(add(scale(kappa,eye(3)),scale(-1,mm(tr(E),E))))
    assert min(upper_minors)>0
    _,r2,_,_,D2,t2=quantities(xs[1]); cut=Q(99,100)
    lower=add(add(scale(Q(5,6),C),scale(Q(1,6),D2)),scale(-cut,eye(4)))
    denominator=2407881992100; K=scale(denominator,lower)
    expected=mat([[206417059721,-50293465200,1125984433750,-1435003762500],[-50293465200,83658415217471,206242965000,-26574143750],[1125984433750,206242965000,61800032332121,80360210700],[-1435003762500,-26574143750,80360210700,11170189945871]])
    assert K==expected; lower_minors=principal_minors(K)
    assert min(lower_minors)>0 and kappa<cut
    assert t1<Q(1006,1000)<Q(1007,1000)<t2
    nr1=mv(tr(A),r); nr2=mv(tr(A),r2); assert dot(nr1,nr1)>dot(nr2,nr2)
    return {'status':'PASS','A':A,'b':b,'x1':xs[0],'x2':xs[1],'spectral_upper_squared':kappa,'spectral_lower_squared':cut,'upper_direction':w,'upper_row_quadratic':row,'upper_column_quadratic':column,'explicit_upper_E':E,'upper_psd_principal_minors':upper_minors,'lower_integer_matrix':K,'lower_denominator':denominator,'lower_principal_minors':lower_minors,'tilde_squared':[t1,t2],'normal_residual_squared':[dot(nr1,nr1),dot(nr2,nr2)]}

def aa(m,v):
    a=[1-mi for mi in m]; den=sum((ai*ai*vi*vi for ai,vi in zip(a,v)),Q(0))
    if den==0: return Q(0),[Q(0)]*len(v)
    alpha=sum((ai*vi*vi for ai,vi in zip(a,v)),Q(0))/den
    return alpha,[mi*(1-alpha*ai)*vi for mi,ai,vi in zip(m,a,v)]
def aa_pairs(m):
    out=[]
    for i in range(len(m)):
        for j in range(i+1,len(m)):
            den=abs(m[i]*(1-m[i]))+abs(m[j]*(1-m[j]))
            out.append(Q(0) if den==0 else (m[i]*m[j]*(m[j]-m[i])/den)**2)
    return max(out)
def aa_raw(m,v):
    r=list(v)
    for _ in range(2):
        w=[mi*ri for mi,ri in zip(m,r)]; d=sub(w,r); gamma=-dot(w,d)/dot(d,d)
        r=[mi*(wi+gamma*di) for mi,wi,di in zip(m,w,d)]
    return r

def ie18():
    out=[]
    for m in ([Q(1,10),Q(1,2),Q(3,5)],[Q(0),Q(1,2),Q(2,3)]):
        v=[Q(1)]*3; a,w=aa(m,v); b,z=aa(m,w); bound=aa_pairs(m); sq=dot(z,z)/3
        assert sq>bound**2 and z==aa_raw(m,v)
        out.append({'eigenvalues':m,'alpha':a,'R_v':w,'beta':b,'R2_v':z,'Lambda':bound,'actual_squared_ratio':sq,'squared_violation':sq/bound**2})
    assert out[0]['R2_v']==[Q(289,84241),-Q(756,84241),Q(1125,84241)]
    assert out[0]['Lambda']==Q(1,121)
    assert out[1]['R2_v']==[Q(0),-Q(18,637),Q(16,637)]
    for d in (10,100,1000):
        e=Q(1,d); m=[e*e,Q(1,2),Q(1,2)+e]; _,w=aa(m,[Q(1)]*3); _,z=aa(m,w)
        assert dot(z,z)/3>aa_pairs(m)**2
    return {'status':'PASS','examples':out,'continuous_family':'See analytic proof draft; finite checks are not the proof.'}

def ie19():
    S=add(eye(3),mat([[1]*3]*3)); J=scale(Q(1,2),mat([[4,1,1],[1,4,1],[1,1,4]]))
    assert all(0<J[i][j]<=S[i][j] for i in range(3) for j in range(3))
    assert all(J[i][i]>sum(J[i][j] for j in range(3) if j!=i) for i in range(3))
    ji,si=inv(J),inv(S); nj,ns=norm_inf(ji),norm_inf(si); assert nj==Q(7,9)<Q(5,4)==ns
    for n in range(3,9):
        for m in (Q(1,3),Q(1),Q(2)):
            for alpha in ((n-2)*m,(n+1)*m):
                D=alpha+m
                for e in (m,m/2,m/10):
                    T=add(scale(D-e,eye(n)),scale(e,mat([[1]*n]*n)))
                    assert norm_inf(inv(T))==(D+(2*n-3)*e)/((D-e)*(D+(n-1)*e))
                sn=(alpha+2*(n-1)*m)/(alpha*(alpha+n*m))
                gap=(n-1)*m*(alpha+2*m)/(alpha*(alpha+m)*(alpha+n*m))
                assert sn-1/D==gap>0
    return {'status':'PASS','J':J,'S':S,'J_inverse':ji,'S_inverse':si,'J_inverse_norm':nj,'S_inverse_norm':ns,'sharp_infimum':'1/(alpha+m)'}

def ie23():
    A=mat([[1,1,0],[1,0,1]]); B=scale(Q(1,3),mat([[1,1],[2,-1],[-1,2]])); X=mat([[0,0],[1,0],[0,1]]); v=list(map(Q,(-1,1,1)))
    assert B==mm(tr(A),inv(mm(A,tr(A))))
    assert mm(A,B)==eye(2)==mm(A,X) and B!=X
    gram=mm(tr(B),B); assert gram==scale(Q(1,3),mat([[2,-1],[-1,2]]))
    assert mm(tr(X),X)==eye(2)
    assert mv(gram,[Q(1),-Q(1)])==[1,-1]
    assert mv(A,v)==[0,0] and mv(tr(B),v)==[0,0]
    assert X==add(B,scale(Q(1,3),outer(v,[Q(1),Q(1)])))
    for m in range(2,10):
        AA=[[Q(1)]+[Q(i==j) for j in range(m)] for i in range(m)]
        invgram=add(eye(m),scale(-Q(1,m+1),mat([[1]*m]*m)))
        assert mm(mm(AA,tr(AA)),invgram)==eye(m)
    return {'status':'PASS','A_small':A,'A_dagger':B,'other_minimizer':X,'Gram':gram,'common_norm':'2^(1/2-1/p)','all_minimizers':'B+t*(-1,1,1)^T*(1,1), |t|<=1/3'}
