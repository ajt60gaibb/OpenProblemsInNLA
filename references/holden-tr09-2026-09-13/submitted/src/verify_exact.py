#!/usr/bin/env python3
"""Finite exact-arithmetic checks for round 5. Not a formal proof verifier."""
from __future__ import annotations
import json
import random
from pathlib import Path
import time
import sympy as s
from rational_hankel import recover, represented_slices


def tensor_vector(vs):
    return s.kronecker_product(*vs)


def design(fs, assignment):
    n, r = fs[0].shape
    eye=s.eye(n)
    cols=[]
    for i,m in enumerate(assignment):
        if m is not None:
            for j in range(n):
                vec=[f[:,i] for f in fs]; vec[m]=eye[:,j]
                cols.append(tensor_vector(vec))
    return s.Matrix.hstack(*cols) if cols else s.zeros(n**3,0)


def chart_jacobian(fs):
    """Fix B_ii,C_ii; fixtures have diagonal entries one in those modes."""
    n,r=fs[0].shape; cols=[]; eye=s.eye(n)
    for m in range(3):
        for i in range(r):
            for j in range(n):
                if m in (1,2) and j==i:
                    continue
                vec=[f[:,i] for f in fs]; vec[m]=eye[:,j]
                cols.append(tensor_vector(vec))
    return s.Matrix.hstack(*cols)


def schedule(r):
    if r==1: return [[0],[1],[2]]
    result=[[0]*r]
    for bit in range((r-1).bit_length()):
        a=[1 if ((i>>bit)&1)==0 else 2 for i in range(r)]
        result.extend([a,[3-m for m in a]])
    return result


def project_complement(d, matrix):
    gram=d.T*d
    if gram.det()==0:
        raise AssertionError('Unexpected singular exact design')
    return matrix-d*gram.inv()*d.T*matrix


def positive_definite_exact(a):
    """Exact symmetric elimination: all Schur pivots must be positive."""
    a=s.Matrix(a)
    if a != a.T: return False
    for k in range(a.rows):
        pivot=a[k,k]
        if not bool(pivot > 0): return False
        for i in range(k+1,a.rows):
            for j in range(i,a.rows):
                value=a[j,i]-a[i,k]*a[j,k]/pivot
                a[j,i]=a[i,j]=value
    return True


def check_common_metric():
    l=s.Matrix([[1,s.Rational(1,50),0],[0,1,s.Rational(1,100)],[s.Rational(1,200),0,1]])
    g=l.T*l
    d=s.Matrix([[1,0],[1,1],[0,2]])
    pg=d*(d.T*g*d).inv()*d.T*g
    dl=l*d; pl=dl*(dl.T*dl).inv()*dl.T
    assert pl*l==l*pg
    assert pg*pg==pg
    assert pg.T*g==g*pg
    return {'kind':'common_metric_conjugacy','exact':True,'ambient_dimension':3}


def check_cycle(r, n, separation, perturbation):
    a=s.Matrix(n,r,lambda i,j: 1 if i==0 else separation*(j+1)**i)
    b=s.eye(n)[:,:r]; c=s.eye(n)[:,:r]
    for i in range(r):
        for j in range(r):
            if i!=j:
                b[i,j]=perturbation*(1 if (i+j)%2 else -1)
                c[i,j]=perturbation*(1 if i<j else -1)
    fs=[a,b,c]; j=chart_jacobian(fs); current=j
    for selection in schedule(r):
        current=project_complement(design(fs,selection), current)
    if perturbation==0:
        assert current==s.zeros(*current.shape)
        return {'kind':'zero_derivative','n':n,'r':r,'separation':str(separation),'exact':True}
    # ||cycle(Jh)||^2 < ||Jh||^2 /64 for every nonzero chart direction.
    certificate=(j.T*j)/64-current.T*current
    assert positive_definite_exact(certificate)
    return {'kind':'strict_one_eighth_derivative_bound','n':n,'r':r,
            'separation':str(separation),'mode_perturbation':str(perturbation),
            'chart_dimension':j.cols,'exact_positive_definite_certificate':True}


def check_nonuniform_design_radius(t):
    co=(1-t*t)/(1+t*t); si=2*t/(1+t*t)
    delta=(si/co)**2
    a=s.Matrix([[1,1,0],[0,delta,1],[0,0,0]])
    root=[a,s.eye(3),s.eye(3)]
    # All root blocks are injective although A itself has rank two.
    for selection in schedule(3):
        d=design(root,selection); assert (d.T*d).det()!=0
    q=s.Matrix([[co,0,-si],[0,1,0],[si,0,co]])
    assert q.T*q==s.eye(3)
    # First-mode least squares has orthonormal pair design.
    updated=a*q.applyfunc(lambda x:x*x)
    assert updated[:,0]==co**2*updated[:,1]
    selection=schedule(3)[1]
    d=design([updated,q,q],selection)
    assert (d.T*d).det()==0
    return {'kind':'shrinking_nonsingular_neighborhood_counterexample',
            'rotation_parameter':str(t),'delta':str(delta),
            'root_designs_full_rank':True,'post_A_mixed_design_singular':True}


def rational_fixture(n,r,kind):
    if kind=='coherent':
        tiny=s.Rational(1,10**6)
        fs=[s.Matrix(n,r,lambda i,j:1 if i==0 else tiny*(j+offset)**i)
            for offset in (1,3,5)]
    elif kind=='unbalanced':
        fs=[s.Matrix(n,r,lambda i,j:(i+offset)**j) for offset in (1,2,3)]
        fs[0]=fs[0]*s.diag(*[s.Integer(10)**(6*j) for j in range(r)])
    elif kind=='two_slices':
        fs=[s.Matrix(n,r,lambda i,j:(i+offset)**j) for offset in (1,2)]
        fs.append(s.Matrix(n,r,lambda i,j:1 if i==0 else (j+1 if i==1 else 0)))
    else:
        fs=[s.Matrix(n,r,lambda i,j:(i+offset)**j) for offset in (1,2,3)]
    return represented_slices(*fs)


def main():
    records=[]; started=time.monotonic()
    records.append(check_common_metric())
    for r,n,sep,p in [
        (2,2,s.Rational(1,100),0),
        (3,3,s.Rational(1,100),0),
        (2,2,s.Rational(1,10**6),s.Rational(1,10000)),
        (2,3,s.Rational(1,10**4),s.Rational(1,10000)),
        (3,3,s.Rational(1,100),s.Rational(1,100000)),
    ]:
        before=time.monotonic(); rec=check_cycle(r,n,sep,p)
        rec['seconds']=time.monotonic()-before; records.append(rec)
        print(rec, flush=True)
    for t in [s.Rational(1,10),s.Rational(1,100),s.Rational(1,1000)]:
        records.append(check_nonuniform_design_radius(t))
    for n,r,kind in [(2,1,'ordinary'),(2,2,'ordinary'),(3,3,'ordinary'),
                     (5,3,'ordinary'),(4,4,'ordinary'),(3,3,'coherent'),
                     (4,3,'unbalanced'),(4,3,'two_slices')]:
        tensor=rational_fixture(n,r,kind)
        for seed in (1,19):
            before=time.monotonic(); result=recover(tensor,r,seed=seed)
            assert result.success, result.reason
            records.append({'kind':'rational_tensor_only_recovery','n':n,'r':r,
                            'family':kind,'seed':seed,'output_width':2*r-1,
                            'exact_reconstruction':True,'grid_size':result.grid_size,
                            'random_entries':result.random_entries,
                            'seconds':time.monotonic()-before})
    out={'scope':'Finite exact rational checks; not independent review or formal verification.',
         'passed_records':len(records),'elapsed_seconds':time.monotonic()-started,'records':records}
    path=Path(__file__).resolve().parents[1]/'results'/'exact_checks.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(out,indent=2)+'\n')
    print('PASS',len(records),'records; saved to',path, flush=True)

if __name__=='__main__': main()
