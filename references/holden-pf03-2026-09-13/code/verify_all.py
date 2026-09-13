"""Verify every finite certificate used in the PF-03 counterexample proof.

Run: python code/verify_all.py
Only the Python standard library is needed. No certificate check uses
floating-point arithmetic, an optimization oracle, randomization, or a tolerance.

The manuscript proves the universally quantified obstruction from the finite
hypotheses checked here. This script is not a formal theorem-prover proof.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,csv,gzip,json,sys,time
from field3 import *
from exact_facets import integer_columns
from build_seed import build_seed
from verify_seed import verify_seed
from verify_facets import verify_facets

HERE=Path(__file__).resolve().parent.parent
DATA=HERE/'data'

def coarse_lower(x:F, denominator:int=10**6)->F:
    return F(x.numerator*denominator//x.denominator,denominator)

def verify_cone(O,Q,Cs,iso):
    d=json.loads((DATA/'rational_cone_certificate.json').read_text())
    W=[[E(F(x)) for x in row] for row in d['coefficient_triangle']]
    ac,bc=map(F,d['center']);delta=F(d['delta'])
    assert ac==F(125992104989487316477,10**20)
    assert bc==F(158740105196819947475,10**20)
    assert delta==F(1,10000)
    assert W==[[ONE,ONE,ONE],[E(ac+delta),E(ac),E(ac-delta)],[E(bc),E(bc+delta),E(bc-delta)]]
    assert rational_rank([[x.rational() for x in row] for row in W])==3
    lam=[E.decode(x) for x in d['barycentric_coefficients']]
    assert sum(lam,ZERO)==ONE
    assert multiply(W,[[x] for x in lam])==[[ONE],[ALPHA],[ALPHA**2]]
    assert all(positive(x-F(33,100),iso) for x in lam)
    blocks=[multiply(U,W) for U in Cs]
    V=[[blocks[j][i][k] for j in range(7) for k in range(3)] for i in range(7)]
    assert [[str(x.rational()) for x in row] for row in V]==d['generators']
    for j,block in enumerate(blocks):
        assert multiply(block,[[x] for x in lam])==[[O[i][j]] for i in range(7)]
    assert rational_rank([[x.rational() for x in row] for row in V])==7
    cross=multiply(multiply(transpose(V),Q),V)
    cross_lows=[]
    for i in range(21):
        for j in range(i+1,21):
            if i//3 != j//3:
                lower=cross[i][j].interval(iso)[0]
                assert lower>F(17,1000)
                cross_lows.append(lower)
    assert len(cross_lows)==189
    assert min(cross_lows)>F(17344,10**6)
    h=[F(x) for x in d['positive_slice_functional']]
    hv=[sum(h[i]*V[i][j].rational() for i in range(7)) for j in range(21)]
    assert min(hv)>F(999,1000)
    print('PASS: all seven algebraic rays lie strictly inside their rational three-ray cones.')
    print('PASS: all 189 cross-block generator pairings exceed 17/1000 (exact).')
    print('PASS: a common rational functional is positive on all 21 generators.')
    return d,V,lam,{'cross_generator_bound':str(coarse_lower(min(cross_lows))),
                   'slice_functional_bound':str(coarse_lower(min(hv))),
                   'barycentric_bound':'33/100'}

def verify_matrix(O,cone,iso,expanded=True):
    data=json.loads((DATA/'facets.json').read_text())
    R=data['facet_normals'];n=len(R)
    assert n==444 and len(R[0])==7
    with (DATA/'R_integer.csv').open(newline='') as f:
        assert [[int(x) for x in row] for row in csv.reader(f)]==R
    assert list(zip(data['facet_normals'],data['facets']))==sorted(zip(data['facet_normals'],data['facets']),key=lambda item:(item[1],item[0]))
    rays=integer_columns(cone)
    for row,face in zip(R,data['facets']):
        values=[sum(x*y for x,y in zip(row,ray)) for ray in rays]
        assert min(values)>=0
        assert [i for i,x in enumerate(values) if x==0]==face
        assert len(face)==6
    assert rational_rank([[F(x) for x in row] for row in R])==7
    B=multiply([[E(x) for x in row] for row in R],O)
    zeros=positive_entries=0
    for row,face in zip(B,data['facets']):
        zero_groups=0
        for j,value in enumerate(row):
            predicted_zero=set(range(3*j,3*j+3)).issubset(face)
            if predicted_zero:
                assert value==ZERO
                zeros+=1;zero_groups+=1
            else:
                assert positive(value,iso)
                positive_entries+=1
        assert zero_groups<=2
    assert (positive_entries,zeros)==(2966,142)
    count=0;max_digits=0
    for i,row in enumerate(R):
        for j in range(i+1):
            value=sum(x*y for x,y in zip(row,R[j]))
            assert value>0
            count+=1;max_digits=max(max_digits,len(str(value)))
    assert count==98790 and max_digits==270
    if expanded:
        with gzip.open(DATA/'A_integer.mtx.gz','rt',encoding='ascii') as f:
            assert f.readline().strip()=='%%MatrixMarket matrix coordinate integer symmetric'
            line=f.readline()
            while line.startswith('%'):
                line=f.readline()
            assert tuple(map(int,line.split()))==(n,n,n*(n+1)//2)
            for i,row in enumerate(R):
                for j in range(i+1):
                    ii,jj,value=map(int,f.readline().split())
                    assert (ii,jj)==(i+1,j+1)
                    assert value==sum(x*y for x,y in zip(row,R[j]))
            assert not f.read().strip()
    print('PASS: the integer facet matrix R has shape 444 by 7 and rank seven.')
    print('PASS: B=R O is nonnegative: 2966 strictly positive entries and 142 exact zeros.')
    print('PASS: all 98790 stored lower-triangular entries of A=R R^T are positive integers.')
    if expanded:
        print('PASS: every expanded matrix entry matches R R^T exactly.')
    return {'order':n,'rank':7,'real_cp_rank':7,'positive_factor_entries':positive_entries,
            'zero_factor_entries':zeros,'expanded_entries_checked':count if expanded else 0,
            'max_matrix_integer_digits':max_digits}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-expanded',action='store_true',help='Skip only the redundant expanded A file check.')
    parser.add_argument('--summary',type=Path,help='Optional path for a JSON verification summary.')
    args=parser.parse_args()
    start=time.monotonic()
    print('PF-03 exact counterexample verification')
    build_seed(check_existing=True)
    d,O,Qp,Q,Bs,Cs,Hs,iso=verify_seed(DATA/'exact_algebraic_certificate.json')
    cone,V,lam,bounds=verify_cone(O,Q,Cs,iso)
    facet_info=verify_facets(verbose=True)
    matrix_info=verify_matrix(O,cone,iso,expanded=not args.skip_expanded)
    local=[]
    for H in Hs:
        local.append({'H00_lower':str(coarse_lower(H[0][0].interval(iso)[0])),
                      'leading_2x2_determinant_lower':str(coarse_lower((H[0][0]*H[1][1]-H[0][1]**2).interval(iso)[0]))})
    qp_lower=min(Qp[i][j].interval(iso)[0] for i in range(7) for j in range(i+1,7))
    summary={'status':'PASS: all finite hypotheses and all supplied matrix entries verified',
             'arithmetic':'arbitrary precision integers and fractions; cubic field t^3-2; rational isolating interval',
             'isolation_interval':[str(x) for x in iso],
             'Qprime_offdiagonal_lower':str(coarse_lower(qp_lower)),
             'local_form_bounds':local,'cone_bounds':bounds,
             'facets':facet_info,'matrix':matrix_info,
             'python':sys.version.split()[0],
             'elapsed_seconds':round(time.monotonic()-start,3),
             'scope':'The manuscript proves the quantified conclusion from these finite checks; this is not a formal proof assistant.'}
    if args.summary:
        args.summary.parent.mkdir(parents=True,exist_ok=True)
        args.summary.write_text(json.dumps(summary,indent=2))
    print('ALL FINITE CERTIFICATE CHECKS PASSED.')
    print('Elapsed seconds:',summary['elapsed_seconds'])
    print('See the manuscript for the unrestricted-width nonexistence proof.')

if __name__=='__main__':
    main()
