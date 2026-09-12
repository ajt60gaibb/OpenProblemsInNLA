#!/usr/bin/env python3
"""Independent exact minor audit and graph/SCC regression checks.
Leibniz determinants here do NOT use minor_tools.det or its elimination code.
"""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import json,random
from graph_criterion import fixed_graph_certificate
from scc_reduction import scc_certificate,scaled_endpoint
ROOT=Path(__file__).resolve().parent

def leibniz(A):
    n=len(A);ans=Q(0)
    for p in permutations(range(n)):
        inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        term=Q((-1)**inv)
        for i,j in enumerate(p):term*=A[i][j]
        ans+=term
    return ans

def run():
    data=json.loads((ROOT/'mixed_parity_example.json').read_text())
    A=[[Q(v) for v in r] for r in data['A_minus']]
    B=[[Q(v) for v in r] for r in data['A_plus']]
    e=data['signature'];count=0
    for name,M in [('A_minus',A),('A_plus',B)]:
        saved=json.loads((ROOT/(name+'_all_minors.json')).read_text())
        assert len(saved)==251
        for item in saved:
            I,J=item['rows_0based'],item['cols_0based']
            d=leibniz([[M[i][j] for j in J] for i in I])
            assert d==Q(item['determinant'])
            assert e[len(I)-1]*d==Q(item['signed_determinant'])>=0
            count+=1
    extra=json.loads((ROOT/'both_boundary_example.json').read_text())
    for name,key in [('A_both_boundary','A_minus'),('B_both_boundary','A_plus')]:
        M=[[Q(v) for v in r] for r in extra[key]]
        saved=json.loads((ROOT/(name+'_all_minors.json')).read_text())
        assert len(saved)==251
        for item in saved:
            I,J=item['rows_0based'],item['cols_0based']
            dd=leibniz([[M[i][j] for j in J] for i in I])
            assert dd==Q(item['determinant'])
            assert extra['signature'][len(I)-1]*dd==Q(item['signed_determinant'])>=0
            count+=1
    cyclic=json.loads((ROOT/'cyclic_graph_dimension_five_example.json').read_text())
    CM=[[Q(v) for v in r] for r in cyclic['A_plus']]
    saved=json.loads((ROOT/'B_cyclic_graph_all_minors.json').read_text())
    assert len(saved)==251
    for item in saved:
        I,J=item['rows_0based'],item['cols_0based']
        dd=leibniz([[CM[i][j] for j in J] for i in I])
        assert dd==Q(item['determinant'])
        assert cyclic['signature'][len(I)-1]*dd==Q(item['signed_determinant'])>=0
        count+=1
    cert=fixed_graph_certificate(A,B,1);assert cert['criterion_applies']
    # Negation reverses checker ordering and changes epsilon_1.
    An=[[-v for v in r] for r in B];Bn=[[-v for v in r] for r in A]
    neg=fixed_graph_certificate(An,Bn,-1);assert neg['criterion_applies']
    graphchecks=2
    # A positive singleton has cycles but is not a counterexample.
    cyc=fixed_graph_certificate(B,B,1);assert not cyc['acyclic'];graphchecks+=1
    sc=scc_certificate(B,B,1);assert not sc['opened_edges'];assert sc['cycle_edges'];graphchecks+=1
    # A four-cycle plus a tail: only the tail is opened by the SCC reduction.
    n=5;fixed={(0,0),(0,1),(1,0),(1,1),(1,2)}
    X=[[Q(10) for _ in range(n)] for _ in range(n)]
    Y=[[X[i][j]+(0 if (i,j) in fixed else Q((-1)**(i+j),100)) for j in range(n)] for i in range(n)]
    # X,Y are graph test data, NOT asserted to be nonsingular SR.
    sc=scc_certificate(X,Y,1)
    assert len(sc['cycle_edges'])==4 and len(sc['opened_edges'])==1
    Z=scaled_endpoint(Y,sc,Q(1,10**8))
    rem={(i,j) for i in range(n) for j in range(n) if Z[i][j]==X[i][j]}
    assert rem=={(0,0),(0,1),(1,0),(1,1)}
    assert all((-1)**(i+j)*(Z[i][j]-X[i][j])>=0 for i in range(n) for j in range(n));graphchecks+=1
    # Fixed zero entries of opposite parities are not certified.
    X=[[Q(1) for _ in range(n)] for _ in range(n)];X[0][0]=0;X[0][1]=0
    Y=[[X[i][j]+(0 if (i,j) in {(0,0),(0,1)} else Q((-1)**(i+j),10)) for j in range(n)] for i in range(n)]
    cert=fixed_graph_certificate(X,Y,1)
    assert cert['acyclic'] and not cert['zero_fixed_one_parity'] and not cert['criterion_applies'];graphchecks+=1
    out={'independent_Leibniz_minor_checks':count,'graph_edge_case_checks':graphchecks,
         'all_passed':True,'graph_only_test_data_not_claimed_SR':True}
    (ROOT/'independent_audit_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':run()
