#!/usr/bin/env python3
"""Exact cyclic-graph example and checks for dimension_five_theorem.md.
Theorem V concerns the real continuum; finite tests are not its proof.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,random
from minor_tools import det,check_sr,all_minors
from graph_criterion import fixed_graph_certificate
ROOT=Path(__file__).resolve().parent

def condition(A,B):
    n=len(A)
    zeros=[(i,j) for i in range(n) for j in range(n) if A[i][j]==B[i][j]==0]
    fixed_blocks=[];bad=[]
    for i in range(n-1):
        for j in range(n-1):
            if all(A[r][c]==B[r][c] for r in (i,i+1) for c in (j,j+1)):
                d=A[i][j]*A[i+1][j+1]-A[i][j+1]*A[i+1][j]
                fixed_blocks.append({'top_left_0based':[i,j],'determinant':str(d)})
                if not d:bad.append([i,j])
    return {'no_fixed_zeros':not zeros,'fixed_zero_positions':zeros,
            'fixed_adjacent_blocks':fixed_blocks,'singular_fixed_blocks':bad,
            'criterion_applies':not zeros and not bad}

def main():
    data=json.loads((ROOT/'both_boundary_example.json').read_text());e=data['signature']
    A=[[Q(v) for v in r] for r in data['A_minus']];B=[[Q(v) for v in r] for r in data['A_plus']]
    # Add a directed fixed rectangle away from both vanishing middle minors.
    for i in (3,4):
        for j in (0,1):B[i][j]=A[i][j]
    ac,bc=check_sr(A,e),check_sr(B,e)
    assert ac['valid'] and bc['valid']
    assert any(v['zero'] for v in ac['minor_counts'].values())
    assert any(v['zero'] for v in bc['minor_counts'].values())
    graph=fixed_graph_certificate(A,B,e[0]);assert not graph['acyclic']
    cert=condition(A,B);assert cert['criterion_applies']
    rng=random.Random(99512);samples=0
    for _ in range(64):
        M=[[A[i][j]+Q(rng.randrange(9),8)*(B[i][j]-A[i][j]) for j in range(5)] for i in range(5)]
        assert check_sr(M,e)['valid'];samples+=1
    # The rejected degenerate conditions are only failures of sufficiency.
    I=[[Q(i==j) for j in range(5)] for i in range(5)]
    assert not condition(I,I)['criterion_applies']
    one=[[Q(1) for j in range(5)] for i in range(5)]
    assert condition(one,one)['singular_fixed_blocks']
    out={'signature':e,'A_minus':[[str(v) for v in r] for r in A],
         'A_plus':[[str(v) for v in r] for r in B],'A_check':ac,'B_check':bc,
         'graph_certificate':graph,'dimension_five_certificate':cert,'exact_sample_checks':samples,
         'note':'Both endpoints non-strict; graph theorem does not apply, Theorem V does. Samples are not proof.'}
    (ROOT/'cyclic_graph_dimension_five_example.json').write_text(json.dumps(out,indent=2)+'\n')
    vals=[{'rows_0based':I,'cols_0based':J,'determinant':str(v),
           'signed_determinant':str(e[len(I)-1]*v)} for I,J,v in all_minors(B)]
    (ROOT/'B_cyclic_graph_all_minors.json').write_text(json.dumps(vals,indent=2)+'\n')
    print(json.dumps({'A_valid':ac['valid'],'B_valid':bc['valid'],
          'graph_acyclic':graph['acyclic'],'Theorem_V_condition':cert,
          'sample_checks':samples},indent=2))
if __name__=='__main__':main()
