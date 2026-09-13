"""Exhaustive exact facet verification over all C(21,6) generator subsets.

This uses integer/rational algebra only.  Every possible facet of a full-
dimensional pointed seven-dimensional cone contains six linearly independent
extreme-ray generators.  Enumeration is therefore a completeness proof.
The standard-library implementation uses fraction-free integer nullspaces.
"""
from pathlib import Path
from itertools import combinations
from math import comb
import json,time
from exact_facets import null_normal,integer_columns
from field3 import rational_rank
from fractions import Fraction as F

HERE=Path(__file__).resolve().parent.parent/'data'

def verify_facets(verbose=True):
    start=time.monotonic()
    d=json.loads((HERE/'facets.json').read_text())
    cone=json.loads((HERE/'rational_cone_certificate.json').read_text())
    rays=integer_columns(cone)
    assert rays==[tuple(row) for row in d['integer_generators']]
    h=[F(x) for x in cone['positive_slice_functional']]
    assert all(sum(x*y for x,y in zip(h,ray))>0 for ray in rays)
    assert rational_rank([[F(ray[i]) for ray in rays] for i in range(7)])==7
    expected={tuple(row):tuple(face) for row,face in zip(d['facet_normals'],d['facets'])}
    assert len(expected)==len(d['facet_normals'])
    found={}
    count=0;deficient=0;non_supporting=0
    for subset in combinations(range(21),6):
        count+=1
        normal=null_normal([rays[i] for i in subset])
        if normal is None:
            deficient+=1
            continue
        vals=[];pos=neg=False
        for ray in rays:
            val=sum(x*y for x,y in zip(normal,ray))
            vals.append(val)
            if val>0:pos=True
            elif val<0:neg=True
            if pos and neg:
                break
        if pos and neg:
            non_supporting+=1
            continue
        assert pos or neg
        if neg:
            normal=tuple(-x for x in normal);vals=[-x for x in vals]
        face=tuple(i for i,v in enumerate(vals) if v==0)
        assert min(vals)==0 and max(vals)>0
        found[normal]=face
    assert count==comb(21,6)
    assert found==expected,('Facet list mismatch',len(found),len(expected))
    R=[[F(x) for x in row] for row in d['facet_normals']]
    assert rational_rank(R)==7
    elapsed=time.monotonic()-start
    result={
      'status':'PASS', 'method':'exhaustive exact integer nullspace enumeration',
      'subsets_checked':count,'rank_deficient_subsets':deficient,
      'non_supporting_subsets':non_supporting,'distinct_facets':len(found),
      'facet_sizes':sorted({len(face) for face in found.values()}),
      'facet_matrix_rank':7,'seconds':round(elapsed,3),
    }
    if verbose:
        print(json.dumps(result,indent=2))
    return result

if __name__=='__main__':
    verify_facets()
