#!/usr/bin/env python3
"""Reproduce the failed single-coordinate boundary search for (+++-+).
All 23 checker-positive coordinate boundaries of the first upper endpoint
reach det=0 first. This is a finite observation about that endpoint only.
"""
from pathlib import Path
from fractions import Fraction as Q
import json
from minor_tools import coordinate_bounds,all_minors,det
ROOT=Path(__file__).resolve().parent

def main():
    data=json.loads((ROOT/'mixed_parity_example.json').read_text())
    B=[[Q(v) for v in r] for r in data['A_plus']];e=data['signature']
    fixed={tuple(x) for x in data['fixed_entries_0based']};records=[]
    for i in range(5):
        for j in range(5):
            if (i,j) in fixed:continue
            lo,hi,_,_=coordinate_bounds(B,e,i,j)
            shift=hi if (i+j)%2==0 else lo
            assert shift is not None
            C=[r[:] for r in B];C[i][j]+=shift
            zeros=[len(I) for I,J,v in all_minors(C) if not v]
            assert zeros==[5] and det(C)==0
            records.append({'entry':[i,j],'shift':str(shift),'zero_orders':zeros})
    assert len(records)==23
    (ROOT/'both_boundary_search_attempts.json').write_text(json.dumps(records,indent=2)+'\n')
    print('23 exact coordinate-boundary attempts reproduced: only determinant becomes zero.')
if __name__=='__main__':main()
