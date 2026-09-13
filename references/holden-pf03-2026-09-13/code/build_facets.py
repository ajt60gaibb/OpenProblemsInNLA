"""Construct the complete facet matrix by exhaustive exact enumeration."""
from pathlib import Path
from itertools import combinations
import json,time
from exact_facets import null_normal,integer_columns

HERE=Path(__file__).resolve().parent.parent/'data'

def build_facets():
    start=time.monotonic()
    cone=json.loads((HERE/'rational_cone_certificate.json').read_text())
    rays=integer_columns(cone);normals={}
    count=0
    for subset in combinations(range(21),6):
        count+=1
        row=null_normal([rays[i] for i in subset])
        if row is None:
            continue
        values=[];pos=neg=False
        for ray in rays:
            value=sum(x*y for x,y in zip(row,ray));values.append(value)
            pos|=value>0;neg|=value<0
            if pos and neg:break
        if pos and neg:continue
        assert pos or neg
        if neg:row=tuple(-x for x in row);values=[-x for x in values]
        face=tuple(i for i,v in enumerate(values) if v==0)
        normals[row]=face
    assert count==54264 and len(normals)==444
    ordered=sorted(normals.items(),key=lambda item:(item[1],item[0]))
    result={'rank':7,'generator_count':21,'order':len(ordered),
            'integer_generators':rays,
            'facet_normals':[list(row) for row,face in ordered],
            'facets':[list(face) for row,face in ordered],
            'description':'All exact supporting primitive facet normals. The complete list is independently checked by enumerating all 54264 six-generator subsets.'}
    (HERE/'facets.json').write_text(json.dumps(result,indent=2))
    print('Rebuilt 444 facets from all 54264 subsets in',round(time.monotonic()-start,3),'seconds.')
    return result

if __name__=='__main__':
    build_facets()
