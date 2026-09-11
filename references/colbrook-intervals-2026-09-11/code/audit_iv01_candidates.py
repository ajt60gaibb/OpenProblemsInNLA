"""Independently recheck any exploratory IV-01 candidates using SymPy.
This audit does not automatically add an entry to the claimed-resolution set.
"""
from pathlib import Path
from itertools import combinations
import json, hashlib, datetime
import sympy as sp

root=Path(__file__).resolve().parents[1]
result={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'arithmetic':'exact SymPy integer determinants',
        'additional_resolution_automatically_claimed':False,'candidates':[]}
seen=set()
for path in sorted((root/'verification').glob('IV-01*.json')):
    try:data=json.loads(path.read_text())
    except Exception:continue
    cert=data.get('certificate')
    if not isinstance(cert,dict):continue
    digest=hashlib.sha256(json.dumps(cert,sort_keys=True).encode()).hexdigest()
    if digest in seen:continue
    seen.add(digest)
    entry={'source':path.name,'certificate_sha256':digest}
    try:
        lo=sp.Matrix(cert['checkerboard_corner_minus'])
        hi=sp.Matrix(cert['checkerboard_corner_plus'])
        member=sp.Matrix(cert['violating_member'])
        sig=tuple(cert['signature']);n=lo.rows
        assert lo.shape==hi.shape==member.shape==(n,n) and len(sig)==n
        assert all((-1)**(i+j)*(hi[i,j]-lo[i,j])>=0 for i in range(n) for j in range(n))
        assert all(min(lo[i,j],hi[i,j])<=member[i,j]<=max(lo[i,j],hi[i,j])
                   for i in range(n) for j in range(n))
        counts=[];bad=[]
        for k in range(1,n+1):
            rows=list(combinations(range(n),k));count=0
            for I in rows:
                for J in rows:
                    for A in (lo,hi):assert sig[k-1]*A[list(I),list(J)].det()>=0
                    value=member[list(I),list(J)].det()
                    if sig[k-1]*value<0:bad.append({'rows':I,'columns':J,'determinant':str(value)})
                    count+=1
            counts.append(count)
        assert lo.det()!=0 and hi.det()!=0 and bad
        entry.update(status='exact_certificate_passed',corner_minors_per_matrix=sum(counts),
                     dimension=n,signature=sig,bad_minors=bad)
    except Exception as exc:entry.update(status='audit_failed',error=repr(exc))
    result['candidates'].append(entry)
result['status']='no_candidate_present' if not result['candidates'] else 'candidate_audits_recorded'
result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(root/'verification'/'IV-01_independent_code_audit.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
