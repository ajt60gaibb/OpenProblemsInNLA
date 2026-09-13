"""Preserve the actual IE23 canonical and analytic source bytes before review."""
from pathlib import Path
import datetime,hashlib,json,subprocess
OUT=Path(__file__).resolve().parent
PROJECT=OUT.parent
REPO=PROJECT.parents[2]
BASE='f41f1f9ffa2171550d4bb795862c6170c4f26070'
paths=[
 'linear-systems-and-elimination/IE-23/README.md',
 'linear-systems-and-elimination/IE-23/problem.tex',
 'linear-systems-and-elimination/IE-23/problem.pdf',
 'references/colbrook-recovered-2026-09-11/manuscripts/IE-23.tex',
 'references/colbrook-recovered-2026-09-11/manuscripts/IE-23.pdf',
 'references/colbrook-recovered-2026-09-11/verification/reviews/IE-23-review.md',
 'references/colbrook-recovered-2026-09-11/README.md',
 'docs/lean/REVIEW.md',
]
records=[]
for relative in paths:
    raw=subprocess.check_output(['git','show',BASE+':'+relative],cwd=REPO)
    assert (REPO/relative).read_bytes()==raw,relative
    blob=subprocess.check_output(['git','rev-parse',BASE+':'+relative],cwd=REPO,text=True).strip()
    snapshot=OUT/'source-snapshot'/relative
    snapshot.parent.mkdir(parents=True,exist_ok=True)
    snapshot.write_bytes(raw)
    assert snapshot.read_bytes()==raw
    records.append({'path':relative,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),
                    'git_blob':blob,'snapshot':str(snapshot.relative_to(PROJECT))})
data={'base':BASE,'date_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'canonical_path':paths[0],'original_files':records,'all_original_bytes_unchanged':True,
      'primary_attribution_check':{
        'url':'https://dokmanic.ece.illinois.edu/assets/pdf/DokmanicG17aa.pdf',
        'version':'arXiv:1706.08349v2, 13 July 2017',
        'example':'Example 4.1, equations (51)-(53), printed pp.16-17',
        'target':'Corollary 4.2(3) and Remark 4.1, printed p.18',
        'checked':'Author PDF read through web tool on 12 September 2026; same A and B and distinction between direct and product objectives verified.',
        'not_archived':'The external PDF bytes are not part of this source freeze; all canonical and analytic proof bytes above are.'}}
(OUT/'source-integrity.json').write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps({'status':'PASS','original_sources':len(records),'base':BASE}))
