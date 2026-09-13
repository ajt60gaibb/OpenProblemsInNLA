from pathlib import Path
import hashlib,json,datetime
E=Path(__file__).resolve().parent;P=E.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
f=json.loads((P/'verification/proof-freeze.json').read_text())
for n,h in f['files'].items(): assert sha(P/n)==h,n
assert sha(P/'reviews/proof-completion.md')=='ad86420d1e3640da6c2edacfc4160a259a766a59764f1f764ca4caa7e1082f78'
assert json.loads((E/'fresh-result.json').read_text())['verdict']=='PASS'
assert json.loads((E/'final-audit.json').read_text())['verdict'].startswith('PASS')
outer=E/'EVIDENCE-MANIFEST.json'
files={str(p.relative_to(E)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(E.rglob('*')) if p.is_file() and p!=outer}
report=P/'reviews/proof-referee-2.md'
files['../proof-referee-2.md']={'sha256':sha(report),'bytes':report.stat().st_size}
outer.write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reviewer':'/root/formal_review_standards','verdict':'APPROVE exact final MF16 mathematical implementation',
 'reviewed_freeze_sha256':sha(P/'verification/proof-freeze.json'),'file_count':len(files),'files':files,
 'self_exclusion':'Only this exact outer EVIDENCE-MANIFEST.json; nested manifests retained.',
 'Linux_Comparator':'pending; this is independent local macOS review'},indent=2)+'\n')
for n,i in files.items(): assert sha(E/n)==i['sha256'],n
print('APPROVE',sha(report),'manifest',sha(outer),'bound',len(files))
