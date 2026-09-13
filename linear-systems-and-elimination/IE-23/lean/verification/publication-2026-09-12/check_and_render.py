"""Canonical wrapper/catalog checks and repository PDF rendering; no Lean build."""
from pathlib import Path
import hashlib,json,os,subprocess
P=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
W=P.parents[2]
env=os.environ.copy()
env['PANDOC']='/tmp/nla-submission-tools/pandoc-3.11-arm64/bin/pandoc'
env['XELATEX']='/Library/TeX/texbin/xelatex'
commands=[
 ('permanent-ids-origin',['python3','tools/validate_problem_ids.py','--base-ref','origin/main']),
 ('permanent-ids-upstream',['python3','tools/validate_problem_ids.py','--base-ref','5830ed4fb06da0659414a3deb2a40ad327aca052']),
 ('manifest',['/tmp/nla-lean-formalization/venv/bin/python','tools/lean/validate_manifest.py','linear-systems-and-elimination/IE-23/lean']),
 ('format-write',['python3','tools/format_math.py','--write','IE-23']),
 ('catalog',['python3','tools/update_catalog.py','--base-ref','origin/main']),
 ('permanent-id-tests',['python3','-m','unittest','discover','-s','tests','-p','test_problem_ids.py','-v']),
 ('format-check',['python3','tools/format_math.py','--check']),
 ('render',['python3','tools/render_problems.py','IE-23']),
 ('pdfinfo',['pdfinfo','linear-systems-and-elimination/IE-23/problem.pdf']),
 ('pdf-text',['pdftotext','-layout','linear-systems-and-elimination/IE-23/problem.pdf',str(E/'problem.txt')]),
 ('pdf-images',['pdftoppm','-r','115','-png','linear-systems-and-elimination/IE-23/problem.pdf',str(E/'page')])]
checks=[]
for name,cmd in commands:
 r=subprocess.run(cmd,cwd=W,env=env,capture_output=True)
 raw=r.stdout+r.stderr;log=E/(name+'.log');log.write_bytes(raw)
 checks.append({'name':name,'command':cmd,'exit_code':r.returncode,'log':log.name,
  'sha256':hashlib.sha256(raw).hexdigest()})
 (E/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
 print(name,r.returncode,raw.decode()[-1200:],flush=True)
 assert r.returncode==0,log
