#!/usr/bin/env python3
"""Fresh independent replay of retained full-Target Linux artifacts and originals.

Reads the integration candidate, unchanged strict checkers, archives and logs.
Writes only to this review's output directory; does not rerun Linux Comparator.
"""
from __future__ import annotations
import argparse
import concurrent.futures
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE=Path(__file__).resolve().parent
BASE='36767fa430309f13d04dc6ebe080d470f5c2444a'
EXPECTED='42d1665800d0185581149ef494e03055b533d636'
CASES=[
 {'label':'PF05','id':'PF-05','project':'nonnegative-and-positive-factorizations/PF-05/lean',
  'source':'c4c7be592c51c8ba81d1579082813310a22b356d','bundle':'promotion-linux-ci/c4c7be59',
  'metadata':'run-39176870923-view.json','job':'job-117821318204.log.gz','archive':'original-artifact.zip','artifact_metadata':'artifact-metadata.json'},
 {'label':'SP12','id':'SP-12','project':'eigenvalues-and-inverse-problems/SP-12/lean',
  'source':'a7adfc8e30ad284f42ec2ea0221a990ee9804031','bundle':'refreshed-linux-ci',
  'metadata':'run-metadata.json','job':'job.log.gz','archive':'lean-SP-12.zip','artifact_metadata':'artifact-metadata.json'},
 {'label':'TR14','id':'TR-14','project':'tensor-computations/TR-14/lean',
  'source':'16a1150d81f606ed6a8333be8c04730e0a477525','bundle':'promotion-linux-ci/16a1150d',
  'metadata':'run.json','job':'job.log.gz','archive':'artifact.zip','artifact_metadata':'artifact.json'},
]
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--repo',type=Path,required=True)
 ap.add_argument('--ref',default=EXPECTED)
 ap.add_argument('--output',type=Path,default=HERE)
 args=ap.parse_args();repo=args.repo.resolve();out=args.output.resolve();out.mkdir(exist_ok=True,parents=True)
 def git(*argv):return subprocess.check_output(['git',*argv],cwd=repo)
 def source(path,ref=None):return git('show',(ref or args.ref)+':'+path)
 head=git('rev-parse','HEAD').decode().strip()
 if head!=args.ref:raise RuntimeError('integration candidate HEAD differs from selected ref')
 report={'reviewer':'OpenAI Codex AI agent /root/verification','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'integration_commit':head,'original_base':BASE,'script_sha256':sha(Path(__file__).read_bytes()),
         'scope':__doc__,'cases':{},'checks':[],'passed':False,'linux_rerun_performed':False}
 def check(name,passed,**evidence):report['checks'].append({'name':name,'passed':bool(passed),**evidence})
 base_registry=source('problem_ids.json',BASE);registry=json.loads(base_registry)
 check('permanent-registry-byte-and-map-identity',source('problem_ids.json')==base_registry,registered_ids=len(registry),sha256=sha(base_registry))
 check('all-registered-canonical-paths-retained',all((repo/p).is_file() for p in registry.values()))
 def replay(case):
  proof=repo/'docs/lean/proofs'/case['id'];verify=proof/'verification';bundle=verify/case['bundle'];script=verify/'check-linux-artifact.py'
  output=out/(case['label']+'-strict-replay.json')
  argv=['python3',str(script),'--ref',case['source'],'--artifact',str(bundle/'artifact'),'--metadata',str(bundle/case['metadata']),
        '--job-log-gz',str(bundle/case['job']),'--archive',str(bundle/case['archive']),'--artifact-metadata',str(bundle/case['artifact_metadata']),
        '--output',str(output)]
  if case['id']!='SP-12':argv+=['--reviewer','/root/verification (independent Codex AI agent, fresh retained artifact replay)']
  cp=subprocess.run(argv,cwd=repo,text=True,capture_output=True,timeout=180)
  record={'argv':argv,'exit_code':cp.returncode,'stdout':cp.stdout,'stderr':cp.stderr,'checker_sha256':sha(script.read_bytes()),
          'output':output.name,'output_sha256':sha(output.read_bytes()) if output.exists() else None}
  (out/(case['label']+'-execution.json')).write_text(json.dumps(record,indent=2)+'\n')
  if cp.returncode:raise RuntimeError('strict retained checker rejected '+case['id'])
  return record
 with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
  replays=list(pool.map(replay,CASES))
 for case,execution in zip(CASES,replays):
  ident=case['id'];label=case['label'];project=case['project'];proof=repo/'docs/lean/proofs'/ident
  strict=json.loads((out/(label+'-strict-replay.json')).read_text())
  data={'execution':execution,'checked_commit':case['source'],'strict_checks':len(strict['checks']),
        'package_inputs':len(strict['inputs']),'lean_inputs':sum(i['path'].endswith('.lean') for i in strict['inputs']),
        'originals':[],'proof_copies':[],'package_exports':[],'integration_inputs':[]}
  report['cases'][ident]=data
  check(ident+':unchanged-strict-artifact-audit',strict['passed'] and all(c['passed'] for c in strict['checks']))
  tree=git('ls-tree','-r','--name-only','-z',args.ref,'--',project).decode().split('\0')
  names={p[len(project)+1:] for p in tree if p};expected={i['path'] for i in strict['inputs']}
  check(ident+':exact-integration-project-file-set',names==expected,files=len(names))
  for item in strict['inputs']:
   observed=sha(source(project+'/'+item['path']))
   data['integration_inputs'].append({'path':item['path'],'expected':item['expected_sha256'],'actual':observed,'passed':observed==item['expected_sha256']})
  check(ident+':every-CI-input-matches-selected-integration-commit',all(i['passed'] for i in data['integration_inputs']),count=len(data['integration_inputs']))
  lock=json.loads(source(project+'/proof-source-lock.json'))
  for item in lock['copies']:
   origin=sha(source(item['source']));dest=sha(source(item['destination']))
   data['proof_copies'].append({'module':item['module'],'source':item['source'],'destination':item['destination'],
      'source_sha256':origin,'destination_sha256':dest,'passed':origin==dest==item['source_sha256']==item['destination_sha256']})
  check(ident+':all-reviewed-shared-proof-copies-exact',all(i['passed'] for i in data['proof_copies']),count=len(data['proof_copies']))
  for rel,expected_hash in lock['package_exports'].items():
   observed=sha(source(project+'/'+rel));data['package_exports'].append({'path':rel,'expected':expected_hash,'actual':observed,'passed':observed==expected_hash})
  check(ident+':all-locked-package-exports-exact',all(i['passed'] for i in data['package_exports']))
  archive=proof/'originals-main-36767';manifest=json.loads((archive/'manifest.json').read_text())
  records=manifest.get('records') or [{'source':i['original_path'],'archive':str((archive/i['archive_file']).relative_to(repo)),'sha256':i['sha256']} for i in manifest['files']]
  for item in records:
   old=source(item['source'],BASE);saved=(repo/item['archive']).read_bytes()
   keep_source=item['source'].split('/')[-1] not in ['README.md','problem.tex','problem.pdf']
   data['originals'].append({'source':item['source'],'archive':item['archive'],'sha256':sha(saved),
      'passed':saved==old and sha(saved)==item['sha256'] and (not keep_source or source(item['source'])==old),
      'original_source_still_in_place_required':keep_source})
  check(ident+':all-retained-originals-byte-identical',all(i['passed'] for i in data['originals']),count=len(data['originals']))
  canonical=registry[ident];old=source(canonical,BASE).decode();new=source(canonical).decode()
  stripped,count=re.subn(r'<!-- formal-lean-proof:start -->.*?<!-- formal-lean-proof:end -->\n\n','',new,flags=re.S)
  # Replace values only; the current line retains its original Markdown
  # trailing-space line break, so do not append that spacing a second time.
  original_status=re.search(r'^\*\*Status:\*\* (.*)$',old,re.M).group(1).rstrip()
  original_date=re.search(r'^\*\*Last checked:\*\* (.*)$',old,re.M).group(1).rstrip()
  stripped=stripped.replace('**Status:** Lean verified','**Status:** '+original_status,1)
  stripped=stripped.replace('**Last checked:** 2026-10-18','**Last checked:** '+original_date,1)
  check(ident+':all-original-canonical-mathematics-credits-history-retained',count==1 and stripped==old,canonical_path=canonical)
  check(ident+':statement-original-snapshot-preserved',source('docs/lean/statements/'+ident+'/ORIGINAL.md')==old.encode())
  statement=source(project+'/NLA/Statements/'+label+'.lean');shared=source('lean-statements/NLA/Statements/'+label+'.lean')
  check(ident+':full-original-Target-definition-unchanged',statement==shared==source('lean-statements/NLA/Statements/'+label+'.lean',BASE),sha256=sha(statement))
  solution=source(project+'/Solution.lean').decode();final=source(project+'/NLA/Proofs/'+label+'/Final.lean').decode()
  check(ident+':actual-unconditional-full-Target-exports',f'theorem target : NLA.Statements.{label}.Target' in solution and f'theorem target : NLA.Statements.{label}.Target' in final and 'import Challenge' not in solution)
  data.update(solution_sha256=sha(solution.encode()),final_sha256=sha(final.encode()),full_target_statement_sha256=sha(statement),
              archive_sha256=strict['archive_sha256'],run=strict['run'],job=strict['job'],artifact_id=strict['artifact_id'])
 check('selected-integration-HEAD-remained-unchanged',git('rev-parse','HEAD').decode().strip()==args.ref)
 report['passed']=all(c['passed'] for c in report['checks'])
 (out/'integration-and-preservation.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'passed':report['passed'],'checks':len(report['checks']),'failed':[c['name'] for c in report['checks'] if not c['passed']],
                   'cases':{k:{x:v[x] for x in ['strict_checks','package_inputs','lean_inputs']} for k,v in report['cases'].items()}},indent=2))
 return 0 if report['passed'] else 1
if __name__=='__main__':raise SystemExit(main())
