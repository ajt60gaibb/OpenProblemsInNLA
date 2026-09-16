from pathlib import Path
import hashlib,json,subprocess,re
repo=Path('/private/tmp/nla-formalization-ie14-20260915'); project=repo/'linear-systems-and-elimination/IE-14/lean'; out=Path('/private/tmp/nla-campaign-existing-review/IE14-final-source')
sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *a:subprocess.check_output(['git','-C',str(repo),*a])
candidate='c04371f6005220866f4f069809002d319554e039'; freeze='58b516b6dbb7fa4e885b679d261bf779c263aad4'; base='d8c38a795876b132c90df8d1be8682d3dcde394c'
check={}
for tag,fn,rev in [('candidate','reviews/final-source-inputs.json',candidate),('freeze','reviews/statement-freeze.json',freeze)]:
 data=json.loads((project/fn).read_text()); check[tag]={}
 for rel,h in data['input_sha256'].items():
  f=project/rel; got=sha(f.read_bytes()); blob=sha(git('show',rev+':'+str(f.relative_to(repo))))
  assert h==got==blob,(tag,rel,h,got,blob)
  check[tag][rel]=h
source=json.loads((project/'reviews/initial/source-hashes.json').read_text());check['original_sources']={}
for rel,meta in source['files'].items():
 b=(repo/rel).read_bytes(); assert sha(b)==meta['sha256'] and len(b)==meta['bytes']
 assert sha(git('show',base+':'+rel))==meta['sha256']
 assert sha(git('show',candidate+':'+rel))==meta['sha256']
 check['original_sources'][rel]=meta
check['preproof_reports']={}
for rel,h in json.loads((project/'reviews/statement-freeze.json').read_text())['independent_statement_reports'].items():
 assert sha((project/rel).read_bytes())==h
 check['preproof_reports'][rel]=h
check['registry']={}
for rev in [base,freeze,candidate]:
 check['registry'][rev]=json.loads(git('show',rev+':problem_ids.json'))['IE-14']
assert len(set(check['registry'].values()))==1
check['candidate_commit']=candidate; check['statement_commit']=freeze; check['published_base']=base
check['seal_sha256']=sha((project/'reviews/final-source-inputs.json').read_bytes())
check['imports']={str(f.relative_to(project)):re.findall(r'^import (.+)$',f.read_text(),re.M) for f in sorted((project/'NLA/IE14').glob('*.lean'))}
for f in list((project/'NLA/IE14').glob('*.lean'))+[project/'Solution.lean']:
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',f.read_text()),f
 assert 'import Challenge' not in f.read_text()
check['proof_source_token_scan']='PASS no sorry/admit/native_decide/axiom tokens; Solution closure excludes Challenge'
check['canonical_status']='Solved' if '**Status:** Solved' in (repo/'linear-systems-and-elimination/IE-14/README.md').read_text() else 'inspect'
(out/'input-verification.json').write_text(json.dumps(check,indent=2)+'\n')
pins={};manifest=json.loads((project/'lake-manifest.json').read_text())
for p in manifest['packages']:
 path=project/'.lake/packages'/p['name']; actual=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip(); assert actual==p['rev'],p['name']
 status=subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],text=True); assert status=='',(p['name'],status)
 pins[p['name']]={'rev':actual,'tracked_clean':True,'url':p['url']}
pins['lean_version']=subprocess.check_output(['/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean','--version'],text=True).strip()
(out/'toolchain-and-package-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
print('PASS:23 candidate,10 frozen,7 originals,2 statement reviews,stable IE14 registry,10 clean exact package revisions')
