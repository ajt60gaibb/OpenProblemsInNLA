#!/usr/bin/env python3
"""Independent, read-only descriptive proposal auditor; no Lean/Comparator replay."""
from pathlib import Path
import hashlib, json, shutil, subprocess, sys
from datetime import datetime, timezone

ROOT = Path('/Users/ajt253/Documents/OpenProblemsInNLA')
WT = Path('/Users/ajt253/.codex/worktrees/re06-nonadaptive-oct26/OpenProblemsInNLA')
OUT = Path(__file__).resolve().parent
REV = ROOT/'reviews/2026-10-23-solved-lean'
CAND = '0c6d346763a932eb2d379f555e66d8ab3dbf3255'
EXEC = '1322d6c23e833cba4223b466a3717af1a197b904'
SRC = '181c365dc426875aaa61984c901478b1b7c696e6'
BASE = 'randomized-and-low-rank-approximation/RE-06/lean/'
PAGE = 'randomized-and-low-rank-approximation/RE-06/README.md'
FREEZE = 'docs/lean/proofs/RE-06/campaign-2026-10-26/FULL_TARGET_SOURCE_FREEZE.json'
checks=[]
def sha(b): return hashlib.sha256(b).hexdigest()
def git(ref, path): return subprocess.check_output(['git','-C',str(WT),'show',ref+':'+path])
def check(name, ok, **extra):
    checks.append(dict(name=name, passed=bool(ok), **extra))
    if not ok: raise AssertionError(name)
def write(path,b):
    p=OUT/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def dump(path,j): write(path,(json.dumps(j,indent=2,ensure_ascii=False)+'\n').encode())
def load(p): return json.loads(Path(p).read_bytes())
def entries(j):
    j=j.get('files',j)
    if isinstance(j,list):return {x['path']:{k:v for k,v in x.items() if k!='path'} for x in j}
    return {k:({'sha256':v} if isinstance(v,str) else v) for k,v in j.items()}
def sealed(label,rel,mname,msha,selected):
    p=REV/rel;m=(p/mname).read_bytes()
    check('sealed-manifest:'+label,sha(m)==msha)
    es=entries(json.loads(m));total=0
    for n,e in es.items():
        b=(p/n).read_bytes();total+=len(b)
        check('sealed-positive:'+label+':'+n,sha(b)==e['sha256'] and ('bytes' not in e or len(b)==e['bytes']))
    for n in [mname]+selected:write('evidence/'+label+'/'+n,(p/n).read_bytes())
    return {'original':str(p),'manifest':mname,'sha256':msha,'positive_count':len(es),'positive_bytes':total,
            'selected_verbatim_copies':selected,'full_positive_archive_copied_here':False}

def main():
    for v,psha in [(1,'c9dc77643a6c6b6c1ea9f5eff4295de546b0981efa582a1e147c5e37cea309cb'),
                    (2,'5712b7add2bb2fca11062bd6f83b482a74b6c087579b270505e0492cac5db845')]:
        p=Path('/private/tmp/nla-re06-promotion-proposal-v'+str(v));pb=(p/'PROMOTION_PACKET.json').read_bytes();j=json.loads(pb)
        check('v%d-packet-hash'%v,sha(pb)==psha)
        expected=set(j['files'])|{'PROMOTION_PACKET.json'}
        check('v%d-exact-proposal-file-set'%v,{x.name for x in p.iterdir()}==expected)
        for n,e in j['files'].items():
            b=(p/n).read_bytes();check('v%d-proposal-positive:'%v+n,sha(b)==e['sha256'] and len(b)==e['bytes'])
        for n in sorted(expected):write('proposal-v%d/'%v+n,(p/n).read_bytes())
    p=OUT/'proposal-v2';packet=load(p/'PROMOTION_PACKET.json')
    check('packet-exact-candidate-and-source',packet['candidate_ref']==CAND and packet['proof_source_ref']==SRC)
    cb=git(CAND,BASE+'PACKAGE_LOCK.json');cl=json.loads(cb);pl=load(p/'PACKAGE_LOCK.json')
    check('candidate-lock-hash',sha(cb)==packet['candidate_lock_sha256']=='7bfbc8d0493068bce0abcf6d239b539e047061bc5139ce1720e02c64b5592153')
    check('proposed-lock-hash',sha((p/'PACKAGE_LOCK.json').read_bytes())==packet['proposed_lock_sha256']=='e712ded5fbc472ab9fa999de9a1fa885aa86b0b88276f2a55afbc01a7a7a921a')
    tree=subprocess.check_output(['git','-C',str(WT),'ls-tree','-r','--name-only',CAND,'--',BASE],text=True).splitlines()
    names={n[len(BASE):] for n in tree}
    check('exact-295-canonical-input-set',names==set(cl['files'])|{'PACKAGE_LOCK.json'} and len(names)==295)
    candidate={}
    for n in sorted(names):
        b=git(CAND,BASE+n);candidate[n]=b;write('candidate/lean/'+n,b)
        check('actual-executed-merge-same-canonical:'+n,b==git(EXEC,BASE+n))
        if n!='PACKAGE_LOCK.json':
            e=cl['files'][n];check('candidate-positive:'+n,sha(b)==e['sha256'] and len(b)==e['bytes'])
    proposed=dict(candidate)
    proposed.update({'formalization.yaml':(p/'formalization.yaml').read_bytes(),'README.md':(p/'lean-README.md').read_bytes(),
                     'PACKAGE_LOCK.json':(p/'PACKAGE_LOCK.json').read_bytes()})
    changed=[n for n in sorted(names) if candidate[n]!=proposed[n]]
    check('exact-three-canonical-deltas',changed==sorted(packet['allowed_changed_canonical_inputs'])==['PACKAGE_LOCK.json','README.md','formalization.yaml'])
    check('unchanged-lock-keyset',set(pl['files'])==set(cl['files']) and pl['proof_source_ref']==cl['proof_source_ref']==SRC)
    lockd=[n for n in sorted(cl['files']) if cl['files'][n]!=pl['files'][n]]
    check('exact-two-locked-entry-deltas',lockd==['README.md','formalization.yaml'])
    for n,e in pl['files'].items():
        b=proposed[n];check('proposed-positive:'+n,sha(b)==e['sha256'] and len(b)==e['bytes'])
    sm=json.loads(candidate['SOURCE_MAP.json']);check('runtime-order-count91',len(sm['runtime_lean_order'])==91)
    for n in sm['runtime_lean_order']:
        if not isinstance(n,str):n=n['path']
        if n not in candidate:n=n.replace('.','/')+'.lean'
        check('runtime-unchanged:'+n,candidate[n]==proposed[n])
    check('all-mapped-copy-count278',len(sm['copies'])==278)
    for e in sm['copies']:
        b=proposed[e['path']]
        check('mapped-copy:'+e['path'],b==git(e['source_ref'],e['source_path']) and sha(b)==e['sha256'] and len(b)==e['bytes'])
    fb=git(SRC,FREEZE);write('evidence/FULL_TARGET_SOURCE_FREEZE.json',fb);f=json.loads(fb)
    check('exact-full-source-freeze',sha(fb)=='93df2eabffe17df3c1d9a2950a60bc0cfcea103e8b4285cbd117b7f945d21e8b')
    frozen=f['proof_inputs']+f['shared_inputs'];check('frozen-source-count87',len(frozen)==87)
    for e in frozen:
        n=e['path'].removeprefix('lean-statements/');b=proposed[n]
        check('frozen-source:'+n,b==git(SRC,e['path']) and sha(b)==e['sha256'] and len(b)==e['bytes'])
    cmp=json.loads(proposed['comparator.json']);exports=['svd_total','query_bound','successful','original_claim','explicit_claim','target']
    check('six-exact-exports-no-definition-allowances',cmp['theorem_names']==['NLA.Proofs.RE06.'+n for n in exports] and cmp['definition_names']==[])
    check('comparator-exact-standard-axioms',set(cmp['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'})
    oldpage=git(CAND,PAGE);write('candidate/RE-06-README.md',oldpage)
    check('entire-original-page-archive-exact',oldpage==(p/'ORIGINAL.md').read_bytes())
    check('entire-preceding-candidate-readme-exact',candidate['README.md']==(p/'CANDIDATE_README.md').read_bytes())
    newpage=(p/'canonical-README.md').read_bytes();marker=b'## Context and notation\n'
    check('original-context-through-EOF-exact',oldpage.split(marker,1)[1]==newpage.split(marker,1)[1])
    # The only changes before Context are status/date and a single added proof section.
    oldhead=oldpage.split(marker,1)[0];newhead=newpage.split(marker,1)[0]
    norm=newhead.split(b'## Lean proof and verification evidence',1)[0].replace(b'**Status:** Lean verified',b'**Status:** Solved').replace(b'**Last checked:** 2026-10-26',b'**Last checked:** 2026-09-13')
    check('original-leading-history-preserved-with-status-date-only',norm==oldhead)
    oldm=json.loads(candidate['formalization.yaml']);newm=json.loads(proposed['formalization.yaml'])
    delta=[]
    def diff(a,b,path=''):
        if type(a)!=type(b):delta.append(path);return
        if isinstance(a,dict):
            for k in sorted(set(a)|set(b)):
                if k not in a or k not in b:delta.append(path+'/'+k)
                else:diff(a[k],b[k],path+'/'+k)
        elif isinstance(a,list):
            if len(a)!=len(b):delta.append(path)
            else:
                for i,(x,y) in enumerate(zip(a,b)):diff(x,y,path+'/'+str(i))
        elif a!=b:delta.append(path)
    diff(oldm,newm)
    allowed={'/project/description','/status/phase','/status/whole_problem_verified','/status/canonical_status','/review/status','/review/reviewers','/review/notes'}
    allowed|={'/status/main_results/'+str(i)+'/verification_status' for i in range(6)}
    check('metadata-only-exact-description-status-review-fields',set(delta)==allowed,paths=delta)
    check('proposed-verified-status',newm['status']['whole_problem_verified'] is True and newm['status']['canonical_status']=='Lean verified')
    allprose='\n'.join((p/n).read_text() for n in ['lean-README.md','proof-README.md','formalization.yaml'])
    check('explicit-future-final-Linux-receipt',all('will receive a separate' in (p/n).read_text() for n in ['lean-README.md','proof-README.md','formalization.yaml']))
    check('honest87-Linux91-local-scope',all('87' in (p/n).read_text() and '91' in (p/n).read_text() for n in ['lean-README.md','proof-README.md']))
    evidence=[]
    evidence.append(sealed('full-source-verification','re06-full-source-review/verification','EVIDENCE_MANIFEST.json','61facd1585065573f8fa64d5ee15b7574bc602b1ea829f2f12594ce720604119',['APPROVAL.json','SEAL.json','REVIEW.md']))
    evidence.append(sealed('full-source-crosscheck','re06-inverse-outer-review/crosscheck','FILE_SHA256.json','7575843d5eea7804a9ec4851296e542d50dca4a8e8cf97610fadba84518db9c0',['APPROVAL.json','MATHEMATICAL_REVIEW.txt','FRESH82_ACCEPTED.json','full-target/RESULT.json']))
    evidence.append(sealed('package-inventory','re06-package-review/inventory','FILE_SHA256.json','24d955d7591d570362af73b38a411c5ec7963e54783609e3e324081468521d80',['REVIEW.json','PACKAGE_FIDELITY.md','replay-v2/RESULT.json']))
    evidence.append(sealed('package-verification','re06-package-review/verification','EVIDENCE_MANIFEST.json','28d5929b6f39ee7408e4343678d635a81961f56bd363fb7a1d981b37b0c62e3a',['APPROVAL.json','SEAL.json','REVIEW.md','result.json']))
    evidence.append(sealed('actual-Linux-crosscheck','re06-linux-review/crosscheck-v2','FILE_SHA256.json','5a9272117c1c6e5399f6088478117733bd7412651063a291353a1c59447b16c8',['APPROVAL.json','REVIEW.txt','DIAGNOSTICS.json','audit-20261026T230527891391Z/RESULT.json']))
    check('source-verification-approval',load(OUT/'evidence/full-source-verification/APPROVAL.json')['approved'] is True)
    check('own-source-approval',load(OUT/'evidence/full-source-crosscheck/APPROVAL.json')['exact_commit']==SRC)
    pi=load(OUT/'evidence/package-inventory/REVIEW.json');pv=load(OUT/'evidence/package-verification/APPROVAL.json')
    check('both-package-approved-exact-candidate',pi['passed'] is True and pv['approved'] is True and pi['reviewed_commit']==pv['package_commit']==CAND)
    check('both-package-exact-lock',pi['package_lock_sha256']==pv['package_lock_sha256']==sha(cb))
    ir=load(OUT/'evidence/package-inventory/replay-v2/RESULT.json')
    check('inventory-own91-plus-audit-plus3-controls',ir['passed'] is True and ir['runtime_source_builds']==91 and ir['own_literal_audit_builds']==1 and ir['actual_negative_commands']==3 and ir['expected_outcomes']==95)
    check('verification-own87-plus13-outcomes',pv['lifted_own_objects']==87 and pv['new_command_outcomes']==13 and pv['fresh_wrappers']==4)
    ci=load(OUT/'evidence/actual-Linux-crosscheck/APPROVAL.json')
    check('actual-candidate-Linux-approval',ci['source_head']==CAND and ci['actually_executed_merge']==EXEC and ci['actual_Comparator_accepted'] is True and ci['actual_LeanCert_kernel_checked'] is True)
    check('actual-CI87-not91',ci['actual_Linux_import_modules']==87 and ci['live_Lean_source_inventory']==91 and ci['all91_compiled_claim'] is False)
    dump('EVIDENCE_BINDINGS.json',{'archives':evidence,'verified_positive_count':sum(x['positive_count'] for x in evidence),'portable_selected_snapshots_only':True,
       'outside_manifest_seals':{'full-source-verification/SEAL.json':'325439f439d632b77e45c1ddc9e104ccebe987ad1e1ff03461b43a5a4b6086c9','package-verification/SEAL.json':'212f905167193f5743a0538533adf4ee67fac05f6293a7508f66c84ae8b352c4'}})
    for n,h in [('full-source-verification/SEAL.json','325439f439d632b77e45c1ddc9e104ccebe987ad1e1ff03461b43a5a4b6086c9'),('package-verification/SEAL.json','212f905167193f5743a0538533adf4ee67fac05f6293a7508f66c84ae8b352c4')]:
        check('outside-manifest-seal:'+n,sha((OUT/'evidence'/n).read_bytes())==h)
    # Only the disposable overlay is written; immutable proposal and live WT remain untouched.
    overlay=Path('/private/tmp/re06-promotion-crosscheck-overlay');overlay.mkdir(exist_ok=False)
    try:
        for n,b in proposed.items():
            q=overlay/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
        cmd=[sys.executable,str(WT/'tools/lean/validate_manifest.py'),str(overlay)]
        env={**__import__('os').environ,'PYTHONDONTWRITEBYTECODE':'1','PYTHONPATH':'/private/tmp/nla-oct23-pydeps'}
        r=subprocess.run(cmd,capture_output=True,text=True,env=env)
        write('METADATA_VALIDATOR.log',(r.stdout+r.stderr).encode());check('real-v04-metadata-validator',r.returncode==0,command=cmd,PYTHONPATH=env['PYTHONPATH'])
    finally:shutil.rmtree(overlay)
    dump('RESULT.json',{'reviewer':'/root/re06_counts/inverse_outer_crosscheck','non_author':True,'UTC':datetime.now(timezone.utc).isoformat(),
       'scope':'Immutable descriptive promotion v2 only; prior source/package/actual candidate Linux approvals independently rebound; no new Lean or Comparator execution',
       'passed':True,'candidate_ref':CAND,'executed_candidate_merge':EXEC,'proof_source_ref':SRC,'proposal_packet_sha256':sha((p/'PROMOTION_PACKET.json').read_bytes()),
       'proposed_lock_sha256':sha((p/'PACKAGE_LOCK.json').read_bytes()),'canonical_input_count':295,'canonical_deltas':changed,'locked_entry_deltas':lockd,
       'unchanged_runtime_sources':91,'unchanged_frozen_sources':87,'unchanged_mapped_copies':278,'metadata_delta_paths':delta,
       'positive_sealed_evidence_files_verified':sum(x['positive_count'] for x in evidence),'check_count':len(checks),'checks':checks,
       'proposal_applied':False,'new_Lean_or_Comparator_execution':False,'final_promoted_input_Linux_receipt_claimed':False,'final_evidence_seal_claimed':False})
    print(json.dumps({'passed':True,'checks':len(checks),'canonical_inputs':295,'sealed_evidence_positives':sum(x['positive_count'] for x in evidence)}))

if __name__=='__main__':
    try:main()
    except Exception as e:
        dump('AUDITOR_DIAGNOSTIC.json',{'error':repr(e),'passed_checks':len(checks),'checks':checks})
        raise
