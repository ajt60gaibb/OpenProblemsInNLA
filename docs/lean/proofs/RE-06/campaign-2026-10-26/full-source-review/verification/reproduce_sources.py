#!/usr/bin/env python3
"""Independent fresh closed-Git Gaussian source replay; audit follows separately."""
import argparse, datetime, hashlib, json, os, re, subprocess, shutil
from pathlib import Path

REF = '181c365dc426875aaa61984c901478b1b7c696e6'
BASE = '099805ef1ce7347d373e47cccc3b2d7cf580a99e'
PRE = 'docs/lean/proofs/RE-06/campaign-2026-10-26/preproof/'
DOC = 'docs/lean/proofs/RE-06/campaign-2026-10-26/gaussian-author/'
STD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(b): return hashlib.sha256(b).hexdigest()

def main():
    p=argparse.ArgumentParser()
    for key in ['repo','lean','packages','build','output']: p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--reuse-repo',type=Path)
    p.add_argument('--prior-source-result',type=Path)
    a=p.parse_args();a.build.mkdir(parents=True,exist_ok=False);a.output.mkdir(parents=True,exist_ok=True)
    src=a.build/'source';obj=a.build/'objects'
    for d in [src,obj,a.output/'sources',a.output/'logs']:d.mkdir(parents=True,exist_ok=True)
    def git(*v,repo=a.repo):return subprocess.check_output(['git','-C',str(repo),*v])
    def blob(path,ref=REF,repo=a.repo):return git('show',ref+':'+path,repo=repo)
    checks=[];commands=[]
    def ck(n,v,**d):
        checks.append({'check':n,'pass':bool(v),**d})
        if not v:raise RuntimeError('Failed check: '+n)
    fb=blob('docs/lean/proofs/RE-06/campaign-2026-10-26/FULL_TARGET_SOURCE_FREEZE.json');freeze=json.loads(fb);(a.output/'FULL_TARGET_SOURCE_FREEZE.json').write_bytes(fb)
    ck('exact_full_source_freeze',sha(fb)=='93df2eabffe17df3c1d9a2950a60bc0cfcea103e8b4285cbd117b7f945d21e8b' and freeze['source_inputs']==87 and freeze['proof_modules']==82 and freeze['unchanged_shared_modules']==5)
    entries={e['path']:e for e in freeze['proof_inputs']+freeze['shared_inputs']};freeze['proof_files']=list(entries.values())
    for e in entries.values():
        b=blob(e['path']);ck('frozen_full_input:'+e['path'],sha(b)==e['sha256'] and len(b)==e['bytes'])
    preexports=json.loads(blob(PRE+'EXPORTS.json'))['exports'];ck('six_literal_preapproved_export_headers',freeze['literal_exports']==[{k:e[k] for k in ['name','binders','type']} for e in preexports])
    ck('implementation_authorization_precedes_full_source',freeze['authorization_commit']=='bb0dd13e3321bb35af762936a75c2c3a8a8363c6' and subprocess.run(['git','-C',str(a.repo),'merge-base','--is-ancestor',freeze['authorization_commit'],REF]).returncode==0)
    lock=json.loads(blob(PRE+'INPUT_LOCK.json'));ck('same_49_original_lock',sha(blob(PRE+'INPUT_LOCK.json'))=='fda0f85d913233b3c62b707b46bf0edd2fca9ba8ba34a618b57d6bc7bb4e222a' and len(lock['files'])==49)
    for e in lock['files']:
        b=blob(e['path']);ck('original:'+e['path'],b==blob(e['path'],BASE)==blob(PRE+'originals/'+e['path']) and sha(b)==e['sha256'] and len(b)==e['bytes'])
    packet=json.loads(blob(PRE+'PACKET_LOCK.json'));ck('unchanged_preproof_packet_lock',sha(blob(PRE+'PACKET_LOCK.json'))=='f318ade71c4e97a2952052ee94c76ca254e558bc0f9bbc15b72d90a738106bc9')
    for e in packet['files']:
        b=blob(PRE+e['path']);ck('packet:'+e['path'],sha(b)==e['sha256'] and len(b)==e['bytes'])
    registry=json.loads(blob('problem_ids.json'));ck('217_fixed_IDs_and_RE06_Solved',len(registry)==217 and registry['RE-06']=='randomized-and-low-rank-approximation/RE-06/README.md' and b'**Status:** Solved' in blob(registry['RE-06']))
    reuse=json.loads(blob(PRE+'REUSE_LOCK.json'));reuse_repo=a.reuse_repo or Path(reuse['source_repository_read_only'])
    for e in reuse['files']:
        b=blob(e['path'],reuse['source_commit'],repo=reuse_repo);ck('retained_reuse:'+e['path'],b==blob(PRE+'supplementary-reuse/'+e['path']) and sha(b)==e['sha256'] and len(b)==e['bytes'])
    modules={};order=[];records=[];decls=[]
    def visit(n):
        if n in modules:return
        path='lean-statements/'+n.replace('.','/')+'.lean';b=blob(path)
        for child in re.findall(r'^import\s+([\w.]+)\s*$',b.decode(),re.M):
            if child.startswith(('NLA.','Reviewed.')):visit(child)
        modules[n]=b;order.append(n);records.append({'module':n,'path':path,'sha256':sha(b),'bytes':len(b)})
    for e in freeze['proof_files']:visit(e['path'][len('lean-statements/'):-5].replace('/','.'))
    ck('exact_closed87_source_closure',len(modules)==87 and {e['path'] for e in records}==set(entries))
    for n,b in modules.items():
        if '.Proofs.' not in n:continue
        code=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S);code=re.sub(r'--[^\n]*','',code)
        ck('kernel_source_without_holes_or_bypass:'+n,'set_option leancert.trust "kernel"' in code and not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b|skipKernelTC',re.sub(r'"(?:\\.|[^"\\])*"','',code)))
        spaces=[]
        for raw in code.splitlines():
            line=raw.strip();ns=re.fullmatch(r'namespace\s+([\w.]+)',line)
            if ns:spaces.append(ns[1]);continue
            if re.fullmatch(r'end(?:\s+\S+)?',line):
                if spaces:spaces.pop()
                continue
            d=re.match(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)',line)
            if d:decls.append({'name':'.'.join(spaces+[d[2]]),'kind':'theorem' if d[1] in ['theorem','lemma'] else 'definition','module':n})
    manifest=json.loads(blob('lean-statements/lake-manifest.json'))
    def pins():
        out=[]
        for e in manifest['packages']:
            d=a.packages/e['name'];head=git('rev-parse','HEAD',repo=d).decode().strip();status=git('status','--porcelain','--untracked-files=no',repo=d).decode();out.append({'name':e['name'],'expected':e['rev'],'actual':head,'tracked_clean':not status,'pass':head==e['rev'] and not status})
        return out
    before=pins();ck('ten_clean_pinned_dependencies_before',len(before)==10 and all(e['pass'] for e in before))
    version=subprocess.check_output([str(a.lean),'--version'],text=True).strip();ck('pinned_Lean4331',blob('lean-statements/lean-toolchain')==b'leanprover/lean4:v4.33.1\n' and '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
    env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[obj]+[a.packages/e['name']/'.lake/build/lib/lean' for e in manifest['packages']]+[a.lean.parent.parent/'lib/lean']))
    def run(n,b,expected=0,needle=None):
        f=src/(n.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
        cpy=a.output/'sources'/(n.replace('.','/')+'.lean.txt');cpy.parent.mkdir(parents=True,exist_ok=True);cpy.write_bytes(b)
        o=obj/(n.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True);argv=[str(a.lean),'-R',str(src),'-o',str(o),str(f)]
        result=subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True,timeout=420);log=result.stdout+result.stderr;(a.output/'logs'/(n+'.log')).write_text(log)
        c={'module':n,'argv':argv,'exit_code':result.returncode,'expected_exit':expected,'source_sha256':sha(b),'object_sha256':sha(o.read_bytes()) if o.exists() else None,'log_sha256':sha(log.encode())};commands.append(c);print(n,result.returncode,flush=True)
        ck('compiler:'+n,result.returncode==expected and (needle is None or needle in log),**c);return log
    reuse=[];prior=None
    if a.prior_source_result:
        pb=a.prior_source_result.read_bytes();prior=json.loads(pb);ck('prior_is_own_fresh63_result',prior['reviewer']=='/root/verification' and prior['source_commit']=='05ceb708f444ed36d34afe2eb1f2d98b0b059a0c' and prior['pass'] and len(prior['commands'])==63)
        ck('continuous_prior_compiler_and_pins',prior['compiler_sha256']==sha(a.lean.read_bytes()) and prior['dependency_pins_after']==before)
        prior_records={e['module']:e for e in prior['source_records']};prior_commands={e['module']:e for e in prior['commands']};prior_build=Path(prior['private_build'])
        for n in order:
            if n not in prior_records or prior_records[n]['sha256']!=sha(modules[n]):continue
            c=prior_commands[n];f=prior_build/'source'/(n.replace('.','/')+'.lean');o=prior_build/'objects'/(n.replace('.','/')+'.olean')
            ck('own_intersection_source_object:'+n,c['exit_code']==0 and sha(f.read_bytes())==sha(modules[n]) and sha(o.read_bytes())==c['object_sha256'])
            destsrc=src/(n.replace('.','/')+'.lean');destsrc.parent.mkdir(parents=True,exist_ok=True);destsrc.write_bytes(modules[n]);destobj=obj/(n.replace('.','/')+'.olean');destobj.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(o,destobj)
            saved=a.output/'sources'/(n.replace('.','/')+'.lean.txt');saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(modules[n])
            reuse.append({'module':n,'source_sha256':sha(modules[n]),'object_sha256':sha(destobj.read_bytes()),'prior_object':str(o),'prior_source_result_sha256':sha(pb),'prior_argv':c['argv']})
        ck('exact57_own_intersection',len(reuse)==57)
    reused={e['module'] for e in reuse}
    for n in order:
        if n not in reused:run(n,modules[n])
    after=pins();ck('ten_dependency_pins_unchanged_after',before==after and all(e['pass'] for e in after));ck('all87_private_sources_unchanged',all((src/(n.replace('.','/')+'.lean')).read_bytes()==b for n,b in modules.items()))
    result={'pass':all(e['pass'] for e in checks),'reviewer':'/root/verification','non_author':True,'UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':REF,'reuse_records':reuse,'prior_source_result':str(a.prior_source_result) if a.prior_source_result else None,'scope':'Full87 source closure with explicit own object intersection lift if selected; independent final audit and controls follow','checks':checks,'commands':commands,'source_records':records,'declarations':decls,'compiler_version':version,'compiler_sha256':sha(a.lean.read_bytes()),'dependency_pins_before':before,'dependency_pins_after':after,'private_build':str(a.build),'LEAN_PATH':env['LEAN_PATH'],'script_sha256':sha(Path(__file__).read_bytes()),'new_Linux_execution':False,'Comparator_execution':False}
    (a.output/'SOURCE_RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'pass':result['pass'],'checks':len(checks),'commands':len(commands),'source_declarations':len(decls)}),flush=True)

if __name__=='__main__':main()
