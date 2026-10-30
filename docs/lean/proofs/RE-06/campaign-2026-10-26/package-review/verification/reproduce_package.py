#!/usr/bin/env python3
"""Independent immutable RE06 candidate audit, own object lift, actual library comparison."""
import argparse, datetime, hashlib, json, os, re, subprocess
from pathlib import Path
REF='0c6d346763a932eb2d379f555e66d8ab3dbf3255'
PROOF='181c365dc426875aaa61984c901478b1b7c696e6'
PREFIX='randomized-and-low-rank-approximation/RE-06/lean/'
PRE='docs/lean/proofs/RE-06/campaign-2026-10-26/preproof/'
STD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()

def main():
    p=argparse.ArgumentParser()
    for n in ['repo','lean','packages','prior','build','output']:p.add_argument('--'+n,type=Path,required=True)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);a.build.mkdir(parents=True,exist_ok=False)
    src=a.build/'source';obj=a.build/'objects';ts=a.build/'tool-source';to=a.build/'tool-objects'
    for d in [src,obj,ts,to,a.output/'logs',a.output/'consumers',a.output/'tool-sources']:d.mkdir(parents=True,exist_ok=True)
    def git(*args):return subprocess.check_output(['git','-C',str(a.repo),*args])
    def blob(path,ref=REF):return git('show',ref+':'+path)
    checks=[];commands=[]
    def ck(n,v,**d):
        checks.append({'check':n,'pass':bool(v),**d})
        if not v:raise RuntimeError('Failed check: '+n)
    files={}
    for line in git('ls-tree','-r',REF,'--',PREFIX).decode().splitlines():
        mode,kind,rest=line.split(' ',2);oid,path=rest.split('\t');n=path[len(PREFIX):]
        ck('plain_package_input:'+n,mode=='100644' and kind=='blob' and '..' not in Path(n).parts and not Path(n).is_absolute())
        b=blob(path);files[n]=b;f=src/n;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
    lock=json.loads(files['PACKAGE_LOCK.json']);ck('exact295_inputs294_locked_plus_self',len(files)==295 and len(lock['files'])==294 and set(files)==set(lock['files'])|{'PACKAGE_LOCK.json'})
    ck('exact_candidate_package_lock',sha(files['PACKAGE_LOCK.json'])=='7bfbc8d0493068bce0abcf6d239b539e047061bc5139ce1720e02c64b5592153' and lock['proof_source_ref']==PROOF)
    for n,e in lock['files'].items():ck('locked_input:'+n,sha(files[n])==e['sha256'] and len(files[n])==e['bytes'])
    mapping=json.loads(files['SOURCE_MAP.json']);ck('exact278_source_copies',len(mapping['copies'])==278 and mapping['proof_source_ref']==PROOF and mapping['full_source_freeze_sha256']=='93df2eabffe17df3c1d9a2950a60bc0cfcea103e8b4285cbd117b7f945d21e8b')
    for e in mapping['copies']:
        b=blob(e['source_path'],e['source_ref']);ck('upstream_verbatim_copy:'+e['path'],b==files[e['path']] and sha(b)==e['sha256'] and len(b)==e['bytes'])
    shared=[e for e in mapping['copies'] if e['path'].startswith(('NLA/','Reviewed/')) and e['path'].endswith('.lean')]
    ck('exact87_shared_copies',len(shared)==87 and all(e['source_ref']==PROOF for e in shared))
    ck('canonical_readme_registry_preserved',blob('randomized-and-low-rank-approximation/RE-06/README.md')==blob('randomized-and-low-rank-approximation/RE-06/README.md',PROOF) and blob('problem_ids.json')==blob('problem_ids.json',PROOF) and len(json.loads(blob('problem_ids.json')))==217)
    prelock=json.loads(files['reviews/preproof/INPUT_LOCK.json']);ck('49_originals',len(prelock['files'])==49)
    for e in prelock['files']:
        b=files['reviews/preproof/originals/'+e['path']];ck('published_original:'+e['path'],b==blob(e['path'])==blob(e['path'],'099805ef1ce7347d373e47cccc3b2d7cf580a99e') and sha(b)==e['sha256'] and len(b)==e['bytes'])
    exports=json.loads(files['reviews/preproof/EXPORTS.json'])['exports'];names=['NLA.Proofs.RE06.'+e['name'] for e in exports]
    config=json.loads(files['comparator.json']);ck('exact6_theorem_only_comparator_config',len(names)==6 and config['theorem_names']==names and config['definition_names']==[] and set(config['permitted_axioms'])==STD and config['challenge_module']=='Challenge' and config['solution_module']=='Solution')
    meta=json.loads(files['formalization.yaml']);ck('truthful_unpromoted_metadata',meta['status']['phase']=='full-target-candidate' and meta['status']['whole_problem_verified'] is False and meta['status']['canonical_status']=='Solved' and meta['status']['sorry_count']==0 and meta['status']['challenge_placeholder_count']==6 and [e['declaration'] for e in meta['status']['main_results']]==names and set(meta['status']['axioms'])==STD)
    ck('source_credit_preserved',meta['sources'][0]['authors']==['Sidney Holden'] and meta['sources'][0]['id'] in files)
    deriv=json.loads(files['CHALLENGE_DERIVATION.json']);original=files[deriv['original']['path']];removed=deriv['removed_lines']
    ck('verbatim_original_reference',original==blob(PRE+'Challenge.lean',PROOF) and sha(original)==deriv['original']['sha256']=='21f59e23c4c4b0168eb031de49b0fe8c31c72179713f1479c895a8020bc7d1a8')
    expected_lines=['#assert_trust kernel '+e['name'] for e in exports]+['#print axioms '+e['name'] for e in exports]
    ck('only12_instrumentation_lines_removed',removed==expected_lines and all(original.decode().splitlines().count(x)==1 for x in removed) and files['Challenge.lean']==('\n'.join(x for x in original.decode().splitlines() if x not in removed)+'\n').encode() and sha(files['Challenge.lean'])==deriv['canonical_reference_sha256'])
    control=files['controls/ChallengeTrustRejection.lean.txt'].decode();ck('moved_commands_preserve_original_namespace',control=='import Challenge\n\nnamespace NLA.Proofs.RE06\n'+'\n'.join(removed)+'\nend NLA.Proofs.RE06\n')
    runtime={n[:-5].replace('/','.'):b for n,b in files.items() if n.endswith('.lean') and not n.startswith('reviews/')};ck('91_runtime_sources',len(runtime)==91 and len(mapping['runtime_lean_order'])==91 and set(mapping['runtime_lean_order'])=={n.replace('.','/')+'.lean' for n in runtime})
    order=[];seen=set();external=set()
    def visit(n):
        if n in seen:return
        seen.add(n)
        for c in re.findall(r'^import\s+([\w.]+)\s*$',runtime[n].decode(),re.M):
            if c in runtime:visit(c)
            else:external.add(c)
        order.append(n)
    for n in sorted(runtime):visit(n)
    ck('imports_confined_to_package_or_pinned_dependencies',all(n.startswith(('Mathlib','LeanCert','Lean')) for n in external))
    # Reconstruct the reference environment's literal import closure: no proof/Solution imports.
    reference_seen=set()
    def ref_visit(n):
        if n in reference_seen:return
        reference_seen.add(n)
        for c in re.findall(r'^import\s+([\w.]+)\s*$',runtime[n].decode(),re.M):
            if c in runtime:ref_visit(c)
    ref_visit('Challenge');ck('reference_isolated_from_solution_and_proof_modules','Solution' not in reference_seen and not any('.Proofs.' in n for n in reference_seen) and reference_seen=={'Challenge','NLA.Statements.RE06','NLA.Statements.Infrastructure','NLA.Computation.NonadaptiveMatrixQuery','NLA.Computation.SVDMachine'})
    manifest=json.loads(files['lake-manifest.json']);upstream_manifest=json.loads(blob('lean-statements/lake-manifest.json',PROOF));expected_manifest=dict(upstream_manifest);expected_manifest['name']='NLARE06';ck('exact_manifest_only_project_name_differs',manifest==expected_manifest and upstream_manifest['name']=='NLAStatements')
    def pins():
        out=[]
        for e in manifest['packages']:
            d=a.packages/e['name'];h=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip();st=subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True);out.append({'name':e['name'],'expected':e['rev'],'actual':h,'tracked_clean':not st,'pass':h==e['rev'] and not st})
        return out
    before=pins();ck('ten_pins_clean_before',len(before)==10 and all(e['pass'] for e in before));version=subprocess.check_output([str(a.lean),'--version'],text=True).strip();ck('pinned_compiler',files['lean-toolchain']==b'leanprover/lean4:v4.33.1\n' and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
    deps=[a.packages/e['name']/'.lake/build/lib/lean' for e in manifest['packages']];env=os.environ.copy();env['PATH']=str(a.lean.parent)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=':'.join(map(str,[obj]+deps+[a.lean.parent.parent/'lib/lean']))
    def run(n,b,root=src,objects=obj,expected=0,needle=None,run_main=False):
        f=root/(n.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);o=objects/(n.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
        argv=[str(a.lean),'--run',str(f)] if run_main else [str(a.lean),'-R',str(root),'-o',str(o),str(f)]
        r=subprocess.run(argv,cwd=root,env=env,capture_output=True,text=True,timeout=420);log=r.stdout+r.stderr;(a.output/'logs'/(n+'.log')).write_text(log);saved=a.output/'consumers'/(n.replace('.','/')+'.lean.txt');saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(b)
        c={'module':n,'argv':argv,'exit_code':r.returncode,'expected_exit':expected,'source_sha256':sha(b),'object_sha256':sha(o.read_bytes()) if o.exists() else None,'log_sha256':sha(log.encode())};commands.append(c);print(n,r.returncode,flush=True);ck('compiler:'+n,r.returncode==expected and (needle is None or needle in log),**c);return log
    pb=a.prior.read_bytes();prior=json.loads(pb);ck('own_approved87_source_receipt',prior['pass'] and prior['reviewer']=='/root/verification' and prior['source_commit']==PROOF and len(prior['source_records'])==87)
    priorapproval=json.loads((a.prior.parent/'APPROVAL.json').read_text());ck('own_full_source_approval_bound',priorapproval['approved'] and priorapproval['non_author'] and priorapproval['source_result_sha256']==sha(pb))
    ck('continuous_own_compiler_and_pins',prior['compiler_sha256']==sha(a.lean.read_bytes()) and prior['dependency_pins_after']==before)
    ps={e['module']:e for e in prior['source_records']};po={e['module']:e for e in prior['commands']+prior['reuse_records']};reused=[]
    for e in shared:
        n=e['path'][:-5].replace('/','.');old=Path(prior['private_build']);f=old/'source'/e['path'];o=old/'objects'/Path(e['path']).with_suffix('.olean');ob=o.read_bytes();b=files[e['path']]
        ck('own87_source_and_object:'+n,sha(b)==ps[n]['sha256']==po[n]['source_sha256'] and f.read_bytes()==b and sha(ob)==po[n]['object_sha256']);dest=obj/Path(e['path']).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(ob);reused.append({'module':n,'source_sha256':sha(b),'object_sha256':sha(ob),'from':str(o),'to':str(dest)})
    ck('all87_own_objects_lifted',len(reused)==87 and set(ps)=={e['module'] for e in reused})
    for n in order:
        if n not in ps:run(n,runtime[n])
    # Replay own exact consumers and all525 actual source declaration audits in canonical environments.
    prioraudit=(a.prior.parent/'sources/Independent/FullTargetAudit.lean.txt').read_bytes();ck('own_audit_bytes_bound',sha(prioraudit)==next(e['source_sha256'] for e in json.loads((a.prior.parent/'AUDIT_RESULT.json').read_text())['commands'] if e['module']=='Independent.FullTargetAudit'))
    audit=prioraudit.replace(b'import NLA.Computation.SVDMachine\n',b'import Solution\nimport Identity\nimport EndpointAudit\nimport NLA.Computation.SVDMachine\n',1)
    log=run('Independent.CanonicalFullAudit',audit);closures={n:{x.strip() for x in v.split(',') if x.strip()} for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)}
    for n in re.findall(r"'([^']+)' does not depend on any axioms",log):closures[n]=set()
    expected={e['name'] for e in prior['declarations']}|set(json.loads((a.prior.parent/'AUDIT_RESULT.json').read_text())['own_consumers']);ck('all533_actual_kinds_kernel_and_axioms',len(expected)==533 and set(closures)==expected and all(v<=STD for v in closures.values()),closures={n:sorted(v) for n,v in closures.items()});ck('six_canonical_exports_exact_std3',all(closures[n]==STD for n in names))
    for n,needle in [('ChallengeTrustRejection','sorryAx'),('DefinitionKindRejection','expected actual theorem declaration'),('CustomAxiomRejection','custom: PackageOracle')]:
        log=run('Negative.'+n,files['controls/'+n+'.lean.txt'],root=a.build/'control-source',expected=1,needle=needle)
        if n=='ChallengeTrustRejection':ck('six_actual_reference_holes_rejected',log.count('error: #assert_trust:')==6 and log.count('depends on sorry or unrecognized axioms')==6 and 'Unknown' not in log)
    tool_lock_bytes=blob('tools/lean/source-lock.json');tool_lock=json.loads(tool_lock_bytes);(a.output/'source-lock.json').write_bytes(tool_lock_bytes);tools=[];archive='eigenvalues-and-inverse-problems/IS-03/lean/verification/linux-2026-09-12/source/forsythe/'
    env['LEAN_PATH']=':'.join(map(str,[to,obj]+deps+[a.lean.parent.parent/'lib/lean']))
    for n,d in [('Export.Parse','.tools/lean4export/Export/Parse.lean'),('Comparator.Util','.tools/comparator/Comparator/Util.lean'),('Comparator.Axioms','.tools/comparator/Comparator/Axioms.lean'),('Comparator.Compare','.tools/comparator/Comparator/Compare.lean')]:
        e=next(e for e in tool_lock['files'] if e['destination']==d);b=blob(archive+d);ck('pinned_library_source:'+n,sha(b)==e['sha256'] and len(b)==e['bytes']);f=a.output/'tool-sources'/(n.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);tools.append({'module':n,**e});run(n,b,root=ts,objects=to)
    runner=(a.output/'ActualComparatorLibrary.lean.txt').read_bytes();log=run('ActualComparatorLibrary',runner,root=ts,objects=to,run_main=True);ck('actual6_library_comparisons_axiom_checks_and_reference_rejects',log.count('PASS actual exact signature:')==6 and log.count('PASS actual transitive standard-three axiom audit:')==6 and log.count('PASS actual reference sorry rejection:')==6)
    ck('own87_originals_and_copies_unchanged',all(sha(Path(e['from']).read_bytes())==e['object_sha256'] and sha(Path(e['to']).read_bytes())==e['object_sha256'] for e in reused));after=pins();ck('ten_pins_clean_and_continuous_after',before==after and all(e['pass'] for e in after));ck('all295_package_input_bytes_unchanged',all((src/n).read_bytes()==b for n,b in files.items()))
    r={'pass':all(c['pass'] for c in checks),'reviewer':'/root/verification','non_author':True,'UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'package_commit':REF,'proof_source_ref':PROOF,'scope':'Unpromoted full canonical candidate, own87object lift plus4fresh wrappers, own full audit, actual controls and pinned Comparator library; no actual Linux/CLI/exporter/raw-kernel claim','checks':checks,'commands':commands,'package_inputs':[{'path':n,'bytes':len(b),'sha256':sha(b)} for n,b in files.items()],'runtime_order':order,'external_imports':sorted(external),'reference_project_import_closure':sorted(reference_seen),'reuse_records':reused,'prior_source_result_sha256':sha(pb),'prior_full_source_approval_sha256':sha((a.prior.parent/'APPROVAL.json').read_bytes()),'private_build':str(a.build),'dependency_pins_before':before,'dependency_pins_after':after,'compiler_version':version,'compiler_sha256':sha(a.lean.read_bytes()),'tool_pins':tools,'Forsythe_commit':tool_lock['commit'],'Comparator_library_executed':True,'Comparator_CLI_executed':False,'Linux_CI_run':False,'exporter_executed':False,'raw_kernel_replay':False,'script_sha256':sha(Path(__file__).read_bytes())}
    (a.output/'result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'pass':r['pass'],'checks':len(checks),'commands':len(commands)}),flush=True)
if __name__=='__main__':main()
