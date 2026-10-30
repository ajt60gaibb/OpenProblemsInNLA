#!/usr/bin/env python3
"""Independent fresh RE05 Gaussian scalar and finite-product moments including exact private helpers; no Wick or success-probability/Target claim."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,importlib.util,json,os,re,subprocess,tempfile,traceback
from source_inventory import declarations_of,without_comments
B=Path(__file__).resolve().parent;REPO=B.parents[5];LIVE=REPO/'lean-statements'
parser=argparse.ArgumentParser()
parser.add_argument('--lean-bin',type=Path,required=True,help='Exact recorded Lean executable or its bin directory')
parser.add_argument('--package-cache',type=Path,required=True,help='Directory containing all ten pinned package checkouts')
parser.add_argument('--object-parent',type=Path,default=Path(tempfile.gettempdir()))
parser.add_argument('--run-dir',default='run-attempt-1')
a=parser.parse_args()
LEAN=a.lean_bin.resolve();LEAN=LEAN/'lean' if LEAN.is_dir() else LEAN
CACHE=a.package_cache.resolve();ALLOWED={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=lambda:datetime.now(timezone.utc).isoformat()
config=json.loads((B/'source-lock.json').read_text())
assert sha(B/'source-lock.json')=='ad96733b4910c27bf0f6397a700a5d25881f351b72ff8b0dbfde80624a3b928d'
input_lock=json.loads((REPO/config['input_lock']['path']).read_text())
assert sha(REPO/config['input_lock']['path'])==config['input_lock']['sha256']
assert len(input_lock['source_inputs'])==18
frozen={str(Path(x['path']).relative_to('lean-statements')):(REPO/x['path']).read_bytes() for x in config['union']}
for x in config['union']:assert sha(REPO/x['path'])==x['sha256']
lookup={d['name']:d for d in config['declarations']}
spec=importlib.util.spec_from_file_location('literal_helper',B/'literal_type.py');lit=importlib.util.module_from_spec(spec);spec.loader.exec_module(lit)
lit.lookup=lookup;lit.frozen=frozen;lit.without_comments=without_comments;lit.sha=lambda b:hashlib.sha256(b).hexdigest()
preamble=(B/'audit-preamble.lean.txt').read_text()
def audit(d):
    kind='theorem' if d['kind'] in {'theorem','lemma'} else 'inductive' if d['kind'] in {'structure','inductive'} else 'definition'
    return '#audit_named '+ ' '.join(json.dumps(x) for x in [d['name'],d['source'].removesuffix('.lean').replace('/','.'),d['visibility'],kind])+'\n'
consumers={};bindings={}
for b in config['blocks']:
    code='\n'.join('import '+m for m in b['roots'])+'\n'+preamble
    code+='\n'.join(audit(d) for d in b['declarations'])
    code+='\nnoncomputable section\nopen scoped BigOperators Matrix InnerProductSpace\n'
    examples=[]
    for n in b['literal_endpoints']:
        part,record=lit.literal(n);code+=part;examples.append(record)
    integration=(B/('integration-'+b['key']+'.lean.txt')).read_text()
    code+='\n'+re.sub(r'^import\s+[^\n]+\n','',integration,flags=re.M)+'\nend\n'
    name='Independent_'+b['key']+'_Consumer.lean';consumers[name]=code.encode()
    bindings[b['key']]={'source':name,'literal_examples':examples}
assert sum(len(x['literal_examples']) for x in bindings.values())==11
negatives={
 'SorryControl.lean':('import NLA.Proofs.RE05.GaussianMoments\n'+preamble+'\nnamespace RE05Negative\ntheorem sorryFalse : False := by sorry\nend RE05Negative\n#audit_named "RE05Negative.sorryFalse" "SorryControl" "public" "theorem"\n', 'sorry'),
 'PrivateControl.lean':('import NLA.Proofs.RE05.GaussianMoments\n'+preamble+'\nnamespace RE05Negative\nprivate axiom hiddenFalse : False\nprivate theorem privateProof : False := hiddenFalse\nend RE05Negative\n#audit_named "RE05Negative.privateProof" "PrivateControl" "private" "theorem"\n','private_axiom'),
 'TargetDefinitionControl.lean':('import NLA.Proofs.RE05.GaussianMoments\n'+preamble+'\n#audit_named "NLA.Statements.RE05.Target" "NLA.Statements.RE05" "public" "theorem"\n','kind')}
for n,(code,_) in negatives.items():consumers[n]=code.encode()
OUT=B/a.run_dir;OUT.mkdir(exist_ok=False);S=OUT/'sources';S.mkdir()
for name,data in {**frozen,**consumers}.items():
    p=S/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
for x in input_lock['source_inputs']:
    p=OUT/'preserved-inputs'/x['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((REPO/x['path']).read_bytes())
(OUT/'consumer-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
author_paths={'gaussian_moments':('gaussian-moments-author-v2/result.json','3bc892751146bbe7ee556bdb5708821d3a7dd0eddea0474c25ea26834b7eb769')}
author_receipts=[]
for key,(path,h) in author_paths.items():
    p=B.parent/path;assert sha(p)==h
    d=json.loads(p.read_text());assert d['passed'] and not d['project_objects_reused']
    author_receipts.append({'key':key,'path':str(p.relative_to(REPO)),'sha256':h,'passed':True})
def pins():
    records=[]
    for d in json.loads((LIVE/'lake-manifest.json').read_text())['packages']:
        p=CACHE/d['name'];rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()
        status=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=p,text=True)
        assert rev==d['rev'] and not status,(d['name'],rev,status)
        lib=p/'.lake/build/lib/lean'
        assert lib.is_dir() or d['name']=='Cli'
        assert not (lib/'NLA').exists() and not (lib/'Reviewed').exists()
        records.append({'name':d['name'],'url':d['url'],'revision':rev,'clean':True,'library':str(lib) if lib.is_dir() else None})
    assert len(records)==10
    return records
def originals():
    records=[]
    for x in input_lock['source_inputs']:
        assert sha(REPO/x['path'])==sha(OUT/'preserved-inputs'/x['path'])==x['sha256']
        records.append({'path':x['path'],'sha256':x['sha256'],'passed':True})
    assert len(json.loads((REPO/'problem_ids.json').read_text()))==217
    return records
def tr04():
    p=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-26/CANONICAL_PROMOTION_FREEZE_2026-10-26.json'
    assert sha(p)=='44b5df77ea7ed70c35aac6e87b2001f2b6860a36f58f1156a50d01a3c83374f7'
    d=json.loads(p.read_text());assert len(d['inputs'])==205
    assert all(sha(REPO/d['project']/n)==h for n,h in d['inputs'].items())
    return {'passed':True,'inputs':205,'freeze_sha256':sha(p)}
def execute(source,obj,env,expected):
    command=[str(LEAN),'-o',str(obj),source];obj.parent.mkdir(parents=True,exist_ok=True)
    p=subprocess.run(command,cwd=S,env=env,capture_output=True,text=True)
    name='command-'+str(len(result['commands'])).zfill(2)+'.log';log=OUT/name
    log.write_text(p.stdout+p.stderr)
    rec={'source':source,'argv':command,'expected_exit_code':expected,'exit_code':p.returncode,'log':name,'log_sha256':sha(log)}
    result['commands'].append(rec);print(source,p.returncode,flush=True)
    assert p.returncode==expected,source
    return log.read_text()
result={'passed':False,'started_utc':now(),'reviewer':'/root/recover_verification','proof_source_authorship':[],
 'scope':config['scope'],'source_lock_sha256':sha(B/'source-lock.json'),'driver_sha256':sha(Path(__file__)),
 'helper_sha256':{n:sha(B/n) for n in ['source_inventory.py','literal_type.py','audit-preamble.lean.txt']},
 'source_sha256':{n:hashlib.sha256(x).hexdigest() for n,x in frozen.items()},
 'consumer_sha256':{n:hashlib.sha256(x).hexdigest() for n,x in consumers.items()},'consumer_bindings':bindings,
 'author_receipts':author_receipts,'commands':[],'blocks':{},'negative_controls':{},
 'project_objects_reused':False,'pinned_external_package_objects_reused':True,
 'full_RE05_Target_proved':False,'probability_99of100_proved':False,'unconditional_SourceQueryBound_proved':False,
 'OriginalClaim_or_SourceCompanion_proved':False,'Linux_or_Comparator_acceptance':False}
try:
    assert sha(LEAN)=='1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
    result['compiler_binary_sha256']=sha(LEAN);result['compiler']=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
    assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in result['compiler']
    result['pins_before']=pins();result['original18_before']=originals();result['TR04_before']=tr04()
    with tempfile.TemporaryDirectory(prefix='re05-independent-',dir=a.object_parent.resolve()) as temporary:
        O=Path(temporary)
        env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(O)]+[p['library'] for p in result['pins_before'] if p['library'] is not None]),PATH=str(LEAN.parent)+os.pathsep+os.environ['PATH'])
        result['private_object_directory']=str(O);result['LEAN_PATH']=env['LEAN_PATH']
        assert not list(O.iterdir())
        for x in config['union']:
            rel=str(Path(x['path']).relative_to('lean-statements'));execute(rel,O/Path(rel).with_suffix('.olean'),env,0)
        for block in config['blocks']:
            key=block['key'];name=bindings[key]['source'];log=execute(name,O/Path(name).with_suffix('.olean'),env,0)
            kinds=re.findall(r'AUDITED_KIND (\S+) (\S+)',log);actual=re.findall(r'AUDITED_ACTUAL (\S+) (\S+) (\S+)',log)
            axs=re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',log)
            expected=[(d['audit_id'],'theorem' if d['kind'] in {'theorem','lemma'} else 'inductive' if d['kind'] in {'inductive','structure'} else 'definition') for d in block['declarations']]
            assert sorted(kinds)==sorted(expected) and sorted(actual)==sorted((d['name'],d['audit_id'],d['visibility']) for d in block['declarations'])
            assert sorted(n for n,_ in axs)==sorted(n for n,_ in expected)
            assert all({a.strip() for a in xs.split(',') if a.strip()}<=ALLOWED for _,xs in axs)
            assert 'error:' not in log and 'sorryAx' not in log
            result['blocks'][key]={'passed':True,'closure_sources':len(block['source_paths']),'explicit_named_kernel_checks':len(expected),'owned_named_declarations':sum(d['source'] in block['owned'] for d in block['declarations']),'complete_raw_theorem_types':len(bindings[key]['literal_examples']),'observed_axioms':sorted({a.strip() for _,xs in axs for a in xs.split(',') if a.strip()})}
        for name,(_,kind) in negatives.items():
            log=execute(name,O/Path(name).with_suffix('.olean'),env,1)
            assert log.count('error:')==1
            axs=re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',log)
            if kind=='kind':
                assert 'constant kind differs from frozen source' in log and not axs
            else:
                assert 'depends on sorry or unrecognized axioms' in log and len(axs)==1
                expected={'sorryAx'} if kind=='sorry' else {'_private.PrivateControl.0.RE05Negative.hiddenFalse'}
                assert {a.strip() for a in axs[0][1].split(',') if a.strip()}==expected
                if kind=='private_axiom':assert axs[0][0]=='_private.PrivateControl.0.RE05Negative.privateProof'
            result['negative_controls'][kind]={'passed':True,'expected_exit':1,'accepted_as_proof':False}
    result['private_objects_removed']=not Path(result['private_object_directory']).exists()
    result['pins_after']=pins();result['original18_after']=originals();result['TR04_after']=tr04()
    assert all(sha(REPO/x['path'])==x['sha256'] for x in config['union'])
    assert all(sha(REPO/b['author_freeze']['path'])==b['author_freeze']['sha256'] for b in config['blocks'])
    assert all(sha(S/n)==h for n,h in {**result['source_sha256'],**result['consumer_sha256']}.items())
    assert len(result['commands'])==11 and len(result['blocks'])==1 and len(result['negative_controls'])==3
    result['passed']=True
except Exception as exc:
    result['exception']=str(exc);result['traceback']=traceback.format_exc()
finally:
    result['finished_utc']=now();(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':result['passed'],'commands':len(result['commands']),'blocks':result['blocks'],'result_sha256':sha(OUT/'result.json'),'exception':result.get('exception')},indent=2))
raise SystemExit(0 if result['passed'] else 1)
