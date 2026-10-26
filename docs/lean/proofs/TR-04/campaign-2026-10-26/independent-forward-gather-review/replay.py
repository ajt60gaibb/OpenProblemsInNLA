#!/usr/bin/env python3
"""Independent actual candidate gather and forward phases fresh kernel replay; only evidence files are written."""
from pathlib import Path
from datetime import datetime, timezone
from zoneinfo import ZoneInfo
import argparse, hashlib, json, os, re, subprocess, tempfile
from source_inventory import without_comments, declarations_of
BASE=Path(__file__).resolve().parent
REPO=BASE.parents[5]
PROJECT=REPO/'lean-statements'
LEAN=REPO.parent/'tooling/lean-4.33.1-darwin_aarch64/bin/lean'
PACKAGES=(PROJECT/'.lake/packages').resolve()
PROOF_BASE='2b049df5e9b15318987f3fa592b1a7c65a0c0057'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(data):return hashlib.sha256(data).hexdigest()
def run(argv,**kw):
 p=subprocess.run(list(map(str,argv)),text=True,capture_output=True,**kw)
 return {'argv':list(map(str,argv)),'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
def timestamp():return datetime.now(timezone.utc).isoformat()
def dependencies():
 records=[]
 for item in json.loads((PROJECT/'lake-manifest.json').read_text())['packages']:
  directory=PACKAGES/item['name'];head=run(['git','-C',directory,'rev-parse','HEAD']);status=run(['git','-C',directory,'status','--porcelain','--untracked-files=no'])
  records.append({'name':item['name'],'expected_revision':item['rev'],'directory':str(directory),'head':head,'status':status,'passed':head['exit_code']==status['exit_code']==0 and head['stdout'].strip()==item['rev'] and not status['stdout'].strip()})
 assert len(records)==10 and all(r['passed'] for r in records),'Ten exact clean dependency pins required'
 return records
preserved=json.loads((REPO/'docs/lean/proofs/TR-04/campaign-2026-10-23/geometry-input-preservation-result.json').read_text())['locked_original_model_review_inputs']
assert len(preserved)==25
def originals():
 records=[]
 for item in preserved:
  path=item['path'];data=(REPO/path).read_bytes();old=subprocess.check_output(['git','show',f'{PROOF_BASE}:{path}'],cwd=REPO)
  records.append({'path':path,'sha256':sha(data),'base_sha256':sha(old),'passed':data==old})
 assert all(r['passed'] for r in records),'Original25 changed'
 return records
config=json.loads((BASE/'source-lock.json').read_text())
for b in config['blocks']:
 assert sha((REPO/b['author_lock_path']).read_bytes())==b['author_lock_sha256']
for r in config['union']:assert sha((REPO/r['path']).read_bytes())==r['sha256'],r['path']
expected={r['path'].removeprefix('lean-statements/'):r for r in config['union']}
frozen={};visiting=set()
def freeze(module):
 name=module.replace('.','/')+'.lean'
 if name in frozen:return
 assert name not in visiting,'Local import cycle'
 visiting.add(name);data=(PROJECT/name).read_bytes();clean=without_comments(data.decode())
 for line in clean.splitlines():
  match=re.fullmatch(r'\s*import\s+([A-Za-z0-9_.]+)\s*',line)
  if match and (PROJECT/(match[1].replace('.','/')+'.lean')).is_file():freeze(match[1])
 lexical=re.sub(r'"(?:\\.|[^"\\])*"','""',clean)
 assert not re.search(r'\b(sorry|admit|axiom|implemented_by|unsafe)\b|trustCompiler|debug\.skipKernelTC',lexical),('Trust construct',name)
 assert name in expected and sha(data)==expected[name]['sha256'],('Unexpected or changed source',name)
 frozen[name]=data;visiting.remove(name)
for b in config['blocks']:
 for m in b['roots']:freeze(m)
assert set(frozen)==set(expected) and len(frozen)==len(config['union'])
all_declarations=[d for n,data in frozen.items() for d in declarations_of(n,data)]
assert all(d['visibility'] in {'public','private','local'} for d in all_declarations)
for d in all_declarations:
 if d['visibility']=='private':
  p=config['private_name_map'][d['name']];assert p['source']==d['source'] and p['line']==d['line'] and p['kind']==d['kind']
assert sha((BASE/'private-name-provenance.json').read_bytes())==config['private_name_provenance_sha256']
assert all(d['kind'] in {'theorem','lemma','def','abbrev','instance','inductive','structure'} for d in all_declarations)
assert len({d['name'] for d in all_declarations})==len(all_declarations)
lookup={d['name']:d for d in all_declarations}

def literal(name):
 d=lookup[name];text=without_comments(frozen[d['source']].decode());start=sum(len(x)+1 for x in text.splitlines()[:d['line']-1]);tail=text[start:]
 match=re.match(r'\s*(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.\']*)',tail)
 assert match,(name,d)
 declaration=match[1];prefix=name.removesuffix('.'+declaration);assert prefix!=name
 body=tail[match.end():];stack=[];header=None;pending_top_level_lets=0
 for i,c in enumerate(body):
  if c in '({[':stack.append(c)
  elif c in ')}]':
   assert stack
   stack.pop()
  elif not stack and re.match(r'let\b',body[i:]) and (i==0 or not re.match(r"[\w']",body[i-1])):
   pending_top_level_lets+=1
  elif body[i:i+2]==':=' and not stack:
   if pending_top_level_lets:
    pending_top_level_lets-=1
   else:
    header=body[:i].rstrip();break
 assert header is not None,name
 rest=header.lstrip();args=[]
 while rest and rest[0] in '({[':
  opener=rest[0];closer={'(':')','{':'}','[':']'}[opener];depth=0
  for i,c in enumerate(rest):
   if c==opener:depth+=1
   elif c==closer:
    depth-=1
    if depth==0:break
  group=rest[1:i]
  if ':' in group:
   names=group.split(':',1)[0].strip().split();assert all(re.fullmatch(r"[^\W\d][\w']*",n) and n!='_' for n in names),(name,group)
   args.extend(names)
  else:
   assert opener=='[',(name,group)
   args.append('(inferInstance)')
  rest=rest[i+1:].lstrip()
 assert rest.startswith(':'),(name,rest[:100])
 source_opens=[line for line in text.splitlines() if line.startswith('open ') and not line.startswith('open scoped ')]
 code=f'namespace {prefix}\n'+'\n'.join(source_opens)+f'\nexample{header} := by\n  exact @{name} '+ ' '.join(args)+f'\nend {prefix}\n'
 return code,{'name':name,'source':d['source'],'line':d['line'],'verbatim_header_sha256':sha(header.encode()),'application_arguments':args}

preamble='''
set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#audit_named " user:str modName:str visibility:str expected:str : command => do
  unless visibility.getString == "public" || visibility.getString == "private" || visibility.getString == "local" do
    throwErrorAt visibility "unsupported visibility"
  let decl := if visibility.getString == "private" then
    Lean.mkPrivateNameCore modName.getString.toName user.getString.toName
    else user.getString.toName
  let some info := (← getEnv).find? decl | throwErrorAt user "missing exact compiler constant {decl}"
  match expected.getString, info with
  | "theorem", .thmInfo _ => pure ()
  | "definition", .defnInfo _ => pure ()
  | "inductive", .inductInfo _ => pure ()
  | _, _ => throwErrorAt user "constant kind differs from frozen source"
  logInfo m!"AUDITED_KIND {user.getString} {expected.getString}"
  logInfo m!"AUDITED_ACTUAL {user.getString} {decl.toString} {visibility.getString}"
  elabCommand (← `(#assert_trust $(mkIdent `kernel) $(mkIdent decl)))
  elabCommand (← `(#print axioms $(mkIdent decl)))
  let axs ← liftCoreM <| collectAxioms decl
  let body := String.intercalate "," (axs.toList.map Name.toString)
  logInfo m!"AUDITED_AXIOMS {user.getString} [{body}]"
'''
consumers={};consumer_info={}
for b in config['blocks']:
 text='\n'.join('import '+m for m in b['roots'])+'\n'+preamble
 for d in b['declarations']:
  kind='theorem' if d['kind'] in {'theorem','lemma'} or d['name'] in {'NLA.Proofs.TR04.squaredErrorProgram_nonzero_realRegisters','NLA.Proofs.TR04.thresholdScanProgram_nonzero_reals','NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters','NLA.Proofs.TR04.ttStartup_nonzero_realRegisters','NLA.Proofs.TR04.ttMetadata_nonzero_realRegisters','NLA.Proofs.TR04.ttFirstSelection_nonzero_reals','NLA.Proofs.TR04.ttInitScalar_nonzero_reals'} else 'inductive' if d['kind'] in {'inductive','structure'} else 'definition'
  module=d['source'].removesuffix('.lean').replace('/','.')
  text+=f'#audit_named {json.dumps(d["name"])} {json.dumps(module)} {json.dumps(d["visibility"])} {json.dumps(kind)}\n'
 text+='\nnoncomputable section\nopen scoped BigOperators Matrix\nopen NLA.Computation.SVDMachine\n'
 for local_decl in b['declarations']:
  if local_decl['visibility']=='local' and local_decl['kind']=='instance':text+=f"attribute [local instance] {local_decl['name']}\n"
 examples=[]
 for name in b['literal_endpoints']:
  code,record=literal(name);text+=code;examples.append(record)
 text+=(BASE/('integration-'+b['key']+'.lean.txt')).read_text()+'\n'
 text+='end\n'
 name='Independent_'+b['key']+'_Consumer.lean';consumers[name]=text.encode();consumer_info[b['key']]={'source':name,'literal_examples':examples}
parser=argparse.ArgumentParser();parser.add_argument('--run-dir',default='run-attempt-1');args=parser.parse_args()
EVIDENCE=BASE/args.run_dir;EVIDENCE.mkdir(exist_ok=False)
for name,data in {**frozen,**consumers}.items():
 p=EVIDENCE/'sources'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
(EVIDENCE/'consumer-bindings.json').write_text(json.dumps(consumer_info,indent=2)+'\n')
result={'started_utc':timestamp(),'started_local':datetime.now(ZoneInfo('America/New_York')).isoformat(),'scope':config['scope'],'reviewer':config['reviewer'],'self_authored_proof_sources':[],'source_lock_sha256':sha((BASE/'source-lock.json').read_bytes()),'driver_sha256':sha(Path(__file__).read_bytes()),'inventory_sha256':sha((BASE/'source_inventory.py').read_bytes()),'project_sources':len(frozen),'source_sha256':{n:sha(d) for n,d in frozen.items()},'consumer_sha256':{n:sha(d) for n,d in consumers.items()},'consumer_bindings':consumer_info,'declarations':all_declarations,'private_or_local_named_declarations':[d for d in all_declarations if d['visibility']!='public'],'private_name_provenance_sha256':config['private_name_provenance_sha256'],'lean_version':run([LEAN,'--version']),'lean_sha256':sha(LEAN.read_bytes()),'dependencies_before':dependencies(),'original25_before':originals(),'project_objects_reused':False,'pinned_external_dependency_objects_reused':True,'fresh_closure_build_shared_by_blocks':True,'commands':[],'blocks':{},'full_TR04_Target_proved':False,'authoritative_Linux_Comparator':False}
try:
 with tempfile.TemporaryDirectory(prefix='objects-',dir=BASE) as temporary:
  fresh=Path(temporary);source=fresh/'source';output=fresh/'output';output.mkdir()
  for name,data in {**frozen,**consumers}.items():
   p=source/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
  libraries=[p/'.lake/build/lib/lean' for p in sorted(PACKAGES.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
  env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[output,*libraries,LEAN.parent.parent/'lib/lean'])))
  result['LEAN_PATH']=env['LEAN_PATH']
  build_order=[]
  for block in config['blocks']:
   wanted={r['path'].removeprefix('lean-statements/') for r in block['records']}
   build_order.extend(n for n in frozen if n in wanted and n not in build_order)
   build_order.append(consumer_info[block['key']]['source'])
  assert len(build_order)==len(frozen)+len(consumers) and len(set(build_order))==len(frozen)+len(consumers)
  for name in build_order:
   target=output/Path(name).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
   command=run([LEAN,'-R',source,'-o',target,source/name],cwd=source,env=env,timeout=300)
   log=command.pop('stdout')+command.pop('stderr');logfile=name.replace('/','-')+'.log';(EVIDENCE/logfile).write_text(log)
   command.update(source=name,log=logfile,log_sha256=sha(log.encode()))
   result['commands'].append(command)
   print(f'{len(result["commands"]):02d}/{len(frozen)+len(consumers)} {name}: {command["exit_code"]}',flush=True)
   if command['exit_code']:break
except Exception as error:result['exception']=repr(error)
result['dependencies_after']=dependencies();result['original25_after']=originals()
result['source_unchanged_after']={n:(PROJECT/n).read_bytes()==data for n,data in frozen.items()}
result['author_locks_unchanged_after']={b['key']:sha((REPO/b['author_lock_path']).read_bytes())==b['author_lock_sha256'] for b in config['blocks']}
commands={c['source']:c for c in result['commands']}
for b in config['blocks']:
 info=consumer_info[b['key']];consumer=commands.get(info['source']);log=(EVIDENCE/consumer['log']).read_text() if consumer else ''
 kinds=re.findall(r'AUDITED_KIND (\S+) (\S+)',log)
 axiom_records=re.findall(r'AUDITED_AXIOMS (\S+) \[([^\]]*)\]',log)
 observed=sorted({a.strip() for _,body in axiom_records for a in body.split(',') if a.strip()})
 names=[n for n,_ in axiom_records];expected_names=[d['name'] for d in b['declarations']]
 actual_bindings=re.findall(r'AUDITED_ACTUAL (\S+) (\S+) (\S+)',log)
 expected_bindings=[(d['name'],config['private_name_map'][d['name']]['actual_kernel_name'] if d['visibility']=='private' else d['name'],d['visibility']) for d in b['declarations']]
 bindings_passed=sorted(actual_bindings)==sorted(expected_bindings)
 sources=[r['path'].removeprefix('lean-statements/') for r in b['records']]
 bresult={'author':b['author'],'source_lock_sha256':b['author_lock_sha256'],'project_closure_count':len(sources),'owned_source_count':len(b['owned']),'owned_declarations':b['owned_declarations'],'explicit_named_declarations':len(expected_names),'theorem_kinds':sum(d['kind'] in {'theorem','lemma'} for d in b['declarations']),'owned_theorem_kinds':sum(d['name'] in b['owned_declarations'] and d['kind'] in {'theorem','lemma'} for d in b['declarations']),'literal_examples':len(info['literal_examples']),'consumer':consumer,'kind_check_count':len(kinds),'actual_kernel_theorem_count':sum(kind=='theorem' for _,kind in kinds),'actual_owned_kernel_theorem_count':sum(kind=='theorem' and name in b['owned_declarations'] for name,kind in kinds),'axiom_report_count':len(names),'observed_axioms':observed,'all_named_declaration_checks_passed':sorted(names)==sorted(expected_names) and sorted(n for n,_ in kinds)==sorted(expected_names) and bindings_passed,'actual_name_bindings':[{'source_name':n,'actual_kernel_name':a,'visibility':v} for n,a,v in actual_bindings],'actual_name_bindings_passed':bindings_passed,'fresh_closure_command_indices':[i for i,c in enumerate(result['commands']) if c['source'] in sources],'source_unchanged_after':all(result['source_unchanged_after'][n] for n in sources),'private_or_local_named_declarations':[d for d in b['declarations'] if d['visibility']!='public'],'author_selected_public_declarations':b['author_selected_public_declarations']}
 bresult['passed']=bool(consumer and consumer['exit_code']==0 and all(n in commands and commands[n]['exit_code']==0 for n in sources) and bresult['all_named_declaration_checks_passed'] and set(observed)<=ALLOWED and bresult['source_unchanged_after'] and result['author_locks_unchanged_after'][b['key']] and 'exception' not in result)
 result['blocks'][b['key']]=bresult
result['passed']=all(b['passed'] for b in result['blocks'].values()) and len(result['commands'])==len(frozen)+len(consumers) and all(c['exit_code']==0 for c in result['commands'])
result['finished_utc']=timestamp();(EVIDENCE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'passed':result['passed'],'commands':len(result['commands']),'project_sources':len(frozen),'explicit_named_declarations':len(all_declarations),'blocks':{k:{x:v[x] for x in ['passed','explicit_named_declarations','owned_theorem_kinds','literal_examples','observed_axioms']} for k,v in result['blocks'].items()},'exception':result.get('exception')},indent=2))
raise SystemExit(0 if result['passed'] else 1)
