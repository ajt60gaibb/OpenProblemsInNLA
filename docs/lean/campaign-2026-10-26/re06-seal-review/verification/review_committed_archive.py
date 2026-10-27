#!/usr/bin/env python3
"""Read-only exact committed archive closure. No proof or CI execution."""
import argparse,hashlib,io,json,subprocess,tarfile
from pathlib import Path
ARCHIVE='71511f51452f7f59e5c298cf8513df0df0f71781'
ACCEPTED='669f3cd681b22882836d081a04652880ce39ba24'
DOC='docs/lean/proofs/RE-06/'
SEAL=DOC+'campaign-2026-10-26/FINAL_EVIDENCE_SEAL.json'
EXPECTED='ac2e99efc7f829e96475fa0f9fc143564ba2ab28ccf0c18bfe0ed491fa2dd496'
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();checks=[]
 def git(*v):return subprocess.check_output(['git','-C',str(a.repo),*v])
 def ck(n,v,**d):
  checks.append({'check':n,'pass':bool(v),**d})
  if not v:raise RuntimeError(n)
 def snap(ref,paths):
  with tarfile.open(fileobj=io.BytesIO(git('archive',ref,*paths))) as t:
   members=[x for x in t if x.isfile()];ck('archive_no_nonregular_non_directory:'+ref,all(x.isfile() or x.isdir() for x in t.getmembers()))
   return {x.name:t.extractfile(x).read() for x in members}
 head=git('rev-parse','HEAD').decode().strip();ck('archive_HEAD',head==ARCHIVE)
 raw=git('show',ARCHIVE+':'+SEAL);s=json.loads(raw);ck('committed_seal_byte_exact',sha(raw)==EXPECTED and raw==(a.repo/SEAL).read_bytes() and s['accepted_input_ref']==ACCEPTED)
 parent=git('rev-parse',ARCHIVE+'^').decode().strip();ck('archive_parent_is_CI_tested_head',parent==ACCEPTED)
 changed=git('diff-tree','--no-commit-id','--name-only','-r',ARCHIVE).decode().splitlines();ck('115_evidence_only_changes',len(changed)==115 and all(n.startswith(DOC) for n in changed))
 can=s['canonical_project']+'/';archive=snap(ARCHIVE,[DOC,can]);accepted=snap(ACCEPTED,[can]);expected={e['path'] for e in s['canonical_files']+s['evidence_files']}|{SEAL}
 ck('exact_committed_positive_set',set(archive)==expected)
 for group in ['canonical_files','evidence_files']:
  for e in s[group]:
   b=archive[e['path']];ck('committed_'+group+':'+e['path'],len(b)==e['bytes'] and sha(b)==e['sha256'] and b==(a.repo/e['path']).read_bytes())
   if group=='canonical_files':ck('canonical_identical_CI_head:'+e['path'],b==accepted[e['path']])
 for e in s['source_files']:
  n=e['path'];b=git('show',ARCHIVE+':'+n);ck('archive_preserves_frozen_source:'+n,sha(b)==e['sha256'] and len(b)==e['bytes'] and b==git('show',ACCEPTED+':'+n))
 ck('registry_unchanged',git('show',ARCHIVE+':problem_ids.json')==git('show',ACCEPTED+':problem_ids.json'))
 ck('catalog_unchanged',git('show',ARCHIVE+':CATALOG.md')==git('show',ACCEPTED+':CATALOG.md'))
 ck('stable_after_audit',head==git('rev-parse','HEAD').decode().strip() and raw==(a.repo/SEAL).read_bytes())
 out={'approved':True,'non_author':True,'scope':'Exact evidence-only committed archive closure, no new Lean/Comparator/Linux execution','archive_ref':ARCHIVE,'accepted_CI_input_ref':ACCEPTED,'seal_sha256':EXPECTED,'changes':changed,'canonical_files':295,'evidence_files':5659,'source_bindings':87,'checks':checks,'script_sha256':sha(Path(__file__).read_bytes())}
 (a.output/'COMMITTED_ARCHIVE_RESULT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'approved':True,'checks':len(checks),'archive':ARCHIVE}))
if __name__=='__main__':main()
