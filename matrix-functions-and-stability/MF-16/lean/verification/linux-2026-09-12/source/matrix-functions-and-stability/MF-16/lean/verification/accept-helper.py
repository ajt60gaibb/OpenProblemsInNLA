"""Implementation integration acknowledgement; not an independent review."""
from pathlib import Path
import hashlib,json,datetime
P=Path(__file__).resolve().parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
D=P/'verification/cayley-hamilton-development'
assert sha(P/'NLA/MF16/CayleyHamilton.lean')=='d6d2a419467df881998175e8d06ab13a49ea4ed86f805eefb56ab90284350df7'
assert sha(D/'handoff.json')=='6f1a73d566bd0bf78a9af1cdba234b8046ff93f1b9b3a3b72e73e049f60659e2'
M=D/'EVIDENCE-MANIFEST.json';assert sha(M)=='6f8f08fef606b30229a5ef398b12a3c79bcdd93a59a22356b9672b9d8d271209'
j=json.loads(M.read_text())
for rel,row in j['files'].items():
 q=D/rel;assert sha(q)==row['sha256'] and q.stat().st_size==row['bytes']
actual={str(q.relative_to(D)) for q in D.rglob('*') if q.is_file() and q!=M}
assert actual==set(j['files']) and len(actual)==9
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'result':'PASS full helper/read-source/exact identity integration check before import','helper_sha256':sha(P/'NLA/MF16/CayleyHamilton.lean'),'handoff_sha256':sha(D/'handoff.json'),'complete_helper_evidence_manifest_sha256':sha(M),'source_read_in_full':True,'actual_route':'Polynomial remainder plus Matrix.aeval_self_charpoly/charpoly_fin_two; genuine matrix power, no diagonalization assumption.','implementation_coauthors':['/root/leancert_examples','/root/solved_statement_inventory'],'not_an_independent_final_review':True,'helper_source_edits':False}
(P/'verification/helper-accepted.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS exact nine-file helper evidence and source; authorized integration only')
