"""Independent read-only MF-16 publication integrity review.

Writes only this referee's separate evidence. Does not rerun Lean, edit any
publication wrapper, regenerate a catalog/PDF, or mutate Git state.
"""
from pathlib import Path
import collections, datetime, hashlib, json, re, shutil, subprocess
import yaml

E = Path(__file__).resolve().parent
P = E.parents[1]
W = P.parents[2]
PREFIX = 'matrix-functions-and-stability/MF-16/lean'
CANDIDATE = '4e24448897a088ca9e7458379add1014c5d11e0c'
BASE = '5830ed4fb06da0659414a3deb2a40ad327aca052'
PUB = P / 'verification/publication-2026-09-12'
OPS = P / 'verification/linux-2026-09-12'
ROOT = P / 'verification/root-operational-2026-09-12'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
digest = lambda raw: hashlib.sha256(raw).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=W)
load = lambda p: json.loads(Path(p).read_text())
known = {
    PUB / 'PUBLICATION-HANDOFF.md': '54ac181f8841c711321af7a5acebe8de5a19c6cf400f7ad434954f144d329e57',
    PUB / 'INTEGRITY-CHECKS.json': 'e710b17d8b9dd6aea9514b0070525b0588167dbc1a00fbb6d1dfd6f49dacc223',
    PUB / 'EVIDENCE-MANIFEST.json': '602c7b7a3c2dd65fd22b81d0cd710ae8ba7ae196bed7f398df0d49d8093df818',
    OPS / 'OPERATIONAL-REVIEW.md': 'e348886719fab4d2dca6aeba02d711d938f22b97c9529c6e91a2e70f086bf960',
    OPS / 'EVIDENCE-MANIFEST.json': 'b8661c4f497acc280bfccdd78e99d06049dc6fc854f09c227b67e65f39eb350a',
    ROOT / 'ROOT-CHECKS.json': 'a09d923c1406601f672aeb6ae5e64eeac1a639a64e77b06489741a3c3523d684',
    P / 'reviews/proof-referee-2.md': '73f5058b627108a37f0f1ff120d6c984e2baf9183b93a7e7d1ea805d9e35933a',
}
for p, h in known.items():
    assert sha(p) == h, p
assert git('rev-parse','HEAD').decode().strip() == CANDIDATE
assert git('show','-s','--format=%an%n%ae%n%cn%n%ce',CANDIDATE).decode().splitlines() == ['George Stepaniants','','George Stepaniants','']

inventory_counts = {}
for d in [PUB, OPS, ROOT]:
    outer = d / 'EVIDENCE-MANIFEST.json'
    manifest = load(outer)
    actual = {str(p.relative_to(d)) for p in d.rglob('*') if p.is_file() and p != outer}
    assert actual == set(manifest['files']), d
    for name, row in manifest['files'].items():
        assert sha(d / name) == row['sha256'], name
        if 'bytes' in row:
            assert (d / name).stat().st_size == row['bytes']
    inventory_counts[str(d.relative_to(P))] = {'bound':len(actual),'including_outer':len(actual)+1,
        'outer_sha256':sha(outer), 'nested_manifests_preserved':sum(Path(n).name=='EVIDENCE-MANIFEST.json' for n in actual)}
assert inventory_counts[str(OPS.relative_to(P))]['including_outer'] == 467
assert inventory_counts[str(ROOT.relative_to(P))]['including_outer'] == 7
assert inventory_counts[str(PUB.relative_to(P))]['including_outer'] == 34

paths = git('ls-tree','-r','--name-only',CANDIDATE,PREFIX).decode().splitlines()
assert len(paths) == 294
candidate_records = {}
archive_map = {'README.md':'archive/README.linux-candidate.md',
               'formalization.yaml':'archive/formalization.linux-candidate.yaml'}
for name in paths:
    rel = name[len(PREFIX)+1:]
    raw = git('show',CANDIDATE+':'+name)
    saved = OPS / 'source' / name
    assert saved.read_bytes() == raw, name
    current = PUB / archive_map[rel] if rel in archive_map else P / rel
    assert current.read_bytes() == raw, rel
    candidate_records[rel] = {'sha256':digest(raw),'git_blob':git('rev-parse',CANDIDATE+':'+name).decode().strip(),
                               'current_exact_location':str(current.relative_to(P))}
assert set(load(PUB/'before.json')['project_inputs']) == set(candidate_records)
for rel, data in candidate_records.items():
    assert load(PUB/'before.json')['project_inputs'][rel] == data['sha256']
frozen_records = {}
for fn in ['verification/proof-freeze.json','reviews/statement-freeze.json']:
    f = load(P/fn)
    for name, expected in f['files'].items():
        actual = P/'verification/pre-candidate-README.md' if name=='README.md' else P/name
        assert sha(actual) == expected, (fn,name)
    frozen_records[fn] = {'sha256':sha(P/fn),'preserved_files':len(f['files']),
                         'historical_README_mapping':'verification/pre-candidate-README.md'}
    for name, expected in f['source_files'].items():
        raw = git('show',f['base']+':'+name)
        assert digest(raw) == expected
        assert (OPS/'source'/name).read_bytes() == raw, name
assert frozen_records['verification/proof-freeze.json']['preserved_files']==182
assert frozen_records['reviews/statement-freeze.json']['preserved_files']==45

def changed(a,b,prefix=''):
    if isinstance(a,dict) and isinstance(b,dict):
        out=[]
        for k in sorted(set(a)|set(b)):
            p=(prefix+'.' if prefix else '')+str(k)
            if k not in a or k not in b: out.append(p)
            else: out+=changed(a[k],b[k],p)
        return out
    return [] if a==b else [prefix]
before_y=yaml.safe_load((PUB/archive_map['formalization.yaml']).read_text())
after_y=yaml.safe_load((P/'formalization.yaml').read_text())
fields=changed(before_y,after_y)
assert set(fields)=={'status.scope','review.status','review.notes','review.linux_verification.status','review.linux_verification.note'},fields
cfg=load(P/'comparator.json')
assert len(cfg['theorem_names'])==9 and cfg['definition_names']==[]
assert [d['declaration'] for d in after_y['status']['main_results']]==cfg['theorem_names']
assert all(d['sorry_count']==0 for d in after_y['status']['main_results'])
assert after_y['status']['sorry_count']==0 and after_y['status']['sorry_in_definitions']==0
assert set(after_y['status']['axioms'])=={'propext','Classical.choice','Quot.sound'}
assert after_y['project']['authors']==['George Stepaniants']
aff='Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
assert after_y['project']['affiliations']['George Stepaniants']==aff

expected={'CATALOG.md','README.md','RESOLVED.md','matrix-functions-and-stability/README.md',
          'matrix-functions-and-stability/MF-16/README.md','matrix-functions-and-stability/MF-16/problem.pdf',
          'matrix-functions-and-stability/MF-16/problem.tex',PREFIX+'/README.md',PREFIX+'/formalization.yaml'}
assert set(git('diff','--name-only',CANDIDATE).decode().splitlines())==expected
publication_hashes={name:sha(W/name) for name in sorted(expected)}
assert publication_hashes==load(PUB/'INTEGRITY-CHECKS.json')['publication_files']
registry=json.loads(git('show',BASE+':problem_ids.json'))
assert len(registry)==217 and (W/'problem_ids.json').read_bytes()==git('show',BASE+':problem_ids.json')
other=0;counts=collections.Counter()
for pid,name in registry.items():
    raw=(W/name).read_bytes();text=raw.decode()
    counts[re.search(r'\*\*Status:\*\*\s*([^\n]+)',text).group(1).strip()]+=1
    if pid!='MF-16':assert raw==git('show',BASE+':'+name),name;other+=1
canon=registry['MF-16'];old=git('show',BASE+':'+canon)
marker=b'## Problem statement'
assert (W/canon).read_bytes().split(marker,1)[1]==old.split(marker,1)[1]
resolved_before=git('show',BASE+':RESOLVED.md').decode();resolved_after=(W/'RESOLVED.md').read_text()
def without_mf16(text):
    a=text.index('**MF-16 (');b=text.index('\n\n**MF-18 (',a)
    return text[:a]+'<MF16_REVIEWED_PARAGRAPH>'+text[b:]
assert without_mf16(resolved_before)==without_mf16(resolved_after)
assert dict(counts)=={'Solved':75,'Open':53,'Partially resolved':72,'Lean verified':17}
added='\n'.join(l[1:] for l in git('diff','--unified=0',CANDIDATE).decode(errors='replace').splitlines()
                if l.startswith('+') and not l.startswith('+++'))
assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}',added)

# Independent examination of the retained actual run identity and acceptance.
run=load(ROOT/'observed-run.json');jobs=load(ROOT/'observed-jobs.json')['jobs']
assert run['id']==34735259429 and run['head_sha']==CANDIDATE
assert run['status']=='completed' and run['conclusion']=='success' and len(jobs)==17
assert all(j['conclusion']=='success' and all(s['conclusion']=='success' for s in j['steps']) for j in jobs)
actual=list((OPS/'artifacts/lean-MF-16').rglob('result.json'))
assert len(actual)==1
receipt=load(actual[0]);(E/'actual-project-receipt.json').write_bytes(actual[0].read_bytes())
comparator=actual[0].parent/'comparator.log'
raw_log=comparator.read_text()
assert 'Lean default kernel accepts the solution' in raw_log and 'Your solution is okay!' in raw_log
axiom_reports=re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",raw_log,re.S)
assert len(axiom_reports)==22
assert all({a.strip() for a in aa.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,aa in axiom_reports)
for name in cfg['theorem_names']:
    assert raw_log.count(name)>=2,name

visual=load(PUB/'VISUAL-REVIEW.json')
pdf=W/'matrix-functions-and-stability/MF-16/problem.pdf';tex=pdf.with_suffix('.tex')
assert sha(pdf)==visual['pdf_sha256']=='411cc22773e3049a69cb4d86986a7a363c535ac2333dbe8745c6576b034864c4'
assert sha(tex)==visual['tex_sha256']=='a3041f7db2a5ac0daf031537e395817af7ebe42161bd4fc11eaa74a47a4728a9'
images={}
for n in [1,2,3]:
    image=Path('/tmp/nla-lean-formalization/mf16-publication-pages')/f'page-{n}.png'
    assert sha(image)==visual['images'][image.name]
    (E/'pages').mkdir(exist_ok=True)
    shutil.copyfile(image,E/'pages'/image.name)
    images[image.name]=sha(image)
for row in load(PUB/'checks.json'):
    assert row['exit_code']==0 and sha(PUB/row['log'])==row['log_sha256']
assert 'Ran 17 tests' in (PUB/'permanent-id-tests.log').read_text()
for name in ['permanent-ids-origin.log','permanent-ids-upstream.log','manifest.log','format-check.log','render.log','pdfinfo.log']:
    (E/name).write_bytes((PUB/name).read_bytes())
(E/'candidate-input-checks.json').write_text(json.dumps(candidate_records,indent=2)+'\n')
(E/'publication-diff.patch').write_bytes(git('diff',CANDIDATE))
result={'verdict':'PASS independent publication integrity review; semantic and actual visual findings in adjacent report',
        'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/formal_review_standards',
        'role':'Independent publication reviewer and prior independent final mathematical referee 2; not publication preparer, no extra mathematical approval',
        'candidate':CANDIDATE,'base':BASE,'candidate_inputs':294,'preserved_nonwrapper_inputs':292,
        'exact_candidate_wrappers_archived':2,'changed_yaml_fields':fields,'frozen_inputs':frozen_records,
        'original_Git_sources':14,'complete_inventories':inventory_counts,'other_canonical_pages_preserved':other,
        'permanent_registry_entries':217,'original_target_suffix_preserved':True,
        'only_MF16_RESOLVED_paragraph_changed':True,'status_counts':dict(counts),
        'publication_files':publication_hashes,'actual_run':run['id'],'all_actual_jobs_and_steps_pass':17,
        'actual_comparator_log_sha256':sha(comparator),'embedded_standard_three_reports':22,
        'nine_export_names':cfg['theorem_names'],'definition_exceptions':[],
        'pdf_pages_actually_displayed_and_reviewed':[1,2,3],'retained_displayed_pngs':images,
        'new_mathematical_compile_or_Linux_run':False,'canonical_or_wrapper_edit':False,
        'Git_mutation_or_publication':False,'George_email_on_new_lines':False}
(E/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','candidate_inputs':294,'nonwrapper_inputs':292,'operational_files':474,
                  'frozen_proof_inputs':182,'frozen_statement_inputs':45,'all_three_PDF_pages':True,
                  'CHECKS_sha256':sha(E/'CHECKS.json')},indent=2))
