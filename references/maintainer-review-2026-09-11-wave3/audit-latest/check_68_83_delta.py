"""Read-only verification of PR68/83 rebased heads from immutable git objects."""
import collections
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPO = '/private/tmp/nla-aa01-reconciliation-20260911'
OUT = Path(__file__).parent
MAIN = '87366c62d3b5c47d170f747b1cb40ab38d501013'
REFS = {68: ('2a1a0b39992bbd5654e7bdf9f869e21a6cee0d71', '24ea75aa75b44b280c7aa0a342ea900f0fdd7be4'),
        83: ('eadd702330dfdc56de30e429d4fb08340c66eafb', '9b35b5e246989843cd67b2fed702216ea1f0acdb')}
def git(*args):
    return subprocess.check_output(['git', '-C', REPO, *args])
def blob(ref, path):
    return git('show', ref+':'+path)
def tree(ref):
    return {x.split(b'\t', 1)[1].decode(): x.split(b'\t', 1)[0].decode()
            for x in git('ls-tree', '-rz', ref).split(b'\0') if x}
mt = tree(MAIN)
reg_bytes = blob(MAIN, 'problem_ids.json')
registry = json.loads(reg_bytes)
assert len(registry) == 203
results = {}
for pr, (old,new) in REFS.items():
    ot, nt = tree(old), tree(new)
    assert git('show','-s','--format=%P',new).decode().split() == [old,MAIN]
    base = git('merge-base',old,MAIN).decode().strip()
    owned_paths = set(git('diff','--name-only',base,old).decode().splitlines()) | set(git('diff','--name-only',MAIN,new).decode().splitlines())
    unexpected = [p for p in mt if p not in owned_paths and mt[p] != nt.get(p)]
    assert not unexpected
    assert blob(new,'problem_ids.json') == reg_bytes == blob(old,'problem_ids.json')
    changed = sorted(p for p in owned_paths if ot.get(p) != nt.get(p))
    protected = [p for p in owned_paths if p in ot and (re.search(r'/solution\.(?:md|tex|pdf)$',p) or '/manuscripts/' in p or '/original-manuscripts/' in p or '/verification/reviews/' in p or p.endswith('original-agent-draft.md') or p.endswith('_witnesses.py'))]
    assert all(ot[p] == nt[p] for p in protected)
    counts = collections.Counter()
    for ident,path in registry.items():
        text = blob(new,path).decode()
        status = re.search(r'^\*\*Status:\*\*\s*([^\n]+)',text,re.M).group(1).strip()
        counts[status] += 1
    if pr == 68:
        prefix = 'references/stepaniants-2026-09-11/'
        record = json.loads(blob(new,prefix+'verification/main-integration-2026-09-11-87366c6.json'))
        assert record['prior_head']==old and record['incoming_commit']==MAIN
        for p,v in record['original_proof_and_reference_hashes'].items():
            data = blob(old,p)
            assert hashlib.sha256(data).hexdigest()==v['sha256'] and len(data)==v['bytes']
            if p==prefix+'README.md': assert blob(new,p).startswith(data)
            else: assert data==blob(new,p)
        for p,v in record['current_files'].items():
            data=blob(new,p)
            assert hashlib.sha256(data).hexdigest()==v['sha256'] and len(data)==v['bytes']
        evidence=[p for p in mt if p.startswith('references/') or re.search(r'/solution\.(md|tex|pdf)$',p)]
        assert len(evidence)==1260
        assert all(mt[p]==nt[p] for p in evidence)
        others=[p for i,p in registry.items() if i not in {'AA-01','MD-03','MD-04'}]
        assert len(others)==200 and all(mt[p]==nt[p] for p in others)
        p=registry['AA-01'];before=blob(old,p);after=blob(new,p);main=blob(MAIN,p)
        marker=b'## Problem statement\n'
        assert before[before.index(marker):]==after[after.index(marker):]
        start=b'<!-- colbrook-arithmetic -->';end=b'<!-- /colbrook-arithmetic -->'
        block=main[main.index(start):main.index(end)+len(end)]
        assert block in after
        old_notice=before.split(b'## Resolution ',1)[1].split(b'\n',1)[1].split(marker,1)[0].strip()
        assert old_notice in after
        assert counts=={'Open':67,'Partially resolved':73,'Solution claimed':1,'Solved':62}
        extra={'verified_main_evidence_blobs':1260,'verified_other_main_pages':200,
               'all_recorded_current_and_historical_hashes_correct':True,
               'both_full_original_resolution_notices_retained':True}
    else:
        p='references/stepaniants-ie15-2026-09-11/verification/document-checks.json'
        prev=json.loads(blob(old,p));now=json.loads(blob(new,p))
        assert all(now[k]==v for k,v in prev.items())
        record=now['later_upstream_integrations'][-1]
        for p,h in record['canonical_and_proof_files_byte_identical_to_previous_head'].items():
            data=blob(new,p)
            assert data==blob(old,p) and hashlib.sha256(data).hexdigest()==h
        assert dict(counts)==record['catalog_totals']
        p=registry['IE-15'];assert ot[p]==nt[p]
        assert b'The order-five witness alone left IE-15 Open' in blob(new,'references/colbrook-recovered-2026-09-11/README.md')
        assert b'That target was open when the order-five result was recorded' in blob(new,'RESOLVED.md')
        extra={'all_six_canonical_and_solution_hashes_correct_and_unchanged':True,
               'old_document_record_values_preserved':True,'both_obsolete_current_open_sentences_fixed':True}
    results[str(pr)]={'old':old,'new':new,'base':base,'contribution_paths':len(owned_paths),
        'genuine_changed_paths':changed,'unexpected_changes_outside_contribution':unexpected,
        'protected_reviewed_proof_source_paths':protected,'proof_sources_and_modes_unchanged':True,
        'all_203_ID_paths_unchanged':True,'canonical_status_counts':dict(counts),**extra}
(OUT/'PR68-83-delta-evidence.json').write_text(json.dumps(results,indent=2)+'\n')
print('PASS: both exact merge heads, all recorded hashes, 203 IDs, proof identity, provenance and status assertions.')
