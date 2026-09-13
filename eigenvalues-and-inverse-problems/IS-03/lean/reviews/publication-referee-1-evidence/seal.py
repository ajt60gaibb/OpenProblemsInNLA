"""Seal this separate read-only publication review; no source/publication edit."""
from pathlib import Path
import datetime, hashlib, json
E=Path(__file__).resolve().parent
P=E.parents[1]
W=P.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,obj):(E/name).write_text(json.dumps(obj,indent=2)+'\n')
assert json.loads((E/'audit-result.json').read_text())['result'].startswith('PASS')
assert (E/'audit.log').read_text().startswith('PASS')
pages=[]
observations=[
 'Read original resolution attribution, George formalization/full affiliation, source distinction and reviewed exports. Main text, equations and footer fit.',
 'Read actual verification scope and complete original n>=5, arbitrary-real-entrywise-nonnegative/exact-n-1 target. Formula, body, link text and footer are readable without clipping.',
 'Read unchanged references and dated historical checks. Main text and complete footer fit; remaining page whitespace is intentional.']
expected=['a120e48d56177c80f4dc91801eee87760706ff1641242ab5ba317f6d779bd6a4','adc96076025a214b8cbcfcf027f86e4005ba13def9a27973dd4e1d7dfa6516c8','8a89314577bb427029d420b0a1f16422eef25ce19f0ead7756c67871556961f4']
for i in range(1,4):
 p=Path('/tmp/nla-is03-publication-pages')/f'page-{i}.png'
 assert sha(p)==expected[i-1]
 pages.append({'page':i,'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size,'actual_original_detail_view':True,'observation':observations[i-1]})
pdf=P.parent/'problem.pdf';tex=P.parent/'problem.tex'
assert sha(pdf)=='48be4ca94c0582e6758dac5a96307f0cac8a9369a64b2c305165a2273e1d5cdc'
assert sha(tex)=='74d890e50b88c14201ca3d685357b7d3fbce8e4121c3e8402b34a2a64fb2462b'
save('VISUAL-REVIEW.json',{'reviewer':'/root/leancert_examples','role':'Independent read-only publication reviewer; additional role, no new mathematical referee','verdict':'PASS all three final pages','pdf':{'path':str(pdf.relative_to(W)),'sha256':sha(pdf),'bytes':pdf.stat().st_size},'tex':{'path':str(tex.relative_to(W)),'sha256':sha(tex),'bytes':tex.stat().st_size},'pages':pages,'new_render_or_artifact_edit':False,'correction_changes_PDF_or_TeX':False})
save('execution.json',{'command':['/tmp/nla-lean-formalization/venv/bin/python',str(E/'audit.py')],'final_exit_code':0,'log':'audit.log','log_sha256':sha(E/'audit.log'),'scope':'Read-only source, metadata, inventory and immutable Git-blob inspection; writes only this separate review evidence. No Lean, test suite, renderer, dependency or Git mutation.','initial_environmental_interruption':{'first_exit_code':120,'first_redirected_log_bytes':0,'second_direct_exit_code':1,'observed_exception':"OSError: [Errno 28] No space left on device writing IS-03-RESOLVED-block.json from audit.py line114. Actual subprocess traceback was read via tool output; no successful earlier audit result is claimed.",'root_remediation':'Root removed148 disposable olean/ilean files from20 inactive independent prefixes, preserving all source, evidence, PDFs, active prefixes and MI22 cache. Review resumed successfully without a change to the auditor or source.','root_cleanup_receipt':'/tmp/nla-lean-formalization/inactive-independent-prefix-cleanup-2026-09-12.json'},'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
M=E/'EVIDENCE-MANIFEST.json'
files={str(p.relative_to(E)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(E.rglob('*')) if p.is_file() and p!=M}
report=E.parent/'publication-referee-1.md'
files['../publication-referee-1.md']={'sha256':sha(report),'bytes':report.stat().st_size}
save(M.name,{'scope':'Complete independent IS-03 publication-review evidence and report; original preparer and correction inventories remain separate and immutable.','exact_self_exclusion':'EVIDENCE-MANIFEST.json in this directory only','files':files})
for rel,row in files.items():
 p=(E/rel).resolve();assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
print(json.dumps({'verdict':'APPROVE corrected publication state','report_sha256':sha(report),'manifest_sha256':sha(M),'bound_files':len(files),'evidence_directory_files_including_outer':len(list(E.glob('*'))),'pdf_sha256':sha(pdf)},indent=2))
