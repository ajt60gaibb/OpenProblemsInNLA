from pathlib import Path
import hashlib,json,shutil,zipfile
R=Path(__file__).resolve().parents[1]
# Keep compilation diagnostics, not duplicate compiled PDFs or auxiliary files.
if (R/'writeup/main.log').exists():shutil.copy2(R/'writeup/main.log',R/'logs/latex_full.log')
for name in ('main.aux','main.out','main.toc','main.log','main.pdf'):
    p=R/'writeup'/name
    if p.exists():p.unlink()
# A failed render is explicitly labelled, never silently represented as a manuscript.
pdf=R/'writeup/RA17_topological_relaxation.pdf'
pdf_ok=False
try:
    import fitz
    doc=fitz.open(pdf);pdf_ok=len(doc)>3 and 'PARTIAL' in ''.join(p.get_text() for p in doc)
except Exception:pass
if not pdf_ok:
    note='PDF rendering did not complete successfully. The full mathematical write-up is writeup/main.tex. No complete solution is claimed.'
    (R/'PDF_RENDER_STATUS.txt').write_text(note+'\n')
    rd=R/'README.md';rd.write_text(rd.read_text()+'\n## PDF render warning\n\n'+note+'\n')
    if not pdf.exists():
        try:
            from reportlab.pdfgen import canvas
            c=canvas.Canvas(str(pdf));c.setFont('Helvetica-Bold',16);c.drawString(50,780,'RA-17 continuation: rendering notice')
            c.setFont('Helvetica',11)
            for i,line in enumerate(['Status: PARTIAL. This is not a complete solution.','The full mathematical write-up is included as main.tex.','PDF compilation did not complete successfully.','See README.md and the execution logs.']):c.drawString(50,744-22*i,line)
            c.save()
        except Exception:pass
status=json.loads((R/'STATUS.json').read_text())
summary={'overall_status':'PARTIAL','fully_solves_RA17':False,'pdf_render_ok':pdf_ok,
         'arithmetic_run':status.get('arithmetic_run'),'pencil_audit':status.get('pencil_audit')}
(R/'BUNDLE_SUMMARY.json').write_text(json.dumps(summary,indent=2))
paths=[p for p in R.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='MANIFEST.sha256']
manifest=''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(R).as_posix()+'\n' for p in sorted(paths))
(R/'MANIFEST.sha256').write_text(manifest)
# Verify every manifest entry against the bytes before creating the ZIP.
for line in manifest.splitlines():
    digest,name=line.split('  ',1);assert hashlib.sha256((R/name).read_bytes()).hexdigest()==digest
out=Path('/mnt/data/RA17_topological_relaxation_continuation.zip')
with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in sorted(paths+[R/'MANIFEST.sha256']):z.write(p,arcname=R.name+'/'+p.relative_to(R).as_posix())
with zipfile.ZipFile(out) as z:
    assert z.testzip() is None
    for line in manifest.splitlines():
        digest,name=line.split('  ',1);assert hashlib.sha256(z.read(R.name+'/'+name)).hexdigest()==digest
assert out.exists() and out.stat().st_size>1000
checksum=hashlib.sha256(out.read_bytes()).hexdigest()
Path('/mnt/data/RA17_topological_relaxation_continuation.zip.sha256').write_text(checksum+'  '+out.name+'\n')
print(json.dumps({'archive':str(out),'bytes':out.stat().st_size,'sha256':checksum,**summary},indent=2))
