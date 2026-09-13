"""Assemble provenance, execution status, and the distributable archive."""
from pathlib import Path
import hashlib,importlib.metadata as md,json,shutil,zipfile,sys,platform
R=Path(__file__).resolve().parents[1]
for name in ('RA17_extended_partial_resolution.zip','RA17_partial_resolution_and_verification.zip'):
    src=Path('/mnt/data')/name
    if src.exists():shutil.copy2(src,R/'prior'/name)
for name in ('sparse_kernel5.py','primary_obstruction.py','degree_parity.py'):
    src=Path('/mnt/data/third_research')/name
    if src.exists():shutil.copy2(src,R/'exploratory'/name)
for name in ('projective_six.py','numerical_six.py','extend9.py','twist_extension.py','multiblock_6.py'):
    src=Path('/mnt/data')/name
    if src.exists():shutil.copy2(src,R/'exploratory'/name)
(R/'exploratory/README.md').write_text('''# Exploratory provenance, not additional theorems\n\nThese files preserve selected interrupted calculations. They may depend on the\noriginal workspace, contain abandoned ideas, or perform numerical searches.\nOnly results explicitly accepted in `data/pencil_audit_status.json` and proved\nin the new manuscript are promoted to certified statements. A timeout or\ninconclusive certificate search is not a counterexample.\n''')
p=R/'code/extract_interrupted_pencil.py'
if p.exists():
    text=p.read_text().replace("P=Path('/mnt/data/third_research/sparse_kernel5.py')", "ROOT=Path(__file__).resolve().parents[1]\nP=ROOT/'exploratory/sparse_kernel5.py'")
    text=text.replace("O=Path('/mnt/data/RA17_continuation/data/interrupted_pencil.json')", "O=ROOT/'data/interrupted_pencil.json'")
    p.write_text(text)
p=R/'code/certify_interrupted_pencil.py'
text=p.read_text().replace('pos+=int(p>0); neg+=int(p<0)', 'pos+=(1 if p>0 else 0); neg+=(1 if p<0 else 0)')
p.write_text(text)
versions={'python':sys.version,'platform':platform.platform()}
for name in ('sympy','numpy','cvxpy','requests','beautifulsoup4'):
    try:versions[name]=md.version(name)
    except md.PackageNotFoundError:pass
(R/'data/environment.json').write_text(json.dumps(versions,indent=2))
(R/'requirements.txt').write_text('sympy=='+versions['sympy']+'\n')
(R/'requirements-optional.txt').write_text('\n'.join(name+'=='+versions[name] for name in ('numpy','cvxpy','requests','beautifulsoup4') if name in versions)+'\n')
checks=R/'data/exact_checks.json';status=json.loads(checks.read_text()) if checks.exists() else {'status':'NOT_COMPLETED'}
pencil=R/'data/pencil_audit_status.json';ps=json.loads(pencil.read_text()) if pencil.exists() else {'status':'NOT_PROMOTED'}
readme=f'''# RA-17 continuation: linear recovery and its topological relaxation

**Overall status: PARTIAL. This is not a full solution of RA-17.**

The missing all-dimension classification is not replaced by a continuous map,
an arbitrary vector-bundle frame, a finite table, or quantifier elimination.
In particular, this continuation does not determine whether mu_R(6,1) is
19 or 20, or whether mu_R(10,1) is 35 or 36.

## Main additional result

Let k=2r, c=d-k, m0=d^2-c^2 and n=m0-1. The complex determinantal degree is

    D(d,r) = product(i=0,...,c-1) (d+i)! i! / ((2r+i)! (c+i)!).

There is a continuous odd map from the unit real rank-at-most-2r link to
S^(n-1) if and only if this degree is even. Separately, the evaluation bundle
dQ over Gr_c(R^d) has c^2+1 independent continuous sections if and only if
the same degree is even. Both are exact statements about relaxations, not
about the existence of constant linear measurement matrices.

For (6,1), D=1764. Thus the rank-seven complement permitted by the previous
index calculation actually exists as an abstract bundle. A stronger argument
using only that complement relation cannot rule out nineteen measurements.
The report independently rederives the lower bound nineteen by the impossible
half-spin index 3/2 at eighteen measurements; the candidate nineteen endpoint
has the integer total index 3.

For even d and rank one, writing h=popcount(d/2-1), the direct index calculation
gives mu_R(d,1) >= 4d-4-2h+(h mod 2). This specializes the prior general index
method; it is not advertised as a new numerical improvement over that package.

## Files

- `writeup/RA17_topological_relaxation.pdf`: the new self-contained manuscript.
- `writeup/main.tex` and `writeup/pencil_audit.tex`: editable LaTeX source.
- `code/verify_relaxation.py`: rational degree, characteristic-number, mod-two,
  and exported integer-measurement checks.
- `data/antidiagonal_6_1.json`: twenty integer measurement rows, with a rational
  sixteen-dimensional kernel basis and the manuscript's uniform rank proof.
- `code/certify_interrupted_pencil.py`: full projective-chart/Hermite checker.
- `code/sos_pencil_certificate.py`: optional SDP proposal followed by mandatory
  rational identity and positive-definiteness verification.
- `data/pencil_audit_status.json`: precise acceptance status of the preserved
  small-pencil calculation. Current status: **{ps.get('status')}**.
- `logs/`: actual outputs and explicit exit codes for bounded certificate runs.
- `prior/`: the two earlier archives, copied without modification.
- `exploratory/`: selected interrupted scripts, not additional certified results.

The arithmetic test run recorded status **{status.get('status')}**.
The number of recorded checks is **{status.get('check_count','not available')}**.
These are arithmetic checks, not proof-assistant verification of topology.

## Reproduce

    python -m pip install -r requirements.txt
    python code/verify_relaxation.py

For a saved positive-Gram certificate:

    python code/sos_pencil_certificate.py --verify data/CERTIFICATE_FILENAME.json

This verification path does not require CVXPY. The optional numerical search
needs the installed packages recorded in `requirements-optional.txt`.
A numerical solver's success is not an exact certificate. Failure, timeout,
or a positive-dimensional chart is not a proof that a pencil is inadmissible.

To compile the manuscript, run `pdflatex main.tex` twice from `writeup/`.
Do not run copied exploratory scripts as if they were a test suite.

## Precise missing step

Either construct a 17-dimensional real linear subspace of 6x6 matrices in which
every nonzero matrix has rank at least three, or prove that every such space
contains a nonzero rank-at-most-two matrix. Neither alternative is established
by this continuation. The exact all-parameter RA-17 question remains unresolved
in this package.

## Assurance and provenance

The mathematical proofs are written arguments relying on the cited standard
index, characteristic-class, and obstruction-theory results. They have not
been independently peer-reviewed or formalized here. No priority claim is made.
Source identifiers, retrieval outcomes, and response hashes are retained in
`data/source_audit.json`; third-party full-text PDFs are not redistributed.
`MANIFEST.sha256` concerns file integrity, not mathematical correctness.
'''
(R/'README.md').write_text(readme)
(R/'STATUS.json').write_text(json.dumps({'overall':'PARTIAL','fully_solves_RA17':False,'new_linear_exact_values_claimed':[],
  'new_theorems':['critical continuous odd relaxation iff degree even','critical evaluation-frame relaxation iff degree even'],
  'arithmetic_run':status.get('status'),'pencil_audit':ps,
  'remaining_pair_6_1':[19,20],'remaining_pair_10_1':[35,36]},indent=2))
print(json.dumps({'arithmetic':status.get('status'),'pencil':ps,'pdf_exists':(R/'writeup/RA17_topological_relaxation.pdf').exists()},indent=2))
