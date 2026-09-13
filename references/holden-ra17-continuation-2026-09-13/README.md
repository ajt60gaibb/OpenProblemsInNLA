# RA-17 continuation: linear recovery and its topological relaxation

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation ([verified affiliation and submission record](SUBMISSION.md)).

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
  small-pencil calculation. Current status: **NOT_PROMOTED**.
- `logs/`: actual outputs and explicit exit codes for bounded certificate runs.
- `prior/`: the two earlier archives, copied without modification.
- `exploratory/`: selected interrupted scripts, not additional certified results.

The arithmetic test run recorded status **PASS**.
The number of recorded checks is **137**.
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
index, characteristic-class, and obstruction-theory results. The partial results passed a [separate informal Codex AI-agent audit](independent-review.md) on 13 September 2026. They have not received external human peer review or formal verification here. No priority claim is made.
Source identifiers, retrieval outcomes, and response hashes are retained in
`data/source_audit.json`; third-party full-text PDFs are not redistributed.
`MANIFEST.sha256` concerns file integrity, not mathematical correctness.
