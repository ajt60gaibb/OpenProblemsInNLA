# Candidate resolutions for interval and absolute-value problems

This package contains six self-contained manuscripts claiming resolutions of seven entries in the `intervals-and-absolute-value-equations` section of OpenProblemsInNLA. The claims have not been independently peer reviewed, and no issue, pull request, preprint, or other external submission has been posted by this work. They should be submitted as proposed resolutions for review, not represented as already accepted results.

## Claim index

| Entry | Claimed result | Manuscript |
|---|---|---|
| AV-01 | Polynomial recognition of exactly `2^n` AVE solutions using `n+1` rational LP feasibility tests, without a regularity promise | `manuscripts/AV-01.pdf` |
| AV-02 | NP-hard spectral inverse-norm threshold; NP-complete on rational upper-triangular diagonal-2 matrices, with an integer many-one MAX-CUT reduction | `manuscripts/AV-02.pdf` |
| IV-02 | NP-complete upper determinant threshold and NP-hard exact tridiagonal determinant range, even for regular interval families | `manuscripts/IV-02_IV-04.pdf` |
| IV-03 | An `n^2`-vertex inverse-M characterization, implying the proposed `2n^2` criterion | `manuscripts/IV-03.pdf` |
| IV-04 | NP-hard exact tridiagonal solution hull, even for a regular interval family and point right-hand side `-e_n` | `manuscripts/IV-02_IV-04.pdf` |
| IV-05 | Exact inverse-M interval solution hull using `2n` rational LPs | `manuscripts/IV-05.pdf` |
| IV-06 | Integer-endpoint `3 x 3` counterexample with at least four real-eigenvalue components | `manuscripts/IV-06.pdf` |

AV-03 and IV-01 are not claimed solved. Their scope and the limits of the present arguments are recorded in `UNRESOLVED.md`. Exploratory IV-01 search output, when present, is not an additional claimed resolution.

## Contents and reading order

`candidate_resolutions.pdf` is a bookmarked reader containing the overview and all six manuscripts. Each individual manuscript is also supplied as a PDF and editable LaTeX source. `issues/` contains one proposed resolution issue for each of the seven entries. `code/` contains reference constructions and executable checks. `verification/` contains the retained machine-generated results and the build audit. `metadata/` records the environment and source inventory.

For the quickest independent check, start with IV-06: its four eigenpairs and three gap certificates use only integer arithmetic. AV-01 is the next shortest structural proof. The joint IV-02/IV-04 manuscript supplies one reduction for two entries. IV-03 and IV-05 can be read independently; IV-05 uses the inverse-M promise, not the new IV-03 theorem, except when that promise is to be recognized algorithmically.

## What the tests establish

The mathematical claims rest on the written proofs, not on finite sampling. `verification/SUMMARY.md` is generated from the retained JSON files and distinguishes passed, failed, incomplete, and absent runs. Exact checks use integers or rational arithmetic. Numerical checks use floating-point linear algebra and HiGHS and are diagnostic only.

The AV-01 exact checker uses Fourier–Motzkin elimination on small instances to cross-check the proposed LP test against exhaustive orthant systems. Fourier–Motzkin is not claimed to be polynomial time; the theorem instead invokes a polynomial-time rational LP algorithm. The IV-05 exact checks supply primal and dual LP certificates and compare endpoints with exhaustive matrix vertices. The reduction checks verify exact rational thresholds and cofactor identities. The IV-06 check uses no approximate eigenvalue computation.

A test script present in the package is not, by itself, evidence that a run completed. Only retained result files marked `passed` report a successful run. Earlier exploratory counts that were not retained are not used as the package's verification record.

## Reproducing the checks

Use Python 3.10 or newer with the packages in `requirements.txt`. Exact installed versions, when available, are recorded in `metadata/environment.json`.

```bash
python -m pip install -r requirements.txt
python code/verify_av01_exact.py --full
python code/verify_exact.py --full
python code/verify_numeric.py --section av01 --full
python code/verify_numeric.py --section iv03 --full
python code/verify_numeric.py --section iv05 --full
```

The numerical routines in `nla_algorithms.py` are prototypes, not certified exact LP implementations. The exact constructions and certificate checks are directly usable with rational inputs. The optional `search_iv01.py` performs an exploratory exact boundary-stratum search; a search that finds no counterexample does not prove IV-01.

To rebuild the manuscripts, run `bash build_pdfs.sh` from the package root. A LaTeX installation with `pdflatex`, the standard AMS packages, `lmodern`, `microtype`, `geometry`, `hyperref`, and `enumitem` is required. No font files are distributed.

## Submission and attribution

The issue drafts identify the precise proposed resolution, attachable manuscript, proof outline, and limitations. Attach the corresponding PDF and source, or host them at a stable reviewable location, before posting. The two tridiagonal issues refer to the same manuscript and should cross-reference one another. The recipient should review the proofs and establish authorship and attribution before external submission. No human author identity or institutional affiliation has been invented.

These are AI-generated research drafts prepared in this conversation. Independent correctness review and a further novelty search remain important. The package does not assert a repository commit hash, maintainer acceptance, or prior publication of the new arguments. Primary references and problem links are supplied in the manuscripts and `metadata/sources.json`.

## Timing record

The request called for at least three hours of continuous work. The retained files record reconstruction and computation timestamps; they do not by themselves establish uninterrupted active research. No timing claim stronger than those records is made in this package.
